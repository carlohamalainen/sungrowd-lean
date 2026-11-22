import Sungrowd.Control

/-! # Control policy

What the inverter should be doing right now.

-/

namespace Sungrowd.Policy

open Sungrowd.Control

/-! ## Time of day -/

/-- A wall-clock minute, as a user enters it: "01:00", "05:55". Brisbane local time. -/
structure TimeOfDay where
  hour      : Nat
  minute    : Nat
  hour_lt   : hour < 24
  minute_lt : minute < 60
  deriving Repr, DecidableEq

def TimeOfDay.minuteOfDay (t : TimeOfDay) : Nat := 60 * t.hour + t.minute

theorem TimeOfDay.minuteOfDay_lt (t : TimeOfDay) : t.minuteOfDay < 1440 := by
  have h_lt := t.hour_lt
  have m_lt := t.minute_lt
  unfold minuteOfDay
  omega

def TimeOfDay.ofHM? (h m : Nat) : Option TimeOfDay :=
  if hh : h < 24 then
    if hm : m < 60 then some ⟨h, m, hh, hm⟩ 
                   else none
  else none

/-- "HH:MM", one or two digits each side. -/
def TimeOfDay.parse? (s : String) : Option TimeOfDay :=
  match s.splitOn ":" with
  | [hs, ms] =>
    if hs.length ∈ [1, 2] ∧ ms.length ∈ [1, 2] then do
      TimeOfDay.ofHM? (← hs.toNat?) (← ms.toNat?)
    else none
  | _ => none

instance : ToString TimeOfDay where
  toString t :=
    let two (n : Nat) := if n < 10 then s!"0{n}" else toString n
    s!"{two t.hour}:{two t.minute}"

/-! ## Intent: what the user asked for -/

/-- Grid import may not exceed what the main fuse allows at this voltage. -/
def nominalGridVoltage : Nat := 240

/-- How the charge rate is decided inside the window. -/
inductive ChargeMode
  /-- Charge at a constant rate. The inverter snaps to 10 W increments, so let's avoid anything under 10. -/
  | fixed    (power : ForcedPower) (h : 10 ≤ power.watts)
  /-- Recompute the rate every tick so that total grid import stays at `ceilingW`. -/
  | adaptive (ceilingW : Nat) (h : 100 ≤ ceilingW)
  deriving Repr, DecidableEq

/-- Charge between `start` and `stop` (half-open, same day) until SOC reaches `maxSOC`. -/
structure ChargeWindow where
  start    : TimeOfDay
  stop     : TimeOfDay
  mode     : ChargeMode
  maxSOC   : Nat
  start_lt : start.minuteOfDay < stop.minuteOfDay
  maxSOC_le : maxSOC ≤ 100
  deriving Repr, DecidableEq

def ChargeWindow.contains (w : ChargeWindow) (minute : Nat) : Bool :=
  w.start.minuteOfDay ≤ minute && minute < w.stop.minuteOfDay

def ChargeWindow.make? (start stop : TimeOfDay) (mode : ChargeMode) (maxSOC : Nat)
    (gridFuseAmps : Nat) : Except String ChargeWindow := do
  if hlt : start.minuteOfDay < stop.minuteOfDay then
    if hsoc : maxSOC ≤ 100 then
      if let .adaptive c _ := mode then
        let fuseW := gridFuseAmps * nominalGridVoltage
        if c > fuseW then
          throw s!"adaptive grid ceiling {c} W exceeds the {gridFuseAmps} A main fuse ({fuseW} W)"
      return ⟨start, stop, mode, maxSOC, hlt, hsoc⟩
    else throw s!"maxSOC {maxSOC} is greater than 100"
  else throw s!"charge window has start {start} at or after end {stop}"

/-- Do `action` regardless of the schedule, until `expiry`. -/
structure ManualOverride where
  action    : Action
  /-- Unix seconds. -/
  expiry    : Option Int
  deriving Repr, DecidableEq

/-- User's intent. A disabled schedule is `window = none`. -/
structure Intent where
  window   : Option ChargeWindow
  override : Option ManualOverride
  deriving Repr, DecidableEq

/-- Clear an override whose deadline has passed. The caller persists the result if it changed. -/
def Intent.expireOverride (i : Intent) (nowUnix : Int) : Intent :=
  match i.override with
  | some { expiry := some t, .. } => if nowUnix < t then i else { i with override := none }
  | _ => i

/-! ## Inputs and state -/

/-- Fresh sensor readings; `none` means missing, stale, or the inverter's NaN sentinel. -/
structure Snapshot where
  /-- Battery state of charge in tenths of a percent: 984 = 98.4 %. -/
  socTenths : Option Nat
  /-- Grid power, W: positive is export, negative is import. -/
  gridW     : Option Int
  /-- Battery power, W: positive is discharge, negative is charge. -/
  batteryW  : Option Int
  deriving Repr

/-! ## The adaptive controller -/

def rampUpPerTickW : Int := 500  -- climb slowly: ~40 s from 0 to 4 kW
def minChargeW     : Int := 200  -- below this, hold at stop rather than a token charge
def quantumW       : Int := 100  -- resolution of the emitted charge command
def hysteresisW    : Int := 60   -- hold band around a quantum boundary; > load jitter, < quantum

/-- One tick of the adaptive controller: the new charge setpoint. The rest of the house draws
`importW - chargingW` from the grid, and the target is whatever of the ceiling that leaves.
Drop to the target at once (a kettle must not hold import over the ceiling for more than a
tick) but climb at most `rampUpPerTickW` per tick. Uses *measured* charging, which is safe
when the BMS tapers the charge rate. -/
def adaptiveStep (prevW ceilingW importW chargingW maxW : Int) : Int :=
  let targetW := ceilingW - (importW - chargingW)
  let next := if targetW < prevW then targetW else min (prevW + rampUpPerTickW) targetW
  min (max next 0) maxW

/-- Snap the setpoint to the 100 W ladder, with hysteresis: hold the previous command until
the setpoint leaves `[prevW - 60, prevW + 100 + 60)`, then floor. Plain flooring is memoryless,
so load jitter on a boundary would flip the command (and force a register write) every tick.
A Schmitt trigger. -/
def hystQuantize (setpointW prevW : Int) : Int :=
  if setpointW ≥ prevW + quantumW + hysteresisW ∨ setpointW < prevW - hysteresisW then
    quantumW * (setpointW / quantumW)
  else
    prevW

theorem adaptiveStep_nonneg (prevW ceilingW importW chargingW maxW : Int) (h : 0 ≤ maxW) :
    0 ≤ adaptiveStep prevW ceilingW importW chargingW maxW := by
  unfold adaptiveStep 
  dsimp only
  split <;> omega

theorem adaptiveStep_le_max (prevW ceilingW importW chargingW maxW : Int) :
    adaptiveStep prevW ceilingW importW chargingW maxW ≤ maxW := by
  unfold adaptiveStep
  dsimp only
  split <;> omega

/-! ## Commands the inverter echoes back

The adaptive controller's command, `ControllerState.cmdW`, is what we send as the forced charge
power. -/

/-- A command the inverter will hold exactly: on the 100 W ladder (so also on the inverter's
10 W grid) and within its rating. `ControllerState` carries a proof of this for its `cmdW`, so
`chargeAt` needs no clamping. -/
def CmdOk (w : Int) : Prop := w % 100 = 0 ∧ 0 ≤ w ∧ w ≤ maxForcedPowerW

instance (w : Int) : Decidable (CmdOk w) := by unfold CmdOk; infer_instance

theorem CmdOk.zero : CmdOk 0 := by decide

/-- `adaptiveStep`, bounded by the inverter's rating, is a valid input to `hystQuantize`. -/
theorem adaptiveStep_ok (prevW ceilingW importW chargingW : Int) :
    0 ≤ adaptiveStep prevW ceilingW importW chargingW maxForcedPowerW ∧
    adaptiveStep prevW ceilingW importW chargingW maxForcedPowerW ≤ maxForcedPowerW :=
  ⟨adaptiveStep_nonneg _ _ _ _ _ (by unfold maxForcedPowerW; omega), adaptiveStep_le_max _ _ _ _ _⟩

/-- Quantizing an in-range setpoint from a valid command gives a valid command. -/
theorem hystQuantize_ok (s prev : Int) (hs : 0 ≤ s ∧ s ≤ maxForcedPowerW) (hp : CmdOk prev) :
    CmdOk (hystQuantize s prev) := by
  unfold CmdOk at * 
  unfold hystQuantize quantumW hysteresisW
  simp only [maxForcedPowerW] at *
  split <;> omega

/-- A forced charge at exactly `w` watts. -/
def chargeAt (w : Int) (h : CmdOk w) : ControlRegisters :=
  ⟨.forced, .charge, ⟨w.toNat, by unfold CmdOk at h; omega, by unfold CmdOk at h; omega⟩⟩

/-! ## Controller state -/

/-- What the controller remembers between ticks. -/
structure ControllerState where
  /-- Have we reached the target SOC? -/
  targetReached : Bool := false
  /-- Adaptive controller's setpoint, at full resolution. -/
  setpointW     : Int := 0
  /-- Last quantized command, the position on the 100 W ladder (for hysteresis). -/
  cmdW          : Int := 0
  /-- The command is one we can send as is. -/
  cmdOk         : CmdOk cmdW := by decide
  /-- The intent we last saw; a change resets the latch and soft-starts the controller. -/
  lastIntent    : Option Intent := none
  deriving Repr

/-- Not actively adaptive-charging: the next entry into adaptive mode soft-starts from zero. -/
def ControllerState.resetAdaptive (st : ControllerState) : ControllerState :=
  { st with setpointW := 0, cmdW := 0, cmdOk := .zero }

/-! ## The decision -/

/-- Why we chose what we chose, for the log. -/
inductive Reason
  | manualOverride
  | scheduleDisabled
  | outsideWindow
  | targetReached
  | scheduledCharge
  | adaptiveCharge
  | adaptiveHold
  deriving Repr, DecidableEq

def Reason.label : Reason → String
  | .manualOverride   => "manual override"
  | .scheduleDisabled => "self consumption"
  | .outsideWindow    => "self consumption (outside window)"
  | .targetReached    => "stop (target SOC reached)"
  | .scheduledCharge  => "scheduled charge"
  | .adaptiveCharge   => "adaptive charge"
  | .adaptiveHold     => "adaptive charge: hold (no grid headroom)"

inductive Decision
  /-- Converge the inverter to these registers. -/
  | apply (registers : ControlRegisters) (reason : Reason)
  /-- Not enough information to decide: leave the inverter as it is. -/
  | leave (why : String)
  deriving Repr, DecidableEq

def forcedStop : ControlRegisters := ⟨.forced, .stop, ⟨0, rfl, by decide⟩⟩

/-- One tick of adaptive charging under a grid import ceiling, given fresh grid and battery
power (positive is export and discharge). -/
def adaptiveTick (st : ControllerState) (ceilingW gridW battW : Int) : Decision × ControllerState :=
  let importW   := max 0 (-gridW)
  let chargingW := max 0 (-battW)
  let setpointW := adaptiveStep st.setpointW ceilingW importW chargingW maxForcedPowerW
  let cmdW      := hystQuantize setpointW st.cmdW
  -- The one place a new command is made, so the one place that needs a proof.
  have cmdOk : CmdOk cmdW := hystQuantize_ok _ _ (adaptiveStep_ok ..) st.cmdOk
  let st        := { st with setpointW, cmdW, cmdOk }
  if cmdW < minChargeW then (.apply forcedStop .adaptiveHold, st)
  else (.apply (chargeAt cmdW cmdOk) .adaptiveCharge, st)

/-- Given the current intent, snapshot, minute of day, and controller state,
decide on the new decision and controller state. We assume that `intent` has 
already had `expireOverride` applied. -/
def decide (intent : Intent) (snap : Snapshot) (minute : Nat) (st : ControllerState) :
    Decision × ControllerState :=
  -- A change of intent resets the latch and soft-starts the adaptive controller.
  let st := if st.lastIntent == some intent then st
    else { targetReached := false, setpointW := 0, cmdW := 0, lastIntent := some intent }
  match intent.override, intent.window with
  | some o, _ => (.apply o.action.registers .manualOverride, st.resetAdaptive)
  | none, none => (.apply .selfConsumption .scheduleDisabled, st.resetAdaptive)
  | none, some w =>
    match snap.socTenths with
    | none => (.leave "no fresh battery SOC; cannot evaluate the schedule", st)
    | some soc =>
      if !w.contains minute then
        (.apply .selfConsumption .outsideWindow, { st.resetAdaptive with targetReached := false })
      else if st.targetReached || soc ≥ 10 * w.maxSOC then
        (.apply forcedStop .targetReached, { st.resetAdaptive with targetReached := true })
      else
        match w.mode with
        | .fixed p _ => let registers       := ⟨.forced, .charge, p⟩
                        let reason          := .scheduledCharge
                        let decision        := .apply registers reason
                        let controllerState := st.resetAdaptive
                        ⟨decision, controllerState⟩
        | .adaptive ceilingW _ =>
          match snap.gridW, snap.batteryW with
          | some gridW, some battW => adaptiveTick st ceilingW gridW battW
          | _, _ => (.leave "no fresh grid/battery power; cannot run the adaptive controller", st)

/-- One reconciliation: expire the override, then decide. Returns the intent to persist. -/
def tick (intent : Intent) (snap : Snapshot) (nowUnix : Int) (minute : Nat)
    (st : ControllerState) : Intent × Decision × ControllerState :=
  let intent := intent.expireOverride nowUnix
  let (d, st) := decide intent snap minute st
  (intent, d, st)

/-! ## Properties -/

/-- Climb at most one ramp step per tick. -/
theorem adaptiveStep_ramp (prevW ceilingW importW chargingW maxW : Int) (h : 0 ≤ prevW) :
    adaptiveStep prevW ceilingW importW chargingW maxW ≤ prevW + rampUpPerTickW := by
  unfold adaptiveStep rampUpPerTickW
  dsimp only
  split <;> omega

/-- When the target falls below the setpoint, drop all the way to it in one tick. -/
theorem adaptiveStep_cut (prevW ceilingW importW chargingW maxW : Int)
    (h : ceilingW - (importW - chargingW) < prevW) :
    adaptiveStep prevW ceilingW importW chargingW maxW ≤ max (ceilingW - (importW - chargingW)) 0 := by
  unfold adaptiveStep
  dsimp only
  split <;> omega

/-- The command stays on the 100 W ladder. -/
theorem hystQuantize_ladder (setpointW prevW : Int) (h : prevW % quantumW = 0) :
    hystQuantize setpointW prevW % quantumW = 0 := by
  unfold hystQuantize
  split
  · simp [quantumW]
  · exact h

/-- A manual override always wins. -/
theorem decide_override (intent : Intent) (snap : Snapshot) (minute : Nat) (st : ControllerState)
    (o : ManualOverride) (h : intent.override = some o) :
    (decide intent snap minute st).1 = .apply o.action.registers .manualOverride := by
  -- short version:
  -- unfold decide
  -- rw [h]

  -- Longer: let's destructure intent
  obtain ⟨window, override⟩ := intent 
  subst h 
  unfold decide 
  change (Decision.apply o.action.registers .manualOverride, _).1 = _
  rfl 

def Decision.charges : Decision → Bool
  | .apply cr _ => cr.command == .charge
  | .leave _    => false

/-- Never charge once SOC has reached the window's target. -/
theorem decide_no_charge_at_target (intent : Intent) (snap : Snapshot) (minute : Nat)
    (st : ControllerState) (w : ChargeWindow) (soc : Nat)
    (hov : intent.override = none) (hw : intent.window = some w) (hsoc : snap.socTenths = some soc)
    (htarget : 10 * w.maxSOC ≤ soc) :
    (decide intent snap minute st).1.charges = false := by
  -- short:
  -- unfold decide
  -- simp only [hov, hw, hsoc]
  -- split <;> simp_all [Decision.charges, forcedStop, ControlRegisters.selfConsumption]
  obtain ⟨window, override⟩ := intent
  obtain ⟨socTenths, gridW, batteryW⟩ := snap
  subst hov 
  subst hw 
  subst hsoc 
  unfold decide
  dsimp only 
  simp only [ge_iff_le] 
  simp only [htarget]
  simp only [decide_true]
  simp only [Bool.or_true]
  simp only [ite_true]
  split 
  · dsimp only [Decision.charges, ControlRegisters.selfConsumption] 
    rfl  
  · dsimp only [Decision.charges, forcedStop] 
    rfl 

/-- Outside the window, hand control back to the inverter. -/
theorem decide_outside_window (intent : Intent) (snap : Snapshot) (minute : Nat)
    (st : ControllerState) (w : ChargeWindow) (soc : Nat)
    (hov : intent.override = none) (hw : intent.window = some w) (hsoc : snap.socTenths = some soc)
    (hout : w.contains minute = false) :
    (decide intent snap minute st).1 = .apply .selfConsumption .outsideWindow := by
  -- short version:
  -- unfold decide
  -- simp only [hov, hw, hsoc]
  -- split <;> simp_all
  obtain ⟨window, override⟩ := intent
  obtain ⟨socTenths, gridW, batteryW⟩ := snap
  subst hov 
  subst hw 
  subst hsoc 
  unfold decide 
  dsimp only 
  simp only [hout] 
  simp only [Bool.not_false]
  -- simp only [ite_true]
  simp only [↓reduceIte, beq_iff_eq]

/-! ## Go's test tables -/

-- TestParseTimeOfDay / String
#guard (TimeOfDay.parse? "01:00").map toString == some "01:00"
#guard (TimeOfDay.parse? "23:59").map toString == some "23:59"
#guard (TimeOfDay.parse? "24:00").isNone
#guard (TimeOfDay.parse? "12:60").isNone
#guard (TimeOfDay.parse? "noon").isNone

-- TestAdaptiveStep: ceiling 4320 W, battery max 5800 W.
#guard adaptiveStep 0    4320 180  0    5800 == 500   -- soft start
#guard adaptiveStep 4140 4320 4320 4140 5800 == 4140  -- steady state
#guard adaptiveStep 4140 4320 6720 4140 5800 == 1740  -- kettle: instant cut
#guard adaptiveStep 1000 4320 6000 1000 5800 == 0     -- floored at zero
#guard adaptiveStep 3000 4320 0    3000 5800 == 3500  -- ramp limited while exporting
#guard adaptiveStep 5700 4320 200  5700 5800 == 5800  -- clamped to battery max
#guard adaptiveStep 4140 4320 1180 1000 5800 == 4140  -- BMS taper

-- Convergence: no PV, house drawing 180 W, ideal plant. Ramps to 4140 W and holds.
#guard Id.run do
  let mut setpoint : Int := 0
  let mut importW  : Int := 180
  for _ in [0:20] do
    setpoint := adaptiveStep setpoint 4320 importW setpoint 5800
    importW := 180 + setpoint
  return setpoint == 4140

-- TestHystQuantize
#guard hystQuantize 150  0    == 0     -- cold start below band holds zero
#guard hystQuantize 160  0    == 100   -- cold start clears band, floors
#guard hystQuantize 1880 1900 == 1900  -- hold inside band
#guard hystQuantize 1955 1900 == 1900  -- hold near top of band
#guard hystQuantize 2060 1900 == 2000  -- step up only past upper edge
#guard hystQuantize 1841 1900 == 1900  -- hold just above lower edge
#guard hystQuantize 1839 1900 == 1800  -- step down past lower edge

-- The 1.8 <-> 1.9 kW chatter regression: jitter across 1900 W settles on one command.
#guard Id.run do
  let jitter : List Int := [1895, 1905, 1888, 1912, 1899, 1901, 1885, 1915]
  let settled := hystQuantize 1895 0
  let mut cmd := settled
  let mut stable := true
  for sp in jitter do
    cmd := hystQuantize sp cmd
    stable := stable && cmd == settled
  return stable && hystQuantize 2500 settled == 2500

/-! ## Scenarios for `decide` and `tick` -/

section Scenarios

private def t (h m : Nat) (hh : h < 24 := by decide) (hm : m < 60 := by decide) : TimeOfDay :=
  ⟨h, m, hh, hm⟩

/-- schedule.json from the Go repo: 00:00–06:00 at 800 W up to 40 %. -/
private def fixedWindow : ChargeWindow :=
  ⟨t 0 0, t 6 0, .fixed ⟨800, by decide, by decide⟩ (by decide), 40, by decide, by decide⟩

private def adaptiveWindow : ChargeWindow :=
  ⟨t 1 0, t 6 0, .adaptive 4320 (by decide), 80, by decide, by decide⟩

private def snap (soc : Nat) (gridW battW : Int := 0) : Snapshot := ⟨some soc, some gridW, some battW⟩

private def charge800 : ControlRegisters := ⟨.forced, .charge, ⟨800, by decide, by decide⟩⟩

-- 03:00, SOC 30.0 %: charge at the fixed rate.
#guard (decide ⟨some fixedWindow, none⟩ (snap 300) 180 {}).1 == .apply charge800 .scheduledCharge

-- SOC reaches 40.0 %: stop and latch; a dip to 39.5 % next tick stays stopped.
#guard
  let i : Intent := ⟨some fixedWindow, none⟩
  let (d1, st1) := decide i (snap 400) 180 {}
  let (d2, st2) := decide i (snap 395) 181 st1
  d1 == .apply forcedStop .targetReached && d2 == .apply forcedStop .targetReached
    && st2.targetReached
    -- Leaving the window releases the latch, so tomorrow's window charges again.
    && (decide i (snap 395) 360 st2).2.targetReached == false

-- Adaptive, 02:00, no PV, house drawing 180 W from the grid: soft start at 500 W, then
-- 1000 W on the next tick (the plant now imports 180 + 500).
#guard
  let i : Intent := ⟨some adaptiveWindow, none⟩
  let (d1, st1) := decide i (snap 500 (-180) 0) 120 {}
  let (d2, _)   := decide i (snap 500 (-680) (-500)) 121 st1
  d1 == .apply (chargeAt 500 (by decide)) .adaptiveCharge
    && d2 == .apply (chargeAt 1000 (by decide)) .adaptiveCharge

-- No fresh SOC: leave the inverter alone rather than guess.
#guard match (decide ⟨some fixedWindow, none⟩ ⟨none, none, none⟩ 180 {}).1 with
  | .leave _ => true
  | _        => false

-- An override until t = 1000 wins at t = 999 and is cleared (and persisted) at t = 1000.
#guard
  let o : ManualOverride := ⟨.stop, some 1000⟩
  let i : Intent := ⟨some fixedWindow, some o⟩
  let (i1, d1, _) := tick i (snap 300) 999 180 {}
  let (i2, d2, _) := tick i (snap 300) 1000 180 {}
  i1 == i && d1 == .apply forcedStop .manualOverride
    && i2.override == none && d2 == .apply charge800 .scheduledCharge

end Scenarios

end Sungrowd.Policy
