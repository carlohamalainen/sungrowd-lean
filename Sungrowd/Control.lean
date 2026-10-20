import Lean.Data.Json
import Std.Time
import Modbus.Client

namespace Sungrowd.Control

inductive EMSMode 
  | selfConsumption 
  | forced 
  deriving DecidableEq, Repr

def EMSMode.toRaw : EMSMode → UInt16
  | selfConsumption   => 0 
  | forced            => 2

def EMSMode.ofRaw? : UInt16 → Option EMSMode 
  | 0   => some .selfConsumption 
  | 2   => some .forced 
  | _   => none 

theorem EMSMode.ofRaw?_toRaw (m : EMSMode) : EMSMode.ofRaw? m.toRaw = some m := by 
  -- shorter proof: cases m <;> rfl
  unfold ofRaw?
  cases m with 
  | selfConsumption => rfl
  | forced          => rfl

theorem EMSMode.toRaw_of_ofRaw? { v : UInt16 } { m : EMSMode } 
    (h : EMSMode.ofRaw? v = some m) : 
    m.toRaw = v := by 
  -- shorter proof:
  -- unfold EMSMode.ofRaw? at h
  -- split at h <;> cases h <;> rfl
  unfold EMSMode.ofRaw? at h 
  split at h 
  · injection h with what_is_m
    subst m 
    rfl
  · injection h 
    subst m 
    rfl
  · nomatch h

/-- Register 13050: what happens in forced mode. -/
inductive Command 
  | charge 
  | discharge 
  | stop 
  deriving DecidableEq, Repr

def Command.toRaw : Command → UInt16 
  | charge      => 0xAA
  | discharge   => 0xBB
  | stop        => 0xCC

def Command.ofRaw? : UInt16 → Option Command 
  | 0xAA  => charge
  | 0xBB  => discharge
  | 0xCC  => stop
  | _     => none

theorem Command.ofRaw?_toRaw (c : Command) : (ofRaw? c.toRaw = c) := by
  cases c <;> rfl

theorem Command.toRaw_of_ofRaw? {v : UInt16 } {c : Command } 
  (h : Command.ofRaw? v = some c) : (c.toRaw = v) := by 
  unfold ofRaw? at h
  -- shorter:
  -- split at h <;> cases h <;> rfl
  split at h
  · injection h; subst c; rfl
  · injection h; subst c; rfl
  · injection h; subst c; rfl
  · nomatch h

/-- SH5.0RS rated powder. -/
def maxForcedPowerW : Nat := 5000

/-- Register 13051. The inverter quantises to 10 W steps, so we only
hold values that will echo back unchanged. -/
structure ForcedPower where 
  watts   : Nat
  step    : watts % 10 = 0
  le_max  : watts ≤ maxForcedPowerW
  deriving Repr

instance : DecidableEq ForcedPower := fun a b => 
  if h : a.watts = b.watts then 
    isTrue (by cases a; cases b; simp at h; subst h; rfl)
  else 
    isFalse (by 
      obtain ⟨w1, s1, l1⟩ := a
      obtain ⟨w2, s2, l2⟩ := b
      simp at h
      intro e 
      injection e with hw
      exact h hw)

/-- Snap down to the 10 W grid; reject anything over maximum power. -/
def ForcedPower.ofWatts? (w : Nat) : Option ForcedPower := 
  if h : w ≤ maxForcedPowerW then 
    some ⟨w / 10 * 10, by omega, by omega⟩ 
  else 
    none

def ForcedPower.toRaw (p : ForcedPower) : UInt16 := p.watts.toUInt16

def ForcedPower.ofRaw? (v : UInt16) : Option ForcedPower := 
  if h : v.toNat % 10 = 0 ∧ v.toNat ≤ maxForcedPowerW then 
    some ⟨v.toNat, h.1, h.2⟩ 
  else 
    none

theorem ForcedPower.ofRaw?_toRaw (p : ForcedPower) : ForcedPower.ofRaw? p.toRaw = some p := by 
  obtain ⟨w, step, le_max⟩ := p 
  simp [maxForcedPowerW] at le_max
  have hlt : w < 65536 := by omega -- so we're not overflowing UInt16
  simp [ofRaw?, toRaw, Nat.mod_eq_of_lt hlt]
  refine ⟨?_, ?_⟩
  · omega 
  · unfold maxForcedPowerW
    omega 


#guard (ForcedPower.ofWatts? 3007).map (·.watts) == some 3000
#guard (ForcedPower.ofWatts? 5001).isNone
#guard (ForcedPower.ofRaw? 3007).isNone


/-! ## The three control registers as one block -/

/-- Registers 13049–13051 are written and read together in one request. -/
def regEMSMode : UInt16 := 13049

structure ControlRegisters where
  mode    : EMSMode
  command : Command
  power   : ForcedPower
  deriving DecidableEq, Repr

def ControlRegisters.toRaw (cr : ControlRegisters) : Vector UInt16 3 :=
  #v[cr.mode.toRaw, cr.command.toRaw, cr.power.toRaw]

def ControlRegisters.ofRaw? (v : Vector UInt16 3) : Option ControlRegisters := do
  return ⟨← EMSMode.ofRaw? v[0], ← Command.ofRaw? v[1], ← ForcedPower.ofRaw? v[2]⟩

theorem ControlRegisters.ofRaw?_toRaw (cr : ControlRegisters) :
    ControlRegisters.ofRaw? cr.toRaw = some cr := by
  simp [ofRaw?, toRaw, EMSMode.ofRaw?_toRaw, Command.ofRaw?_toRaw, ForcedPower.ofRaw?_toRaw]

/-- Sungrow's "self consumption" mode: the inverter runs its own EMS. -/
def ControlRegisters.selfConsumption : ControlRegisters := ⟨.selfConsumption, .stop, ⟨0, rfl, by decide⟩⟩

def EMSMode.label : EMSMode → String
  | .selfConsumption => "self_consumption"
  | .forced          => "forced"

def Command.label : Command → String
  | .charge    => "charge"
  | .discharge => "discharge"
  | .stop      => "stop"

instance : ToString ControlRegisters where
  toString cr := s!"{cr.mode.label} {cr.command.label} {cr.power.watts} W"

/-- JSON interpretation of raw words. We might not be able to decode the bytes
that come back. Labels are `unknown` for values we don't model. -/
def rawJson (v : Vector UInt16 3) : Lean.Json :=
  Lean.Json.mkObj [
    ("ems_mode",          v[0].toNat),
    ("ems_mode_label",    ((EMSMode.ofRaw? v[0]).map (·.label)).getD "unknown"),
    ("ems_command",       v[1].toNat),
    ("ems_command_label", ((Command.ofRaw? v[1]).map (·.label)).getD "unknown"),
    ("forced_power_w",    v[2].toNat)]

def showRaw (v : Vector UInt16 3) : String :=
  match ControlRegisters.ofRaw? v with
  | some cr => toString cr
  | none    => s!"undecodable {v.toArray}"

/-! ## Verified write -/

open Modbus

def readControl (c : Client) : M (Vector UInt16 3) :=
  c.readHoldingRegisters regEMSMode 3

/-- How a write ended, in increasing order of concern. -/
inductive WriteOutcome
  /-- The registers already held the value; nothing was sent. -/
  | noOp
  | ok
  /-- Never reached the inverter (including: the read before it failed). Unchanged. -/
  | notSent    (e : Error)
  /-- Sent, but the read-back failed. -/
  | unverified (e : Error)
  /-- Sent and read back, but the inverter shows something else. -/
  | mismatch   (saw : Vector UInt16 3)
  deriving Repr

def WriteOutcome.err? : WriteOutcome → Option String
  | .noOp | .ok     => none
  | .notSent e      => some s!"control write was not sent (inverter unchanged): {e}"
  | .unverified e   => some s!"control write was sent but could not be confirmed: {e}"
  | .mismatch saw   => some s!"control write was sent but did not take effect: now see {showRaw saw}"

/-- Audit record of one write attempt. -/
structure WriteOp where
  recordedAt : Std.Time.Timestamp         -- like `Reading.read_at`; formatted only for JSON
  before     : Option (Vector UInt16 3)   -- none if the read before writing failed
  intended   : ControlRegisters
  after      : Option (Vector UInt16 3)   -- none if not read back
  outcome    : WriteOutcome

instance : Lean.ToJson WriteOp where
  toJson op := Lean.Json.mkObj <|
    [("recorded_at", Lean.toJson (Std.Time.DateTime.ofTimestamp op.recordedAt .UTC).toISO8601String)]
    ++ (op.before.map fun v => [("before", rawJson v)]).getD []
    ++ [("intended", rawJson op.intended.toRaw)]
    ++ (op.after.map fun v => [("after", rawJson v)]).getD []
    ++ (if op.outcome matches .noOp then [("no_op", Lean.toJson true)] else [])
    ++ (op.outcome.err?.map fun e => [("err", Lean.toJson e)]).getD []

/-- Read the registers, write `value` if they differ, then read back to check. -/
def safeWriteControl (c : Client) (value : ControlRegisters) : Std.Async.Async WriteOp := do
  let recordedAt ← Std.Time.Timestamp.now
  let op : WriteOp := { recordedAt, before := none, intended := value, after := none, outcome := .ok }
  let want := value.toRaw

  let before ← match ← (readControl c).run with
    | .error e => return { op with outcome := .notSent e }
    | .ok v    => pure v
  let op := { op with before := some before }

  if before == want then
    return { op with after := some before, outcome := .noOp }

  if let .error e ← (c.writeMultipleRegisters regEMSMode want).run then
    return { op with outcome := .notSent e }

  match ← (readControl c).run with
  | .error e => return { op with outcome := .unverified e }
  | .ok after =>
    let op := { op with after := some after }
    return if after == want then op else { op with outcome := .mismatch after }

end Sungrowd.Control
