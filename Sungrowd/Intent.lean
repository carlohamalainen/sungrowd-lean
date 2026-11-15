import Lean.Data.Json
import Std.Time
import Sungrowd.Policy

/-! # Intent as JSON

sungrowd-go uses JSON for schedules and persisted intent. We maintain
the same format for full compatability.

`schedule.json`, i.e. `server.ChargeWindow`, for example:

`{"enabled": true, "mode": "adaptive", "start": "01:00", "end": "06:00",
  "charge_watts": 0, "ceiling_watts": 4320, "max_soc": 80}`

`persistedState`, the `state_json` column of its database:
`{"charge_window": <schedule>, "manual_override": {"registers": {…}, "expiry": "<RFC 3339>"}}`

-/

namespace Sungrowd.Policy

open Lean (Json ToJson FromJson toJson fromJson?)
open Sungrowd.Control

/-- Reject keys we don't know, like Go's `DisallowUnknownFields`: a typo such as `"max_SOC"`
must not silently become a default. -/
def checkKeys (what : String) (j : Json) (known : List String) : Except String Unit := do
  for k in (← j.getObj?).keys do
    unless known.contains k do throw s!"{what}: unknown field \"{k}\""

/-- A field that may be absent or `null`. -/
def optField (α : Type) [FromJson α] (j : Json) (k : String) : Except String (Option α) :=
  match fromJson? (j.getObjValD k) with
  | .ok v    => .ok v
  | .error e => .error s!"{k}: {e}"

def field (α : Type) [FromJson α] (j : Json) (k : String) : Except String α := do
  let some v ← optField α j k | throw s!"missing field \"{k}\""
  return v

/-! ## Time of day -/

instance : FromJson TimeOfDay where
  fromJson? j := do
    let s ← j.getStr?
    let some t := TimeOfDay.parse? s | throw s!"invalid time \"{s}\": want HH:MM"
    return t

instance : ToJson TimeOfDay := ⟨fun t => toString t⟩

/-! ## Schedule -/

def scheduleKeys : List String :=
  ["enabled", "mode", "start", "end", "charge_watts", "ceiling_watts", "max_soc"]

/-- Go's `ChargeWindow` JSON. A disabled schedule (`"enabled": false`) or `null` is `none`:
Go keeps a disabled window's fields around for the UI, but the controller never looks at them.

`gridFuseAmps` is the one check that needs configuration (see `ChargeWindow.make?`). The
fixed-mode rate is bounded by `ForcedPower` (the inverter's 5000 W rating), where Go uses its
configured battery limit. -/
def scheduleOfJson (gridFuseAmps : Nat) (j : Json) : Except String (Option ChargeWindow) := do
  if j.isNull then return none
  checkKeys "schedule" j scheduleKeys
  unless ← field Bool j "enabled" do return none
  let start  ← field TimeOfDay j "start"
  let stop   ← field TimeOfDay j "end"
  let maxSOC ← field Nat j "max_soc"
  -- Go's `EffectiveMode`: an empty or missing mode is fixed (rows saved before adaptive existed).
  let mode ← match (← optField String j "mode").getD "" with
    | "" | "fixed" =>
      let w ← field Nat j "charge_watts"
      let some p := ForcedPower.ofWatts? w
        | throw s!"charge watts {w} is greater than the maximum {maxForcedPowerW}"
      if h : 10 < p.watts then pure (ChargeMode.fixed p h)
      else throw s!"charge watts {w} is too low"
    | "adaptive" =>
      let c := (← optField Nat j "ceiling_watts").getD 0
      if h : 100 ≤ c then pure (ChargeMode.adaptive c h)
      else throw s!"adaptive grid ceiling {c} W is too low"
    | m => throw s!"unknown charge mode \"{m}\""
  ChargeWindow.make? start stop mode maxSOC gridFuseAmps

/-- Go's shape. The field the mode doesn't use is written as 0 (`charge_watts`) or left out
(`ceiling_watts`, which Go tags `omitempty`). -/
def scheduleJson (w : ChargeWindow) : Json :=
  let (mode, chargeW, ceiling) : String × Nat × List (String × Json) := match w.mode with
    | .fixed p _    => ("fixed", p.watts, [])
    | .adaptive c _ => ("adaptive", 0, [("ceiling_watts", toJson c)])
  Json.mkObj <|
    [("enabled", toJson true), ("mode", toJson mode), ("start", toJson w.start),
     ("end", toJson w.stop), ("charge_watts", toJson chargeW)]
    ++ ceiling ++ [("max_soc", toJson w.maxSOC)]

/-- `none` is Go's disabled window. -/
def scheduleToJson : Option ChargeWindow → Json
  | some w => scheduleJson w
  | none   => Json.mkObj [("enabled", toJson false)]

/-! ## Timestamps

Go writes `time.Time` as RFC 3339 with fractional seconds when they are non-zero. Lean's
ISO 8601 parser wants whole seconds, so the fraction is dropped. -/

/-- `"2026-10-26T06:00:00.5+10:00"` ⇒ `"2026-10-26T06:00:00+10:00"`. -/
def dropFraction (s : String) : String :=
  match s.toList.splitAt 19 with
  | (pre, '.' :: rest) => String.ofList (pre ++ rest.dropWhile Char.isDigit)
  | _                  => s

def unixOfRFC3339 (s : String) : Except String Int := do
  let dt ← Std.Time.DateTime.fromISO8601String (dropFraction s)
    |>.mapError fun e => s!"invalid timestamp \"{s}\": {e}"
  return dt.toTimestamp.toSecondsSinceUnixEpoch.val

def rfc3339OfUnix (t : Int) : String :=
  let ts := Std.Time.Timestamp.ofSecondsSinceUnixEpoch ⟨t⟩
  (Std.Time.DateTime.ofTimestamp ts .UTC).toISO8601String

/-! ## Manual override -/

/-- Go's `ControlRegisters` JSON. The `_label` fields are for humans and are ignored. -/
def registersOfJson (j : Json) : Except String ControlRegisters := do
  let mode  ← field Nat j "ems_mode"
  let cmd   ← field Nat j "ems_command"
  let power ← field Nat j "forced_power_w"

  let word (n : Nat) (k : String) : Except String UInt16 :=
    if n < UInt16.size 
      then pure n.toUInt16 
      else throw s!"{k} {n} does not fit in a register"

  let raw : Vector UInt16 3 := #v[← word mode "ems_mode", ← word cmd "ems_command", ← word power "forced_power_w"]

  let some cr := ControlRegisters.ofRaw? raw | throw s!"unsupported registers {showRaw raw}"

  return cr

instance : ToJson ManualOverride where
  toJson o := Json.mkObj <|
    [("registers", rawJson o.registers.toRaw)]
    ++ (o.expiry.map fun t => [("expiry", toJson (rfc3339OfUnix t))]).getD []

def overrideOfJson (j : Json) : Except String (Option ManualOverride) := do
  if j.isNull then return none
  let registers ← registersOfJson (← field Json j "registers")
  let expiry ← match ← optField String j "expiry" with
    | some s => some <$> unixOfRFC3339 s
    | none   => pure none
  return some { registers, expiry }

/-! ## Intent -/

instance : ToJson Intent where
  toJson i := Json.mkObj [
    ("charge_window",   scheduleToJson i.window),
    ("manual_override", toJson i.override)]

def intentOfJson (gridFuseAmps : Nat) (j : Json) : Except String Intent := do
  checkKeys "intent" j ["charge_window", "manual_override"]
  let window   ← scheduleOfJson gridFuseAmps (j.getObjValD "charge_window")
    |>.mapError (s!"charge_window: {·}")
  let override ← overrideOfJson (j.getObjValD "manual_override")
    |>.mapError (s!"manual_override: {·}")
  return { window, override }

/-- Either file format: a persisted intent if it has one of `persistedState`'s keys, otherwise
a bare schedule (no override), as in Go's `schedule.json`. -/
def intentOfFile (gridFuseAmps : Nat) (j : Json) : Except String Intent :=
  let isIntent := (j.getObjVal? "charge_window").isOk || (j.getObjVal? "manual_override").isOk
  if isIntent then intentOfJson gridFuseAmps j
  else return { window := ← scheduleOfJson gridFuseAmps j, override := none }

/-! ## Controller state

Not a Go format: Go keeps this in memory. Persisting it lets a `tick` run from cron or a shell
loop behave like one long-running daemon (the latch holds, the adaptive ramp continues). -/

instance : ToJson ControllerState where
  toJson st := Json.mkObj [
    ("target_reached", st.targetReached),
    ("setpoint_w",     st.setpointW),
    ("cmd_w",          st.cmdW),
    ("last_intent",    toJson st.lastIntent)]

def controllerStateOfJson (gridFuseAmps : Nat) (j : Json) : Except String ControllerState := do
  checkKeys "controller state" j ["target_reached", "setpoint_w", "cmd_w", "last_intent"]
  let lastIntent ← match j.getObjValD "last_intent" with
    | .null => pure none
    | li    => some <$> intentOfJson gridFuseAmps li
  let cmdW ← field Int j "cmd_w"
  -- A hand-edited or corrupted file must not put the controller off the ladder.
  if cmdOk : CmdOk cmdW then
    return {
      targetReached := ← field Bool j "target_reached"
      setpointW     := ← field Int j "setpoint_w"
      cmdW, cmdOk, lastIntent }
  else
    throw s!"cmd_w {cmdW} is not a multiple of 100 in 0..{maxForcedPowerW}"

/-! ## Examples -/

private def parse (s : String) : Except String Json := Json.parse s

private def err? : Except String α → Option String
  | .error e => some e
  | .ok _    => none

-- The repository's `schedule.json` from the Go daemon.
#guard match parse "{\"enabled\": true, \"start\": \"00:00\", \"end\": \"06:00\",
    \"charge_watts\": 800, \"max_soc\": 40}" >>= intentOfFile 20 with
  | .ok { window := some { mode := .fixed p _, maxSOC := 40, .. }, override := none } =>
    p.watts == 800
  | _ => false

#guard match parse "{\"enabled\": true, \"mode\": \"adaptive\", \"start\": \"01:00\",
    \"end\": \"06:00\", \"charge_watts\": 0, \"ceiling_watts\": 4320, \"max_soc\": 80}"
    >>= intentOfFile 20 with
  | .ok { window := some { mode := .adaptive 4320 _, .. }, .. } => true
  | _ => false

-- Errors name the field.
#guard err? (parse "{\"enabled\": true, \"start\": \"06:00\", \"end\": \"01:00\",
    \"charge_watts\": 800, \"max_soc\": 40}" >>= intentOfFile 20)
  == some "charge window has start 06:00 at or after end 01:00"
#guard err? (parse "{\"enabled\": true, \"start\": \"00:00\", \"end\": \"06:00\",
    \"charge_watts\": 800, \"max_SOC\": 40}" >>= intentOfFile 20)
  == some "schedule: unknown field \"max_SOC\""
#guard err? (parse "{\"enabled\": true, \"mode\": \"adaptive\", \"start\": \"01:00\",
    \"end\": \"06:00\", \"ceiling_watts\": 6000, \"max_soc\": 80}" >>= intentOfFile 20)
  == some "adaptive grid ceiling 6000 W exceeds the 20 A main fuse (4800 W)"
#guard (parse "{\"enabled\": false}" >>= intentOfFile 20).toOption.map (·.window.isNone) == some true
#guard (parse "null" >>= intentOfFile 20).toOption.map (·.window.isNone) == some true

-- A persisted intent with an override, as Go stores it (fractional seconds included).
#guard match parse "{\"charge_window\": {\"enabled\": false}, \"manual_override\":
    {\"registers\": {\"ems_mode\": 2, \"ems_mode_label\": \"forced\", \"ems_command\": 204,
     \"ems_command_label\": \"stop\", \"forced_power_w\": 0},
     \"expiry\": \"2026-10-26T06:00:00.5+10:00\"}}" >>= intentOfFile 20 with
  | .ok { window := none, override := some { registers, expiry := some t } } =>
    registers == ⟨.forced, .stop, ⟨0, rfl, by decide⟩⟩ && t == 1792958400
  | _ => false

#guard (unixOfRFC3339 (rfc3339OfUnix 1792958400)).toOption == some 1792958400

-- What we write, we read back.
#guard
  let i : Intent := { window := none, override := some ⟨.selfConsumption, some 1792958400⟩ }
  (intentOfJson 20 (toJson i)).toOption == some i

-- Controller state round-trips, and an off-ladder command is rejected.
#guard
  let st : ControllerState := { targetReached := true, setpointW := 1234, cmdW := 1200 }
  (controllerStateOfJson 20 (toJson st)).toOption.map (·.cmdW) == some 1200
#guard err? (parse "{\"target_reached\": false, \"setpoint_w\": 0, \"cmd_w\": 150}"
    >>= controllerStateOfJson 20) == some "cmd_w 150 is not a multiple of 100 in 0..5000"

end Sungrowd.Policy
