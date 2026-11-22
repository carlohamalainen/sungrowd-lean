import Lean.Data.Json
import Std.Time
import Sungrowd.Policy

/-! # Intent as JSON

A key is present only when it means something: no `null`s, no flags that switch other fields
off, no power where nothing uses one. An intent, with every key optional:

`{"charge_window": {"mode": "adaptive", "start": "01:00", "end": "06:00",
                    "ceiling_watts": 4320, "max_soc": 80},
  "manual_override": {"action": "charge", "watts": 3000, "expiry": "2026-11-23T20:00:00Z"}}`

A fixed window has `"mode": "fixed"` and `charge_watts` in place of `ceiling_watts`. An
override's `action` is `self_consumption`, `stop`, `charge` or `discharge`; only the last two
take `watts`. `{}` is no schedule and no override.

## Reading sungrowd-go's formats

We also read what the Go daemon wrote, but never write it:

* `schedule.json`, i.e. `server.ChargeWindow`: `{"enabled": true, "mode": "adaptive",
  "start": "01:00", "end": "06:00", "charge_watts": 0, "ceiling_watts": 4320, "max_soc": 80}`.
  `"enabled": false` is no window; a missing or empty `mode` is fixed.
* `persistedState`, the `state_json` column of its database: `{"charge_window": <schedule>,
  "manual_override": null | {"registers": {…}, "expiry": "<RFC 3339>"}}`.

The key `enabled` marks a Go schedule and `registers` a Go override; neither is in our format.
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

def hasKey (j : Json) (k : String) : Bool := (j.getObjVal? k).isOk

/-- An object with the keys whose values are present. -/
def objOpt (kvs : List (String × Option Json)) : Json :=
  Json.mkObj (kvs.filterMap fun (k, v) => v.map (k, ·))

/-! ## Time of day -/

instance : FromJson TimeOfDay where
  fromJson? j := do
    let s ← j.getStr?
    let some t := TimeOfDay.parse? s | throw s!"invalid time \"{s}\": want HH:MM"
    return t

instance : ToJson TimeOfDay := ⟨fun t => toString t⟩

/-! ## Schedule -/

def fixedMode (w : Nat) : Except String ChargeMode := do
  let some p := ForcedPower.ofWatts? w
    | throw s!"charge watts {w} is greater than the maximum {maxForcedPowerW}"
  if h : 10 ≤ p.watts then pure (ChargeMode.fixed p h)
  else throw s!"charge watts {w} is too low"

def adaptiveMode (c : Nat) : Except String ChargeMode :=
  if h : 100 ≤ c then pure (ChargeMode.adaptive c h)
  else throw s!"adaptive grid ceiling {c} W is too low"

/-- The fields both modes share. `gridFuseAmps` is the one check that needs configuration
(see `ChargeWindow.make?`). The fixed-mode rate is bounded by `ForcedPower` (the inverter's
5000 W rating), where Go uses its configured battery limit. -/
def windowOfJson (gridFuseAmps : Nat) (j : Json) (mode : ChargeMode) :
    Except String ChargeWindow := do
  ChargeWindow.make? (← field TimeOfDay j "start") (← field TimeOfDay j "end") mode
    (← field Nat j "max_soc") gridFuseAmps

def goScheduleKeys : List String :=
  ["enabled", "mode", "start", "end", "charge_watts", "ceiling_watts", "max_soc"]

/-- Go's `ChargeWindow`. Go keeps a disabled window's fields around for the UI, and the field
of the mode not in use, but nothing reads them. -/
def goScheduleOfJson (gridFuseAmps : Nat) (j : Json) : Except String (Option ChargeWindow) := do
  checkKeys "schedule" j goScheduleKeys
  unless ← field Bool j "enabled" do return none
  -- Go's `EffectiveMode`: an empty or missing mode is fixed (rows saved before adaptive existed).
  let mode ← match (← optField String j "mode").getD "" with
    | "" | "fixed" => fixedMode (← field Nat j "charge_watts")
    | "adaptive"   => adaptiveMode ((← optField Nat j "ceiling_watts").getD 0)
    | m            => throw s!"unknown charge mode \"{m}\""
  windowOfJson gridFuseAmps j mode

/-- Our format: each mode has exactly its own power field. -/
def scheduleOfJson (gridFuseAmps : Nat) (j : Json) : Except String ChargeWindow := do
  let common := ["mode", "start", "end", "max_soc"]
  let mode ← match ← field String j "mode" with
    | "fixed" =>
      checkKeys "schedule" j ("charge_watts" :: common)
      fixedMode (← field Nat j "charge_watts")
    | "adaptive" =>
      checkKeys "schedule" j ("ceiling_watts" :: common)
      adaptiveMode (← field Nat j "ceiling_watts")
    | m => throw s!"unknown charge mode \"{m}\""
  windowOfJson gridFuseAmps j mode

/-- A window in either format; Go's has `enabled`, and may be `null` or disabled. -/
def anyScheduleOfJson (gridFuseAmps : Nat) (j : Json) : Except String (Option ChargeWindow) :=
  if j.isNull then pure none
  else if hasKey j "enabled" then goScheduleOfJson gridFuseAmps j
  else some <$> scheduleOfJson gridFuseAmps j

def scheduleJson (w : ChargeWindow) : Json := match w.mode with
  | .fixed p _ => Json.mkObj <|
                    [("mode", "fixed"),
                     ("start", toJson w.start),
                     ("end", toJson w.stop),
                     ("charge_watts", toJson p.watts),
                     ("max_soc", toJson w.maxSOC)]
  | .adaptive c _ => Json.mkObj <|
                      [("mode", "adaptive"),
                       ("start", toJson w.start),
                       ("end", toJson w.stop),
                       ("ceiling_watts", toJson c),
                       ("max_soc", toJson w.maxSOC)]

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

/-- Our format: `watts` for a charge or discharge, and only then. -/
def actionOfJson (j : Json) : Except String Action := do
  let power : Except String ForcedPower := do
    let w ← field Nat j "watts"
    let some p := ForcedPower.ofWatts? w
      | throw s!"watts {w} is greater than the maximum {maxForcedPowerW}"
    return p
  let noPower := checkKeys "override" j ["action", "expiry"]
  let withPower := checkKeys "override" j ["action", "watts", "expiry"]
  match ← field String j "action" with
  | "self_consumption" => do noPower;   pure .selfConsumption
  | "stop"             => do noPower;   pure .stop
  | "charge"           => do withPower; .charge <$> power
  | "discharge"        => do withPower; .discharge <$> power
  | a                  => throw s!"unknown action \"{a}\""

def actionFields : Action → List (String × Json)
  | .selfConsumption => [("action", "self_consumption")]
  | .stop            => [("action", "stop")]
  | .charge p        => [("action", "charge"),    ("watts", toJson p.watts)]
  | .discharge p     => [("action", "discharge"), ("watts", toJson p.watts)]

instance : ToJson ManualOverride where
  toJson o := Json.mkObj <|
    actionFields o.action
    ++ (o.expiry.map fun t => [("expiry", toJson (rfc3339OfUnix t))]).getD []

/-- An override in either format; Go's has `registers`, and may be `null`. -/
def overrideOfJson (j : Json) : Except String (Option ManualOverride) := do
  if j.isNull then return none
  let action ← if hasKey j "registers" then do
      checkKeys "override" j ["registers", "expiry"]
      Action.ofRegisters <$> registersOfJson (← field Json j "registers")
    else actionOfJson j
  let expiry ← match ← optField String j "expiry" with
    | some s => some <$> unixOfRFC3339 s
    | none   => pure none
  return some { action, expiry }

/-! ## Intent -/

instance : ToJson Intent where
  toJson i := objOpt [
    ("charge_window",   i.window.map scheduleJson),
    ("manual_override", i.override.map toJson)]

/-- Ours, or Go's `persistedState`. -/
def intentOfJson (gridFuseAmps : Nat) (j : Json) : Except String Intent := do
  checkKeys "intent" j ["charge_window", "manual_override"]
  let window   ← anyScheduleOfJson gridFuseAmps (j.getObjValD "charge_window")
    |>.mapError (s!"charge_window: {·}")
  let override ← overrideOfJson (j.getObjValD "manual_override")
    |>.mapError (s!"manual_override: {·}")
  return { window, override }

/-- An intent file: ours, Go's `persistedState`, or Go's bare `schedule.json` (which has
`enabled`). -/
def intentOfFile (gridFuseAmps : Nat) (j : Json) : Except String Intent := do
  if j.isNull then return { window := none, override := none }
  if hasKey j "enabled" then
    return { window := ← goScheduleOfJson gridFuseAmps j, override := none }
  intentOfJson gridFuseAmps j

/-! ## Controller state

Not a Go format: Go keeps this in memory. Persisting it lets a `tick` run from cron or a shell
loop behave like one long-running daemon (the latch holds, the adaptive ramp continues). -/

instance : ToJson ControllerState where
  toJson st := objOpt [
    ("target_reached", some (toJson st.targetReached)),
    ("setpoint_w",     some (toJson st.setpointW)),
    ("cmd_w",          some (toJson st.cmdW)),
    ("last_intent",    st.lastIntent.map toJson)]

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

/-! ### Go's formats -/

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
  | .ok { window := none, override := some { action, expiry := some t } } =>
    action == .stop && t == 1792958400
  | _ => false

-- Go allows self consumption with a leftover command and power; they mean nothing.
#guard match parse "{\"charge_window\": null, \"manual_override\": {\"registers\":
    {\"ems_mode\": 0, \"ems_command\": 170, \"forced_power_w\": 3000}}}" >>= intentOfFile 20 with
  | .ok { override := some { action := .selfConsumption, expiry := none }, .. } => true
  | _ => false

#guard (parse "{\"charge_window\": null, \"manual_override\": null}" >>= intentOfFile 20).toOption
  == some { window := none, override := none }

/-! ### Ours -/

#guard (unixOfRFC3339 (rfc3339OfUnix 1792958400)).toOption == some 1792958400

#guard (parse "{}" >>= intentOfFile 20).toOption == some { window := none, override := none }
#guard (toJson ({ window := none, override := none } : Intent)).compress == "{}"

#guard match parse "{\"charge_window\": {\"mode\": \"adaptive\", \"start\": \"01:00\",
    \"end\": \"06:00\", \"ceiling_watts\": 4320, \"max_soc\": 80}, \"manual_override\":
    {\"action\": \"charge\", \"watts\": 3000, \"expiry\": \"2026-11-23T20:00:00Z\"}}"
    >>= intentOfFile 20 with
  | .ok { window := some { mode := .adaptive 4320 _, .. },
          override := some { action := .charge p, expiry := some _ } } => p.watts == 3000
  | _ => false

-- A power where nothing uses one, the other mode's power, or a missing mode is an error.
#guard err? (parse "{\"manual_override\": {\"action\": \"stop\", \"watts\": 0}}"
    >>= intentOfFile 20) == some "manual_override: override: unknown field \"watts\""
#guard err? (parse "{\"charge_window\": {\"mode\": \"adaptive\", \"start\": \"01:00\",
    \"end\": \"06:00\", \"charge_watts\": 0, \"ceiling_watts\": 4320, \"max_soc\": 80}}"
    >>= intentOfFile 20) == some "charge_window: schedule: unknown field \"charge_watts\""
#guard err? (parse "{\"charge_window\": {\"start\": \"00:00\", \"end\": \"06:00\",
    \"charge_watts\": 800, \"max_soc\": 40}}" >>= intentOfFile 20)
  == some "charge_window: missing field \"mode\""

-- What we write, we read back.
#guard
  let i : Intent := { window := none, override := some ⟨.selfConsumption, some 1792958400⟩ }
  (intentOfJson 20 (toJson i)).toOption == some i

/-- Parse an intent (in either format), write it, read it back: the same intent. -/
private def roundTrips (s : String) : Bool :=
  match parse s >>= intentOfFile 20 with
  | .ok i    => (intentOfJson 20 (toJson i)).toOption == some i
  | .error _ => false

#guard roundTrips "{\"enabled\": true, \"start\": \"00:00\", \"end\": \"06:00\",
    \"charge_watts\": 800, \"max_soc\": 40}"
#guard roundTrips "{\"enabled\": true, \"mode\": \"adaptive\", \"start\": \"01:00\",
    \"end\": \"06:00\", \"ceiling_watts\": 4320, \"max_soc\": 80}"
#guard roundTrips "{\"manual_override\": {\"action\": \"discharge\", \"watts\": 2500}}"
#guard roundTrips "{\"charge_window\": {\"enabled\": false}, \"manual_override\":
    {\"registers\": {\"ems_mode\": 2, \"ems_command\": 170, \"forced_power_w\": 3000},
     \"expiry\": \"2026-11-24T06:00:00+10:00\"}}"

-- Controller state round-trips, and an off-ladder command is rejected.
#guard
  let st : ControllerState := { targetReached := true, setpointW := 1234, cmdW := 1200 }
  (controllerStateOfJson 20 (toJson st)).toOption.map (·.cmdW) == some 1200
#guard (toJson ({} : ControllerState)).compress == "{\"cmd_w\":0,\"setpoint_w\":0,\"target_reached\":false}"
#guard err? (parse "{\"target_reached\": false, \"setpoint_w\": 0, \"cmd_w\": 150}"
    >>= controllerStateOfJson 20) == some "cmd_w 150 is not a multiple of 100 in 0..5000"

end Sungrowd.Policy
