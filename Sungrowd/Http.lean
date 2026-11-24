import Std.Http
import Sungrowd.Daemon
import Sungrowd.Store

/-! # The daemon's HTTP endpoints, as in Go: `/metrics`, `/healthz`, `/diag` and the control API -/

namespace Sungrowd

open Std Async
open Modbus
open Sungrowd.Control
open Sungrowd.Inverter

/-- The Prometheus text format for the last successful read, plus Go's daemon metrics. -/
def metricsText (s : Shared) : String := Id.run do
  let mut out := ""
  let metric (name help kind value : String) : String :=
    s!"# HELP {name} {help}\n# TYPE {name} {kind}\n{name} {value}\n"
  for b in s.blocks.getD #[] do
    for slot in b.slots do
      let some m := metricDefs.find? (·.sensorId == slot.sensor.unique_id) | continue
      let some r := slot.reading | continue
      let some raw := decodeRaw slot.sensor r.raw | continue  -- the NaN sentinel
      out := out ++ metric m.name m.help (toString m.kind) (scaled slot.sensor raw)
  -- EMS mode from the cached control registers; absent until they have been read.
  if let some (v, _) := s.control then
    out := out ++ metric "solar_ems_mode_setpoint"
      "EMS mode setpoint from holding register (0=self-consumption, 2=forced, 3=external EMS)"
      "gauge" (toString v[0])
    out := out ++ metric "solar_forced_active"
      "1 if the inverter is in forced mode (EMS setpoint = 2), else 0"
      "gauge" (if v[0] == 2 then "1" else "0")
  if let some ms := s.lastReadMs then
    out := out ++ metric "solar_last_successful_read_timestamp_seconds"
      "Unix time of the last successful full sensor-block read from the inverter"
      "gauge" (toString (ms / 1000))
  out := out ++ metric "solar_modbus_read_errors_total"
    "Failed sensor-block reads (after retries) since the daemon started"
    "counter" (toString s.readErrors)
  return out

/-- Go's `/healthz` body, and whether it is healthy. -/
def healthJson (s : Shared) (nowMs : Int) (thresholdS : Nat) : Bool × String :=
  let age? := s.lastReadMs.map (nowMs - ·)
  let ok := match age? with
    | some age => age ≤ thresholdS * 1000
    | none     => false
  let ageJson : Lean.Json := match age? with
    | some age => .num ⟨age, 3⟩
    | none     => .null
  (ok, (Lean.Json.mkObj [
    ("status",                if ok then "ok" else "stale"),
    ("last_read_age_seconds", ageJson),
    ("threshold_seconds",     thresholdS)]).compress)

/-- `host:port`, e.g. `0.0.0.0:9180`. -/
def parseListen (s : String) : Except String (String × UInt16) :=
  match s.splitOn ":" with
  | [h, p] => match p.toNat? with
    | some n => if n < UInt16.size then pure (h, n.toUInt16) else throw s!"port {p} is out of range"
    | none   => throw s!"port {p} is not a number"
  | _ => throw s!"{s}: expected host:port"

/-! ## The control API

Go's `/control/override`, `/control/schedule` and `/diag`, with our JSON formats (see
`Sungrowd/Intent.lean`). A change goes through `Store.updateIntent`, so it can't lose a
concurrent change by the worker, and then wakes the worker so it takes effect at once. -/

open Lean (Json ToJson toJson)
open Sungrowd.Policy

/-- The next time the Brisbane clock shows `t`, strictly after `nowUnix`. -/
def nextOccurrence (t : TimeOfDay) (nowUnix : Int) : Int :=
  let localS := nowUnix + brisbaneOffsetS
  let at_ := localS - localS % 86400 + 60 * t.minuteOfDay - brisbaneOffsetS
  if at_ ≤ nowUnix then at_ + 86400 else at_

/-- A request body as JSON; an empty body is `null`. -/
def bodyJson (body : String) : Except String Json :=
  if body.trimAscii.isEmpty then pure .null else Json.parse body

/-- `POST /control/override`: an override in our format, or `null` to clear it. As in Go's
API, `expiry` may also be `"HH:MM"`, the next time the Brisbane clock shows it. -/
def overrideOfRequest (nowUnix : Int) (j : Json) : Except String (Option ManualOverride) := do
  let j := match j.getObjValD "expiry" with
    | .str s => match TimeOfDay.parse? s with
      | some t => j.setObjVal! "expiry" (toJson (rfc3339OfUnix (nextOccurrence t nowUnix)))
      | none   => j
    | _ => j
  let some o ← overrideOfJson j | return none
  if let some e := o.expiry then
    if e ≤ nowUnix then throw s!"expiry {rfc3339OfUnix e} is in the past"
  return some o

/-- `GET /diag`: what the daemon knows, from memory and the database; no inverter I/O. -/
def diagJson (s : Shared) (stored : Except String Intent) : Json := Json.mkObj [
  ("intent", match stored with
    | .ok i    => toJson i
    | .error e => Json.mkObj [("error", toJson e)]),
  ("effective_intent",  toJson s.effective),
  ("decision",          toJson (s.decision.map (·.show))),
  ("controller_state",  toJson s.controller),
  ("control_registers", toJson (s.control.map fun (v, _) => v.toArray.map UInt16.toNat)),
  ("read_errors",       toJson s.readErrors),
  ("last_read_error",   toJson s.lastReadErr),
  ("sensors", Json.mkObj <| Id.run do
    let mut out := []
    for b in s.blocks.getD #[] do
      for slot in b.slots do
        out := out ++ [(slot.sensor.unique_id, toJson slot.display)]
    return out)]

structure Api where
  shared     : IO.Ref Shared
  thresholdS : Nat
  /-- Each request opens its own connection: one connection's transactions would interleave
  with the worker's. -/
  dbPath     : System.FilePath
  fuse       : Nat
  log        : Log
  wake       : Std.Channel Unit

def maxBodyBytes : UInt64 := 65536

def Api.loadIntent (api : Api) : IO (Except String Intent) :=
  try (← Store.open api.dbPath).loadIntent api.fuse
  catch e => pure (.error (toString e))

/-- Change the intent in the database, then wake the worker (without blocking, as Go does). -/
def Api.updateIntent (api : Api) (f : Intent → Intent) : IO (Except String Intent) := do
  let r ← try (← Store.open api.dbPath).updateIntent api.fuse f
    catch e => pure (.error (toString e))
  if r matches .ok _ then discard <| api.wake.trySend ()
  return r

abbrev Reply := Async (Http.Response Http.Body.Full)

def plain (status : Http.Status) (msg : String) : Reply :=
  (Http.Response.withStatus status).text (msg ++ "\n")

/-- The request body as JSON, or a 400. -/
def withBody (body : Http.Body.Stream) (k : Json → Reply) : Reply := do
  let s : Except String String ← try .ok <$> body.readAll (maximumSize := some maxBodyBytes)
    catch e => pure (.error (toString e))
  match s >>= bodyJson with
  | .ok j    => k j
  | .error e => plain .badRequest s!"invalid body: {e}"

/-- Apply `f` to the stored intent: 202 with `echo`, or a 500 if the database fails. -/
def Api.persist (api : Api) (what : String) (f : Intent → Intent) (echo : Json) : Reply := do
  match ← api.updateIntent f with
  | .ok _ =>
    if echo.isNull then api.log.info s!"{what} cleared"
    else api.log.info s!"{what} set" [("value", echo.compress)]
    Http.Response.accepted.json echo.compress
  | .error e =>
    api.log.error s!"could not persist {what}" [("err", e)]
    plain .internalServerError s!"could not persist: {e}"

def Api.respond (api : Api) (req : Http.Request Http.Body.Stream) : Reply := do
  let method := req.line.method
  let notAllowed := plain .methodNotAllowed "method not allowed"
  let s ← api.shared.get
  match toString req.line.uri.pathOrRoot with
  | "/metrics" =>
    Http.Response.ok
      |>.header! "Content-Type" "text/plain; version=0.0.4; charset=utf-8"
      |>.fromBytes (metricsText s).toUTF8
  | "/healthz" =>
    let nowMs := (← Std.Time.Timestamp.now).toMillisecondsSinceUnixEpoch.val
    let (ok, body) := healthJson s nowMs api.thresholdS
    (if ok then Http.Response.ok else Http.Response.serviceUnavailable) |>.json body
  | "/diag" =>
    if method != .get then notAllowed else
    Http.Response.ok.json (diagJson s (← api.loadIntent)).pretty
  | "/control/override" =>
    if method != .post then notAllowed else
    withBody req.body fun j => do
      let nowUnix := (← Std.Time.Timestamp.now).toSecondsSinceUnixEpoch.val
      match overrideOfRequest nowUnix j with
      | .error e => plain .badRequest e
      | .ok o    => api.persist "manual override" ({ · with override := o }) (toJson o)
  | "/control/schedule" =>
    if method != .post then notAllowed else
    withBody req.body fun j =>
      match anyScheduleOfJson api.fuse j with
      | .error e => plain .badRequest e
      | .ok w    => api.persist "charge window" ({ · with window := w }) (toJson (w.map scheduleJson))
  | _ => plain .notFound "404 page not found"

/-! ## Examples -/

-- Before any read: only the error counter.
#guard metricsText {} == "# HELP solar_modbus_read_errors_total Failed sensor-block reads (after retries) since the daemon started\n# TYPE solar_modbus_read_errors_total counter\nsolar_modbus_read_errors_total 0\n"
#guard ((metricsText { control := some (#v[2, 170, 500], 0) }).splitOn "\n").contains "solar_forced_active 1"

#guard healthJson {} 1000 120 == (false, "{\"last_read_age_seconds\":null,\"status\":\"stale\",\"threshold_seconds\":120}")
#guard healthJson { lastReadMs := some 0 } 3200 120 == (true, "{\"last_read_age_seconds\":3.2,\"status\":\"ok\",\"threshold_seconds\":120}")
#guard (healthJson { lastReadMs := some 0 } 120_001 120).1 == false

#guard (parseListen "0.0.0.0:9180").toOption == some ("0.0.0.0", 9180)
#guard (parseListen "0.0.0.0").toOption.isNone


-- 06:00 in Brisbane, on the 24th.
private def sixAM : Int := 1795464000
#guard rfc3339OfUnix sixAM == "2026-11-23T20:00:00Z"
private def at_ (h m : Nat) (hh : h < 24 := by decide) (hm : m < 60 := by decide) : String :=
  rfc3339OfUnix (nextOccurrence ⟨h, m, hh, hm⟩ sixAM)
#guard at_ 7 0 == "2026-11-23T21:00:00Z"   -- later today
#guard at_ 5 0 == "2026-11-24T19:00:00Z"   -- tomorrow
#guard at_ 6 0 == "2026-11-24T20:00:00Z"   -- now is not the next occurrence

-- The echoed override, or `none` for a 400.
private def req (s : String) : Option String :=
  ((bodyJson s >>= overrideOfRequest sixAM).map fun o => (toJson o).compress).toOption
#guard req "" == some "null"
#guard req " null\n" == some "null"
#guard req "{\"action\": \"charge\", \"watts\": 3000, \"expiry\": \"07:30\"}"
  == some "{\"action\":\"charge\",\"expiry\":\"2026-11-23T21:30:00Z\",\"watts\":3000}"
#guard req "{\"action\": \"stop\", \"expiry\": \"2026-11-23T21:00:00Z\"}"
  == some "{\"action\":\"stop\",\"expiry\":\"2026-11-23T21:00:00Z\"}"
#guard req "{\"action\": \"stop\", \"expiry\": \"2026-11-23T19:00:00Z\"}" == none  -- past
#guard req "{\"action\": \"charge\"}" == none                                     -- no watts
#guard req "{\"action\": \"stop\", \"expiry\": \"25:00\"}" == none
#guard req "{" == none

end Sungrowd
