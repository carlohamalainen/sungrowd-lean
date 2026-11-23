import Std.Http
import Sungrowd.Daemon

/-! # The daemon's HTTP endpoints: `/metrics` and `/healthz`, as in Go -/

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

def httpHandler (shared : IO.Ref Shared) (thresholdS : Nat) : Http.Server.StatelessHandler where
  onRequest req := do
    let s ← shared.get
    match toString req.line.uri.pathOrRoot with
    | "/metrics" =>
      Http.Response.ok
        |>.header! "Content-Type" "text/plain; version=0.0.4; charset=utf-8"
        |>.fromBytes (metricsText s).toUTF8
    | "/healthz" =>
      let nowMs := (← Std.Time.Timestamp.now).toMillisecondsSinceUnixEpoch.val
      let (ok, body) := healthJson s nowMs thresholdS
      (if ok then Http.Response.ok else Http.Response.serviceUnavailable) |>.json body
    | _ => Http.Response.notFound |>.text "404 page not found\n"

/-- `host:port`, e.g. `0.0.0.0:9180`. -/
def parseListen (s : String) : Except String (String × UInt16) :=
  match s.splitOn ":" with
  | [h, p] => match p.toNat? with
    | some n => if n < UInt16.size then pure (h, n.toUInt16) else throw s!"port {p} is out of range"
    | none   => throw s!"port {p} is not a number"
  | _ => throw s!"{s}: expected host:port"

/-! ## Examples -/

-- Before any read: only the error counter.
#guard metricsText {} == "# HELP solar_modbus_read_errors_total Failed sensor-block reads (after retries) since the daemon started\n# TYPE solar_modbus_read_errors_total counter\nsolar_modbus_read_errors_total 0\n"
#guard ((metricsText { control := some (#v[2, 170, 500], 0) }).splitOn "\n").contains "solar_forced_active 1"

#guard healthJson {} 1000 120 == (false, "{\"last_read_age_seconds\":null,\"status\":\"stale\",\"threshold_seconds\":120}")
#guard healthJson { lastReadMs := some 0 } 3200 120 == (true, "{\"last_read_age_seconds\":3.2,\"status\":\"ok\",\"threshold_seconds\":120}")
#guard (healthJson { lastReadMs := some 0 } 120_001 120).1 == false

#guard (parseListen "0.0.0.0:9180").toOption == some ("0.0.0.0", 9180)
#guard (parseListen "0.0.0.0").toOption.isNone

end Sungrowd
