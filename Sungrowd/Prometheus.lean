import Sungrowd.Format
import Sungrowd.Log

/-! # Actual generation and SOC history, from Prometheus: Go's `promquery` and the server's
`Actual…` queries

Optional: with `SUNGROWD_PROMETHEUS_URL` set (the Prometheus that scrapes this daemon's
`/metrics`), the UI shows SOC history and forecast vs actual, and `/actual` serves daily PV
generation.

The client is read only, two calls of the HTTP API (`/api/v1/query` and `/api/v1/query_range`),
run with `curl`, which URL-encodes the parameters. Values stay exact decimals: Prometheus sends
them as strings like `"54.3"` or `"1.2345e+03"`. -/

namespace Sungrowd

open Lean (Json)

def prometheusEnvVar : String := "SUNGROWD_PROMETHEUS_URL"

/-- Go's metric names for the actuals. -/
def pvTotalMetric : String := "solar_pv_kwh_total"  -- lifetime cumulative kWh (counter)
def socMetric     : String := "solar_battery_soc_percent"

structure Prom where
  /-- e.g. `http://localhost:9090`, without a trailing slash. -/
  base : String

/-- Go's `promquery.New`, if `SUNGROWD_PROMETHEUS_URL` is set. -/
def Prom.ofEnv (log : Log) : IO (Option Prom) := do
  let some u ← IO.getEnv prometheusEnvVar | return none
  if u.isEmpty then return none
  log.info "prometheus configured for actuals" [("url", u)]
  return some ⟨String.ofList (u.toList.reverse.dropWhile (· == '/')).reverse⟩

/-- Go's `snippet`: the first 200 characters of an error body. -/
private def snippet (s : String) : String := String.ofList (s.toList.take 200)

/-- Go's `get`: the `data.result` of a successful API call. A 10 s timeout, as Go's client. -/
def Prom.get (p : Prom) (path : String) (params : List (String × String)) :
    ExceptT String IO Json := do
  let encoded := params.foldl (fun acc (k, v) => acc ++ #["--data-urlencode", s!"{k}={v}"]) #[]
  let out ← (IO.Process.output {
      cmd := "curl",
      args := #["-sS", "--max-time", "10", "-G", "-w", "\n%{http_code}"] ++ encoded ++ #[p.base ++ path] }
    : IO _)
  if out.exitCode != 0 then throw out.stderr.trimAscii.toString  -- curl says "curl: (7) …"
  -- The body, then the status on its own line.
  let lines := out.stdout.splitOn "\n"
  let status := lines.getLast?.getD ""
  let body := "\n".intercalate lines.dropLast
  if status != "200" then throw s!"prometheus HTTP {status}: {snippet body}"
  let resp ← match Json.parse body with
    | .ok j    => pure j
    | .error e => throw s!"decode prometheus response: {e}"
  if resp.getObjValD "status" != .str "success" then
    throw s!"prometheus query failed: {(resp.getObjValAs? String "error").toOption.getD ""}"
  return (resp.getObjValD "data").getObjValD "result"

/-- Go's `parsePair`: `[ts, "value"]`, with the timestamp in whole seconds. -/
def parsePair : Json → Option (Int × Dec)
  | .arr #[ts, v] => do return ((← Dec.ofJson? ts).floor, ← Dec.ofJson? v)
  | _             => none

#guard (parsePair (Json.arr #[.num ⟨17954122495, 1⟩, .str "54.3"])).map (fun (t, v) => (t, v.fixed 1))
  == some (1795412249, "54.3")

/-- Go's `Instant`: the first series' value at `t`; none if the query matched nothing. -/
def Prom.instant (p : Prom) (query : String) (t : Int) : ExceptT String IO (Option Dec) := do
  let result ← p.get "/api/v1/query" [("query", query), ("time", toString t)]
  let .arr results := result | throw "decode vector: not an array"
  let some first := results[0]? | return none
  let some (_, v) := parsePair (first.getObjValD "value") | throw "decode value: not [ts, \"v\"]"
  return some v

/-- Go's `Range`: the first series' samples over `[start, stop]` every `stepS` seconds. Samples
that don't parse are skipped, as in Go. -/
def Prom.range (p : Prom) (query : String) (start stop : Int) (stepS : Nat) :
    ExceptT String IO (Array (Int × Dec)) := do
  let result ← p.get "/api/v1/query_range"
    [("query", query), ("start", toString start), ("end", toString stop), ("step", toString stepS)]
  let .arr results := result | throw "decode matrix: not an array"
  let some first := results[0]? | return #[]
  let .arr values := first.getObjValD "values" | throw "decode values: not an array"
  return values.filterMap parsePair

/-! ## Go's actuals -/

/-- Go's `pvDelta`: the lifetime PV counter's increase between two instants, to 0.1 kWh. None
if either end has no data. -/
def Prom.pvDelta (p : Prom) (start stop : Int) : ExceptT String IO (Option Dec) := do
  let some beg ← p.instant pvTotalMetric start | return none
  let some fin ← p.instant pvTotalMetric stop  | return none
  let d := fin - beg
  let d := if d.isNeg then ⟨0, 0⟩ else d  -- a counter reset within the window
  return some ⟨d.roundMul 10, 1⟩

/-- Go's `ActualPVForDay`: kWh generated on a local day, `[00:00, next 00:00)`. -/
def Prom.actualPVForDay (p : Prom) (day : Int) : ExceptT String IO (Option Dec) :=
  p.pvDelta (brisbaneMidnight day) (brisbaneMidnight (day + 1))

/-- Go's `ActualSOCCurve`: the SOC (%) across a local day every ten minutes, up to now if the
day is still going, by minute of the day (the next midnight is 1440, not 0). -/
def Prom.socCurve (p : Prom) (day nowUnix : Int) : ExceptT String IO (Array (Nat × Dec)) := do
  let start := brisbaneMidnight day
  let stop := min (brisbaneMidnight (day + 1)) nowUnix
  if stop ≤ start then return #[]
  let pts ← p.range socMetric start stop 600
  return pts.map fun (t, v) => ((t - start).toNat / 60, v)

end Sungrowd
