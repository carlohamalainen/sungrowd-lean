import Sungrowd.Store
import Sungrowd.HttpClient
import Sungrowd.Format
import Sungrowd.Log

/-! # Solcast PV forecasts: Go's `solcast` package

`POST /solcast` (a systemd timer, as for Go) downloads the rooftop site's forecast, and stores the
raw JSON and its half-hour periods in Go's `solcast_raw` and `solcast_forecast` tables. Reads
take the freshest download that covers a whole local day, and apply the site correction on the
way out; stored forecasts are never changed.

Forecast values are floats, as in Go and in the `REAL` columns; they become exact decimals only
to be printed. -/

namespace Sungrowd

open Lean (Json JsonNumber ToJson toJson)
open Sungrowd.Policy (unixOfRFC3339 rfc3339OfUnix)
open Sungrowd.Inverter (brisbaneOffsetS)

def solcastKeyEnvVar      : String := "SOLCAST_API_KEY"
def solcastResourceEnvVar : String := "SOLCAST_RESOURCE_ID"

/-! ## Parsing -/

/-- Go's `parseISOMinutes`: `"PT30M"`, `"PT1H"`, `"PT1H30M"` in whole minutes. -/
def parseISOMinutes (s : String) : Except String Nat := do
  let some rest := s.dropPrefix? "PT" | throw "not a PT duration"
  let rest := rest.toString
  let atoi (t : String) : Except String Nat :=
    match t.toNat? with
    | some n => pure n
    | none   => throw s!"strconv.Atoi: parsing \"{t}\": invalid syntax"
  let (hours, rest) ← match rest.splitOn "H" with
    | [h, after] => pure (← atoi h, after)
    | _          => pure (0, rest)
  let mins ← match rest.splitOn "M" with
    | m :: _ :: _ => if m.isEmpty then pure 0 else atoi m
    | _           => pure 0
  let total := hours * 60 + mins
  if total == 0 then throw s!"parsed zero minutes from \"{s}\""
  return total

-- Go's `TestParseISOMinutes`.
#guard [("PT5M", 5), ("PT30M", 30), ("PT1H", 60), ("PT1H30M", 90)].all fun (s, n) =>
  (parseISOMinutes s).toOption == some n
#guard ["", "30M", "PT", "PT0M", "PTxM"].all fun s => (parseISOMinutes s).toOption.isNone

/-- Go's `Period`: one half-hour row, normalised for storage. kW. -/
structure Period where
  periodEnd : String  -- RFC 3339, UTC
  minutes   : Nat
  p50       : Float
  p10       : Float
  p90       : Float

private def numField (j : Json) (k : String) : Float :=
  match j.getObjValD k with
  | .num n => n.toFloat
  | _      => 0  -- Go's zero value for a missing field

/-- Go's `ParseForecasts`: `period_end` re-formatted to RFC 3339 UTC (Solcast sends 7-digit
fractional seconds), the ISO duration in minutes. -/
def parseForecasts (raw : String) : Except String (Array Period) := do
  let j ← Json.parse raw |>.mapError (s!"decode solcast json: {·}")
  let forecasts := match j.getObjValD "forecasts" with
    | .arr a => a
    | _      => #[]
  forecasts.mapM fun e => do
    let endS := (e.getObjValAs? String "period_end").toOption.getD ""
    let t ← unixOfRFC3339 endS |>.mapError (s!"period_end \"{endS}\": {·}")
    let periodS := (e.getObjValAs? String "period").toOption.getD ""
    let minutes ← parseISOMinutes periodS |>.mapError (s!"period \"{periodS}\": {·}")
    return { periodEnd := rfc3339OfUnix t, minutes,
             p50 := numField e "pv_estimate", p10 := numField e "pv_estimate10",
             p90 := numField e "pv_estimate90" }

-- Go's `TestParseForecasts`.
#guard match parseForecasts "{\"forecasts\":[
    {\"pv_estimate\":1.5,\"pv_estimate10\":0.5,\"pv_estimate90\":2.5,\"period_end\":\"2026-06-10T00:30:00.0000000Z\",\"period\":\"PT30M\"},
    {\"pv_estimate\":2.0,\"pv_estimate10\":1.0,\"pv_estimate90\":3.0,\"period_end\":\"2026-06-10T11:00:00+10:00\",\"period\":\"PT30M\"}]}" with
  | .ok #[p, q] =>
    p.periodEnd == "2026-06-10T00:30:00Z" && p.minutes == 30 &&
    p.p50 == 1.5 && p.p10 == 0.5 && p.p90 == 2.5 && q.periodEnd == "2026-06-10T01:00:00Z"
  | _ => false
#guard ["not json",
        "{\"forecasts\":[{\"period_end\":\"yesterday\",\"period\":\"PT30M\"}]}",
        "{\"forecasts\":[{\"period_end\":\"2026-06-10T00:30:00Z\",\"period\":\"30 minutes\"}]}"].all
  fun s => (parseForecasts s).toOption.isNone

/-! ## A day's forecast -/

/-- Go's `DayPeriod`: one half-hour estimate (kW), by its local start time. -/
structure DayPeriod where
  time : String  -- local "HH:MM"
  p10  : Float
  p50  : Float
  p90  : Float

/-- Go's `DayForecast`: a local day's half-hour curve, daily totals (kWh) and peak P50 (kW). -/
structure DayForecast where
  date        : String
  totalKWhP50 : Float := 0
  totalKWhP10 : Float := 0
  totalKWhP90 : Float := 0
  peakKWP50   : Float := 0
  /-- The site-corrected total; zero without a correction. -/
  expectedKWh : Float := 0
  /-- The factor that gave `expectedKWh`; zero without a correction. -/
  scale       : Float := 0
  /-- Solcast's own spread is wide (P10 under a fraction of P50): a cloud risk. -/
  uncertain   : Bool := false
  periods     : Array DayPeriod := #[]

/-- Go's `round3`. -/
def round3 (v : Float) : Float := (v * 1000).round / 1000

/-- A float as an exact decimal, to `places` (Go prints the shortest float, which for these
values, kW to four places and totals to three, is the same). -/
def Dec.ofFloat (x : Float) (places : Nat := 6) : Dec :=
  ⟨(x * (10 ^ places).toFloat).round.toInt64.toInt, places⟩

def floatJson (x : Float) : Json := (Dec.ofFloat x).toJson

instance : ToJson DayPeriod where
  toJson p := Json.mkObj [("time", p.time), ("p10", floatJson p.p10), ("p50", floatJson p.p50),
                          ("p90", floatJson p.p90)]

instance : ToJson DayForecast where
  toJson d := Json.mkObj [
    ("date", d.date), ("total_kwh_p50", floatJson d.totalKWhP50),
    ("total_kwh_p10", floatJson d.totalKWhP10), ("total_kwh_p90", floatJson d.totalKWhP90),
    ("peak_kw_p50", floatJson d.peakKWP50), ("expected_kwh", floatJson d.expectedKWh),
    ("scale", floatJson d.scale), ("uncertain", toJson d.uncertain),
    ("periods", toJson d.periods)]

/-- Go's `Correction`, fitted to day-ahead downloads against the PV counter (26 Aug – 9 Sep
2026): actual / P50 had median 0.62, and days where Solcast itself was unsure (P10 under half
of P50) varied too much to get a factor of their own, so they are flagged instead. -/
structure Correction where
  /-- Multiplies the P50 total to give `expectedKWh`; ≤ 0 is off. -/
  scale          : Float := 0.62
  /-- A day is uncertain when its P10 total is under this fraction of its P50 total. -/
  uncertainRatio : Float := 0.5

def Correction.enabled (c : Correction) : Bool := c.scale > 0

/-- Go's `Apply`. -/
def Correction.apply (c : Correction) (d : DayForecast) : DayForecast :=
  if !c.enabled then d else
  { d with scale := c.scale, expectedKWh := round3 (d.totalKWhP50 * c.scale),
           uncertain := c.uncertainRatio > 0 && d.totalKWhP10 < c.uncertainRatio * d.totalKWhP50 }

-- Go's `TestCorrectionApply`.
#guard
  let c : Correction := {}
  let clear := c.apply { date := "", totalKWhP10 := 19.4, totalKWhP50 := 19.7, totalKWhP90 := 19.8 }
  let cloudy := c.apply { date := "", totalKWhP10 := 5.6, totalKWhP50 := 15.4, totalKWhP90 := 19.9 }
  let edge := c.apply { date := "", totalKWhP10 := 5, totalKWhP50 := 10 }
  let off := ({ scale := 0, uncertainRatio := 0 } : Correction).apply { date := "", totalKWhP10 := 1, totalKWhP50 := 10 }
  let noFlag := ({ scale := 0.5, uncertainRatio := 0 } : Correction).apply { date := "", totalKWhP10 := 1, totalKWhP50 := 10 }
  clear.expectedKWh == 12.214 && clear.scale == 0.62 && !clear.uncertain &&
  cloudy.expectedKWh == 9.548 && cloudy.uncertain &&
  !edge.uncertain &&
  off.expectedKWh == 0 && off.scale == 0 && !off.uncertain &&
  noFlag.expectedKWh == 5 && !noFlag.uncertain

/-! ## Storage -/

/-- Go's `InsertSolcastForecast`: the raw response and its periods, in one transaction. -/
def Store.insertSolcastForecast (s : Store) (recordedAt resourceId raw : String)
    (periods : Array Period) : IO Int64 :=
  s.db.transaction do
    s.db exec!"INSERT INTO solcast_raw(recorded_at, solcast_resource_id, raw_json)
      VALUES ({recordedAt}, {resourceId}, {raw})"
    let id ← s.db.lastInsertRowId
    for p in periods do
      let minutes : Int64 := p.minutes.toInt64
      s.db exec!"INSERT INTO solcast_forecast(download_id, period_end, period_minutes, pv_estimate, pv_estimate10, pv_estimate90)
        VALUES ({id}, {p.periodEnd}, {minutes}, {p.p50}, {p.p10}, {p.p90})"
    return id

/-- Brisbane has no daylight saving, so every local day has 48 half-hours: a download that has
all of them covers the day. -/
def periodsPerDay : Int64 := 48

/-- Go's `ForecastForDay`: the latest download that covers the whole local day, so a download
made mid-day backfills to an earlier one for the hours it lacks. Periods are attributed to
days by their local start. None if no download covers the day. -/
def Store.forecastForDay (s : Store) (day : Int) : IO (Option DayForecast) := do
  let date := dateString day
  -- SQLite has no time zones: shift the UTC period end by the fixed offset, then back off the
  -- period's length, to get the local day of its start. Go's SQL, verbatim.
  let modifier := s!"+{brisbaneOffsetS} seconds"
  let ids ← (← s.db query!"SELECT download_id FROM solcast_forecast
      WHERE date(datetime(period_end, {modifier}, '-'||period_minutes||' minutes')) = {date}
      GROUP BY download_id HAVING COUNT(*) >= {periodsPerDay}
      ORDER BY download_id DESC LIMIT 1" as Int64).toList
  let [download] := ids | return none
  let rows ← (← s.db query!"SELECT period_end, period_minutes, pv_estimate, pv_estimate10, pv_estimate90
      FROM solcast_forecast
      WHERE download_id = {download} AND date(datetime(period_end, {modifier}, '-'||period_minutes||' minutes')) = {date}
      ORDER BY period_end" as (String × Int64 × Float × Float × Float)).toList
  let mut d : DayForecast := { date }
  for (endS, mins, p50, p10, p90) in rows do
    let .ok stop := unixOfRFC3339 endS | continue
    let hours := mins.toFloat / 60
    d := { d with
      totalKWhP50 := d.totalKWhP50 + p50 * hours
      totalKWhP10 := d.totalKWhP10 + p10 * hours
      totalKWhP90 := d.totalKWhP90 + p90 * hours
      peakKWP50   := if p50 > d.peakKWP50 then p50 else d.peakKWP50
      periods     := d.periods.push ⟨brisbaneClock (stop - mins.toInt * 60), p10, p50, p90⟩ }
  return some { d with totalKWhP50 := round3 d.totalKWhP50, totalKWhP10 := round3 d.totalKWhP10,
                       totalKWhP90 := round3 d.totalKWhP90 }

/-! ## Fetching -/

/-- Go's `Fetch`: the rooftop site's forecast, raw. 30 s, Go's `FetchSolcast` deadline. -/
def solcastFetch (resourceId apiKey : String) : IO (Except String String) := do
  let url := s!"https://api.solcast.com.au/rooftop_sites/{resourceId}/forecasts?format=json"
  match ← httpRequest "GET" url (headers := [("Authorization", s!"Bearer {apiKey}")]) (timeoutS := 30) with
  | .error e => return .error e
  | .ok r =>
    if r.status != 200 then return .error s!"solcast HTTP {r.status}: {snippet r.body}"
    return .ok r.body

/-- Go's `FetchSolcast`: download, parse and store the forecast; the new download's id. -/
def Store.fetchSolcast (s : Store) (log : Log) (resourceId apiKey : String) :
    IO (Except String Int64) := do
  log.debug "fetching solcast forecast" [("resource_id", resourceId)]
  let raw ← match ← solcastFetch resourceId apiKey with
    | .ok raw  => pure raw
    | .error e => return .error s!"fetch solcast: {e}"
  let periods ← match parseForecasts raw with
    | .ok ps   => pure ps
    | .error e => return .error s!"parse solcast: {e}"
  log.debug "solcast forecast fetched" [("bytes", toString raw.utf8ByteSize), ("periods", toString periods.size)]
  try
    return .ok (← s.insertSolcastForecast (← nowRFC3339) resourceId raw periods)
  catch e => return .error s!"store solcast: {e}"

end Sungrowd
