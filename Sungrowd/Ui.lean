import Datastar
import Sungrowd.Http

/-! # The web UI: Go's `ui.go`

The page is Go's `index.html`, verbatim (`ui/index.html`), with its two template values filled
in, and Go's vendored Datastar bundle (`ui/datastar.js`). The fragments the server patches in
are Go's, character for character: the same elements, classes and format strings.

Everything goes through the Datastar SDK: `sseResponse` for the streams, `patchElements` and
`patchSignals` for the events, `readSignals` for what the page sends.

Not ported yet: the forecast, forecast-vs-actual and SOC-history panels need Solcast and
Prometheus, so they show what Go shows without them. -/

namespace Sungrowd

open Std Async Http
open Lean (Json JsonNumber toJson)
open Datastar
open Sungrowd.Policy Sungrowd.Control Sungrowd.Inverter
open Modbus (msOffset)

/-! ## Go's formatting, exactly -/

/-- Go's `%.{places}f` of `num / den`, or `%+.{places}f` with `plus`. Exact, rounding half away
from zero, where Go rounds the nearest float. A negative value keeps its sign even when it rounds
to zero, as Go's does: `-0.00`. -/
def fixedFrac (num : Int) (den : Nat) (places : Nat) (plus : Bool := false) : String :=
  let sign := if num < 0 then "-" else if plus then "+" else ""
  let scaled := (2 * num.natAbs * 10 ^ places + den) / (2 * den)
  sign ++ withDecimals scaled places

/-- An exact decimal, `m × 10^-e`, so the UI never needs a float. -/
structure Dec where
  m : Int
  e : Nat := 0
  deriving Repr

namespace Dec

def ofJsonNumber (n : JsonNumber) : Dec := ⟨n.mantissa, n.exponent⟩

def align (a b : Dec) : Int × Int × Nat :=
  let e := max a.e b.e
  (a.m * 10 ^ (e - a.e), b.m * 10 ^ (e - b.e), e)

instance : Add Dec := ⟨fun a b => let (x, y, e) := a.align b; ⟨x + y, e⟩⟩
instance : Sub Dec := ⟨fun a b => let (x, y, e) := a.align b; ⟨x - y, e⟩⟩

def lt (a b : Dec) : Bool := let (x, y, _) := a.align b; x < y

/-- `a / 10^k`. -/
def shift (a : Dec) (k : Nat) : Dec := ⟨a.m, a.e + k⟩

/-- `round(a × k)`, half away from zero. -/
def roundMul (a : Dec) (k : Nat) : Int :=
  let q := (2 * a.m.natAbs * k + 10 ^ a.e) / (2 * 10 ^ a.e)
  if a.m < 0 then -q else q

/-- Go's `%.{places}f`. -/
def fixed (a : Dec) (places : Nat) (plus : Bool := false) : String :=
  fixedFrac a.m (10 ^ a.e) places plus

/-- Go's `%v` (and `%g`, for these values): no trailing zeros. -/
partial def short (a : Dec) : String :=
  if a.e > 0 && a.m % 10 == 0 then short ⟨a.m / 10, a.e - 1⟩ else withDecimals a.m a.e

def toJson (a : Dec) : Json := .num ⟨a.m, a.e⟩

end Dec

#guard fixedFrac 1234 1000 2 == "1.23"
#guard fixedFrac (-1) 1000 2 (plus := true) == "-0.00"
#guard fixedFrac 0 1000 2 (plus := true) == "+0.00"
#guard fixedFrac 4320 240 1 == "18.0"
#guard (Dec.mk 50 1).short == "5" && (Dec.mk 58 1).short == "5.8" && (Dec.mk 20 0).short == "20"
#guard (Dec.mk 15 1).roundMul 1000 == 1500

/-- Go's `html.EscapeString`. -/
def htmlEscape (s : String) : String :=
  s.foldl (init := "") fun acc c => acc ++ match c with
    | '<'  => "&lt;"
    | '>'  => "&gt;"
    | '&'  => "&amp;"
    | '\'' => "&#39;"
    | '"'  => "&#34;"
    | c    => c.toString

#guard htmlEscape "a<b & \"c\"" == "a&lt;b &amp; &#34;c&#34;"

/-! ### Brisbane wall-clock time -/

private def two (n : Nat) : String := if n < 10 then s!"0{n}" else toString n

/-- Day of month and month (1–12) of a day number since 1970-01-01 (Hinnant's `civil_from_days`). -/
def dayMonth (days : Int) : Nat × Nat :=
  let z := days + 719468
  let era := z / 146097
  let doe := z - era * 146097
  let yoe := (doe - doe / 1460 + doe / 36524 - doe / 146096) / 365
  let doy := doe - (365 * yoe + yoe / 4 - yoe / 100)
  let mp := (5 * doy + 2) / 153
  let d := doy - (153 * mp + 2) / 5 + 1
  let m := if mp < 10 then mp + 3 else mp - 9
  (d.toNat, m.toNat)

/-- Go's layout `"15:04"`, or `"15:04:05"` with `seconds`. -/
def brisbaneClock (unix : Int) (seconds : Bool := false) : String :=
  let t := (unix + brisbaneOffsetS) % 86400
  let hm := s!"{two (t / 3600).toNat}:{two (t % 3600 / 60).toNat}"
  if seconds then s!"{hm}:{two (t % 60).toNat}" else hm

/-- Go's layout `"2 Jan 15:04:05"`. -/
def brisbaneStamp (unix : Int) : String :=
  let (d, m) := dayMonth ((unix + brisbaneOffsetS) / 86400)
  let months := #["Jan", "Feb", "Mar", "Apr", "May", "Jun", "Jul", "Aug", "Sep", "Oct", "Nov", "Dec"]
  s!"{d} {months[m - 1]!} {brisbaneClock unix (seconds := true)}"

#guard brisbaneStamp 1795412249 == "23 Nov 15:37:29"
#guard brisbaneClock 1795464000 == "06:00"

/-! ## Labels -/

/-- Go's `modeLabel`: `EMSModeLabel` with spaces. -/
def modeLabel : Nat → String
  | 0 => "self consumption"
  | 2 => "forced"
  | _ => "unknown"

/-- Go's `EMSCommandLabel`. -/
def commandLabel : Nat → String
  | 0xAA => "charge"
  | 0xBB => "discharge"
  | 0xCC => "stop"
  | _    => "unknown"

/-! ## The panels -/

/-- Go's `uiDataStaleAfter` and `uiStaleAfter`. -/
def uiDataStaleAfterMs : Nat := 30_000
def uiStaleAfterMs     : Nat := 45_000

/-- Each Prometheus metric's value in the last read (Go's snapshot, by metric name). -/
def metricValues (blocks : Array ReadBlock) : List (String × Dec) := Id.run do
  let mut out := []
  for b in blocks do
    for slot in b.slots do
      let some m := metricDefs.find? (·.sensorId == slot.sensor.unique_id) | continue
      let some r := slot.reading | continue
      let some raw := decodeRaw slot.sensor r.raw | continue
      let v : Dec := match slot.sensor.scale with
        | none        => ⟨raw, 0⟩
        | some ⟨m, e⟩ => ⟨raw * m, e⟩
      out := (m.name, v) :: out
  return out

/-- Go's `metricRow`. -/
def metricRow (label : String) (kw : Dec) (signed : Bool) (posWord negWord : String) : String :=
  let (rowCls, valCls, dir, val) :=
    if !signed then ("", "", "", kw.fixed 2)
    else
      let val := kw.fixed 2 (plus := true)
      if (Dec.mk 5 3).lt kw then (" tint-pos", " pos", posWord, val)
      else if kw.lt ⟨-5, 3⟩ then (" tint-neg", " neg", negWord, val)
      else ("", "", "", val)
  s!"<div class=\"metric{rowCls}\">" ++
  s!"<span class=\"m-label\">{htmlEscape label}</span>" ++
  s!"<span class=\"m-val{valCls}\">{val}<span class=\"m-unit\">kW</span></span>" ++
  s!"<span class=\"m-dir\">{dir}</span></div>"

/-- Go's `renderStats`: the live power figures and the SOC bar. -/
def renderStats (s : Shared) (nowMs : Int) : String := Id.run do
  let mut b := "<div id=\"stats\">"
  match s.lastReadMs with
  | none => b := b ++ "<div class=\"stale-banner\">no successful inverter read since startup</div>"
  | some at_ =>
    let age := (nowMs - at_).toNat
    if age > uiDataStaleAfterMs then
      b := b ++ s!"<div class=\"stale-banner\">DATA STALE — last successful read {goDuration age} ago</div>"
  let m := metricValues (s.blocks.getD #[])
  if m.isEmpty then
    return b ++ "<p class=\"empty\">no telemetry yet</p></div>"
  let get (name : String) : Dec := (m.lookup name).getD ⟨0, 0⟩
  let kw (name : String) := (get name).shift 3
  let pv   := kw "solar_pv_power_watts"
  let batt := kw "solar_battery_power_watts"  -- + discharge / − charge
  let soc  := get "solar_battery_soc_percent"
  let grid := kw "solar_grid_power_watts"     -- + export / − import
  let load := kw "solar_load_power_watts"
  let drawn := pv + batt - grid               -- DC-side energy balance (iSolarCloud's "load")
  b := b ++ "<div class=\"metrics\">"
  b := b ++ metricRow "PV" pv false "" ""
  b := b ++ metricRow "Battery" batt true "discharging" "charging"
  b := b ++ metricRow "Grid" grid true "exporting" "importing"
  b := b ++ metricRow "House load" load false "" ""
  b := b ++ metricRow "Drawn" drawn false "" ""
  b := b ++ "</div>"
  let clamped : Dec := if soc.lt ⟨0, 0⟩ then ⟨0, 0⟩ else if (Dec.mk 100 0).lt soc then ⟨100, 0⟩ else soc
  b := b ++ "<div class=\"soc\">" ++
    s!"<div class=\"soc-head\"><span class=\"m-label\">State of charge</span><span class=\"soc-pct\">{soc.fixed 0}%</span></div>" ++
    s!"<div class=\"bar\"><div class=\"bar-fill\" style=\"width:{clamped.fixed 1}%\"></div></div></div>"
  return b ++ "</div>"

/-- Go's `renderStatus`: the cached control registers as pills. -/
def renderStatus (s : Shared) (nowMono : Nat) : String :=
  match s.control with
  | none =>
    "<div id=\"status\"><p class=\"ago stale\">control state never confirmed (inverter unreachable since startup)</p></div>"
  | some (v, at_) =>
    let (mode, cmd, power) := (v[0].toNat, v[1].toNat, v[2].toNat)
    let modeCls := match mode with
      | 2 => "pill-warn"
      | 0 => "pill-ok"
      | _ => "pill-muted"
    let age := nowMono - at_
    let staleCls := if age > uiStaleAfterMs then " stale" else ""
    "<div id=\"status\">" ++
    "<div class=\"pills\">" ++
    s!"<span class=\"pill {modeCls}\">{htmlEscape (modeLabel mode)}</span>" ++
    s!"<span class=\"pill pill-cmd\">{htmlEscape (commandLabel cmd)}</span>" ++
    s!"<span class=\"pill pill-power\">{fixedFrac power 1000 2} kW</span></div>" ++
    s!"<p class=\"ago{staleCls}\">confirmed {goDuration age} ago</p>" ++
    "</div>"

/-- Go's `renderMode`: the override, or the schedule, or neither. -/
def renderMode (i : Intent) (targetReached : Bool) : String := Id.run do
  let mut b := "<div id=\"mode\">"
  match i.override, i.window with
  | some o, _ =>
    let r := o.action.registers.toRaw
    let untilStr := match o.expiry with
      | some t => " · until " ++ brisbaneClock t
      | none   => ""
    b := b ++ "<div class=\"mode-line\"><span class=\"dot dot-on\"></span>" ++
      s!"<span><strong>Manual override</strong> · {htmlEscape (modeLabel r[0].toNat)} · {htmlEscape (commandLabel r[1].toNat)} · {fixedFrac r[2].toNat 1000 2} kW{untilStr}</span></div>"
  | none, some _ =>
    b := b ++ "<div class=\"mode-line\"><span class=\"dot dot-on\"></span>" ++
      "<span>Automatic — following schedule</span></div>"
  | none, none =>
    -- No override and no schedule: the worker holds self-consumption.
    b := b ++ "<div class=\"mode-line\"><span class=\"dot\"></span>" ++
      "<span>Self-consumption</span></div>"
  match i.window with
  | some w =>
    let reached := if targetReached then "yes" else "no"
    let (mode, rate) := match w.mode with
      | .fixed p _ => ("fixed", s!"<dt>Rate</dt><dd>{fixedFrac p.watts 1000 2} kW</dd>")
      | .adaptive c _ =>
        ("adaptive", s!"<dt>Grid cap</dt><dd>{fixedFrac c nominalGridVoltage 1} A · {fixedFrac c 1000 2} kW</dd>")
    b := b ++ "<dl class=\"kv\">" ++
      s!"<dt>Charge window</dt><dd>{w.start}–{w.stop}</dd>" ++
      s!"<dt>Mode</dt><dd>{mode}</dd>" ++
      rate ++
      s!"<dt>Target SOC</dt><dd>{w.maxSOC}%</dd>" ++
      s!"<dt>Target reached</dt><dd>{reached}</dd></dl>"
  | none => b := b ++ "<p class=\"note\">Schedule disabled</p>"
  return b ++ "</div>"

/-- Go's `ctrlSummary`, from a `WriteOp`'s registers JSON; `null` (not read) is a dash. -/
def ctrlSummary (j : Json) : String :=
  match j.getObjValAs? Nat "ems_mode", j.getObjValAs? Nat "ems_command", j.getObjValAs? Nat "forced_power_w" with
  | .ok mode, .ok cmd, .ok power =>
    if mode != 2 then modeLabel mode
    else if power == 0 then commandLabel cmd
    else s!"{commandLabel cmd} {fixedFrac power 1000 2} kW"
  | _, _, _ => "—"

/-- Go's `renderControlWrites`: the audit trail, newest first. -/
def renderControlWrites (ops : Except String (Array Json)) : String := Id.run do
  let mut b := "<div id=\"control-writes\">"
  match ops with
  | .error _ => b := b ++ "<p class=\"empty\">control write history unavailable</p>"
  | .ok ops =>
    if ops.isEmpty then
      b := b ++ "<p class=\"empty\">no control writes yet</p>"
    else
      b := b ++ "<table class=\"cw\"><thead><tr>" ++
        "<th>Time</th><th>Write</th><th>Result</th></tr></thead><tbody>"
      for op in ops do
        let at_ := (op.getObjValAs? String "recorded_at").toOption.getD ""
        let when := match unixOfRFC3339 at_ with
          | .ok t    => brisbaneStamp t
          | .error _ => at_
        let err := (op.getObjValAs? String "err").toOption.getD ""
        let noOp := (op.getObjValAs? Bool "no_op").toOption.getD false
        let result :=
          if err != "" then "<span class=\"cw-pill cw-fail\">error</span>"
          else if noOp then "<span class=\"cw-pill cw-noop\">no-op</span>"
          else "<span class=\"cw-pill cw-ok\">ok</span>"
        b := b ++ s!"<tr><td>{htmlEscape when}</td><td>{htmlEscape (ctrlSummary (op.getObjValD "before"))}<span class=\"cw-arrow\">→</span>{htmlEscape (ctrlSummary (op.getObjValD "intended"))}</td><td>{result}</td></tr>"
        if err != "" then
          b := b ++ s!"<tr class=\"cw-err\"><td colspan=\"3\">{htmlEscape err}</td></tr>"
      b := b ++ "</tbody></table>"
  return b ++ "</div>"

/-- Go's `renderDiag`: `/diag`, read only. -/
def renderDiag (j : Json) : String :=
  "<pre id=\"diag\" class=\"diag\">" ++ htmlEscape j.pretty ++ "</pre>"

def renderClock (unix : Int) : String :=
  s!"<span id=\"clock\">{brisbaneClock unix (seconds := true)} AEST</span>"

/-- What Go's `renderForecast`, `renderCompare` and `renderSOCHistory` show with no Solcast
forecast and no `SUNGROWD_PROMETHEUS_URL`. -/
def renderForecast    : String := "<div id=\"forecast\"><p class=\"empty\">no complete forecast yet</p></div>"
def renderCompare     : String := "<div id=\"compare\"><p class=\"empty\">set SUNGROWD_PROMETHEUS_URL to see actuals</p></div>"
def renderSOCHistory  : String := "<div id=\"soc-history\"><p class=\"empty\">set SUNGROWD_PROMETHEUS_URL to see SOC history</p></div>"

/-- Go's `resultBox`. -/
def resultBox (id kind msg : String) : String :=
  if msg.isEmpty then s!"<div id=\"{id}\"></div>"
  else s!"<div id=\"{id}\"><div class=\"alert alert-{kind}\">{htmlEscape msg}</div></div>"

def actionResult   := resultBox "action-result"
def scheduleResult := resultBox "schedule-result"

/-! ## Signals -/

/-- Go's `sigString`: trimmed; `""` if absent or not a string. -/
def sigString (j : Json) (k : String) : String :=
  match j.getObjValD k with
  | .str s => s.trimAscii.toString
  | _      => ""

/-- Go's `sigFloat`: a JSON number or a numeric string (Datastar may send an
`<input type=number>` either way). -/
def sigNumber (j : Json) (k : String) : Option Dec :=
  match j.getObjValD k with
  | .num n => some (.ofJsonNumber n)
  | .str s => match Json.parse s.trimAscii.toString with
    | .ok (.num n) => some (.ofJsonNumber n)
    | _            => none
  | _ => none

/-- Go's `parseExpiry`: `"HH:MM"`, the next time Brisbane's clock shows it; `""` is none. -/
def parseExpiry (s : String) (nowUnix : Int) : Option (Option Int) :=
  let s := s.trimAscii.toString
  if s.isEmpty then some none
  else (TimeOfDay.parse? s).map fun t => some (nextOccurrence t nowUnix)

def untilMsg : Option Int → String
  | some t => " until " ++ brisbaneClock t
  | none   => ""

/-- Go's `scheduleSeed`: the editor's starting values, from the stored window. -/
def scheduleSeed (w : Option ChargeWindow) : Json :=
  let (start, stop, soc) := match w with
    | some w => (toString w.start, toString w.stop, w.maxSOC)
    | none   => ("01:00", "06:00", 80)
  let (mode, kw, capA) : String × Dec × Dec := match (w.map (·.mode) : Option ChargeMode) with
    | some (.fixed p _)    => ("fixed", ⟨p.watts, 3⟩, ⟨18, 0⟩)
    -- To 0.001 A; Go's float has more digits, but the input steps by 0.5 A.
    | some (.adaptive c _) => ("adaptive", ⟨1, 0⟩, ⟨(2 * c * 1000 + 240) / (2 * 240), 3⟩)
    | none                 => ("fixed", ⟨1, 0⟩, ⟨18, 0⟩)
  Json.mkObj [
    ("scheduleStart", start), ("scheduleEnd", stop), ("scheduleMode", mode),
    ("scheduleKw", kw.toJson), ("scheduleCapA", capA.toJson),
    ("scheduleSoc", toJson soc)]

/-! ## Handlers -/

def indexHtml : String := include_str "../ui/index.html"
def datastarJs : String := include_str "../ui/datastar.js"

def maxForcedPowerKW : Dec := ⟨maxForcedPowerW, 3⟩

/-- Go's `uiPageHandler`: the template's two values, as Go's `text/template` prints them. -/
def Api.page (api : Api) : String :=
  (indexHtml.replace "{{.MaxKW}}" maxForcedPowerKW.short).replace "{{.FuseA}}" (toString api.fuse)

/-- The stored intent; Go's `Diagnostics` logs an unreadable one and shows none. -/
def Api.intentOrEmpty (api : Api) (stored : Except String Intent) : IO Intent :=
  match stored with
  | .ok i    => pure i
  | .error e => do
    api.log.error "diagnostics: could not load intent" [("err", e)]
    pure { window := none, override := none }

/-- Go's `uiUpdatesHandler`: one stream per open page, re-rendering from memory and the
database (no inverter I/O). The clock every second, the live panels every 500 ms, the slow ones
every 10 s, forecast-vs-actual every minute. Ends when the page goes away (`send` throws) or the
server shuts down. -/
def Api.uiUpdates (api : Api) : ContextAsync (Response Body.Any) :=
  sseResponse fun sse => do
    -- Its own connection, used only by this stream.
    let store ← Store.open api.dbPath
    let load : IO (Except String Intent) :=
      try store.loadIntent api.fuse catch e => pure (.error (toString e))

    let patch (html : String) : Async Unit := sse.send (patchElements html)
    let tick : Async Unit := do
      let ms := (← Std.Time.Timestamp.now).toMillisecondsSinceUnixEpoch.val
      sse.send (patchSignals s!"\{\"tickMs\": {ms}}")
    let renderData : Async Unit := do
      let s ← api.shared.get
      let i ← api.intentOrEmpty (← load)
      patch (renderStats s (← Std.Time.Timestamp.now).toMillisecondsSinceUnixEpoch.val)
      patch (renderStatus s (← IO.monoMsNow))
      patch (renderMode i s.controller.targetReached)
    let renderSlow : Async Unit := do
      patch renderForecast
      patch renderSOCHistory
      let ops ← try .ok <$> store.recentControlWrites 20 catch e => pure (.error (toString e))
      if let .error e := ops then api.log.warn "ui control writes" [("err", e)]
      patch (renderControlWrites ops)
      patch (renderDiag (diagJson (← api.shared.get) (← load)))
    let clock : Async Unit := do
      patch (renderClock (← Std.Time.Timestamp.now).toSecondsSinceUnixEpoch.val)

    -- Seed the schedule editor once, without clobbering edits already made.
    if let .ok i ← load then
      sse.send (patchSignals (scheduleSeed i.window).compress (onlyIfMissing := true))

    -- Initial paint.
    renderData; renderSlow; patch renderCompare; clock; tick

    let mut n : Nat := 0
    repeat
      let done ← Selectable.one #[
        .case (← Selector.sleep (msOffset 500)) fun _ => pure false,
        .case (← ContextAsync.doneSelector) fun _ => pure true]
      if done then break
      n := n + 1
      renderData
      if n % 2 == 0 then clock; tick
      if n % 20 == 0 then renderSlow
      if n % 120 == 0 then patch renderCompare

/-- An action: read the signals (Go logs a bad body and carries on with none), work out the
fragments to patch, and send them. -/
def Api.uiAction (api : Api) (name : String) (req : Request Body.Stream)
    (k : Json → IO (List String)) : ContextAsync (Response Body.Any) := do
  let sig ← match ← readSignals (α := Json) req with
    | .ok j    => pure j
    | .error e =>
      api.log.warn "ui action: read signals" [("action", name), ("err", e)]
      pure Json.null
  let fragments ← k sig
  sseResponse fun sse => do
    for f in fragments do sse.send (patchElements f)

/-- Go's `SetManualOverride`, then its log line. -/
def Api.setOverride (api : Api) (o : Option ManualOverride) : IO (Except String Intent) := do
  let r ← api.updateIntent ({ · with override := o })
  if r matches .ok _ then
    match o with
    | none   => api.log.info "manual override cleared"
    | some o => api.log.info "manual override set" [("value", (toJson o).compress)]
  return r

/-- Go's `uiResumeHandler`. -/
def Api.uiResume (api : Api) (req : Request Body.Stream) : ContextAsync (Response Body.Any) :=
  api.uiAction "resume" req fun _ => do
    match ← api.setOverride none with
    | .error e => return [actionResult "err" s!"Clear override failed: {e}"]
    | .ok _    => return [actionResult "ok" "Override cleared — schedule resumed."]

/-- Go's `uiForceChargeHandler`. -/
def Api.uiForceCharge (api : Api) (req : Request Body.Stream) : ContextAsync (Response Body.Any) :=
  api.uiAction "force-charge" req fun sig => do
    let nowUnix := (← Std.Time.Timestamp.now).toSecondsSinceUnixEpoch.val
    let raw := match sig.getObjValD "chargeRateKw" with
      | .str s => s
      | _      => ""
    let some kw := sigNumber sig "chargeRateKw"
      | return [actionResult "err" s!"Invalid kW {(toJson raw).compress}"]
    let watts := kw.roundMul 1000
    let some p := (if kw.m ≤ 0 then none else ForcedPower.ofWatts? watts.toNat)
      | return [actionResult "err" s!"kW must be 0.0–{maxForcedPowerKW.fixed 1}"]
    let some expiry := parseExpiry (sigString sig "overrideExpiry") nowUnix
      | return [actionResult "err" "Invalid expiry time."]
    match ← api.setOverride (some { action := .charge p, expiry }) with
    | .error e => return [actionResult "err" s!"Force-charge failed: {e}"]
    | .ok _    => return [actionResult "ok" s!"Force charging at {kw.fixed 2} kW{untilMsg expiry}."]

/-- Go's `uiStopHandler`. -/
def Api.uiStop (api : Api) (req : Request Body.Stream) : ContextAsync (Response Body.Any) :=
  api.uiAction "stop" req fun sig => do
    let nowUnix := (← Std.Time.Timestamp.now).toSecondsSinceUnixEpoch.val
    let some expiry := parseExpiry (sigString sig "overrideExpiry") nowUnix
      | return [actionResult "err" "Invalid expiry time."]
    match ← api.setOverride (some { action := .stop, expiry }) with
    | .error e => return [actionResult "err" s!"Stop failed: {e}"]
    | .ok _    => return [actionResult "ok" s!"Battery held (stop){untilMsg expiry}."]

/-- Go's `SetChargeWindow`/`DisableChargeWindow`, then `renderMode` and the result. -/
def Api.setWindow (api : Api) (w : Option ChargeWindow) (failed ok : String) : IO (List String) := do
  match ← api.updateIntent ({ · with window := w }) with
  | .error e => return [scheduleResult "err" s!"{failed}{e}"]
  | .ok i =>
    match w with
    | some w => api.log.info "charge window updated" [("window", (scheduleJson w).compress)]
    | none   => api.log.info "charge window disabled"
    let s ← api.shared.get
    return [renderMode i s.controller.targetReached, scheduleResult "ok" ok]

/-- Go's `uiScheduleHandler`. -/
def Api.uiSchedule (api : Api) (req : Request Body.Stream) : ContextAsync (Response Body.Any) :=
  api.uiAction "schedule" req fun sig => do
    let fieldsErr := [scheduleResult "err" "Check the start, end and SOC fields."]
    let some start := TimeOfDay.parse? (sigString sig "scheduleStart") | return fieldsErr
    let some stop  := TimeOfDay.parse? (sigString sig "scheduleEnd")   | return fieldsErr
    let some soc   := sigNumber sig "scheduleSoc"                      | return fieldsErr
    if soc.lt ⟨1, 0⟩ || (Dec.mk 100 0).lt soc then
      return [scheduleResult "err" "Max SOC must be 1–100%."]
    let soc := soc.m.toNat / 10 ^ soc.e  -- Go's uint8(soc) truncates
    let mode ← if sigString sig "scheduleMode" == "adaptive" then
        let capErr := [scheduleResult "err" s!"Grid cap must be 1–{api.fuse} A (main fuse)."]
        let some capA := sigNumber sig "scheduleCapA" | return capErr
        if capA.lt ⟨1, 0⟩ || (Dec.mk api.fuse 0).lt capA then return capErr
        pure (adaptiveMode (capA.roundMul nominalGridVoltage).toNat)
      else
        let rateErr := [scheduleResult "err" s!"Rate must be 0.0–{maxForcedPowerKW.fixed 1} kW"]
        let some kw := sigNumber sig "scheduleKw" | return rateErr
        if kw.m ≤ 0 || maxForcedPowerKW.lt kw then return rateErr
        pure (fixedMode (kw.roundMul 1000).toNat)
    match mode >>= fun mode => ChargeWindow.make? start stop mode soc api.fuse with
    | .error e => return [scheduleResult "err" e]
    | .ok w    => api.setWindow (some w) "" "Schedule saved."

/-- Go's `uiScheduleDisableHandler`. Go keeps a disabled window's fields; we have no disabled
window, so the editor's inputs (already in the page) are what remains. -/
def Api.uiScheduleDisable (api : Api) (req : Request Body.Stream) : ContextAsync (Response Body.Any) :=
  api.uiAction "schedule-disable" req fun _ =>
    api.setWindow none "Disable failed: " "Schedule disabled."

/-! ## Routing -/

def Api.handler (api : Api) : Http.Server.StatelessHandler where
  onRequest req := do
    match req.line.method, toString req.line.uri.pathOrRoot with
    | .get, "/" =>
      Response.ok
        |>.header! "Content-Type" "text/html; charset=utf-8"
        |>.fromBytes api.page.toUTF8
    | .get, "/datastar.js" =>
      -- Small; always revalidate so upgrades take effect immediately.
      Response.ok
        |>.header! "Content-Type" "text/javascript; charset=utf-8"
        |>.header! "Cache-Control" "no-cache"
        |>.fromBytes datastarJs.toUTF8
    | .get,  "/ui/updates"                => api.uiUpdates
    | .post, "/ui/action/force-charge"    => api.uiForceCharge req
    | .post, "/ui/action/stop"            => api.uiStop req
    | .post, "/ui/action/resume"          => api.uiResume req
    | .post, "/ui/action/schedule"        => api.uiSchedule req
    | .post, "/ui/action/schedule-disable" => api.uiScheduleDisable req
    | _, _ => return ← api.respond req

end Sungrowd
