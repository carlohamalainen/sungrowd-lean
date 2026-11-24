import Sungrowd.Inverter

/-! # Go's formatting, exactly: decimals without floats, HTML escaping, Brisbane dates

Shared by the UI and the Prometheus actuals. -/

namespace Sungrowd

open Lean (Json JsonNumber)
open Sungrowd.Inverter


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

def mulInt (a : Dec) (k : Int) : Dec := ⟨a.m * k, a.e⟩

/-- Rounded down to a whole number. -/
def floor (a : Dec) : Int := a.m / (10 ^ a.e : Nat)

def isNeg (a : Dec) : Bool := a.m < 0

/-- A JSON number, or a string holding one (as Prometheus sends values). -/
def ofJson? : Json → Option Dec
  | .num n => some (ofJsonNumber n)
  | .str s => match Json.parse s with
    | .ok (.num n) => some (ofJsonNumber n)
    | _            => none
  | _ => none

end Dec

#guard fixedFrac 1234 1000 2 == "1.23"
#guard fixedFrac (-1) 1000 2 (plus := true) == "-0.00"
#guard fixedFrac 0 1000 2 (plus := true) == "+0.00"
#guard fixedFrac 4320 240 1 == "18.0"
#guard (Dec.mk 50 1).short == "5" && (Dec.mk 58 1).short == "5.8" && (Dec.mk 20 0).short == "20"
#guard (Dec.mk 15 1).roundMul 1000 == 1500
#guard (Dec.ofJson? (.str "1.2345e+03")).map (·.fixed 1) == some "1234.5"
#guard (Dec.ofJson? (.str "NaN")).isNone
#guard (Dec.mk 17954122495 1).floor == 1795412249

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

/-! ## Brisbane wall-clock time

Brisbane has no daylight saving, so local time is UTC+10 all year. A *day number* counts local
days since 1970-01-01. -/

private def two (n : Nat) : String := if n < 10 then s!"0{n}" else toString n

/-- Year, month (1–12) and day of a day number (Hinnant's `civil_from_days`). -/
def civilOfDays (days : Int) : Int × Nat × Nat :=
  let z := days + 719468
  let era := z / 146097
  let doe := z - era * 146097
  let yoe := (doe - doe / 1460 + doe / 36524 - doe / 146096) / 365
  let doy := doe - (365 * yoe + yoe / 4 - yoe / 100)
  let mp := (5 * doy + 2) / 153
  let d := doy - (153 * mp + 2) / 5 + 1
  let m := if mp < 10 then mp + 3 else mp - 9
  (yoe + era * 400 + (if m ≤ 2 then 1 else 0), m.toNat, d.toNat)

/-- The inverse (Hinnant's `days_from_civil`). -/
def daysOfCivil (y : Int) (m d : Nat) : Int :=
  let y := if m ≤ 2 then y - 1 else y
  let era := y / 400
  let yoe := y - era * 400
  let mp : Int := if m > 2 then m - 3 else m + 9
  let doy := (153 * mp + 2) / 5 + d - 1
  let doe := yoe * 365 + yoe / 4 - yoe / 100 + doy
  era * 146097 + doe - 719468

/-- The local day a Unix time falls on. -/
def brisbaneDay (unix : Int) : Int := (unix + brisbaneOffsetS) / 86400

/-- Local midnight starting a day: Unix seconds. -/
def brisbaneMidnight (day : Int) : Int := day * 86400 - brisbaneOffsetS

/-- Minutes since local midnight. -/
def brisbaneMinuteOfDay (unix : Int) : Nat := ((unix + brisbaneOffsetS) % 86400 / 60).toNat

private def months : Array String :=
  #["Jan", "Feb", "Mar", "Apr", "May", "Jun", "Jul", "Aug", "Sep", "Oct", "Nov", "Dec"]

/-- Go's layout `"2006-01-02"`. -/
def dateString (day : Int) : String :=
  let (y, m, d) := civilOfDays day
  s!"{y}-{two m}-{two d}"

/-- Go's `time.ParseInLocation("2006-01-02", s, brisbane)`, as a day number. -/
def parseDate? (s : String) : Option Int := do
  let [y, m, d] := s.splitOn "-" | none
  guard (y.length == 4 && m.length == 2 && d.length == 2)
  let day := daysOfCivil (← y.toNat?) (← m.toNat?) (← d.toNat?)
  guard (dateString day == s)  -- rejects 2026-02-30 and the like
  return day

/-- Go's layout `"Mon 2 Jan"`. -/
def dayLabel (day : Int) : String :=
  let (_, m, d) := civilOfDays day
  let weekdays := #["Thu", "Fri", "Sat", "Sun", "Mon", "Tue", "Wed"]  -- day 0 was a Thursday
  s!"{weekdays[(day % 7).toNat]!} {d} {months[m - 1]!}"

/-- Go's layout `"15:04"`, or `"15:04:05"` with `seconds`. -/
def brisbaneClock (unix : Int) (seconds : Bool := false) : String :=
  let t := (unix + brisbaneOffsetS) % 86400
  let hm := s!"{two (t / 3600).toNat}:{two (t % 3600 / 60).toNat}"
  if seconds then s!"{hm}:{two (t % 60).toNat}" else hm

/-- Go's layout `"2 Jan 15:04:05"`. -/
def brisbaneStamp (unix : Int) : String :=
  let (_, m, d) := civilOfDays (brisbaneDay unix)
  s!"{d} {months[m - 1]!} {brisbaneClock unix (seconds := true)}"

#guard brisbaneStamp 1795412249 == "23 Nov 15:37:29"
#guard brisbaneClock 1795464000 == "06:00"
#guard dateString (brisbaneDay 1795412249) == "2026-11-23"
#guard dayLabel (brisbaneDay 1795412249) == "Mon 23 Nov"
#guard parseDate? "2026-11-23" == some (brisbaneDay 1795412249)
#guard parseDate? "2026-02-30" == none && parseDate? "26-11-23" == none
#guard dateString (daysOfCivil 2028 2 29) == "2028-02-29" && dateString 0 == "1970-01-01"
#guard brisbaneMidnight (brisbaneDay 1795412249) == 1795356000  -- 2026-11-23T00:00+10:00
#guard brisbaneMinuteOfDay 1795412249 == 15 * 60 + 37
end Sungrowd
