import Sungrowd.Intent

/-! # Logging, in the shape of Go's `slog` text handler

`time=2026-11-23T01:43:35Z level=INFO msg="control registers changed" reason="adaptive charge"`,
one line per event on stderr. -/

namespace Sungrowd

inductive LogLevel
  | debug | info | warn | error

def LogLevel.rank : LogLevel → Nat
  | .debug => 0 | .info => 1 | .warn => 2 | .error => 3

def LogLevel.label : LogLevel → String
  | .debug => "DEBUG" | .info => "INFO" | .warn => "WARN" | .error => "ERROR"

/-- As Go: unknown levels are `info`. -/
def LogLevel.parse (s : String) : LogLevel :=
  match s.toLower with
  | "debug" => .debug
  | "warn" | "warning" => .warn
  | "error" => .error
  | _ => .info

structure Log where
  level : LogLevel

/-- Quote a value if it would be ambiguous unquoted, like `slog`. -/
def logValue (v : String) : String :=
  if v.isEmpty || v.any (fun c => c == ' ' || c == '=' || c == '"') then (repr v).pretty else v

/-- `time=… level=INFO msg="…" key=value …` on stderr. -/
def Log.log (l : Log) (lvl : LogLevel) (msg : String) (kvs : List (String × String) := []) :
    IO Unit := do
  if lvl.rank < l.level.rank then return
  let now := (← Std.Time.Timestamp.now).toSecondsSinceUnixEpoch.val
  let fields := kvs.foldl (fun acc (k, v) => acc ++ s!" {k}={logValue v}") ""
  IO.eprintln s!"time={Policy.rfc3339OfUnix now} level={lvl.label} msg={logValue msg}{fields}"

def Log.debug (l : Log) (msg : String) (kvs : List (String × String) := []) : IO Unit :=
  l.log .debug msg kvs
def Log.info (l : Log) (msg : String) (kvs : List (String × String) := []) : IO Unit :=
  l.log .info msg kvs
def Log.warn (l : Log) (msg : String) (kvs : List (String × String) := []) : IO Unit :=
  l.log .warn msg kvs
def Log.error (l : Log) (msg : String) (kvs : List (String × String) := []) : IO Unit :=
  l.log .error msg kvs

#guard logValue "charge" == "charge"
#guard logValue "adaptive charge" == "\"adaptive charge\""
#guard logValue "" == "\"\""
#guard (LogLevel.parse "WARNING").label == "WARN"
#guard (LogLevel.parse "nonsense").label == "INFO"

/-- Go's `Duration.String`, after `Round(time.Second)`: `45s`, `1m30s`, `1h0m0s`. -/
def goDuration (ms : Nat) : String :=
  let s := (ms + 500) / 1000
  let (h, m, sec) := (s / 3600, s % 3600 / 60, s % 60)
  if s == 0 then "0s"
  else if h > 0 then s!"{h}h{m}m{sec}s"
  else if m > 0 then s!"{m}m{sec}s"
  else s!"{sec}s"

#guard goDuration 44_600 == "45s" && goDuration 90_000 == "1m30s" && goDuration 3_600_000 == "1h0m0s"

end Sungrowd
