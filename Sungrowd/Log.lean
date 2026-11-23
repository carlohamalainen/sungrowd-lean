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

end Sungrowd
