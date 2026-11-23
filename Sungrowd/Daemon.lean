import Sungrowd.Inverter
import Sungrowd.Intent
import Sungrowd.Log

/-! # The daemon: `sungrowd run`

Go's `Server.Run` and `handle`, with the intent in a file instead of SQLite. Every constant
and policy here is Go's:

* tick every 5 s, and once at startup;
* each tick re-reads the intent; if it can't, leave the inverter as it is;
* read the sensors every tick, 3 attempts on a fresh connection each (Sungrow inverters return
  modbus exception 4 in short clusters), at most one new connection per second;
* trust cached control registers for 30 s before reading them again;
* `/metrics` serves the last successful read; `/healthz` is 503 once that is older than
  `SUNGROWD_STALE_THRESHOLD_SECONDS` (default 120).

Writes to the inverter only with `--apply`; without it, the daemon logs what it would write. -/

namespace Sungrowd

open Std Async
open Modbus
open Sungrowd.Control
open Sungrowd.Inverter

def tickIntervalMs       : Nat := 5000
def readAttempts         : Nat := 3
def controlReconcileMs   : Nat := 30000
def connectSpacingMs     : Nat := 1000
def listenEnvVar         : String := "SUNGROWD_LISTEN"
def listenDefault        : String := "0.0.0.0:9180"
def staleEnvVar          : String := "SUNGROWD_STALE_THRESHOLD_SECONDS"
def staleDefaultS        : Nat := 120
def logLevelEnvVar       : String := "SUNGROWD_LOG_LEVEL"

/-! ## Helpers shared with `tick` -/

def orThrow (what : String) : Except String α → ExceptT String IO α
  | .ok a    => pure a
  | .error e => throw s!"{what}: {e}"

def readJsonFile (path : System.FilePath) : ExceptT String IO Lean.Json := do
  orThrow path.toString (Lean.Json.parse (← IO.FS.readFile path))

def envNat (var : String) (default : Nat) : ExceptT String IO Nat := do
  match ← IO.getEnv var with
  | none   => pure default
  | some s => match s.toNat? with
    | some n => pure n
    | none   => throw s!"{var}={s} is not a whole number"

def _root_.Sungrowd.Policy.Decision.show : Policy.Decision → String
  | .apply r reason => s!"{reason.label}: {r}"
  | .leave why      => s!"leave the inverter as it is: {why}"

/-! ### What the worker shares with the HTTP handlers -/

/-- Go's `hardwareCache`, plus the read error count. -/
structure Shared where
  /-- The last successful sensor read, for `/metrics`. -/
  blocks        : Option (Array ReadBlock) := none
  /-- When it happened: Unix ms (for the metric and `/healthz`). -/
  lastReadMs    : Option Int := none
  lastReadErr   : Option String := none
  /-- Failed sensor reads, after retries, since the daemon started. -/
  readErrors    : Nat := 0
  /-- The control registers as last read or written, and when (monotonic ms). -/
  control       : Option (Vector UInt16 3 × Nat) := none

structure RunArgs where
  intentPath : System.FilePath
  apply      : Bool

def parseRun : List String → Except String RunArgs
  | [p]              => pure ⟨p, false⟩
  | [p, "--apply"]   => pure ⟨p, true⟩
  | ["--apply", p]   => pure ⟨p, true⟩
  | args             => throw s!"run: expected <intent.json> [--apply], got {args}"

structure Daemon where
  host        : String
  port        : UInt16
  debug       : Bool
  fuse        : Nat
  args        : RunArgs
  log         : Log
  shared      : IO.Ref Shared
  /-- Monotonic ms of the last connection, for Go's one-per-second connection limiter. -/
  lastConnect : IO.Ref Nat
  /-- The read blocks, unread, as `loadBlocks` gave them. -/
  blocks      : Array ReadBlock

/-- A fresh connection, at most one per `connectSpacingMs` (Go's `withConn`). -/
def Daemon.withConn (d : Daemon) (k : Client → M α) : M α := do
  let now ← IO.monoMsNow
  let next := (← d.lastConnect.get) + connectSpacingMs
  if now < next then sleep (msOffset (next - now))
  d.lastConnect.set (← IO.monoMsNow)
  withClient d.host d.port d.debug k

/-- Go's `readWithRetry`: `readAttempts` tries, each on a fresh connection. -/
def Daemon.readWithRetry (d : Daemon) (what : String) (read : Client → M α) : M α := do
  let mut lastErr := Error.io "no attempts"
  for attempt in [1:readAttempts + 1] do
    try
      let a ← d.withConn read
      if attempt > 1 then
        d.log.debug "inverter read recovered on retry" [("what", what), ("attempt", toString attempt)]
      return a
    catch e =>
      lastErr := e
      if attempt < readAttempts then
        d.log.debug "inverter read failed, retrying"
          [("what", what), ("attempt", toString attempt), ("err", toString e)]
  throw lastErr

def Daemon.readSensors (d : Daemon) : M (Array ReadBlock) :=
  d.readWithRetry "sensor blocks" fun c => d.blocks.mapM (·.readCtx c)

def Daemon.readControl (d : Daemon) : M (Vector UInt16 3) :=
  d.readWithRetry "control registers" fun c =>
    (Sungrowd.Control.readControl c).context
      s!"reading the control registers {regEMSMode}..{regEMSMode + 2}"

def Daemon.setControl (d : Daemon) (v : Vector UInt16 3) : IO Unit := do
  let now ← IO.monoMsNow
  d.shared.modify fun s => { s with control := some (v, now) }

/-- Go's `applyControl`: converge the inverter to `desired`, skipping I/O while the cached
registers already match and are under `controlReconcileMs` old. -/
def Daemon.applyControl (d : Daemon) (desired : ControlRegisters) (reason : String) : IO Unit := do
  let want := desired.toRaw
  if let some (v, at_) := (← d.shared.get).control then
    if v == want && (← IO.monoMsNow) < at_ + controlReconcileMs then
      d.log.debug "control registers already correct (cached)" [("reason", reason)]
      return
  let current ← match ← (d.readControl).run.block with
    | .ok v    => pure v
    | .error e =>
      d.log.error "apply control failed" [("reason", reason), ("err", toString e)]
      return
  d.setControl current
  if current == want then
    d.log.debug "control registers already correct" [("reason", reason), ("current", showRaw current)]
    return
  if !d.args.apply then
    d.log.info "would change control registers (no --apply)"
      [("reason", reason), ("from", showRaw current), ("to", toString desired)]
    return
  d.log.info "changing control registers"
    [("reason", reason), ("from", showRaw current), ("to", toString desired)]
  let op ← match ← (d.withConn fun c => guardIO (safeWriteControl c desired)).run.block with
    | .ok op   => pure op
    | .error e =>
      d.log.error "control write could not be sent — inverter left unchanged"
        [("reason", reason), ("err", toString e)]
      return
  -- Go audits every attempt in its `control_write` table; we log it.
  d.log.info "control write" [("op", (Lean.toJson op).compress)]
  match op.outcome with
  | .ok | .noOp =>
    d.setControl want
    d.log.info "control registers changed" [("reason", reason), ("now", toString desired)]
  | .unverified e =>
    d.log.warn "control write sent but not confirmed this tick (will re-check next tick)"
      [("reason", reason), ("err", toString e)]
  | .mismatch saw =>
    d.setControl saw
    d.log.error "control write did NOT take effect — inverter shows a different value"
      [("reason", reason), ("saw", showRaw saw)]
  | .notSent e =>
    d.log.error "control write could not be sent — inverter left unchanged"
      [("reason", reason), ("err", toString e)]

/-- What the worker remembers between ticks, besides the controller state. -/
structure Worker where
  st           : Policy.ControllerState := {}
  /-- The intent as last loaded and after expiry, to log changes once. -/
  loaded       : Option Policy.Intent := none
  effective    : Option Policy.Intent := none
  lastDecision : Option Policy.Decision := none

def writeFileAtomic (path : System.FilePath) (content : String) : IO Unit := do
  let tmp := path.addExtension "tmp"
  IO.FS.writeFile tmp content
  IO.FS.rename tmp path

/-- One tick: Go's `handle`. -/
def Daemon.handle (d : Daemon) (w : Worker) : IO Worker := do
  -- The intent file is the single source of truth for what the user wants.
  let intent ← match ← (do
      orThrow d.args.intentPath.toString
        (Policy.intentOfFile d.fuse (← readJsonFile d.args.intentPath)) : ExceptT String IO _).run with
    | .ok i    => pure i
    | .error e =>
      -- Don't fall back to a mode the user never asked for.
      d.log.error "could not load desired intent; leaving hardware unchanged" [("err", e)]
      return w
  if w.loaded != some intent then
    d.log.info "intent" [("intent", (Lean.toJson intent).compress)]

  -- Always refresh the sensors (best effort), so /metrics is live even if we decide nothing.
  let snap ← match ← d.readSensors.run.block with
    | .ok blocks =>
      let nowMs := (← Std.Time.Timestamp.now).toMillisecondsSinceUnixEpoch.val
      d.shared.modify fun s => { s with blocks := some blocks, lastReadMs := some nowMs, lastReadErr := none }
      pure (snapshotOf blocks)
    | .error e =>
      d.shared.modify fun s => { s with readErrors := s.readErrors + 1, lastReadErr := some (toString e) }
      d.log.warn "sensor block read failed; snapshot may be stale" [("err", toString e)]
      pure ⟨none, none, none⟩

  let nowUnix := (← Std.Time.Timestamp.now).toSecondsSinceUnixEpoch.val
  let minute  := brisbaneMinute nowUnix
  let (effective, decision, st) := Policy.tick intent snap nowUnix minute w.st

  -- Auto-expire a manual override whose deadline has passed.
  if effective != intent && w.effective != some effective then
    if d.args.apply then
      d.log.info "manual override expired; clearing" [("path", d.args.intentPath.toString)]
      try writeFileAtomic d.args.intentPath ((Lean.toJson effective).pretty ++ "\n")
      catch e => d.log.error "could not clear expired override" [("err", toString e)]
    else
      d.log.info "manual override expired; not clearing it from the file (no --apply)"

  d.log.debug "tick" [("soc", toString snap.socTenths), ("grid_w", toString snap.gridW),
    ("battery_w", toString snap.batteryW), ("decision", decision.show)]
  if w.lastDecision != some decision then
    d.log.info "decision" [("decision", decision.show)]

  match decision with
  | .leave why => d.log.error "leaving the inverter as it is" [("why", why)]
  | .apply r reason => d.applyControl r reason.label

  return { st, loaded := some intent, effective := some effective, lastDecision := some decision }

end Sungrowd
