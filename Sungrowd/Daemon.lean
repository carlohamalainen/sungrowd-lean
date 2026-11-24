import Sungrowd.Inverter
import Sungrowd.Intent
import Sungrowd.Log
import Sungrowd.Store
import Std.Sync.Channel

/-! # The daemon: `sungrowd run`

Go's `Server.Run` and `handle`. Every constant and policy here is Go's:

* the intent lives in the database (`Sungrowd/Store.lean`), seeded from a schedule file when
  the database has none;
* tick every 5 s, once at startup, and at once when an HTTP handler changes the intent;
* each tick re-reads the intent; if it can't, leave the inverter as it is;
* an expired override is cleared from the database;
* every write attempt is recorded in `control_write`;
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
def dbEnvVar             : String := "SUNGROWD_DB"
def dbDefault            : String := "sungrowd.db"
/-- Seeds a fresh database's intent: Go's `schedule.json`, or an intent in our format. -/
def scheduleEnvVar       : String := "SUNGROWD_SCHEDULE"
def scheduleDefault      : String := "schedule.json"

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
  /-- The last tick, for `/diag`: the intent after expiry, the decision, the controller state. -/
  effective     : Option Policy.Intent := none
  decision      : Option Policy.Decision := none
  controller    : Policy.ControllerState := {}

structure RunArgs where
  apply : Bool

def parseRun : List String → Except String RunArgs
  | []          => pure ⟨false⟩
  | ["--apply"] => pure ⟨true⟩
  | args        => throw s!"run: expected [--apply], got {args}"

structure Daemon where
  host        : String
  port        : UInt16
  debug       : Bool
  fuse        : Nat
  args        : RunArgs
  log         : Log
  store       : Store
  shared      : IO.Ref Shared
  /-- Monotonic ms of the last connection, for Go's one-per-second connection limiter. -/
  lastConnect : IO.Ref Nat
  /-- The read blocks, unread, as `loadBlocks` gave them. -/
  blocks      : Array ReadBlock
  /-- Go's buffered-1 wake channel: the HTTP handlers nudge the worker to tick now, after
  changing the intent. -/
  wake        : Std.Channel Unit

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
registers already do what it asks (`heldBy`) and are under `controlReconcileMs` old. -/
def Daemon.applyControl (d : Daemon) (desired : ControlRegisters) (reason : String) : IO Unit := do
  let want := desired.toRaw
  if let some (v, at_) := (← d.shared.get).control then
    if desired.heldBy v && (← IO.monoMsNow) < at_ + controlReconcileMs then
      d.log.debug "control registers already correct (cached)" [("reason", reason)]
      return
  let current ← match ← (d.readControl).run.block with
    | .ok v    => pure v
    | .error e =>
      d.log.error "apply control failed" [("reason", reason), ("err", toString e)]
      return
  d.setControl current
  if desired.heldBy current then
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
      -- Couldn't connect: still an attempt, so still audited.
      pure { recordedAt := ← Std.Time.Timestamp.now, before := none, intended := desired,
             after := none, outcome := .notSent e }
  -- Audit every attempt, as Go does.
  d.log.debug "control write" [("op", (Lean.toJson op).compress)]
  try discard <| d.store.insertControlWrite op
  catch e => d.log.error "could not record control write" [("err", toString e)]
  match op.outcome with
  | .ok | .noOp =>
    d.setControl (op.after.getD want)
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

/-- One tick: Go's `handle`. -/
def Daemon.handle (d : Daemon) (w : Worker) : IO Worker := do
  -- The database is the single source of truth for what the user wants.
  let loaded ← try d.store.loadIntent d.fuse catch e => pure (.error (toString e))
  let intent ← match loaded with
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

  -- Auto-expire a manual override whose deadline has passed: clear it from the database (unless
  -- it has been replaced since we loaded it), and carry on this tick without it.
  if effective != intent then
    d.log.info "manual override expired; clearing"
      [("override", (Lean.toJson intent.override).compress)]
    let clear (i : Policy.Intent) := if i.override == intent.override then { i with override := none } else i
    match ← (try d.store.updateIntent d.fuse clear catch e => pure (.error (toString e))) with
    | .ok _    => pure ()
    | .error e => d.log.error "could not clear expired override" [("err", e)]

  d.log.debug "tick" [("soc", toString snap.socTenths), ("grid_w", toString snap.gridW),
    ("battery_w", toString snap.batteryW), ("decision", decision.show)]
  if w.lastDecision != some decision then
    d.log.info "decision" [("decision", decision.show)]

  match decision with
  | .leave why => d.log.error "leaving the inverter as it is" [("why", why)]
  | .apply r reason => d.applyControl r reason.label

  d.shared.modify fun s =>
    { s with effective := some effective, decision := some decision, controller := st }
  return { st, loaded := some intent, effective := some effective, lastDecision := some decision }

/-- Go's worker loop: tick at once, then every `tickIntervalMs` (skipping ticks if one overruns,
like a Go ticker), and also whenever `wake` has a message. A wake doesn't move the schedule.

Returns on SIGINT or SIGTERM, Go's `signal.NotifyContext`. A tick in progress finishes first, so a
write is never cut off between sending and reading back. -/
def Daemon.loop (d : Daemon) : IO Unit := do
  -- `wait` starts listening now. A select only starts a waiter when it checks it, so without
  -- this a signal during the first tick would get the default action and kill the process.
  let signals ← [("SIGINT", Signal.sigint), ("SIGTERM", .sigterm)].mapM fun (name, sig) => do
    let waiter ← Signal.Waiter.mk sig (repeating := false)
    discard waiter.wait
    return (name, waiter)
  let mut w : Worker := {}
  let mut next ← IO.monoMsNow
  repeat
    w ← try d.handle w catch e => do
      d.log.error "tick failed" [("err", toString e)]
      pure w
    let now ← IO.monoMsNow
    while next ≤ now do next := next + tickIntervalMs
    -- Wait for the next tick, a wake, or a signal (which a one-shot waiter keeps until checked).
    let wait : Async (Option String) := do
      Selectable.one <|
        #[.case (← Selector.sleep (msOffset (next - now))) fun _ => pure none,
          .case d.wake.recvSelector fun _ => pure none]
        ++ signals.toArray.map fun (name, waiter) => .case waiter.selector fun _ => pure (some name)
    if let some name ← wait.block then
      d.log.info "shutting down" [("signal", name)]
      break

end Sungrowd
