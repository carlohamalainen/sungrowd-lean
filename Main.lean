import Modbus.Client
import Sungrowd.Control
import Sungrowd.Intent
import Sungrowd.Inverter
import Sungrowd.Daemon
import Sungrowd.Http
import Sungrowd.Ui
import Std.Data.HashMap
import Std.Http

open Std Async
open Modbus
open Sungrowd
open Sungrowd.Control
open Sungrowd.Inverter

/-! The `sungrowd` command line (see `usage`): read the sensors, read or write the EMS control
registers, run the controller once (`tick`), or run the daemon (`run`). The inverter itself
(sensors, decoding, read blocks, connecting) is `Sungrowd/Inverter.lean`. -/

/-- If set (to anything), raw frames are traced to stderr. -/
def debugEnvVar   : String := "SUNGROWD_DEBUG"
def modbusPort    : UInt16 := 502
/-- Overrides `modbusPort`, e.g. to point at a fake inverter on localhost. -/
def portEnvVar    : String := "SUNGROWD_WINET_PORT"
/-- The main fuse, which bounds an adaptive window's grid ceiling. Go's default is 20 A. -/
def gridFuseEnvVar : String := "SUNGROWD_GRID_FUSE_A"
def gridFuseAmpsDefault : Nat := 20

/-- Connect once, read every block in one request each, and print one line per sensor.
`names` maps a sensor's `unique_id` to the metric name to print. -/
def readBlocks (host : String) (port : UInt16) (debug : Bool) (names : HashMap String String)
    (blocks : Array ReadBlock) : M Unit :=
  withClient host port debug fun c => do
    let name (s : Sensor) : String := names.getD s.unique_id s.unique_id
    let width := blocks.foldl (init := 0) fun w b =>
      b.slots.foldl (init := w) fun w slot => max w (name slot.sensor).length
    for b in blocks do
      let b ← b.readCtx c
      for slot in b.slots do
        let n := name slot.sensor
        IO.println s!"{n.pushn ' ' (width - n.length)}  {slot.display}"

def readMain (host : String) (port : UInt16) (debug : Bool) : IO UInt32 := do
  let (blocks, names) ← match ← loadBlocks.run with
    | .ok bn   => pure bn
    | .error e =>
      IO.eprintln s!"error: {e}"
      return 2

  match ← (readBlocks host port debug names blocks).run.block with
  | .ok ()   => return 0
  | .error e =>
    IO.eprintln s!"error: {e}"
    return 1

/-! ## Control registers -/

/-- `write` arguments to the registers they ask for. Power goes through `ofWatts?`, so it is
snapped to 10 W and capped at the rating before anything is sent. -/
def parseWrite : List String → Except String ControlRegisters
  | ["self-consumption"] => pure .selfConsumption
  | ["forced", "stop"]   => pure ⟨.forced, .stop, ⟨0, rfl, by decide⟩⟩
  | ["forced", cmd, w]   => do
    let command ← match cmd with
      | "charge"    => pure Command.charge
      | "discharge" => pure .discharge
      | _           => throw s!"unknown command {cmd}"
    let some watts := w.toNat? | throw s!"watts: expected a whole number, got {w}"
    let some power := ForcedPower.ofWatts? watts
      | throw s!"watts: {watts} is over the {maxForcedPowerW} W rating"
    pure ⟨.forced, command, power⟩
  | args => throw s!"cannot parse write arguments {args}"

def usage : String := "usage:
  sungrowd                                   read the sensors in metricDefs
  sungrowd control                           read the EMS control registers
  sungrowd write self-consumption [--dry-run]
  sungrowd write forced stop [--dry-run]
  sungrowd write forced charge|discharge <watts> [--dry-run]
  sungrowd tick <intent.json> [--state <state.json>] [--apply]
                                             decide once from a schedule or intent file
  sungrowd run [--apply]                     the daemon: tick every 5 s, serve /metrics and /healthz"

def controlMain (host : String) (port : UInt16) (debug : Bool) : IO UInt32 := do
  match ← (withClient host port debug readControl).run.block with
  | .ok v    =>
    IO.println s!"{showRaw v}  raw {v.toArray}"
    return 0
  | .error e =>
    IO.eprintln s!"error: {e}"
    return 1

/-- Exit 0 if the inverter now holds `value` (written or already there), 1 otherwise. -/
def writeMain (host : String) (port : UInt16) (debug : Bool) (value : ControlRegisters) : IO UInt32 := do
  let op? ← (withClient host port debug fun c => guardIO (safeWriteControl c value)).run.block
  match op? with
  | .error e =>
    IO.eprintln s!"error: {e}"
    return 1
  | .ok op =>
    IO.println (Lean.toJson op).pretty
    return if op.outcome.err?.isNone then 0 else 1

/-! ## One reconciliation: `tick` -/

structure TickArgs where
  intentPath : System.FilePath
  statePath  : Option System.FilePath
  apply      : Bool

def parseTick (args : List String) : Except String TickArgs :=
  go args none none false
where
  go : List String → Option String → Option String → Bool → Except String TickArgs
    | [],                    some p, s,      a => pure ⟨p, s.map (·), a⟩
    | [],                    none,   _,      _ => throw "tick: missing intent file"
    | "--apply" :: rest,     p,      s,      _ => go rest p s true
    | ["--state"],           _,      _,      _ => throw "tick: --state needs a file"
    | "--state" :: f :: rest, p,     _,      a => go rest p (some f) a
    | arg :: rest,           none,   s,      a =>
      if arg.startsWith "--" then throw s!"tick: unknown option {arg}" else go rest (some arg) s a
    | arg :: _,              some _, _,      _ => throw s!"tick: unexpected argument {arg}"

def showOpt (o : Option α) (f : α → String) : String := (o.map f).getD "unavailable"

/-- Read the inverter, run `Policy.tick` once, and print what it decided. Writes only with
`--apply`, and only if the inverter doesn't already hold the decision. With `--state`, the
controller state is loaded before and saved after, so repeated ticks behave like the daemon. -/
def tickMain (host : String) (port : UInt16) (debug : Bool) (args : TickArgs) : IO UInt32 := do
  let setup : ExceptT String IO _ := do
    let fuse   ← envNat gridFuseEnvVar gridFuseAmpsDefault
    let intent ← orThrow args.intentPath.toString
      (Policy.intentOfFile fuse (← readJsonFile args.intentPath))
    let st : Policy.ControllerState ← match args.statePath with
      | some p =>
        if ← p.pathExists then orThrow p.toString (Policy.controllerStateOfJson fuse (← readJsonFile p))
        else pure {}
      | none => pure {}
    let (blocks, _) ← loadBlocks
    return (intent, st, blocks)
  let (intent, st, blocks) ← match ← setup.run with
    | .ok v    => pure v
    | .error e =>
      IO.eprintln s!"error: {e}"
      return 2

  let run : M UInt32 := withClient host port debug fun c => do
    let current ← (readControl c).context
      s!"reading the control registers {regEMSMode}..{regEMSMode + 2}"
    -- Best effort, as in Go: an override or a disabled schedule doesn't need the sensors.
    let blocks ← try blocks.mapM (·.readCtx c) catch e => do
      IO.eprintln s!"warning: sensor read failed: {e}"
      pure blocks
    let snap    := snapshotOf blocks
    let nowUnix := (← Std.Time.Timestamp.now).toSecondsSinceUnixEpoch.val
    let minute  := brisbaneMinute nowUnix
    let (intent', decision, st') := Policy.tick intent snap nowUnix minute st

    let hhmm := (Policy.TimeOfDay.ofHM? (minute / 60) (minute % 60)).map toString |>.getD "?"
    IO.println s!"now       {Policy.rfc3339OfUnix nowUnix} ({hhmm} Brisbane)"
    IO.println s!"intent    {(Lean.toJson intent).compress}"
    if intent' != intent then
      IO.println s!"          override expired; {args.intentPath} is unchanged"
    IO.println s!"soc       {showOpt snap.socTenths fun s => s!"{withDecimals s 1} %"}"
    IO.println s!"grid      {showOpt snap.gridW fun w => s!"{w} W"} (+export/-import)"
    IO.println s!"battery   {showOpt snap.batteryW fun w => s!"{w} W"} (+discharge/-charge)"
    IO.println s!"inverter  {showRaw current}"
    IO.println s!"decision  {decision.show}"
    IO.println s!"state     {(Lean.toJson st').compress}"
    if let some p := args.statePath then
      IO.FS.writeFile p ((Lean.toJson st').pretty ++ "\n")

    match decision with
    | .leave _ => return 0
    | .apply r _ =>
      if r.heldBy current then
        IO.println "action    none: the inverter already holds it"
        return 0
      if !args.apply then
        IO.println s!"action    would write {r} (pass --apply to write)"
        return 0
      let op ← guardIO (safeWriteControl c r)
      IO.println (Lean.toJson op).pretty
      return if op.outcome.err?.isNone then 0 else 1

  match ← run.run.block with
  | .ok code => return code
  | .error e =>
    IO.eprintln s!"error: {e}"
    return 1

def runMain (host : String) (port : UInt16) (debug : Bool) (args : RunArgs) : IO UInt32 := do
  let log : Log := ⟨LogLevel.parse ((← IO.getEnv logLevelEnvVar).getD "info")⟩
  let setup : ExceptT String IO _ := do
    let fuse       ← envNat gridFuseEnvVar gridFuseAmpsDefault
    let thresholdS ← envNat staleEnvVar staleDefaultS
    let listen     := (← IO.getEnv listenEnvVar).getD listenDefault
    let (lh, lp)   ← orThrow listenEnvVar (parseListen listen)
    let dbPath     := (← IO.getEnv dbEnvVar).getD dbDefault
    let store ← try Store.open dbPath catch e => throw s!"opening the database {dbPath}: {e}"
    let (blocks, _) ← loadBlocks
    return (fuse, thresholdS, listen, lh, lp, dbPath, store, blocks)
  let (fuse, thresholdS, listen, lh, lp, dbPath, store, blocks) ← match ← setup.run with
    | .ok v    => pure v
    | .error e =>
      IO.eprintln s!"error: {e}"
      return 2
  log.info "starting" [("inverter", s!"{host}:{port}"), ("db", dbPath),
    ("apply", toString args.apply), ("listen", listen), ("tick_ms", toString tickIntervalMs)]

  -- Go's startup seeding: a fresh database takes its intent from the schedule file. After that
  -- the database is the only source of truth, and the file is ignored.
  if (← store.intentJson).isNone then
    let path : System.FilePath := (← IO.getEnv scheduleEnvVar).getD scheduleDefault
    let seeded : ExceptT String IO Policy.Intent := do
      orThrow path.toString (Policy.intentOfFile fuse (← readJsonFile path))
    match ← seeded.run with
    | .ok i =>
      store.saveIntent i
      log.info "seeded the intent from the schedule file"
        [("path", path.toString), ("intent", (Lean.toJson i).compress)]
    | .error e =>
      log.error "could not seed the intent from the schedule file; continuing without it"
        [("path", path.toString), ("err", e)]

  let d : Daemon := { host, port, debug, fuse, args, log, store, blocks,
                      shared := ← IO.mkRef {}, lastConnect := ← IO.mkRef 0,
                      wake := ← Std.Channel.new (some 1) }

  -- Prime the control-register cache, but start degraded rather than failing if the inverter
  -- is unreachable: otherwise a restart during an outage never serves /healthz or /metrics.
  match ← (d.withConn Sungrowd.Control.readControl).run.block with
  | .ok v    => d.setControl v
  | .error e =>
    d.shared.modify fun s => { s with readErrors := s.readErrors + 1, lastReadErr := some (toString e) }
    log.warn "initial inverter read failed; starting degraded" [("err", toString e)]

  let serve : Async Http.Server := do
    Http.Server.serve (← resolve lh lp)
      (Api.handler { shared := d.shared, thresholdS, dbPath, fuse, log, wake := d.wake })
  let server ← try serve.block catch e => do
    IO.eprintln s!"error: listening on {listen}: {e}"
    return 2
  log.info "listening" [("addr", listen)]

  d.loop

  -- Go gives open requests up to 10 s. Ours are short, and `shutdown` cancels them anyway. The
  -- inverter is left as it is, as in Go: forced mode stays forced until something changes it.
  let stop : Async Unit := do
    server.shutdown
    Selectable.one #[.case server.waitShutdownSelector pure,
                     .case (← Selector.sleep (msOffset 10000)) pure]
  try stop.block catch e => log.error "http shutdown" [("err", toString e)]
  log.info "stopped"
  return 0

def main (args : List String) : IO UInt32 := do
  let some host ← IO.getEnv hostEnvVar
    | IO.eprintln s!"error: {hostEnvVar} is not set (expected the inverter's IP or hostname)"
      return 2
  let debug := (← IO.getEnv debugEnvVar).isSome
  let port ← match ← IO.getEnv portEnvVar with
    | none   => pure modbusPort
    | some p => match p.toNat? with
      | some n => if n < UInt16.size then pure n.toUInt16 else
          IO.eprintln s!"error: {portEnvVar}={p} is out of range"; return 2
      | none =>
        IO.eprintln s!"error: {portEnvVar}={p} is not a number"; return 2

  match args with
  | []          => readMain host port debug
  | ["control"] => controlMain host port debug
  | "write" :: rest =>
    let dryRun := rest.contains "--dry-run"
    match parseWrite (rest.filter (· != "--dry-run")) with
    | .error e =>
      IO.eprintln s!"error: {e}\n{usage}"
      return 2
    | .ok value =>
      if dryRun then
        let pdu := writeMultipleRequest Sungrowd.Control.regEMSMode value.toRaw
        IO.println s!"would write {value} to {Sungrowd.Control.regEMSMode}..: raw {value.toRaw.toArray}, PDU {hex pdu}"
        return 0
      writeMain host port debug value
  | "tick" :: rest =>
    match parseTick rest with
    | .error e =>
      IO.eprintln s!"error: {e}\n{usage}"
      return 2
    | .ok a => tickMain host port debug a
  | "run" :: rest =>
    match parseRun rest with
    | .error e =>
      IO.eprintln s!"error: {e}\n{usage}"
      return 2
    | .ok a => runMain host port debug a
  | _ =>
    IO.eprintln usage
    return 2
