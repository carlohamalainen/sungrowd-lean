import Sungrowd.Daemon
import Sungrowd.HttpClient

/-! # Push notifications when the inverter data goes stale: Go's `notify` package

The `Watcher` is a pure state machine over "when was the last good read", so it is tested with
Go's own cases and proved to alternate: never two "stale" alerts without a "recovered" between.

Publishing is an ntfy POST, with `httpRequest` (`Sungrowd/HttpClient.lean`). -/

namespace Sungrowd

open Std Async
open Modbus (msOffset)

/-! ## The watcher -/

inductive StaleEvent
  | none | wentStale | recovered
  deriving DecidableEq, Repr

/-- Go's `Watcher`. Times are Unix ms. -/
structure Watcher where
  thresholdMs : Nat
  /-- Process start: stands in for the last read until the first success. -/
  start       : Int
  stale       : Bool := false
  /-- The last read (or the start) the outage is measured from. -/
  staleSince  : Int := 0
  deriving Repr

/-- Go's `Observe`. Fresh means a read within the threshold. A brief blip shorter than the
threshold never alerts, and an outage alerts once. -/
def Watcher.observe (w : Watcher) (now : Int) (lastRead : Option Int) : StaleEvent × Watcher :=
  let ref := lastRead.getD w.start
  let fresh := match lastRead with
    | some t => now - t ≤ w.thresholdMs
    | none   => false
  if w.stale && fresh then (.recovered, { w with stale := false })
  else if !w.stale && !fresh && now - ref > w.thresholdMs then
    (.wentStale, { w with stale := true, staleSince := ref })
  else (.none, w)

/-- An alert flips the state, and nothing else does: so alerts alternate, starting with
`wentStale`, and an outage is reported once however long it lasts. -/
theorem Watcher.observe_alternates (w : Watcher) (now : Int) (lastRead : Option Int) :
    ((w.observe now lastRead).1 = .wentStale → !w.stale ∧ (w.observe now lastRead).2.stale) ∧
    ((w.observe now lastRead).1 = .recovered → w.stale ∧ !(w.observe now lastRead).2.stale) ∧
    ((w.observe now lastRead).1 = .none → (w.observe now lastRead).2.stale = w.stale) := by
  cases lastRead <;> simp only [observe] <;> (repeat' split) <;> simp_all

/-! Go's `watcher_test.go`. Minutes and seconds in ms from `start`. -/

private def sec (n : Nat) : Int := n * 1000
private def min (n : Nat) : Int := n * 60_000

private def events (w : Watcher) (obs : List (Int × Option Int)) : List StaleEvent :=
  (obs.foldl (fun (acc, w) (now, last) => let (e, w) := w.observe now last; (acc ++ [e], w))
    ([], w)).1

-- Stale, no repeat alert, then recovered.
#guard
  let last := sec 30
  let recoveredRead := last + min 5
  events { thresholdMs := 120_000, start := 0 }
    [(sec 35, some last), (last + sec 90, some last), (last + min 3, some last),
     (last + min 4, some last), (recoveredRead + sec 1, some recoveredRead),
     (recoveredRead + sec 2, some recoveredRead)]
  == [.none, .none, .wentStale, .none, .recovered, .none]

-- The outage is measured from the last read.
#guard ((({ thresholdMs := 120_000, start := 0 } : Watcher).observe (sec 30 + min 3) (some (sec 30))).2.staleSince
  == sec 30)

-- Never read: measured from the start, and the first read recovers.
#guard events { thresholdMs := 120_000, start := 0 }
    [(min 1, none), (min 3, none), (min 10 + sec 1, some (min 10))]
  == [.none, .wentStale, .recovered]

-- A brief blip (one tick in three missed) never alerts.
#guard
  let (obs, _) := (List.range 20).foldl (fun (acc, last) i =>
      let now := last + sec (i * 5)
      let last := if i % 3 != 0 then now else last
      (acc ++ [(now, some last)], last)) (([] : List (Int × Option Int)), (0 : Int))
  (events { thresholdMs := 120_000, start := 0 } obs).all (· == .none)

/-! ## ntfy -/

def ntfyServerEnvVar  : String := "SUNGROWD_NTFY_SERVER"
def ntfyServerDefault : String := "https://ntfy.sh"
def ntfyTopicEnvVar   : String := "SUNGROWD_NTFY_TOPIC"
/-- Go's watcher checks every 15 s. -/
def staleCheckMs      : Nat := 15_000

structure Ntfy where
  /-- e.g. `https://ntfy.sh`, without a trailing slash. -/
  server : String
  topic  : String

/-- Go's `NewNtfy`: none (disabled) without a topic. -/
def Ntfy.ofEnv : IO (Option Ntfy) := do
  let some topic ← IO.getEnv ntfyTopicEnvVar | return none
  if topic.isEmpty then return none
  let server := (← IO.getEnv ntfyServerEnvVar).getD ntfyServerDefault
  return some ⟨String.ofList (server.toList.reverse.dropWhile (· == '/')).reverse, topic⟩

/-- Go's `Publish`: POST `body` to the topic with ntfy's headers, a 10 s timeout, and log the
outcome. Never throws. -/
def Ntfy.publish (n : Ntfy) (log : Log) (title priority tags body : String) : IO Unit := do
  match ← httpRequest "POST" s!"{n.server}/{n.topic}" (body := some body)
      (headers := [("Title", title), ("Priority", priority), ("Tags", tags)]) with
  | .error e => log.error "ntfy: publish failed" [("title", title), ("err", e)]
  | .ok r =>
    if r.status < 200 || r.status ≥ 300 then
      log.error "ntfy: publish rejected" [("title", title), ("status", toString r.status)]
    else
      log.info "ntfy: published" [("title", title), ("priority", priority)]

/-- Go's `watchStaleness`: every 15 s, push on going stale and on recovering. Returns when
`stop` has a message. -/
def watchStaleness (shared : IO.Ref Shared) (log : Log) (n : Option Ntfy) (thresholdS : Nat)
    (startMs : Int) (stop : Std.Channel Unit) : IO Unit := do
  let some n := n
    | log.info s!"ntfy staleness notifications disabled ({ntfyTopicEnvVar} not set)"
  log.info "ntfy staleness notifications enabled" [("threshold", goDuration (thresholdS * 1000))]
  let mut w : Watcher := { thresholdMs := thresholdS * 1000, start := startMs }
  repeat
    let wait : Async Bool := do
      Selectable.one #[
        .case (← Selector.sleep (msOffset staleCheckMs)) fun _ => pure false,
        .case stop.recvSelector fun _ => pure true]
    if ← wait.block then break
    let now := (← Std.Time.Timestamp.now).toMillisecondsSinceUnixEpoch.val
    let s ← shared.get
    let (e, w') := w.observe now s.lastReadMs
    w := w'
    match e with
    | .wentStale =>
      let mut detail := match s.lastReadMs with
        | some t => s!"No fresh Modbus read for {goDuration (now - t).toNat}"
        | none   => "No successful Modbus read since the daemon started"
      if let some err := s.lastReadErr then detail := detail ++ s!" (last error: {err})"
      n.publish log "sungrowd: inverter data STALE" "high" "warning,zap" detail
    | .recovered =>
      n.publish log "sungrowd: inverter data recovered" "default" "white_check_mark"
        s!"Fresh Modbus reads again after {goDuration (now - w.staleSince).toNat} of stale data."
    | .none => pure ()

end Sungrowd
