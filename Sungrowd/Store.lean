import SQLite
import Sungrowd.Intent
import Sungrowd.Control

/-! # The database

The Go daemon's SQLite schema, verbatim, so a copy of Go's `sungrowd.db` can be imported once
(a one-way port: the Lean daemon owns its database from then on):

* `server_state`: one row (`id = 1`) holding the intent as JSON in `state_json`. We read Go's
  format and ours (see `Sungrowd/Intent.lean`), but write only ours, which Go can't read.
* `control_write`: an audit record of every control-register write attempt. Our `WriteOp` JSON
  has the same shape as Go's, so both daemons' records can be queried together.
* `solcast_raw`, `solcast_forecast`: created for compatibility; not used yet.

Every query uses the `sql!`/`exec!`/`query!` interpolation, so values are bound as parameters,
never spliced into SQL. Integers are bound as `Int64`: leansqlite binds a `Nat` as a blob. -/

namespace Sungrowd

open Sungrowd.Policy
open Sungrowd.Control

/-- Go's `store.schema`. -/
def schema : String := "
CREATE TABLE IF NOT EXISTS solcast_raw (
  id                    INTEGER PRIMARY KEY,
  raw_json              TEXT NOT NULL CHECK (json_valid(raw_json)),
  solcast_resource_id   TEXT NOT NULL,
  recorded_at           TEXT NOT NULL -- UTC RFC3339 (transaction time)
) STRICT;

CREATE INDEX IF NOT EXISTS solcast_raw_recorded_at ON solcast_raw(recorded_at);

CREATE TABLE IF NOT EXISTS solcast_forecast (
  download_id    INTEGER NOT NULL REFERENCES solcast_raw(id),
  period_end     TEXT    NOT NULL,   -- UTC RFC3339
  period_minutes INTEGER NOT NULL,   -- from ISO \"period\" (PT30M -> 30)
  pv_estimate    REAL    NOT NULL,   -- P50 (kW)
  pv_estimate10  REAL    NOT NULL,   -- P10 (kW)
  pv_estimate90  REAL    NOT NULL,   -- P90 (kW)
  PRIMARY KEY (download_id, period_end)
) WITHOUT ROWID, STRICT;

CREATE INDEX IF NOT EXISTS solcast_forecast_period_end ON solcast_forecast(period_end);

CREATE TABLE IF NOT EXISTS control_write (
  id          INTEGER PRIMARY KEY,
  recorded_at TEXT    NOT NULL,                            -- UTC RFC3339
  no_op       INTEGER NOT NULL,                            -- 1 if device already in intended state
  ok          INTEGER NOT NULL,                            -- 1 if the write succeeded (err is NULL)
  err         TEXT,                                        -- NULL on success
  op_json     TEXT    NOT NULL CHECK (json_valid(op_json)) -- full WriteOp; query with json_extract
) STRICT;

CREATE INDEX IF NOT EXISTS control_write_recorded_at ON control_write(recorded_at);

CREATE TABLE IF NOT EXISTS server_state (
  id         INTEGER PRIMARY KEY CHECK (id = 1),
  state_json TEXT NOT NULL CHECK (json_valid(state_json)),
  updated_at TEXT NOT NULL -- UTC RFC3339
) STRICT;
"

structure Store where
  db : SQLite

/-- Open (creating if need be) and apply the schema, with Go's pragmas: WAL, so readers don't
block the writer; a 5 s busy timeout; foreign keys on. -/
def Store.open (path : System.FilePath) : IO Store := do
  let db ← SQLite.open path (busyTimeoutMs := 5000)
  db.exec "PRAGMA journal_mode = WAL; PRAGMA foreign_keys = ON;"
  db.exec schema
  return ⟨db⟩

def nowRFC3339 : IO String := do
  return rfc3339OfUnix (← Std.Time.Timestamp.now).toSecondsSinceUnixEpoch.val

/-! ## Intent -/

/-- The `state_json` of the one `server_state` row, or `none` for a fresh database. -/
def Store.intentJson (s : Store) : IO (Option String) := do
  for json in ← s.db query!"SELECT state_json FROM server_state WHERE id = 1" as String do
    return some json
  return none

/-- Go's `loadIntent`: a fresh database is no schedule and no override. Errors are a bad row,
which the caller should not act on. -/
def Store.loadIntent (s : Store) (gridFuseAmps : Nat) : IO (Except String Intent) := do
  let some json ← s.intentJson | return .ok { window := none, override := none }
  return (Lean.Json.parse json >>= intentOfJson gridFuseAmps).mapError (s!"server_state: {·}")

/-- Replace the intent, in our format. -/
def Store.saveIntent (s : Store) (i : Intent) : IO Unit := do
  let json := (Lean.toJson i).compress
  let now ← nowRFC3339
  s.db exec!"INSERT INTO server_state (id, state_json, updated_at) VALUES (1, {json}, {now})
    ON CONFLICT(id) DO UPDATE SET state_json = excluded.state_json, updated_at = excluded.updated_at"

/-- Go's `updateIntent`: read, change, write in one transaction, so two writers (the worker
clearing an expired override, an HTTP handler setting a schedule) can't lose each other's
change. `immediate` takes the write lock before the read. -/
def Store.updateIntent (s : Store) (gridFuseAmps : Nat) (f : Intent → Intent) :
    IO (Except String Intent) :=
  s.db.transaction (mode := .immediate) do
    match ← s.loadIntent gridFuseAmps with
    | .error e => return .error e
    | .ok i =>
      let i' := f i
      s.saveIntent i'
      return .ok i'

/-! ## Control writes -/

/-- Go's `InsertControlWrite`. Returns the row id. -/
def Store.insertControlWrite (s : Store) (op : WriteOp) : IO Int64 := do
  let recordedAt := (Std.Time.DateTime.ofTimestamp op.recordedAt .UTC).toISO8601String
  let noOp : Int64 := if op.outcome matches .noOp then 1 else 0
  let err := op.outcome.err?
  let ok : Int64 := if err.isNone then 1 else 0
  let json := (Lean.toJson op).compress
  s.db exec!"INSERT INTO control_write (recorded_at, no_op, ok, err, op_json)
    VALUES ({recordedAt}, {noOp}, {ok}, {err}, {json})"
  s.db.lastInsertRowId

/-- Go's `GetControlWrites`: the latest `limit` write attempts, newest first, as their `op_json`. -/
def Store.recentControlWrites (s : Store) (limit : Nat) : IO (Array Lean.Json) := do
  let n : Int64 := limit.toInt64
  let rows ← (← s.db query!"SELECT op_json FROM control_write ORDER BY id DESC LIMIT {n}" as String).toList
  rows.toArray.mapM fun r => IO.ofExcept (Lean.Json.parse r)

end Sungrowd
