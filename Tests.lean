import Sungrowd.Store

/-! # Tests that need IO

Run with `lake test`. Each test gets a fresh database in a temporary directory.

`lake test -- <path/to/sungrowd.db>` also loads the intent from that database (read only) and
prints it, e.g. to check a copy of the Go daemon's database. -/

open Sungrowd Sungrowd.Policy Sungrowd.Control

structure Results where
  passed : Nat := 0
  failed : Array String := #[]

abbrev TestM := StateT Results IO

def check (name : String) (ok : Bool) (detail : String := "") : TestM Unit :=
  if ok then modify fun r => { r with passed := r.passed + 1 }
  else do
    IO.eprintln s!"FAIL {name}{if detail.isEmpty then "" else s!": {detail}"}"
    modify fun r => { r with failed := r.failed.push name }

def withStore (k : Store → TestM Unit) : TestM Unit := do
  let dir ← IO.FS.createTempDir
  try k (← Store.open (dir / "test.db"))
  finally IO.FS.removeDirAll dir

/-- The row in the Go repository's own `sungrowd.db`. -/
def goStateJson : String :=
  "{\"charge_window\":{\"enabled\":true,\"start\":\"00:00\",\"end\":\"06:00\",\"charge_watts\":2000,\"max_soc\":100},\"manual_override\":null}"

def storeTests : TestM Unit := do
  withStore fun s => do
    check "fresh database has no intent row" ((← s.intentJson).isNone)
    let i ← s.loadIntent 20
    check "fresh database is the empty intent" (i.toOption == some { window := none, override := none })

  withStore fun s => do
    s.db exec!"INSERT INTO server_state (id, state_json, updated_at)
      VALUES (1, {goStateJson}, '2026-06-10T11:48:27Z')"
    match ← s.loadIntent 20 with
    | .ok { window := some { mode := .fixed p _, maxSOC := 100, .. }, override := none } =>
      check "reads Go's state_json" (p.watts == 2000) s!"watts {p.watts}"
    | other => check "reads Go's state_json" false s!"{repr (other.map (·.window.isSome))}"

  withStore fun s => do
    let bad := "{\"charge_window\": {\"mode\": \"turbo\"}}"
    s.db exec!"INSERT INTO server_state (id, state_json, updated_at)
      VALUES (1, {bad}, '2026-06-10T11:48:27Z')"
    let r ← s.loadIntent 20
    check "a bad row is an error, not a default" (r.toOption.isNone)

  withStore fun s => do
    let i : Intent := { window := none, override := some ⟨.stop, some 1792958400⟩ }
    s.saveIntent i
    check "saveIntent then loadIntent" ((← s.loadIntent 20).toOption == some i)
    s.saveIntent { window := none, override := none }
    check "saveIntent replaces the row" ((← s.intentJson) == some "{}")
    let n ← s.db query!"SELECT count(*) FROM server_state" as Int64
    check "one server_state row" ((← n.toList) == [1])

  withStore fun s => do
    s.saveIntent { window := none, override := some ⟨.selfConsumption, some 1000⟩ }
    let r ← s.updateIntent 20 fun i => { i with override := none }
    check "updateIntent returns the new intent" (r.toOption == some { window := none, override := none })
    check "updateIntent persists" ((← s.loadIntent 20).toOption == some { window := none, override := none })

  withStore fun s => do
    let op : WriteOp := {
      recordedAt := Std.Time.Timestamp.ofSecondsSinceUnixEpoch ⟨1795412249⟩
      before := some #v[2, 204, 3000]
      intended := (Action.charge ⟨500, by decide, by decide⟩).registers
      after := some #v[2, 170, 500]
      outcome := .ok }
    let id ← s.insertControlWrite op
    check "insertControlWrite returns the row id" (id == 1)
    let rows ← s.db query!"SELECT recorded_at, no_op, ok, err,
        json_extract(op_json, '$.intended.forced_power_w') FROM control_write"
      as (String × Int64 × Int64 × Option String × Int64)
    let rows ← rows.toList
    check "control_write row, as Go writes it"
      (rows == [("2026-11-23T05:37:29Z", 0, 1, none, 500)]) s!"{rows}"
    let failed : WriteOp := { op with after := none, outcome := .notSent .timeout }
    discard <| s.insertControlWrite failed
    let errs ← s.db query!"SELECT ok, err FROM control_write WHERE id = 2" as (Int64 × Option String)
    check "a failed write has ok = 0 and its error"
      ((← errs.toList) == [(0, some "control write was not sent (inverter unchanged): timeout")])

  -- Reopening applies the schema again, which must be harmless.
  let dir ← IO.FS.createTempDir
  try
    let s ← Store.open (dir / "test.db")
    s.saveIntent { window := none, override := some ⟨.stop, none⟩ }
    let s' ← Store.open (dir / "test.db")
    check "reopen keeps the data" ((← s'.loadIntent 20).toOption.map (·.override.isSome) == some true)
  finally IO.FS.removeDirAll dir

def main (args : List String) : IO UInt32 := do
  let ((), r) ← storeTests.run {}
  IO.println s!"{r.passed} passed, {r.failed.size} failed"
  for path in args do
    let s ← Store.open path
    match ← s.loadIntent 20 with
    | .ok i    => IO.println s!"{path}: intent {(Lean.toJson i).compress}"
    | .error e => IO.println s!"{path}: {e}"
  return if r.failed.isEmpty then 0 else 1
