# Reviewing sungrowd-lean

A guide for working through the whole port, calmly and in order. About 6,000 lines: 5,000 of
Lean, plus the page, two Python scripts and the config. It's meant to be done over several
sittings: each part below stands on its own, ends with a checklist, and is small enough for one
session.

Tick the boxes as you go (`- [x]`). Write anything you find under **Notes** in each part, or in
[Findings](#findings) at the end, so nothing depends on memory.

## How to use this

- **Order.** Bottom up, in dependency order, so you never read code that uses something you
  haven't seen. The one exception: if time is short, do [the safety review](#part-0-the-safety-review-do-this-first)
  first. It is the part that can move energy in the house.
- **Each part** lists its files and their Go counterparts (in `tmp/sungrowd-go`), what the code
  does, what to read first, and questions to check. The questions are prompts, not a full list.
- **Evidence.** Most claims in the code are checked: `#guard`s and theorems run on every
  `lake build`, and `lake test` runs the IO tests. A part says which checks cover it, so you can
  look at *what* is tested rather than re-testing it by hand.
- **Provenance.** The early commits (Modbus, the register model, the first policy and its
  proofs) came first and were done slowly; most of what came after, from `sungrowd tick` on, was
  written with Claude, quickly, and tested with fakes. `jj log -r 'files("Sungrowd/X.lean")'`
  shows a file's history. Read the later parts with more suspicion.

### Before you start

```
lake build        # compiles everything, runs every #guard and checks every proof
lake test         # the IO tests (database), 13 checks
```

Both should be clean: no errors, no warnings, no `sorry`. A quick self-check:

```
grep -rn "sorry\|admit" Modbus Sungrowd Main.lean Tests.lean    # expect nothing
```

**Your shell has live credentials.** It exports the Go daemon's real settings
(`SOLCAST_API_KEY`, `SOLCAST_RESOURCE_ID`, `SUNGROWD_NTFY_TOPIC`, `SUNGROWD_PROMETHEUS_URL`,
`SUNGROWD_WINET_HOST`, `SUNGROWD_DB`, …). Anything you run inherits them. To try the daemon
safely, strip them and use the fakes:

```
uv run --no-project scripts/fake_inverter.py &
env -u SOLCAST_API_KEY -u SOLCAST_RESOURCE_ID -u SUNGROWD_NTFY_TOPIC -u SUNGROWD_NTFY_SERVER \
    -u SUNGROWD_PROMETHEUS_URL \
    SUNGROWD_WINET_HOST=127.0.0.1 SUNGROWD_WINET_PORT=15020 SUNGROWD_DB=tmp/review.db \
    SUNGROWD_LISTEN=127.0.0.1:9180 SUNGROWD_SCHEDULE=samples/adaptive-all-day.json \
    .lake/build/bin/sungrowd run          # shadow mode: never writes to the inverter
```

Then open <http://127.0.0.1:9180/>.

### The map

Arrows point at what a module imports.

```
Modbus.Codec ← Modbus.Client
                  ↑
Sungrowd.Registers   Sungrowd.Control ← Sungrowd.Policy ← Sungrowd.Intent ← Sungrowd.Log
   (RunningState, PowerFlow)    ↑                                ↑
                  Sungrowd.Inverter ─────────────────────────────┘
                         ↑
       Sungrowd.Store ← Sungrowd.Daemon ← Sungrowd.Notify
                         ↑
   HttpClient ← Prometheus, Solcast ← Sungrowd.Http ← Sungrowd.Ui ← Main
                Format ↗
```

| Part | Files | Lines | Go counterpart |
|---|---|---|---|
| [0. Safety review](#part-0-the-safety-review-do-this-first) | write paths across files | — | `internal/server/server.go` |
| [1. Modbus](#part-1-modbus) | `Modbus/Codec.lean`, `Modbus/Client.lean` | 340 | a Modbus library |
| [2. Register model](#part-2-the-register-model) | `Registers`, `RunningState`, `PowerFlow`, `Examples`, `Inverter` | 1,060 | `internal/sungrow` |
| [3. Control registers](#part-3-control-registers-and-writes) | `Control.lean` | 300 | `internal/sungrow/sungrow.go` |
| [4. Policy](#part-4-the-control-policy) | `Policy.lean` | 490 | `internal/server/server.go` |
| [5. Intent JSON](#part-5-intent-json) | `Intent.lean` | 370 | `server.go` (persisted state) |
| [6. CLI](#part-6-the-cli) | `Main.lean` (minus `runMain`) | 190 | `cmd/`, `main.go` |
| [7. Store](#part-7-the-database) | `Store.lean`, `Tests.lean` | 240 | `internal/store` |
| [8. Daemon](#part-8-the-daemon) | `Daemon.lean`, `Log.lean`, `runMain` | 450 | `server.go` `Run`/`handle`, `main.go` |
| [9. HTTP API](#part-9-the-http-api) | `Http.lean` | 315 | `main.go` handlers |
| [10. Outbound HTTP, alerts](#part-10-outbound-http-and-alerts) | `HttpClient.lean`, `Notify.lean` | 220 | `internal/notify` |
| [11. Actuals](#part-11-prometheus-actuals-and-formatting) | `Prometheus.lean`, `Format.lean` | 290 | `internal/promquery`, `server.go` |
| [12. Solcast](#part-12-solcast) | `Solcast.lean` | 245 | `internal/solcast` |
| [13. Web UI](#part-13-the-web-ui) | `Ui.lean`, `ui/` | 660 + page | `ui.go`, `index.html` |
| [14. Odds and ends](#part-14-odds-and-ends) | scripts, samples, README, lakefile | — | — |

---

## Part 0: the safety review (do this first)

The one thing this program must never get wrong is writing the inverter's EMS registers
(13049–13051). Everything else is reporting. This part follows every path that can write, end
to end, across files you will read properly later.

**There are three ways to write, and they all end in `safeWriteControl`**
(`Sungrowd/Control.lean:282`), which is the only caller of `Client.writeMultipleRegisters`
(`Modbus/Client.lean:166`):

1. `sungrowd write …` (`Main.lean:96` `writeMain`): you asked for it on the command line.
   `--dry-run` prints the PDU instead.
2. `sungrowd tick … --apply` (`Main.lean:131` `tickMain`, the write at about line 184). Without
   `--apply` it prints "would write".
3. `sungrowd run --apply` (`Sungrowd/Daemon.lean:148` `applyControl`). Without `--apply`, the
   check at about line 163 logs "would change" and returns before any connection is made.

**What a write does** (`safeWriteControl`): it reads the three registers; if the inverter
already does what we want (`heldBy`, `Control.lean:203`) it records a no-op and sends nothing;
otherwise it writes all three, reads them back, and reports `ok`, `mismatch`, `unverified` or
`notSent`. Every attempt in the daemon is audited in `control_write`.

**What can be written.** The types limit it: `ControlRegisters` (`Control.lean:135`) holds an
`EMSMode` (self-consumption or forced), a `Command` (charge, discharge, stop) and a
`ForcedPower` whose `le_max` field proves `watts ≤ 5000`. So no value outside those can reach
the wire, whatever the policy computes. The policy's adaptive command carries
`cmdOk : CmdOk cmdW` (a multiple of 100 W, between 0 and the maximum) in its state.

Check:

- [ ] `grep -n "writeMultipleRegisters" -r Modbus Sungrowd Main.lean` finds only the definition
      and `safeWriteControl`.
- [ ] `grep -n "safeWriteControl" -r Sungrowd Main.lean` finds only the three paths above.
- [ ] Each of the three paths writes only when you asked: `write` (an explicit command),
      `tick --apply`, `run --apply`. Follow `args.apply` in `tickMain` and `applyControl`.
- [ ] `ForcedPower.ofWatts?` (`Control.lean:100`) rejects anything over `maxForcedPowerW`, and
      that constant (`Control.lean:77`, 5000) is what you want for this inverter. Go's default is
      5.8 kW (`SUNGROWD_MAX_FORCED_POWER_KW`); this port has no such setting, so 5000 W is a hard
      limit.
- [ ] `heldBy` (`Control.lean:203`) can only *skip* a write when the inverter already behaves
      as asked; registers we can't decode (e.g. EMS mode 3) are never "held", so we write.
      `heldBy_toRaw` proves registers we wrote and read back exactly count as held.
- [ ] The daemon's control cache (`applyControl`, `controlReconcileMs` 30 s) can skip a read,
      never a needed write: it only skips when the cached registers already `heldBy` the
      decision.
- [ ] **The HTTP API can change what the daemon does** (`/control/*`, `/ui/action/*`), and the
      server listens on `0.0.0.0:9180` with no authentication, as Go's does. Anyone on the LAN
      can set an override. Decide whether that's acceptable (it was for Go).
- [ ] Shutdown (`Daemon.loop`) leaves the inverter as it is, even mid-override (Go does the
      same). A forced charge keeps going until something changes it.

**Notes**

---

## Part 1: Modbus

**Files:** `Modbus/Codec.lean` (166), `Modbus/Client.lean` (171).

**What:** Modbus TCP framing (MBAP header), the read (FC 3/4) and write-multiple (FC 16)
requests and their responses; a client with a deadline per connection, transaction ids, and an
optional hex trace (`SUNGROWD_DEBUG`).

Read: `Codec.lean` top to bottom, then `Client.request` (`Client.lean:118`) and
`recvExact` (`Client.lean:85`).

Check:

- [ ] The `!` lookups can't panic: `Header.decode` (`Codec.lean:88`) checks
      `b.size < Header.size` first; `checkResponse` (`Codec.lean:116`) checks
      `body.size == 0` and `body.size < 2`; `checkResponse pdu[0]!` (`Client.lean:151`) indexes
      our own request PDU, never empty. *Optional exercise:* replace them with `b[i]'h` and
      proofs, as `getU16` (`Codec.lean:42`) already does.
- [ ] `recvExact` is `partial`: each loop either grows `acc`, or fails on the deadline or EOF.
      Convince yourself it can't spin. (`remainingMs` hits 0, then `.timeout`.)
- [ ] The MBAP length handling (`Client.lean:139`): `len - 1` is only reached after
      `2 ≤ len ≤ 254`. `Nat` subtraction truncates at 0, so that check is what keeps it honest.
- [ ] `ValidReadQuantity` / `ValidWriteQuantity` bound the register counts at the type level
      (125 and 123).
- [ ] `checkWriteEcho` confirms the inverter echoed our address and count.

Evidence: 19 `#guard`s in `Codec.lean`; `Header.size_encode` (the encoded header is 7 bytes).

**Notes**

---

## Part 2: the register model

**Files:** `Sungrowd/Registers.lean` (284), `RunningState.lean` (179), `PowerFlow.lean` (123),
`Examples.lean` (182), `Inverter.lean` (290).

**What:** the Home Assistant Sungrow YAML (as JSON, `reference/`) parsed into `Sensor`s; sensors
grouped into contiguous `ReadBlock`s; raw words decoded (`int16`/`uint32`/word swap/NaN
sentinel) and scaled exactly; the running-state and power-flow codes decoded.
`Inverter.lean` (moved out of `Main` later) holds the metric list, decoding, block building
and the controller's `snapshotOf`.

Read: `Registers.lean`, then `Inverter.lean` from `metricDefs` (line 52) down.

Check:

- [ ] `metricDefs` (`Inverter.lean:52`): every metric name, help string and kind matches Go's
      Prometheus metrics, since dashboards and the Prometheus actuals (Part 11) depend on them.
- [ ] `decodeRaw` (`Inverter.lean:131`): the NaN sentinel is filtered *before* scaling, and the
      `uint32`/`int32` word order follows `swap`.
- [ ] `scaled` / `withDecimals` (`Inverter.lean:111`, `123`): exact, no floats.
- [ ] `snapshotOf` (`Inverter.lean:272`): SOC in tenths from `sg_battery_level`, grid power from
      `sg_battery_export_power_raw` (+ export / − import), battery power from `sg_battery_power`
      (+ discharge / − charge). The policy's signs depend on these.
- [ ] `brisbaneMinute` (`Inverter.lean:262`) assumes UTC+10 all year, which is right for
      Brisbane (no daylight saving) and is what Go does.

Evidence: `Slot.sensors_*` and `ReadBlock.mem_sensors` (slots keep their sensors through
updates), `RunningState.ofRaw?_toRaw` / `toRaw_of_ofRaw?`, `PowerFlow.toRaw_flags` (decoding
loses no bits), 14 `#guard`s in `Examples.lean`, 8 in `Inverter.lean`.

**Notes**

---

## Part 3: control registers and writes

**File:** `Sungrowd/Control.lean` (304). `Action` and `heldBy` were added later.

**What:** the three EMS registers as types (`EMSMode`, `Command`, `ForcedPower`,
`ControlRegisters`) with round-trip proofs; `Action`, the four things we ask of the inverter;
`safeWriteControl` and its audit record `WriteOp`.

Read: top to bottom. Part 0 already covered the write path; here, check the types.

Check:

- [ ] Raw values: mode 0 (self-consumption) and 2 (forced); command 0xAA charge, 0xBB discharge,
      0xCC stop. Compare with Go's `internal/sungrow/sungrow.go`.
- [ ] `ForcedPower`'s `step : watts % 10 = 0` matches the inverter's 10 W resolution, and
      `ofWatts?` rounds *down* to it.
- [ ] `Action.ofRegisters` (`Control.lean:186`) says what the inverter actually does with a set
      of registers: it ignores command and power outside forced mode, and power for a stop.
      `Action.ofRegisters_registers` proves `ofRegisters ∘ registers = id`.
- [ ] `WriteOp`'s JSON (`Control.lean:271`) has the same shape as Go's, because both daemons'
      `control_write` rows sit in one table after migration.

Evidence: `EMSMode`/`Command`/`ForcedPower`/`ControlRegisters` round trips,
`Action.ofRegisters_registers`, `ControlRegisters.heldBy_toRaw`, 7 `#guard`s.

**Notes**

---

## Part 4: the control policy

**File:** `Sungrowd/Policy.lean` (490). Refactored later: the `cmdOk` invariant, `Action`
overrides, `adaptiveTick`.

**What:** a pure function, `tick intent snapshot now minute state → (effective intent,
decision, state)`. The override wins; otherwise, inside a charge window, fixed-rate charging or
the adaptive controller (grid-import ceiling, 500 W/tick ramp, 100 W quantum with 60 W
hysteresis) until the SOC target latches; outside it, self-consumption.

Read: `TimeOfDay` and `ChargeWindow` (to line 110), the adaptive controller (`adaptiveStep`,
`hystQuantize`, line 132), `CmdOk` (line 167), `ControllerState` (line 194), `decide` (line
258), `tick` (line 287), then the theorems and the scenarios at the end.

Check:

- [ ] Compare `decide` with Go's `handle` branch by branch: override, no window, outside the
      window, missing SOC (`leave`), target reached (the latch), fixed, adaptive.
- [ ] The SOC latch: where `targetReached` is set and where it is cleared (a new intent, leaving
      the window).
- [ ] `Decision.leave` (no fresh SOC) never writes anything; see Part 8.
- [ ] The theorems say what you want them to say. In plain words:
  - `adaptiveStep_nonneg`, `adaptiveStep_le_max`, `adaptiveStep_ok`: the setpoint stays in
    `[0, max]`.
  - `hystQuantize_ok`, `hystQuantize_ladder`: the command stays on the 100 W ladder, in range.
  - `adaptiveStep_ramp`: it climbs at most 500 W per tick.
  - `adaptiveStep_cut`: over the ceiling, it drops straight to what the ceiling allows.
  - `decide_override`: an override always decides.
  - `decide_no_charge_at_target`: at or above the target SOC (no override), it never charges.
  - `decide_outside_window`: outside the window (no override), it hands back to
    self-consumption.
- [ ] What isn't proved: that the controller converges, or anything about time. The scenarios
      (`#guard`s at the end) exercise those.

Evidence: 12 theorems, 26 `#guard`s.

**Notes**

---

## Part 5: intent JSON

**File:** `Sungrowd/Intent.lean` (372).

**What:** what the user asked for (`charge_window`, `manual_override`) to and from JSON, in our
format, "Clojure-style" (absent keys rather than nulls). It also **reads** Go's formats (its
`schedule.json` and its persisted `server_state`), so a Go database can be imported once; it
never writes them. Plus the controller state's JSON, for `tick --state`.

Read: the module docstring, then the helpers (to line 60), schedules (line 70–140), overrides
(line 159–215), `intentOfJson`/`intentOfFile` (line 222–240), and the `#guard`s.

Check:

- [ ] Unknown keys are errors (`checkKeys`), so a typo isn't silently ignored.
- [ ] How Go's formats are told apart: an `enabled` key means a Go schedule, a `registers` key a
      Go override.
- [ ] A Go override's registers become an `Action` through `Action.ofRegisters`, so a Go
      "self_consumption + charge 3000 W" reads as plain self-consumption. Is that what you want?
- [ ] `controllerStateOfJson` (line 250) re-checks `CmdOk` rather than trusting the file.
- [ ] `roundTrips` (line 350): our own JSON reads back to the same value.

Evidence: 25 `#guard`s, including the round trips and Go's real `schedule.json`.

**Notes**

---

## Part 6: the CLI

**File:** `Main.lean` (337), apart from `runMain` (Part 8).

**What:** `sungrowd` (read the sensors), `control` (read the EMS registers), `write …`,
`tick <intent> [--state] [--apply]`, `run [--apply]`.

Check:

- [ ] `parseWrite` (`Main.lean:62`) only accepts the forms in `usage`.
- [ ] `tickMain` (`Main.lean:131`): the state file is written *before* the write is attempted,
      and the "already holds it" check uses `heldBy`.
- [ ] Exit codes: 2 for usage and configuration errors.

**Notes**

---

## Part 7: the database

**Files:** `Sungrowd/Store.lean` (132), `Tests.lean` (107).

**What:** Go's SQLite schema, verbatim, via leansqlite. `server_state` holds the intent (one
row); `control_write` audits every write attempt; the Solcast tables come in Part 12. WAL mode,
5 s busy timeout, foreign keys on.

Check:

- [ ] `schema` (`Store.lean:25`) is identical to Go's `internal/store` schema (diff them).
- [ ] Every query uses the `exec!`/`query!` interpolation, so values are bound parameters, never
      spliced into SQL. Integers are `Int64`, because leansqlite binds `Nat` as a blob.
- [ ] `loadIntent` (`Store.lean:89`): no row is the empty intent, and a bad row is an **error**,
      never a default. The daemon then leaves the inverter alone.
- [ ] `updateIntent` (`Store.lean:103`) is read, change, write in an immediate transaction, so
      the worker clearing an expired override and an HTTP handler can't lose each other's
      change.
- [ ] One-way port: we read Go's `state_json` but write ours, so Go can't use the database
      afterwards. That was your decision; the README says so.
- [ ] `Tests.lean`: what the 13 checks cover (fresh database, Go's row, a bad row, save/load,
      update, control-write rows, reopening).

**Notes**

---

## Part 8: the daemon

**Files:** `Sungrowd/Daemon.lean` (283), `Sungrowd/Log.lean` (68), `runMain` in `Main.lean`
(line 194).

**What:** Go's worker. Every 5 s, at startup, and when an HTTP handler wakes it: load the
intent, read the sensors (3 tries, each on a fresh connection, at most one new connection per
second), decide, clear an expired override, and apply the decision. `runMain` wires it all up:
settings, seeding a fresh database from `SUNGROWD_SCHEDULE`, the HTTP server, the staleness
watcher, signals.

Read: the module docstring, `Shared` (line 70), `withConn`/`readWithRetry` (line 111),
`applyControl` (line 148), `handle` (line 203), `loop` (line 258), then `runMain`.

Check:

- [ ] Constants match Go: tick 5 s, 3 read attempts, 1 s connection spacing, 30 s reconcile,
      120 s staleness.
- [ ] `handle`: an unreadable intent logs and returns **before** any decision; a failed sensor
      read gives an empty snapshot, which the policy turns into `leave` (no write).
- [ ] Expired overrides: the clear only removes the override if it is still the one that
      expired (`clear`, line 235), so one set in the meantime survives. In shadow mode this
      still writes the database (but never the inverter).
- [ ] Concurrency: the worker and the HTTP server share `IO.Ref Shared`, updated with
      `modify`; each HTTP request opens its own database connection.
- [ ] `loop`: the wake channel holds at most one message (Go's buffered-1 channel), and a wake
      doesn't shift the 5 s schedule. Signal waiters are started up front, so a SIGTERM during
      the first tick isn't lost; a tick in progress finishes before shutdown.
- [ ] `runMain`: seeding only happens when the database has no row. The initial control read
      failing starts the daemon degraded, rather than exiting (Go's behaviour).
- [ ] `Log.lean`: Go's slog text format; levels from `SUNGROWD_LOG_LEVEL`.

Evidence: tested against `scripts/fake_inverter.py` (the ramp, retries on injected exceptions,
an unreachable inverter, expiry, a bad row). The real-inverter runs (the blog post) used
`tick`, which shares `Policy.tick` and `safeWriteControl` with the daemon, but `run` itself
has only met the fake.

**Notes**

---

## Part 9: the HTTP API

**File:** `Sungrowd/Http.lean` (315).

**What:** `/metrics` (Prometheus text), `/healthz` (503 when stale), `/diag`,
`POST /control/override`, `POST /control/schedule`, `/actual`, `/forecast`, `POST /solcast`.
Routing is in `Api.respond` (line 218); the UI routes are added in Part 13.

Check:

- [ ] `metricsText`: names and types match Go's; the NaN sentinel is skipped.
- [ ] `overrideOfRequest` (line 87): an `"HH:MM"` expiry is the *next* time Brisbane's clock
      shows it; an expiry in the past is a 400 (Go couldn't get one); `null` or an empty body
      clears.
- [ ] Bodies are capped at 64 KiB (`maxBodyBytes`); a bad body is a 400 and changes nothing.
- [ ] Each change goes through `updateIntent`, then wakes the worker.
- [ ] `/diag` is our own shape, not Go's (Go's lists Solcast settings, which ours doesn't yet).
- [ ] Wrong methods are 405s.

Evidence: 19 `#guard`s (metrics, health, `nextOccurrence`, override parsing); curl tests against
the fake inverter.

**Notes**

---

## Part 10: outbound HTTP and alerts

**Files:** `Sungrowd/HttpClient.lean` (67), `Sungrowd/Notify.lean` (150).

**What:** `Std` has no HTTP client yet, so `httpRequest` runs `curl`, giving it the whole
request on stdin as a config file (`--config -`). That keeps the Solcast key out of `ps`. It's
the only subprocess in the program. `Notify.lean` ports Go's staleness watcher and ntfy
pushes.

Check:

- [ ] `curlQuote` (line 16) escapes everything curl's config syntax needs (backslash, quote,
      newline, CR, tab). A value with other control characters?
- [ ] `httpRequest` reads stdout fully, then stderr. If curl ever wrote more than a pipe buffer
      (64 KiB) to stderr before finishing stdout, this would deadlock; in practice curl writes a
      line. Is that acceptable?
- [ ] Every caller sets a timeout (10 s, or 30 s for Solcast).
- [ ] `Watcher.observe` (line 34) against Go's `watcher.go`; `observe_alternates` proves
      alerts alternate (never two "stale" without a "recovered").
- [ ] Without `SUNGROWD_NTFY_TOPIC` nothing is sent.
- [ ] If you find a native HTTP client library, this file is the only place to change.

Evidence: Go's three watcher tests as `#guard`s; the theorem; tested against a fake ntfy
server (stale, recovered, unreachable, disabled).

**Notes**

---

## Part 11: Prometheus actuals and formatting

**Files:** `Sungrowd/Prometheus.lean` (111), `Sungrowd/Format.lean` (177).

**What:** Go's read-only Prometheus client (`instant`, `range`) and its queries: PV kWh per day
(the lifetime counter's delta, to 0.1), PV today so far, today's PV curve, and a day's SOC curve.
`Format.lean` holds `Dec`, an exact decimal for Go's `%.Nf` without floats; HTML escaping; and
Brisbane dates (Hinnant's civil-date algorithms).

Check:

- [ ] `pvDelta`: a counter reset in the window counts as 0, as in Go.
- [ ] `Dec.fixed` rounds half away from zero; Go rounds the nearest float, so the two can differ
      at exact halves (1.125 kW: we print 1.13, Go may print 1.12). Cosmetic, but you should
      know.
- [ ] `Dec.short` is `partial`: it terminates because `e` decreases.
- [ ] `parseDate?` rejects impossible dates by round-tripping (`2026-02-30` fails).
- [ ] `dayLabel`'s weekday table starts on Thursday (1970-01-01).

Evidence: 19 `#guard`s in `Format.lean` (rounding, signs, a leap day, invalid dates, known
timestamps); tested against a fake Prometheus.

**Notes**

---

## Part 12: Solcast

**File:** `Sungrowd/Solcast.lean` (244).

**What:** `POST /solcast` (a systemd timer, as for Go) downloads the rooftop forecast, and stores
the raw JSON and its half-hour periods. Reads take the freshest download that covers the whole
local day (48 half-hours), and apply the site correction (×0.62, flagging days where P10 is
under half of P50) on the way out.

Check:

- [ ] `Store.forecastForDay` (line 191) uses Go's SQL verbatim, including the
      `datetime(period_end, '+36000 seconds', '-'||period_minutes||' minutes')` trick.
- [ ] Values are floats, as in Go and the `REAL` columns. `Dec.ofFloat` converts them only for
      printing.
- [ ] `Correction.apply` against Go's `Apply`; the defaults (0.62, 0.5) and their rationale in
      the docstring.
- [ ] Go refuses to start without `SOLCAST_*`; this port makes them optional (`/solcast` is a
      503). Your call.

Evidence: Go's three Solcast tests as `#guard`s. **Cross-checked against Go itself:** Go's
`ForecastForDay` and Lean's `/forecast`, on a copy of Go's database (10–14 June), gave
identical JSON; Go's `sparkline` and ours, identical for a real forecast.

**Notes**

---

## Part 13: the web UI

**Files:** `Sungrowd/Ui.lean` (658), `ui/index.html` and `ui/datastar.js` (Go's, byte for byte).

**What:** Go's Datastar page, served verbatim (only `{{.MaxKW}}` and `{{.FuseA}}` filled in),
driven by the official Datastar Lean SDK: one SSE stream per open page re-renders the panels
(live 500 ms, clock 1 s, slow panels 10 s, compare 60 s); the action buttons `POST` signals and
get fragments back.

Read: the renderers (`renderStats` onwards) side by side with `ui.go`; then the handlers
(`Api.uiUpdates`, `uiAction`, the five actions) and `Api.handler`.

Check:

- [ ] `cmp ui/index.html tmp/sungrowd-go/index.html` and the same for `datastar.js`: identical.
- [ ] Each renderer's format strings against Go's: classes, wording, `%.2f` / `%+.2f`, the
      characters `—`, `–`, `·`, `→`, `×`.
- [ ] The actions reach the database through the same `updateIntent` as the API, and say what
      Go says on success and failure.
- [ ] Each SSE stream opens its own database connection, and runs Prometheus queries as curl
      processes: 2 every 10 s and up to 10 a minute per open page.
- [ ] `readSignals` (SDK) reads the request body without a size limit, unlike the API's 64 KiB.
- [ ] "Disable" removes the window; Go kept a disabled window's fields.
- [ ] **Not yet tried in a browser.** Everything was checked with curl. Open it and click
      through each button.

Evidence: 3 `#guard`s here, plus `Format`'s; the forecast panel and sparkline cross-checked
against Go on real data.

**Notes**

---

## Part 14: odds and ends

- [ ] `scripts/fake_inverter.py`: uses `logging`, run with `uv`; `FAKE_*` settings in its
      docstring.
- [ ] `scripts/yaml_to_json.py`: the one-off conversion of the Home Assistant YAML.
- [ ] `samples/*.json`: our intent format.
- [ ] `lakefile.toml`: leansqlite `v4.36.0`, datastar `v1.1.0`, both pinned to tags.
- [ ] `README.md` against the code: settings and their defaults, endpoints, the migration note.
- [ ] `.gitignore` includes the database's `-wal` and `-shm` files.

**Notes**

---

## Appendix A: where the port differs from Go on purpose

| Area | Go | Lean | Why |
|---|---|---|---|
| Intent JSON | `enabled`, `registers`, nulls | absent keys, `action` | your redesign; Go's still read |
| Database | shared format | one-way: reads Go's, writes ours | your decision |
| Disabled schedule | kept, `enabled: false` | removed | no "disabled window" type |
| Write comparison | raw registers | the action (`heldBy`) | no needless rewrites of e.g. "stop 3000 W" |
| Override expiry in the past | can't happen (`HH:MM` only) | 400 | the API also takes RFC 3339 |
| Audit of an unsent write | not recorded | recorded as `notSent` | every attempt is audited |
| Max forced power | `SUNGROWD_MAX_FORCED_POWER_KW` (5.8) | fixed 5000 W | a proved bound in the types |
| Solcast credentials | required at startup | optional | runs without Solcast |
| `/diag` | Go's diagnostics shape | our own | different state |
| `%.Nf` rounding | nearest float | exact, half away from zero | no floats in display code |
| HTTP client | Go's `net/http` | `curl` | no client in Lean's `Std` yet |
| WiNet dongle reboot | yes | not ported | rarely used |

## Appendix B: the checks behind it

- **Theorems** (30, no `sorry`): Codec 1, Registers 4, RunningState 2, PowerFlow 2,
  Control 8, Policy 12, Notify 1. Part 3, Part 4 and Part 10 state the important ones in plain
  words.
- **`#guard`s** (about 165), run on every build: Codec 19, Examples 14, Control 7, Policy 26,
  Intent 25, Inverter 8, Log 6, Http 19, Notify 4, Format 19, Solcast 5, Ui 3, and a few
  others.
- **`lake test`**: 13 database checks.
- **Manual tests**, not repeatable from the repo: fakes for the inverter (in the repo), ntfy
  and Prometheus (not in the repo); the Go cross-checks; your runs against the real inverter.

## Findings

Anything you'd change, question or want explained. One line each is enough; mark which part.

-
