# sungrowd-lean

Porting <https://codeberg.org/carlohamalainen/sungrowd-go> to Lean4.

# Usage

```
lake build
export SUNGROWD_WINET_HOST=192.168.1.x   # the inverter (WiNet-S dongle)
```

Read the sensors listed in `metricDefs` (`Main.lean`):

```
.lake/build/bin/sungrowd
```

Read the EMS control registers (13049 mode, 13050 command, 13051 forced power):

```
.lake/build/bin/sungrowd control
```

Write the control registers.

```
# What would be sent, without connecting:
.lake/build/bin/sungrowd write forced stop --dry-run

# Forced mode, battery idle:
.lake/build/bin/sungrowd write forced stop

# Forced charge / discharge at 3 kW:
.lake/build/bin/sungrowd write forced charge 3000
.lake/build/bin/sungrowd write forced discharge 3000

# Hand control back to the inverter's own EMS:
.lake/build/bin/sungrowd write self-consumption

# Trace every Modbus frame (TX/RX hex) to stderr:
SUNGROWD_DEBUG=1 .lake/build/bin/sungrowd write forced charge 3000
```

Run the control policy once (`Sungrowd/Policy.lean`): read the inverter, decide, and print
what it would write. The intent file is ours (see `Sungrowd/Intent.lean`), for example

```json
{"charge_window": {"mode": "adaptive", "start": "01:00", "end": "06:00",
                   "ceiling_watts": 4320, "max_soc": 80},
 "manual_override": {"action": "charge", "watts": 3000, "expiry": "2026-11-23T20:00:00Z"}}
```

with every key optional, or the Go daemon's `schedule.json` or persisted intent, which are read
but never written.

```
# Dry run (the default): nothing is written.
.lake/build/bin/sungrowd tick tmp/sungrowd-go/schedule.json

# Keep the controller state between runs, so the SOC latch holds and the adaptive ramp continues:
.lake/build/bin/sungrowd tick schedule.json --state state.json

# Write the decision, if the inverter doesn't already hold it:
.lake/build/bin/sungrowd tick schedule.json --state state.json --apply

# The main fuse that bounds an adaptive ceiling (default 20 A):
SUNGROWD_GRID_FUSE_A=20 .lake/build/bin/sungrowd tick schedule.json
```

Run the daemon: tick every 5 s and serve `/metrics` (Prometheus) and `/healthz`. Like `tick`,
it only writes to the inverter with `--apply`.

The intent lives in a SQLite database (`SUNGROWD_DB`, default `sungrowd.db`) with the Go
daemon's schema. A fresh database is seeded from `SUNGROWD_SCHEDULE` (default `schedule.json`:
Go's schedule format, or an intent in ours); after that the file is ignored. Every write
attempt is recorded in `control_write`, and an expired override is cleared from the database.

```
# Shadow mode: log what it would write.
SUNGROWD_SCHEDULE=samples/adaptive-all-day.json .lake/build/bin/sungrowd run

# Control the inverter.
.lake/build/bin/sungrowd run --apply

curl localhost:9180/metrics
curl localhost:9180/healthz
sqlite3 sungrowd.db 'select recorded_at, ok, err from control_write order by id desc limit 5'
```

Change the intent while it runs (Go's control API, with our JSON formats; the worker ticks at
once after a change):

```
# A manual override, in our format; "expiry" is RFC 3339 or "HH:MM" (the next time Brisbane's
# clock shows it), and may be left out.
curl -X POST localhost:9180/control/override -d '{"action": "charge", "watts": 3000, "expiry": "06:00"}'
curl -X POST localhost:9180/control/override -d null        # back to the schedule

# The charge window (Go's format is accepted too); null removes it.
curl -X POST localhost:9180/control/schedule \
  -d '{"mode": "adaptive", "start": "01:00", "end": "06:00", "ceiling_watts": 4320, "max_soc": 80}'
curl -X POST localhost:9180/control/schedule -d null

# What the daemon knows: the stored intent, the last decision, controller state, sensors.
curl localhost:9180/diag
```

A bad body is a 400 and changes nothing.

With `SUNGROWD_PROMETHEUS_URL` set (the Prometheus that scrapes `/metrics`), the UI shows SOC history
and forecast vs actual, and `/actual` serves daily PV generation:

```
curl localhost:9180/actual              # the last 7 complete days, newest first
curl 'localhost:9180/actual?days=30'
curl 'localhost:9180/actual?date=2026-11-23'
```

The web UI is at <http://localhost:9180/>: the Go daemon's page, verbatim (`ui/index.html`, with
its vendored Datastar bundle `ui/datastar.js`), driven by the
[Datastar Lean SDK](https://github.com/starfederation/datastar-lean) (`Sungrowd/Ui.lean`). The PV
forecast needs Solcast, which isn't ported yet, so that panel and the forecast columns show what Go
shows without a forecast.

SIGINT or SIGTERM stops the daemon after the tick in progress (so a write is never cut off before
its read-back). Like Go's daemon, it leaves the inverter as it is.

To move over from the Go daemon, stop it and copy its database: the Lean daemon reads Go's
intent format and keeps its `control_write` history, but writes only its own format, so the
Go daemon can't use the database afterwards.

Settings, with Go's defaults: `SUNGROWD_DB` (`sungrowd.db`), `SUNGROWD_SCHEDULE`
(`schedule.json`), `SUNGROWD_LISTEN` (`0.0.0.0:9180`), `SUNGROWD_STALE_THRESHOLD_SECONDS` (120),
`SUNGROWD_LOG_LEVEL` (`info`; or `debug`, `warn`, `error`), `SUNGROWD_GRID_FUSE_A` (20),
`SUNGROWD_NTFY_TOPIC` (unset: no notifications), `SUNGROWD_NTFY_SERVER` (`https://ntfy.sh`),
`SUNGROWD_PROMETHEUS_URL` (unset: no actuals), `SUNGROWD_FORECAST_SCALE` (0.62; 0 is off).

With `SUNGROWD_NTFY_TOPIC` set, the daemon pushes an ntfy notification when the inverter data goes
stale (no good read for `SUNGROWD_STALE_THRESHOLD_SECONDS`, checked every 15 s) and again when it
recovers, as Go does. It posts with `curl`, which must be on the `PATH`: Lean's standard library
has no HTTP client yet.

## Tests

Most checks are `#guard`s and proofs, which `lake build` runs. `lake test` runs the rest, which
need IO (e.g. the database tests, on temporary files). `lake test -- path/to/sungrowd.db` also
prints the intent stored in that database, e.g. a copy of the Go daemon's.

## Testing without the inverter

`scripts/fake_inverter.py` is a fake Modbus TCP inverter on localhost (see its docstring for the
`FAKE_*` settings, including injected modbus exceptions):

```
uv run --no-project scripts/fake_inverter.py &
export SUNGROWD_WINET_HOST=127.0.0.1 SUNGROWD_WINET_PORT=15020
SUNGROWD_DB=tmp/test.db SUNGROWD_SCHEDULE=samples/adaptive-all-day.json .lake/build/bin/sungrowd run --apply
```

# TODO

Try <https://github.com/scidonia/leanin> 

<https://github.com/paulbutcher/lean-telemetry>
