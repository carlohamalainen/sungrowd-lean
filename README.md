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
what it would write. The file is either the Go daemon's `schedule.json` or its persisted intent
(`{"charge_window": …, "manual_override": …}`).

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

# TODO

Try <https://github.com/scidonia/leanin> 

<https://github.com/paulbutcher/lean-telemetry>
