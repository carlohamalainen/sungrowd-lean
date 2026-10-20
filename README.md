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

# TODO

Try <https://github.com/scidonia/leanin> 

