import Modbus.Client
import Sungrowd.Registers
import Std.Data.HashMap

open Std Async
open Modbus
open Sungrowd

/-! Read a fixed set of Sungrow input registers from the inverter and print them.

The register table is `reference/modbus_sungrow.json` (parsed by
`Sungrowd/Registers.lean`). `metricDefs` below picks the sensors we care about
by their Home Assistant `unique_id`, and the table supplies everything else:
address, data type, word order, scale, NaN sentinel and unit. -/

def hostEnvVar    : String := "SUNGROWD_WINET_HOST"
/-- If set (to anything), raw frames are traced to stderr. -/
def debugEnvVar   : String := "SUNGROWD_DEBUG"
def registersPath : System.FilePath := "reference/modbus_sungrow.json"
def modbusPort    : UInt16 := 502
def unitId        : UInt8  := 1
/-- Deadline for connecting and reading every metric, one round trip each. -/
def timeoutMs     : Nat    := 30000

inductive MetricKind
  | gauge
  | counter
  deriving Repr, BEq

instance : ToString MetricKind where
  toString
    | .gauge   => "gauge"
    | .counter => "counter"

/-- One exported value: which sensor to read, and how to name and describe it. -/
structure MetricDef where
  sensorId : String
  name     : String
  help     : String
  kind     : MetricKind

instance : ToString MetricDef where
  toString m := s!"{m.name} ({m.kind}, sensor {m.sensorId}): {m.help}"

def metricDefs : Array MetricDef := #[
  -- Solar (instantaneous + per-string).
  ⟨"sg_total_dc_power",       "solar_pv_power_watts",               "Solar PV generation (total DC power)", .gauge⟩,
  ⟨"sg_mppt1_voltage",        "solar_pv_string1_voltage_volts",     "MPPT1 DC string voltage",              .gauge⟩,
  ⟨"sg_mppt1_current",        "solar_pv_string1_current_amperes",   "MPPT1 DC string current",              .gauge⟩,
  ⟨"sg_mppt2_voltage",        "solar_pv_string2_voltage_volts",     "MPPT2 DC string voltage",              .gauge⟩,
  ⟨"sg_mppt2_current",        "solar_pv_string2_current_amperes",   "MPPT2 DC string current",              .gauge⟩,
  ⟨"sg_inverter_temperature", "solar_inverter_temperature_celsius", "Inverter internal temperature",        .gauge⟩,

  -- Battery.
  ⟨"sg_battery_power",           "solar_battery_power_watts",         "Battery power; positive=discharging, negative=charging", .gauge⟩,
  ⟨"sg_battery_level",           "solar_battery_soc_percent",         "Battery state of charge",                                .gauge⟩,
  ⟨"sg_battery_state_of_health", "solar_battery_soh_percent",         "Battery state of health",                                .gauge⟩,
  ⟨"sg_battery_voltage",         "solar_battery_voltage_volts",       "Battery voltage",                                        .gauge⟩,
  ⟨"sg_battery_temperature",     "solar_battery_temperature_celsius", "Battery temperature",                                    .gauge⟩,

  -- Grid + load.
  ⟨"sg_total_active_power", "solar_inverter_ac_power_watts", "Inverter total AC active power", .gauge⟩,
  ⟨"sg_load_power",         "solar_load_power_watts",        "Household load power",           .gauge⟩,
  ⟨"sg_grid_frequency",     "solar_grid_frequency_hertz",    "Grid frequency",                 .gauge⟩,
  -- Grid power (reg 13009). Reported as unavailable when the inverter sends the
  -- int32 NaN sentinel (0x7FFFFFFF), which the register table lists as `nan_value`.
  ⟨"sg_battery_export_power_raw", "solar_grid_power_watts", "Grid power; positive=exporting/selling, negative=importing/buying", .gauge⟩,

  -- Daily energy (gauges; reset at local midnight).
  ⟨"sg_daily_pv_generation",            "solar_pv_daily_kwh",                     "PV generation today (resets at local midnight)", .gauge⟩,
  ⟨"sg_daily_battery_charge",           "solar_battery_charge_daily_kwh",         "Battery charge energy today",                    .gauge⟩,
  ⟨"sg_daily_battery_discharge",        "solar_battery_discharge_daily_kwh",      "Battery discharge energy today",                 .gauge⟩,
  ⟨"sg_daily_battery_charge_from_pv",   "solar_battery_charge_from_pv_daily_kwh", "Battery charge sourced from PV today",           .gauge⟩,
  ⟨"sg_daily_direct_energy_consumption", "solar_direct_consumption_daily_kwh",    "PV-to-load directly today (bypassing battery)",  .gauge⟩,

  -- Lifetime energy (counters; monotonic).
  ⟨"sg_total_pv_generation",            "solar_pv_kwh_total",                     "PV generation lifetime total",                  .counter⟩,
  ⟨"sg_total_battery_charge",           "solar_battery_charge_kwh_total",         "Battery charge energy lifetime total",          .counter⟩,
  ⟨"sg_total_battery_discharge",        "solar_battery_discharge_kwh_total",      "Battery discharge energy lifetime total",       .counter⟩,
  ⟨"sg_total_battery_charge_from_pv",   "solar_battery_charge_from_pv_kwh_total", "Battery charge sourced from PV lifetime total", .counter⟩,
  ⟨"sg_total_imported_energy",          "solar_grid_import_kwh_total",            "Energy imported from grid lifetime total",      .counter⟩,
  ⟨"sg_total_exported_energy",          "solar_grid_export_kwh_total",            "Energy exported to grid lifetime total",        .counter⟩,
  ⟨"sg_total_direct_energy_consumption", "solar_direct_consumption_kwh_total",    "PV-to-load directly lifetime total",            .counter⟩,

  -- State / mode.
  ⟨"uid_sg_running_state_raw", "solar_running_state",     "Inverter running-state bitfield (raw)", .gauge⟩,
  ⟨"uid_power_flow_status",    "solar_power_flow_status", "Power-flow status bitfield (raw)",      .gauge⟩
]

/-! ## Decoding -/

/-- Reinterpret a register's bits as a signed 16-bit value (two's complement). -/
def s16 (v : UInt16) : Int := v.toInt16.toInt

/-- Combine two consecutive registers into one 32-bit word. With `swap := word`
the register at `address` holds the low half ("CDAB"); otherwise the high half. -/
def u32 (r : Vector UInt16 2) (swap : Option Swap) : UInt32 :=
  let (hi, lo) := match swap with
    | some .word => (r[1], r[0])
    | none       => (r[0], r[1])
  (hi.toUInt32 <<< 16) ||| lo.toUInt32

/-- Render `v` with `decimals` implied decimal places: `withDecimals 345 1 = "34.5"`. -/
def withDecimals (v : Int) (decimals : Nat) : String :=
  let scale := 10 ^ decimals
  let sign  := if v < 0 then "-" else ""
  let a     := v.natAbs
  if decimals == 0 then s!"{sign}{a}"
  else
    let frac := toString (a % scale)
    let pad  := String.ofList (List.replicate (decimals - frac.length) '0')
    s!"{sign}{a / scale}.{pad}{frac}"

/-- Apply the sensor's `scale` exactly. The scale is a decimal `mantissa × 10^-exponent`,
so `raw * mantissa` with `exponent` implied decimals is the scaled value. -/
def scaled (s : Sensor) (raw : Int) : String :=
  match s.scale with
  | none        => toString raw
  | some ⟨m, e⟩ => withDecimals (raw * m) e

/-- Decode a sensor's registers to its raw (unscaled) integer value. `none` when the
inverter reports the sensor's `nan_value`, and for string sensors, which
`resolveMetrics` rejects up front. -/
def decodeRaw (s : Sensor) (r : Vector UInt16 s.words) : Option Int :=
  let raw? : Option Int := match h : s.data_type with
    | .int16  => some (s16 (r[0]'(by simp [Sensor.words, h])))
    | .uint16 => some (r[0]'(by simp [Sensor.words, h])).toNat
    | .int32  => some (u32 (r.cast (by simp [Sensor.words, h])) s.swap).toInt32.toInt
    | .uint32 => some (u32 (r.cast (by simp [Sensor.words, h])) s.swap).toNat
    | .string => none
  raw?.filter (some · != s.nan_value)

/-- A slot's reading as a scaled value with its unit, e.g. `"34.5 V"`. -/
def Sungrowd.Slot.display (slot : Slot) : String :=
  let s := slot.sensor
  match slot.reading with
  | none   => "not read"
  | some r =>
    match decodeRaw s r.raw with
    | none     => "unavailable"
    | some raw => s!"{scaled s raw} {s.unit_of_measurement.getD "(unitless)"}"

/-! ## Reading -/

/-- Read `n` registers at the sensor's address, from its address space.  -/
def readRegs (c : Client) (s : Sensor) (n : Nat)
    (hn : ValidReadQuantity n := by first | omega | decide) : M (Vector UInt16 n) :=
  match s.input_type with
  | .input   => c.readInputRegisters   s.address n hn
  | .holding => c.readHoldingRegisters s.address n hn

/-- Connect once, read every block in one request each, and print one line per sensor.
`names` maps a sensor's `unique_id` to the metric name to print. -/
def readBlocks (host : String) (debug : Bool) (names : HashMap String String)
    (blocks : Array ReadBlock) : M Unit := do
  let addr ← guardIO <| resolve host modbusPort
  let deadline := (← IO.monoMsNow) + timeoutMs
  let c ← connect addr unitId deadline debug
  try
    let name (s : Sensor) : String := names.getD s.unique_id s.unique_id
    let width := blocks.foldl (init := 0) fun w b =>
      b.slots.foldl (init := w) fun w slot => max w (name slot.sensor).length
    for b in blocks do
      let b ← b.read c
      for slot in b.slots do
        let n := name slot.sensor
        IO.println s!"{n.pushn ' ' (width - n.length)}  {slot.display}"
  finally
    guardIO c.close

/-! ## Setup -/

/-- Lookup table by Home Assistant `unique_id`. -/
def sensorsById (h : Hub) : Std.HashMap String Sensor :=
  h.sensors.foldl (init := {}) fun m s => m.insert s.unique_id s

/-- Resolve every metric to its sensor, rejecting anything we cannot decode. -/
def resolveMetrics (byId : HashMap (InputType × String) Sensor) : Except String (Array (MetricDef × Sensor)) := do
  let mut out := #[]
  for m in metricDefs do
    let k : InputType × String := ⟨.input, m.sensorId⟩
    let some s := byId[k]?
      | throw s!"no sensor {m.sensorId} (needed for {m.name})"
    if s.data_type == .string then
      throw s!"{m.sensorId} is a string sensor; only numeric sensors are supported"
    out := out.push (m, s)
  return out

/-- The block that covers exactly `ss` from the first slot's start to the last slot's stop. -/
def ReadBlock.ofSlots? (ss : Array Slot) : Option ReadBlock := do
  let first ← ss[0]?
  let last  ← ss.back?
  let ty := first.sensor.input_type
  let addr := first.sensor.start
  ReadBlock.make? ty addr (last.sensor.stop - addr) ss

def toBlocks (slots : Array Slot) : Except String (Array ReadBlock) := do
  let mut blocks  : Array ReadBlock  := #[]
  let mut current : Option ReadBlock := none

  for s in slots do
    -- If we have started to construct a ReadBlock, then try to
    -- add `s` to it and continue:
    if let some b := current then
      if let some b' := ReadBlock.ofSlots? (b.slots.push s) then
        current := some b'
        continue

      -- Couldn't add `s`, so this block is done.
      blocks := blocks.push b

    -- Can we get started with just `s`?
    let some b := ReadBlock.ofSlots? #[s]
          | throw s!"sensor {s.sensor.unique_id} does not fit in a read block"
    current := some b

  if let some b := current then
    blocks := blocks.push b

  return blocks

def main : IO UInt32 := do
  let some host ← IO.getEnv hostEnvVar
    | IO.eprintln s!"error: {hostEnvVar} is not set (expected the inverter's IP or hostname)"
      return 2
  let debug := (← IO.getEnv debugEnvVar).isSome

  let registers ← Registers.load registersPath

  let some hub := registers.modbus[0]?
    | IO.eprintln s!"error: {registersPath}: no modbus hub"
      return 2

  let targets ← match resolveMetrics (Registers.byId hub) with
    | .ok t    => pure t
    | .error e =>
      IO.eprintln s!"error: {registersPath}: {e}"
      return 2

  let sensors := targets.map (·.2) |>.qsort (·.address < ·.address)

  let slots : Array Slot := sensors.map fun s => Slot.mk s none

  let blocks ← match toBlocks slots with
    | .ok bs   => pure bs
    | .error e =>
      IO.eprintln s!"error: {e}"
      return 2

  let names : HashMap String String :=
    targets.foldl (init := {}) fun m (d, s) => m.insert s.unique_id d.name

  match ← (readBlocks host debug names blocks).run.block with
  | .ok ()   => return 0
  | .error e =>
    IO.eprintln s!"error: {e}"
    return 1
