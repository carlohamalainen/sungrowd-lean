import Sungrowd.Registers

/-! # Hand-written register definitions for demos. -/

namespace Sungrowd.Examples

open Lean

/-! ## Sensors -/

-- `int16` with a scale of `0.1`, so a raw `253` reads as 25.3 °C.
def inverterTemperature : Sensor :=
  { name                := "Inverter temperature"
    unique_id           := "sg_inverter_temperature"
    address             := 5007
    input_type          := .input
    data_type           := .int16
    scale               := some ⟨1, 1⟩
    precision           := some 1
    scan_interval       := some 60
    unit_of_measurement := some "°C"
    device_class        := some "temperature"
    state_class         := some "measurement" }

def mppt1Voltage : Sensor :=
  { name                := "MPPT1 voltage"
    unique_id           := "sg_mppt1_voltage"
    address             := 5010
    input_type          := .input
    data_type           := .uint16
    scale               := some ⟨1, 1⟩
    precision           := some 1
    scan_interval       := some 10
    unit_of_measurement := some "V"
    device_class        := some "voltage"
    state_class         := some "measurement" }

-- `uint32` spanning registers 5016 and 5017, low word first.
def totalDcPower : Sensor :=
  { name                := "Total DC power"
    unique_id           := "sg_total_dc_power"
    address             := 5016
    input_type          := .input
    data_type           := .uint32
    swap                := some .word
    scale               := some ⟨1, 0⟩
    precision           := some 0
    scan_interval       := some 10
    unit_of_measurement := some "W"
    device_class        := some "power"
    state_class         := some "measurement" }

-- Signed: negative while the battery is charging.
def batteryPower : Sensor :=
  { name                := "Battery power"
    unique_id           := "sg_battery_power"
    address             := 5213
    input_type          := .input
    data_type           := .int32
    swap                := some .word
    scale               := some ⟨1, 0⟩
    precision           := some 0
    scan_interval       := some 10
    unit_of_measurement := some "W"
    device_class        := some "power"
    state_class         := some "measurement" }

-- Scale `0.01`: a raw `5002` is 50.02 Hz.
def gridFrequency : Sensor :=
  { name                := "Grid frequency"
    unique_id           := "sg_grid_frequency"
    address             := 5241
    input_type          := .input
    data_type           := .uint16
    scale               := some ⟨1, 2⟩
    precision           := some 2
    scan_interval       := some 10
    unit_of_measurement := some "Hz"
    device_class        := some "frequency"
    state_class         := some "measurement" }

/-- The only field that matters for a `ReadBlock` is where the sensor sits, so
a minimal sensor leaves every optional field at its default. -/
def batteryLevel : Sensor :=
  { name       := "Battery level"
    unique_id  := "sg_battery_level"
    address    := 13022
    input_type := .input
    data_type  := .uint16
    scale      := some ⟨1, 1⟩ }

/-- info: Sungrowd.Examples.inverterTemperature : Sensor -/
#guard_msgs in
#check inverterTemperature

/-- info: 2 -/
#guard_msgs in
#eval totalDcPower.words

/-- info: (5016, 5018) -/
#guard_msgs in
#eval (totalDcPower.start, totalDcPower.stop)

/-- info: 0.010000 -/
#guard_msgs in
#eval (⟨1, 2⟩ : JsonNumber).toFloat

/-! ## Read blocks

The first block from `tmp/output.txt`: registers `[5007, 5018)` in one read.
The four proof fields are closed by `decide`: the sensors are literals, so the
kernel can check every address itself.
-/

def dcBlock : ReadBlock :=
  { input_type := .input
    address    := 5007
    nr_words   := 11
    slots      := #[⟨inverterTemperature, none⟩, ⟨mppt1Voltage, none⟩, ⟨totalDcPower, none⟩]
    fits       := by decide
    same_type  := by decide
    disjoint   := by decide
    inside     := by decide }

/-- info: Sungrowd.Examples.dcBlock : ReadBlock -/
#guard_msgs in
#check dcBlock

/--
info: dcBlock.inside : ∀ (s : Sensor),
  s ∈ Slot.sensors dcBlock.slots → dcBlock.address ≤ s.start ∧ s.stop ≤ dcBlock.address + dcBlock.nr_words
-/
#guard_msgs in
#check dcBlock.inside

/-- info: 3 -/
#guard_msgs in
#eval dcBlock.slots.size

/-- Pull one sensor's registers out of a block-sized read. These raw words
are made up: index 0 is register 5007, index 9 is 5016, and so on. -/
def fakeDcRead : Vector UInt16 dcBlock.nr_words :=
  #v[253, 0, 0, 3124, 0, 0, 0, 0, 0, 1480, 0]

-- Temperature: one word.
/-- info: #[253] -/
#guard_msgs in
#eval (dcBlock.slice fakeDcRead ⟨0, by decide⟩).toArray

-- Total DC power: two words.
/-- info: #[1480, 0] -/
#guard_msgs in
#eval (dcBlock.slice fakeDcRead ⟨2, by decide⟩).toArray

/-! ## Blocks that `ReadBlock.make?` rejects -/

-- Fine: the two sensors are 28 registers apart, so 29 words cover both.
/-- info: true -/
#guard_msgs in
#eval (ReadBlock.make? .input 5213 29 #[⟨batteryPower, none⟩, ⟨gridFrequency, none⟩]).isSome

-- Too short: grid frequency at 5241 is outside `[5213, 5241)`.
/-- info: false -/
#guard_msgs in
#eval (ReadBlock.make? .input 5213 28 #[⟨batteryPower, none⟩, ⟨gridFrequency, none⟩]).isSome

-- Too long: Modbus allows at most 125 registers in one read.
/-- info: false -/
#guard_msgs in
#eval (ReadBlock.make? .input 13022 126 #[⟨batteryLevel, none⟩]).isSome

-- Wrong order: slots must be in ascending address order.
/-- info: false -/
#guard_msgs in
#eval (ReadBlock.make? .input 5007 11 #[⟨totalDcPower, none⟩, ⟨inverterTemperature, none⟩]).isSome

-- Wrong register type: these are input registers, not holding registers.
/-- info: false -/
#guard_msgs in
#eval (ReadBlock.make? .holding 5007 11 #[⟨inverterTemperature, none⟩]).isSome

end Sungrowd.Examples
