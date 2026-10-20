import Lean.Data.Json
import Lean.Elab.Deriving.FromToJson
import Std.Time
import Std.Async

import Modbus.Client

/-! # Sungrow register definitions

The register table for Sungrow SHx inverters comes from the Home Assistant
integration <https://github.com/mkaiser/Sungrow-SHx-Inverter-Modbus-Home-Assistant>
(`reference/modbus_sungrow.yaml`).

Lean has no YAML parser (?) so I did a one off YAML to JSON conversion using
`scripts/yaml_to_json.py` which produces `reference/modbus_sungrow.json`.
-/

namespace Sungrowd

open Lean
open Std.Time
open Std.Async

/-- Modbus has read-only "input" registers and writable "holding" registers. -/
inductive InputType
  | input
  | holding
deriving BEq, DecidableEq, Hashable, Repr

instance : ToString InputType where
  toString
    | .input   => "input"
    | .holding => "holding"

instance : FromJson InputType where
  fromJson?
    | .str "input"   => .ok .input
    | .str "holding" => .ok .holding
    | j => .error s!"input_type: expected \"input\" or \"holding\", got {j.compress}"

/-- How to interpret the raw 16-bit registers. -/
inductive DataType
  | int16
  | uint16
  | int32
  | uint32
  /-- ASCII packed two characters per register, `count` registers long. -/
  | string
  deriving BEq, DecidableEq, Repr

instance : ToString DataType where
  toString
  | .int16  => "int16"
  | .uint16 => "uint16"
  | .int32  => "int32"
  | .uint32 => "uint32"
  | .string => "string"

instance : FromJson DataType where
  fromJson?
    | .str "int16"  => .ok .int16
    | .str "uint16" => .ok .uint16
    | .str "int32"  => .ok .int32
    | .str "uint32" => .ok .uint32
    | .str "string" => .ok .string
    | j             => .error s!"data_type: unknown {j.compress}"

/-- Word order of a 32-bit value spanning two consecutive registers.

Modbus sends each 16-bit register big-endian (high byte first) but does not
specify how a 32-bit value is split across two registers. Most devices put
the high word at `address` and the low word at `address + 1` ("ABCD");
`word` selects the other convention, where the register at `address` holds
the low half ("CDAB").

Every single entry in our Home Assistant YAML/JSON happens to be `word`.
-/
inductive Swap
  | word
  deriving BEq, DecidableEq, Repr

instance : FromJson Swap where
  fromJson?
    | .str "word" => .ok .word
    | j => .error s!"swap: unknown {j.compress}"

/-- Register addresses and switch command values are 16-bit but the JSON carries
them as plain integers, so decode via `Nat` and range-check. -/
instance : FromJson UInt16 where
  fromJson? j := do
    let n : Nat ← fromJson? j
    if n < UInt16.size then pure (UInt16.ofNat n)
    else throw s!"expected a 16-bit value, got {n}"

/-- One readable register (a Home Assistant `modbus` sensor). -/
structure Sensor where
  name                : String
  unique_id           : String
  /-- Zero-based wire address (one less than the "reg NNNN" in Sungrow's docs). -/
  address             : UInt16
  input_type          : InputType
  data_type           : DataType
  /-- Register count, only for `string` sensors. -/
  count               : Option Nat        := none
  swap                : Option Swap       := none
  /-- Multiplier applied to the raw value, e.g. `0.1`. Kept as an exact decimal. -/
  scale               : Option JsonNumber := none
  /-- Decimal places Home Assistant displays. -/
  precision           : Option Nat        := none
  scan_interval       : Option Nat        := none
  /-- Raw value the inverter reports when the reading is unavailable. -/
  nan_value           : Option Int        := none
  unit_of_measurement : Option String     := none
  device_class        : Option String     := none
  state_class         : Option String     := none
  deriving Repr, FromJson

instance : ToString Sensor where
  toString s := s!"<{s.name}> {s.unique_id} {s.address} {s.input_type} {s.data_type} "

/-- Number of 16-bit registers one read of this sensor needs. -/
def Sensor.words (s : Sensor) : Nat :=
  match s.data_type with
  | .int16  | .uint16 => 1
  | .int32  | .uint32 => 2
  | .string           => s.count.getD 1

/-- First register of the sensor. A Sensor's registers are in the half-open range `[s.start, s.stop)`. -/
def Sensor.start (s : Sensor) : Nat := s.address.toNat

/-- One past the sensor's last register, so `[s.start, s.stop)` is half-open. -/
def Sensor.stop  (s : Sensor) : Nat := s.start + s.words

/-- One Modbus hub (there is exactly one in the file). -/
structure Hub where
  name     : String
  sensors  : Array Sensor
  deriving Repr, FromJson

/-- The top-level object of `modbus_sungrow.json`. -/
structure Registers where
  modbus : Array Hub
  deriving Repr, FromJson

def Hub.sensor? (h : Hub) (inputType : InputType) (uniqueId : String) : Option Sensor :=
  h.sensors.find? (fun s => s.input_type == inputType ∧ s.unique_id == uniqueId)

def Registers.parse (s : String) : Except String Registers :=
  Json.parse s >>= fromJson?

def Registers.load (path : System.FilePath) : IO Registers := do
  match Registers.parse (← IO.FS.readFile path) with
  | .ok r    => pure r
  | .error e => throw <| IO.userError s!"{path}: {e}"

def Registers.byId (h : Hub) : Std.HashMap (InputType × String) Sensor :=
  h.sensors.foldl (init := {}) fun m s => m.insert ⟨s.input_type, s.unique_id⟩ s

/-- One read of a sensor: its `n` registers, as they came off the wire. -/
structure Reading (n : Nat) where
  raw       : Vector UInt16 n
  read_at   : Timestamp   -- for humans, UTC
  read_mono : Nat         -- for liveness checks, IO.monoNanosNow
deriving Repr

structure Slot where
  sensor    : Sensor
  reading   : Option (Reading sensor.words) := none
deriving Repr

def Slot.sensors (slots : Array Slot) : List Sensor :=
  slots.toList.map (·.sensor)
 
structure ReadBlock where
  input_type  : InputType
  address     : Nat
  nr_words    : Nat
  slots       : Array Slot

  fits        : Modbus.ValidReadQuantity nr_words
  same_type   : ∀ s ∈ Slot.sensors slots, s.input_type = input_type
  disjoint    : (Slot.sensors slots).Pairwise (·.stop ≤ ·.start)
  inside      : ∀ s ∈ Slot.sensors slots,
                  address ≤ s.start ∧ s.stop ≤ address + nr_words
deriving Repr

theorem Slot.sensors_set (a : Array Slot) (i : Nat) (hi : i < a.size) (x : Slot)
    (hx : x.sensor = a[i].sensor) : Slot.sensors (a.set i x hi) = Slot.sensors a := by
    unfold Slot.sensors
    rw [Array.toList_set, List.map_set, hx]
    apply List.ext_getElem
    case hl => simp
    case h =>
      intro j h1 h2
      simp [List.getElem_set]
      intro i_eq_j
      subst i_eq_j
      rfl

theorem Slot.sensors_setReading (a : Array Slot) (i : Nat) (hi : i < a.size)
          (r : Option (Reading a[i].sensor.words)) :
          Slot.sensors (a.set i { a[i] with reading := r } hi) = Slot.sensors a := by
  let x : Slot := { a[i] with reading := r}
  apply Slot.sensors_set a i hi x
  rfl

def ReadBlock.make? (ty : InputType) (addr n : Nat) (slots : Array Slot) : Option ReadBlock :=
  if h : (Modbus.ValidReadQuantity n)
       ∧ (∀ s ∈ Slot.sensors slots, s.input_type = ty)
       ∧ (Slot.sensors slots).Pairwise (·.stop ≤ ·.start)
       ∧ (∀ s ∈ Slot.sensors slots, addr ≤ s.start ∧ s.stop ≤ addr + n)
    then
      have ⟨fits, same_type, disjoint, inside⟩ := h
      some ⟨ty, addr, n, slots, fits, same_type, disjoint, inside⟩
    else
      none

def ReadBlock.setReading (b : ReadBlock) (i : Fin b.slots.size)
    (r : Reading b.slots[i].sensor.words) : ReadBlock :=
  { b with
      slots := b.slots.set i { b.slots[i] with reading := some r }
      fits        := b.fits
      same_type   := Slot.sensors_setReading b.slots i i.isLt (some r) ▸ b.same_type
      disjoint    := Slot.sensors_setReading b.slots i i.isLt (some r) ▸ b.disjoint
      inside      := Slot.sensors_setReading b.slots i i.isLt (some r) ▸ b.inside
  }

/-- Rebuilding every slot from its own sensor leaves the sensor list unchanged. -/
theorem Slot.sensors_ofFn (a : Array Slot)
    (f : (i : Fin a.size) → Option (Reading a[i].sensor.words)) :
    Slot.sensors (Array.ofFn fun i => { sensor := a[i].sensor, reading := f i })
      = Slot.sensors a := by
  unfold Slot.sensors
  apply List.ext_getElem
  case hl => simp
  case h =>
    intro j h1 h2
    simp

/-- Replace every slot's reading at once; `f i` is the new reading for slot `i`. -/
def ReadBlock.setReadings (b : ReadBlock)
    (f : (i : Fin b.slots.size) → Option (Reading b.slots[i].sensor.words)) : ReadBlock :=
  { b with
      slots       := Array.ofFn fun i => { sensor := b.slots[i].sensor, reading := f i }
      same_type   := Slot.sensors_ofFn b.slots f ▸ b.same_type
      disjoint    := Slot.sensors_ofFn b.slots f ▸ b.disjoint
      inside      := Slot.sensors_ofFn b.slots f ▸ b.inside
  }

-- TODO mpr?
theorem ReadBlock.mem_sensors (b : ReadBlock) (i : Fin b.slots.size) :
    b.slots[i].sensor ∈ Slot.sensors b.slots :=
  List.mem_map.mpr ⟨b.slots[i], Array.getElem_mem_toList i.isLt, rfl⟩

-- given a ReadBlock and a raw vector of words read from the inverter, an index into the slots,
-- we can extract the raw words for this sensor, specifically the correct number of words
-- since i is dependent, amazing.
def ReadBlock.slice (b : ReadBlock) (v : Vector UInt16 b.nr_words) (i : Fin b.slots.size) :
    Vector UInt16 b.slots[i].sensor.words :=

  let s      := b.slots[i].sensor
  let offset := s.start - b.address

  have hin : b.address ≤ s.start ∧ s.stop ≤ b.address + b.nr_words := b.inside s (b.mem_sensors i)

  Vector.ofFn fun (k : Fin s.words) =>
    v[offset + k]'(by
      have hk : k.val < s.words := k.isLt
      have hstop : s.stop = s.start + s.words := rfl
      omega
      )

/-- Read the block's registers in one request and record a reading in every slot. -/
def ReadBlock.read (b : ReadBlock) (c : Modbus.Client) : Modbus.M ReadBlock := do
  let addr := b.address.toUInt16
  let v ← match b.input_type with
    | .input   => c.readInputRegisters   addr b.nr_words b.fits
    | .holding => c.readHoldingRegisters addr b.nr_words b.fits
  let readAt ← Timestamp.now
  let readMono ← IO.monoNanosNow

  return b.setReadings fun i => some ⟨b.slice v i, readAt, readMono⟩

end Sungrowd
