import Lean.Data.Json
import Lean.Elab.Deriving.FromToJson

/-! # Sungrow register definitions

The register table for Sungrow SHx inverters comes from the Home Assistant
integration <https://github.com/mkaiser/Sungrow-SHx-Inverter-Modbus-Home-Assistant>
(`reference/modbus_sungrow.yaml`).

Lean has no YAML parser (?) so I did a one off YAML to JSON conversion using
`scripts/yaml_to_json.py` which produces `reference/modbus_sungrow.json`.
-/

namespace Sungrowd

open Lean

/-- Modbus has read-only "input" registers and writable "holding" registers. -/
inductive InputType
  | input
  | holding
deriving BEq, DecidableEq, Hashable, Repr

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

/-- Number of 16-bit registers one read of this sensor needs. -/
def Sensor.words (s : Sensor) : Nat :=
  match s.data_type with
  | .int16  | .uint16 => 1
  | .int32  | .uint32 => 2
  | .string           => s.count.getD 1

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

end Sungrowd
