import Modbus.Client

open Std Async
open Modbus

/-! A minimal end-to-end check: read one register from the inverter and print it.

The register is Sungrow's "Inverter temperature" (sensor `sg_inverter_temperature`):
input register 5007, signed 16-bit, one implied decimal, degrees Celsius. -/

def hostEnvVar      : String := "SUNGROWD_WINET_HOST"
/-- If set (to anything), raw frames are traced to stderr. -/
def debugEnvVar     : String := "SUNGROWD_DEBUG"
def modbusPort      : UInt16 := 502
def unitId          : UInt8  := 1
def temperatureAddr : UInt16 := 5007
def timeoutMs       : Nat    := 3000

/-- Reinterpret a register's bits as a signed 16-bit value (two's complement). -/
def s16 (v : UInt16) : Int := v.toInt16.toInt

/-- Reinterpret a register's bits as an unsigned 16-bit value. -/
def u16 (v : UInt16) : Int := v.toNat

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

def readTemperature (host : String) (debug : Bool) : M Int := do
  let addr ← guardIO (resolve host modbusPort)
  let deadline := (← IO.monoMsNow) + timeoutMs
  let c ← connect addr unitId deadline debug
  try
    let regs ← c.readInputRegisters temperatureAddr 1
    return s16 regs[0]
  finally
    guardIO c.close

def main : IO UInt32 := do
  let some host ← IO.getEnv hostEnvVar
    | IO.eprintln s!"error: {hostEnvVar} is not set (expected the inverter's IP or hostname)"
      return 2
  let debug := (← IO.getEnv debugEnvVar).isSome
  match ← (readTemperature host debug).run.block with
  | .ok t =>
    IO.println s!"inverter temperature: {withDecimals t 1} °C  (raw {t})"
    return 0
  | .error e =>
    IO.eprintln s!"error: {e}"
    return 1
