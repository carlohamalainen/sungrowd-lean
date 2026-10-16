import Std.Async
import Std.Net
import Modbus.Codec

open Std Async
open Std.Net

namespace Modbus

abbrev M := ExceptT Error Async

def msOffset (ms : Nat) : Std.Time.Millisecond.Offset := ⟨ms⟩

def guardIO (x : Async α) : M α :=
  ExceptT.mk (try .ok <$> x
               catch e => pure (.error (.io e.toString)))

/-
https://simplymodbus.ca/learn-tcp.html

MBAP Header

A new 7-byte header called the MBAP header (Modbus Application Header) is added
to the start of the message.  This header has the following data:

Transaction Identifier: 2 bytes set by the Client to uniquely identify each
request. These bytes are echoed by the Server since its responses may not be
received in the same order as the requests.

Protocol Identifier: 2 bytes set by the Client, always = 00 00

Length:  2 bytes identifying the number of bytes in the message to follow.

Unit Identifier: 1 byte set by the Client and echoed by the Server for
identification of a remote slave connected on a serial line or on other buses.
-/

structure Client where
  sock      : TCP.Socket.Client
  unit      : UInt8
  deadline  : Nat
  tx        : IO.Ref UInt16
  /-- When set, every frame sent and received is written to stderr. -/
  debug     : Bool := false

/-- Emit a debug line to stderr, if `debug` is on. -/
def Client.trace (c : Client) (msg : String) : M Unit := do
  if c.debug then IO.eprintln msg

def Client.remainingMs (c : Client) : BaseIO Nat := do
  return c.deadline - (← IO.monoMsNow)

def Client.close (c : Client) : Async Unit := do
  try c.sock.shutdown
   catch _ => pure ()

def resolve (host : String) (port : UInt16) : Async SocketAddress := do
  let addrs ← DNS.getAddrInfo host (toString port)
  match addrs[0]? with
    | some (IPAddr.v4 ip) => return SocketAddress.v4 ⟨ip, port⟩
    | some (IPAddr.v6 ip) => return SocketAddress.v6 ⟨ip, port⟩
    | none                => throw <| IO.userError s!"no address found for {host}"

def connect (addr : SocketAddress) (unit : UInt8) (deadline : Nat) (debug : Bool := false) : M Client := do
  let sock ← guardIO <| TCP.Socket.Client.mk
  let remaining := deadline - (← IO.monoMsNow) -- Nat subtraction floors to zero
  if remaining == 0 then throw .timeout

  let connected ← guardIO <| Async.race
    (do sock.connect addr; return true)
    (do Async.sleep (msOffset remaining); return false)

  unless connected do
    throw .timeout

  guardIO sock.noDelay

  return { sock, unit, deadline, debug, tx := ← IO.mkRef 0 }

partial def Client.recvExact (c : Client) (n : Nat) (acc : ByteArray := .empty) : M ByteArray := do
  if acc.size ≥ n then return acc

  let remaining ← c.remainingMs
  if remaining == 0 then throw .timeout

  /-
  Why Selectable instead of race?

  Consider a server that sends 3 bytes 100ms after accepting the connection, and
  a client that times out its first read at 30ms and reads again 150ms later:

  ** race (recv vs sleep) **
  first read: timeout
  second read: none (the bytes were read by the orphaned read and the socket hit EOF)

  ** Selectable.one [recv, sleep] **
  first read: timeout
  second read: some [1, 2, 3] (the bytes were still in the socket)

  The contract on Selector.registerFn is that data is never consumed from the source
  unless its waiter has won. In contrast, Async.race just abandons whichever loses.
  -/
  let chunk : Except Error ByteArray ← guardIO <| Selectable.one #[
    .case (c.sock.recvSelector (n - acc.size).toUInt64) fun
      | some bytes => pure (if bytes.size == 0 then .error .closed else .ok bytes)
      | none => pure (.error .closed),

    .case (← Selector.sleep (msOffset remaining)) fun _ => pure (.error .timeout)
  ]

  c.recvExact n (acc ++ (← ofExcept chunk))

def Client.request (c : Client) (pdu : ByteArray) : M ByteArray := do
  let tx ← c.tx.modifyGet fun t => (t, t + 1)
  let req := frame tx c.unit pdu
  c.trace s!"TX {hex (req.extract 0 Header.size)} | {hex pdu}   mbap tx={tx} len={req.size - 6} unit={c.unit}"
  guardIO <| c.sock.send req

  let hdrBytes ← c.recvExact Header.size
  let some hdr := Header.decode hdrBytes
       | throw (.protocol "short MBAP header")

  unless hdr.tx == tx do
    throw <| .protocol s!"transaction id mismatch: sent {tx}, got {hdr.tx}"

  unless hdr.protocol == 0 do
    throw <| .protocol s!"unexpected protocol id {hdr.protocol}"

  unless hdr.unit == c.unit do
    throw <| .protocol s!"unit id mismatch: sent {c.unit}, got {hdr.unit}"

  let len := hdr.length.toNat

  unless 2 ≤ len && len ≤ 254 do
    throw <| .protocol s!"bad MBAP length {len}"

  /-
  The MBAP length field counts every byte *after itself*.

  In other words, length counts the 'unit' byte, which the header
  has already consumed.
  -/
  let body ← c.recvExact (len - 1)
  c.trace s!"RX {hex hdrBytes} | {hex body}   mbap tx={hdr.tx} len={len} unit={hdr.unit}"

  ofExcept <| checkResponse pdu[0]! body

def Client.readRegisters (c : Client) (fc : UInt8) (addr : UInt16) (n : Nat)
  (_hn : ValidReadQuantity n := by first | omega | decide) : M (Vector UInt16 n) := do
  let body ← c.request <| readRequest fc addr n
  ofExcept <| parseReadResponse body n

def Client.readHoldingRegisters (c : Client) (addr : UInt16) (n : Nat)
      (_hn : ValidReadQuantity n := by first | omega | decide) : M (Vector UInt16 n) := do
  c.readRegisters fcReadHolding addr n

def Client.readInputRegisters (c : Client) (addr : UInt16) (n : Nat)
      (_hn : ValidReadQuantity n := by first | omega | decide) : M (Vector UInt16 n) := do
  c.readRegisters fcReadInput addr n

def Client.writeMultipleRegisters (c : Client) (addr : UInt16) (vals : Vector UInt16 n)
      (hn : ValidWriteQuantity n := by first | omega | decide) : M Unit := do
  let body ← c.request <| writeMultipleRequest addr vals
  ofExcept (checkWriteEcho body addr vals.size)

end Modbus
