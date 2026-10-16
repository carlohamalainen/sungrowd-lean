namespace Modbus

inductive Error where
  | exception (code : UInt8)
  | timeout
  | closed
  | protocol (msg : String)
  | io (msg : String)
  deriving Repr, BEq -- TODO , Inhabited

def Error.toString : Error → String
  | .exception code => s!"modbus exception {code}"
  | .timeout => "timeout"
  | .closed => "closed"
  | .protocol msg => s!"protocol error: {msg}"
  | .io msg => s!"io error: {msg}"

instance : ToString Error := ⟨Error.toString⟩

/-- Space-separated lowercase hex, e.g. `00 01 13 87`. -/
def hex (b : ByteArray) : String :=
  " ".intercalate (b.toList.map fun x => x.toBitVec.toHex)

def putU16 (b : ByteArray) (v : UInt16) : ByteArray :=
  let vHigh := (v >>> 8).toUInt8
  let vLow := v.toUInt8
  b.push vHigh |>.push vLow

def getU16 (b : ByteArray) (i : Nat) (h : i + 1 < b.size): UInt16 :=
  let vHigh := b[i].toUInt16
  let vLow  := b[i + 1].toUInt16
  (vHigh <<< 8) ||| vLow

def getU16! (b : ByteArray) (i : Nat) : UInt16 :=
  let vHigh := b[i]!.toUInt16
  let vLow  := b[i + 1]!.toUInt16
  (vHigh <<< 8) ||| vLow

def getU16? (b : ByteArray) (i : Nat) : Option UInt16 :=
  if h : i + 1 < b.size then some (getU16 b i h) else none

def fcReadHolding   : UInt8 := 3  -- https://simplymodbus.ca/learn-rtu-fc03.html
def fcReadInput     : UInt8 := 4  -- https://simplymodbus.ca/learn-rtu-fc04.html
def fcWriteMultiple : UInt8 := 16 -- https://simplymodbus.ca/learn-rtu-fc16.html

/-- Maximum number of registers that one FC3/FC4 read may request (spec 0x7D). -/
abbrev maxReadQuantity  : Nat := 125

/-- Maximum number of registers that one FC16 write may carry (spec 0x7B),
so the byte count fits in a `UInt8`. -/
abbrev maxWriteQuantity : Nat := 123

/-- `n` is a legal register count for one FC3/FC4 read. -/
abbrev ValidReadQuantity (n : Nat) : Prop := 1 ≤ n ∧ n ≤ maxReadQuantity

/-- `n` is a legal register count for one FC16 write. -/
abbrev ValidWriteQuantity (n : Nat) : Prop := 1 ≤ n ∧ n ≤ maxWriteQuantity

structure Header where
  tx        : UInt16
  protocol  : UInt16
  length    : UInt16
  unit      : UInt8
  deriving Repr, BEq

def Header.encode (h : Header) : ByteArray :=
  ByteArray.empty
    |> (putU16 · h.tx)
    |> (putU16 · h.protocol)
    |> (putU16 · h.length)
    |> (.push  · h.unit)

def Header.size : Nat := 7

def Header.decode (b : ByteArray) : Option Header :=
  if b.size < Header.size then none
  else some { tx := getU16! b 0, protocol := getU16! b 2, length := getU16! b 4, unit := b[6]! }

theorem Header.size_encode (h : Header) : h.encode.size = Header.size := by
  simp [Header.encode, putU16]
  decide

def frame (tx : UInt16) (unit : UInt8) (pdu : ByteArray) : ByteArray :=
  let length := (pdu.size + 1).toUInt16
  (Header.encode { tx, protocol := 0, length := length, unit }) ++ pdu

def readRequest (fc : UInt8) (addr : UInt16) (n : Nat)
        (_hn : ValidReadQuantity n := by first | omega | decide) : ByteArray :=
  ByteArray.empty
    |> (.push · fc)
    |> (putU16 · addr)
    |> (putU16 · n.toUInt16)

def writeMultipleRequest (addr : UInt16) (vals : Vector UInt16 n)
      (_h : ValidWriteQuantity n := by first | omega | decide) : ByteArray :=
  let hdr := ByteArray.empty
        |> (.push · fcWriteMultiple)
        |> (putU16 · addr)
        |> (putU16 · n.toUInt16)
        |> (.push · ((2 * n).toUInt8))
  vals.foldl putU16 hdr

def checkResponse (fc : UInt8) (body : ByteArray) : Except Error ByteArray :=
  if body.size == 0 then .error (.protocol "empty response body")
  else if body[0]! == (fc ||| 0x80) then
    if body.size < 2 then .error (.protocol "truncated exception response")
    else .error (.exception body[1]!)
  else if body[0]! != fc then .error (.protocol s!"unexpected function code {body[0]!}")
  else .ok body

def parseReadResponse (body : ByteArray) (n : Nat) : Except Error (Vector UInt16 n) :=
  if h : body.size = 2 + 2 * n then
    if body[1].toNat != 2 * n then
      .error (.protocol s!"byte count {body[1]} does not match {2 * n} registers")
    else
      .ok (Vector.ofFn fun (i : Fin n) => getU16 body (2 + 2 * i) (by omega))
  else
    .error (.protocol s!"expected {2 + 2 * n} bytes, got {body.size}")

/-- FC16 response echoes the request: fc (1) | start address (2) | quantity (2). -/
def checkWriteEcho (body : ByteArray) (addr : UInt16) (n : Nat) : Except Error Unit :=
  if h : body.size = 5 then
    if getU16 body 1 (by omega) = addr ∧ getU16 body 3 (by omega) = n.toUInt16 then
      .ok ()
    else
      let gotAddr := getU16 body 1 (by omega)
      let gotQty  := getU16 body 3 (by omega)
      .error (.protocol s!"write echo mismatch: got addr {gotAddr} qty {gotQty}, expected addr {addr} qty {n}")
  else
    .error (.protocol s!"write echo: expected 5 bytes, got {body.size}")

#guard (frame 7 1 (readRequest fcReadHolding 13049 3)).toList ==
  [0, 7, 0, 0, 0, 6, 1, 3, 0x32, 0xF9, 0, 3]
#guard (readRequest fcReadInput 5016 2).toList == [4, 0x13, 0x98, 0, 2]
#guard (writeMultipleRequest 13049 #v[2, 0xAA, 3000]).toList ==
  [16, 0x32, 0xF9, 0, 3, 6, 0, 2, 0, 0xAA, 0x0B, 0xB8]
#guard Header.decode (ByteArray.mk #[0, 7, 0, 0, 0, 6, 1]) == some ⟨7, 0, 6, 1⟩
#guard Header.decode (ByteArray.mk #[0, 7, 0]) == none
#guard getU16 (ByteArray.mk #[0xAB, 0xCD]) 0 (by decide) == 0xABCD
#guard hex (ByteArray.mk #[0, 0x0A, 0xFF]) == "00 0a ff"
#guard hex .empty == ""
#guard getU16? (ByteArray.mk #[0xAB, 0xCD]) 0 == some 0xABCD
#guard getU16? (ByteArray.mk #[0xAB, 0xCD]) 1 == none
#guard (parseReadResponse (ByteArray.mk #[3, 6, 0, 2, 0, 0xAA, 0x0B, 0xB8]) 3 |>.toOption) ==
  some #v[2, 0xAA, 3000]
#guard (parseReadResponse (ByteArray.mk #[3, 4, 0, 2, 0, 0xAA]) 3 |>.toOption) == none
#guard (checkResponse 3 (ByteArray.mk #[0x83, 4]) matches .error (.exception 4))
#guard (checkResponse 3 (ByteArray.mk #[0x83]) matches .error (.protocol _))
#guard (checkResponse 3 (ByteArray.mk #[4, 0]) matches .error (.protocol _))
#guard (checkWriteEcho (ByteArray.mk #[16, 0x32, 0xF9, 0, 3]) 13049 3 matches .ok ())
#guard (checkWriteEcho (ByteArray.mk #[16, 0x32, 0xF9, 0, 2]) 13049 3 matches .error _)

end Modbus
