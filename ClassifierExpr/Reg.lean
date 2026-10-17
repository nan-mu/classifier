import ClassifierExpr.Bits

namespace ClassifierExpr

inductive RegKind where
  | real
  | stack
  | map
  | packet
  | context
  deriving DecidableEq, BEq, ReflBEq, LawfulBEq, Repr, Inhabited

/-- Byte offsets admitted by packet address binding. Packet leaves name existing
byte-cell equalities, not arbitrary symbolic registers. -/
inductive PacketOffset where
  | c (value : Nat)
  | packet (alpha : Nat)
  | add (lhs rhs : PacketOffset)
  | low (bits : Nat) (arg : PacketOffset)
  | shl (arg amount : PacketOffset)
  | sub (arg : PacketOffset) (constant : Nat)
  | id (arg : PacketOffset)
  | zext (bits input : Nat) (arg : PacketOffset)
  | sext (bits input : Nat) (arg : PacketOffset)
  | or (lhs rhs : PacketOffset)
  | mask (arg : PacketOffset) (constant : Nat)
  | lshr (arg : PacketOffset) (constant : Nat)
  deriving DecidableEq, BEq, ReflBEq, LawfulBEq, Repr, Inhabited

def PacketOffset.orderKey : PacketOffset → List Nat
  | .c n => [0, n]
  | .packet a => [1, a]
  | .add a b => [2, a.orderKey.length] ++ a.orderKey ++ b.orderKey
  | .low q a => [3, q] ++ a.orderKey
  | .shl a b => [4, a.orderKey.length] ++ a.orderKey ++ b.orderKey
  | .sub a n => [5, n] ++ a.orderKey
  | .id a => [6] ++ a.orderKey
  | .zext q v a => [7, q, v] ++ a.orderKey
  | .sext q v a => [8, q, v] ++ a.orderKey
  | .or a b => [9, a.orderKey.length] ++ a.orderKey ++ b.orderKey
  | .mask a n => [10, n] ++ a.orderKey
  | .lshr a n => [11, n] ++ a.orderKey

def PacketOffset.code : PacketOffset → List Nat
  | .c n => [0, n]
  | .packet a => [1, a]
  | .add a b => [2] ++ a.code ++ b.code
  | .low q a => [3, q] ++ a.code
  | .shl a b => [4] ++ a.code ++ b.code
  | .sub a n => [5, n] ++ a.code
  | .id a => [6] ++ a.code
  | .zext q v a => [7, q, v] ++ a.code
  | .sext q v a => [8, q, v] ++ a.code
  | .or a b => [9] ++ a.code ++ b.code
  | .mask a n => [10, n] ++ a.code
  | .lshr a n => [11, n] ++ a.code

def PacketOffset.decode : Nat → List Nat → Option (PacketOffset × List Nat)
  | 0, _ => none
  | fuel + 1, xs => match xs with
    | 0 :: n :: rest => some (.c n, rest)
    | 1 :: a :: rest => some (.packet a, rest)
    | 2 :: rest => do
      let (a, rest) ← decode fuel rest
      let (b, rest) ← decode fuel rest
      pure (.add a b, rest)
    | 3 :: q :: rest => do
      let (a, rest) ← decode fuel rest
      pure (.low q a, rest)
    | 4 :: rest => do
      let (a, rest) ← decode fuel rest
      let (b, rest) ← decode fuel rest
      pure (.shl a b, rest)
    | 5 :: n :: rest => do
      let (a, rest) ← decode fuel rest
      pure (.sub a n, rest)
    | 6 :: rest => do
      let (a, rest) ← decode fuel rest
      pure (.id a, rest)
    | 7 :: q :: v :: rest => do
      let (a, rest) ← decode fuel rest
      pure (.zext q v a, rest)
    | 8 :: q :: v :: rest => do
      let (a, rest) ← decode fuel rest
      pure (.sext q v a, rest)
    | 9 :: rest => do
      let (a, rest) ← decode fuel rest
      let (b, rest) ← decode fuel rest
      pure (.or a b, rest)
    | 10 :: n :: rest => do
      let (a, rest) ← decode fuel rest
      pure (.mask a n, rest)
    | 11 :: n :: rest => do
      let (a, rest) ← decode fuel rest
      pure (.lshr a n, rest)
    | _ => none

/- A finite prefix round-trip fixture covers every constructor and input width. -/
#guard
  let t : PacketOffset := .lshr (.mask (.or (.id (.sext 8 64 (.zext 4 32
    (.sub (.add (.packet 7) (.shl (.low 4 (.packet 9)) (.c 2))) 3)))) (.c 1)) 255) 1
  PacketOffset.decode t.code.length (t.code ++ [91, 92]) == some (t, [91, 92])

/-- The passed inequality is data + checkedEnd ≤ data_end (strict when
`strict` is true). Binding verifies that it covers offset + bytes, so a check
for a larger interval may authorize a narrower access. -/
structure CompoundPacketReg where
  κ : Nat
  offset : PacketOffset
  bytes : Nat
  endCtx : Nat
  strict : Bool
  byteIndex : Nat := 0
  checkedEnd : PacketOffset
  deriving DecidableEq, BEq, ReflBEq, LawfulBEq, Repr, Inhabited

/-- \(\mathrm{Reg}_{k,w}=(k,w,\alpha)\). Alpha assignment is architecture-specific. -/
structure Reg where
  kind  : RegKind
  width : Width
  alpha : Nat
  compound : Option CompoundPacketReg := none
  deriving DecidableEq, BEq, ReflBEq, LawfulBEq, Repr, Inhabited

def Reg.real (w : Width) (α : Nat) : Reg := ⟨.real, w, α, none⟩
def Reg.stack (w : Width) (α : Nat) : Reg := ⟨.stack, w, α, none⟩
def Reg.map (w : Width) (α : Nat) : Reg := ⟨.map, w, α, none⟩
def Reg.ctx (w : Width) (α : Nat) : Reg := ⟨.context, w, α, none⟩

def Reg.real32 (α : Nat) : Reg := .real .w32 α
def Reg.real64 (α : Nat) : Reg := .real .w64 α
def Reg.sw (α : Nat) : Reg := .stack .w32 α
def Reg.sr (α : Nat) : Reg := .stack .w64 α
def Reg.map32 (α : Nat) : Reg := .map .w32 α
def Reg.map64 (α : Nat) : Reg := .map .w64 α
def Reg.ctx32 (α : Nat) : Reg := .ctx .w32 α
def Reg.ctx64 (α : Nat) : Reg := .ctx .w64 α

/-- A four-byte Map word at a byte offset in a lookup-result namespace. -/
def Reg.mapWord (resource byteOffset : Nat) : Reg :=
  .map32 ((resource + byteOffset) * (resource + byteOffset + 1) / 2 + byteOffset)

/-- An eight-byte Map word at a byte offset in a lookup-result namespace. -/
def Reg.mapDword (resource byteOffset : Nat) : Reg :=
  ⟨.map, .w64, (resource + byteOffset) * (resource + byteOffset + 1) / 2 + byteOffset, none⟩

/-- Cantor pairing keeps resource identity and byte offset distinct, without a fixed stride. -/
def Reg.packet (κ offset : Nat) : Reg :=
  ⟨.packet, .w32, (κ + offset) * (κ + offset + 1) / 2 + offset, none⟩

def Reg.compoundPacket (p : CompoundPacketReg) : Reg :=
  ⟨.packet, .w32, p.κ, some p⟩

def Reg.valid (r : Reg) : Bool :=
  match r.compound with
  | none => r.kind != .packet || r.width == .w32
  | some p => r.kind == .packet && r.width == .w32 && r.alpha == p.κ &&
      [1, 2, 4, 8].contains p.bytes && p.byteIndex < p.bytes

end ClassifierExpr
