import ClassifierExpr.Bits

namespace ClassifierExpr

inductive RegKind where
  | real
  | stack
  | map
  | packet
  | context
  deriving DecidableEq, BEq, ReflBEq, LawfulBEq, Repr, Inhabited

/-- \(\mathrm{Reg}_{k,w}=(k,w,\alpha)\). Alpha assignment is architecture-specific. -/
structure Reg where
  kind  : RegKind
  width : Width
  alpha : Nat
  deriving DecidableEq, BEq, ReflBEq, LawfulBEq, Repr, Inhabited

def Reg.real (w : Width) (α : Nat) : Reg := ⟨.real, w, α⟩
def Reg.stack (w : Width) (α : Nat) : Reg := ⟨.stack, w, α⟩
def Reg.map (w : Width) (α : Nat) : Reg := ⟨.map, w, α⟩
def Reg.ctx (w : Width) (α : Nat) : Reg := ⟨.context, w, α⟩

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
  ⟨.map, .w64, (resource + byteOffset) * (resource + byteOffset + 1) / 2 + byteOffset⟩

/-- Cantor pairing keeps resource identity and byte offset distinct, without a fixed stride. -/
def Reg.packet (κ offset : Nat) : Reg :=
  ⟨.packet, .w32, (κ + offset) * (κ + offset + 1) / 2 + offset⟩

def Reg.valid (r : Reg) : Bool := r.kind != .packet || r.width == .w32

end ClassifierExpr
