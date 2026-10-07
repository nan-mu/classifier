import CommonMath.Bits

namespace CommonMath

inductive RegKind where
  | real
  | stack
  | map
  deriving DecidableEq, BEq, Repr, Inhabited

/-- \(\mathrm{Reg}_{k,w}=(k,w,\alpha)\). Alpha assignment is architecture-specific. -/
structure Reg where
  kind  : RegKind
  width : Width
  alpha : Nat
  deriving DecidableEq, BEq, Repr, Inhabited

def Reg.real (w : Width) (α : Nat) : Reg := ⟨.real, w, α⟩
def Reg.stack (w : Width) (α : Nat) : Reg := ⟨.stack, w, α⟩
def Reg.map (w : Width) (α : Nat) : Reg := ⟨.map, w, α⟩

def Reg.real32 (α : Nat) : Reg := .real .w32 α
def Reg.real64 (α : Nat) : Reg := .real .w64 α
def Reg.sw (α : Nat) : Reg := .stack .w32 α
def Reg.sr (α : Nat) : Reg := .stack .w64 α
def Reg.map32 (α : Nat) : Reg := .map .w32 α
def Reg.map64 (α : Nat) : Reg := .map .w64 α

end CommonMath
