import CommonMath.Numeric

namespace CommonMath

@[export common_math_add32]
def exportAdd32 (a b : UInt32) : UInt32 :=
  UInt32.ofNat (ADD .w32 a.toNat b.toNat)

@[export common_math_sub32]
def exportSub32 (a b : UInt32) : UInt32 :=
  UInt32.ofNat (SUB .w32 a.toNat b.toNat)

@[export common_math_and32]
def exportAnd32 (a b : UInt32) : UInt32 :=
  UInt32.ofNat (AND 32 a.toNat b.toNat)

/-- Toward-zero signed quotient bits; div-by-zero and overflow left to callers. -/
@[export common_math_tq32]
def exportTq32 (a b : UInt32) : UInt32 :=
  let x := s 32 a.toNat
  let y := s 32 b.toNat
  if y == 0 then 0xffffffff
  else UInt32.ofNat (M 32 (TQ x y))

@[export common_math_divu32]
def exportDivu32 (a b : UInt32) : UInt32 :=
  let a := a.toNat; let b := b.toNat
  if b == 0 then 0xffffffff
  else UInt32.ofNat (a / b)

end CommonMath
