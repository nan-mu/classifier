import ClassifierExpr.Bits

namespace ClassifierExpr

/-! Named numeric functions from `doc/Expr/待处理.md#位向量与共同数值函数`. Architecture-neutral. -/

def ADD (w : Width) (a b : Nat) : Nat := MNat w.bits (a + b)
def SUB (w : Width) (a b : Nat) : Nat :=
  M w.bits (Int.ofNat (MNat w.bits a) - Int.ofNat (MNat w.bits b))
def MULLO (w : Width) (a b : Nat) : Nat := MNat w.bits (a * b)
def NEG (w : Width) (a : Nat) : Nat := M w.bits (-(Int.ofNat (MNat w.bits a)))
def ID (_w : Width) (a : Nat) : Nat := a

def AND (q : Nat) (a b : Nat) : Nat := MNat q (a &&& b)

def OR (q : Nat) (a b : Nat) : Nat := MNat q (a ||| b)

def XOR (q : Nat) (a b : Nat) : Nat := MNat q (a ^^^ b)

def kShift (w : Width) (b : Nat) : Nat := b % w.bits

def SHL (w : Width) (a b : Nat) : Nat :=
  MNat w.bits (MNat w.bits a * (1 <<< kShift w b))

def LSHR (w : Width) (a b : Nat) : Nat :=
  MNat w.bits a / (1 <<< kShift w b)

/-- Arithmetic right shift uses floor division of the signed view. -/
def ASHR (w : Width) (a b : Nat) : Nat :=
  M w.bits (s w.bits a / Int.ofNat (1 <<< kShift w b))

def LTU (w : Width) (a b : Nat) : Nat :=
  indicator (MNat w.bits a < MNat w.bits b)

def LTS (w : Width) (a b : Nat) : Nat :=
  indicator (s w.bits a < s w.bits b)

def LOW (q v : Nat) (a : Nat) : Nat := MNat q (MNat v a)

def EXTRACT (o ℓ v : Nat) (a : Nat) : Nat :=
  MNat ℓ (MNat v a / (1 <<< o))

def Z (q : Nat) (w : Width) (_v : Nat) (a : Nat) : Nat :=
  MNat w.bits (MNat q a)

def S (q : Nat) (w : Width) (_v : Nat) (a : Nat) : Nat :=
  M w.bits (s q (MNat q a))

def sgn : Int → Int
  | x => if x < 0 then -1 else if x == 0 then 0 else 1

def TQ (x y : Int) : Int :=
  if y == 0 then 0
  else sgn x * sgn y * (x.natAbs / y.natAbs)

def TR (x y : Int) : Int := x - y * TQ x y

def UDIV (w : Width) (zeroResult a b : Nat) : Nat :=
  let A := MNat w.bits a
  let B := MNat w.bits b
  if B == 0 then MNat w.bits zeroResult else A / B

def UREM (w : Width) (a b : Nat) : Nat :=
  let A := MNat w.bits a
  let B := MNat w.bits b
  if B == 0 then A else A % B

def SDIV (w : Width) (zeroResult a b : Nat) : Nat :=
  let x := s w.bits a
  let y := s w.bits b
  if y == 0 then MNat w.bits zeroResult else M w.bits (TQ x y)

def SREM (w : Width) (a b : Nat) : Nat :=
  let x := s w.bits a
  let y := s w.bits b
  if y == 0 then MNat w.bits a else M w.bits (TR x y)

def MULH (w : Width) (a b : Nat) : Nat :=
  M w.bits (s w.bits a * s w.bits b / Int.ofNat (1 <<< w.bits))

def MULHU (w : Width) (a b : Nat) : Nat :=
  MNat w.bits (MNat w.bits a * MNat w.bits b / (1 <<< w.bits))

def MULHSU (w : Width) (a b : Nat) : Nat :=
  M w.bits (s w.bits a * Int.ofNat (MNat w.bits b) / Int.ofNat (1 <<< w.bits))

def SELECTEQ (w : Width) (lhs rhs ifEqual ifDifferent : Nat) : Nat :=
  MNat w.bits (if MNat w.bits lhs == MNat w.bits rhs then ifEqual else ifDifferent)

def BSWAP (q v : Nat) (a : Nat) : Nat :=
  let bytes := q / 8
  Id.run do
    let mut acc := 0
    for j in [:bytes] do
      let bj := EXTRACT (8 * j) 8 v a
      acc := acc + bj * (1 <<< (8 * (bytes - 1 - j)))
    pure acc

/-- Merge low `q` bits of `src` into `old` (width `wbits`). Shared store helper. -/
def mergeLow (q wbits : Nat) (old src : Nat) : Nat :=
  let hi := old / (1 <<< q) * (1 <<< q)
  MNat wbits (hi + MNat q src)

end ClassifierExpr
