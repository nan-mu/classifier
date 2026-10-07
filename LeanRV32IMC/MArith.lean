import CommonMath

namespace LeanRV32IMC
open CommonMath

/-! RV32M numeric rules (div-by-zero / overflow). Not part of CommonMath. -/

def mulhu (a b : Nat) : Nat :=
  MNat 32 ((MNat 32 a * MNat 32 b) / (1 <<< 32))

def mulh (a b : Nat) : Nat :=
  let p := s 32 a * s 32 b
  M 32 (p / (Int.ofNat (1 <<< 32)))

def mulhsu (a b : Nat) : Nat :=
  let p := s 32 a * Int.ofNat (MNat 32 b)
  M 32 (p / (Int.ofNat (1 <<< 32)))

def divu (a b : Nat) : Nat :=
  let a := MNat 32 a; let b := MNat 32 b
  if b == 0 then (1 <<< 32) - 1 else a / b

def remu (a b : Nat) : Nat :=
  let a := MNat 32 a; let b := MNat 32 b
  if b == 0 then a else a - b * (a / b)

def divs (a b : Nat) : Nat :=
  let x := s 32 a; let y := s 32 b
  if y == 0 then (1 <<< 32) - 1
  else if x == -(Int.ofNat (1 <<< 31)) && y == -1 then 1 <<< 31
  else M 32 (TQ x y)

def rems (a b : Nat) : Nat :=
  let x := s 32 a; let y := s 32 b
  if y == 0 then MNat 32 a
  else if x == -(Int.ofNat (1 <<< 31)) && y == -1 then 0
  else M 32 (TR x y)

/-- Closed fold; `none` if either source still has free vars. -/
def closedBin (f : Nat → Nat → Nat) (ta tb : Term) : Option Term :=
  match eval (solve ta), eval (solve tb) with
  | some a, some b => some (Term.C32 (f a b))
  | _, _ => none

end LeanRV32IMC
