import CommonMath.Bits
import CommonMath.Numeric

namespace CommonMath

/-- Form operators whose signatures lie in \(W\) (`doc/common-math.md` §4, §7). -/
inductive Op where
  | add (w : Width)
  | sub (w : Width)
  | mullo (w : Width)
  | neg (w : Width)
  | id (w : Width)
  | and (q : Nat)
  | or (q : Nat)
  | xor (q : Nat)
  | shl (w : Width)
  | lshr (w : Width)
  | ashr (w : Width)
  | ltu (w : Width)
  | lts (w : Width)
  | low (q v : Nat)
  | extract (o ℓ v : Nat)
  | zext (q : Nat) (w : Width) (v : Nat)
  | sext (q : Nat) (w : Width) (v : Nat)
  | bswap (q v : Nat)
  | mergeLow (q wbits : Nat)
  deriving DecidableEq, BEq, Repr

def interpretOp (op : Op) (args : List Nat) : Option Nat :=
  match op, args with
  | .add w, [a, b] => some (ADD w a b)
  | .sub w, [a, b] => some (SUB w a b)
  | .mullo w, [a, b] => some (MULLO w a b)
  | .neg w, [a] => some (NEG w a)
  | .id w, [a] => some (ID w a)
  | .and q, [a, b] => some (AND q a b)
  | .or q, [a, b] => some (OR q a b)
  | .xor q, [a, b] => some (XOR q a b)
  | .shl w, [a, b] => some (SHL w a b)
  | .lshr w, [a, b] => some (LSHR w a b)
  | .ashr w, [a, b] => some (ASHR w a b)
  | .ltu w, [a, b] => some (LTU w a b)
  | .lts w, [a, b] => some (LTS w a b)
  | .low q v, [a] => some (LOW q v a)
  | .extract o ℓ v, [a] => some (EXTRACT o ℓ v a)
  | .zext q w v, [a] => some (Z q w v a)
  | .sext q w v, [a] => some (S q w v a)
  | .bswap q v, [a] => some (BSWAP q v a)
  | .mergeLow q wbits, [old, src] => some (mergeLow q wbits old src)
  | _, _ => none

end CommonMath
