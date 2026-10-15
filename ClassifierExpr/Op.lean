import ClassifierExpr.Bits
import ClassifierExpr.Numeric

namespace ClassifierExpr

/-- Form operators whose signatures lie in \(W\) (`doc/Expr/待处理.md#右值`,
`doc/Expr/待处理.md#位向量与共同数值函数`). -/
inductive Op where
  | add (w : Width)
  | sub (w : Width)
  | mullo (w : Width)
  | udiv (w : Width) (zeroResult : Nat)
  | urem (w : Width)
  | sdiv (w : Width) (zeroResult : Nat)
  | srem (w : Width)
  | mulh (w : Width)
  | mulhu (w : Width)
  | mulhsu (w : Width)
  | selectEq (w : Width)
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
  | externalResult (event lane : Nat)
  /-- Byte in a resource's immutable input image; eval has no concrete image. -/
  | inputByte (resource : Nat)
  | mergeLow (q wbits : Nat)
  deriving DecidableEq, BEq, ReflBEq, LawfulBEq, Repr

/-- Constructor order and every raw semantic parameter, without carrier erasure. -/
def Op.orderKey : Op → List Nat
  | .add w => [0, w.bits] | .sub w => [1, w.bits] | .mullo w => [2, w.bits]
  | .udiv w z => [3, w.bits, z] | .urem w => [4, w.bits]
  | .sdiv w z => [5, w.bits, z] | .srem w => [6, w.bits]
  | .mulh w => [7, w.bits] | .mulhu w => [8, w.bits]
  | .mulhsu w => [9, w.bits] | .selectEq w => [10, w.bits]
  | .neg w => [11, w.bits] | .id w => [12, w.bits]
  | .and q => [13, q] | .or q => [14, q] | .xor q => [15, q]
  | .shl w => [16, w.bits] | .lshr w => [17, w.bits] | .ashr w => [18, w.bits]
  | .ltu w => [19, w.bits] | .lts w => [20, w.bits]
  | .low q v => [21, q, v] | .extract o n v => [22, o, n, v]
  | .zext q w v => [23, q, w.bits, v] | .sext q w v => [24, q, w.bits, v]
  | .bswap q v => [25, q, v] | .externalResult e l => [26, e, l]
  | .inputByte r => [27, r] | .mergeLow q v => [28, q, v]

/-- The shared authority for output carriers, input carriers and operator parameters. -/
def Op.validSignature (op : Op) (output : Width) (inputs : List Width) : Bool :=
  let uniform (n : Nat) := inputs.length == n && inputs.all (· == output)
  let input (v : Nat) := inputs.length == 1 && inputs.all (·.bits == v)
  let bounded (q bits : Nat) := 0 < q && q ≤ bits
  match op with
  | .add w | .sub w | .mullo w | .udiv w _ | .urem w | .sdiv w _ | .srem w
  | .mulh w | .mulhu w | .mulhsu w | .shl w | .lshr w | .ashr w | .ltu w | .lts w =>
    output == w && uniform 2
  | .selectEq w => output == w && uniform 4
  | .neg w | .id w => output == w && uniform 1
  | .and q | .or q | .xor q => bounded q output.bits && uniform 2
  | .low q v => bounded q v && q ≤ output.bits && input v
  | .extract o len v => 0 < len && o + len ≤ v && len ≤ output.bits && input v
  | .zext q out v | .sext q out v =>
    output == out && bounded q output.bits && q ≤ v && input v
  | .bswap q v =>
    (q == 16 || q == 32 || q == 64) && q ≤ v && q ≤ output.bits && input v
  | .mergeLow q v => v == output.bits && bounded q v && uniform 2
  | .externalResult _ _ => !inputs.isEmpty && inputs.all (· == output)
  | .inputByte _ => output == .w32 && match inputs with
    | [base, address] => base == address
    | _ => false

def interpretOp (op : Op) (args : List Nat) : Option Nat :=
  match op, args with
  | .add w, [a, b] => some (ADD w a b)
  | .sub w, [a, b] => some (SUB w a b)
  | .mullo w, [a, b] => some (MULLO w a b)
  | .udiv w zeroResult, [a, b] => some (UDIV w zeroResult a b)
  | .urem w, [a, b] => some (UREM w a b)
  | .sdiv w zeroResult, [a, b] => some (SDIV w zeroResult a b)
  | .srem w, [a, b] => some (SREM w a b)
  | .mulh w, [a, b] => some (MULH w a b)
  | .mulhu w, [a, b] => some (MULHU w a b)
  | .mulhsu w, [a, b] => some (MULHSU w a b)
  | .selectEq w, [lhs, rhs, yes, no] => some (SELECTEQ w lhs rhs yes no)
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

end ClassifierExpr
