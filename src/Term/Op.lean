import Term.Value.Bits
import Term.Value.Numeric

namespace Term
open Term.Value

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
  /-- Value-preserving packet-read annotation. Remaining arguments encode the
checked compound register; they are constants, not extra memory reads. -/
  | packetRead (bytes endCtx : Nat)
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
  | .packetRead bytes ending => [29, bytes, ending]

/-- Inverse of `orderKey` on the image of that function. -/
def Op.ofOrderKey : List Nat → Option Op
  | [0, 32] => some (.add .w32) | [0, 64] => some (.add .w64)
  | [1, 32] => some (.sub .w32) | [1, 64] => some (.sub .w64)
  | [2, 32] => some (.mullo .w32) | [2, 64] => some (.mullo .w64)
  | [3, 32, z] => some (.udiv .w32 z) | [3, 64, z] => some (.udiv .w64 z)
  | [4, 32] => some (.urem .w32) | [4, 64] => some (.urem .w64)
  | [5, 32, z] => some (.sdiv .w32 z) | [5, 64, z] => some (.sdiv .w64 z)
  | [6, 32] => some (.srem .w32) | [6, 64] => some (.srem .w64)
  | [7, 32] => some (.mulh .w32) | [7, 64] => some (.mulh .w64)
  | [8, 32] => some (.mulhu .w32) | [8, 64] => some (.mulhu .w64)
  | [9, 32] => some (.mulhsu .w32) | [9, 64] => some (.mulhsu .w64)
  | [10, 32] => some (.selectEq .w32) | [10, 64] => some (.selectEq .w64)
  | [11, 32] => some (.neg .w32) | [11, 64] => some (.neg .w64)
  | [12, 32] => some (.id .w32) | [12, 64] => some (.id .w64)
  | [13, q] => some (.and q) | [14, q] => some (.or q) | [15, q] => some (.xor q)
  | [16, 32] => some (.shl .w32) | [16, 64] => some (.shl .w64)
  | [17, 32] => some (.lshr .w32) | [17, 64] => some (.lshr .w64)
  | [18, 32] => some (.ashr .w32) | [18, 64] => some (.ashr .w64)
  | [19, 32] => some (.ltu .w32) | [19, 64] => some (.ltu .w64)
  | [20, 32] => some (.lts .w32) | [20, 64] => some (.lts .w64)
  | [21, q, v] => some (.low q v)
  | [22, o, n, v] => some (.extract o n v)
  | [23, q, 32, v] => some (.zext q .w32 v) | [23, q, 64, v] => some (.zext q .w64 v)
  | [24, q, 32, v] => some (.sext q .w32 v) | [24, q, 64, v] => some (.sext q .w64 v)
  | [25, q, v] => some (.bswap q v)
  | [26, e, l] => some (.externalResult e l)
  | [27, r] => some (.inputByte r)
  | [28, q, v] => some (.mergeLow q v)
  | [29, bytes, ending] => some (.packetRead bytes ending)
  | _ => none

theorem Op.orderKey_round (op : Op) : Op.ofOrderKey op.orderKey = some op := by
  cases op with
  | add w => cases w <;> rfl
  | sub w => cases w <;> rfl
  | mullo w => cases w <;> rfl
  | udiv w z => cases w <;> rfl
  | urem w => cases w <;> rfl
  | sdiv w z => cases w <;> rfl
  | srem w => cases w <;> rfl
  | mulh w => cases w <;> rfl
  | mulhu w => cases w <;> rfl
  | mulhsu w => cases w <;> rfl
  | selectEq w => cases w <;> rfl
  | neg w => cases w <;> rfl
  | id w => cases w <;> rfl
  | and q => rfl
  | or q => rfl
  | xor q => rfl
  | shl w => cases w <;> rfl
  | lshr w => cases w <;> rfl
  | ashr w => cases w <;> rfl
  | ltu w => cases w <;> rfl
  | lts w => cases w <;> rfl
  | low q v => rfl
  | extract o n v => rfl
  | zext q w v => cases w <;> rfl
  | sext q w v => cases w <;> rfl
  | bswap q v => rfl
  | externalResult e l => rfl
  | inputByte r => rfl
  | mergeLow q v => rfl
  | packetRead bytes ending => rfl

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
  | .packetRead bytes _ => output == .w32 && [1, 2, 4, 8].contains bytes &&
      !inputs.isEmpty && inputs.all (· == .w32)

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
  | .packetRead _ _, value :: _ => some value
  | _, _ => none

end Term
