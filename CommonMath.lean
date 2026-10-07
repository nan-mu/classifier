/-!
# CommonMath — shared classifier mathematics

Executable Lean model of `doc/common-math.md`: registers, terms, Expr,
solve/eval, and named numeric functions. No Sail runtime objects.
-/

namespace CommonMath

/-! ## Widths and bit patterns -/

/-- Register / term width set \(W=\{32,64\}\). -/
inductive Width where
  | w32
  | w64
  deriving DecidableEq, BEq, Repr, Inhabited

def Width.bits : Width → Nat
  | .w32 => 32
  | .w64 => 64

def Width.mask (w : Width) : Nat :=
  (1 <<< w.bits) - 1

/-- \(M_q(z)=z\bmod 2^q\) with non-negative representative. -/
def M (q : Nat) (z : Int) : Nat :=
  let m := (1 : Int) <<< q
  let r := z % m
  if r < 0 then (r + m).toNat else r.toNat

def MNat (q : Nat) (a : Nat) : Nat :=
  a % (1 <<< q)

/-- Unsigned view \(u_q(a)=a\). -/
def u (q : Nat) (a : Nat) : Nat := MNat q a

/-- Signed two's-complement view \(s_q\). -/
def s (q : Nat) (a : Nat) : Int :=
  let a' := MNat q a
  let half := (1 : Nat) <<< (q - 1)
  if a' < half then Int.ofNat a' else Int.ofNat a' - Int.ofNat (1 <<< q)

def indicator (φ : Bool) : Nat := if φ then 1 else 0

/-! ## Registers -/

inductive RegKind where
  | real
  | stack
  | map
  deriving DecidableEq, BEq, Repr, Inhabited

/-- \(\mathrm{Reg}_{k,w}=(k,w,\alpha)\). -/
structure Reg where
  kind  : RegKind
  width : Width
  alpha : Nat
  deriving DecidableEq, BEq, Repr, Inhabited

def Reg.real32 (α : Nat) : Reg := ⟨.real, .w32, α⟩
def Reg.real64 (α : Nat) : Reg := ⟨.real, .w64, α⟩
def Reg.sw (α : Nat) : Reg := ⟨.stack, .w32, α⟩
def Reg.sr (α : Nat) : Reg := ⟨.stack, .w64, α⟩
def Reg.map32 (α : Nat) : Reg := ⟨.map, .w32, α⟩
def Reg.map64 (α : Nat) : Reg := ⟨.map, .w64, α⟩

/-- Canonical PC / SP / RA alphas in \(\mathcal I_{\mathrm{Real}}\). -/
def pcAlpha : Nat := 32
def spAlpha : Nat := 2
def raAlpha : Nat := 1
def x0Alpha : Nat := 0

def Reg.pc32 : Reg := Reg.real32 pcAlpha
def Reg.sp32 : Reg := Reg.real32 spAlpha
def Reg.ra32 : Reg := Reg.real32 raAlpha
def Reg.x0 : Reg := Reg.real32 x0Alpha

/-! ## Operators -/

/-- Form operators with fixed width signatures used by value functions. -/
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
  | mulhu32
  | mulh32
  | mulhsu32
  | divu32
  | remu32
  | div32
  | rem32
  | addImm32 (imm : Nat)
  | shlImm32 (k : Nat)
  | lshrImm32 (k : Nat)
  | ashrImm32 (k : Nat)
  | andImm32 (imm : Nat)
  | orImm32 (imm : Nat)
  | xorImm32 (imm : Nat)
  | slti32 (imm : Nat)
  | sltiu32 (imm : Nat)
  | auipc32 (uimm : Nat)
  | linkPlus4
  | linkPlus2
  | storeLow (q w : Nat)
  deriving DecidableEq, BEq, Repr

/-! ## Terms -/

inductive Term where
  | const (w : Width) (c : Nat)
  | var (w : Width) (ξ : Nat)
  | app (w : Width) (op : Op) (args : List Term)
  deriving Repr, Inhabited

def Term.width : Term → Width
  | .const w _ => w
  | .var w _ => w
  | .app w _ _ => w

def Term.C32 (c : Nat) : Term := .const .w32 (MNat 32 c)
def Term.C64 (c : Nat) : Term := .const .w64 (MNat 64 c)
def Term.V32 (ξ : Nat) : Term := .var .w32 ξ
def Term.V64 (ξ : Nat) : Term := .var .w64 ξ

/-! ## Relations and Expr -/

inductive Rel where
  | eq
  | ne
  | ltu | leu | gtu | geu
  | lts | les | gts | ges
  | eqN (q : Nat)
  | neN (q : Nat)
  | ltuN (q : Nat) | leuN (q : Nat) | gtuN (q : Nat) | geuN (q : Nat)
  | ltsN (q : Nat) | lesN (q : Nat) | gtsN (q : Nat) | gesN (q : Nat)
  | bitsnz (q : Nat)
  | bitsz (q : Nat)
  deriving DecidableEq, BEq, Repr, Inhabited

structure Expr where
  reg  : Reg
  rel  : Rel
  term : Term
  deriving Repr, Inhabited

def Expr.key (e : Expr) : Reg × Rel := (e.reg, e.rel)

def Expr.mkEq (r : Reg) (t : Term) : Expr := ⟨r, .eq, t⟩

/-! ## Named numeric functions (section 7) -/

def ADD (w : Width) (a b : Nat) : Nat := MNat w.bits (a + b)
def SUB (w : Width) (a b : Nat) : Nat := M (w.bits) (Int.ofNat (MNat w.bits a) - Int.ofNat (MNat w.bits b))
def MULLO (w : Width) (a b : Nat) : Nat := MNat w.bits (a * b)
def NEG (w : Width) (a : Nat) : Nat := M (w.bits) (-(Int.ofNat (MNat w.bits a)))
def ID (_w : Width) (a : Nat) : Nat := a

def bit (a j : Nat) : Nat := (a / (1 <<< j)) % 2

def AND (q : Nat) (a b : Nat) : Nat :=
  Id.run do
    let mut acc := 0
    for j in [:q] do
      acc := acc + bit a j * bit b j * (1 <<< j)
    pure acc

def OR (q : Nat) (a b : Nat) : Nat :=
  Id.run do
    let mut acc := 0
    for j in [:q] do
      let bj := max (bit a j) (bit b j)
      acc := acc + bj * (1 <<< j)
    pure acc

def XOR (q : Nat) (a b : Nat) : Nat :=
  Id.run do
    let mut acc := 0
    for j in [:q] do
      acc := acc + ((bit a j + bit b j) % 2) * (1 <<< j)
    pure acc

def kShift (w : Width) (b : Nat) : Nat := b % w.bits

def SHL (w : Width) (a b : Nat) : Nat :=
  MNat w.bits (MNat w.bits a * (1 <<< kShift w b))

def LSHR (w : Width) (a b : Nat) : Nat :=
  MNat w.bits a / (1 <<< kShift w b)

def ASHR (w : Width) (a b : Nat) : Nat :=
  let sa := s w.bits (MNat w.bits a)
  let k := kShift w b
  M w.bits (sa / (Int.ofNat (1 <<< k)))

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

/-- Toward-zero quotient. -/
def TQ (x y : Int) : Int :=
  if y == 0 then 0
  else sgn x * sgn y * (x.natAbs / y.natAbs)

def TR (x y : Int) : Int := x - y * TQ x y

def BSWAP (q v : Nat) (a : Nat) : Nat :=
  let bytes := q / 8
  Id.run do
    let mut acc := 0
    for j in [:bytes] do
      let bj := EXTRACT (8 * j) 8 v a
      acc := acc + bj * (1 <<< (8 * (bytes - 1 - j)))
    pure acc

def MULHU32 (a b : Nat) : Nat :=
  MNat 32 ((MNat 32 a * MNat 32 b) / (1 <<< 32))

def MULH32 (a b : Nat) : Nat :=
  let p := s 32 a * s 32 b
  M 32 (p / (Int.ofNat (1 <<< 32)))

def MULHSU32 (a b : Nat) : Nat :=
  let p := s 32 a * Int.ofNat (MNat 32 b)
  M 32 (p / (Int.ofNat (1 <<< 32)))

def DIVU32 (a b : Nat) : Nat :=
  let a := MNat 32 a; let b := MNat 32 b
  if b == 0 then (1 <<< 32) - 1 else a / b

def REMU32 (a b : Nat) : Nat :=
  let a := MNat 32 a; let b := MNat 32 b
  if b == 0 then a else a - b * (a / b)

def DIV32 (a b : Nat) : Nat :=
  let x := s 32 a; let y := s 32 b
  if y == 0 then (1 <<< 32) - 1
  else if x == -(Int.ofNat (1 <<< 31)) && y == -1 then 1 <<< 31
  else M 32 (TQ x y)

def REM32 (a b : Nat) : Nat :=
  let x := s 32 a; let y := s 32 b
  if y == 0 then MNat 32 a
  else if x == -(Int.ofNat (1 <<< 31)) && y == -1 then 0
  else M 32 (TR x y)

/-! ## Operator interpretation -/

partial def interpretOp (op : Op) (args : List Nat) : Nat :=
  match op, args with
  | .add w, [a, b] => ADD w a b
  | .sub w, [a, b] => SUB w a b
  | .mullo w, [a, b] => MULLO w a b
  | .neg w, [a] => NEG w a
  | .id w, [a] => ID w a
  | .and q, [a, b] => AND q a b
  | .or q, [a, b] => OR q a b
  | .xor q, [a, b] => XOR q a b
  | .shl w, [a, b] => SHL w a b
  | .lshr w, [a, b] => LSHR w a b
  | .ashr w, [a, b] => ASHR w a b
  | .ltu w, [a, b] => LTU w a b
  | .lts w, [a, b] => LTS w a b
  | .low q v, [a] => LOW q v a
  | .extract o ℓ v, [a] => EXTRACT o ℓ v a
  | .zext q w v, [a] => Z q w v a
  | .sext q w v, [a] => S q w v a
  | .bswap q v, [a] => BSWAP q v a
  | .mulhu32, [a, b] => MULHU32 a b
  | .mulh32, [a, b] => MULH32 a b
  | .mulhsu32, [a, b] => MULHSU32 a b
  | .divu32, [a, b] => DIVU32 a b
  | .remu32, [a, b] => REMU32 a b
  | .div32, [a, b] => DIV32 a b
  | .rem32, [a, b] => REM32 a b
  | .addImm32 imm, [a] => MNat 32 (a + imm)
  | .shlImm32 k, [a] => MNat 32 (MNat 32 a * (1 <<< (k % 32)))
  | .lshrImm32 k, [a] => MNat 32 a / (1 <<< (k % 32))
  | .ashrImm32 k, [a] => M 32 (s 32 a / Int.ofNat (1 <<< (k % 32)))
  | .andImm32 imm, [a] => AND 32 a imm
  | .orImm32 imm, [a] => OR 32 a imm
  | .xorImm32 imm, [a] => XOR 32 a imm
  | .slti32 imm, [a] => indicator (s 32 a < s 32 imm)
  | .sltiu32 imm, [a] => indicator (MNat 32 a < MNat 32 imm)
  | .auipc32 uimm, [π] => MNat 32 (π + uimm)
  | .linkPlus4, [π] => MNat 32 (π + 4)
  | .linkPlus2, [π] => MNat 32 (π + 2)
  | .storeLow q wbits, [old, src] =>
      let hi := old / (1 <<< q) * (1 <<< q)
      MNat wbits (hi + MNat q src)
  | _, _ => 0

/-! ## FV, eval, solve -/

def Var := Width × Nat

partial def FV : Term → List Var
  | .const _ _ => []
  | .var w ξ => [(w, ξ)]
  | .app _ _ args => args.foldl (fun acc t => acc ++ FV t) []

def FV.empty (t : Term) : Bool := (FV t).isEmpty

partial def eval : Term → Option Nat
  | .const _ c => some c
  | .var _ _ => none
  | .app _ op args =>
      let rec go : List Term → Option (List Nat)
        | [] => some []
        | t :: ts =>
          match eval t, go ts with
          | some v, some vs => some (v :: vs)
          | _, _ => none
      match go args with
      | some vs => some (interpretOp op vs)
      | none => none

/-- \(\operatorname{solve}_w\): fold closed terms to constants; leave open terms intact. -/
def solve (t : Term) : Term :=
  if FV.empty t then
    match eval t with
    | some c => .const t.width (MNat t.width.bits c)
    | none => t
  else t

def star (w : Width) (op : Op) (args : List Term) : Term :=
  solve (.app w op args)

def solveExpr (e : Expr) : Expr :=
  { e with term := solve e.term }

/-! ## Expr sets, key uniqueness, override -/

/-- Finite Expr set encoded as a list with unique keys (invariant). -/
abbrev ExprSet := List Expr

def keysUnique (E : ExprSet) : Bool :=
  Id.run do
    let mut seen : List (Reg × Rel) := []
    for e in E do
      if seen.elem e.key then return false
      seen := e.key :: seen
    pure true

def lookupEq (E : ExprSet) (r : Reg) : Option Term :=
  match E.find? (fun e => e.reg == r && e.rel == .eq) with
  | some e => some e.term
  | none => none

/-- Override \(E_g\times E_i\): drop same-key members of \(E_g\), then union \(E_i\). -/
def override (Eg Ei : ExprSet) : ExprSet :=
  let kept := Eg.filter (fun e => !(Ei.any (fun ei => ei.key == e.key)))
  kept ++ Ei

/-! ## Relation interpretation (for tests / Predicate later) -/

def interpretRel (wbits : Nat) (rel : Rel) (a b : Nat) : Bool :=
  let a := MNat wbits a; let b := MNat wbits b
  match rel with
  | .eq => a == b
  | .ne => a != b
  | .ltu => a < b
  | .leu => a ≤ b
  | .gtu => a > b
  | .geu => a ≥ b
  | .lts => s wbits a < s wbits b
  | .les => s wbits a ≤ s wbits b
  | .gts => s wbits a > s wbits b
  | .ges => s wbits a ≥ s wbits b
  | .eqN q => MNat q a == MNat q b
  | .neN q => MNat q a != MNat q b
  | .ltuN q => MNat q a < MNat q b
  | .leuN q => MNat q a ≤ MNat q b
  | .gtuN q => MNat q a > MNat q b
  | .geuN q => MNat q a ≥ MNat q b
  | .ltsN q => s q (MNat q a) < s q (MNat q b)
  | .lesN q => s q (MNat q a) ≤ s q (MNat q b)
  | .gtsN q => s q (MNat q a) > s q (MNat q b)
  | .gesN q => s q (MNat q a) ≥ s q (MNat q b)
  | .bitsnz q => AND q (MNat q a) (MNat q b) != 0
  | .bitsz q => AND q (MNat q a) (MNat q b) == 0

/-! ## FFI-friendly numeric exports -/

@[export common_math_add32]
def exportAdd32 (a b : UInt32) : UInt32 :=
  UInt32.ofNat (ADD .w32 a.toNat b.toNat)

@[export common_math_sub32]
def exportSub32 (a b : UInt32) : UInt32 :=
  UInt32.ofNat (SUB .w32 a.toNat b.toNat)

@[export common_math_and32]
def exportAnd32 (a b : UInt32) : UInt32 :=
  UInt32.ofNat (AND 32 a.toNat b.toNat)

@[export common_math_div32]
def exportDiv32 (a b : UInt32) : UInt32 :=
  UInt32.ofNat (DIV32 a.toNat b.toNat)

@[export common_math_divu32]
def exportDivu32 (a b : UInt32) : UInt32 :=
  UInt32.ofNat (DIVU32 a.toNat b.toNat)

end CommonMath
