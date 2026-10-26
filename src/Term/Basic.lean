import Std.Tactic
import Init.Data.Order.Ord
import Term.Value.NumericProofs
import Term.Value.Bits
import Term.Op
import Expression.Reg

namespace Term
open Term.Value Expression

mutual
/-- Storage named by an expression. Each constructor carries only the fields in its grammar. -/
inductive Reg where
  | real (r b e : Nat)
  | stack (b e : Nat)
  | map (m : Nat) (key : List Term) (b e : Nat)
  | packet (b e : Nat)
  | context (field : ContextField) (b e : Nat)
  deriving Repr, Inhabited

inductive Term where
  | const (w : Width) (c : Nat)
  | var (w : Width) (ξ : Nat)
  /-- Live register. A value that must survive a later write is the term stored in `Expr`. -/
  | regVar (reg : Reg)
  | app (w : Width) (op : Op) (args : List Term)
  deriving Repr, Inhabited
end

mutual
  private def regDecEq : (a b : Reg) → Decidable (a = b)
    | .real r1 b1 e1, .real r2 b2 e2 =>
      decidable_of_iff (r1 = r2 ∧ b1 = b2 ∧ e1 = e2) (by simp)
    | .stack b1 e1, .stack b2 e2 =>
      decidable_of_iff (b1 = b2 ∧ e1 = e2) (by simp)
    | .map m1 k1 b1 e1, .map m2 k2 b2 e2 =>
      letI := termListDecEq k1 k2
      decidable_of_iff (m1 = m2 ∧ k1 = k2 ∧ b1 = b2 ∧ e1 = e2) (by simp)
    | .packet b1 e1, .packet b2 e2 =>
      decidable_of_iff (b1 = b2 ∧ e1 = e2) (by simp)
    | .context j1 b1 e1, .context j2 b2 e2 =>
      decidable_of_iff (j1 = j2 ∧ b1 = b2 ∧ e1 = e2) (by simp)
    | .real .., .stack .. | .real .., .map .. | .real .., .packet .. | .real .., .context ..
    | .stack .., .real .. | .stack .., .map .. | .stack .., .packet .. | .stack .., .context ..
    | .map .., .real .. | .map .., .stack .. | .map .., .packet .. | .map .., .context ..
    | .packet .., .real .. | .packet .., .stack .. | .packet .., .map .. | .packet .., .context ..
    | .context .., .real .. | .context .., .stack .. | .context .., .map .. | .context .., .packet .. =>
      .isFalse (by intro h; cases h)
  termination_by a b => sizeOf a + sizeOf b

  private def termDecEq : (a b : Term) → Decidable (a = b)
    | .const w c, .const v d => decidable_of_iff (w = v ∧ c = d) (by simp)
    | .var w n, .var v m => decidable_of_iff (w = v ∧ n = m) (by simp)
    | .regVar r, .regVar s =>
      letI := regDecEq r s
      decidable_of_iff (r = s) (by simp)
    | .app w f xs, .app v g ys =>
      letI := termListDecEq xs ys
      decidable_of_iff (w = v ∧ f = g ∧ xs = ys) (by simp)
    | .const .., .var .. | .const .., .regVar .. | .const .., .app ..
    | .var .., .const .. | .var .., .regVar .. | .var .., .app ..
    | .regVar .., .const .. | .regVar .., .var .. | .regVar .., .app ..
    | .app .., .const .. | .app .., .var .. | .app .., .regVar .. =>
      .isFalse (by intro h; cases h)
  termination_by a b => sizeOf a + sizeOf b

  private def termListDecEq : (xs ys : List Term) → Decidable (xs = ys)
    | [], [] => .isTrue rfl
    | [], _ :: _ | _ :: _, [] => .isFalse (by intro h; cases h)
    | x :: xs, y :: ys =>
      letI := termDecEq x y
      letI := termListDecEq xs ys
      decidable_of_iff (x = y ∧ xs = ys) (by simp)
  termination_by xs ys => sizeOf xs + sizeOf ys
end

instance : DecidableEq Reg := regDecEq
instance : DecidableEq Term := termDecEq
instance : BEq Reg := ⟨fun a b => decide (a = b)⟩
instance : BEq Term := ⟨fun a b => decide (a = b)⟩
instance : LawfulBEq Reg where
  eq_of_beq := of_decide_eq_true
  rfl := of_decide_eq_self_eq_true _
instance : LawfulBEq Term where
  eq_of_beq := of_decide_eq_true
  rfl := of_decide_eq_self_eq_true _

namespace Reg

def lo : Reg → Nat
  | .real _ b _ => b
  | .stack b _ => b
  | .map _ _ b _ => b
  | .packet b _ => b
  | .context _ b _ => b

def hi : Reg → Nat
  | .real _ _ e => e
  | .stack _ e => e
  | .map _ _ _ e => e
  | .packet _ e => e
  | .context _ _ e => e

def bits (r : Reg) : Nat := r.hi - r.lo

def valid (r : Reg) : Bool :=
  decide (r.lo < r.hi) &&
    match r with
    | .context j _ e => decide (e ≤ j.cap)
    | _ => true

def index : Reg → Nat
  | .real r _ _ => r
  | .map m _ _ _ => m
  | .context (.lddw slot) _ _ => slot
  | .context (.mapKeyBytes id) _ _ => id
  | .context (.mapValueBytes id) _ _ => id
  | _ => 0

def withInterval (r : Reg) (b e : Nat) : Reg :=
  match r with
  | .real id _ _ => .real id b e
  | .stack _ _ => .stack b e
  | .map m key _ _ => .map m key b e
  | .packet _ _ => .packet b e
  | .context j _ _ => .context j b e

def sameResource : Reg → Reg → Bool
  | .real a .., .real c .. => a == c
  | .stack .., .stack .. => true
  | .map a ka .., .map c kc .. => a == c && ka == kc
  | .packet .., .packet .. => true
  | .context a .., .context c .. => a == c
  | _, _ => false

def overlaps (a b : Reg) : Bool :=
  a.sameResource b && decide (a.lo < b.hi && b.lo < a.hi)

def r32 (r : Nat) : Reg := .real r 0 32
def r64 (r : Nat) : Reg := .real r 0 64

end Reg

/-- Full machine register. RV32 uses `real32`. eBPF's 64-bit view uses `real64`. -/
def Reg.real32 : Nat → Reg := Reg.r32
def Reg.real64 : Nat → Reg := Reg.r64


def Term.width : Term → Width
  | .const w _ => w
  | .var w _ => w
  | .regVar r => Width.ofBits r.bits
  | .app w _ _ => w

/-- Bits constrained by the term. Narrow `low` and `extract` keep their own length. -/
def Term.semanticBits : Term → Nat
  | .const w _ => w.bits
  | .var w _ => w.bits
  | .regVar r => r.bits
  | .app w op _ =>
    match op with
    | .low q _ => q
    | .extract _ len _ => len
    | .zext q _ _ => q
    | .sext q _ _ => q
    | .and q | .or q | .xor q => q
    | .bswap q _ => q
    | .mergeLow _ n => n
    | .inputByte _ => 8
    | .add u | .sub u | .mullo u | .udiv u _ | .urem u | .sdiv u _ | .srem u
    | .mulh u | .mulhu u | .mulhsu u | .selectEq u | .neg u | .id u
    | .shl u | .lshr u | .ashr u | .ltu u | .lts u => u.bits
    | .externalResult _ | .packetRead _ _ => w.bits

def Term.C (w : Width) (c : Nat) : Term := .const w (MNat w.bits c)
def Term.C32 (c : Nat) : Term := .C .w32 c
def Term.C64 (c : Nat) : Term := .C .w64 c
def Term.V (w : Width) (ξ : Nat) : Term := .var w ξ
def Term.V32 (ξ : Nat) : Term := .V .w32 ξ
def Term.V64 (ξ : Nat) : Term := .V .w64 ξ

structure Var where
  width : Width
  name  : Nat
  register : Option Reg := none
  deriving DecidableEq, BEq, Repr

def FV : Term → List Var
  | .const _ _ => []
  | .var w ξ => [⟨w, ξ, none⟩]
  | .regVar r => [⟨Width.ofBits r.bits, r.index, some r⟩]
  | .app _ _ args => args.foldl (fun acc t => acc ++ FV t) []

def FV.isEmpty (t : Term) : Bool := (FV t).isEmpty
mutual
  def Term.wellFormed : Term → Bool
    | .const w c => c < 2 ^ w.bits
    | .var _ _ => true
    | .regVar reg => reg.valid
    | .app w op args => op.validSignature w (args.map Term.width) && termsWellFormed args
  termination_by t => sizeOf t

  def termsWellFormed : List Term → Bool
    | [] => true
    | t :: ts => t.wellFormed && termsWellFormed ts
  termination_by ts => sizeOf ts
end

/-- Only the two external operation families can be supplied by the environment. -/
structure ExternalInterpretation where
  externalResult : Width → Nat → List Nat → Option Nat
  inputByte : Nat → Nat → Nat → Option Nat

def ExternalInterpretation.Total (θ : ExternalInterpretation) : Prop :=
  (∀ w lane args, ∃ v, θ.externalResult w lane args = some v) ∧
  (∀ resource base address, ∃ v, θ.inputByte resource base address = some v)

def interpretWith (θ : ExternalInterpretation) (w : Width) (op : Op)
    (args : List Nat) : Option Nat :=
  match op, args with
  | .externalResult lane, vs => θ.externalResult w lane vs
  | .inputByte resource, [base, address] => θ.inputByte resource base address
  | _, _ => interpretOp op args

mutual
  def interpretTerm (ν : Var → Nat) (θ : ExternalInterpretation) : Term → Option Nat
    | .const w c => if c < 2 ^ w.bits then some c else none
    | .var w ξ => some (MNat w.bits (ν ⟨w, ξ, none⟩))
    | .regVar r =>
      if r.valid then
        some (MNat (Width.ofBits r.bits).bits
          (MNat r.bits (ν ⟨Width.ofBits r.bits, r.index, some r⟩)))
      else none
    | .app w op args => do
      if !op.validSignature w (args.map Term.width) then none else
        let values ← interpretTerms ν θ args
        let value ← interpretWith θ w op values
        pure (MNat w.bits value)
  termination_by t => sizeOf t

  def interpretTerms (ν : Var → Nat) (θ : ExternalInterpretation) :
      List Term → Option (List Nat)
    | [] => some []
    | t :: ts => do
      let value ← interpretTerm ν θ t
      let values ← interpretTerms ν θ ts
      pure (value :: values)
  termination_by ts => sizeOf ts
end


mutual
  def eval : Term → Option Nat
    | .const w c => if c < 2 ^ w.bits then some c else none
    | .var _ _ => none
    | .regVar _ => none
    | .app w op args => do
      if !op.validSignature w (args.map Term.width) then none else
        let values ← evalArgs args
        let value ← interpretOp op values
        pure (MNat w.bits value)
  termination_by t => sizeOf t

  private def evalArgs : List Term → Option (List Nat)
    | [] => some []
    | t :: ts =>
        match eval t, evalArgs ts with
        | some v, some vs => some (v :: vs)
        | _, _ => none
  termination_by ts => sizeOf ts
end

mutual
  /-- Prefix encoding for the raw structural order. Zero delimits argument lists. -/
  def Term.orderKey : Term → List Nat
    | .const w c => [w.bits + 1, 1, c + 1]
    | .var w n => [w.bits + 1, 2, n + 1]
    | .regVar r => [3] ++ regOrderKey r
    | .app w op args =>
      [w.bits + 1, 4] ++ op.orderKey.map (· + 1) ++ [0] ++ termOrderKeys args ++ [0]
  termination_by t => sizeOf t

  private def termOrderKeys : List Term → List Nat
    | [] => []
    | t :: ts => t.orderKey ++ termOrderKeys ts
  termination_by ts => sizeOf ts

  private def regOrderKey : Reg → List Nat
    | .real r b e => [0, r + 1, b + 1, e + 1]
    | .stack b e => [1, b + 1, e + 1]
    | .map m key b e => [2, m + 1, b + 1, e + 1] ++ termOrderKeys key ++ [0]
    | .packet b e => [3, b + 1, e + 1]
    | .context j b e => [4, contextCode j + 1, b + 1, e + 1]
  termination_by r => sizeOf r

  private def contextCode : ContextField → Nat
    | .data => 0
    | .dataEnd => 1
    | .dataMeta => 2
    | .ingressIfindex => 3
    | .rxQueueIndex => 4
    | .egressIfindex => 5
    | .ctx => 6
    | .sp => 7
    | .packetBytes => 8
    | .imageBase => 9
    | .helper => 10
    | .wrapperReturn => 11
    | .lddw slot => (12 <<< 32) + slot
    | .mapKeyBytes id => (13 <<< 32) + id
    | .mapValueBytes id => (14 <<< 32) + id
end

def Term.rawLE (a b : Term) : Bool := (compare a.orderKey b.orderKey).isLE

def termZero : Term → Bool
  | .const _ 0 => true
  | _ => false

private def termOne : Term → Bool
  | .const _ 1 => true
  | _ => false

/-- The only descent is through algebraic heads specified by R2 through R6. -/
def additiveSpine (w : Width) (t : Term) : List Term × Nat :=
  match t with
  | .const _ c => ([], c)
  | .app _ (.add _) [a, b] =>
    let x := additiveSpine w a
    let y := additiveSpine w b
    (x.1 ++ y.1, x.2 + y.2)
  | .app _ (.sub _) [a, b] =>
    if a == b then ([], 0) else
    match b with
    | .const _ c =>
      let x := additiveSpine w a
      (x.1, x.2 + NEG w c)
    | _ => ([t], 0)
  | .app _ (.xor q) [a, b] =>
    if a == b then ([], 0)
    else if q == w.bits && termZero b then additiveSpine w a
    else ([t], 0)
  | .app _ (.or q) [a, b] =>
    if q == w.bits && termZero b then additiveSpine w a else ([t], 0)
  | .app _ (.and q) [a, .const _ c] =>
    if q == w.bits && c == w.mask then additiveSpine w a else ([t], 0)
  | .app _ (.mullo _) [a, b] =>
    if termOne b then additiveSpine w a else ([t], 0)
  | .app _ (.shl _) [a, b] | .app _ (.lshr _) [a, b] | .app _ (.ashr _) [a, b] =>
    if termZero b then additiveSpine w a else ([t], 0)
  | _ => ([t], 0)
termination_by sizeOf t

def rebuildSpine (w : Width) (atoms : List Term) (constant : Nat) : Term :=
  let c := MNat w.bits constant
  match atoms with
  | [] => .const w c
  | a :: rest =>
    let sum := rest.foldl (fun lhs rhs => .app w (.add w) [lhs, rhs]) a
    if c == 0 then sum else .app w (.add w) [sum, .const w c]

def normalizeAlgebra (t : Term) : Term :=
  let spine := additiveSpine t.width t
  rebuildSpine t.width (spine.1.mergeSort Term.rawLE) spine.2

def foldClosed (t : Term) : Term :=
  if FV.isEmpty t then
    match eval t with
    | some c => .const t.width (MNat t.width.bits c)
    | none => t
  else t

/-- Trailing zeros of `n`. Zero reports none. -/
def ctz : Nat → Nat
  | 0 => 0
  | n + 1 => if (n + 1) % 2 = 0 then ctz ((n + 1) / 2) + 1 else 0
termination_by n => n
decreasing_by
  simp_wf
  exact Nat.div_lt_self (Nat.succ_pos n) (by decide)

/-- Bits needed to hold `n`. Zero uses none. -/
def bitLen (n : Nat) : Nat :=
  if n == 0 then 0 else Nat.log2 n + 1

/-- Shift amount when `c = 2^k`, otherwise none. `1` yields `some 0`. -/
def natPow2Shift? (c : Nat) : Option Nat :=
  if c != 0 && c &&& (c - 1) == 0 then some (Nat.log2 c) else none

/-- Inclusive-exclusive bit interval. `lo ≥ hi` means the only value is zero. -/
structure BitSpan where
  lo : Nat
  hi : Nat
  deriving DecidableEq, Repr

namespace BitSpan

def empty : BitSpan := ⟨0, 0⟩

def isEmpty (s : BitSpan) : Bool := decide (s.lo ≥ s.hi)

def disjoint (a b : BitSpan) : Bool :=
  a.isEmpty || b.isEmpty || a.hi ≤ b.lo || b.hi ≤ a.lo

def join (a b : BitSpan) : Option BitSpan :=
  if a.isEmpty then some b
  else if b.isEmpty then some a
  else if a.hi ≤ b.lo then some ⟨a.lo, b.hi⟩
  else if b.hi ≤ a.lo then some ⟨b.lo, a.hi⟩
  else none

end BitSpan

/-- Static bound on the bits a term can occupy. Unknown terms yield none. -/
def bitRange (w : Width) (t : Term) : Option BitSpan :=
  match t with
  | .const _ c =>
    some (if c == 0 then .empty else ⟨ctz c, bitLen c⟩)
  | .app tw op args =>
    if tw != w then none else
    match op, args with
    | .and q, [_, .const _ m] | .and q, [.const _ m, _] =>
      if q == 0 || w.bits < q then none else
        let m := m &&& ((1 <<< q) - 1)
        some (if m == 0 then .empty else ⟨ctz m, bitLen m⟩)
    | .zext q _ _, [_] =>
      if 0 < q && q ≤ w.bits then some ⟨0, q⟩ else none
    | .low q _, [_] =>
      if 0 < q && q ≤ w.bits then some ⟨0, q⟩ else none
    | .extract 0 ℓ _, [_] =>
      if 0 < ℓ && ℓ ≤ w.bits then some ⟨0, ℓ⟩ else none
    | .id _, [a] => bitRange w a
    | .mullo _, [a, .const _ c] | .mullo _, [.const _ c, a] =>
      match natPow2Shift? c with
      | some k =>
        match bitRange w a with
        | some s =>
          if s.isEmpty then some .empty
          else if s.hi + k ≤ w.bits then some ⟨s.lo + k, s.hi + k⟩ else none
        | none => none
      | none => none
    | .add _, [a, b] =>
      match bitRange w a, bitRange w b with
      | some sa, some sb => BitSpan.join sa sb
      | _, _ => none
    | .udiv _ z, [a, .const _ c] =>
      if z != 0 then none else
      match natPow2Shift? c with
      | some k =>
        if w.bits ≤ k then none else
        match bitRange w a with
        | some s =>
          some (if s.isEmpty || s.hi ≤ k then .empty else
            ⟨if s.lo ≤ k then 0 else s.lo - k, s.hi - k⟩)
        | none => some ⟨0, w.bits - k⟩
      | none => none
    | _, _ => none
  | _ => none
termination_by sizeOf t

/-- One bottom-up step. Concrete shifts become products or quotients; bitwise
or becomes addition only when the two sides occupy disjoint bits. -/
def rewriteHead (w : Width) (op : Op) (args : List Term) : Term :=
  match op, args with
  | .shl _, [.const wa av, .const wc k] =>
    if wa == w && wc == w then .const w (SHL w av k) else .app w op args
  | .shl _, [a, .const wc k] =>
    if wc == w && a.width == w then
      if k % w.bits == 0 then a
      else .app w (.mullo w) [a, .const w (1 <<< (k % w.bits))]
    else .app w op args
  | .lshr _, [.const wa av, .const wc k] =>
    if wa == w && wc == w then .const w (LSHR w av k) else .app w op args
  | .lshr _, [a, .const wc k] =>
    if wc == w && a.width == w then
      if k % w.bits == 0 then a
      else .app w (.udiv w 0) [a, .const w (1 <<< (k % w.bits))]
    else .app w op args
  | .or q, [a, b] =>
    if q == w.bits && termZero a && a.width == w && b.width == w then b
    else if q == w.bits && termZero b && a.width == w && b.width == w then a
    else
      match a, b with
      | .const wa av, .const wb bv =>
        if wa == w && wb == w && 0 < q && q ≤ w.bits then
          .const w (MNat w.bits (OR q av bv))
        else .app w op args
      | _, _ =>
        match bitRange w a, bitRange w b with
        | some sa, some sb =>
          if 0 < q && q ≤ w.bits && sa.hi ≤ q && sb.hi ≤ q && sa.disjoint sb then
            .app w (.add w) [a, b]
          else .app w op args
        | _, _ => .app w op args
  | _, _ => .app w op args

/-- DnD's integer-domain conversion, restricted to rewrites that preserve `2^w`. -/
def liftInteger : Term → Term
  | .const w c => .const w c
  | .var w n => .var w n
  | .regVar r => .regVar r
  | .app w op args => rewriteHead w op (args.map liftInteger)
termination_by t => sizeOf t

/-- R1 folds a closed root. Open trees are rewritten on bit idioms, then only
along the permitted algebraic spine. -/
def solve (t : Term) : Term :=
  if t.wellFormed then
    let folded := foldClosed t
    foldClosed (normalizeAlgebra (liftInteger folded))
  else t

private def SpineAtom (w : Width) (a : Term) : Prop :=
  a.wellFormed = true ∧ a.width = w ∧ additiveSpine w a = ([a], 0)

private theorem additiveSpine_atoms (w : Width) (t : Term) :
    t.wellFormed = true → t.width = w →
      ∀ a ∈ (additiveSpine w t).1, SpineAtom w a := by
  fun_induction additiveSpine w t <;>
    simp_all [SpineAtom, Term.wellFormed, termsWellFormed, Op.validSignature,
      Term.width, termZero, termOne, List.mem_append, additiveSpine]
  case case2 wo wi lhs rhs x y ihl ihr =>
    intro hwi hl hr hfl hfr hw atom hm
    rcases hm with hm | hm
    · exact ihl hfl (hl.trans hw) atom hm
    · exact ihr hfr (hr.trans hw) atom hm
  case case4 wo wi lhs wc c x hne ih =>
    intro hwi hl hc hfl hbound hw atom hm
    exact ih hfl (hl.trans hw) atom hm
  case case8 wo q lhs rhs hne hz =>
    intro hpos hbound hl hr hfl hfr hw
    simpa only [hw] using hbound
  case case10 wo q lhs rhs hz =>
    intro hpos hbound hl hr hfl hfr hw
    simpa only [hw] using hbound
  case case12 wo q lhs wc c hz =>
    intro hpos hbound hl hc hfl hcBound hw
    exact ⟨by simpa only [hw] using hbound, by simpa only [hw] using hcBound⟩

private theorem rawLE_trans (a b c : Term)
    (hab : a.rawLE b) (hbc : b.rawLE c) : a.rawLE c :=
  Std.TransOrd.isLE_trans hab hbc

private theorem rawLE_total (a b : Term) : a.rawLE b || b.rawLE a := by
  have hs := Std.OrientedOrd.eq_swap (a := a.orderKey) (b := b.orderKey)
  cases h : compare a.orderKey b.orderKey <;>
    cases h' : compare b.orderKey a.orderKey <;> simp_all [Term.rawLE]

private theorem spine_foldl (w : Width) (atoms : List Term) (acc : Term)
    (ha : ∀ a ∈ atoms, additiveSpine w a = ([a], 0)) :
    additiveSpine w (atoms.foldl (fun lhs rhs => .app w (.add w) [lhs, rhs]) acc) =
      ((additiveSpine w acc).1 ++ atoms, (additiveSpine w acc).2) := by
  induction atoms generalizing acc with
  | nil => simp
  | cons a atoms ih =>
    rw [List.foldl_cons, ih _ (fun x hx => ha x (by simp [hx]))]
    simp [additiveSpine, ha a (by simp), List.append_assoc]

private theorem add_foldl_valid (w : Width) (atoms : List Term) (acc : Term)
    (hw : acc.wellFormed = true) (hc : acc.width = w)
    (ha : ∀ a ∈ atoms, a.wellFormed = true ∧ a.width = w) :
    (atoms.foldl (fun lhs rhs => .app w (.add w) [lhs, rhs]) acc).wellFormed = true ∧
      (atoms.foldl (fun lhs rhs => .app w (.add w) [lhs, rhs]) acc).width = w := by
  induction atoms generalizing acc with
  | nil => exact ⟨hw, hc⟩
  | cons a atoms ih =>
    have h := ha a (by simp)
    apply ih
    · simp [Term.wellFormed, termsWellFormed, Op.validSignature, hw, hc, h.1, h.2]
    · rfl
    · intro x hx
      exact ha x (by simp [hx])

private theorem rebuildSpine_spec (w : Width) (atoms : List Term) (c : Nat)
    (ha : ∀ a ∈ atoms, SpineAtom w a) :
    (rebuildSpine w atoms c).wellFormed = true ∧
      (rebuildSpine w atoms c).width = w ∧
      additiveSpine w (rebuildSpine w atoms c) = (atoms, MNat w.bits c) := by
  cases atoms with
  | nil =>
    simp [rebuildSpine, Term.wellFormed, Term.width, additiveSpine, MNat_lt]
  | cons a atoms =>
    have hh := ha a (by simp)
    have ht : ∀ x ∈ atoms, SpineAtom w x := fun x hx => ha x (by simp [hx])
    have hv := add_foldl_valid w atoms a hh.1 hh.2.1
      (fun x hx => ⟨(ht x hx).1, (ht x hx).2.1⟩)
    have hs := spine_foldl w atoms a (fun x hx => (ht x hx).2.2)
    rw [hh.2.2] at hs
    simp only [List.singleton_append] at hs
    unfold rebuildSpine
    dsimp only
    split
    · rename_i hz
      have hz' : MNat w.bits c = 0 := eq_of_beq hz
      exact ⟨hv.1, hv.2, by simpa [hz'] using hs⟩
    · refine ⟨?_, rfl, ?_⟩
      · simp [Term.wellFormed, termsWellFormed, Op.validSignature, Term.width,
          hv.1, MNat_lt]
        simpa only [Term.width] using hv.2
      · simp [additiveSpine, hs]

theorem normalizeAlgebra_wellFormed (t : Term) (h : t.wellFormed = true) :
    (normalizeAlgebra t).wellFormed = true ∧ (normalizeAlgebra t).width = t.width := by
  have ha := additiveSpine_atoms t.width t h rfl
  obtain ⟨hv, hw, _⟩ := rebuildSpine_spec t.width
    ((additiveSpine t.width t).1.mergeSort Term.rawLE)
    (additiveSpine t.width t).2 (fun a hm => ha a (List.mem_mergeSort.mp hm))
  exact ⟨hv, hw⟩

theorem normalizeAlgebra_idempotent (t : Term) (h : t.wellFormed = true) :
    normalizeAlgebra (normalizeAlgebra t) = normalizeAlgebra t := by
  have ha := additiveSpine_atoms t.width t h rfl
  have hs := rebuildSpine_spec t.width
    ((additiveSpine t.width t).1.mergeSort Term.rawLE)
    (additiveSpine t.width t).2 (fun a hm => ha a (List.mem_mergeSort.mp hm))
  have hsort := List.mergeSort_of_pairwise
    (List.pairwise_mergeSort rawLE_trans rawLE_total (additiveSpine t.width t).1)
  unfold normalizeAlgebra at *
  rw [hs.2.1, hs.2.2]
  dsimp only
  rw [hsort]
  simp only [rebuildSpine, MNat_idempotent]

@[simp] theorem foldClosed_width (t : Term) : (foldClosed t).width = t.width := by
  unfold foldClosed
  split
  · split <;> rfl
  · rfl

theorem foldClosed_wellFormed (t : Term) (h : t.wellFormed = true) :
    (foldClosed t).wellFormed = true := by
  unfold foldClosed
  split
  · split
    · simp [Term.wellFormed, MNat_lt]
    · exact h
  · exact h

@[simp] theorem foldClosed_idempotent (t : Term) :
    foldClosed (foldClosed t) = foldClosed t := by
  unfold foldClosed
  split
  · split
    · simp [FV.isEmpty, FV, eval, Term.width, MNat_lt]
    · simp_all
  · rfl

private theorem normalizeAlgebra_const (w : Width) (c : Nat) :
    normalizeAlgebra (.const w c) = .const w (MNat w.bits c) := by
  simp [normalizeAlgebra, additiveSpine, rebuildSpine, Term.width]

private theorem foldClosed_algebra_fixed (t : Term)
    (h : normalizeAlgebra t = t) :
    normalizeAlgebra (foldClosed t) = foldClosed t := by
  unfold foldClosed
  split
  · split
    · simp [normalizeAlgebra_const, MNat_idempotent]
    · exact h
  · exact h

theorem rewriteHead_width (w : Width) (op : Op) (args : List Term) :
    (rewriteHead w op args).width = w := by
  unfold rewriteHead
  repeat (any_goals split)
  all_goals simp_all [Term.width, Bool.and_eq_true, beq_iff_eq]

theorem liftInteger_width (t : Term) : (liftInteger t).width = t.width := by
  cases t with
  | const _ _ | var _ _ | regVar _ => simp [liftInteger]
  | app w op args =>
    simp only [liftInteger]
    exact rewriteHead_width w op (args.map liftInteger)

private theorem terms_member_wf (args : List Term) (a : Term)
    (ha : a ∈ args) (h : termsWellFormed args = true) : a.wellFormed = true := by
  induction args with
  | nil => cases ha
  | cons b args ih =>
    simp only [termsWellFormed, Bool.and_eq_true] at h
    cases ha with
    | head => exact h.1
    | tail _ ht => exact ih ht h.2

private theorem terms_map_wf (args : List Term)
    (h : ∀ a ∈ args, (liftInteger a).wellFormed = true) :
    termsWellFormed (args.map liftInteger) = true := by
  induction args with
  | nil => simp [termsWellFormed]
  | cons a args ih =>
    simp [termsWellFormed, h a (by simp), ih (fun x hx => h x (by simp [hx]))]

theorem rewriteHead_wellFormed (w : Width) (op : Op) (args : List Term)
    (hs : op.validSignature w (args.map Term.width) = true)
    (hf : termsWellFormed args = true) :
    (rewriteHead w op args).wellFormed = true := by
  unfold rewriteHead
  repeat (any_goals split)
  all_goals try simp_all [Term.wellFormed, termsWellFormed, Op.validSignature,
    Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, SHL_lt, LSHR_lt, MNat_lt]
  all_goals
    first
    | (refine ⟨rfl, ?_⟩; simpa [kShift] using shift_pow_lt _ _)
    | (apply Nat.lt_of_lt_of_le (OR_lt _ _ _); apply Nat.pow_le_pow_right (by decide); omega)
    | exact MNat_lt _ _
    | done

theorem liftInteger_wellFormed (t : Term) (h : t.wellFormed = true) :
    (liftInteger t).wellFormed = true := by
  match t with
  | .const .. => simpa [liftInteger] using h
  | .var .. => simp [liftInteger, Term.wellFormed]
  | .regVar .. => simpa [liftInteger] using h
  | .app w op args =>
    have hs : op.validSignature w (args.map Term.width) = true ∧
        termsWellFormed args = true := by
      simpa [Term.wellFormed, Bool.and_eq_true] using h
    simp only [liftInteger]
    refine rewriteHead_wellFormed w op (args.map liftInteger) ?_ ?_
    · have hw : (args.map liftInteger).map Term.width = args.map Term.width := by
        induction args with
        | nil => rfl
        | cons a as ih => simp [liftInteger_width]
      simpa [hw] using hs.1
    · exact terms_map_wf args (fun a ha =>
        liftInteger_wellFormed a (terms_member_wf args a ha hs.2))
termination_by sizeOf t

private theorem mem_foldl_FV (args : List Term) (acc : List Var) (v : Var)
    (h : v ∈ args.foldl (fun acc t => acc ++ FV t) acc) :
    v ∈ acc ∨ ∃ a ∈ args, v ∈ FV a := by
  induction args generalizing acc with
  | nil => exact Or.inl h
  | cons a args ih =>
    rw [List.foldl_cons] at h
    rcases ih (acc ++ FV a) h with h | ⟨b, hb, hv⟩
    · rw [List.mem_append] at h
      rcases h with h | h
      · exact Or.inl h
      · exact Or.inr ⟨a, by simp, h⟩
    · exact Or.inr ⟨b, by simp [hb], hv⟩

private theorem mem_acc_FV (args : List Term) (acc : List Var) (v : Var)
    (h : v ∈ acc) : v ∈ args.foldl (fun acc t => acc ++ FV t) acc := by
  induction args generalizing acc with
  | nil => exact h
  | cons a args ih =>
    rw [List.foldl_cons]
    exact ih (acc ++ FV a) (by simp [h])

private theorem mem_FV_child (args : List Term) (acc : List Var) (b : Term) (v : Var)
    (hb : b ∈ args) (hv : v ∈ FV b) :
    v ∈ args.foldl (fun acc t => acc ++ FV t) acc := by
  induction args generalizing acc with
  | nil => cases hb
  | cons hd rest ih =>
    rw [List.foldl_cons]
    rcases (List.mem_cons).mp hb with rfl | hb
    · exact mem_acc_FV rest (acc ++ FV b) v (by simp [hv])
    · exact ih _ hb

theorem rewriteHead_support (w : Width) (op : Op) (args : List Term) (v : Var)
    (h : v ∈ FV (rewriteHead w op args)) : ∃ a ∈ args, v ∈ FV a := by
  unfold rewriteHead at h
  repeat (any_goals split at h)
  all_goals try simp_all [FV]
  all_goals
    first
    | done
    | (obtain ⟨l, ⟨a, ha, rfl⟩, hv⟩ := ‹∃ l, (∃ a, a ∈ args ∧ FV a = l) ∧ v ∈ l›
       exact ⟨a, ha, hv⟩)

theorem liftInteger_support (t : Term) (v : Var) (h : v ∈ FV (liftInteger t)) : v ∈ FV t := by
  match t with
  | .const .. => simp [liftInteger, FV] at h
  | .var .. => simpa [liftInteger, FV] using h
  | .regVar .. => simpa [liftInteger, FV] using h
  | .app w op args =>
    simp only [liftInteger] at h
    obtain ⟨a, ha, hv⟩ := rewriteHead_support w op (args.map liftInteger) v h
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
    simpa [FV] using mem_FV_child args [] b v hb (liftInteger_support b v hv)
termination_by sizeOf t

private theorem bool_contra {b : Bool} (h1 : b = true) (h2 : b = false) : False := by
  cases h2
  cases h1

private theorem map_fixed (args : List Term) (h : ∀ a ∈ args, liftInteger a = a) :
    args.map liftInteger = args := by
  induction args with
  | nil => rfl
  | cons a args ih =>
    simp [h a (by simp), ih (fun x hx => h x (by simp [hx]))]

private theorem rewriteHead_fixed (w : Width) (op : Op) (args : List Term)
    (h : ∀ a ∈ args, liftInteger a = a) :
    liftInteger (rewriteHead w op args) = rewriteHead w op args := by
  cases op with
  | shl ow =>
    cases args with
    | nil => simp [rewriteHead, liftInteger]
    | cons a rest =>
      cases rest with
      | nil => simp [rewriteHead, liftInteger, h a (by simp)]
      | cons b rest2 =>
        cases rest2 with
        | cons _ _ => simp [rewriteHead, liftInteger, map_fixed _ h]
        | nil =>
          have ha : liftInteger a = a := h a (by simp)
          have hb : liftInteger b = b := h b (by simp)
          cases b with
          | const wc k =>
            cases a with
            | const wa av =>
              cases hf : (wa == w && wc == w) <;>
                simp [rewriteHead, hf, liftInteger, List.map_cons, List.map_nil]
            | var ww nn =>
              cases hf : (wc == w && (Term.var ww nn).width == w) <;>
                cases hs : ((k % w.bits) == 0) <;>
                  simp [rewriteHead, hf, hs, liftInteger, ha, hb, List.map_cons, List.map_nil]
            | regVar r =>
              cases hf : (wc == w && (Term.regVar r).width == w) <;>
                cases hs : ((k % w.bits) == 0) <;>
                  simp [rewriteHead, hf, hs, liftInteger, ha, hb, List.map_cons, List.map_nil]
            | app ww op as =>
              cases hf : (wc == w && (Term.app ww op as).width == w) <;>
                cases hs : ((k % w.bits) == 0) <;>
                  simp [rewriteHead, hf, hs, liftInteger, ha, hb, List.map_cons, List.map_nil]
          | var _ _ | regVar _ | app _ _ _ =>
            simp [rewriteHead, liftInteger, ha, hb, List.map_cons, List.map_nil]
  | lshr ow =>
    cases args with
    | nil => simp [rewriteHead, liftInteger]
    | cons a rest =>
      cases rest with
      | nil => simp [rewriteHead, liftInteger, h a (by simp)]
      | cons b rest2 =>
        cases rest2 with
        | cons _ _ => simp [rewriteHead, liftInteger, map_fixed _ h]
        | nil =>
          have ha : liftInteger a = a := h a (by simp)
          have hb : liftInteger b = b := h b (by simp)
          cases b with
          | const wc k =>
            cases a with
            | const wa av =>
              cases hf : (wa == w && wc == w) <;>
                simp [rewriteHead, hf, liftInteger, List.map_cons, List.map_nil]
            | var ww nn =>
              cases hf : (wc == w && (Term.var ww nn).width == w) <;>
                cases hs : ((k % w.bits) == 0) <;>
                  simp [rewriteHead, hf, hs, liftInteger, ha, hb, List.map_cons, List.map_nil]
            | regVar r =>
              cases hf : (wc == w && (Term.regVar r).width == w) <;>
                cases hs : ((k % w.bits) == 0) <;>
                  simp [rewriteHead, hf, hs, liftInteger, ha, hb, List.map_cons, List.map_nil]
            | app ww op as =>
              cases hf : (wc == w && (Term.app ww op as).width == w) <;>
                cases hs : ((k % w.bits) == 0) <;>
                  simp [rewriteHead, hf, hs, liftInteger, ha, hb, List.map_cons, List.map_nil]
          | var _ _ | regVar _ | app _ _ _ =>
            simp [rewriteHead, liftInteger, ha, hb, List.map_cons, List.map_nil]
  | or q =>
    cases args with
    | nil => simp [rewriteHead, liftInteger]
    | cons a rest =>
      cases rest with
      | nil => simp [rewriteHead, liftInteger, h a (by simp)]
      | cons b rest2 =>
        cases rest2 with
        | cons _ _ => simp [rewriteHead, liftInteger, map_fixed _ h]
        | nil =>
          have ha : liftInteger a = a := h a (by simp)
          have hb : liftInteger b = b := h b (by simp)
          simp only [rewriteHead]
          split
          · exact hb
          · rename_i hza
            split
            · exact ha
            · rename_i hzb
              split
              · split
                · simp [liftInteger]
                · rename_i hfold
                  simp only [liftInteger, ha, hb, List.map_cons, List.map_nil, rewriteHead,
                    if_neg hza, if_neg hzb, if_neg hfold]
              · rename_i _ _ xnot
                split
                · split
                  · simp only [liftInteger, rewriteHead, ha, hb, List.map_cons, List.map_nil]
                  · rename_i _ _ sa sb hra hrb hdisj
                    simp only [liftInteger, ha, hb, List.map_cons, List.map_nil, rewriteHead,
                      if_neg hza, if_neg hzb, hra, hrb, if_neg hdisj]
                · rename_i _ _ xrange
                  simp only [liftInteger, ha, hb, List.map_cons, List.map_nil, rewriteHead,
                    if_neg hza, if_neg hzb]
  | add w' => simp [rewriteHead, liftInteger, map_fixed args h]
  | sub w' => simp [rewriteHead, liftInteger, map_fixed args h]
  | mullo w' => simp [rewriteHead, liftInteger, map_fixed args h]
  | udiv w' _ => simp [rewriteHead, liftInteger, map_fixed args h]
  | urem w' => simp [rewriteHead, liftInteger, map_fixed args h]
  | sdiv w' _ => simp [rewriteHead, liftInteger, map_fixed args h]
  | srem w' => simp [rewriteHead, liftInteger, map_fixed args h]
  | mulh w' => simp [rewriteHead, liftInteger, map_fixed args h]
  | mulhu w' => simp [rewriteHead, liftInteger, map_fixed args h]
  | mulhsu w' => simp [rewriteHead, liftInteger, map_fixed args h]
  | selectEq w' => simp [rewriteHead, liftInteger, map_fixed args h]
  | neg w' => simp [rewriteHead, liftInteger, map_fixed args h]
  | id w' => simp [rewriteHead, liftInteger, map_fixed args h]
  | and _ => simp [rewriteHead, liftInteger, map_fixed args h]
  | xor _ => simp [rewriteHead, liftInteger, map_fixed args h]
  | ashr w' => simp [rewriteHead, liftInteger, map_fixed args h]
  | ltu w' => simp [rewriteHead, liftInteger, map_fixed args h]
  | lts w' => simp [rewriteHead, liftInteger, map_fixed args h]
  | low _ _ => simp [rewriteHead, liftInteger, map_fixed args h]
  | extract _ _ _ => simp [rewriteHead, liftInteger, map_fixed args h]
  | zext _ _ _ => simp [rewriteHead, liftInteger, map_fixed args h]
  | sext _ _ _ => simp [rewriteHead, liftInteger, map_fixed args h]
  | bswap _ _ => simp [rewriteHead, liftInteger, map_fixed args h]
  | externalResult _ => simp [rewriteHead, liftInteger, map_fixed args h]
  | inputByte _ => simp [rewriteHead, liftInteger, map_fixed args h]
  | mergeLow _ _ => simp [rewriteHead, liftInteger, map_fixed args h]
  | packetRead _ _ => simp [rewriteHead, liftInteger, map_fixed args h]

theorem liftInteger_idempotent (t : Term) : liftInteger (liftInteger t) = liftInteger t := by
  match t with
  | .const _ _ | .var _ _ | .regVar _ => simp [liftInteger]
  | .app w op args =>
    simp only [liftInteger]
    apply rewriteHead_fixed
    intro a ha
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
    exact liftInteger_idempotent b
termination_by sizeOf t

mutual
private def termDepth : Term → Nat
  | .const _ _ | .var _ _ | .regVar _ => 0
  | .app _ _ args => termDepths args + 1
private def termDepths : List Term → Nat
  | [] => 0
  | a :: as => max (termDepth a) (termDepths as)
end

private theorem termDepth_mem (a : Term) (args : List Term) (h : a ∈ args) :
    termDepth a ≤ termDepths args := by
  induction args with
  | nil => cases h
  | cons b bs ih =>
    rcases List.mem_cons.mp h with rfl | h
    · exact Nat.le_max_left _ _
    · exact Nat.le_trans (ih h) (Nat.le_max_right _ _)

private theorem termDepths_map (args : List Term)
    (h : ∀ a ∈ args, termDepth (liftInteger a) ≤ termDepth a) :
    termDepths (args.map liftInteger) ≤ termDepths args := by
  induction args with
  | nil => simp [termDepths]
  | cons a as ih =>
    simp only [List.map_cons, termDepths]
    have h1 := h a (by simp)
    have h2 := ih (fun x hx => h x (by simp [hx]))
    omega

private theorem termDepth_rewrite (w : Width) (op : Op) (args : List Term) :
    termDepth (rewriteHead w op args) ≤ termDepth (.app w op args) := by
  unfold rewriteHead
  repeat (any_goals split)
  all_goals simp_all [termDepth, termDepths] <;> omega

private theorem termDepth_lift (t : Term) : termDepth (liftInteger t) ≤ termDepth t := by
  match t with
  | .const _ _ | .var _ _ | .regVar _ => simp [liftInteger, termDepth]
  | .app w op args =>
    simp only [liftInteger, termDepth]
    exact Nat.le_trans (termDepth_rewrite w op (args.map liftInteger))
      (Nat.succ_le_succ (termDepths_map args (fun a _ => termDepth_lift a)))
termination_by sizeOf t

private theorem termDepth_arg (w : Width) (op : Op) (args : List Term) (a : Term)
    (h : a ∈ args) : termDepth a < termDepth (.app w op args) := by
  simp only [termDepth]
  exact Nat.lt_succ_of_le (termDepth_mem a args h)

private theorem map_mem_fixed (args : List Term) (hmap : args.map liftInteger = args)
    (a : Term) (ha : a ∈ args) : liftInteger a = a := by
  induction args with
  | nil => cases ha
  | cons b bs ih =>
    simp only [List.map_cons, List.cons.injEq] at hmap
    rcases hmap with ⟨hb, hbs⟩
    rcases List.mem_cons.mp ha with rfl | ha
    · exact hb
    · exact ih hbs ha

private theorem child_result_absurd (w : Width) (op : Op) (args : List Term) (x : Term)
    (hx : x ∈ args.map liftInteger) (h : x = .app w op args) : False := by
  have hlt := termDepth_arg w op (args.map liftInteger) x hx
  rw [h] at hlt
  have hle := termDepths_map args (fun a _ => termDepth_lift a)
  simp only [termDepth] at hlt
  omega

private theorem app_children_fixed (w : Width) (op : Op) (args : List Term)
    (h : liftInteger (.app w op args) = .app w op args) (a : Term) (ha : a ∈ args) :
    liftInteger a = a := by
  simp only [liftInteger] at h
  cases op with
  | shl ow =>
    cases hmap : args.map liftInteger with
    | nil =>
      simp [rewriteHead, hmap] at h
      exact map_mem_fixed args (hmap.trans h.symm) a ha
    | cons x xs =>
      cases xs with
      | nil =>
        simp [rewriteHead, hmap] at h
        exact map_mem_fixed args (hmap.trans h) a ha
      | cons y ys =>
        cases ys with
        | cons z zs =>
          simp [rewriteHead, hmap] at h
          exact map_mem_fixed args (hmap.trans h) a ha
        | nil =>
          cases y with
          | const wc k =>
            cases x with
            | const wa av =>
              cases hf : (wa == w && wc == w) <;> simp [rewriteHead, hmap, hf] at h
              · exact map_mem_fixed args (hmap.trans h) a ha
            | var ww nn =>
              cases hf : (wc == w && (Term.var ww nn).width == w) <;>
                cases hs : ((k % w.bits) == 0) <;> simp [rewriteHead, hmap, hf, hs] at h
              · exact map_mem_fixed args (hmap.trans h) a ha
              · exact map_mem_fixed args (hmap.trans h) a ha
            | regVar r =>
              cases hf : (wc == w && (Term.regVar r).width == w) <;>
                cases hs : ((k % w.bits) == 0) <;> simp [rewriteHead, hmap, hf, hs] at h
              · exact map_mem_fixed args (hmap.trans h) a ha
              · exact map_mem_fixed args (hmap.trans h) a ha
            | app ww oop as =>
              cases hf : (wc == w && (Term.app ww oop as).width == w)
              · cases hs : ((k % w.bits) == 0) <;> simp [rewriteHead, hmap, hf] at h
                · exact map_mem_fixed args (hmap.trans h) a ha
                · exact map_mem_fixed args (hmap.trans h) a ha
              · cases hs : ((k % w.bits) == 0)
                · rw [hmap] at h
                  simp only [rewriteHead, hf, hs] at h
                  cases h
                · rw [hmap] at h
                  simp only [rewriteHead, hf, hs] at h
                  exact (child_result_absurd w (.shl ow) args
                    (.app ww oop as) (by simp [hmap]) h).elim
          | var _ _ | regVar _ | app _ _ _ =>
            simp [rewriteHead, hmap] at h
            exact map_mem_fixed args (hmap.trans h) a ha
  | lshr ow =>
    cases hmap : args.map liftInteger with
    | nil =>
      simp [rewriteHead, hmap] at h
      exact map_mem_fixed args (hmap.trans h.symm) a ha
    | cons x xs =>
      cases xs with
      | nil =>
        simp [rewriteHead, hmap] at h
        exact map_mem_fixed args (hmap.trans h) a ha
      | cons y ys =>
        cases ys with
        | cons z zs =>
          simp [rewriteHead, hmap] at h
          exact map_mem_fixed args (hmap.trans h) a ha
        | nil =>
          cases y with
          | const wc k =>
            cases x with
            | const wa av =>
              cases hf : (wa == w && wc == w) <;> simp [rewriteHead, hmap, hf] at h
              · exact map_mem_fixed args (hmap.trans h) a ha
            | var ww nn =>
              cases hf : (wc == w && (Term.var ww nn).width == w) <;>
                cases hs : ((k % w.bits) == 0) <;> simp [rewriteHead, hmap, hf, hs] at h
              · exact map_mem_fixed args (hmap.trans h) a ha
              · exact map_mem_fixed args (hmap.trans h) a ha
            | regVar r =>
              cases hf : (wc == w && (Term.regVar r).width == w) <;>
                cases hs : ((k % w.bits) == 0) <;> simp [rewriteHead, hmap, hf, hs] at h
              · exact map_mem_fixed args (hmap.trans h) a ha
              · exact map_mem_fixed args (hmap.trans h) a ha
            | app ww oop as =>
              cases hf : (wc == w && (Term.app ww oop as).width == w)
              · cases hs : ((k % w.bits) == 0) <;> simp [rewriteHead, hmap, hf] at h
                · exact map_mem_fixed args (hmap.trans h) a ha
                · exact map_mem_fixed args (hmap.trans h) a ha
              · cases hs : ((k % w.bits) == 0)
                · rw [hmap] at h
                  simp only [rewriteHead, hf, hs] at h
                  cases h
                · rw [hmap] at h
                  simp only [rewriteHead, hf, hs] at h
                  exact (child_result_absurd w (.lshr ow) args
                    (.app ww oop as) (by simp [hmap]) h).elim
          | var _ _ | regVar _ | app _ _ _ =>
            simp [rewriteHead, hmap] at h
            exact map_mem_fixed args (hmap.trans h) a ha
  | or q =>
    cases hmap : args.map liftInteger with
    | nil =>
      simp [rewriteHead, hmap] at h
      exact map_mem_fixed args (hmap.trans h.symm) a ha
    | cons x xs =>
      cases xs with
      | nil =>
        simp [rewriteHead, hmap] at h
        exact map_mem_fixed args (hmap.trans h) a ha
      | cons y ys =>
        cases ys with
        | cons z zs =>
          simp [rewriteHead, hmap] at h
          exact map_mem_fixed args (hmap.trans h) a ha
        | nil =>
          rw [hmap] at h
          simp only [rewriteHead] at h
          split at h
          · exact (child_result_absurd w (.or q) args y (by simp [hmap]) h).elim
          · split at h
            · exact (child_result_absurd w (.or q) args x (by simp [hmap]) h).elim
            · split at h
              · split at h
                · cases h
                · injection h with _ _ heq
                  exact map_mem_fixed args (hmap.trans heq) a ha
              · split at h
                · split at h
                  · cases h
                  · injection h with _ _ heq
                    exact map_mem_fixed args (hmap.trans heq) a ha
                · injection h with _ _ heq
                  exact map_mem_fixed args (hmap.trans heq) a ha
  | add _ | sub _ | mullo _ | udiv _ _ | urem _ | sdiv _ _ | srem _ | mulh _ | mulhu _
    | mulhsu _ | selectEq _ | neg _ | id _ | and _ | xor _ | ashr _ | ltu _ | lts _
    | low _ _ | extract _ _ _ | zext _ _ _ | sext _ _ _ | bswap _ _ | externalResult _
    | inputByte _ | mergeLow _ _ | packetRead _ _ =>
    simp only [rewriteHead] at h
    injection h with _ _ heq
    exact map_mem_fixed args heq a ha

private theorem spine_atoms_fixed (w : Width) (t : Term) (h : liftInteger t = t) :
    ∀ a ∈ (additiveSpine w t).1, liftInteger a = a := by
  fun_induction additiveSpine w t
  case case2 wo wi lhs rhs _ _ ihl ihr =>
    intro a ha
    simp only [List.mem_append] at ha
    rcases ha with ha | ha
    · exact ihl (app_children_fixed wo (.add wi) [lhs, rhs] h lhs (by simp)) a ha
    · exact ihr (app_children_fixed wo (.add wi) [lhs, rhs] h rhs (by simp)) a ha
  case case4 wo wi lhs wc c _ hne ih =>
    exact ih (app_children_fixed wo (.sub wi) [lhs, .const wc c] h lhs (by simp))
  case case7 wo q lhs rhs hne hz ih =>
    exact ih (app_children_fixed wo (.xor q) [lhs, rhs] h lhs (by simp))
  case case9 wo q lhs rhs hz ih =>
    exact ih (app_children_fixed wo (.or q) [lhs, rhs] h lhs (by simp))
  case case11 wo q lhs wc c hz ih =>
    exact ih (app_children_fixed wo (.and q) [lhs, .const wc c] h lhs (by simp))
  case case13 wo wi lhs rhs hone ih =>
    exact ih (app_children_fixed wo (.mullo wi) [lhs, rhs] h lhs (by simp))
  case case15 wo wi lhs rhs hz ih =>
    exact ih (app_children_fixed wo (.shl wi) [lhs, rhs] h lhs (by simp))
  case case17 wo wi lhs rhs hz ih =>
    exact ih (app_children_fixed wo (.lshr wi) [lhs, rhs] h lhs (by simp))
  case case19 wo wi lhs rhs hz ih =>
    exact ih (app_children_fixed wo (.ashr wi) [lhs, rhs] h lhs (by simp))
  all_goals simp_all

private theorem foldl_add_fixed (w : Width) (atoms : List Term) (acc : Term)
    (hacc : liftInteger acc = acc) (ha : ∀ a ∈ atoms, liftInteger a = a) :
    liftInteger (atoms.foldl (fun lhs rhs => .app w (.add w) [lhs, rhs]) acc) =
      atoms.foldl (fun lhs rhs => .app w (.add w) [lhs, rhs]) acc := by
  induction atoms generalizing acc with
  | nil => exact hacc
  | cons a as ih =>
    rw [List.foldl_cons]
    exact ih (.app w (.add w) [acc, a])
      (by simp only [liftInteger, rewriteHead, List.map_cons, List.map_nil, hacc,
        ha a (by simp)])
      (fun x hx => ha x (by simp [hx]))

private theorem rebuild_fixed (w : Width) (atoms : List Term) (c : Nat)
    (ha : ∀ a ∈ atoms, liftInteger a = a) :
    liftInteger (rebuildSpine w atoms c) = rebuildSpine w atoms c := by
  cases atoms with
  | nil => simp [rebuildSpine, liftInteger]
  | cons a as =>
    have hsum := foldl_add_fixed w as a (ha a (by simp)) (fun x hx => ha x (by simp [hx]))
    simp only [rebuildSpine]
    split
    · exact hsum
    · simp only [liftInteger, rewriteHead, List.map_cons, List.map_nil, hsum, liftInteger]

private theorem liftInteger_normalize (t : Term) (h : liftInteger t = t) :
    liftInteger (normalizeAlgebra t) = normalizeAlgebra t := by
  unfold normalizeAlgebra
  refine rebuild_fixed t.width _ _ ?_
  intro a hm
  exact spine_atoms_fixed t.width t h a (List.mem_mergeSort.mp hm)

private theorem liftInteger_fold (t : Term) (h : liftInteger t = t) :
    liftInteger (foldClosed t) = foldClosed t := by
  unfold foldClosed
  split
  · split
    · simp [liftInteger]
    · exact h
  · exact h

/-- Solving twice has the same result as solving once for every raw term. -/
theorem solve_idempotent (t : Term) : solve (solve t) = solve t := by
  by_cases h : t.wellFormed = true
  · simp [solve, h]
    let v := liftInteger (foldClosed t)
    have hv : liftInteger v = v := liftInteger_idempotent _
    have hl : v.wellFormed = true :=
      liftInteger_wellFormed _ (foldClosed_wellFormed t h)
    have hn := liftInteger_normalize v hv
    have hfold := liftInteger_fold (normalizeAlgebra v) hn
    have hs : (foldClosed (normalizeAlgebra v)).wellFormed = true :=
      foldClosed_wellFormed _ (normalizeAlgebra_wellFormed v hl).1
    have halg := foldClosed_algebra_fixed (normalizeAlgebra v)
      (normalizeAlgebra_idempotent v hl)
    intro _
    rw [hfold, halg, foldClosed_idempotent]
  · simp [solve, h]

theorem solve_width (t : Term) : (solve t).width = t.width := by
  unfold solve
  split
  · rename_i h
    rw [foldClosed_width,
      (normalizeAlgebra_wellFormed _ (liftInteger_wellFormed _ (foldClosed_wellFormed t h))).2,
      liftInteger_width, foldClosed_width]
  · rfl

/-- \(f^\star(t_1,\ldots,t_n)=\operatorname{solve}_w(f(t_1,\ldots,t_n))\). -/
def star (w : Width) (op : Op) (args : List Term) : Term :=
  solve (.app w op args)

def addStar (w : Width) (t1 t2 : Term) : Term := star w (Op.add w) [t1, t2]
def subStar (w : Width) (t1 t2 : Term) : Term := star w (Op.sub w) [t1, t2]
def mulloStar (w : Width) (t1 t2 : Term) : Term := star w (Op.mullo w) [t1, t2]
def andStar (q : Nat) (w : Width) (t1 t2 : Term) : Term := star w (Op.and q) [t1, t2]
def orStar (q : Nat) (w : Width) (t1 t2 : Term) : Term := star w (Op.or q) [t1, t2]
def xorStar (q : Nat) (w : Width) (t1 t2 : Term) : Term := star w (Op.xor q) [t1, t2]
def shlStar (w : Width) (t1 t2 : Term) : Term := star w (Op.shl w) [t1, t2]
def lshrStar (w : Width) (t1 t2 : Term) : Term := star w (Op.lshr w) [t1, t2]
def ashrStar (w : Width) (t1 t2 : Term) : Term := star w (Op.ashr w) [t1, t2]
def ltuStar (w : Width) (t1 t2 : Term) : Term := star w (Op.ltu w) [t1, t2]
def ltsStar (w : Width) (t1 t2 : Term) : Term := star w (Op.lts w) [t1, t2]
def idStar (w : Width) (t : Term) : Term := star w (Op.id w) [t]
def negStar (w : Width) (t : Term) : Term := star w (Op.neg w) [t]
def zStar (q : Nat) (w : Width) (v : Nat) (t : Term) : Term := star w (Op.zext q w v) [t]
def sStar (q : Nat) (w : Width) (v : Nat) (t : Term) : Term := star w (Op.sext q w v) [t]

private theorem additiveSpine_support (w : Width) (t : Term) :
    ∀ a ∈ (additiveSpine w t).1, ∀ v ∈ FV a, v ∈ FV t := by
  fun_induction additiveSpine w t <;>
    simp_all [FV, List.foldl, List.mem_append]
  case case2 wo wi lhs rhs x y ihl ihr =>
    intro atom hm v hv
    rcases hm with hm | hm
    · exact Or.inl (ihl atom hm v hv)
    · exact Or.inr (ihr atom hm v hv)
  case case4 wo wi lhs wc c x hne ih =>
    exact ih
  case case7 wo q lhs rhs hne hz ih =>
    intro atom hm v hv
    exact Or.inl (ih atom hm v hv)
  case case9 wo q lhs rhs hz ih =>
    intro atom hm v hv
    exact Or.inl (ih atom hm v hv)
  case case11 wo q lhs wc c hz ih =>
    exact ih
  case case13 wo wi lhs rhs hz ih =>
    intro atom hm v hv
    exact Or.inl (ih atom hm v hv)
  case case15 wo wi lhs rhs hz ih =>
    intro atom hm v hv
    exact Or.inl (ih atom hm v hv)
  case case17 wo wi lhs rhs hz ih =>
    intro atom hm v hv
    exact Or.inl (ih atom hm v hv)
  case case19 wo wi lhs rhs hz ih =>
    intro atom hm v hv
    exact Or.inl (ih atom hm v hv)

private theorem add_foldl_support (w : Width) (atoms : List Term) (acc : Term) :
    ∀ v ∈ FV (atoms.foldl (fun lhs rhs => .app w (.add w) [lhs, rhs]) acc),
      v ∈ FV acc ∨ ∃ a ∈ atoms, v ∈ FV a := by
  induction atoms generalizing acc with
  | nil => simp
  | cons a atoms ih =>
    intro v hv
    obtain h | ⟨b, hb, hv⟩ := ih (.app w (.add w) [acc, a]) v hv
    · simp only [FV, List.foldl, List.nil_append, List.mem_append] at h
      rcases h with h | h
      · exact Or.inl h
      · exact Or.inr ⟨a, by simp, h⟩
    · exact Or.inr ⟨b, by simp [hb], hv⟩

theorem normalizeAlgebra_support (t : Term) (v : Var)
    (h : v ∈ FV (normalizeAlgebra t)) : v ∈ FV t := by
  let atoms := (additiveSpine t.width t).1.mergeSort Term.rawLE
  have ha : ∀ a ∈ atoms, ∀ x ∈ FV a, x ∈ FV t := by
    intro a hm x hx
    exact additiveSpine_support t.width t a (List.mem_mergeSort.mp hm) x hx
  change v ∈ FV (rebuildSpine t.width atoms (additiveSpine t.width t).2) at h
  cases hs : atoms with
  | nil => simp [hs, rebuildSpine, FV] at h
  | cons a rest =>
    have hv : v ∈ FV (rest.foldl (fun lhs rhs => .app t.width (.add t.width) [lhs, rhs]) a) := by
      unfold rebuildSpine at h
      rw [hs] at h
      dsimp only at h
      split at h
      · exact h
      · simpa [FV, List.foldl] using h
    obtain hv | ⟨b, hb, hv⟩ := add_foldl_support t.width rest a v hv
    · exact ha a (by rw [hs]; simp) v hv
    · exact ha b (by rw [hs]; simp [hb]) v hv

theorem foldClosed_support (t : Term) (v : Var)
    (h : v ∈ FV (foldClosed t)) : v ∈ FV t := by
  unfold foldClosed at h
  split at h
  · split at h
    · simp [FV] at h
    · exact h
  · exact h

theorem solve_support (t : Term) (v : Var) (h : v ∈ FV (solve t)) : v ∈ FV t := by
  unfold solve at h
  split at h
  · exact foldClosed_support t v
      (liftInteger_support _ v
        (normalizeAlgebra_support _ v
          (foldClosed_support _ v h)))
  · exact h

private theorem interpretWith_pure (θ : ExternalInterpretation) (w : Width)
    (op : Op) (args : List Nat) (v : Nat) (h : interpretOp op args = some v) :
    interpretWith θ w op args = some v := by
  cases op <;> simp_all [interpretOp, interpretWith]

mutual
  /-- A successful partial numeric evaluation agrees with every explicit completion. -/
  theorem eval_interpret (t : Term) (ν : Var → Nat) (θ : ExternalInterpretation)
      (v : Nat) (h : eval t = some v) : interpretTerm ν θ t = some v := by
    cases t with
    | const w c => simpa only [eval, interpretTerm] using h
    | var w n => simp [eval] at h
    | regVar r => simp [eval] at h
    | app w op args =>
      cases hs : op.validSignature w (args.map Term.width) with
      | false => simp [eval, hs] at h
      | true =>
        cases ha : evalArgs args with
        | none => simp [eval, hs, ha] at h
        | some values =>
          cases ho : interpretOp op values with
          | none => simp [eval, hs, ha, ho] at h
          | some value =>
            have hv : MNat w.bits value = v := by
              simpa [eval, hs, ha, ho] using h
            simp [interpretTerm, hs, evalArgs_interpret args ν θ values ha,
              interpretWith_pure θ w op values value ho, hv]
  termination_by sizeOf t

  private theorem evalArgs_interpret (args : List Term) (ν : Var → Nat)
      (θ : ExternalInterpretation) (values : List Nat)
      (h : evalArgs args = some values) : interpretTerms ν θ args = some values := by
    cases args with
    | nil => simpa only [evalArgs, interpretTerms] using h
    | cons t ts =>
      cases ht : eval t with
      | none => simp [evalArgs, ht] at h
      | some v =>
        cases hs : evalArgs ts with
        | none => simp [evalArgs, ht, hs] at h
        | some vs =>
          simp only [evalArgs, ht, hs, Option.some.injEq] at h
          simpa [interpretTerms, eval_interpret t ν θ v ht,
            evalArgs_interpret ts ν θ vs hs] using congrArg some h
  termination_by sizeOf args
end

theorem eval_lt (t : Term) (v : Nat) (h : eval t = some v) : v < 2 ^ t.width.bits := by
  cases t with
  | const w c =>
    simp only [eval] at h
    split at h
    · simp_all [Term.width]
    · contradiction
  | var w n => simp [eval] at h
  | regVar r => simp [eval] at h
  | app w op args =>
    cases hs : op.validSignature w (args.map Term.width) with
    | false => simp [eval, hs] at h
    | true =>
      cases ha : evalArgs args with
      | none => simp [eval, hs, ha] at h
      | some values =>
        cases ho : interpretOp op values with
        | none => simp [eval, hs, ha, ho] at h
        | some value =>
          have hv : MNat w.bits value = v := by
            simpa [eval, hs, ha, ho] using h
          rw [← hv]
          exact MNat_lt w.bits value

theorem foldClosed_interpret (t : Term) (ν : Var → Nat) (θ : ExternalInterpretation) :
    interpretTerm ν θ (foldClosed t) = interpretTerm ν θ t := by
  unfold foldClosed
  split
  · split
    · rename_i value he
      rw [eval_interpret t ν θ value he, MNat_of_lt (eval_lt t value he)]
      simp [interpretTerm, eval_lt t value he]
    · rfl
  · rfl

end Term
