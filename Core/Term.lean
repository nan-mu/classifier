import Std.Tactic
import Init.Data.Order.Ord
import Core.NumericProofs
import Core.Bits
import Core.Op
import Core.Reg

namespace Core

inductive Term where
  | const (w : Width) (c : Nat)
  | var (w : Width) (ξ : Nat)
  /-- Value of a register at a fixed dynamic event, rather than a live register lookup. -/
  | regVar (event : Nat) (reg : Reg)
  | app (w : Width) (op : Op) (args : List Term)
  deriving Repr, Inhabited

mutual
  private def termDecEq : (a b : Term) → Decidable (a = b)
    | .const w c, .const v d => decidable_of_iff (w = v ∧ c = d) (by simp)
    | .var w n, .var v m => decidable_of_iff (w = v ∧ n = m) (by simp)
    | .regVar e r, .regVar f s => decidable_of_iff (e = f ∧ r = s) (by simp)
    | .app w f xs, .app v g ys =>
      letI := termListDecEq xs ys
      decidable_of_iff (w = v ∧ f = g ∧ xs = ys) (by simp)
    | .const _ _, .var _ _ | .const _ _, .regVar _ _ | .const _ _, .app _ _ _
    | .var _ _, .const _ _ | .var _ _, .regVar _ _ | .var _ _, .app _ _ _
    | .regVar _ _, .const _ _ | .regVar _ _, .var _ _ | .regVar _ _, .app _ _ _
    | .app _ _ _, .const _ _ | .app _ _ _, .var _ _ | .app _ _ _, .regVar _ _ =>
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

instance : DecidableEq Term := termDecEq
instance : BEq Term := ⟨fun a b => decide (a = b)⟩
instance : LawfulBEq Term where
  eq_of_beq := of_decide_eq_true
  rfl := of_decide_eq_self_eq_true _


def Term.width : Term → Width
  | .const w _ => w
  | .var w _ => w
  | .regVar _ r => r.width
  | .app w _ _ => w

def Term.C (w : Width) (c : Nat) : Term := .const w (MNat w.bits c)
def Term.C32 (c : Nat) : Term := .C .w32 c
def Term.C64 (c : Nat) : Term := .C .w64 c
def Term.V (w : Width) (ξ : Nat) : Term := .var w ξ
def Term.V32 (ξ : Nat) : Term := .V .w32 ξ
def Term.V64 (ξ : Nat) : Term := .V .w64 ξ

structure Var where
  width : Width
  name  : Nat
  register : Option (Nat × Reg) := none
  deriving DecidableEq, BEq, Repr

def FV : Term → List Var
  | .const _ _ => []
  | .var w ξ => [⟨w, ξ, none⟩]
  | .regVar event r => [⟨r.width, r.alpha, some (event, r)⟩]
  | .app _ _ args => args.foldl (fun acc t => acc ++ FV t) []

def FV.isEmpty (t : Term) : Bool := (FV t).isEmpty
mutual
  def Term.wellFormed : Term → Bool
    | .const w c => c < 2 ^ w.bits
    | .var _ _ => true
    | .regVar _ reg => reg.valid && reg.kind == .real
    | .app w op args => op.validSignature w (args.map Term.width) && termsWellFormed args
  termination_by t => sizeOf t

  def termsWellFormed : List Term → Bool
    | [] => true
    | t :: ts => t.wellFormed && termsWellFormed ts
  termination_by ts => sizeOf ts
end

/-- Only the two external operation families can be supplied by the environment. -/
structure ExternalInterpretation where
  externalResult : Width → Nat → Nat → List Nat → Option Nat
  inputByte : Nat → Nat → Nat → Option Nat

def ExternalInterpretation.Total (θ : ExternalInterpretation) : Prop :=
  (∀ w event lane args, ∃ v, θ.externalResult w event lane args = some v) ∧
  (∀ resource base address, ∃ v, θ.inputByte resource base address = some v)

def interpretWith (θ : ExternalInterpretation) (w : Width) (op : Op)
    (args : List Nat) : Option Nat :=
  match op, args with
  | .externalResult event lane, vs => θ.externalResult w event lane vs
  | .inputByte resource, [base, address] => θ.inputByte resource base address
  | _, _ => interpretOp op args

mutual
  def interpretTerm (ν : Var → Nat) (θ : ExternalInterpretation) : Term → Option Nat
    | .const w c => if c < 2 ^ w.bits then some c else none
    | .var w ξ => some (MNat w.bits (ν ⟨w, ξ, none⟩))
    | .regVar event r =>
      if r.valid && r.kind == .real then
        some (MNat r.width.bits (ν ⟨r.width, r.alpha, some (event, r)⟩))
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
    | .regVar _ _ => none
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

private def regKindCode : RegKind → Nat
  | .real => 0 | .stack => 1 | .map => 2 | .packet => 3 | .context => 4

mutual
  /-- Prefix encoding for the raw structural order. Zero delimits argument lists. -/
  def Term.orderKey : Term → List Nat
    | .const w c => [w.bits + 1, 1, c + 1]
    | .var w n => [w.bits + 1, 2, n + 1]
    | .regVar event r =>
      [r.width.bits + 1, 3, event + 1, regKindCode r.kind + 1, r.alpha + 1] ++
        (match r.compound with
        | none => [0]
        | some p => [1, p.κ, p.bytes, p.endCtx, if p.strict then 1 else 0,
            p.byteIndex, p.offset.orderKey.length] ++ p.offset.orderKey ++ p.checkedEnd.orderKey)
    | .app w op args =>
      [w.bits + 1, 4] ++ op.orderKey.map (· + 1) ++ [0] ++ termOrderKeys args ++ [0]
  termination_by t => sizeOf t

  private def termOrderKeys : List Term → List Nat
    | [] => []
    | t :: ts => t.orderKey ++ termOrderKeys ts
  termination_by ts => sizeOf ts
end

def Term.rawLE (a b : Term) : Bool := (compare a.orderKey b.orderKey).isLE

private def termZero : Term → Bool
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

/-- R1 is whole-term folding. Open trees are traversed only along the permitted spine. -/
def solve (t : Term) : Term :=
  if t.wellFormed then
    let folded := foldClosed t
    foldClosed (normalizeAlgebra folded)
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

/-- Solving twice has the same result as solving once for every raw term. -/
theorem solve_idempotent (t : Term) : solve (solve t) = solve t := by
  by_cases h : t.wellFormed = true
  · let n := normalizeAlgebra (foldClosed t)
    have hf := foldClosed_wellFormed t h
    have hn := (normalizeAlgebra_wellFormed _ hf).1
    have hfix := foldClosed_algebra_fixed n (normalizeAlgebra_idempotent _ hf)
    have hout := foldClosed_wellFormed n hn
    change solve (if t.wellFormed then foldClosed n else t) = _
    simp only [h, ↓reduceIte]
    unfold solve
    simp only [hout, ↓reduceIte, foldClosed_idempotent, hfix]
    simp only [h, ↓reduceIte]
    rfl
  · simp [solve, h]

theorem solve_width (t : Term) : (solve t).width = t.width := by
  unfold solve
  split
  · rename_i h
    rw [foldClosed_width, (normalizeAlgebra_wellFormed _ (foldClosed_wellFormed t h)).2,
      foldClosed_width]
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
  · exact foldClosed_support t v (normalizeAlgebra_support _ v (foldClosed_support _ v h))
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
    | regVar e r => simp [eval] at h
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
  | regVar e r => simp [eval] at h
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

end Core
