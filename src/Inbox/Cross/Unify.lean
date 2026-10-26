import Inbox.Cross.Pred
import Inbox.Wire.Parse

namespace Inbox.Cross
open Term Term.Value Expression Observation Inbox.Wire

/-! Injective renaming of prepared observations.

Real indices may change and must keep the interval. Other registers keep
their constructor, identity and interval. Variable names rename only when the
widths already match. Map-write and packet-write values are compared as
little-endian byte extracts. The match itself is index-aligned. -/

end Inbox.Cross

namespace Term

/-- Same constructor and interval. Real indices may differ. Map keys must match. -/
def Reg.renameable (a b : Reg) : Bool :=
  match a, b with
  | .real _ b e, .real _ c f => b == c && e == f
  | .stack b e, .stack c f => b == c && e == f
  | .packet b e, .packet c f => b == c && e == f
  | .context j b e, .context i c f => j == i && b == c && e == f
  | .map m k b e, .map n q c f => m == n && k == q && b == c && e == f
  | _, _ => false

end Term

namespace Inbox.Cross
open Term Term.Value Expression Observation Inbox.Wire

structure Subst where
  vars : List (Nat × Nat) := []
  regs : List (Reg × Reg) := []
  deriving DecidableEq, BEq, Repr

namespace Subst

def empty : Subst := ⟨[], []⟩

def varImage? (σ : Subst) (x : Nat) : Option Nat :=
  (σ.vars.find? (·.1 == x)).map (·.2)

def regImage? (σ : Subst) (r : Reg) : Option Reg :=
  (σ.regs.find? (·.1 == r)).map (·.2)

def varLookup (σ : Subst) (x : Nat) : Nat := (σ.varImage? x).getD x

def regLookup (σ : Subst) (r : Reg) : Reg :=
  (σ.regImage? r).getD r

def addVar? (σ : Subst) (x y : Nat) : Option Subst :=
  match σ.varImage? x with
  | some y₀ => if y₀ == y then some σ else none
  | none => if σ.vars.any (·.2 == y) then none
            else some ⟨(x, y) :: σ.vars, σ.regs⟩

def addReg? (σ : Subst) (a b : Reg) : Option Subst :=
  match σ.regImage? a with
  | some b₀ => if b₀ == b then some σ else none
  | none => if σ.regs.any (·.2 == b) then none
            else some ⟨σ.vars, (a, b) :: σ.regs⟩

def strip (σ : Subst) : Subst :=
  ⟨σ.vars.filter (fun e => e.1 != e.2),
   σ.regs.filter (fun e => e.1 != e.2)⟩

/-- Domain and codomain are duplicate-free for variables and for whole registers. -/
def Injective (σ : Subst) : Prop :=
  (σ.vars.map (·.1)).Nodup ∧ (σ.vars.map (·.2)).Nodup ∧
  (σ.regs.map (·.1)).Nodup ∧ (σ.regs.map (·.2)).Nodup

def Extends (σ σ' : Subst) : Prop :=
  (∀ e ∈ σ.vars, e ∈ σ'.vars) ∧ (∀ e ∈ σ.regs, e ∈ σ'.regs)

mutual
  def applyTerm (σ : Subst) : Term → Term
    | .const w c => .const w c
    | .var w n => .var w (σ.varLookup n)
    | .regVar r => .regVar (σ.regLookup r)
    | .app w op args => .app w op (applyTerms σ args)
  termination_by t => sizeOf t

  def applyTerms (σ : Subst) : List Term → List Term
    | [] => []
    | t :: ts => applyTerm σ t :: applyTerms σ ts
  termination_by ts => sizeOf ts
end

mutual
  def Determined (σ : Subst) : Term → Prop
    | .const _ _ => True
    | .var _ n => ∃ y, σ.varImage? n = some y
    | .regVar r => ∃ b, σ.regImage? r = some b
    | .app _ _ args => DeterminedTerms σ args
  termination_by t => sizeOf t

  def DeterminedTerms (σ : Subst) : List Term → Prop
    | [] => True
    | t :: ts => Determined σ t ∧ DeterminedTerms σ ts
  termination_by ts => sizeOf ts
end

mutual
  def mergeList (σ : Subst) : List Term → List Term → Option Subst
    | [], [] => some σ
    | a :: as, b :: bs =>
      match mergeTerm σ a b with
      | none => none
      | some σ' => mergeList σ' as bs
    | _, _ => none
  termination_by as bs => sizeOf as + sizeOf bs

  def mergeTerm (σ : Subst) : Term → Term → Option Subst
    | .const w a, .const v b =>
      if w == v then
        if a == b then some σ else none
      else none
    | .var w a, .var v b =>
      if w == v then addVar? σ a b else none
    | .regVar a, .regVar b =>
      if a.renameable b then addReg? σ a b else none
    | .app w f as, .app v g bs =>
      if w == v then
        if f == g then mergeList σ as bs else none
      else none
    | _, _ => none
  termination_by a b => sizeOf a + sizeOf b
end

private theorem find_key_of_mem {α κ : Type} [BEq κ] [LawfulBEq κ]
    (key : α → κ) {xs : List α} (hn : (xs.map key).Nodup)
    {e : α} (he : e ∈ xs) :
    xs.find? (fun d => key d == key e) = some e := by
  induction xs with
  | nil => simp at he
  | cons d ds ih =>
    simp only [List.map_cons, List.nodup_cons] at hn
    rcases List.mem_cons.mp he with rfl | he
    · simp
    · have hne : key d ≠ key e := by
        intro h
        exact hn.1 (h ▸ List.mem_map.mpr ⟨e, he, rfl⟩)
      simp only [List.find?_cons, beq_eq_false_iff_ne.mpr hne]
      exact ih hn.2 he

private theorem image_some_iff {α κ δ : Type} [BEq κ] [LawfulBEq κ]
    (key : α → κ) (value : α → δ) {xs : List α}
    (hn : (xs.map key).Nodup) (x : κ) (y : δ) :
    (xs.find? (fun e => key e == x)).map value = some y ↔
      ∃ e ∈ xs, key e = x ∧ value e = y := by
  constructor
  · intro h
    cases hf : xs.find? (fun e => key e == x) with
    | none => simp [hf] at h
    | some e =>
      exact ⟨e, List.mem_of_find?_eq_some hf,
        eq_of_beq (List.find?_some (p := fun d => key d == x) hf), by simpa [hf] using h⟩
  · rintro ⟨e, he, hk, hv⟩
    rw [← hk, find_key_of_mem key hn he]
    simp [hv]

theorem extends_refl (σ : Subst) : Extends σ σ :=
  ⟨fun _ h => h, fun _ h => h⟩

theorem extends_trans {σ τ υ : Subst} (h : Extends σ τ) (g : Extends τ υ) :
    Extends σ υ :=
  ⟨fun e he => g.1 e (h.1 e he), fun e he => g.2 e (h.2 e he)⟩

theorem empty_injective : Injective empty := by
  simp [Injective, empty]

theorem varImage_some_iff {σ : Subst} (h : Injective σ) (x y : Nat) :
    σ.varImage? x = some y ↔ (x, y) ∈ σ.vars := by
  rw [varImage?, image_some_iff (fun e : Nat × Nat => e.1) (fun e => e.2) h.1]
  constructor
  · rintro ⟨⟨a, b⟩, he, rfl, rfl⟩; exact he
  · intro he; exact ⟨(x, y), he, rfl, rfl⟩

theorem regImage_some_iff {σ : Subst} (h : Injective σ) (a b : Reg) :
    σ.regImage? a = some b ↔ (a, b) ∈ σ.regs := by
  rw [regImage?, image_some_iff (fun e : Reg × Reg => e.1) (fun e => e.2) h.2.2.1]
  constructor
  · rintro ⟨⟨x, y⟩, he, rfl, rfl⟩; exact he
  · intro he; exact ⟨(a, b), he, rfl, rfl⟩

theorem varImage_extends {σ τ : Subst} (he : Extends σ τ)
    (hi : Injective σ) (hj : Injective τ) {x y : Nat}
    (h : σ.varImage? x = some y) : τ.varImage? x = some y :=
  (varImage_some_iff hj x y).mpr (he.1 _ ((varImage_some_iff hi x y).mp h))

theorem regImage_extends {σ τ : Subst} (he : Extends σ τ)
    (hi : Injective σ) (hj : Injective τ) {a b : Reg}
    (h : σ.regImage? a = some b) : τ.regImage? a = some b :=
  (regImage_some_iff hj a b).mpr (he.2 _ ((regImage_some_iff hi a b).mp h))

theorem addVar_sound {σ τ : Subst} {x y : Nat} (hi : Injective σ)
    (h : addVar? σ x y = some τ) :
    Extends σ τ ∧ Injective τ ∧ τ.varImage? x = some y := by
  unfold addVar? at h
  split at h
  · split at h
    · have hτ : σ = τ := Option.some.inj h
      subst τ
      exact ⟨extends_refl σ, hi, by simp_all⟩
    · contradiction
  · rename_i hn
    split at h
    · contradiction
    · have hτ : ⟨(x, y) :: σ.vars, σ.regs⟩ = τ := Option.some.inj h
      subst τ
      have hx : x ∉ σ.vars.map (·.1) := by
        intro hm
        obtain ⟨e, he, hk⟩ := List.mem_map.mp hm
        have hf := find_key_of_mem (fun e : Nat × Nat => e.1) hi.1 he
        have : σ.varImage? x = some e.2 := by
          simp only [varImage?, ← hk, hf, Option.map_some]
        rw [hn] at this
        contradiction
      have hy : y ∉ σ.vars.map (·.2) := by
        simpa using ‹¬ σ.vars.any (fun e => e.2 == y) = true›
      refine ⟨⟨fun e he => List.mem_cons_of_mem _ he, fun _ he => he⟩, ?_, ?_⟩
      · simpa [Injective, List.map_cons, List.nodup_cons] using
          And.intro (And.intro hx hi.1) (And.intro (And.intro hy hi.2.1) hi.2.2)
      · simp [varImage?]

theorem addReg_sound {σ τ : Subst} {a b : Reg}
    (hi : Injective σ) (h : addReg? σ a b = some τ) :
    Extends σ τ ∧ Injective τ ∧ τ.regImage? a = some b := by
  unfold addReg? at h
  split at h
  · split at h
    · have hτ : σ = τ := Option.some.inj h
      subst τ
      exact ⟨extends_refl σ, hi, by simp_all⟩
    · contradiction
  · rename_i hn
    split at h
    · contradiction
    · have hτ : ⟨σ.vars, (a, b) :: σ.regs⟩ = τ := Option.some.inj h
      subst τ
      have ha : a ∉ σ.regs.map (·.1) := by
        intro hm
        obtain ⟨e, he, hk⟩ := List.mem_map.mp hm
        have hf := find_key_of_mem (fun e : Reg × Reg => e.1) hi.2.2.1 he
        have : σ.regImage? a = some e.2 := by
          simp only [regImage?, ← hk, hf, Option.map_some]
        rw [hn] at this
        contradiction
      have hb : b ∉ σ.regs.map (·.2) := by
        simpa using ‹¬ σ.regs.any (fun e => e.2 == b) = true›
      refine ⟨⟨fun _ he => he, fun e he => List.mem_cons_of_mem _ he⟩, ?_, ?_⟩
      · simpa [Injective, List.map_cons, List.nodup_cons] using
          And.intro hi.1 (And.intro hi.2.1 (And.intro (And.intro ha hi.2.2.1)
            (And.intro hb hi.2.2.2)))
      · simp [regImage?]

mutual
  theorem determined_extends {σ τ : Subst} (he : Extends σ τ)
      (hi : Injective σ) (hj : Injective τ) (a : Term) (hd : Determined σ a) :
      Determined τ a ∧ applyTerm τ a = applyTerm σ a := by
    cases a <;> simp only [Determined] at hd ⊢
    case const w c => exact ⟨True.intro, by simp only [applyTerm]⟩
    case var w x =>
      obtain ⟨y, hy⟩ := hd
      have ht := varImage_extends he hi hj hy
      exact ⟨⟨y, ht⟩, by simp [applyTerm, varLookup, ht, hy]⟩
    case regVar r =>
      obtain ⟨b, hb⟩ := hd
      have ht := regImage_extends he hi hj hb
      exact ⟨⟨b, ht⟩, by simp [applyTerm, regLookup, ht, hb]⟩
    case app w f ts =>
      obtain ⟨hd, ht⟩ := determinedTerms_extends he hi hj ts hd
      exact ⟨hd, by simp only [applyTerm, ht]⟩
  termination_by sizeOf a

  theorem determinedTerms_extends {σ τ : Subst} (he : Extends σ τ)
      (hi : Injective σ) (hj : Injective τ) (as : List Term)
      (hd : DeterminedTerms σ as) :
      DeterminedTerms τ as ∧ applyTerms τ as = applyTerms σ as := by
    cases as <;> simp only [DeterminedTerms] at hd ⊢
    case nil => exact ⟨True.intro, by simp only [applyTerms]⟩
    case cons a as =>
      obtain ⟨ha, hta⟩ := determined_extends he hi hj a hd.1
      obtain ⟨has, htas⟩ := determinedTerms_extends he hi hj as hd.2
      exact ⟨⟨ha, has⟩, by simp only [applyTerms, hta, htas]⟩
  termination_by sizeOf as
end

mutual
  theorem mergeTerm_spec (σ τ : Subst) (a b : Term)
      (hi : Injective σ) (h : mergeTerm σ a b = some τ) :
      Extends σ τ ∧ Injective τ ∧ Determined τ a ∧ applyTerm τ a = b := by
    cases a <;> cases b <;> simp only [mergeTerm, Determined] at h ⊢
    all_goals try contradiction
    case const.const w a v b =>
      split at h
      · split at h
        · have hv : w = v := eq_of_beq ‹w == v›
          have hc : a = b := eq_of_beq ‹a == b›
          subst v; subst b; cases h
          exact ⟨extends_refl _, hi, True.intro, by simp only [applyTerm]⟩
        · contradiction
      · contradiction
    case var.var w x v y =>
      split at h
      · have hw : w = v := eq_of_beq ‹w == v›
        subst v
        obtain ⟨he, hj, hv⟩ := addVar_sound hi h
        exact ⟨he, hj, ⟨y, hv⟩, by simp [applyTerm, varLookup, hv]⟩
      · contradiction
    case regVar.regVar a b =>
      split at h
      · obtain ⟨he, hj, hr⟩ := addReg_sound hi h
        exact ⟨he, hj, ⟨b, hr⟩, by simp [applyTerm, regLookup, hr]⟩
      · contradiction
    case app.app w f as v g bs =>
      split at h
      · split at h
        · have hw : w = v := eq_of_beq ‹w == v›
          have hf : f = g := eq_of_beq ‹f == g›
          subst v; subst g
          obtain ⟨he, hj, hd, ht⟩ := mergeList_spec σ τ as bs hi h
          exact ⟨he, hj, hd, by simp only [applyTerm, ht]⟩
        · contradiction
      · contradiction
  termination_by sizeOf a + sizeOf b

  theorem mergeList_spec (σ τ : Subst) (as bs : List Term)
      (hi : Injective σ) (h : mergeList σ as bs = some τ) :
      Extends σ τ ∧ Injective τ ∧ DeterminedTerms τ as ∧ applyTerms τ as = bs := by
    cases as with
    | nil =>
      cases bs <;> simp only [mergeList, DeterminedTerms] at h ⊢
      · cases h; exact ⟨extends_refl _, hi, True.intro, by simp only [applyTerms]⟩
      · contradiction
    | cons a as =>
      cases bs with
      | nil => simp [mergeList] at h
      | cons b bs =>
        simp only [mergeList] at h
        cases hm : mergeTerm σ a b with
        | none => simp [hm] at h
        | some υ =>
          simp only [hm] at h
          obtain ⟨he, hj, hd, ht⟩ := mergeTerm_spec σ υ a b hi hm
          obtain ⟨he', hj', hd', ht'⟩ := mergeList_spec υ τ as bs hj h
          obtain ⟨hda, hta⟩ := determined_extends he' hj hj' a hd
          simp only [DeterminedTerms]
          exact ⟨extends_trans he he', hj', ⟨hda, hd'⟩,
            by simp only [applyTerms, hta, ht, ht']⟩
  termination_by sizeOf as + sizeOf bs
end

private theorem filtered_lookup_getD {α κ δ : Type}
    [BEq κ] [LawfulBEq κ] [BEq δ] [LawfulBEq δ]
    (key : α → κ) (value : α → δ) (default : κ → δ)
    (xs : List α) (hn : (xs.map key).Nodup) (x : κ) :
    (((xs.filter (fun e => default (key e) != value e)).find?
      (fun e => key e == x)).map value).getD (default x) =
    ((xs.find? (fun e => key e == x)).map value).getD (default x) := by
  induction xs with
  | nil => simp
  | cons e es ih =>
    simp only [List.map_cons, List.nodup_cons] at hn
    by_cases hk : key e = x
    · have hf : es.find? (fun d => key d == x) = none := by
        apply List.find?_eq_none.mpr
        intro d hd heq
        have hdx : key d = x := eq_of_beq heq
        exact hn.1 (List.mem_map.mpr ⟨d, hd, hdx.trans hk.symm⟩)
      have hg : (es.filter (fun d => default (key d) != value d)).find?
          (fun d => key d == x) = none := by
        apply List.find?_eq_none.mpr
        intro d hd
        exact List.find?_eq_none.mp hf d (List.mem_filter.mp hd).1
      by_cases hv : default x = value e
      · simp [hk, hv, hg]
      · simp [hk, hv]
    · have hk' : (key e == x) = false := beq_eq_false_iff_ne.mpr hk
      by_cases hv : (default (key e) != value e) = true
      · simpa [List.filter_cons, List.find?_cons, hk', hv] using ih hn.2
      · simpa [List.filter_cons, List.find?_cons, hk', hv] using ih hn.2

theorem strip_varLookup {σ : Subst} (hi : Injective σ) (x : Nat) :
    σ.strip.varLookup x = σ.varLookup x := by
  exact filtered_lookup_getD (fun e : Nat × Nat => e.1) (·.2) id σ.vars hi.1 x

theorem strip_regLookup {σ : Subst} (hi : Injective σ) (r : Reg) :
    σ.strip.regLookup r = σ.regLookup r := by
  exact filtered_lookup_getD (fun e : Reg × Reg => e.1) (·.2) id σ.regs hi.2.2.1 r

theorem strip_injective {σ : Subst} (hi : Injective σ) : Injective σ.strip := by
  exact ⟨(List.filter_sublist.map _).nodup hi.1,
    (List.filter_sublist.map _).nodup hi.2.1,
    (List.filter_sublist.map _).nodup hi.2.2.1,
    (List.filter_sublist.map _).nodup hi.2.2.2⟩

mutual
  theorem strip_applyTerm {σ : Subst} (hi : Injective σ) (t : Term) :
      applyTerm σ.strip t = applyTerm σ t := by
    cases t with
    | const w c => simp only [applyTerm]
    | var w x => simp only [applyTerm, strip_varLookup hi]
    | regVar r => simp only [applyTerm, strip_regLookup hi]
    | app w op ts => simp only [applyTerm, strip_applyTerms hi ts]
  termination_by sizeOf t

  theorem strip_applyTerms {σ : Subst} (hi : Injective σ) (ts : List Term) :
      applyTerms σ.strip ts = applyTerms σ ts := by
    cases ts with
    | nil => simp only [applyTerms]
    | cons t ts => simp only [applyTerms, strip_applyTerm hi t, strip_applyTerms hi ts]
  termination_by sizeOf ts
end

end Subst

/-- Little-endian byte terms of a write value. The access width is a bit count. -/
def byteTerms (bits : Nat) (source : Term) : List Term :=
  let n := bits / 8
  (List.range n).map fun j =>
    solve (Term.app .w32 (.extract (8 * j) 8 source.width.bits) [source])

/-- Terms the comparison reads. A write contributes its byte extracts, not the
unsplit source. -/
def comparedTerms : Observation → List Term
  | .helper _ args => args
  | .branch _ _ cond => [cond.lhs, cond.rhs]
  | .ret term => [term]
  | .mapWrite map key _ bits source => map :: (key ++ byteTerms bits source)
  | .packetWrite _ bits source => byteTerms bits source

def sameShape : Observation → Observation → Bool
  | .helper k _, .helper k' _ => k == k'
  | .branch _ d c, .branch _ d' c' => d == d' && c.rel == c'.rel
  | .ret _, .ret _ => true
  | .mapWrite _ _ o w _, .mapWrite _ _ o' w' _ => o == o' && w == w'
  | .packetWrite o w _, .packetWrite o' w' _ => o == o' && w == w'
  | _, _ => false

def mergeObs (σ : Subst) (a b : Observation) : Option Subst :=
  if sameShape a b then Subst.mergeList σ (comparedTerms a) (comparedTerms b) else none

theorem mergeObs_spec (σ τ : Subst) (a b : Observation)
    (hi : Subst.Injective σ) (h : mergeObs σ a b = some τ) :
    Subst.Extends σ τ ∧ Subst.Injective τ ∧
      Subst.DeterminedTerms τ (comparedTerms a) ∧
      Subst.applyTerms τ (comparedTerms a) = comparedTerms b := by
  unfold mergeObs at h
  split at h
  · exact Subst.mergeList_spec σ τ (comparedTerms a) (comparedTerms b) hi h
  · contradiction

def zipMatch (σ : Subst) : List Observation → List Observation → Option Subst
  | [], [] => some σ
  | a :: as, b :: bs =>
    match mergeObs σ a b with
    | none => none
    | some σ' => zipMatch σ' as bs
  | _, _ => none

theorem zip_spec (σ τ : Subst) (L R : List Observation)
    (hi : Subst.Injective σ) (h : zipMatch σ L R = some τ) :
    Subst.Extends σ τ ∧ Subst.Injective τ ∧ L.length = R.length ∧
      ∀ (i : Nat) (a b : Observation), L[i]? = some a → R[i]? = some b →
        Subst.applyTerms τ (comparedTerms a) = comparedTerms b := by
  induction L generalizing σ τ R with
  | nil =>
    cases R <;> simp only [zipMatch] at h
    · cases h
      refine ⟨Subst.extends_refl _, hi, rfl, ?_⟩
      intro i a b ha
      simp at ha
    · contradiction
  | cons a as ih =>
    cases R with
    | nil => simp [zipMatch] at h
    | cons b bs =>
      simp only [zipMatch] at h
      cases hm : mergeObs σ a b with
      | none => simp [hm] at h
      | some υ =>
        simp only [hm] at h
        obtain ⟨he, hj, hd, ht⟩ := mergeObs_spec σ υ a b hi hm
        obtain ⟨he', hj', hlen, htail⟩ := ih υ τ bs hj h
        refine ⟨Subst.extends_trans he he', hj', by simp [hlen], ?_⟩
        intro i x y hx hy
        cases i with
        | zero =>
          simp only [List.getElem?_cons_zero] at hx hy
          cases hx; cases hy
          obtain ⟨_, hta⟩ := Subst.determinedTerms_extends he' hj hj' (comparedTerms a) hd
          exact hta.trans ht
        | succ i =>
          simp only [List.getElem?_cons_succ] at hx hy
          exact htail i x y hx hy

structure UnifyOut where
  pass : Bool
  pairs : List (Nat × Nat)
  onlyLeft : List Nat
  onlyRight : List Nat
  subst : Subst
  ambiguous : Bool
  deriving Repr

def identityPairs (n : Nat) : List (Nat × Nat) :=
  (List.range n).map fun i => (i, i)

def unifyLists (L R : List Observation) : UnifyOut :=
  match zipMatch .empty (L.map prepare) (R.map prepare) with
  | some σ =>
    { pass := true
      pairs := identityPairs L.length
      onlyLeft := []
      onlyRight := []
      subst := σ.strip
      ambiguous := false }
  | none =>
    { pass := false
      pairs := []
      onlyLeft := List.range L.length
      onlyRight := List.range R.length
      subst := .empty
      ambiguous := false }

theorem identityPairs_mem (n i j : Nat) :
    (i, j) ∈ identityPairs n ↔ j = i ∧ i < n := by
  simp only [identityPairs, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨k, hk, hp⟩
    cases hp
    exact ⟨rfl, hk⟩
  · intro ⟨hj, hi⟩
    refine ⟨i, hi, ?_⟩
    cases hj
    rfl

theorem unify_subst_injective (L R : List Observation) :
    Subst.Injective (unifyLists L R).subst := by
  unfold unifyLists
  cases hzip : zipMatch .empty (L.map prepare) (R.map prepare) with
  | some σ =>
    have h := zip_spec .empty σ (L.map prepare) (R.map prepare) Subst.empty_injective hzip
    simpa [hzip] using Subst.strip_injective h.2.1
  | none =>
    simpa [hzip] using Subst.empty_injective

theorem unify_pairs_sound (L R : List Observation) (i j : Nat)
    (hij : (i, j) ∈ (unifyLists L R).pairs) :
    ∃ a b, (L.map prepare)[i]? = some a ∧ (R.map prepare)[j]? = some b ∧
      Subst.applyTerms (unifyLists L R).subst (comparedTerms a) = comparedTerms b := by
  unfold unifyLists at hij ⊢
  cases hzip : zipMatch .empty (L.map prepare) (R.map prepare) with
  | none =>
    simp [hzip] at hij
  | some σ =>
    simp only [hzip] at hij ⊢
    have hmem := (identityPairs_mem L.length i j).mp hij
    obtain ⟨rfl, hi⟩ := hmem
    have hspec := zip_spec .empty σ (L.map prepare) (R.map prepare)
      Subst.empty_injective hzip
    have hlen : (L.map prepare).length = (R.map prepare).length := hspec.2.2.1
    have hiL : j < (L.map prepare).length := by simpa using hi
    have hiR : j < (R.map prepare).length := by simpa [hlen] using hiL
    have ha : (L.map prepare)[j]? = some ((L.map prepare)[j]) :=
      List.getElem?_eq_getElem hiL
    have hb : (R.map prepare)[j]? = some ((R.map prepare)[j]) :=
      List.getElem?_eq_getElem hiR
    refine ⟨(L.map prepare)[j], (R.map prepare)[j], ha, hb, ?_⟩
    have happ := hspec.2.2.2 j _ _ ha hb
    exact (Subst.strip_applyTerms hspec.2.1 (comparedTerms ((L.map prepare)[j]))).trans happ

theorem unify_pass_iff_length (L R : List Observation) :
    (unifyLists L R).pass = true ↔
      (unifyLists L R).pairs.length = L.length ∧ L.length = R.length := by
  unfold unifyLists
  cases hzip : zipMatch .empty (L.map prepare) (R.map prepare) with
  | some σ =>
    have hlen := (zip_spec .empty σ (L.map prepare) (R.map prepare)
      Subst.empty_injective hzip).2.2.1
    simp only [identityPairs, List.length_map, List.length_range, true_iff]
    simpa [List.length_map] using hlen
  | none =>
    dsimp
    constructor
    · intro h
      cases h
    · intro ⟨h0, hlen⟩
      cases L <;> cases R <;> simp [zipMatch] at hzip h0 hlen

private def renderNats (ns : List Nat) : String :=
  "[" ++ String.intercalate "," (ns.map toString) ++ "]"

private def renderSubst (σ : Subst) : String :=
  let vars := σ.vars.mergeSort (fun a b =>
    a.1 < b.1 || (a.1 == b.1 && a.2 ≤ b.2))
  let regs := σ.regs.mergeSort (fun a b => renderReg a.1 ≤ renderReg b.1)
  let vs := String.intercalate "," (vars.map fun (a, b) => renderNats [a, b])
  let rs := String.intercalate "," (regs.map fun (a, b) =>
    s!"[\"{renderReg a}\",\"{renderReg b}\"]")
  s!"\{\"vars\":[{vs}],\"regs\":[{rs}]}"

private def renderUnifyOut (out : UnifyOut) : String :=
  if out.ambiguous then "{\"ok\":false}" else
  let pairs := String.intercalate "," (out.pairs.map fun (i, j) =>
    s!"\{\"left\":{i},\"right\":{j}}")
  s!"\{\"ok\":true,\"pass\":{out.pass},\"pairs\":[{pairs}],\"onlyLeft\":{renderNats out.onlyLeft},\"onlyRight\":{renderNats out.onlyRight},\"subst\":{renderSubst out.subst}}"

private def exactFields (value : Lean.Json) (fields : List String) : Bool :=
  match value.getObj?.toOption with
  | none => false
  | some obj => obj.size == fields.length && fields.all obj.contains

private def field (value : Lean.Json) (key : String) : Option Lean.Json :=
  (value.getObjVal? key).toOption

/-- Boxed Lean String ABI. Bad observation JSON and lists longer than 32 return
`null`. A full index-aligned match sets `pass` true. -/
@[export lean_cross_pred_unify]
def exportCrossPredUnify (requestJson : String) : String :=
  let result : Option String := do
    let j ← (Lean.Json.parse requestJson).toOption
    if !exactFields j ["left", "right"] then none
    let left ← ((← field j "left").getArr?).toOption
    let right ← ((← field j "right").getArr?).toOption
    if left.size > 32 || right.size > 32 then none
    let L ← left.toList.mapM parsePredicateJson
    let R ← right.toList.mapM parsePredicateJson
    pure (renderUnifyOut (unifyLists L R))
  result.getD "null"

#guard exportCrossPredUnify
  "{\"left\":[{\"kind\":\"ret\",\"width\":32,\"term\":\"v32:4\"}],\"right\":[{\"kind\":\"ret\",\"width\":32,\"term\":\"v32:9\"}]}" ==
  "{\"ok\":true,\"pass\":true,\"pairs\":[{\"left\":0,\"right\":0}],\"onlyLeft\":[],\"onlyRight\":[],\"subst\":{\"vars\":[[4,9]],\"regs\":[]}}"

#guard exportCrossPredUnify
  "{\"left\":[{\"kind\":\"ret\",\"width\":32,\"term\":\"1\"},{\"kind\":\"ret\",\"width\":32,\"term\":\"2\"}],\"right\":[{\"kind\":\"ret\",\"width\":32,\"term\":\"2\"},{\"kind\":\"ret\",\"width\":32,\"term\":\"1\"}]}" ==
  "{\"ok\":true,\"pass\":false,\"pairs\":[],\"onlyLeft\":[0,1],\"onlyRight\":[0,1],\"subst\":{\"vars\":[],\"regs\":[]}}"

end Inbox.Cross
