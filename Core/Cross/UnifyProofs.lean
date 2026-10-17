import Core.Cross.Unify

namespace Core
namespace ObservationEqProofObligations

/-- The two projections are subsequences of the original zero-based indices. -/
theorem unify_pairs_sublist (L R : List CrossPred) :
    ((unifyLists L R).pairs.map Prod.fst).Sublist (List.range L.length) ∧
    ((unifyLists L R).pairs.map Prod.snd).Sublist (List.range R.length) := by
  obtain ⟨_, hl, hr⟩ := search_structure
    ((List.range L.length).zip L) ((List.range R.length).zip R) .empty
  constructor
  · simpa only [List.map_fst_zip (l₁ := List.range L.length) (l₂ := L) (by simp)] using hl
  · simpa only [List.map_fst_zip (l₁ := List.range R.length) (l₂ := R) (by simp)] using hr

theorem unify_pairs_strict (L R : List CrossPred) :
    ((unifyLists L R).pairs.map Prod.fst).Pairwise (· < ·) ∧
    ((unifyLists L R).pairs.map Prod.snd).Pairwise (· < ·) := by
  obtain ⟨hl, hr⟩ := unify_pairs_sublist L R
  exact ⟨List.pairwise_lt_range.sublist hl, List.pairwise_lt_range.sublist hr⟩

theorem unify_pairs_nodup (L R : List CrossPred) :
    ((unifyLists L R).pairs.map Prod.fst).Nodup ∧
    ((unifyLists L R).pairs.map Prod.snd).Nodup ∧
    (unifyLists L R).pairs.Nodup := by
  obtain ⟨hl, hr⟩ := unify_pairs_strict L R
  refine ⟨hl.imp Nat.ne_of_lt, hr.imp Nat.ne_of_lt, ?_⟩
  apply (List.pairwise_map.mp hl).imp
  intro a b hab heq
  subst b
  exact Nat.lt_irrefl _ hab

theorem unify_pairs_bounds (L R : List CrossPred) (i j : Nat)
    (h : (i, j) ∈ (unifyLists L R).pairs) : i < L.length ∧ j < R.length := by
  obtain ⟨hl, hr⟩ := unify_pairs_sublist L R
  exact ⟨List.mem_range.mp (hl.subset (List.mem_map_of_mem h)),
    List.mem_range.mp (hr.subset (List.mem_map_of_mem h))⟩

theorem unify_pairs_length_le (L R : List CrossPred) :
    (unifyLists L R).pairs.length ≤ L.length ∧
    (unifyLists L R).pairs.length ≤ R.length := by
  obtain ⟨hl, hr⟩ := unify_pairs_sublist L R
  exact ⟨by simpa using hl.length_le, by simpa using hr.length_le⟩

theorem unify_onlyLeft_mem_iff (L R : List CrossPred) (i : Nat) :
    i ∈ (unifyLists L R).onlyLeft ↔
      i < L.length ∧ i ∉ (unifyLists L R).pairs.map Prod.fst := by
  simp only [unifyLists, List.mem_filter, List.mem_range, Bool.not_eq_true',
    List.any_eq_false, beq_iff_eq]
  constructor
  · rintro ⟨hi, hn⟩
    refine ⟨hi, ?_⟩
    intro hm
    obtain ⟨p, hp, heq⟩ := List.mem_map.mp hm
    exact hn p hp heq
  · rintro ⟨hi, hn⟩
    refine ⟨hi, ?_⟩
    intro p hp heq
    exact hn (List.mem_map.mpr ⟨p, hp, heq⟩)

theorem unify_onlyRight_mem_iff (L R : List CrossPred) (j : Nat) :
    j ∈ (unifyLists L R).onlyRight ↔
      j < R.length ∧ j ∉ (unifyLists L R).pairs.map Prod.snd := by
  simp only [unifyLists, List.mem_filter, List.mem_range, Bool.not_eq_true',
    List.any_eq_false, beq_iff_eq]
  constructor
  · rintro ⟨hj, hn⟩
    refine ⟨hj, ?_⟩
    intro hm
    obtain ⟨p, hp, heq⟩ := List.mem_map.mp hm
    exact hn p hp heq
  · rintro ⟨hj, hn⟩
    refine ⟨hj, ?_⟩
    intro p hp heq
    exact hn (List.mem_map.mpr ⟨p, hp, heq⟩)

theorem unify_onlyLeft_pair_iff (L R : List CrossPred) (i : Nat) :
    i ∈ (unifyLists L R).onlyLeft ↔
      i < L.length ∧ ∀ j, (i, j) ∉ (unifyLists L R).pairs := by
  rw [unify_onlyLeft_mem_iff]
  constructor
  · rintro ⟨hi, hn⟩
    refine ⟨hi, fun j hj => hn ?_⟩
    exact List.mem_map_of_mem hj
  · rintro ⟨hi, hn⟩
    refine ⟨hi, ?_⟩
    rintro hm
    obtain ⟨⟨a, b⟩, hp, heq⟩ := List.mem_map.mp hm
    dsimp at heq
    subst a
    exact hn b hp

theorem unify_onlyRight_pair_iff (L R : List CrossPred) (j : Nat) :
    j ∈ (unifyLists L R).onlyRight ↔
      j < R.length ∧ ∀ i, (i, j) ∉ (unifyLists L R).pairs := by
  rw [unify_onlyRight_mem_iff]
  constructor
  · rintro ⟨hj, hn⟩
    refine ⟨hj, fun i hi => hn ?_⟩
    exact List.mem_map_of_mem hi
  · rintro ⟨hj, hn⟩
    refine ⟨hj, ?_⟩
    rintro hm
    obtain ⟨⟨a, b⟩, hp, heq⟩ := List.mem_map.mp hm
    dsimp at heq
    subst b
    exact hn a hp

theorem unify_only_strict (L R : List CrossPred) :
    (unifyLists L R).onlyLeft.Pairwise (· < ·) ∧
    (unifyLists L R).onlyRight.Pairwise (· < ·) := by
  constructor <;> exact List.pairwise_lt_range.sublist List.filter_sublist

theorem unify_only_nodup (L R : List CrossPred) :
    (unifyLists L R).onlyLeft.Nodup ∧ (unifyLists L R).onlyRight.Nodup := by
  obtain ⟨hl, hr⟩ := unify_only_strict L R
  exact ⟨hl.imp Nat.ne_of_lt, hr.imp Nat.ne_of_lt⟩

private theorem sublist_eq_of_coverage {α : Type} {xs ys : List α}
    (hs : xs.Sublist ys) (hn : ys.Nodup) (hc : ys ⊆ xs) : xs = ys := by
  revert hn hc
  induction hs with
  | slnil => intro _ _; rfl
  | @cons xs ys a hs ih =>
    intro hn hc
    have ha : a ∉ ys := (List.nodup_cons.mp hn).1
    have hm : a ∈ xs := hc (by simp)
    exact False.elim (ha (hs.subset hm))
  | @cons₂ xs ys a hs ih =>
    intro hn hc
    have hnodup := List.nodup_cons.mp hn
    have hcov : ys ⊆ xs := by
      intro b hb
      rcases List.mem_cons.mp (hc (List.mem_cons_of_mem a hb)) with heq | hm
      · subst b
        exact False.elim (hnodup.1 hb)
      · exact hm
    exact congrArg (List.cons a) (ih hnodup.2 hcov)

theorem unify_pass_iff_coverage (L R : List CrossPred) :
    (unifyLists L R).pass = true ↔
      (∀ i, i < L.length → i ∈ (unifyLists L R).pairs.map Prod.fst) ∧
      (∀ j, j < R.length → j ∈ (unifyLists L R).pairs.map Prod.snd) := by
  have hp : (unifyLists L R).pass = true ↔
      (unifyLists L R).onlyLeft = [] ∧ (unifyLists L R).onlyRight = [] := by
    simp [UnifyOut.pass]
  rw [hp]
  constructor
  · rintro ⟨hl, hr⟩
    constructor
    · intro i hi
      apply Classical.byContradiction
      intro hn
      have hm := (unify_onlyLeft_mem_iff L R i).mpr ⟨hi, hn⟩
      simp only [hl, List.not_mem_nil] at hm
    · intro j hj
      apply Classical.byContradiction
      intro hn
      have hm := (unify_onlyRight_mem_iff L R j).mpr ⟨hj, hn⟩
      simp only [hr, List.not_mem_nil] at hm
  · rintro ⟨hl, hr⟩
    constructor
    · apply List.eq_nil_iff_forall_not_mem.mpr
      intro i hi
      obtain ⟨hb, hn⟩ := (unify_onlyLeft_mem_iff L R i).mp hi
      exact hn (hl i hb)
    · apply List.eq_nil_iff_forall_not_mem.mpr
      intro j hj
      obtain ⟨hb, hn⟩ := (unify_onlyRight_mem_iff L R j).mp hj
      exact hn (hr j hb)

theorem unify_pass_iff_full (L R : List CrossPred) :
    (unifyLists L R).pass = true ↔
      (unifyLists L R).pairs.map Prod.fst = List.range L.length ∧
      (unifyLists L R).pairs.map Prod.snd = List.range R.length := by
  rw [unify_pass_iff_coverage]
  obtain ⟨hsl, hsr⟩ := unify_pairs_sublist L R
  constructor
  · rintro ⟨hl, hr⟩
    exact ⟨sublist_eq_of_coverage hsl List.nodup_range
        (fun _ hi => hl _ (List.mem_range.mp hi)),
      sublist_eq_of_coverage hsr List.nodup_range
        (fun _ hj => hr _ (List.mem_range.mp hj))⟩
  · rintro ⟨hl, hr⟩
    constructor
    · intro i hi
      rw [hl]
      exact List.mem_range.mpr hi
    · intro j hj
      rw [hr]
      exact List.mem_range.mpr hj

theorem unify_pass_iff_length (L R : List CrossPred) :
    (unifyLists L R).pass = true ↔
      (unifyLists L R).pairs.length = L.length ∧ L.length = R.length := by
  rw [unify_pass_iff_full]
  obtain ⟨hsl, hsr⟩ := unify_pairs_sublist L R
  constructor
  · rintro ⟨hl, hr⟩
    have hleft : (unifyLists L R).pairs.length = L.length := by
      simpa using congrArg List.length hl
    have hright : (unifyLists L R).pairs.length = R.length := by
      simpa using congrArg List.length hr
    exact ⟨hleft, hleft.symm.trans hright⟩
  · rintro ⟨hl, heq⟩
    exact ⟨hsl.eq_of_length (by simpa using hl),
      hsr.eq_of_length (by simpa using hl.trans heq)⟩

end ObservationEqProofObligations
end Core

namespace Core.CrossSubst

theorem swap_injective {σ : CrossSubst} (hi : Injective σ) : Injective σ.swap := by
  simpa only [Injective, swap, List.map_map, Function.comp_def] using
    And.intro hi.2.1 (And.intro hi.1 (And.intro hi.2.2.2 hi.2.2.1))

theorem swap_swap (σ : CrossSubst) : σ.swap.swap = σ := by
  cases σ
  simp [swap, List.map_map, Function.comp_def]

theorem swap_strip (σ : CrossSubst) : σ.strip.swap = σ.swap.strip := by
  have hneq (a b : Nat) : (a != b) = (b != a) := by
    exact bne_comm
  cases σ
  simp [swap, strip, List.filter_map, Function.comp_def, hneq]

theorem swap_varImage_some {σ : CrossSubst} (hi : Injective σ) {x y : Nat}
    (h : σ.varImage? x = some y) : σ.swap.varImage? y = some x := by
  apply (varImage_some_iff (swap_injective hi) y x).mpr
  exact List.mem_map.mpr ⟨(x, y), (varImage_some_iff hi x y).mp h, rfl⟩

theorem swap_regImage_some {σ : CrossSubst} (hi : Injective σ)
    {k : RegKind} {a b : Nat} (h : σ.regImage? k a = some b) :
    σ.swap.regImage? k b = some a := by
  apply (regImage_some_iff (swap_injective hi) k b a).mpr
  exact List.mem_map.mpr ⟨(k, a, b), (regImage_some_iff hi k a b).mp h, rfl⟩

mutual
  theorem determined_swap (σ : CrossSubst) (hi : Injective σ) (t : CrossTerm)
      (hd : Determined σ t) :
      Determined σ.swap (applyTerm σ t) ∧ applyTerm σ.swap (applyTerm σ t) = t := by
    cases t with
    | c z => simp only [applyTerm, Determined, and_self]
    | var x =>
      simp only [Determined] at hd
      obtain ⟨y, hy⟩ := hd
      have hs := swap_varImage_some hi hy
      refine ⟨?_, ?_⟩
      · simpa only [applyTerm, varLookup, hy, Option.getD_some, Determined] using
          (show ∃ z, σ.swap.varImage? y = some z from ⟨x, hs⟩)
      · simp only [applyTerm, varLookup, hy, hs, Option.getD_some]
    | reg k a =>
      simp only [Determined] at hd
      obtain ⟨b, hb⟩ := hd
      have hs := swap_regImage_some hi hb
      refine ⟨?_, ?_⟩
      · simpa only [applyTerm, regLookup, hb, Option.getD_some, Determined] using
          (show ∃ c, σ.swap.regImage? k b = some c from ⟨a, hs⟩)
      · simp only [applyTerm, regLookup, hb, hs, Option.getD_some]
    | app f ts =>
      simp only [Determined] at hd
      obtain ⟨hd, ht⟩ := determinedTerms_swap σ hi ts hd
      refine ⟨?_, ?_⟩
      · simpa only [applyTerm, Determined] using hd
      · simp only [applyTerm, ht]
    | external l ts =>
      simp only [Determined] at hd
      obtain ⟨hd, ht⟩ := determinedTerms_swap σ hi ts hd
      refine ⟨?_, ?_⟩
      · simpa only [applyTerm, Determined] using hd
      · simp only [applyTerm, ht]
  termination_by sizeOf t

  theorem determinedTerms_swap (σ : CrossSubst) (hi : Injective σ)
      (ts : List CrossTerm) (hd : DeterminedTerms σ ts) :
      DeterminedTerms σ.swap (applyTerms σ ts) ∧
        applyTerms σ.swap (applyTerms σ ts) = ts := by
    cases ts with
    | nil => simp only [applyTerms, DeterminedTerms, and_self]
    | cons t ts =>
      simp only [DeterminedTerms] at hd
      obtain ⟨hd₁, ht₁⟩ := determined_swap σ hi t hd.1
      obtain ⟨hd₂, ht₂⟩ := determinedTerms_swap σ hi ts hd.2
      refine ⟨?_, ?_⟩
      · simpa only [applyTerms, DeterminedTerms] using And.intro hd₁ hd₂
      · simp only [applyTerms, ht₁, ht₂]
  termination_by sizeOf ts
end

private theorem determinedValue_swap (σ : CrossSubst) (hi : Injective σ)
    (v : CrossValue) (hd : DeterminedValue σ v) :
    DeterminedValue σ.swap (applyValue σ v) ∧
      applyValue σ.swap (applyValue σ v) = v := by
  cases v with
  | bytes ts =>
    obtain ⟨hd, ht⟩ := determinedTerms_swap σ hi ts hd
    exact ⟨hd, by simp only [applyValue, ht]⟩
  | source t =>
    obtain ⟨hd, ht⟩ := determined_swap σ hi t hd
    exact ⟨hd, by simp only [applyValue, ht]⟩

private theorem determinedMutation_swap (σ : CrossSubst) (hi : Injective σ)
    (m : CrossMutation) (hd : DeterminedMutation σ m) :
    DeterminedMutation σ.swap (applyMutation σ m) ∧
      applyMutation σ.swap (applyMutation σ m) = m := by
  obtain ⟨hd₁, ht₁⟩ := determined_swap σ hi m.map hd.1
  obtain ⟨hd₂, ht₂⟩ := determinedTerms_swap σ hi m.key hd.2.1
  obtain ⟨hd₃, ht₃⟩ := determinedValue_swap σ hi m.value hd.2.2
  exact ⟨⟨hd₁, hd₂, hd₃⟩, by simp only [applyMutation, ht₁, ht₂, ht₃]⟩

private theorem determinedHelper_swap (σ : CrossSubst) (hi : Injective σ)
    (h : CrossHelper) (hd : DeterminedHelper σ h) :
    DeterminedHelper σ.swap (applyHelper σ h) ∧
      applyHelper σ.swap (applyHelper σ h) = h := by
  cases h with
  | lookup m key =>
    obtain ⟨hd₁, ht₁⟩ := determined_swap σ hi m hd.1
    obtain ⟨hd₂, ht₂⟩ := determinedTerms_swap σ hi key hd.2
    exact ⟨⟨hd₁, hd₂⟩, by simp only [applyHelper, ht₁, ht₂]⟩
  | mutation m =>
    obtain ⟨hd, ht⟩ := determinedMutation_swap σ hi m hd
    exact ⟨hd, by simp only [applyHelper, ht]⟩
  | other id args =>
    obtain ⟨hd, ht⟩ := determinedTerms_swap σ hi args hd
    exact ⟨hd, by simp only [applyHelper, ht]⟩

private theorem determinedCond_swap (σ : CrossSubst) (hi : Injective σ)
    (c : CrossCond) (hd : DeterminedCond σ c) :
    DeterminedCond σ.swap (applyCond σ c) ∧
      applyCond σ.swap (applyCond σ c) = c := by
  cases c with
  | plain r a b | packetBound a r b =>
    obtain ⟨hd₁, ht₁⟩ := determined_swap σ hi a hd.1
    obtain ⟨hd₂, ht₂⟩ := determined_swap σ hi b hd.2
    exact ⟨⟨hd₁, hd₂⟩, by simp only [applyCond, ht₁, ht₂]⟩
  | packetField a r z =>
    obtain ⟨hd, ht⟩ := determined_swap σ hi a hd
    exact ⟨hd, by simp only [applyCond, ht]⟩

/-- Inversion is local to covered input symbols, not a global lookup hypothesis. -/
theorem determinedPred_swap (σ : CrossSubst) (hi : Injective σ)
    (p : CrossPred) (hd : DeterminedPred σ p) :
    DeterminedPred σ.swap (rename σ p) ∧ rename σ.swap (rename σ p) = p := by
  cases p with
  | helper h =>
    obtain ⟨hd, ht⟩ := determinedHelper_swap σ hi h hd
    exact ⟨hd, by simp only [rename, ht]⟩
  | branch b =>
    obtain ⟨hd, ht⟩ := determinedCond_swap σ hi b.cond hd
    exact ⟨hd, by simp only [rename, ht]⟩
  | ret r =>
    obtain ⟨hd, ht⟩ := determined_swap σ hi r.payload hd
    exact ⟨hd, by cases r; simp only [rename, ht]⟩
  | mapWrite m =>
    obtain ⟨hd, ht⟩ := determinedMutation_swap σ hi m hd
    exact ⟨hd, by simp only [rename, ht]⟩
  | packetWrite p =>
    obtain ⟨hd₁, ht₁⟩ := determined_swap σ hi p.offset hd.1
    obtain ⟨hd₂, ht₂⟩ := determinedValue_swap σ hi p.value hd.2
    exact ⟨⟨hd₁, hd₂⟩, by simp only [rename, ht₁, ht₂]⟩

theorem rename_swap_of_determined (σ : CrossSubst) (hi : Injective σ)
    (p : CrossPred) (hd : DeterminedPred σ p) :
    rename σ.strip.swap (rename σ.strip p) = p := by
  rw [swap_strip, ProofObligations.strip_rename _ _ (swap_injective hi),
    ProofObligations.strip_rename _ _ hi]
  exact (determinedPred_swap σ hi p hd).2

end Core.CrossSubst

namespace Core

/-- A shared, explicitly covered injective renaming witnesses an ordered alignment. -/
structure AlignmentWith (σ : CrossSubst) (L R : List CrossPred)
    (pairs : List (Nat × Nat)) : Prop where
  injective : CrossSubst.Injective σ
  leftStrict : pairs.Pairwise (fun a b => a.1 < b.1)
  rightStrict : pairs.Pairwise (fun a b => a.2 < b.2)
  matched : ∀ i j, (i, j) ∈ pairs →
    ∃ a b, L[i]? = some a ∧ R[j]? = some b ∧
      CrossSubst.DeterminedPred σ a ∧ CrossSubst.rename σ a = b

def AdmissibleAlignment (L R : List CrossPred) (pairs : List (Nat × Nat)) : Prop :=
  ∃ σ, AlignmentWith σ L R pairs

def MaximumAlignment (L R : List CrossPred) (pairs : List (Nat × Nat)) : Prop :=
  AdmissibleAlignment L R pairs ∧
    ∀ other, AdmissibleAlignment L R other → other.length ≤ pairs.length

def AmbiguousMaximum (L R : List CrossPred) : Prop :=
  ∃ a b, MaximumAlignment L R a ∧ MaximumAlignment L R b ∧ a ≠ b

theorem AlignmentWith.swap {σ : CrossSubst} {L R : List CrossPred}
    {pairs : List (Nat × Nat)} (h : AlignmentWith σ L R pairs) :
    AlignmentWith σ.swap R L (pairs.map Prod.swap) := by
  refine ⟨CrossSubst.swap_injective h.injective, ?_, ?_, ?_⟩
  · simpa only [List.pairwise_map, Prod.swap] using h.rightStrict
  · simpa only [List.pairwise_map, Prod.swap] using h.leftStrict
  · intro j i hij
    obtain ⟨⟨a, b⟩, hab, heq⟩ := List.mem_map.mp hij
    have heq : (b, a) = (j, i) := heq
    obtain ⟨hb, ha⟩ := Prod.mk.inj heq
    subst j
    subst i
    obtain ⟨p, q, hp, hq, hd, ht⟩ := h.matched a b hab
    obtain ⟨hd', ht'⟩ := CrossSubst.determinedPred_swap σ h.injective p hd
    rw [ht] at hd' ht'
    exact ⟨q, p, hq, hp, hd', ht'⟩

theorem admissibleAlignment_swap {L R : List CrossPred}
    {pairs : List (Nat × Nat)} (h : AdmissibleAlignment L R pairs) :
    AdmissibleAlignment R L (pairs.map Prod.swap) := by
  obtain ⟨σ, h⟩ := h
  exact ⟨σ.swap, h.swap⟩

theorem admissibleAlignment_swap_iff (L R : List CrossPred) (pairs : List (Nat × Nat)) :
    AdmissibleAlignment R L (pairs.map Prod.swap) ↔ AdmissibleAlignment L R pairs := by
  constructor
  · intro h
    simpa only [List.map_map, Prod.swap_swap_eq, List.map_id] using admissibleAlignment_swap h
  · exact admissibleAlignment_swap

theorem maximumAlignment_swap {L R : List CrossPred}
    {pairs : List (Nat × Nat)} (h : MaximumAlignment L R pairs) :
    MaximumAlignment R L (pairs.map Prod.swap) := by
  refine ⟨admissibleAlignment_swap h.1, ?_⟩
  intro other ho
  have hb := h.2 (other.map Prod.swap) (admissibleAlignment_swap ho)
  simpa only [List.length_map] using hb

theorem maximumAlignment_swap_iff (L R : List CrossPred) (pairs : List (Nat × Nat)) :
    MaximumAlignment R L (pairs.map Prod.swap) ↔ MaximumAlignment L R pairs := by
  constructor
  · intro h
    simpa only [List.map_map, Prod.swap_swap_eq, List.map_id] using maximumAlignment_swap h
  · exact maximumAlignment_swap

theorem ambiguousMaximum_swap_iff (L R : List CrossPred) :
    AmbiguousMaximum L R ↔ AmbiguousMaximum R L := by
  have forward : ∀ L R, AmbiguousMaximum L R → AmbiguousMaximum R L := by
    intro L R h
    obtain ⟨a, b, ha, hb, hne⟩ := h
    refine ⟨a.map Prod.swap, b.map Prod.swap,
      maximumAlignment_swap ha, maximumAlignment_swap hb, ?_⟩
    intro heq
    have hback := congrArg (List.map Prod.swap) heq
    simp only [List.map_map, Prod.swap_swap_eq, List.map_id] at hback
    exact hne hback
  exact ⟨forward L R, forward R L⟩

namespace ObservationEqProofObligations

theorem unify_admissible (L R : List CrossPred) :
    AdmissibleAlignment L R (unifyLists L R).pairs := by
  obtain ⟨σ, hi, _, hm⟩ := unify_alignment_witness L R
  obtain ⟨hl, hr⟩ := unify_pairs_strict L R
  exact ⟨σ, hi, List.pairwise_map.mp hl, List.pairwise_map.mp hr, hm⟩

/-- Swapping the exported substitution recovers each actually matched input. -/
theorem unify_pairs_inverse (L R : List CrossPred) (i j : Nat)
    (h : (i, j) ∈ (unifyLists L R).pairs) :
    ∃ a b, L[i]? = some a ∧ R[j]? = some b ∧
      CrossSubst.rename (unifyLists L R).subst.swap b = a := by
  obtain ⟨σ, hi, heq, hm⟩ := unify_alignment_witness L R
  obtain ⟨a, b, ha, hb, hd, ht⟩ := hm i j h
  refine ⟨a, b, ha, hb, ?_⟩
  rw [← heq, CrossSubst.swap_strip,
    CrossSubst.ProofObligations.strip_rename _ _ (CrossSubst.swap_injective hi), ← ht]
  exact (CrossSubst.determinedPred_swap σ hi a hd).2

end ObservationEqProofObligations
end Core

namespace Core.CrossSubst

theorem addVar_complete (σ υ : CrossSubst) (hi : Injective σ) (hj : Injective υ)
    (he : Extends σ υ) (x y : Nat) (hy : υ.varImage? x = some y) :
    ∃ τ, addVar? σ x y = some τ ∧ Extends τ υ := by
  cases hx : σ.varImage? x with
  | some z =>
    have hz := varImage_extends he hi hj hx
    have hzy : z = y := Option.some.inj (hz.symm.trans hy)
    subst z
    exact ⟨σ, by simp [addVar?, hx], he⟩
  | none =>
    have hf : σ.vars.any (·.2 == y) = false := by
      apply List.any_eq_false.mpr
      intro e hm
      intro htarget
      have htarget : e.2 = y := eq_of_beq htarget
      obtain ⟨a, b⟩ := e
      dsimp at htarget
      subst b
      have ha := (varImage_some_iff hj a y).mpr (he.1 _ hm)
      have hback := swap_varImage_some hj hy
      have hback' := swap_varImage_some hj ha
      have hax : a = x := Option.some.inj (hback'.symm.trans hback)
      subst a
      have hσ := (varImage_some_iff hi x y).mpr hm
      simp [hx] at hσ
    refine ⟨⟨(x, y) :: σ.vars, σ.regs⟩, by simp [addVar?, hx, hf], ?_⟩
    constructor
    · intro e hm
      rcases List.mem_cons.mp hm with hm | hm
      · subst e
        exact (varImage_some_iff hj x y).mp hy
      · exact he.1 _ hm
    · exact he.2

theorem addReg_complete (σ υ : CrossSubst) (hi : Injective σ) (hj : Injective υ)
    (he : Extends σ υ) (k : RegKind) (a b : Nat)
    (hb : υ.regImage? k a = some b) :
    ∃ τ, addReg? σ k a b = some τ ∧ Extends τ υ := by
  cases ha : σ.regImage? k a with
  | some c =>
    have hc := regImage_extends he hi hj ha
    have hcb : c = b := Option.some.inj (hc.symm.trans hb)
    subst c
    exact ⟨σ, by simp [addReg?, ha], he⟩
  | none =>
    have hf : σ.regs.any (fun e => e.1 == k && e.2.2 == b) = false := by
      apply List.any_eq_false.mpr
      intro e hm htarget
      obtain ⟨hk, ht⟩ : e.1 = k ∧ e.2.2 = b := by simpa using htarget
      obtain ⟨l, c, d⟩ := e
      dsimp at hk ht
      subst l; subst d
      have hc := (regImage_some_iff hj k c b).mpr (he.2 _ hm)
      have hback := swap_regImage_some hj hb
      have hback' := swap_regImage_some hj hc
      have hca : c = a := Option.some.inj (hback'.symm.trans hback)
      subst c
      have hσ := (regImage_some_iff hi k a b).mpr hm
      simp [ha] at hσ
    refine ⟨⟨σ.vars, (k, a, b) :: σ.regs⟩, by simp [addReg?, ha, hf], ?_⟩
    constructor
    · exact he.1
    · intro e hm
      rcases List.mem_cons.mp hm with hm | hm
      · subst e
        exact (regImage_some_iff hj k a b).mp hb
      · exact he.2 _ hm

mutual
  /-- A covered injective witness is sufficient for successful structural merging. -/
  theorem mergeTerm_complete (σ υ : CrossSubst) (a : CrossTerm)
      (hi : Injective σ) (hj : Injective υ) (he : Extends σ υ)
      (hd : Determined υ a) :
      ∃ τ, mergeTerm σ a (applyTerm υ a) = some τ ∧ Extends τ υ := by
    cases a with
    | c z => exact ⟨σ, by simp [mergeTerm, applyTerm], he⟩
    | var x =>
      simp only [Determined] at hd
      obtain ⟨y, hy⟩ := hd
      obtain ⟨τ, hm, he'⟩ := addVar_complete σ υ hi hj he x y hy
      exact ⟨τ, by simpa [mergeTerm, applyTerm, varLookup, hy] using hm, he'⟩
    | reg k a =>
      simp only [Determined] at hd
      obtain ⟨b, hb⟩ := hd
      obtain ⟨τ, hm, he'⟩ := addReg_complete σ υ hi hj he k a b hb
      exact ⟨τ, by simpa [mergeTerm, applyTerm, regLookup, hb] using hm, he'⟩
    | app f as =>
      simp only [Determined] at hd
      obtain ⟨τ, hm, he'⟩ := mergeList_complete σ υ as hi hj he hd
      exact ⟨τ, by simpa [mergeTerm, applyTerm] using hm, he'⟩
    | external l as =>
      simp only [Determined] at hd
      obtain ⟨τ, hm, he'⟩ := mergeList_complete σ υ as hi hj he hd
      exact ⟨τ, by simpa [mergeTerm, applyTerm] using hm, he'⟩
  termination_by sizeOf a

  theorem mergeList_complete (σ υ : CrossSubst) (as : List CrossTerm)
      (hi : Injective σ) (hj : Injective υ) (he : Extends σ υ)
      (hd : DeterminedTerms υ as) :
      ∃ τ, mergeList σ as (applyTerms υ as) = some τ ∧ Extends τ υ := by
    cases as with
    | nil => exact ⟨σ, by simp only [applyTerms, mergeList], he⟩
    | cons a as =>
      simp only [DeterminedTerms] at hd
      obtain ⟨σ₁, hm, he₁⟩ := mergeTerm_complete σ υ a hi hj he hd.1
      have hi₁ := (mergeTerm_spec σ σ₁ a (applyTerm υ a) hi hm).2.1
      obtain ⟨τ, hl, he₂⟩ := mergeList_complete σ₁ υ as hi₁ hj he₁ hd.2
      exact ⟨τ, by simp [mergeList, applyTerms, hm, hl], he₂⟩
  termination_by sizeOf as
end

theorem mergeValue_complete (σ υ : CrossSubst) (a : CrossValue)
    (hi : Injective σ) (hj : Injective υ) (he : Extends σ υ)
    (hd : DeterminedValue υ a) :
    ∃ τ, mergeValue σ a (applyValue υ a) = some τ ∧ Extends τ υ := by
  cases a with
  | bytes as => exact mergeList_complete σ υ as hi hj he hd
  | source a => exact mergeTerm_complete σ υ a hi hj he hd

theorem mergeMutation_complete (σ υ : CrossSubst) (a : CrossMutation)
    (hi : Injective σ) (hj : Injective υ) (he : Extends σ υ)
    (hd : DeterminedMutation υ a) :
    ∃ τ, mergeMutation σ a (applyMutation υ a) = some τ ∧ Extends τ υ := by
  obtain ⟨σ₁, hm, he₁⟩ := mergeTerm_complete σ υ a.map hi hj he hd.1
  have hi₁ := (mergeTerm_spec σ σ₁ a.map (applyTerm υ a.map) hi hm).2.1
  obtain ⟨σ₂, hk, he₂⟩ := mergeList_complete σ₁ υ a.key hi₁ hj he₁ hd.2.1
  have hi₂ := (mergeList_spec σ₁ σ₂ a.key (applyTerms υ a.key) hi₁ hk).2.1
  obtain ⟨τ, hv, he₃⟩ := mergeValue_complete σ₂ υ a.value hi₂ hj he₂ hd.2.2
  exact ⟨τ, by simp [mergeMutation, applyMutation, hm, hk, hv], he₃⟩

theorem mergeHelper_complete (σ υ : CrossSubst) (a : CrossHelper)
    (hi : Injective σ) (hj : Injective υ) (he : Extends σ υ)
    (hd : DeterminedHelper υ a) :
    ∃ τ, mergeHelper σ a (applyHelper υ a) = some τ ∧ Extends τ υ := by
  cases a with
  | lookup a as =>
    obtain ⟨σ₁, hm, he₁⟩ := mergeTerm_complete σ υ a hi hj he hd.1
    have hi₁ := (mergeTerm_spec σ σ₁ a (applyTerm υ a) hi hm).2.1
    obtain ⟨τ, hl, he₂⟩ := mergeList_complete σ₁ υ as hi₁ hj he₁ hd.2
    exact ⟨τ, by simp [mergeHelper, applyHelper, hm, hl], he₂⟩
  | mutation a => exact mergeMutation_complete σ υ a hi hj he hd
  | other id as =>
    obtain ⟨τ, hl, he'⟩ := mergeList_complete σ υ as hi hj he hd
    exact ⟨τ, by simpa [mergeHelper, applyHelper] using hl, he'⟩

theorem mergeCond_complete (σ υ : CrossSubst) (a : CrossCond)
    (hi : Injective σ) (hj : Injective υ) (he : Extends σ υ)
    (hd : DeterminedCond υ a) :
    ∃ τ, mergeCond σ a (applyCond υ a) = some τ ∧ Extends τ υ := by
  cases a with
  | plain r a b | packetBound a r b =>
    obtain ⟨σ₁, hm, he₁⟩ := mergeTerm_complete σ υ a hi hj he hd.1
    have hi₁ := (mergeTerm_spec σ σ₁ a (applyTerm υ a) hi hm).2.1
    obtain ⟨τ, hn, he₂⟩ := mergeTerm_complete σ₁ υ b hi₁ hj he₁ hd.2
    exact ⟨τ, by simp [mergeCond, applyCond, hm, hn], he₂⟩
  | packetField a r z =>
    obtain ⟨τ, hm, he'⟩ := mergeTerm_complete σ υ a hi hj he hd
    exact ⟨τ, by simpa [mergeCond, applyCond] using hm, he'⟩

theorem mergePred_complete (σ υ : CrossSubst) (a : CrossPred)
    (hi : Injective σ) (hj : Injective υ) (he : Extends σ υ)
    (hd : DeterminedPred υ a) :
    ∃ τ, mergePred σ a (rename υ a) = some τ ∧ Extends τ υ := by
  cases a with
  | helper a => exact mergeHelper_complete σ υ a hi hj he hd
  | branch a =>
    obtain ⟨τ, hm, he'⟩ := mergeCond_complete σ υ a.cond hi hj he hd
    exact ⟨τ, by simpa [mergePred, rename] using hm, he'⟩
  | ret a => exact mergeTerm_complete σ υ a.payload hi hj he hd
  | mapWrite a => exact mergeMutation_complete σ υ a hi hj he hd
  | packetWrite a =>
    obtain ⟨σ₁, hm, he₁⟩ := mergeTerm_complete σ υ a.offset hi hj he hd.1
    have hi₁ := (mergeTerm_spec σ σ₁ a.offset (applyTerm υ a.offset) hi hm).2.1
    obtain ⟨τ, hv, he₂⟩ := mergeValue_complete σ₁ υ a.value hi₁ hj he₁ hd.2
    exact ⟨τ, by simp [mergePred, rename, hm, hv], he₂⟩

end Core.CrossSubst

namespace Core.CrossSubst

theorem applyTerm_injective_on_determined (σ : CrossSubst) (hi : Injective σ)
    (a b : CrossTerm) (ha : Determined σ a) (hb : Determined σ b)
    (heq : applyTerm σ a = applyTerm σ b) : a = b := by
  have hback := congrArg (applyTerm σ.swap) heq
  rw [(determined_swap σ hi a ha).2, (determined_swap σ hi b hb).2] at hback
  exact hback

theorem rename_injective_on_determined (σ : CrossSubst) (hi : Injective σ)
    (a b : CrossPred) (ha : DeterminedPred σ a) (hb : DeterminedPred σ b)
    (heq : rename σ a = rename σ b) : a = b := by
  have hback := congrArg (rename σ.swap) heq
  rw [(determinedPred_swap σ hi a ha).2, (determinedPred_swap σ hi b hb).2] at hback
  exact hback

end Core.CrossSubst

namespace Core

private theorem strict_length_bound (xs : List Nat) (hi : Nat) :
    ∀ lo, xs.Pairwise (· < ·) → (∀ x ∈ xs, lo ≤ x ∧ x < hi) →
      xs.length ≤ hi - lo := by
  induction xs with
  | nil => intro lo _ _; simp
  | cons a xs ih =>
    intro lo hp hb
    obtain ⟨hlo, hhi⟩ := hb a List.mem_cons_self
    obtain ⟨hhead, htail⟩ := List.pairwise_cons.mp hp
    have hlen := ih (a + 1) htail (by
      intro x hx
      exact ⟨Nat.succ_le_of_lt (hhead x hx), (hb x (List.mem_cons_of_mem a hx)).2⟩)
    simp only [List.length_cons]
    omega

theorem AlignmentWith.length_le {σ : CrossSubst} {L R : List CrossPred}
    {pairs : List (Nat × Nat)} (h : AlignmentWith σ L R pairs) :
    pairs.length ≤ L.length ∧ pairs.length ≤ R.length := by
  constructor
  · have hb : ∀ i ∈ pairs.map Prod.fst, 0 ≤ i ∧ i < L.length := by
      intro i hi
      obtain ⟨⟨a, b⟩, hp, heq⟩ := List.mem_map.mp hi
      dsimp at heq
      subst a
      obtain ⟨p, q, hp, _, _, _⟩ := h.matched i b hp
      exact ⟨Nat.zero_le _, (List.getElem?_eq_some_iff.mp hp).1⟩
    simpa using strict_length_bound (pairs.map Prod.fst) L.length 0
      (List.pairwise_map.mpr h.leftStrict) hb
  · have hb : ∀ j ∈ pairs.map Prod.snd, 0 ≤ j ∧ j < R.length := by
      intro j hj
      obtain ⟨⟨a, b⟩, hp, heq⟩ := List.mem_map.mp hj
      dsimp at heq
      subst b
      obtain ⟨p, q, _, hq, _, _⟩ := h.matched a j hp
      exact ⟨Nat.zero_le _, (List.getElem?_eq_some_iff.mp hq).1⟩
    simpa using strict_length_bound (pairs.map Prod.snd) R.length 0
      (List.pairwise_map.mpr h.rightStrict) hb

theorem admissibleAlignment_length_le {L R : List CrossPred}
    {pairs : List (Nat × Nat)} (h : AdmissibleAlignment L R pairs) :
    pairs.length ≤ L.length ∧ pairs.length ≤ R.length := by
  obtain ⟨_, h⟩ := h
  exact h.length_le

namespace ObservationEqProofObligations

/-- Saturating either side certifies maximality against all admissible alignments. -/
theorem unify_maximum_of_saturated (L R : List CrossPred)
    (h : (unifyLists L R).pairs.length = L.length ∨
      (unifyLists L R).pairs.length = R.length) :
    MaximumAlignment L R (unifyLists L R).pairs := by
  refine ⟨unify_admissible L R, ?_⟩
  intro other ho
  obtain ⟨hl, hr⟩ := admissibleAlignment_length_le ho
  rcases h with h | h <;> omega

theorem unify_pass_maximum (L R : List CrossPred) (h : (unifyLists L R).pass = true) :
    MaximumAlignment L R (unifyLists L R).pairs := by
  exact unify_maximum_of_saturated L R (Or.inl ((unify_pass_iff_length L R).mp h).1)

private theorem head_payload_unique (l : Nat × CrossPred) (ls : List (Nat × CrossPred))
    (hs : (l :: ls).Pairwise (fun a b => a.1 < b.1)) (a : CrossPred)
    (hm : (l.1, a) ∈ l :: ls) : a = l.2 := by
  rcases List.mem_cons.mp hm with h | h
  · exact congrArg Prod.snd h
  · have hh := (List.pairwise_cons.mp hs).1 (l.1, a) h
    exact False.elim (Nat.lt_irrefl _ hh)

private theorem mem_drop_of_label_gt (R : List (Nat × CrossPred))
    (hs : R.Pairwise (fun a b => a.1 < b.1)) (k : Nat) (r b : Nat × CrossPred)
    (hr : R[k]? = some r) (hb : b ∈ R) (hlt : r.1 < b.1) :
    b ∈ R.drop (k + 1) := by
  induction R generalizing k with
  | nil => simp at hr
  | cons a R ih =>
    obtain ⟨hhead, htail⟩ := List.pairwise_cons.mp hs
    cases k with
    | zero =>
      have har : a = r := by simpa using hr
      subst r
      rcases List.mem_cons.mp hb with hb | hb
      · subst b; exact False.elim (Nat.lt_irrefl _ hlt)
      · simpa using hb
    | succ k =>
      have hr' : R[k]? = some r := by simpa using hr
      have har := hhead r (List.mem_of_getElem? hr')
      have hb' : b ∈ R := by
        rcases List.mem_cons.mp hb with hb | hb
        · subst b; omega
        · exact hb
      simpa using ih htail k hr' hb'

/-- Every independently witnessed increasing alignment is covered by a search branch. -/
theorem search_dominates_alignment (L R : List (Nat × CrossPred)) (σ υ : CrossSubst)
    (pairs : List (Nat × Nat))
    (hL : L.Pairwise (fun a b => a.1 < b.1))
    (hR : R.Pairwise (fun a b => a.1 < b.1))
    (hi : CrossSubst.Injective σ) (hj : CrossSubst.Injective υ)
    (he : CrossSubst.Extends σ υ)
    (hl : pairs.Pairwise (fun a b => a.1 < b.1))
    (hr : pairs.Pairwise (fun a b => a.2 < b.2))
    (hm : ∀ i j, (i, j) ∈ pairs →
      ∃ a b, (i, a) ∈ L ∧ (j, b) ∈ R ∧
        CrossSubst.DeterminedPred υ a ∧ CrossSubst.rename υ a = b) :
    pairs.length ≤ (search L R σ).size := by
  induction L generalizing R σ pairs with
  | nil =>
    cases pairs with
    | nil => simp [search]
    | cons p ps =>
      obtain ⟨a, b, ha, _⟩ := hm p.1 p.2 List.mem_cons_self
      simp at ha
  | cons l ls ih =>
    cases pairs with
    | nil => exact Nat.zero_le _
    | cons p ps =>
      obtain ⟨al, ar, hal, har, hd, ht⟩ := hm p.1 p.2 List.mem_cons_self
      obtain ⟨hpl, htl⟩ := List.pairwise_cons.mp hl
      obtain ⟨hpr, htr⟩ := List.pairwise_cons.mp hr
      obtain ⟨hhead, htail⟩ := List.pairwise_cons.mp hL
      by_cases hp : p.1 = l.1
      · have ha : al = l.2 := head_payload_unique l ls hL al (by simpa [hp] using hal)
        subst al
        obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp har
        obtain ⟨τ, hmerge, hτυ⟩ :=
          CrossSubst.mergePred_complete σ υ l.2 hi hj he hd
        rw [ht] at hmerge
        have hiτ := (CrossSubst.ProofObligations.mergePred_sound σ τ l.2 ar hi hmerge).2.1
        have hrest : ∀ i j, (i, j) ∈ ps →
            ∃ a b, (i, a) ∈ ls ∧ (j, b) ∈ R.drop (k + 1) ∧
              CrossSubst.DeterminedPred υ a ∧ CrossSubst.rename υ a = b := by
          intro i j hij
          obtain ⟨a, b, ha, hb, hd, ht⟩ := hm i j (List.mem_cons_of_mem _ hij)
          have hil := hpl (i, j) hij
          have hjr := hpr (i, j) hij
          have ha' : (i, a) ∈ ls := by
            rcases List.mem_cons.mp ha with ha | ha
            · have heq := congrArg Prod.fst ha
              dsimp at heq
              omega
            · exact ha
          exact ⟨a, b, ha', mem_drop_of_label_gt R hR k (p.2, ar) (j, b)
            hk hb hjr, hd, ht⟩
        have hb := ih (R.drop (k + 1)) τ ps htail
          (hR.sublist (List.drop_sublist _ _)) hiτ hτυ htl htr hrest
        have hc := search_ge_branch l ls R σ τ k (p.2, ar) hk hmerge
        simp only [List.length_cons]
        omega
      · have hfirst : (p.1, al) ∈ ls := by
          rcases List.mem_cons.mp hal with hal | hal
          · have heq := congrArg Prod.fst hal
            exact False.elim (hp heq)
          · exact hal
        have hlt := hhead (p.1, al) hfirst
        have hrest : ∀ i j, (i, j) ∈ p :: ps →
            ∃ a b, (i, a) ∈ ls ∧ (j, b) ∈ R ∧
              CrossSubst.DeterminedPred υ a ∧ CrossSubst.rename υ a = b := by
          intro i j hij
          obtain ⟨a, b, ha, hb, hd, ht⟩ := hm i j hij
          have hne : i ≠ l.1 := by
            rcases List.mem_cons.mp hij with hij | hij
            · have heq := congrArg Prod.fst hij
              dsimp at heq
              omega
            · have hpi := hpl (i, j) hij
              omega
          have ha' : (i, a) ∈ ls := by
            rcases List.mem_cons.mp ha with ha | ha
            · exact False.elim (hne (congrArg Prod.fst ha))
            · exact ha
          exact ⟨a, b, ha', hb, hd, ht⟩
        exact Nat.le_trans (ih R σ (p :: ps) htail hR hi he hl hr hrest)
          (search_ge_skip l ls R σ)

private theorem indexed_get_mem (L : List CrossPred) (i : Nat) (a : CrossPred)
    (h : L[i]? = some a) : (i, a) ∈ (List.range L.length).zip L := by
  apply List.mem_iff_getElem?.mpr
  exact ⟨i, List.getElem?_zip_eq_some.mpr
    ⟨List.getElem?_range (List.getElem?_eq_some_iff.mp h).1, h⟩⟩

/-- General maximality includes non-saturated outputs and uses the independent relation. -/
theorem unify_maximum (L R : List CrossPred) :
    MaximumAlignment L R (unifyLists L R).pairs := by
  refine ⟨unify_admissible L R, ?_⟩
  intro other ho
  obtain ⟨υ, hυ⟩ := ho
  have hi : CrossSubst.Injective .empty := by
    simp [CrossSubst.Injective, CrossSubst.empty]
  have he : CrossSubst.Extends .empty υ := by
    simp [CrossSubst.Extends, CrossSubst.empty]
  have hL : ((List.range L.length).zip L).Pairwise (fun a b => a.1 < b.1) := by
    apply List.pairwise_map.mp
    simpa only [List.map_fst_zip (l₁ := List.range L.length) (l₂ := L) (by simp)] using
      (List.pairwise_lt_range : (List.range L.length).Pairwise (· < ·))
  have hR : ((List.range R.length).zip R).Pairwise (fun a b => a.1 < b.1) := by
    apply List.pairwise_map.mp
    simpa only [List.map_fst_zip (l₁ := List.range R.length) (l₂ := R) (by simp)] using
      (List.pairwise_lt_range : (List.range R.length).Pairwise (· < ·))
  have hdom := search_dominates_alignment
    ((List.range L.length).zip L) ((List.range R.length).zip R) .empty υ other
    hL hR hi hυ.injective he hυ.leftStrict hυ.rightStrict (by
      intro i j hij
      obtain ⟨a, b, ha, hb, hd, ht⟩ := hυ.matched i j hij
      exact ⟨a, b, indexed_get_mem L i a ha, indexed_get_mem R j b hb, hd, ht⟩)
  change other.length ≤ (search ((List.range L.length).zip L)
    ((List.range R.length).zip R) .empty).pairs.length
  rw [← (search_structure _ _ .empty).1]
  exact hdom

theorem unify_cardinality_swap (L R : List CrossPred) :
    (unifyLists L R).pairs.length = (unifyLists R L).pairs.length := by
  have hLR := unify_maximum L R
  have hRL := unify_maximum R L
  have h₁ := hLR.2 ((unifyLists R L).pairs.map Prod.swap)
    (admissibleAlignment_swap hRL.1)
  have h₂ := hRL.2 ((unifyLists L R).pairs.map Prod.swap)
    (admissibleAlignment_swap hLR.1)
  simp only [List.length_map] at h₁ h₂
  omega

theorem unify_pass_swap (L R : List CrossPred) :
    (unifyLists L R).pass = (unifyLists R L).pass := by
  apply Bool.eq_iff_iff.mpr
  rw [unify_pass_iff_length, unify_pass_iff_length, unify_cardinality_swap]
  omega

/-- Uniqueness concerns pair lists; substitution witnesses need not be unique. -/
theorem unify_pairs_swap_of_unique (L R : List CrossPred)
    (hu : ¬ AmbiguousMaximum L R) :
    (unifyLists R L).pairs = (unifyLists L R).pairs.map Prod.swap := by
  have hLR := unify_maximum L R
  have hRL := maximumAlignment_swap (unify_maximum R L)
  have heq : (unifyLists R L).pairs.map Prod.swap = (unifyLists L R).pairs := by
    apply Classical.byContradiction
    intro hn
    exact hu ⟨_, _, hRL, hLR, hn⟩
  have hback := congrArg (List.map Prod.swap) heq
  simpa only [List.map_map, Prod.swap_swap_eq, List.map_id] using hback

private theorem unify_onlyLeft_eq (L R : List CrossPred) :
    (unifyLists L R).onlyLeft =
      (List.range L.length).filter
        (fun i => !(unifyLists L R).pairs.any (fun p => p.1 == i)) := rfl

private theorem unify_onlyRight_eq (L R : List CrossPred) :
    (unifyLists L R).onlyRight =
      (List.range R.length).filter
        (fun j => !(unifyLists L R).pairs.any (fun p => p.2 == j)) := rfl

theorem unify_only_swap_of_pairs (L R : List CrossPred)
    (hp : (unifyLists R L).pairs = (unifyLists L R).pairs.map Prod.swap) :
    (unifyLists R L).onlyLeft = (unifyLists L R).onlyRight ∧
      (unifyLists R L).onlyRight = (unifyLists L R).onlyLeft := by
  constructor
  · rw [unify_onlyLeft_eq, unify_onlyRight_eq, hp]
    simp only [List.any_map, Function.comp_def, Prod.swap]
  · rw [unify_onlyRight_eq, unify_onlyLeft_eq, hp]
    simp only [List.any_map, Function.comp_def, Prod.swap]

theorem unify_only_swap_of_unique (L R : List CrossPred)
    (hu : ¬ AmbiguousMaximum L R) :
    (unifyLists R L).onlyLeft = (unifyLists L R).onlyRight ∧
      (unifyLists R L).onlyRight = (unifyLists L R).onlyLeft :=
  unify_only_swap_of_pairs L R (unify_pairs_swap_of_unique L R hu)

private def TaggedAlignment (σ : CrossSubst) (L R : List (Nat × CrossPred))
    (pairs : List (Nat × Nat)) : Prop :=
  ∃ υ, CrossSubst.Injective υ ∧ CrossSubst.Extends σ υ ∧
    pairs.Pairwise (fun a b => a.1 < b.1) ∧
    pairs.Pairwise (fun a b => a.2 < b.2) ∧
    ∀ i j, (i, j) ∈ pairs →
      ∃ a b, (i, a) ∈ L ∧ (j, b) ∈ R ∧
        CrossSubst.DeterminedPred υ a ∧ CrossSubst.rename υ a = b

private theorem tagged_search (L R : List (Nat × CrossPred)) (σ : CrossSubst)
    (hL : L.Pairwise (fun a b => a.1 < b.1))
    (hR : R.Pairwise (fun a b => a.1 < b.1))
    (hi : CrossSubst.Injective σ) :
    TaggedAlignment σ L R (search L R σ).pairs := by
  obtain ⟨he, hj, _⟩ := search_sound L R σ hi
  obtain ⟨_, hl, hr⟩ := search_structure L R σ
  refine ⟨_, hj, he, ?_, ?_, search_pairs_determined L R σ hi⟩
  · have hs : (L.map Prod.fst).Pairwise (· < ·) := List.pairwise_map.mpr hL
    exact List.pairwise_map.mp (hs.sublist hl)
  · have hs : (R.map Prod.fst).Pairwise (· < ·) := List.pairwise_map.mpr hR
    exact List.pairwise_map.mp (hs.sublist hr)

private theorem tagged_bound (L R : List (Nat × CrossPred)) (σ : CrossSubst)
    (hL : L.Pairwise (fun a b => a.1 < b.1))
    (hR : R.Pairwise (fun a b => a.1 < b.1))
    (hi : CrossSubst.Injective σ) (p : List (Nat × Nat))
    (hp : TaggedAlignment σ L R p) : p.length ≤ (search L R σ).size := by
  obtain ⟨υ, hj, he, hl, hr, hm⟩ := hp
  exact search_dominates_alignment L R σ υ p hL hR hi hj he hl hr hm

private theorem tagged_skip (l : Nat × CrossPred) (ls R : List (Nat × CrossPred))
    (σ : CrossSubst) (p : List (Nat × Nat))
    (hp : TaggedAlignment σ ls R p) : TaggedAlignment σ (l :: ls) R p := by
  obtain ⟨υ, hj, he, hl, hr, hm⟩ := hp
  refine ⟨υ, hj, he, hl, hr, ?_⟩
  intro i j hij
  obtain ⟨a, b, ha, hb, hd, ht⟩ := hm i j hij
  exact ⟨a, b, List.mem_cons_of_mem _ ha, hb, hd, ht⟩

private theorem drop_label_gt (R : List (Nat × CrossPred))
    (hR : R.Pairwise (fun a b => a.1 < b.1))
    (k : Nat) (r b : Nat × CrossPred)
    (hr : R[k]? = some r) (hb : b ∈ R.drop (k + 1)) : r.1 < b.1 := by
  induction R generalizing k with
  | nil => simp at hr
  | cons a R ih =>
    obtain ⟨hh, ht⟩ := List.pairwise_cons.mp hR
    cases k with
    | zero =>
      have har : a = r := by simpa using hr
      subst r
      exact hh b (by simpa using hb)
    | succ k =>
      exact ih ht k (by simpa using hr) (by simpa using hb)

private theorem tagged_cons (l : Nat × CrossPred) (ls R : List (Nat × CrossPred))
    (σ τ : CrossSubst) (k : Nat) (r : Nat × CrossPred)
    (hL : (l :: ls).Pairwise (fun a b => a.1 < b.1))
    (hR : R.Pairwise (fun a b => a.1 < b.1))
    (hi : CrossSubst.Injective σ)
    (hg : R[k]? = some r) (hm : CrossSubst.mergePred σ l.2 r.2 = some τ)
    (p : List (Nat × Nat)) (hp : TaggedAlignment τ ls (R.drop (k + 1)) p) :
    TaggedAlignment σ (l :: ls) R ((l.1, r.1) :: p) := by
  obtain ⟨υ, hj, he, hl, hr, hmatched⟩ := hp
  obtain ⟨he₀, hiτ, ht⟩ := CrossSubst.mergePred_spec σ τ l.2 r.2 hi hm
  refine ⟨υ, hj, CrossSubst.extends_trans he₀ he, ?_, ?_, ?_⟩
  · apply List.pairwise_cons.mpr
    refine ⟨?_, hl⟩
    intro q hq
    obtain ⟨a, b, ha, _, _, _⟩ := hmatched q.1 q.2 hq
    exact (List.pairwise_cons.mp hL).1 (q.1, a) ha
  · apply List.pairwise_cons.mpr
    refine ⟨?_, hr⟩
    intro q hq
    obtain ⟨a, b, _, hb, _, _⟩ := hmatched q.1 q.2 hq
    exact drop_label_gt R hR k r (q.2, b) hg hb
  · intro i j hij
    rcases List.mem_cons.mp hij with hij | hij
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hij
      exact ⟨l.2, r.2, by simp, List.mem_of_getElem? hg,
        CrossSubst.determinedPred_extends he hiτ hj l.2
          (CrossSubst.mergePred_determined σ τ l.2 r.2 hi hm),
        ht υ he hj⟩
    · obtain ⟨a, b, ha, hb, hd, ht⟩ := hmatched i j hij
      exact ⟨a, b, List.mem_cons_of_mem _ ha, List.mem_of_mem_drop hb, hd, ht⟩

private theorem strict_tag_index_unique (R : List (Nat × CrossPred))
    (hR : R.Pairwise (fun a b => a.1 < b.1))
    (k j : Nat) (r s : Nat × CrossPred)
    (hr : R[k]? = some r) (hs : R[j]? = some s) (he : r.1 = s.1) : k = j := by
  induction R generalizing k j with
  | nil => simp at hr
  | cons a R ih =>
    obtain ⟨hh, ht⟩ := List.pairwise_cons.mp hR
    cases k with
    | zero =>
      have har : a = r := by simpa using hr
      subst r
      cases j with
      | zero => rfl
      | succ j =>
        have hs' : R[j]? = some s := by simpa using hs
        have hlt := hh s (List.mem_of_getElem? hs')
        omega
    | succ k =>
      have hr' : R[k]? = some r := by simpa using hr
      cases j with
      | zero =>
        have has : a = s := by simpa using hs
        subst s
        have hlt := hh r (List.mem_of_getElem? hr')
        omega
      | succ j =>
        exact congrArg Nat.succ (ih ht k j hr' (by simpa using hs))

private theorem filterMap_nodup_of_separated {α β : Type} (f : α → Option β)
    (xs : List α)
    (hs : xs.Pairwise (fun a b => ∀ x y, f a = some x → f b = some y → x ≠ y)) :
    (xs.filterMap f).Nodup := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    obtain ⟨hh, ht⟩ := List.pairwise_cons.mp hs
    cases ha : f a with
    | none => simpa [ha] using ih ht
    | some b =>
      simp only [List.filterMap_cons, ha]
      apply List.nodup_cons.mpr
      refine ⟨?_, ih ht⟩
      intro hb
      obtain ⟨c, hc, hcb⟩ := List.mem_filterMap.mp hb
      exact hh c hc b b ha hcb rfl

private def matchBranch (l : Nat × CrossPred) (ls R : List (Nat × CrossPred))
    (σ : CrossSubst) (k : Nat) : Option Match := do
  let r ← R[k]?
  let τ ← CrossSubst.mergePred σ l.2 r.2
  let s := search ls (R.drop (k + 1)) τ
  pure ⟨s.size + 1, s.subst, (l.1, r.1) :: s.pairs, s.ambiguous⟩

private theorem matchBranch_some (l : Nat × CrossPred) (ls R : List (Nat × CrossPred))
    (σ : CrossSubst) (k : Nat) (m : Match) (hm : matchBranch l ls R σ k = some m) :
    ∃ r τ, R[k]? = some r ∧ CrossSubst.mergePred σ l.2 r.2 = some τ ∧
      m = ⟨(search ls (R.drop (k + 1)) τ).size + 1,
        (search ls (R.drop (k + 1)) τ).subst,
        (l.1, r.1) :: (search ls (R.drop (k + 1)) τ).pairs,
        (search ls (R.drop (k + 1)) τ).ambiguous⟩ := by
  unfold matchBranch at hm
  cases hg : R[k]? with
  | none => simp [hg] at hm
  | some r =>
    cases hmerge : CrossSubst.mergePred σ l.2 r.2 with
    | none => simp [hg, hmerge] at hm
    | some τ =>
      exact ⟨r, τ, rfl, hmerge, by simpa [hg, hmerge] using hm.symm⟩

/-- Strict labels separate the skip branch from every current-left branch. -/
private theorem search_candidate_pairs_nodup
    (l : Nat × CrossPred) (ls R : List (Nat × CrossPred)) (σ : CrossSubst)
    (hL : (l :: ls).Pairwise (fun a b => a.1 < b.1))
    (hR : R.Pairwise (fun a b => a.1 < b.1)) :
    (((search ls R σ) :: (List.range R.length).filterMap
      (matchBranch l ls R σ)).map Match.pairs).Nodup := by
  have hbranches :
      (((List.range R.length).filterMap (matchBranch l ls R σ)).map Match.pairs).Nodup := by
    rw [List.map_filterMap]
    apply filterMap_nodup_of_separated
    apply List.pairwise_lt_range.imp
    intro k j hkj x y hx hy
    obtain ⟨m, hm, hmx⟩ := Option.map_eq_some_iff.mp hx
    obtain ⟨n, hn, hny⟩ := Option.map_eq_some_iff.mp hy
    obtain ⟨r, τ, hg, hmerge, rfl⟩ := matchBranch_some l ls R σ k m hm
    obtain ⟨s, υ, hj, hmerge', rfl⟩ := matchBranch_some l ls R σ j n hn
    intro heq
    have hp : (l.1, r.1) :: (search ls (R.drop (k + 1)) τ).pairs =
        (l.1, s.1) :: (search ls (R.drop (j + 1)) υ).pairs := hmx.trans (heq.trans hny.symm)
    have hrs : r.1 = s.1 := congrArg Prod.snd (List.cons.inj hp).1
    have hkj' := strict_tag_index_unique R hR k j r s hg hj hrs
    omega
  apply List.nodup_cons.mpr
  refine ⟨?_, hbranches⟩
  intro hm
  obtain ⟨m, hm, hp⟩ := List.mem_map.mp hm
  obtain ⟨k, _, hkm⟩ := List.mem_filterMap.mp hm
  obtain ⟨r, τ, hg, hmerge, rfl⟩ := matchBranch_some l ls R σ k m hkm
  have hleft := (search_structure ls R σ).2.1
  have hmem : l.1 ∈ (search ls R σ).pairs.map Prod.fst := by
    rw [← hp]
    simp
  obtain ⟨a, ha, heq⟩ := List.mem_map.mp (hleft.subset hmem)
  have hlt := (List.pairwise_cons.mp hL).1 a ha
  omega

/-- The Boolean detects distinct maximum pair lists, rather than distinct substitutions. -/
private theorem search_ambiguity (L R : List (Nat × CrossPred)) (σ : CrossSubst)
    (hL : L.Pairwise (fun a b => a.1 < b.1))
    (hR : R.Pairwise (fun a b => a.1 < b.1))
    (hi : CrossSubst.Injective σ) :
    (search L R σ).ambiguous = true ↔
      ∃ p, TaggedAlignment σ L R p ∧ p.length = (search L R σ).size ∧
        p ≠ (search L R σ).pairs := by
  induction L generalizing R σ with
  | nil =>
    constructor
    · simp [search]
    · rintro ⟨p, _, hl, hn⟩
      have hz : p.length = 0 := by simpa only [search] using hl
      have hp : p = [] := by
        cases p with
        | nil => rfl
        | cons a ps => simp at hz
      exact False.elim (hn (by simpa only [search] using hp))
  | cons l ls ih =>
    have htail := (List.pairwise_cons.mp hL).2
    let skip := search ls R σ
    let branches := (List.range R.length).filterMap (matchBranch l ls R σ)
    have hskip : TaggedAlignment σ (l :: ls) R skip.pairs :=
      tagged_skip l ls R σ _ (tagged_search ls R σ htail hR hi)
    have hbranch : ∀ m ∈ branches, TaggedAlignment σ (l :: ls) R m.pairs := by
      intro m hm
      obtain ⟨k, _, hkm⟩ := List.mem_filterMap.mp hm
      obtain ⟨r, τ, hg, hmerge, rfl⟩ := matchBranch_some l ls R σ k m hkm
      have hiτ := (CrossSubst.mergePred_spec σ τ l.2 r.2 hi hmerge).2.1
      exact tagged_cons l ls R σ τ k r hL hR hi hg hmerge _
        (tagged_search ls (R.drop (k + 1)) τ htail
          (hR.sublist (List.drop_sublist _ _)) hiτ)
    rw [search]
    apply chooseMatch_ambiguity_certificate
      (skip :: branches) skip (TaggedAlignment σ (l :: ls) R)
    · simp
    · exact search_candidate_pairs_nodup l ls R σ hL hR
    · intro m hm
      rcases List.mem_cons.mp hm with hm | hm
      · subst m
        exact (search_structure ls R σ).1.symm
      · obtain ⟨k, _, hkm⟩ := List.mem_filterMap.mp hm
        obtain ⟨r, τ, hg, hmerge, rfl⟩ := matchBranch_some l ls R σ k m hkm
        have hn := (search_structure ls (R.drop (k + 1)) τ).1
        dsimp
        omega
    · intro m hm
      rcases List.mem_cons.mp hm with hm | hm
      · subst m; exact hskip
      · exact hbranch m hm
    · intro m hm hamb
      rcases List.mem_cons.mp hm with hm | hm
      · subst m
        obtain ⟨p, hp, hl, hn⟩ := (ih R σ htail hR hi).mp hamb
        exact ⟨p, tagged_skip l ls R σ p hp, hl, hn⟩
      · obtain ⟨k, _, hkm⟩ := List.mem_filterMap.mp hm
        obtain ⟨r, τ, hg, hmerge, rfl⟩ := matchBranch_some l ls R σ k m hkm
        have hiτ := (CrossSubst.mergePred_spec σ τ l.2 r.2 hi hmerge).2.1
        obtain ⟨p, hp, hl, hn⟩ := (ih (R.drop (k + 1)) τ htail
          (hR.sublist (List.drop_sublist _ _)) hiτ).mp hamb
        refine ⟨(l.1, r.1) :: p,
          tagged_cons l ls R σ τ k r hL hR hi hg hmerge p hp, ?_, ?_⟩
        · simpa only [List.length_cons] using congrArg (· + 1) hl
        · intro heq
          exact hn (List.cons.inj heq).2
    · intro p hp hlen
      have hlen : p.length = (search (l :: ls) R σ).size := by
        rw [search]
        exact hlen
      suffices ∃ m ∈ skip :: branches,
          m.size = (search (l :: ls) R σ).size ∧
            (p = m.pairs ∨ m.ambiguous = true) by
        obtain ⟨m, hm, hs, hp⟩ := this
        refine ⟨m, hm, ?_, hp⟩
        rw [search] at hs
        exact hs
      have skip_cover (q : List (Nat × Nat)) (hq : TaggedAlignment σ ls R q)
          (hlen : q.length = (search (l :: ls) R σ).size) :
          ∃ m ∈ skip :: branches,
            m.size = (search (l :: ls) R σ).size ∧
              (q = m.pairs ∨ m.ambiguous = true) := by
        have hb := tagged_bound ls R σ htail hR hi q hq
        have hg := search_ge_skip l ls R σ
        have heq : q.length = skip.size := by dsimp [skip]; omega
        refine ⟨skip, List.mem_cons_self, by omega, ?_⟩
        by_cases hs : q = skip.pairs
        · exact Or.inl hs
        · exact Or.inr ((ih R σ htail hR hi).mpr ⟨q, hq, heq, hs⟩)
      obtain ⟨υ, hj, he, hl, hr, hm⟩ := hp
      cases p with
      | nil =>
        apply skip_cover [] _ hlen
        exact ⟨υ, hj, he, by simp, by simp, by simp⟩
      | cons p ps =>
        obtain ⟨al, ar, hal, har, hd, ht⟩ := hm p.1 p.2 List.mem_cons_self
        obtain ⟨hpl, htl⟩ := List.pairwise_cons.mp hl
        obtain ⟨hpr, htr⟩ := List.pairwise_cons.mp hr
        obtain ⟨hhead, _⟩ := List.pairwise_cons.mp hL
        by_cases hp : p.1 = l.1
        · have ha : al = l.2 := head_payload_unique l ls hL al (by simpa [hp] using hal)
          subst al
          obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp har
          obtain ⟨τ, hmerge, hτυ⟩ :=
            CrossSubst.mergePred_complete σ υ l.2 hi hj he hd
          rw [ht] at hmerge
          have hiτ := (CrossSubst.mergePred_spec σ τ l.2 ar hi hmerge).2.1
          have hps : TaggedAlignment τ ls (R.drop (k + 1)) ps := by
            refine ⟨υ, hj, hτυ, htl, htr, ?_⟩
            intro i j hij
            obtain ⟨a, b, ha, hb, hd, ht⟩ := hm i j (List.mem_cons_of_mem _ hij)
            have hil := hpl (i, j) hij
            have hjr := hpr (i, j) hij
            have ha' : (i, a) ∈ ls := by
              rcases List.mem_cons.mp ha with ha | ha
              · have heq := congrArg Prod.fst ha
                dsimp at heq
                omega
              · exact ha
            exact ⟨a, b, ha',
              mem_drop_of_label_gt R hR k (p.2, ar) (j, b) hk hb hjr, hd, ht⟩
          have hb := tagged_bound ls (R.drop (k + 1)) τ htail
            (hR.sublist (List.drop_sublist _ _)) hiτ ps hps
          have hg := search_ge_branch l ls R σ τ k (p.2, ar) hk hmerge
          have heq : ps.length = (search ls (R.drop (k + 1)) τ).size := by
            simp only [List.length_cons] at hlen
            omega
          let m : Match := ⟨(search ls (R.drop (k + 1)) τ).size + 1,
            (search ls (R.drop (k + 1)) τ).subst,
            (l.1, p.2) :: (search ls (R.drop (k + 1)) τ).pairs,
            (search ls (R.drop (k + 1)) τ).ambiguous⟩
          refine ⟨m, List.mem_cons_of_mem _ ?_, ?_, ?_⟩
          · apply List.mem_filterMap.mpr
            exact ⟨k, List.mem_range.mpr (List.getElem?_eq_some_iff.mp hk).1,
              by simp [matchBranch, hk, hmerge, m]⟩
          · dsimp [m]
            simp only [List.length_cons] at hlen
            omega
          · by_cases hs : ps = (search ls (R.drop (k + 1)) τ).pairs
            · left
              change p :: ps =
                (l.1, p.2) :: (search ls (R.drop (k + 1)) τ).pairs
              have hpPair : p = (l.1, p.2) := Prod.ext hp rfl
              rw [hpPair, hs]
            · right
              exact (ih (R.drop (k + 1)) τ htail
                (hR.sublist (List.drop_sublist _ _)) hiτ).mpr ⟨ps, hps, heq, hs⟩
        · have hfirst : (p.1, al) ∈ ls := by
            rcases List.mem_cons.mp hal with hal | hal
            · exact False.elim (hp (congrArg Prod.fst hal))
            · exact hal
          have hlt := hhead (p.1, al) hfirst
          apply skip_cover (p :: ps) _ hlen
          refine ⟨υ, hj, he, hl, hr, ?_⟩
          intro i j hij
          obtain ⟨a, b, ha, hb, hd, ht⟩ := hm i j hij
          have hne : i ≠ l.1 := by
            rcases List.mem_cons.mp hij with hij | hij
            · have heq := congrArg Prod.fst hij
              dsimp at heq
              omega
            · have hpi := hpl (i, j) hij
              omega
          have ha' : (i, a) ∈ ls := by
            rcases List.mem_cons.mp ha with ha | ha
            · exact False.elim (hne (congrArg Prod.fst ha))
            · exact ha
          exact ⟨a, b, ha', hb, hd, ht⟩

private theorem indexed_payload (L : List CrossPred) (i : Nat) (a : CrossPred)
    (h : (i, a) ∈ (List.range L.length).zip L) : L[i]? = some a := by
  obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp h
  obtain ⟨hi, ha⟩ := List.getElem?_zip_eq_some.mp hk
  have hlt : k < L.length := by
    simpa using (List.getElem?_eq_some_iff.mp hi).1
  have heq : k = i := by simpa [List.getElem?_range hlt] using hi
  simpa [heq] using ha

private theorem indexed_strict (L : List CrossPred) :
    ((List.range L.length).zip L).Pairwise (fun a b => a.1 < b.1) := by
  apply List.pairwise_map.mp
  simpa only [List.map_fst_zip (l₁ := List.range L.length) (l₂ := L) (by simp)] using
    (List.pairwise_lt_range : (List.range L.length).Pairwise (· < ·))

private theorem tagged_indexed_iff (L R : List CrossPred) (p : List (Nat × Nat)) :
    TaggedAlignment .empty ((List.range L.length).zip L)
      ((List.range R.length).zip R) p ↔ AdmissibleAlignment L R p := by
  constructor
  · rintro ⟨υ, hi, _, hl, hr, hm⟩
    refine ⟨υ, hi, hl, hr, ?_⟩
    intro i j hij
    obtain ⟨a, b, ha, hb, hd, ht⟩ := hm i j hij
    exact ⟨a, b, indexed_payload L i a ha, indexed_payload R j b hb, hd, ht⟩
  · rintro ⟨υ, hυ⟩
    refine ⟨υ, hυ.injective, ?_, hυ.leftStrict, hυ.rightStrict, ?_⟩
    · simp [CrossSubst.Extends, CrossSubst.empty]
    · intro i j hij
      obtain ⟨a, b, ha, hb, hd, ht⟩ := hυ.matched i j hij
      exact ⟨a, b, indexed_get_mem L i a ha, indexed_get_mem R j b hb, hd, ht⟩

theorem unify_ambiguous_iff (L R : List CrossPred) :
    (unifyLists L R).ambiguous = true ↔ AmbiguousMaximum L R := by
  have hi : CrossSubst.Injective .empty := by
    simp [CrossSubst.Injective, CrossSubst.empty]
  have hc := search_ambiguity ((List.range L.length).zip L)
    ((List.range R.length).zip R) .empty (indexed_strict L) (indexed_strict R) hi
  have hs := (search_structure ((List.range L.length).zip L)
    ((List.range R.length).zip R) .empty).1
  have hmax := unify_maximum L R
  constructor
  · intro hamb
    obtain ⟨p, hp, hl, hn⟩ := hc.mp hamb
    have had := (tagged_indexed_iff L R p).mp hp
    have hlen : p.length = (unifyLists L R).pairs.length := hl.trans hs
    have hpm : MaximumAlignment L R p := by
      refine ⟨had, ?_⟩
      intro q hq
      exact Nat.le_trans (hmax.2 q hq) (Nat.le_of_eq hlen.symm)
    exact ⟨p, (unifyLists L R).pairs, hpm, hmax, hn⟩
  · rintro ⟨a, b, ha, hb, hne⟩
    have hlen (p : List (Nat × Nat)) (hp : MaximumAlignment L R p) :
        p.length = (unifyLists L R).pairs.length :=
      Nat.le_antisymm (hmax.2 p hp.1) (hp.2 _ hmax.1)
    have witness : ∃ p, MaximumAlignment L R p ∧ p ≠ (unifyLists L R).pairs := by
      by_cases he : a = (unifyLists L R).pairs
      · exact ⟨b, hb, fun h => hne (he.trans h.symm)⟩
      · exact ⟨a, ha, he⟩
    obtain ⟨p, hp, hn⟩ := witness
    apply hc.mpr
    exact ⟨p, (tagged_indexed_iff L R p).mpr hp.1, (hlen p hp).trans hs.symm, hn⟩

theorem unify_ambiguous_swap (L R : List CrossPred) :
    (unifyLists L R).ambiguous = (unifyLists R L).ambiguous := by
  apply Bool.eq_iff_iff.mpr
  rw [unify_ambiguous_iff, unify_ambiguous_iff, ambiguousMaximum_swap_iff]

theorem unify_pairs_swap_of_unambiguous (L R : List CrossPred)
    (hu : (unifyLists L R).ambiguous = false) :
    (unifyLists R L).pairs = (unifyLists L R).pairs.map Prod.swap := by
  apply unify_pairs_swap_of_unique L R
  intro ha
  have ht := (unify_ambiguous_iff L R).mpr ha
  rw [hu] at ht
  exact Bool.noConfusion ht

theorem unify_only_swap_of_unambiguous (L R : List CrossPred)
    (hu : (unifyLists L R).ambiguous = false) :
    (unifyLists R L).onlyLeft = (unifyLists L R).onlyRight ∧
      (unifyLists R L).onlyRight = (unifyLists L R).onlyLeft :=
  unify_only_swap_of_pairs L R (unify_pairs_swap_of_unambiguous L R hu)

/-- Repeated internal tags can make distinct branches export the same pair list. -/
theorem search_duplicate_tags_tie :
    let p : CrossPred := .ret ⟨.c 0⟩
    let out := search [(0, p), (0, p)] [(0, p)] .empty
    out.ambiguous = true ∧ out.pairs = [(0, 0)] := by
  decide +kernel

/-- With ties, first-maximizer selection need not commute with swapping inputs. -/
theorem unify_ambiguous_pairs_need_not_swap :
    let p : CrossPred := .ret ⟨.c 0⟩
    let L := [p]
    let R := [p, p]
    (unifyLists L R).ambiguous = true ∧
      (unifyLists R L).ambiguous = true ∧
      (unifyLists L R).pairs = [(0, 0)] ∧
      (unifyLists R L).pairs = [(1, 0)] ∧
      (unifyLists R L).pairs ≠ (unifyLists L R).pairs.map Prod.swap := by
  decide +kernel

/-- Compound keys use the ordinary recursive app case: packet-offset leaves and
the bound context cell participate in renaming; width, packet id and strictness do not. -/
theorem compoundPacket_apply (σ : CrossSubst) (p : CompoundPacketReg) :
    CrossSubst.applyTerm σ p.toCross =
      .app (.packetReg p.bytes) [.c p.κ, CrossSubst.applyTerm σ p.offset.toCross,
        .reg .context (σ.regLookup .context p.endCtx),
        .c (if p.strict then 1 else 0), .c p.byteIndex,
        CrossSubst.applyTerm σ p.checkedEnd.toCross] := by
  simp only [CompoundPacketReg.toCross, CrossSubst.applyTerm, CrossSubst.applyTerms]

theorem compoundPacket_determined (σ : CrossSubst) (p : CompoundPacketReg) :
    CrossSubst.Determined σ p.toCross ↔
      CrossSubst.Determined σ p.offset.toCross ∧
        (∃ b, σ.regImage? .context p.endCtx = some b) ∧
        CrossSubst.Determined σ p.checkedEnd.toCross := by
  simp [CompoundPacketReg.toCross, CrossSubst.Determined, CrossSubst.DeterminedTerms]

theorem compoundPacket_merge (σ τ : CrossSubst) (a b : CompoundPacketReg)
    (hi : σ.Injective) (h : CrossSubst.mergeTerm σ a.toCross b.toCross = some τ) :
    CrossSubst.Extends σ τ ∧ τ.Injective ∧
      CrossSubst.Determined τ a.toCross ∧ CrossSubst.applyTerm τ a.toCross = b.toCross :=
  CrossSubst.mergeTerm_spec σ τ a.toCross b.toCross hi h

theorem compoundPacket_determinedCond (σ : CrossSubst) (p : CompoundPacketReg)
    (r : CrossRel) (z : Int) :
    CrossSubst.DeterminedCond σ (.packetField p.toCross r z) ↔
      CrossSubst.Determined σ p.offset.toCross ∧
        (∃ b, σ.regImage? .context p.endCtx = some b) ∧
        CrossSubst.Determined σ p.checkedEnd.toCross :=
  compoundPacket_determined σ p

end ObservationEqProofObligations
end Core
