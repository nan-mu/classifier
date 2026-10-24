import Core.Cross.UnifyProofs

namespace Verification.Verified.UnifyMatch

open Core ObservationEqProofObligations

/-!
One structural statement for `unifyLists`: the pairs are a maximum ordered
alignment, the substitution is injective, matched observations rename onto
each other, coverage is full length, and ambiguity is exactly the existence
of two distinct maximum alignments.

Renaming equality is syntactic. It does not identify variable values, resource
identities, or external results.
-/

theorem unify_structural
    (L R : List CrossPred) :
    CrossSubst.Injective (unifyLists L R).subst ∧
    MaximumAlignment L R (unifyLists L R).pairs ∧
    (∀ i j, (i, j) ∈ (unifyLists L R).pairs →
      ∃ a b, L[i]? = some a ∧ R[j]? = some b ∧
        CrossSubst.rename (unifyLists L R).subst a = b) ∧
    ((unifyLists L R).pass = true ↔
      (unifyLists L R).pairs.length = L.length ∧ L.length = R.length) ∧
    ((unifyLists L R).ambiguous = true ↔ AmbiguousMaximum L R) := by
  refine ⟨unify_subst_injective L R, unify_maximum L R, ?_, unify_pass_iff_length L R,
    unify_ambiguous_iff L R⟩
  intro i j hij
  exact unify_pairs_sound L R i j hij

/-- When the maximum alignment is unique, swapping the lists swaps the pairs
and the unmatched indices. Ambiguous inputs are excluded: `unify_ambiguous_pairs_need_not_swap`.
-/
theorem unify_unique_swap
    (L R : List CrossPred) (hu : (unifyLists L R).ambiguous = false) :
    (unifyLists R L).pairs = (unifyLists L R).pairs.map Prod.swap ∧
      (unifyLists R L).onlyLeft = (unifyLists L R).onlyRight ∧
      (unifyLists R L).onlyRight = (unifyLists L R).onlyLeft ∧
      (unifyLists L R).pass = (unifyLists R L).pass := by
  obtain ⟨hL, hR⟩ := unify_only_swap_of_unambiguous L R hu
  exact ⟨unify_pairs_swap_of_unambiguous L R hu, hL, hR, unify_pass_swap L R⟩

end Verification.Verified.UnifyMatch
