import Match.Unify

namespace Verification.Verified.UnifyMatch

open Term Term.Value Expression Observation Match

/-!
`unifyLists` is an index-aligned match of prepared observations. The
substitution is injective. Each paired item's compared terms rename onto the
other item. `pass` is full coverage. The alignment is a single attempt, so it
does not report a second maximum.
-/

theorem unify_structural (L R : List Observation) :
    Subst.Injective (unifyLists L R).subst ∧
    (∀ i j, (i, j) ∈ (unifyLists L R).pairs →
      ∃ a b, (L.map prepare)[i]? = some a ∧ (R.map prepare)[j]? = some b ∧
        Subst.applyTerms (unifyLists L R).subst (comparedTerms a) = comparedTerms b) ∧
    ((unifyLists L R).pass = true ↔
      (unifyLists L R).pairs.length = L.length ∧ L.length = R.length) := by
  refine ⟨unify_subst_injective L R, ?_, unify_pass_iff_length L R⟩
  intro i j hij
  exact unify_pairs_sound L R i j hij

end Verification.Verified.UnifyMatch
