import Verification.Obligation
import Verification.Verified.UnifyMatch

namespace Verification.Verified.Acceptance

open Term Term.Value Expression Observation Match Verification.Obligation Verification.Verified.UnifyMatch

/-!
Acceptance is the index-aligned match of prepared observations.

`MeaningsAgree` does not follow. It still needs the shared valuation and
syntactic survival of the original arguments. RV32 safety is not derived from
eBPF safety here.
-/

theorem accept_is_structural (a : Accepts) :
    Subst.Injective (unifyLists a.left a.right).subst ∧
    (∀ i j, (i, j) ∈ matched a →
      ∃ u v,
        (a.left.map prepare)[i]? = some u ∧
        (a.right.map prepare)[j]? = some v ∧
        Subst.applyTerms (unifyLists a.left a.right).subst (comparedTerms u) =
          comparedTerms v) ∧
    (unifyLists a.left a.right).pairs.length = a.left.length ∧
    a.left.length = a.right.length := by
  have h := unify_structural a.left a.right
  have hlen := h.2.2.mp a.pass
  exact ⟨h.1, h.2.1, hlen.1, hlen.2⟩

/-- A helper argument is part of the comparison, so distinct flag constants do
not produce a passing match. -/
theorem distinct_helper_args_reject :
    (unifyLists
      [.helper .update [.C32 0]]
      [.helper .update [.C32 1]]).pass = false := by
  native_decide

/-- Conditional last step. `ValuationFollows`, `ArgsFaithful` and
`RenamePreservesArguments` are not proved. Entry, step, history and path
coverage are further premises of those three, not inputs of this function. -/
theorem meanings_if_arguments_survive
    (c : SharedCondition) (a : Accepts)
    (hval : ValuationFollows c a) (hren : RenamePreservesArguments c a)
    (hfaith : ArgsFaithful a) :
    MeaningsAgree c a := by
  exact ⟨hren hval hfaith, hval.2.2, hval.2.1⟩

end Verification.Verified.Acceptance
