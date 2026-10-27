import Match.Unify

namespace Verification.Verified.HelperProjection

open Term Term.Value Expression Observation Match

/-!
Comparison reads the helper argument list after `solve`. A flags word is an
argument, so two updates that differ only there do not match.
-/

theorem prepare_keeps_helper (event : Nat) (kind : HelperKind) (args : List Term) :
    prepare (.helper event kind args) = .helper event kind (args.map solve) := by
  rfl

theorem compared_helper (event : Nat) (kind : HelperKind) (args : List Term) :
    comparedTerms (prepare (.helper event kind args)) = args.map solve := by
  simp [prepare, comparedTerms]

end Verification.Verified.HelperProjection
