import Inbox.Cross.Unify

namespace Verification.Verified.HelperProjection

open Term Term.Value Expression Observation Inbox.Cross

/-!
Comparison reads the helper argument list after `solve`. A flags word is an
argument, so two updates that differ only there do not match.
-/

theorem prepare_keeps_helper (kind : HelperKind) (args : List Term) :
    prepare (.helper kind args) = .helper kind (args.map solve) := by
  rfl

theorem compared_helper (kind : HelperKind) (args : List Term) :
    comparedTerms (prepare (.helper kind args)) = args.map solve := by
  simp [prepare, comparedTerms]

end Verification.Verified.HelperProjection
