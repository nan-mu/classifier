import Verification.Verified.Acceptance
import Verification.Verified.HelperProjection
import Verification.Verified.HistoryAndPath
import Verification.Verified.SolveMeaning
import Verification.Verified.StateUpdate
import Verification.Verified.UnifyMatch

/-!
Sorry-free reading of the verifier.

`#print axioms` below is the dependency check for the theorems that carry the
semantic claims. `sorryAx` and `Node.BpfBound`'s axioms must not appear.
-/

#print axioms Verification.Verified.StateUpdate.assign_lookup
#print axioms Verification.Verified.StateUpdate.kept_lookup
#print axioms Verification.Verified.SolveMeaning.solve_preserves_interpretation
#print axioms Verification.Verified.HistoryAndPath.dependency_blocks_ignoring
#print axioms Verification.Verified.HistoryAndPath.linearTrace_of_step_preservation
#print axioms Verification.Verified.HistoryAndPath.drive_equal_states
#print axioms Verification.Verified.UnifyMatch.unify_structural
#print axioms Verification.Verified.Acceptance.distinct_helper_args_reject
#print axioms Verification.Verified.Acceptance.accept_is_structural
#print axioms Verification.Verified.Acceptance.meanings_if_arguments_survive
#print axioms Verification.Verified.HistoryAndPath.both_directions_rejected
