import Verification.Obligation
import Verification.Verified.HistoryAndPath

namespace Verification.Unverified.Required.PathCoverage

open Core Node Verification.Obligation Verification.Verified.HistoryAndPath

/-!
`drive_equal_states` equates successors of equal states. It is not used for
`sameObservation`.

`sameObservation` stops the taken walk. The ordered observations of the
unexpanded suffix are `linearTrace_of_step_preservation` once
`History.ebpf_ignorable_step` is proved, including repetitions.
`duplicate_observation_is_dropped` is why the final `State.predicates`
list is not that record.

`CoveredSelection` is a premise on a particular `Accepts`. It is not true for
every structure that merely unifies, and it does not ask the verifier to
accept every equivalent program. There is no theorem `∀ a, CoveredSelection a`.
-/

/-- Some faithful per-step records of the completed graphs flatten to the
aligned lists. -/
def CoveredSelection (a : Accepts) : Prop :=
  ∃ (gL gR : RunGraph) (cL : Coverage gL) (cR : Coverage gR),
    ListsFromRuns a gL gR cL cR

theorem accumulated_predicates_drop_repeats
    (parent : State) (p : Predicate) (h : parent.predicates.contains p = true) :
    (update parent { exprs := [], predicates := [p] }).predicates = parent.predicates :=
  duplicate_observation_is_dropped parent p h

end Verification.Unverified.Required.PathCoverage
