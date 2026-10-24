import Node.Drive

namespace Verification.Unverified.Required.BranchDecision

open Core Node

/-!
`Node.live_constraint_excludes_both` in `Node/BpfBound.lean` is an axiom.
`Expr.decideWith` does not read a saved row, so the axiom is not a theorem
about `step`. After the row is deleted, the Linux checker can still explore
both successors while scalar ranges overlap. `both_directions_rejected` is the
proved driver reaction when both directions are actually returned.

The missing fact is the exclusion itself, from `step`, while the row is alive.
-/

/-- While `row` is still a row of `σ`, `step` does not return both directions. -/
def SavedRowExcludesBoth (step : Nat → State → StepResult) : Prop :=
  ∀ j σ row cs,
    row ∈ σ.exprs →
    step j σ = .candidates cs →
    cs.any (fun c => c.dir == .taken) = false ∨
    cs.any (fun c => c.dir == .notTaken) = false

/-- sorry: required obligation, not a proof. -/
theorem saved_row_excludes_both (step : Nat → State → StepResult) :
    SavedRowExcludesBoth step := by
  sorry

end Verification.Unverified.Required.BranchDecision
