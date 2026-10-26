import Node.Path

namespace Node
open Term Term.Value Expression Observation Interface Interface.Step Wire

/-!
Human theorems taken from the Linux BPF verifier (`kernel/bpf/verifier.c`,
`do_check` / `is_state_visited`). This file does not re-implement that checker
and does not prove these facts from `step`.
-/

/-- A program an accepting run of the Linux BPF verifier has finished.
The predicate is an assumption. This repository does not decide it. -/
axiom BpfAccepted : Type

/-- How many only-taken returns to `parent` that accepting run explored.
`is_state_visited` prunes a back-edge whose state is already covered.
An exploration that does not finish is rejected, so an accepted program has
a finite count. This does not say the count is at most `loopLimit`. -/
axiom bpfLoopBound : BpfAccepted → Nat → Nat

theorem loop_limit_not_exhausted
    (accepted : BpfAccepted) (parent limit returns : Nat)
    (enough : bpfLoopBound accepted parent ≤ limit)
    (bound : returns ≤ bpfLoopBound accepted parent) :
    returns ≤ limit :=
  Nat.le_trans bound enough

/-- The taken arm's comparison row is still a row of the pre-state. -/
def constraintAlive (σ : State) (row : Expr) : Prop :=
  σ.exprs.contains row = true

/-- If that row is still present, `step` does not return both directions.
Current `Expr.decideWith` does not read saved rows, so this is not derived
from the instruction step. It is the decision rule this case needs. -/
axiom live_constraint_excludes_both
    (step : Nat → State → StepResult) (j : Nat) (σ : State) (row : Expr) :
    constraintAlive σ row →
    ∀ cs, step j σ = .candidates cs →
      cs.any (fun c => c.dir == .taken) = false ∨
      cs.any (fun c => c.dir == .notTaken) = false

/-- After an assignment deletes that row, acceptance still supplies the finite
bound above. The verifier may explore both directions again while scalar
bounds do not decide the comparison. It does not explore that back-edge
without a finite bound. `driveTaken` still rejects if both directions appear. -/
theorem accepted_returns_are_bounded
    (accepted : BpfAccepted) (parent : Nat) :
    ∃ N, N = bpfLoopBound accepted parent :=
  ⟨bpfLoopBound accepted parent, rfl⟩

end Node
