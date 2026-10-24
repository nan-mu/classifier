namespace Verification.Unverified.Assumed.BpfChecker

/-!
Candidate external premise from the Linux BPF verifier
(`kernel/bpf/verifier.c`, `do_check` / `is_state_visited`).

Scope: a program that this checker has accepted, in the checker's own state
model, helper set, and kernel configuration.

Not in scope, and not assumed here:

- this repository's `State`, `ebpfStep`, or `rv32Step`
- `loopLimit` or any concrete fuel being large enough
- a saved comparison row excluding both successors
- RV32 safety
- completeness of `history`

`authorConfirmed` is false in every value this file constructs. No theorem
in `Verification.Verified` consumes the structure. `Node.bpfLoopBound` and
`Node.live_constraint_excludes_both` are existing axioms and are not used.
-/

/-- Finite only-taken returns to one parent, as reported by an accepting run.
Finiteness is the `Nat`. It is not an inequality against `loopLimit`. -/
structure FiniteBackedge where
  authorConfirmed : Bool := false
  /-- Parent instruction index to the checker's count. -/
  bound : Nat → Nat
  source : String := "Linux kernel/bpf/verifier.c do_check / is_state_visited"
  scope : String := "programs accepted by that checker in its own state model"

/-- A finite bound is not a proof that `fuel` survives it. -/
theorem finite_bound_misses_fuel
    (c : FiniteBackedge) (parent fuel : Nat)
    (h : ¬ c.bound parent ≤ fuel) :
    ¬ ∀ returns, returns ≤ c.bound parent → returns ≤ fuel := by
  intro hall
  exact h (hall (c.bound parent) (Nat.le_refl _))

/-- The inequality that would make the current fuel enough. It is not a field
of `FiniteBackedge`. -/
def FuelCovers (c : FiniteBackedge) (parent fuel : Nat) : Prop :=
  c.bound parent ≤ fuel

theorem fuel_covers_bounds_returns
    (c : FiniteBackedge) (parent fuel returns : Nat)
    (hfuel : FuelCovers c parent fuel)
    (hret : returns ≤ c.bound parent) :
    returns ≤ fuel :=
  Nat.le_trans hret hfuel

end Verification.Unverified.Assumed.BpfChecker
