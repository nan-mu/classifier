import Verification.Obligation
import Verification.Verified.Acceptance

namespace Verification.Unverified.Required.CrossMeaning

open Term Term.Value Expression Observation Interface Interface.Step Wire Match Verification.Obligation

/-!
`accept_is_structural` is injective coverage and rename equality of the
compared terms. A helper argument, including a flags word, stays in that
comparison. `distinct_helper_args_reject` is the mismatch.

`ValuationFollows` and `RenamePreservesArguments` are not proved. They are not
eBPF-checker facts. Register values are a further premise: `regImage?` is not
a value. Adjacent write re-pairing is not part of `unifyLists`.
-/

/-- Values of renamed registers. Not part of `ValuationFollows`. -/
def RegisterValuesFollow (a : Accepts) (ρL ρR : Reg → Nat) : Prop :=
  ∀ x y, (substOf a).regImage? x = some y → ρL x = ρR y

/-- Disagreement at a renamed register is not `RegisterValuesFollow`.
The positive statement, that the run's register values do follow, is not proved. -/
theorem register_disagreement_blocks_follow
    (a : Accepts) (ρL ρR : Reg → Nat) (x y : Reg)
    (hmap : (substOf a).regImage? x = some y)
    (hval : ρL x ≠ ρR y) :
    ¬ RegisterValuesFollow a ρL ρR := by
  intro h
  exact hval (h x y hmap)

end Verification.Unverified.Required.CrossMeaning
