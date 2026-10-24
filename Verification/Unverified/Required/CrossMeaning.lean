import Verification.Obligation
import Verification.Verified.Acceptance

namespace Verification.Unverified.Required.CrossMeaning

open Core Verification.Obligation

/-!
`accept_is_structural` is injective coverage, maximality and syntactic rename
equality. `projection_acceptance_misses_flag_meaning` shows that equality does
not preserve an update flag, so it is not `MeaningsAgree`.

`toCrossHelper` on a layout-sized update keeps the map, key tail and value
tail (`toCrossHelper_update_full`). It drops the event (`helper_event_erased`),
the flags word (`update_flags_erased`), and it has no success bit and no
helper return. Those dropped fields are why `ArgsFaithful` is required.

`ValuationFollows` and `RenamePreservesArguments` are not proved. They are not
eBPF-checker facts. Register values are a further premise: `regImage?` is not
a value.
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
