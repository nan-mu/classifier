import Verification.Obligation
import Verification.Unverified.Required.BranchDecision
import Verification.Unverified.Required.CrossMeaning
import Verification.Unverified.Required.History
import Verification.Unverified.Required.Instruction
import Verification.Unverified.Required.PathCoverage
import Verification.Unverified.Required.UpdateMeaning
import Verification.Verified.Acceptance

namespace Verification.Unverified.Required.Acceptance

open Verification.Obligation

/-!
Target: `MeaningsAgree c a` for a completed unambiguous comparison whose lists
are the covered runs.

Proved conditional step: `meanings_if_arguments_survive`.
It needs `ValuationFollows`, `ArgsFaithful` and `RenamePreservesArguments`.
`ArgsFaithful` asks for the original argument terms, which a rename need not
preserve. `distinct_helper_args_reject` is a mismatch, not a passing pair.

Still open, and not supplied by this conditional step:

- `create_installs_entry`, `EntryIdentified` for the host pair
- `exit_ret_term`, `exit_ret_occurrence`, `rv32_ret_term`
- `covered_probe_reads_extract`, `missed_probe_keeps_old_read`
- `dependency_complete`, `ebpf_ignorable_step`, `ebpf_ignorable_branch`
- `CoveredSelection` for the run that was actually compared
- `RegisterValuesFollow` for the run's register values
- `saved_row_excludes_both`
- `RenamePreservesArguments` itself

RV32 safety is not this target and is not derived from eBPF checker acceptance.
-/

/-- The conditional step is the whole proof that is available.
`RenamePreservesArguments` is still an assumption of that step. -/
theorem meanings_if_arguments_survive
    (c : SharedCondition) (a : Accepts)
    (hval : ValuationFollows c a) (hren : RenamePreservesArguments c a)
    (hfaith : ArgsFaithful a) :
    MeaningsAgree c a :=
  Verification.Verified.Acceptance.meanings_if_arguments_survive c a hval hren hfaith

end Verification.Unverified.Required.Acceptance
