import Expression.Interval
import Cross.EBPF.Step
import Cross.RV32.Expand
import Verification.Obligation

namespace Verification.Unverified.Required.Instruction

open Term Term.Value Expression Observation Interface Interface.Step Wire Match Verification.Obligation

/-!
There is no instruction semantics in this repository besides `ebpfStep` and
`rv32Step`. The statements below talk about `readInterval` and `lookupEq`,
which are not defined as those functions. They are not proved, because the
exit readers `fullReg` and `emitIndirect` are private.

Occurrence (whether a `ret` is emitted) and parameter correctness (the `ret`
term is the pre-state register) are separate propositions.
-/

/-- Parameter correctness for one eBPF instruction: `exit` returns the pre-state
full r0. -/
def ExitRetTerm : Prop :=
  ∀ (I : Array Cross.EBPF.Insn) (event j : Nat) (σ : State) (t : Term),
    I[j]? = some .exit →
    readInterval σ.exprs (Reg.real64 0) = some t →
    t.width = .w64 → t.semanticBits = 64 →
    Cross.EBPF.ebpfStep I event j σ =
      .candidates [⟨.ok, .exit, Expr.nil, [.ret t]⟩]

/-- sorry: required obligation, not a proof. -/
theorem exit_ret_term : ExitRetTerm := by
  sorry

/-- Occurrence for the same instruction: a missing full r0 is a rejection, not
a return of a fresh term. -/
def ExitRetOccurrence : Prop :=
  ∀ (I : Array Cross.EBPF.Insn) (event j : Nat) (σ : State),
    I[j]? = some .exit →
    readInterval σ.exprs (Reg.real64 0) = none →
    Cross.EBPF.ebpfStep I event j σ = .reject .undefinedSrc

/-- sorry: required obligation, not a proof. -/
theorem exit_ret_occurrence : ExitRetOccurrence := by
  sorry

/-- RV32's recognized wrapper return records the pre-state term of `a0`. -/
def Rv32RetTerm : Prop :=
  ∀ (I : Array Cross.RV32.Insn) (j : Nat) (σ : State) (t : Term),
    σ.exprs.lookupEq (Reg.real32 10) = some t →
    (∃ c, Cross.RV32.rv32Step I j σ = .candidates [c] ∧ c.loc = .exit ∧ .ret t ∈ c.P_k) ∨
      ∀ c, Cross.RV32.rv32Step I j σ = .candidates [c] → c.loc ≠ .exit

/-- sorry: required obligation, not a proof. Not every state with `a0` defined
is a return; the disjunction is the public shape of that fact. -/
theorem rv32_ret_term : Rv32RetTerm := by
  sorry

/-- Create installs the host entry terms it was given. One `#guard` literal
does not prove this. Cross-architecture identification is `EntryIdentified`,
which is a premise for a particular `c`, not a theorem. -/
theorem create_installs_entry (p : Cross.EBPF.EntryParams) (q : Cross.RV32.EntryParams)
    (σL σR : State) : EntryBindings p q σL σR := by
  sorry

end Verification.Unverified.Required.Instruction
