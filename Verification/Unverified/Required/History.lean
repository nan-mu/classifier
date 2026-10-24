import EBPF.Step
import RV32.Expand
import Verification.Verified.HistoryAndPath

namespace Verification.Unverified.Required.History

open Core Node Verification.Verified.HistoryAndPath

/-!
`dependency_blocks_ignoring` is only: a register already placed in
`observationDeps` is not returned by `history`.

The two further claims are stated here. Neither is `observation_dep_not_ignorable`.
The linear induction `linearTrace_of_step_preservation` is proved, and it is
not applied to equal states. Discharging `StepPreserves` for the real `step`
functions is open, including branches, which that hypothesis rejects.
-/

/-- Every register whose entry value can change an observation argument is
already in `observationDeps`. This is completeness of the analysis. -/
def DependencyComplete : Prop :=
  ∀ (entry : List Expr) (steps : List (List Expr × List Predicate)) (r : Reg)
    (ν₁ ν₂ : Var → Nat) (θ : ExternalInterpretation) (p : Predicate),
    p ∈ steps.flatMap (·.2) →
    (∀ v, v ∉ FV ((entry.lookupEq r).getD (Term.C32 0)) → ν₁ v = ν₂ v) →
    denoteOne ν₁ θ p ≠ denoteOne ν₂ θ p →
    r ∈ observationDeps entry steps
  where
    denoteOne (ν : Var → Nat) (θ : ExternalInterpretation) (p : Predicate) : Option (List Nat) :=
      (match p with
        | .helper _ _ args => args
        | .branch _ _ cond => [cond.lhs, cond.rhs]
        | .ret term => [term]
        | .mapWrite _ map key _ _ source => map :: (key ++ [source])
        | .packetWrite _ _ _ source => [source]).mapM (interpretTerm ν θ)

/-- sorry: required obligation, not a proof. -/
theorem dependency_complete : DependencyComplete := by
  sorry

/-- A difference that `history` calls ignorable does not change the next
linear observation. The covered set is that history list, not an arbitrary
register list. `drive_equal_states` does not prove this. -/
def IgnorablePreservesEbpf (I : Array EBPF.Insn) (event : Nat)
    (steps : List (List Expr × List Predicate)) (entry : List Expr) : Prop :=
  StepPreserves (fun j σ => EBPF.ebpfStep I event j σ) (history steps entry)

def IgnorablePreservesRv32 (I : Array RV32.Insn)
    (steps : List (List Expr × List Predicate)) (entry : List Expr) : Prop :=
  StepPreserves (fun j σ => RV32.rv32Step I j σ) (history steps entry)

/-- sorry: required obligation, not a proof. -/
theorem ebpf_ignorable_step
    (I : Array EBPF.Insn) (event : Nat)
    (steps : List (List Expr × List Predicate)) (entry : List Expr) :
    IgnorablePreservesEbpf I event steps entry := by
  sorry

/-- sorry: required obligation, not a proof. -/
theorem rv32_ignorable_step
    (I : Array RV32.Insn)
    (steps : List (List Expr × List Predicate)) (entry : List Expr) :
    IgnorablePreservesRv32 I steps entry := by
  sorry

/-- Branching steps are excluded by `StepPreserves`. Both directions still
need the same observation agreement on the history-covered set. -/
def BranchPreserves (step : Nat → SemState → StepResult)
    (steps : List (List Expr × List Predicate)) (entry : List Expr) : Prop :=
  ∀ j σ τ cσ dσ cτ dτ,
    ExprIgnorable (history steps entry) σ τ →
    step j σ = .candidates [cσ, dσ] →
    step j τ = .candidates [cτ, dτ] →
    cσ.dir = cτ.dir ∧ dσ.dir = dτ.dir ∧
    cσ.loc = cτ.loc ∧ dσ.loc = dτ.loc ∧
    cσ.P_k = cτ.P_k ∧ dσ.P_k = dτ.P_k

/-- sorry: required obligation, not a proof. -/
theorem ebpf_ignorable_branch
    (I : Array EBPF.Insn) (event : Nat)
    (steps : List (List Expr × List Predicate)) (entry : List Expr) :
    BranchPreserves (fun j σ => EBPF.ebpfStep I event j σ) steps entry := by
  sorry

/-- Finite linear observations agree by `linearTrace_of_step_preservation`
once `ebpf_ignorable_step` is available. This does not discharge that premise.
-/
theorem ebpf_linear_trace_agrees
    (I : Array EBPF.Insn) (event : Nat)
    (steps : List (List Expr × List Predicate)) (entry : List Expr)
    (h : IgnorablePreservesEbpf I event steps entry)
    (fuel j : Nat) (σ τ : SemState)
    (hign : ExprIgnorable (history steps entry) σ τ) :
    linearTrace (fun j σ => EBPF.ebpfStep I event j σ) fuel j σ =
      linearTrace (fun j σ => EBPF.ebpfStep I event j σ) fuel j τ :=
  linearTrace_of_step_preservation _ (history steps entry) h fuel j σ τ hign

end Verification.Unverified.Required.History
