import Observation.Insn
import Cross.EBPF.Create
import Cross.RV32.Create

namespace Verification.Unverified.Assumed.HelperAndHost

open Term Term.Value Expression Observation Interface Interface.Step Wire

/-!
Host and helper contracts are parameters. `authorConfirmed` stays false.
Neither contract is an eBPF-checker theorem, and neither identifies the two
architectures' inputs. `EntryIdentified` remains a required premise.

`helperArity` / `helperRequired` count arguments. They do not determine the
value a helper returns or whether a map update succeeds.
-/

/-- What the host does for one helper id and concrete argument list. -/
structure HelperBehavior where
  authorConfirmed : Bool := false
  source : String := "host helper contract, not helperArity"
  behavior : HelperKind → List Nat → Option Nat

/-- A parameter-count constraint does not select the host result. -/
def ParameterCount (k : HelperKind) (args : List Term) : Prop :=
  helperRequired k ≤ args.length

theorem parameter_count_leaves_behavior_open
    (b : HelperBehavior) (k : HelperKind) (args : List Term) (vals : List Nat)
    (_h : ParameterCount k args) :
    b.behavior k vals = none ∨ ∃ n, b.behavior k vals = some n := by
  cases hres : b.behavior k vals
  · exact Or.inl rfl
  · exact Or.inr ⟨_, rfl⟩

/-- Per-architecture host supply. Cross-architecture agreement is
`Verification.Obligation.EntryIdentified` and is not a field. -/
structure HostEntry where
  authorConfirmed : Bool := false
  source : String := "host entry contract for one architecture"
  ebpf : Cross.EBPF.EntryParams → Prop
  rv32 : Cross.RV32.EntryParams → Prop

end Verification.Unverified.Assumed.HelperAndHost
