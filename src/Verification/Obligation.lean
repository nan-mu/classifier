import Inbox.Cross.Unify
import Term.Semantics
import Cross.EBPF.Create
import Node.Budget
import Cross.RV32.Create

namespace Verification.Obligation

open Term Term.Value Expression Observation Interface Interface.Step Inbox.Wire Inbox.Cross Node

/-- Shared valuation. Checker acceptance does not provide it. -/
structure SharedCondition where
  νL : Var → Nat
  νR : Var → Nat
  θL : ExternalInterpretation
  θR : ExternalInterpretation
  resource : Nat → Prop
  external : Prop

def predArgs : Observation → List Term
  | .helper _ args => args
  | .branch _ _ cond => [cond.lhs, cond.rhs]
  | .ret term => [term]
  | .mapWrite map key _ _ source => map :: (key ++ [source])
  | .packetWrite _ _ source => [source]

def denotePred (ν : Var → Nat) (θ : ExternalInterpretation) (p : Observation) :
    Option (List Nat) :=
  (predArgs p).mapM (interpretTerm ν θ)

/-- Completed runs plus an index-aligned match of the prepared observations.
The lists are inputs. This does not read them out of the graphs. -/
structure Accepts where
  ebpf : ExpandOutcome
  rv32 : ExpandOutcome
  left : List Observation
  right : List Observation
  ebpfComplete : ∃ g, ebpf = .complete g
  rv32Complete : ∃ g, rv32 = .complete g
  pass : (unifyLists left right).pass = true

def matched (a : Accepts) : List (Nat × Nat) :=
  (unifyLists a.left a.right).pairs

/-- Target: matched original observations denote the same arguments, and `c`
identifies resources and external results. A structural match is not this
statement. RV32 safety is not this statement. -/
def MeaningsAgree (c : SharedCondition) (a : Accepts) : Prop :=
  (∀ i j p q, (i, j) ∈ matched a → a.left[i]? = some p → a.right[j]? = some q →
      denotePred c.νL c.θL p = denotePred c.νR c.θR q) ∧
    (∀ id, c.resource id) ∧ c.external

/-- Bindings `buildE0` must install. No cross-architecture identification. -/
def EntryBindings (p : Cross.EBPF.EntryParams) (q : Cross.RV32.EntryParams)
    (σL σR : State) : Prop :=
  Cross.EBPF.buildE0 p = .ok σL → Cross.RV32.buildE0 q = .ok σR →
    σL.exprs.lookupEq (Reg.real64 1) = some (solve p.tCtx) ∧
    σL.exprs.lookupEq (Reg.real64 10) = some (solve p.tSp) ∧
    σR.exprs.lookupEq (Reg.real32 10) = some (solve q.tCtx) ∧
    σR.exprs.lookupEq (Reg.real32 2) = some (solve q.tSp)

/-- Identification of one entry pair under `c`. False for an arbitrary `c`. -/
def EntryIdentified (c : SharedCondition)
    (p : Cross.EBPF.EntryParams) (q : Cross.RV32.EntryParams) : Prop :=
  interpretTerm c.νL c.θL p.tCtx = interpretTerm c.νR c.θR q.tCtx ∧
  interpretTerm c.νL c.θL p.tData = interpretTerm c.νR c.θR q.tData ∧
  interpretTerm c.νL c.θL (Term.C32 p.packetBytes) = interpretTerm c.νR c.θR q.tLen

/-- Per-step observation record of one completed graph. `faithful` is the claim
that `steps` is that record in order, with duplicates kept. -/
structure Coverage (g : RunGraph) where
  steps : List (List Observation)
  faithful : Prop

/-- `a.left` / `a.right` are the flattened faithful records of the two graphs. -/
def ListsFromRuns (a : Accepts) (gL gR : RunGraph)
    (cL : Coverage gL) (cR : Coverage gR) : Prop :=
  a.ebpf = .complete gL ∧ a.rv32 = .complete gR ∧
    a.left = cL.steps.flatten ∧ a.right = cR.steps.flatten ∧
    cL.faithful ∧ cR.faithful

def substOf (a : Accepts) : Subst :=
  (unifyLists a.left a.right).subst

/-- Explicit variable names, resources and external results follow the alignment.
Register values are absent: `Subst.regImage?` has no value function here. -/
def ValuationFollows (c : SharedCondition) (a : Accepts) : Prop :=
  (∀ (w : Width) (x y : Nat), (substOf a).varImage? x = some y →
      c.νL ⟨w, x, none⟩ = c.νR ⟨w, y, none⟩) ∧
    c.external ∧ (∀ id, c.resource id)

/-- Matched observations still have the same original argument terms.
Renaming can change a variable name, so this is stronger than the match. -/
def ArgsFaithful (a : Accepts) : Prop :=
  ∀ i j p q, (i, j) ∈ matched a → a.left[i]? = some p → a.right[j]? = some q →
    predArgs p = predArgs q

/-- Argument denotations survive renaming when the valuation follows and the
original arguments are syntactically the same. -/
def RenamePreservesArguments (c : SharedCondition) (a : Accepts) : Prop :=
  ValuationFollows c a → ArgsFaithful a →
    ∀ i j p q, (i, j) ∈ matched a → a.left[i]? = some p → a.right[j]? = some q →
      denotePred c.νL c.θL p = denotePred c.νR c.θR q

end Verification.Obligation
