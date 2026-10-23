import Core.Expr
import Core.Insn
import Core.Direction

namespace Node
open Core

/-! ## Location, node, edge, step (`doc/NodeInference/路径.md`) -/

/-- Pre-execution snapshot (Exit holds the final post-return state). -/
structure Node where
  loc   : Location
  state : SemState
  deriving Repr, Inhabited

structure Edge where
  src : NodeId
  dir : Direction
  dst : NodeId
  deriving DecidableEq, BEq, Repr, Inhabited

structure RunGraph where
  nodes : Array Node
  edges : Array Edge
  root  : NodeId := 0
  deriving Repr, Inhabited

/-- Local result of one candidate successor. Virtual stores are equalities in `E_k`. -/
structure Candidate where
  dir        : Direction
  loc        : Location
  E_k : List Expr
  P_k : List Predicate
  deriving Repr, Inhabited

inductive RejectReason where
  | invalidEntry
  | unsupported
  | unboundTarget
  | undefinedSrc
  | localReject
  deriving DecidableEq, BEq, Repr, Inhabited

inductive StepResult where
  | reject (reason : RejectReason)
  | candidates (cs : List Candidate)
  deriving Repr

/-- A row records the branch fact rather than an assignment when its relation
and right-hand side are the branch condition and its register still holds the
condition's left-hand side. -/
def branchFact (E : List Expr) (Pi : List Predicate) (e : Expr) : Bool :=
  Pi.any fun
    | .branch _ _ cond =>
      e.rel == cond.rel && solve e.term == solve cond.rhs &&
        match E.lookupEq e.reg with
        | some lhs => solve lhs == solve cond.lhs
        | none => false
    | _ => false

/-- \(\operatorname{updateExpr}\) = assignment override with comparison invalidation.
Branch facts in `Ei` are appended and do not replace the compared register. -/
def updateExpr (E Ei : List Expr) (Pi : List Predicate := []) : List Expr :=
  let facts := Ei.filter (branchFact E Pi)
  let rest := Ei.filter fun e => !facts.contains e
  facts.foldl (fun acc e => acc.insertConstraint e) (E.override rest)

/-- Structural union of all five observation classes. Existing list order is retained,
then first occurrences of new local members are appended. This is not event history. -/
def mergePredicate (P Pi : List Predicate) : Except RejectReason (List Predicate) :=
  match Pi with
  | [] => .ok P
  | p :: ps =>
    mergePredicate (if P.contains p then P else P ++ [p]) ps

/-- The caller applies this composition rule to the input state and a candidate's
local result; step returns the increments, not the composed global state. -/
def applyLocal (σ : SemState) (Ei : List Expr) (Pi : List Predicate) :
    Except RejectReason SemState := do
  if !σ.exprs.keysUnique || !σ.exprs.wellTyped || !Ei.keysUnique || !Ei.wellTyped then
    throw .localReject
  let predicates ← mergePredicate σ.predicates Pi
  pure { exprs := updateExpr σ.exprs Ei Pi, predicates }

def isExit : Location → Bool
  | .exit => true
  | .pos _ => false

def asPos? : Location → Option Nat
  | .pos j => some j
  | .exit => none

def RunGraph.ofWork (nodes : Array Node) (edges : Array Edge) : RunGraph :=
  ⟨nodes, edges, 0⟩

end Node
