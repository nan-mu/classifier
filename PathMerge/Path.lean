import ClassifierExpr.Expr
import ClassifierExpr.Insn
import ClassifierExpr.Direction

namespace PathMerge
open ClassifierExpr

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

/-- Local result of one candidate successor: the increments σ_k = (E_k, P_k). -/
structure Candidate where
  dir        : Direction
  loc        : Location
  E_k : ExprSet
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

/-- \(\operatorname{updateExpr}\) = assignment override with comparison invalidation. -/
def updateExpr (E Ei : ExprSet) : ExprSet :=
  ExprSet.override E Ei

/-- Structural union of all five observation classes. Existing list order is retained,
then first occurrences of new local members are appended. This is not event history. -/
def mergePredicate (P Pi : List Predicate) : Except RejectReason (List Predicate) :=
  match Pi with
  | [] => .ok P
  | p :: ps =>
    mergePredicate (if P.contains p then P else P ++ [p]) ps

/-- The caller applies this composition rule to the input state and a candidate's
local result; step returns the increments, not the composed global state. -/
def applyLocal (σ : SemState) (Ei : ExprSet) (Pi : List Predicate) :
    Except RejectReason SemState := do
  if !σ.exprs.keysUnique || !σ.exprs.wellTyped || !Ei.keysUnique || !Ei.wellTyped then
    throw .localReject
  let predicates ← mergePredicate σ.predicates Pi
  pure ⟨updateExpr σ.exprs Ei, predicates⟩

def isExit : Location → Bool
  | .exit => true
  | .pos _ => false

def asPos? : Location → Option Nat
  | .pos j => some j
  | .exit => none

def RunGraph.ofWork (nodes : Array Node) (edges : Array Edge) : RunGraph :=
  ⟨nodes, edges, 0⟩

end PathMerge
