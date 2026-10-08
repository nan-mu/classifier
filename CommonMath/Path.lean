import CommonMath.Expr
import CommonMath.Insn
import CommonMath.Direction

namespace CommonMath

/-! ## Location, node, edge, step (`doc/common-math.md` §12–15) -/

inductive Location where
  | pos (j : Nat)
  | exit
  deriving DecidableEq, BEq, Repr, Inhabited

/-- Semantic state \(\sigma=(\mathcal E,\mathcal P)\). -/
structure SemState where
  exprs      : ExprSet
  predicates : List Predicate
  deriving Repr, Inhabited

def SemState.empty : SemState := ⟨ExprSet.empty, []⟩

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

/-- Local effect of one candidate successor. -/
structure Candidate where
  dir        : Direction
  loc        : Location
  exprs      : ExprSet
  predicates : List Predicate
  deriving Repr, Inhabited

inductive RejectReason where
  | invalidEntry
  | limitExceeded
  | unsupported
  | unboundTarget
  | undefinedSrc
  | localReject
  deriving DecidableEq, BEq, Repr, Inhabited

inductive StepResult where
  | reject (reason : RejectReason)
  | candidates (cs : List Candidate)
  deriving Repr

/-- \(\operatorname{updateExpr}\) = key-unique override. -/
def updateExpr (E Ei : ExprSet) : ExprSet :=
  ExprSet.override E Ei

/-- cmp merges append structurally new conditions, retaining complements.
Return observations use the same append/dedup rule.
An empty local effect is identity. -/
def mergePredicate (P Pi : List Predicate) : Except RejectReason (List Predicate) :=
  match Pi with
  | [] => .ok P
  | p :: ps =>
    mergePredicate (if P.contains p then P else P ++ [p]) ps

def SemState.applyLocal (σ : SemState) (Ei : ExprSet) (Pi : List Predicate) :
    Except RejectReason SemState := do
  let predicates ← mergePredicate σ.predicates Pi
  pure ⟨updateExpr σ.exprs Ei, predicates⟩

def Location.isExit : Location → Bool
  | .exit => true
  | .pos _ => false

def Location.asPos? : Location → Option Nat
  | .pos j => some j
  | .exit => none

def RunGraph.ofWork (nodes : Array Node) (edges : Array Edge) : RunGraph :=
  ⟨nodes, edges, 0⟩

end CommonMath
