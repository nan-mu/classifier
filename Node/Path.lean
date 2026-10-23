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

def isExit : Location → Bool
  | .exit => true
  | .pos _ => false

def asPos? : Location → Option Nat
  | .pos j => some j
  | .exit => none

def RunGraph.ofWork (nodes : Array Node) (edges : Array Edge) : RunGraph :=
  ⟨nodes, edges, 0⟩

end Node
