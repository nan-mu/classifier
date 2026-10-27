import Expression.Basic
import Observation.Insn
import Interface.Step.Direction
import Wire.Parse

namespace Node
open Term Term.Value Expression Observation Interface Interface.Step Wire

/-- Path-graph node. Observations do not carry it. -/
abbrev NodeId := Nat

/-! ## Location, node, edge, step (`doc/路径.md`) -/

/-- Pre-execution snapshot (Exit holds the final post-return state). -/
structure Node where
  loc   : Location
  state : State
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
  P_k : List Observation
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

/-- Step increment. A stored node uses `exprs` and `predicates`. -/
def renderIncrementJson (step : State) : String :=
  let (writes, observations) := renderStateJson step
  s!"\"writes\":[{writes}],\"observations\":[{observations}]"

@[export lean_expand_update]
def exportUpdate (localExprs localPreds stepExprs stepPreds : String) : String :=
  match parseStateJson localExprs localPreds, parseStateJson stepExprs stepPreds with
  | some parent, some step =>
    let (exprs, preds) := renderStateJson (update parent step)
    s!"\{\"status\":\"ok\",\"exprs\":[{exprs}],\"predicates\":[{preds}]}"
  | _, _ => "{\"status\":\"fail\",\"reason\":\"LocalReject\"}"

end Node
