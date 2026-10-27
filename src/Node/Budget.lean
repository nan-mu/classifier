import Node.Path
import Interface.Update
import Wire.Render

namespace Node
open Term Term.Value Expression Observation Interface Interface.Step Wire

/-! ## Budgeted node expansion (`doc/路径.md`). `fuel` bounds analysis and is separate from a rejected instruction. -/

structure WorkState where
  nodes : Array Node
  edges : Array Edge
  work  : List NodeId
  fuel  : Nat
  deriving Repr, Inhabited

inductive ExpandOutcome where
  | complete (g : RunGraph)
  | fail (reason : RejectReason) (g : RunGraph)
  /-- Runtime budget exhaustion, separate from step rejection reasons. -/
  | limitExceeded (g : RunGraph)
  deriving Repr, Inhabited

def WorkState.toGraph (ws : WorkState) : RunGraph :=
  RunGraph.ofWork ws.nodes ws.edges

/-- Create root + Work. `progLen` is \(|\mathbf I|\). -/
def expandInit (progLen j0 : Nat) (σ0 : State) (B : Nat) :
    Except RejectReason WorkState :=
  if j0 ≥ progLen then
    Except.error .invalidEntry
  else
    Except.ok {
      nodes := #[⟨.pos j0, σ0⟩]
      edges := #[]
      work  := [0]
      fuel  := B
    }

private def prepareCandidate (σ : State) (c : Candidate) (progLen : Nat) :
    Except RejectReason (Direction × Location × State) :=
  match c.loc with
  | .exit => pure (c.dir, .exit, update σ { exprs := c.E_k, predicates := c.P_k })
  | .pos k =>
    if k ≥ progLen then throw .unboundTarget
    else pure (c.dir, .pos k, update σ { exprs := c.E_k, predicates := c.P_k })

def prepareAll (σ : State) (progLen : Nat) :
    List Candidate → Except RejectReason (List (Direction × Location × State))
  | [] => Except.ok []
  | c :: cs =>
    match prepareCandidate σ c progLen with
    | Except.error e => Except.error e
    | Except.ok row =>
      match prepareAll σ progLen cs with
      | Except.error e => Except.error e
      | Except.ok rows => Except.ok (row :: rows)

/-- Visits of one instruction along a single path. A symbolic loop otherwise
keeps both directions and spends the budget. Other paths may visit it again. -/
def loopVisitLimit : Nat := 4

private def pathVisits (nodes : Array Node) (edges : Array Edge) (start : NodeId)
    (loc : Location) : Nat :=
  let rec go (id : NodeId) (fuel : Nat) : Nat :=
    if fuel = 0 then 0 else
      let here := match nodes[id]? with
        | some node => if node.loc == loc then 1 else 0
        | none => 0
      match edges.find? (fun e => e.dst == id) with
      | some e => here + go e.src (fuel - 1)
      | none => here
  go start (nodes.size + 1)

private def appendPrepared (eta : NodeId) (nodes : Array Node) (edges : Array Edge)
    (work : List NodeId) :
    List (Direction × Location × State) → Array Node × Array Edge × List NodeId
  | [] => (nodes, edges, work)
  | (d, loc, σ') :: rs =>
    if !Node.isExit loc && pathVisits nodes edges eta loc ≥ loopVisitLimit then
      appendPrepared eta nodes edges work rs
    else
      let zeta := nodes.size
      let nodes := nodes.push ⟨loc, σ'⟩
      let edges := edges.push ⟨eta, d, zeta⟩
      let work := if Node.isExit loc then work else work ++ [zeta]
      appendPrepared eta nodes edges work rs

/-- One node expansion (`doc/路径.md`). `progLen` bounds non-Exit targets. -/
def expandOne (progLen : Nat) (step : Nat → State → StepResult) (ws : WorkState) :
    Sum ExpandOutcome WorkState :=
  match ws.work with
  | [] => Sum.inl (.complete ws.toGraph)
  | eta :: rest =>
    if ws.fuel = 0 then
      Sum.inl (.limitExceeded ws.toGraph)
    else
      match ws.nodes[eta]? with
      | none => Sum.inl (.fail .localReject ws.toGraph)
      | some node =>
        match node.loc with
        | .exit => Sum.inl (.fail .localReject ws.toGraph)
        | .pos j =>
          match step j node.state with
          | .reject reason => Sum.inl (.fail reason ws.toGraph)
          | .candidates cs =>
            match prepareAll node.state progLen cs with
            | Except.error reason => Sum.inl (.fail reason ws.toGraph)
            | Except.ok prepared =>
              let (nodes, edges, work') :=
                appendPrepared eta ws.nodes ws.edges rest prepared
              Sum.inr {
                nodes := nodes
                edges := edges
                work  := work'
                fuel  := ws.fuel - 1
              }

/-- Recurse while fuel remains (`doc/路径.md`). This definition is `partial`. -/
partial def expand (progLen : Nat) (step : Nat → State → StepResult) (ws : WorkState) :
    ExpandOutcome :=
  match expandOne progLen step ws with
  | Sum.inl outcome => outcome
  | Sum.inr ws' => expand progLen step ws'

private def loopVisitCheck : Bool :=
  let step (_j : Nat) (_σ : State) : StepResult :=
    .candidates [
      ⟨.taken, .pos 0, Expr.nil, []⟩,
      ⟨.notTaken, .exit, Expr.nil, [.ret (Term.C32 1)]⟩]
  match expandInit 1 0 ⟨Expr.nil, []⟩ 100 with
  | .error _ => false
  | .ok ws =>
    match expand 1 step ws with
    | .complete g => g.nodes.size ≤ 2 * loopVisitLimit + 1 &&
        g.nodes.any (fun n => n.loc == .exit)
    | _ => false

#guard loopVisitCheck

/-- Run `n` successful `expandOne` calls (or stop at earlier terminal). -/
def expandN (progLen : Nat) (step : Nat → State → StepResult) (ws : WorkState) :
    Nat → Sum ExpandOutcome WorkState
  | 0 => Sum.inr ws
  | n + 1 =>
    match expandOne progLen step ws with
    | Sum.inl outcome => Sum.inl outcome
    | Sum.inr ws' => expandN progLen step ws' n

def reasonTag : RejectReason → String
  | .invalidEntry => "InvalidEntry"
  | .unsupported => "Unsupported"
  | .unboundTarget => "UnboundTarget"
  | .undefinedSrc => "UndefinedSrc"
  | .localReject => "LocalReject"

def dirTag : Direction → String
  | .ok => "OK"
  | .taken => "Taken"
  | .notTaken => "NotTaken"

def snapshotJson (nodes : Array Node) (edges : Array Edge) (work : List NodeId)
    (fuel : Nat) (status : String) (reason : Option RejectReason)
    (failed : Option NodeId := none) (budgetExhausted : Bool := false) : String :=
  let nodeStrs := Id.run do
    let mut acc : List String := []
    for id in [:nodes.size] do
      if let some n := nodes[id]? then
        let (ej, pj) := renderStateJson n.state
        let loc := match n.loc with | .exit => "exit" | .pos j => toString j
        acc := acc ++
          [s!"\{\"id\":{id},\"loc\":\"{loc}\",\"exprs\":[{ej}],\"predicates\":[{pj}]}"]
    pure (String.intercalate "," acc)
  let edgeStrs := String.intercalate "," (edges.toList.map fun e =>
    s!"\{\"src\":{e.src},\"dir\":\"{dirTag e.dir}\",\"dst\":{e.dst}}")
  let workStr := String.intercalate "," (work.map toString)
  let reasonField := match reason with
    | none => if budgetExhausted then "\"LimitExceeded\"" else "null"
    | some r => s!"\"{reasonTag r}\""
  let failedField := match failed with | none => "null" | some id => toString id
  s!"\{\"status\":\"{status}\",\"reason\":{reasonField},\"failed\":{failedField},\"fuel\":{fuel},\"work\":[{workStr}],\"nodes\":[{nodeStrs}],\"edges\":[{edgeStrs}]}"

def snapshotAfter (progLen : Nat) (stepFn : NodeId → Nat → State → StepResult)
    (ws : WorkState) : Nat → String
  | 0 => snapshotJson ws.nodes ws.edges ws.work ws.fuel
      (if ws.work.isEmpty then "complete" else "running") none
  | n + 1 =>
    match expandOne progLen (stepFn (ws.work.headD 0)) ws with
    | .inr ws' => snapshotAfter progLen stepFn ws' n
    | .inl (.complete g) => snapshotJson g.nodes g.edges [] ws.fuel "complete" none
    | .inl (.limitExceeded g) =>
      snapshotJson g.nodes g.edges ws.work ws.fuel "fail" none none true
    | .inl (.fail reason g) =>
      -- expandOne's terminal result has only a graph; retain diagnostic queue/fuel here.
      let attempted := !ws.work.isEmpty && ws.fuel > 0
      snapshotJson g.nodes g.edges (if attempted then ws.work.tail else ws.work)
        (if attempted then ws.fuel - 1 else ws.fuel) "fail" (some reason)
        (if attempted then ws.work.head? else none)

end Node
