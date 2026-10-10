import CommonMath.Path

namespace CommonMath

/-! ## Budgeted node expansion (`doc/NodeInference/节点推理阅读索引.md`) -/

structure WorkState where
  nodes : Array Node
  edges : Array Edge
  work  : List NodeId
  fuel  : Nat
  deriving Repr, Inhabited

inductive ExpandOutcome where
  | complete (g : RunGraph)
  | fail (reason : RejectReason) (g : RunGraph)
  deriving Repr, Inhabited

def WorkState.toGraph (ws : WorkState) : RunGraph :=
  RunGraph.ofWork ws.nodes ws.edges

/-- Create root + Work. `progLen` is \(|\mathbf I|\). -/
def expandInit (progLen j0 : Nat) (σ0 : SemState) (B : Nat) :
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

private def prepareCandidate (σ : SemState) (c : Candidate) (progLen : Nat) :
    Except RejectReason (Direction × Location × SemState) :=
  match c.loc with
  | .exit =>
      do
        let state ← σ.applyLocal c.exprs c.predicates
        pure (c.dir, .exit, state)
  | .pos k =>
      if k ≥ progLen then
        Except.error .unboundTarget
      else
        do
          let state ← σ.applyLocal c.exprs c.predicates
          pure (c.dir, .pos k, state)

def prepareAll (σ : SemState) (progLen : Nat) :
    List Candidate → Except RejectReason (List (Direction × Location × SemState))
  | [] => Except.ok []
  | c :: cs =>
    match prepareCandidate σ c progLen with
    | Except.error e => Except.error e
    | Except.ok row =>
      match prepareAll σ progLen cs with
      | Except.error e => Except.error e
      | Except.ok rows => Except.ok (row :: rows)

private def appendPrepared (eta : NodeId) (nodes : Array Node) (edges : Array Edge)
    (work : List NodeId) :
    List (Direction × Location × SemState) → Array Node × Array Edge × List NodeId
  | [] => (nodes, edges, work)
  | (d, loc, σ') :: rs =>
    let zeta := nodes.size
    let nodes := nodes.push ⟨loc, σ'⟩
    let edges := edges.push ⟨eta, d, zeta⟩
    let work := if loc.isExit then work else work ++ [zeta]
    appendPrepared eta nodes edges work rs

/-- One node expansion (`doc/NodeInference/节点推理阅读索引.md`). `progLen` bounds non-Exit targets. -/
def expandOne (progLen : Nat) (step : Nat → SemState → StepResult) (ws : WorkState) :
    Sum ExpandOutcome WorkState :=
  match ws.work with
  | [] => Sum.inl (.complete ws.toGraph)
  | eta :: rest =>
    if ws.fuel = 0 then
      Sum.inl (.fail .limitExceeded ws.toGraph)
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

/-- Recurse on remaining fuel (`doc/NodeInference/有限预算展开的终止证明.md`). -/
partial def expand (progLen : Nat) (step : Nat → SemState → StepResult) (ws : WorkState) :
    ExpandOutcome :=
  match expandOne progLen step ws with
  | Sum.inl outcome => outcome
  | Sum.inr ws' => expand progLen step ws'

/-- Run `n` successful `expandOne` calls (or stop at earlier terminal). -/
def expandN (progLen : Nat) (step : Nat → SemState → StepResult) (ws : WorkState) :
    Nat → Sum ExpandOutcome WorkState
  | 0 => Sum.inr ws
  | n + 1 =>
    match expandOne progLen step ws with
    | Sum.inl outcome => Sum.inl outcome
    | Sum.inr ws' => expandN progLen step ws' n

end CommonMath
