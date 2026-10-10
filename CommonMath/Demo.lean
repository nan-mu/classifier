import CommonMath.Expand
import CommonMath.Term
import CommonMath.Reg
import CommonMath.Render

namespace CommonMath

private def comparisonOverwriteCheck : Bool :=
  let reg := Reg.real32 1
  let original := ExprSet.empty.insertEq reg (Term.V32 1)
    |>.insertConstraint (Expr.mkRel reg .eq (Term.C32 10))
    |>.insertConstraint (Expr.mkRel reg .ltu (Term.C32 20))
  let updated := ExprSet.override original (ExprSet.empty.insertEq reg (Term.C32 20))
  original.keysUnique && original.lookupEq reg == some (Term.V32 1) &&
    original.constraints.length == 2 && updated.constraints.isEmpty &&
    updated.lookupEq reg == some (Term.C32 20)

private def comparisonAccumulationCheck : Bool :=
  let reg := Reg.real64 1
  let E := ExprSet.empty.insertEq reg (Term.V64 1)
  let a := Expr.mkRel reg .eq (Term.C64 10)
  let b := Expr.mkRel reg .eq (Term.C64 20)
  let result := ExprSet.override E (ExprSet.empty.insertConstraint a |>.insertConstraint b)
  result.lookupEq reg == some (Term.V64 1) && result.constraints == [a, b] &&
    (result.insertConstraint a).constraints == [a, b] && result.keysUnique &&
    (ExprSet.override result (ExprSet.empty.insertEq (Reg.real64 2) (Term.C64 0))).constraints == [a, b]

private def observationMergeCheck : Bool :=
  let p := Predicate.helper 7 .clock []
  let r := Predicate.ret (Term.V32 1)
  match mergePredicate [p] [r, r, p], mergePredicate [r] [] with
  | .ok merged, .ok unchanged => merged == [p, r] && unchanged == [r]
  | _, _ => false

#guard comparisonOverwriteCheck
#guard comparisonAccumulationCheck
#guard observationMergeCheck
#guard (Expr.mkRel (Reg.real32 1) .ltu (Term.C32 2)).decideWith (Term.V32 1) == none
#guard (Expr.mkRel (Reg.real32 1) .lts (Term.C32 0)).decideWith (Term.C32 0xffffffff) == some true
#guard (Expr.mkRel (Reg.real64 1) .lts (Term.C64 0)).decideWith (Term.C64 0xffffffff) == some false
#guard (Expr.mkRel (Reg.real64 1) (.ltsN 32) (Term.C64 0)).decideWith (Term.C64 0xffffffff) == some true
#guard (Expr.mkRel (Reg.real64 1) .eq (Term.C64 0)).decideWith (Term.C32 0) == none

/-! ## Bounded loop demo (`doc/NodeInference/有界循环的节点展开例证.md`) -/

private def demoReg : Reg := Reg.real32 1

private def readR (σ : SemState) : Option Nat :=
  match σ.exprs.lookupEq demoReg with
  | none => none
  | some t => eval (solve t)

private def setR (v : Nat) : ExprSet :=
  ExprSet.empty.insertEq demoReg (Term.C32 v)

def demoProgLen : Nat := 4

/-- Single-instruction rule for the §18 listing. -/
def demoStep (j : Nat) (σ : SemState) : StepResult :=
  match readR σ with
  | none => .reject .undefinedSrc
  | some r =>
    match j with
    | 0 =>
      if r ≥ 3 then
        .candidates [⟨.taken, .pos 3,
          ExprSet.empty.insertConstraint (Expr.mkRel demoReg .geu (Term.C32 3)), []⟩]
      else
        .candidates [⟨.notTaken, .pos 1,
          ExprSet.empty.insertConstraint (Expr.mkRel demoReg .ltu (Term.C32 3)), []⟩]
    | 1 =>
      .candidates [⟨.only, .pos 2, setR (r + 1), []⟩]
    | 2 =>
      .candidates [⟨.only, .pos 0, ExprSet.empty, []⟩]
    | 3 =>
      .candidates [⟨.only, .exit, ExprSet.empty, [.ret (Term.C32 r)]⟩]
    | _ => .reject .unboundTarget

def demoσ0 : SemState := ⟨setR 0, []⟩

def demoInit (B : Nat) : Except RejectReason WorkState :=
  expandInit demoProgLen 0 demoσ0 B

def demoExpand (B : Nat) : ExpandOutcome :=
  match demoInit B with
  | .error reason => .fail reason ⟨#[], #[], 0⟩
  | .ok ws => expand demoProgLen demoStep ws

def demoHasExit (g : RunGraph) : Bool :=
  g.nodes.any fun n => n.loc.isExit

/-- `B=11` completes with Exit; `B=10` hits LimitExceeded. -/
def demoCheck : Bool :=
  match demoExpand 11, demoExpand 10 with
  | .complete g, .fail .limitExceeded _ => demoHasExit g
  | _, _ => false

def demoCompleteNodes (B : Nat) : Nat :=
  match demoExpand B with
  | .complete g => g.nodes.size
  | .fail _ _ => 0

private def reasonTag : RejectReason → String
  | .invalidEntry => "InvalidEntry"
  | .limitExceeded => "LimitExceeded"
  | .unsupported => "Unsupported"
  | .unboundTarget => "UnboundTarget"
  | .undefinedSrc => "UndefinedSrc"
  | .localReject => "LocalReject"

private def dirTag : Direction → String
  | .only => "Only"
  | .taken => "Taken"
  | .notTaken => "NotTaken"

/-- JSON snapshot after `steps` expandOne calls (or earlier terminal).
Node payload is SemState σ=(E,P) per `doc/NodeInference/语义状态与节点快照.md`. -/
def demoSnapshot (steps budget : Nat) : String :=
  let pack (nodes : Array Node) (edges : Array Edge) (work : List NodeId)
      (fuel : Nat) (status : String) (reason : Option RejectReason) (log : String) : String :=
    let nodeStrs := Id.run do
      let mut acc : List String := []
      for i in [:nodes.size] do
        if let some n := nodes[i]? then
          let (ej, pj) := renderSemStateJson n.state
          let loc := match n.loc with | .exit => "exit" | .pos j => toString j
          acc := acc ++
            [s!"\{\"id\":{i},\"loc\":\"{loc}\",\"exprs\":[{ej}],\"predicates\":[{pj}]}"]
      pure (String.intercalate "," acc)
    let edgeStrs := String.intercalate ","
      (edges.toList.map fun e =>
        s!"\{\"src\":{e.src},\"dir\":\"{dirTag e.dir}\",\"dst\":{e.dst}}")
    let workStr := String.intercalate "," (work.map toString)
    let reasonField := match reason with
      | none => "null"
      | some r => s!"\"{reasonTag r}\""
    s!"\{\"status\":\"{status}\",\"reason\":{reasonField},\"fuel\":{fuel},\"work\":[{workStr}],\"nodes\":[{nodeStrs}],\"edges\":[{edgeStrs}],\"log\":[\"{log}\"]}"
  match demoInit budget with
  | .error reason =>
      pack #[] #[] [] 0 "fail" (some reason) "init"
  | .ok ws0 =>
    match expandN demoProgLen demoStep ws0 steps with
    | Sum.inl (.complete g) =>
        pack g.nodes g.edges [] 0 "complete" none "complete"
    | Sum.inl (.fail reason g) =>
        pack g.nodes g.edges [] 0 "fail" (some reason) "fail"
    | Sum.inr ws =>
        -- Empty Work is Complete at the next loop head (§16); surface it without an extra step.
        if ws.work.isEmpty then
          pack ws.nodes ws.edges [] ws.fuel "complete" none "complete"
        else
          pack ws.nodes ws.edges ws.work ws.fuel "running" none s!"steps={steps}"

@[export lean_path_demo_check]
def exportDemoCheck (_unused : UInt32) : UInt32 :=
  if demoCheck then 1 else 0

@[export lean_path_demo_nodes]
def exportDemoNodes (budget : UInt32) : UInt32 :=
  UInt32.ofNat (demoCompleteNodes budget.toNat)

@[export lean_path_demo_snapshot]
def exportDemoSnapshot (steps budget : UInt32) : String :=
  demoSnapshot steps.toNat budget.toNat

end CommonMath
