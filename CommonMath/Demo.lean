import CommonMath.Expand
import CommonMath.Term
import CommonMath.Reg

namespace CommonMath

/-! ## §18 bounded loop demo (`doc/common-math.md` §18) -/

private def demoReg : Reg := Reg.real32 1

private def readR (σ : SemState) : Option Nat :=
  match σ.exprs.lookupEq demoReg with
  | none => none
  | some t => eval (solve t)

private def setR (v : Nat) : ExprSet :=
  ExprSet.empty.insertEq demoReg (Term.C32 v)

private def predTaken : Predicate := ⟨1⟩
private def predNotTaken : Predicate := ⟨2⟩
private def predReturn : Predicate := ⟨3⟩

def demoProgLen : Nat := 4

/-- Single-instruction rule for the §18 listing. -/
def demoStep (j : Nat) (σ : SemState) : StepResult :=
  match readR σ with
  | none => .reject .undefinedSrc
  | some r =>
    match j with
    | 0 =>
      if r ≥ 3 then
        .candidates [⟨.taken, .pos 3, ExprSet.empty, [predTaken]⟩]
      else
        .candidates [⟨.notTaken, .pos 1, ExprSet.empty, [predNotTaken]⟩]
    | 1 =>
      .candidates [⟨.only, .pos 2, setR (r + 1), []⟩]
    | 2 =>
      .candidates [⟨.only, .pos 0, ExprSet.empty, []⟩]
    | 3 =>
      .candidates [⟨.only, .exit, ExprSet.empty, [predReturn]⟩]
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

/-- JSON snapshot after `steps` expandOne calls (or earlier terminal). -/
def demoSnapshot (steps budget : Nat) : String :=
  let pack (nodes : Array Node) (edges : Array Edge) (work : List NodeId)
      (fuel : Nat) (status : String) (reason : Option RejectReason) (log : String) : String :=
    let nodeStrs := Id.run do
      let mut acc : List String := []
      for i in [:nodes.size] do
        if let some n := nodes[i]? then
          let r := match readR n.state with | some v => toString v | none => "null"
          let preds := String.intercalate "," (n.state.predicates.map fun p => toString p.tag)
          let loc := match n.loc with | .exit => "exit" | .pos j => toString j
          acc := acc ++
            [s!"\{\"id\":{i},\"loc\":\"{loc}\",\"r\":{r},\"preds\":[{preds}]}"]
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
