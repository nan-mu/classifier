import CommonMath.Expand
import CommonMath.Term
import CommonMath.Reg
import CommonMath.Render

namespace CommonMath

/-- cmp merge is idempotent; empty Pi is identity even for nonempty P. -/
def demoCmpMergeIdempotent : Bool :=
  let p := Predicate.cmp .ltu (Term.V32 1) (Term.V32 2)
  match mergePredicate [p] [p, p], mergePredicate [p] [] with
  | .ok merged, .ok unchanged => merged == [p] && unchanged == [p]
  | _, _ => false

/-- Distinct conditions append once, and complementary conditions are retained. -/
def demoCmpMergeAppendCheck : Bool :=
  let p := Predicate.cmp .ltu (Term.V32 1) (Term.V32 2)
  let q := Predicate.cmp .geu (Term.V32 1) (Term.V32 2)
  match mergePredicate [p] [q, p, q] with
  | .ok merged => merged == [p, q]
  | _ => false

#guard demoCmpMergeIdempotent
#guard demoCmpMergeAppendCheck
#guard renderPredicateJson (.cmp .ltu (Term.V32 1) (Term.V32 2)) ==
  "{\"kind\":\"cmp\",\"rel\":\"ltu\",\"width\":32,\"lhs\":\"v32:1\",\"rhs\":\"v32:2\"}"

/-- Return observations append once, preserving existing conditions and order. -/
def demoRetMergeAppendCheck : Bool :=
  let p := Predicate.cmp .ltu (Term.V32 1) (Term.V32 2)
  let r := Predicate.ret (Term.V32 1)
  let s := Predicate.ret (Term.C32 0)
  match mergePredicate [p] [r, r, s, p, s], mergePredicate [r] [r, r],
      mergePredicate [r] [] with
  | .ok merged, .ok deduped, .ok unchanged =>
    merged == [p, r, s] && deduped == [r] && unchanged == [r]
  | _, _, _ => false

#guard demoRetMergeAppendCheck
#guard renderPredicateJson (.ret (Term.V32 1)) ==
  "{\"kind\":\"ret\",\"term\":\"v32:1\"}"
#guard renderPredicateJson (.ret (Term.C32 0)) ==
  "{\"kind\":\"ret\",\"term\":\"0\"}"

/-- Retained handoff check name: nonempty condition Pi now succeeds. -/
def demoNonemptyPiMergeCheck : Bool := demoCmpMergeAppendCheck

#guard demoNonemptyPiMergeCheck
#guard (Predicate.cmp .ltu (Term.V32 1) (Term.C32 2)).eval? == none
#guard (Predicate.cmp .lts (Term.C32 0xffffffff) (Term.C32 0)).eval? == some true
#guard (Predicate.cmp .ltu (Term.C32 0xffffffff) (Term.C32 0)).eval? == some false
#guard (Predicate.cmp .eq (.const .w32 0x100000000) (Term.C32 0)).eval? == some true
#guard renderPredicateJson (.cmp .geu (Term.V32 1) (Term.V32 2)) ==
  "{\"kind\":\"cmp\",\"rel\":\"geu\",\"width\":32,\"lhs\":\"v32:1\",\"rhs\":\"v32:2\"}"

/-! ## §18 bounded loop demo (`doc/common-math.md` §18) -/

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
        .candidates [⟨.taken, .pos 3, ExprSet.empty, []⟩]
      else
        .candidates [⟨.notTaken, .pos 1, ExprSet.empty, []⟩]
    | 1 =>
      .candidates [⟨.only, .pos 2, setR (r + 1), []⟩]
    | 2 =>
      .candidates [⟨.only, .pos 0, ExprSet.empty, []⟩]
    | 3 =>
      .candidates [⟨.only, .exit, ExprSet.empty, []⟩]
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
Node payload is SemState σ=(E,P) per `doc/common-math.md` §12. -/
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
