import Node.Path
import Expression.Interval

namespace Node
open Term Term.Value Expression Observation Interface Interface.Step Wire

/-!
One step of 标准推理 or Taken推演. See `doc/NodeInference/分支合并处理.md`.

`history` takes the not_taken interval as pairs `(E_i, O_i)` and the entry
bindings of that interval. It returns registers whose entry values do not
reach an observation. Positions here are 0-based indexes. The document counts
instructions from 1.
-/

/-- How many only-taken returns to the same parent this frame may still take. -/
def loopLimit : Nat := 128

inductive DriveLabel where
  | standard (j : Nat) (state : State)
  | taken
      (parent : Nat) (parentState : State)
      (here : Nat) (hereState : State)
      (oldNotTaken : State)
      (interval : List (List Expr × List Observation))
      (loopsLeft : Nat)
  deriving Repr

inductive DriveStop where
  | reject (reason : RejectReason)
  | reachedExit
  | sameObservation
  | end
  deriving DecidableEq, Repr

inductive DriveResult where
  | labels (loopsLeft : Option Nat) (next : List DriveLabel)
  | stop (reason : DriveStop)
  deriving Repr

private def termRegs : Term → List Reg
  | .regVar r => [r]
  | .app _ _ args => args.flatMap termRegs
  | .const _ _ | .var _ _ => []

private def predRegs : Observation → List Reg
  | .helper _ args => args.flatMap termRegs
  | .branch _ _ cond => termRegs cond.lhs ++ termRegs cond.rhs
  | .ret term => termRegs term
  | .mapWrite map key _ _ source =>
      termRegs map ++ key.flatMap termRegs ++ termRegs source
  | .packetWrite _ _ source => termRegs source

private def predAtoms : Observation → List Var
  | .helper _ args => args.flatMap FV
  | .branch _ _ cond => FV cond.lhs ++ FV cond.rhs
  | .ret term => FV term
  | .mapWrite map key _ _ source =>
      FV map ++ key.flatMap FV ++ FV source
  | .packetWrite _ _ source => FV source

private def atomOrigins (table : List (Var × Reg)) (atoms : List Var) : List Reg :=
  atoms.flatMap fun v =>
    table.filterMap fun pair => if pair.1 == v then some pair.2 else none

/-- Entry registers whose values reach some observation in `steps`.
A `regVar` counts directly. A plain variable counts when an entry binding's
term contains it, including inside a derived application. -/
def observationDeps (entry : List Expr)
    (steps : List (List Expr × List Observation)) : List Reg :=
  let table := entry.bindings.flatMap fun e =>
    (FV e.term).map fun v => (v, e.reg)
  let obs := steps.flatMap (·.2)
  ((obs.flatMap fun p => atomOrigins table (predAtoms p)) ++
    obs.flatMap predRegs).eraseDups

/-- Written registers whose entry values do not reach an observation.
A later overwrite does not drop a value already captured by an earlier observation. -/
def history (steps : List (List Expr × List Observation))
    (entry : List Expr := []) : List Reg :=
  let deps := observationDeps entry steps
  let written := (steps.flatMap fun (exprs, _) => exprs.bindings.map (·.reg)).eraseDups
  written.filter fun r => !deps.contains r

/-- A register that reaches an observation is not ignorable, whether or not it
is overwritten again later. -/
theorem observation_dep_not_ignorable
    (steps : List (List Expr × List Observation)) (entry : List Expr) (r : Reg)
    (h : r ∈ observationDeps entry steps) : r ∉ history steps entry := by
  intro hr
  simp only [history] at hr
  obtain ⟨_, hc⟩ := List.mem_filter.mp hr
  rw [show (observationDeps entry steps).contains r = true from
    List.contains_iff_mem.mpr h] at hc
  simp at hc

private def exactValueDiff (oldExprs newExprs : List Expr) : List Reg :=
  let regs := (oldExprs.bindings.map (·.reg) ++ newExprs.bindings.map (·.reg)).eraseDups
  regs.filter fun r => oldExprs.lookupEq r != newExprs.lookupEq r

private def resourceReps (regs : List Reg) : List Reg :=
  regs.foldl (fun acc r =>
    if acc.any (fun s => s.sameResource r) then acc else acc ++ [r]) []

private def segments : List Nat → List (Nat × Nat)
  | p :: q :: rest =>
    let tail := segments (q :: rest)
    if p < q then (p, q) :: tail else tail
  | _ => []

private def coversProbe (E : List Expr) (probe : Reg) : Bool :=
  E.bindings.any fun e =>
    e.reg.sameResource probe && decide (e.reg.lo ≤ probe.lo) &&
      decide (probe.hi ≤ e.reg.hi)

private def segmentDiff (oldExprs newExprs : List Expr) (probe : Reg) : Option Reg :=
  match readInterval oldExprs probe, readInterval newExprs probe with
  | some a, some b => if a == b then none else some probe
  | none, none =>
      if coversProbe oldExprs probe || coversProbe newExprs probe then some probe else none
  | _, _ => some probe

private def alignedValueDiff (oldExprs newExprs : List Expr) : List Reg :=
  let regs := oldExprs.bindings.map (·.reg) ++ newExprs.bindings.map (·.reg)
  (resourceReps regs).flatMap fun rep =>
    let points := (regs.filter (·.sameResource rep)).flatMap fun r => [r.lo, r.hi]
    (segments (points.eraseDups.mergeSort (· ≤ ·))).filterMap fun (p, q) =>
      segmentDiff oldExprs newExprs (rep.withInterval p q)

/-- Differences of value bindings after splitting each resource at every interval
endpoint. Equal fragments of one value are not a difference. An ill-typed side
keeps the whole-register comparison. -/
def valueDiffRegs (oldExprs newExprs : List Expr) : List Reg :=
  if !oldExprs.wellTyped || !newExprs.wellTyped then
    exactValueDiff oldExprs newExprs
  else
    alignedValueDiff oldExprs newExprs

def diffCovered (oldExprs newExprs : List Expr) (covered : List Reg) : Bool :=
  (valueDiffRegs oldExprs newExprs).all (covered.contains ·)

private def place (progLen : Nat) (σ : State) (c : Candidate) :
    Except RejectReason (Option (Nat × State)) :=
  match c.loc with
  | .exit => .ok none
  | .pos k =>
      if k ≥ progLen then
        .error .unboundTarget
      else do
        let state ← (Except.ok (update σ { exprs := c.E_k, predicates := c.P_k }))
        pure (some (k, state))

private def asStandard (loopsLeft : Option Nat) (placed : Option (Nat × State)) : DriveResult :=
  match placed with
  | none => .stop .reachedExit
  | some (k, state) => .labels loopsLeft [.standard k state]

def driveStandard (step : Nat → State → StepResult) (progLen j : Nat)
    (σ : State) : DriveResult :=
  match step j σ with
  | .reject reason => .stop (.reject reason)
  | .candidates [] => .stop .end
  | .candidates [c] =>
      match place progLen σ c with
      | .error reason => .stop (.reject reason)
      | .ok placed => asStandard none placed
  | .candidates cs =>
      match cs.find? (·.dir == .notTaken), cs.find? (·.dir == .taken) with
      | some notTaken, some taken =>
          if cs.length != 2 then
            .stop .end
          else
            match place progLen σ notTaken, place progLen σ taken with
            | .ok (some (jn, sn)), .ok (some (jt, st)) =>
                .labels none [
                  .standard jn sn,
                  .taken j σ jt st sn [] loopLimit
                ]
            | .error reason, _ => .stop (.reject reason)
            | _, .error reason => .stop (.reject reason)
            | _, _ => .stop .end
      | _, _ => .stop .end

def driveTaken (step : Nat → State → StepResult) (progLen : Nat)
    (parent : Nat) (_parentState hereState oldNotTaken : State)
    (here : Nat) (interval : List (List Expr × List Observation)) (loopsLeft : Nat) : DriveResult :=
  if here != parent then
    .labels (some loopsLeft) [.standard here hereState]
  else
    match step parent hereState with
    | .reject reason => .stop (.reject reason)
    | .candidates [] => .stop .end
    | .candidates [c] =>
        if c.dir == .notTaken then
          match place progLen hereState c with
          | .error reason => .stop (.reject reason)
          | .ok none => .stop .end
          | .ok (some (k, fresh)) =>
              let regs := history interval oldNotTaken.exprs
              if diffCovered oldNotTaken.exprs fresh.exprs regs then
                .stop .sameObservation
              else
                asStandard (some loopsLeft) (some (k, fresh))
        else if c.dir == .taken then
          if loopsLeft = 0 then
            .stop (.reject .localReject)
          else
            match place progLen hereState c with
            | .error reason => .stop (.reject reason)
            | .ok placed => asStandard (some (loopsLeft - 1)) placed
        else
          match place progLen hereState c with
          | .error reason => .stop (.reject reason)
          | .ok placed => asStandard (some loopsLeft) placed
    | .candidates cs =>
        match cs.find? (·.dir == .notTaken), cs.find? (·.dir == .taken) with
        | some _, some _ =>
            .stop (.reject .localReject)
        | _, _ => .stop .end

private def r0 : Reg := .real32 0

private def eq0 (n : Nat) : List Expr :=
  [Expr.mkEq r0 (.const .w32 n)]

private def state (n : Nat) : State :=
  ⟨eq0 n, []⟩

private def go (j : Nat) (dir : Direction) : Candidate :=
  { dir, loc := .pos j, E_k := [], P_k := [] }

private def demo (j : Nat) (_ : State) : StepResult :=
  if j == 0 then
    .candidates [go 1 .notTaken, go 2 .taken]
  else if j == 2 then
    .candidates [go 0 .ok]
  else
    .candidates [go (j + 1) .ok]

#guard
  match driveStandard demo 4 1 (state 0) with
  | .labels none [.standard 2 _] => true
  | _ => false

#guard
  match driveStandard demo 4 0 (state 0) with
  | .labels none [.standard 1 _, .taken 0 _ 2 _ _ [] 128] => true
  | _ => false

#guard
  match driveTaken demo 4 0 (state 0) (state 0) (state 0) 2 [] 128 with
  | .labels (some 128) [.standard 2 _] => true
  | _ => false

private def backBoth (_ : Nat) (_ : State) : StepResult :=
  .candidates [go 1 .notTaken, go 2 .taken]

#guard
  match driveTaken backBoth 4 0 (state 0) (state 0) (state 0) 0 [] 128 with
  | .stop (.reject .localReject) => true
  | _ => false

private def backNot (j : Nat) (_ : State) : StepResult :=
  .candidates [{
    dir := .notTaken
    loc := .pos (j + 1)
    E_k := eq0 2
    P_k := []
  }]

#guard (history [(eq0 1, []), (eq0 2, [])]).contains r0

#guard
  match driveTaken backNot 4 0 (state 0) (state 1) (state 1) 0
      [(eq0 1, []), (eq0 2, [])] 128 with
  | .stop .sameObservation => true
  | _ => false

#guard
  match driveTaken backNot 4 0 (state 0) (state 1) (state 1) 0 [] 128 with
  | .labels (some 128) [.standard 1 _] => true
  | _ => false

private def backTaken (j : Nat) (_ : State) : StepResult :=
  .candidates [go (j + 1) .taken]

#guard
  match driveTaken backTaken 4 0 (state 0) (state 0) (state 0) 0 [] 1 with
  | .labels (some 0) [.standard 1 _] => true
  | _ => false

#guard
  match driveTaken backTaken 4 0 (state 0) (state 0) (state 0) 0 [] 0 with
  | .stop (.reject .localReject) => true
  | _ => false

/-! Entry value captured before a later overwrite, and derived variables. -/

private def entryX : List Expr := [Expr.mkEq r0 (Term.V32 7)]

private def capturedThenOverwritten : List (List Expr × List Observation) :=
  [([], [Observation.packetWrite 0 8 (Term.V32 7)]), (eq0 0, []), (eq0 1, [])]

private def regVarThenOverwritten : List (List Expr × List Observation) :=
  [([], [Observation.packetWrite 0 8 (Term.regVar r0)]), (eq0 0, []), (eq0 1, [])]

private def derivedHelper : List (List Expr × List Observation) :=
  let arg := addStar .w32 (Term.V32 7) (Term.C32 1)
  [([Expr.mkEq r0 arg], [Observation.helper .clock [arg]])]

private def killedBeforeUse : List (List Expr × List Observation) :=
  [(eq0 0, []), (eq0 1, []), ([], [Observation.packetWrite 0 8 (Term.C32 0)])]

#guard r0 ∈ observationDeps entryX capturedThenOverwritten
#guard r0 ∉ history capturedThenOverwritten entryX
#guard r0 ∈ observationDeps [] regVarThenOverwritten
#guard r0 ∉ history regVarThenOverwritten
#guard r0 ∈ observationDeps entryX derivedHelper
#guard r0 ∉ history derivedHelper entryX
#guard (history killedBeforeUse entryX).contains r0

private def backConst (j : Nat) (_ : State) : StepResult :=
  .candidates [{
    dir := .notTaken
    loc := .pos (j + 1)
    E_k := eq0 1
    P_k := []
  }]

#guard
  match driveTaken backConst 4 0 (state 0) ⟨entryX, []⟩ ⟨entryX, []⟩ 0
      capturedThenOverwritten 128 with
  | .labels (some 128) [.standard 1 _] => true
  | _ => false

/-! Whole-register keys and equal bit slices of the same term. -/

private def r10 : Reg := .real32 10
private def wide : Term := Term.V32 3
private def other : Term := Term.V32 9

private def readSlice (t : Term) (lo hi : Nat) : Option Term :=
  readInterval [Expr.mkEq r10 t] (r10.withInterval lo hi)

#guard
  match readSlice wide 0 8, readSlice wide 8 32, readSlice other 8 32 with
  | some lo, some hi, some hiOther =>
      let whole := [Expr.mkEq r10 wide]
      let split := [Expr.mkEq (r10.withInterval 0 8) lo,
        Expr.mkEq (r10.withInterval 8 32) hi]
      let splitOther := [Expr.mkEq (r10.withInterval 0 8) lo,
        Expr.mkEq (r10.withInterval 8 32) hiOther]
      valueDiffRegs whole split == [] &&
        (valueDiffRegs whole splitOther).contains (r10.withInterval 8 32) &&
        (valueDiffRegs whole [Expr.mkEq r10 other]).contains r10
  | _, _, _ => false

end Node
