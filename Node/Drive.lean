import Node.Path

namespace Node
open Core

/-!
One step of 标准推理 or Taken推演. See `doc/NodeInference/分支合并处理.md`.

`history` takes the not_taken interval as pairs `(E_i, O_i)` and returns registers.
Positions here are 0-based indexes. The document counts instructions from 1.
-/

/-- How many only-taken returns to the same parent this frame may still take. -/
def loopLimit : Nat := 128

inductive DriveLabel where
  | standard (j : Nat) (state : SemState)
  | taken
      (parent : Nat) (parentState : SemState)
      (here : Nat) (hereState : SemState)
      (oldNotTaken : SemState)
      (interval : List (List Expr × List Predicate))
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
  | .regVar _ r => [r]
  | .app _ _ args => args.flatMap termRegs
  | .const _ _ | .var _ _ => []

private def exprRegs (e : Expr) : List Reg :=
  e.reg :: termRegs e.term

private def predRegs : Predicate → List Reg
  | .helper _ _ args => args.flatMap termRegs
  | .branch _ _ cond => termRegs cond.lhs ++ termRegs cond.rhs
  | .ret term => termRegs term
  | .mapWrite _ map key _ _ source =>
      termRegs map ++ key.flatMap termRegs ++ termRegs source
  | .packetWrite _ _ _ _ source _ => termRegs source

/-- Registers overwritten again later in the interval, or present in some
`E_i` and absent from every `O_i`. -/
def history (steps : List (List Expr × List Predicate)) : List Reg :=
  let writes := steps.map fun (exprs, _) => exprs.bindings.map (·.reg)
  let overwritten := (writes.flatten.eraseDups).filter fun r =>
    (writes.filter (·.contains r)).length ≥ 2
  let inExprs := (steps.flatMap fun (exprs, _) => exprs.flatMap exprRegs).eraseDups
  let inObs := (steps.flatMap fun (_, obs) => obs.flatMap predRegs).eraseDups
  let unused := inExprs.filter fun r => !inObs.contains r
  (overwritten ++ unused).eraseDups

def valueDiffRegs (oldExprs newExprs : List Expr) : List Reg :=
  let regs := (oldExprs.bindings.map (·.reg) ++ newExprs.bindings.map (·.reg)).eraseDups
  regs.filter fun r => oldExprs.lookupEq r != newExprs.lookupEq r

def diffCovered (oldExprs newExprs : List Expr) (covered : List Reg) : Bool :=
  (valueDiffRegs oldExprs newExprs).all (covered.contains ·)

private def place (progLen : Nat) (σ : SemState) (c : Candidate) :
    Except RejectReason (Option (Nat × SemState)) :=
  match c.loc with
  | .exit => .ok none
  | .pos k =>
      if k ≥ progLen then
        .error .unboundTarget
      else do
        let state ← applyLocal σ c.E_k c.P_k c.memWrites
        pure (some (k, state))

private def asStandard (loopsLeft : Option Nat) (placed : Option (Nat × SemState)) : DriveResult :=
  match placed with
  | none => .stop .reachedExit
  | some (k, state) => .labels loopsLeft [.standard k state]

def driveStandard (step : Nat → SemState → StepResult) (progLen j : Nat)
    (σ : SemState) : DriveResult :=
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

def driveTaken (step : Nat → SemState → StepResult) (progLen : Nat)
    (parent : Nat) (_parentState hereState oldNotTaken : SemState)
    (here : Nat) (interval : List (List Expr × List Predicate)) (loopsLeft : Nat) : DriveResult :=
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
              let regs := history interval
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

private def state (n : Nat) : SemState :=
  ⟨eq0 n, [], .empty⟩

private def go (j : Nat) (dir : Direction) : Candidate :=
  { dir, loc := .pos j, E_k := [], P_k := [] }

private def demo (j : Nat) (_ : SemState) : StepResult :=
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

private def backBoth (_ : Nat) (_ : SemState) : StepResult :=
  .candidates [go 1 .notTaken, go 2 .taken]

#guard
  match driveTaken backBoth 4 0 (state 0) (state 0) (state 0) 0 [] 128 with
  | .stop (.reject .localReject) => true
  | _ => false

private def backNot (j : Nat) (_ : SemState) : StepResult :=
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

private def backTaken (j : Nat) (_ : SemState) : StepResult :=
  .candidates [go (j + 1) .taken]

#guard
  match driveTaken backTaken 4 0 (state 0) (state 0) (state 0) 0 [] 1 with
  | .labels (some 0) [.standard 1 _] => true
  | _ => false

#guard
  match driveTaken backTaken 4 0 (state 0) (state 0) (state 0) 0 [] 0 with
  | .stop (.reject .localReject) => true
  | _ => false

end Node
