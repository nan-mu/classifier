import EBPF.Encode
import Core.Update
import EBPF.Helper
import Node.Path

namespace EBPF
open Core Node

private def fullReg (E : List Expr) (r : Nat) : Option Term := do
  if r > 10 then none
  let t ← readInterval E (Reg.real64 r)
  if t.width == .w64 && t.semanticBits == 64 then some t else none

private def jumpSource (E : List Expr) : Source → Option Term
  | .imm bits => some (Term.C64 (M 64 (s 32 bits.toNat)))
  | .reg r => fullReg E r

private def jumpRel : Width → JumpOp → Rel
  | .w64, .jeq => .eq
  | .w64, .jne => .ne
  | .w64, .jgt => .gtu
  | .w64, .jge => .geu
  | .w64, .jlt => .ltu
  | .w64, .jle => .leu
  | .w64, .jsgt => .gts
  | .w64, .jsge => .ges
  | .w64, .jslt => .lts
  | .w64, .jsle => .les
  | .w64, .jset => .bitsnz 64
  | .w32, .jeq => .eqN 32
  | .w32, .jne => .neN 32
  | .w32, .jgt => .gtuN 32
  | .w32, .jge => .geuN 32
  | .w32, .jlt => .ltuN 32
  | .w32, .jle => .leuN 32
  | .w32, .jsgt => .gtsN 32
  | .w32, .jsge => .gesN 32
  | .w32, .jslt => .ltsN 32
  | .w32, .jsle => .lesN 32
  | .w32, .jset => .bitsnz 32

/-- Jump offsets count raw slots, including LDDW continuation slots. -/
private def jumpTarget (I : Array Insn) (j : Nat) (offset : Int) : Option Location :=
  let target := Int.ofNat j + 1 + offset
  if target < 0 || target ≥ Int.ofNat I.size then none
  else if I[target.toNat]? == some .continuation then none
  else some (.pos target.toNat)

private partial def containsInputByte : Term → Bool
  | .app _ (.inputByte _) _ => true
  | .app _ _ args => args.any containsInputByte
  | _ => false

/-- Straight-line `exit`, or `r0 = imm` followed by `exit`. Not a jump.
XDP_PASS and XDP_DROP are non-zero immediates. RV treats every `li a0`. -/
private def straightAbort (I : Array Insn) (j : Nat) : Bool :=
  match I[j]? with
  | some .exit => true
  | some (.mov _ dst (.imm _)) => dst == 0 && I[j + 1]? == some .exit
  | _ => false

private def abortLoc (I : Array Insn) : Option Location → Bool
  | some .exit => true
  | some (.pos j) => straightAbort I j
  | none => false

private def comparisonCandidate (I : Array Insn) (j : Nat) (offset : Int)
    (dir : BranchDirection) (lhs : Term) (e : Expr) : Except RejectReason Candidate := do
  let some target := jumpTarget I j offset | throw .unboundTarget
  let direction := match dir with | .taken => Direction.taken | .notTaken => .notTaken
  pure ⟨direction, target, (let row := solveExpr e; if Expr.nil.contains row then Expr.nil else Expr.nil ++ [row]),
    [.branch (j + 1) dir ⟨lhs, e.rel, e.term⟩]⟩

/-- An early return is still a successor. Landing on `.exit` records the branch
and does not step the `exit` instruction, so the arm has no `ret` observation.
That matches RV `abortExit`. -/
private def abortExit (j : Nat) (dir : BranchDirection) (lhs : Term) (e : Expr) : Candidate :=
  let direction := match dir with | .taken => Direction.taken | .notTaken => .notTaken
  ⟨direction, .exit, (let row := solveExpr e; if Expr.nil.contains row then Expr.nil else Expr.nil ++ [row]),
    [.branch (j + 1) dir ⟨lhs, e.rel, e.term⟩]⟩

private def branchCandidates (I : Array Insn) (j : Nat) (E : List Expr)
    (width : Width) (op : JumpOp) (dst : Nat) (src : Source) (offset : Int) :
    Except RejectReason (List Candidate) := do
  let some lhs := fullReg E dst | throw .undefinedSrc
  let some rhs := jumpSource E src | throw .undefinedSrc
  let rel := jumpRel width op
  let taken := Expr.mkRel (Reg.real64 dst) rel rhs
  let fall := Expr.mkRel (Reg.real64 dst) rel.compl rhs
  match taken.decideWith lhs with
  | some true => pure [← comparisonCandidate I j offset .taken lhs taken]
  | some false => pure [← comparisonCandidate I j 0 .notTaken lhs fall]
  | none =>
    -- A packet byte has no single concrete outcome. Both live arms would copy
    -- an unrolled body. An arm that is only an early return is one exit node,
    -- and RV already emits that fork. Dropping it leaves the other arch with
    -- a one-sided edge, so the compare segments diverge.
    if containsInputByte lhs || containsInputByte rhs then
      let takenLoc := jumpTarget I j offset
      let fallLoc := jumpTarget I j 0
      let takenAborts := abortLoc I takenLoc
      let fallAborts := abortLoc I fallLoc
      if takenAborts || fallAborts then
        let takenArm ← if takenAborts then
            pure (abortExit j .taken lhs taken)
          else
            comparisonCandidate I j offset .taken lhs taken
        let fallArm ← if fallAborts then
            pure (abortExit j .notTaken lhs fall)
          else
            comparisonCandidate I j 0 .notTaken lhs fall
        pure [takenArm, fallArm]
      else
        pure [← comparisonCandidate I j 0 .notTaken lhs fall]
    else
      let takenCandidate ← comparisonCandidate I j offset .taken lhs taken
      let fallCandidate ← comparisonCandidate I j 0 .notTaken lhs fall
      pure [takenCandidate, fallCandidate]

private def wideImmediate (I : Array Insn) (E : List Expr) (j dst : Nat)
    (srcType : UInt8) (bits : UInt64) : Except RejectReason Candidate := do
  if dst > 9 || I[j + 1]? != some .continuation then throw .localReject
  let value ← match lddwBind E j with
    | .bound t => if t.width == .w64 then pure t else throw .undefinedSrc
    | .unbound =>
      if srcType == 0 then pure (Term.C64 bits.toNat) else throw .unsupported
  if j + 2 ≥ I.size then throw .unboundTarget
  pure ⟨.ok, .pos (j + 2), (update ⟨Expr.nil, []⟩ { exprs := [Expr.mkEq (Reg.real64 dst) (solve value)], predicates := [] }).exprs, []⟩

/-- All operands come from the executing pre-state. EXIT captures full-width r0;
falling off the sequence is never a return. Native helper calls freeze full-width
ABI observations and write r0, anchoring lookup Map word zero. -/
def ebpfStep (I : Array Insn) (event : NodeId)
    (j : Nat) (σ : State) : StepResult :=
  match I[j]? with
  | none => .reject .unboundTarget
  | some (.illegal _) => .reject .localReject
  | some .continuation => .reject .localReject
  | some (.callHelper id) =>
    if j + 1 ≥ I.size then .reject .unboundTarget
    else match parseHelperCall σ.exprs id.toNat with
      | .error reason => .reject reason
      | .ok call =>
        let frozen := freezeHelperArgs σ.exprs call σ.predicates
        match lookupAnchor σ.exprs event call frozen with
        | .error reason => .reject reason
        | .ok rows => .candidates [⟨.ok, .pos (j + 1), helperExpr event call ++ rows,
            [.helper event call.kind frozen]⟩]
  | some (.jcond width op dst src offset) =>
    match branchCandidates I j σ.exprs width op dst src offset with
    | .error reason => .reject reason
    | .ok cs => .candidates cs
  | some (.ja offset) =>
    match jumpTarget I j offset with
    | none => .reject .unboundTarget
    | some target => .candidates [⟨.ok, target, Expr.nil, []⟩]
  | some (.lddw dst srcType bits) =>
    match wideImmediate I σ.exprs j dst srcType bits with
    | .error reason => .reject reason
    | .ok candidate => .candidates [candidate]
  | some .exit =>
    match fullReg σ.exprs 0 with
    | some t => .candidates [⟨.ok, .exit, Expr.nil, [.ret t]⟩]
    | none => .reject .undefinedSrc
  | some i =>
    match exprEffects event σ.exprs i σ.predicates with
    | .error reason => .reject reason
    | .ok (effect, predicates) => if j + 1 < I.size then
        .candidates [⟨.ok, .pos (j + 1), effect.delta, predicates⟩]
      else .reject .unboundTarget

private def checkEntry : EntryParams :=
  ⟨Term.V64 1, Term.V64 0, Term.V32 2, 64⟩

private def aluExitSequenceCheck : Bool := Id.run do
  let I := decodeProgram #[0x00000007000000b7, 0x0000000100000007, 0x95]
  let p := checkEntry
  let .ok root := buildE0 p | return false
  let .candidates [mov] := ebpfStep I 0 0 root | return false
  let afterMov := update root { exprs := mov.E_k, predicates := mov.P_k }
  let .candidates [add] := ebpfStep I 1 1 afterMov | return false
  let afterAdd := update afterMov { exprs := add.E_k, predicates := add.P_k }
  let .candidates [exit] := ebpfStep I 2 2 afterAdd | return false
  let final := update afterAdd { exprs := exit.E_k, predicates := exit.P_k }
  return mov.dir == .ok && mov.loc == .pos 1 &&
    add.dir == .ok && add.loc == .pos 2 &&
    exit.dir == .ok && exit.loc == .exit &&
    root.exprs.lookupEq (Reg.real64 0) == none &&
    afterMov.exprs.lookupEq (Reg.real64 0) == some (Term.C64 7) &&
    final.exprs.lookupEq (Reg.real64 0) == some (Term.C64 8) &&
    final.exprs.lookupEq (Reg.real64 1) == some p.tCtx &&
    [root, afterMov, afterAdd].all (fun state => state.predicates.isEmpty) &&
    final.predicates == [.ret (Term.C64 8)]

#guard aluExitSequenceCheck
#guard match expr ((update ⟨Expr.nil, []⟩ { exprs := [Expr.mkEq (Reg.real64 1) (solve (Term.V64 7))], predicates := [] }).exprs)
    (.mov .w64 0 (.reg 1)) with
  | some E => E.lookupEq (Reg.real64 0) == some (idStar .w64 (Term.V64 7))
  | none => false
#guard (expr Expr.nil (.binary .w64 .add 0 (.imm 1))).isNone
#guard (expr Expr.nil (.mov .w64 10 (.imm 1))).isNone
#guard match decodeInsnWord 0x00000000000010bf with
  | .mov .w64 0 (.reg 1) => true
  | _ => false
#guard [0x00000000000100b7, 0x0000000000000ab7,
    0x00000001000010bf, 0x0000000000000195].all (fun w =>
  match decodeInsnWord w with
  | .illegal _ => true
  | _ => false)
#guard match buildE0 ⟨Term.V32 1, Term.V64 0, Term.V32 2, 64⟩ with
  | .error .invalidEntry => true
  | _ => false
#guard match expr Expr.nil (.mov .w64 0 (.imm 0xffffffff)) with
  | some E => E.lookupEq (Reg.real64 0) == some (Term.C64 0xffffffffffffffff)
  | none => false

private def halves (E : List Expr) (r low high : Nat) : Bool :=
  match readInterval E (.real r 0 32), readInterval E (.real r 32 64) with
  | some lo, some hi => eval (solve lo) == some low && eval (solve hi) == some high
  | _, _ => false

#guard match expr Expr.nil (.mov .w32 0 (.imm 0xffffffff)) with
  | some E => halves E 0 0xffffffff 0
  | none => false
#guard match expr ((update ⟨Expr.nil, []⟩ { exprs := [Expr.mkEq (Reg.real64 0) (solve (Term.C64 0xffffffff))], predicates := [] }).exprs)
    (.binary .w32 .add 0 (.imm 1)) with
  | some E => halves E 0 0 0
  | none => false
#guard match ebpfStep #[.exit] 0 0 State.empty with
  | .reject .undefinedSrc => true
  | _ => false
#guard match ebpfStep (decodeProgram #[0]) 0 0 State.empty with
  | .reject .localReject => true
  | _ => false
#guard match ebpfStep #[.mov .w64 0 (.imm 1)] 0 0 State.empty with
  | .reject .unboundTarget => true
  | _ => false

private def oneCandidateCheck (result : StepResult) (dir : Direction) (loc : Location)
    (E : List Expr) (P : List Predicate) : Bool :=
  match result with
  | .candidates [c] => c.dir == dir && c.loc == loc && c.E_k == E && c.P_k == P
  | _ => false

private def branchCheck : Bool := Id.run do
  let I := #[.jcond .w64 .jeq 1 (.reg 2) 1, .exit, .exit]
  let lhs := Term.V64 7
  let rhs := Term.V64 8
  let E := (update ⟨Expr.nil, []⟩ { exprs := [Expr.mkEq (Reg.real64 1) (solve lhs)], predicates := [] }).exprs |> (fun acc => (update ⟨acc, []⟩ { exprs := [Expr.mkEq (Reg.real64 2) (solve rhs)], predicates := [] }).exprs)
  let .candidates [taken, fall] := ebpfStep I 11 0 ⟨E, []⟩ | return false
  let afterTaken := update ⟨E, []⟩ { exprs := taken.E_k, predicates := taken.P_k }
  return taken.dir == .taken && taken.loc == .pos 2 &&
    taken.E_k == [⟨Reg.real64 1, .eq, rhs⟩] &&
    taken.P_k == [.branch 1 .taken ⟨lhs, .eq, rhs⟩] &&
    fall.dir == .notTaken && fall.loc == .pos 1 &&
    fall.E_k == [⟨Reg.real64 1, .ne, rhs⟩] &&
    fall.P_k == [.branch 1 .notTaken ⟨lhs, .ne, rhs⟩] &&
    afterTaken.exprs.lookupEq (Reg.real64 1) == some lhs

#guard branchCheck

/-- A packet compare whose taken arm is `exit` keeps that arm as `.exit`.
The fallthrough stays a real successor. No `ret` is added on the exit arm. -/
private def packetAbortArmCheck : Bool := Id.run do
  let byte := Term.app .w32 (.inputByte 0) [Term.C32 0, Term.C32 12]
  let lhs := idStar .w64 (Term.app .w64 (.zext 32 .w64 32) [byte])
  let I := #[.jcond .w32 .jne 1 (.imm 8) 1, .mov .w64 2 (.imm 1), .exit]
  let E := (update ⟨Expr.nil, []⟩ { exprs := [Expr.mkEq (Reg.real64 1) (solve lhs)], predicates := [] }).exprs
  match ebpfStep I 0 0 ⟨E, []⟩ with
  | .candidates [abort, fall] =>
    abort.dir == .taken && abort.loc == .exit &&
      fall.dir == .notTaken && fall.loc == .pos 1
  | _ => false

/-- Both arms of a packet compare stay in the program. Keep the fallthrough only. -/
private def packetLiveArmsCheck : Bool := Id.run do
  let byte := Term.app .w32 (.inputByte 0) [Term.C32 0, Term.C32 12]
  let lhs := idStar .w64 (Term.app .w64 (.zext 32 .w64 32) [byte])
  let I := #[.jcond .w32 .jne 1 (.imm 8) 1, .mov .w64 2 (.imm 1), .mov .w64 3 (.imm 1)]
  let E := (update ⟨Expr.nil, []⟩ { exprs := [Expr.mkEq (Reg.real64 1) (solve lhs)], predicates := [] }).exprs
  match ebpfStep I 0 0 ⟨E, []⟩ with
  | .candidates [c] => c.dir == .notTaken && c.loc == .pos 1
  | _ => false

#guard packetAbortArmCheck
#guard packetLiveArmsCheck
#guard oneCandidateCheck
    (ebpfStep #[.jcond .w64 .jne 1 (.imm 2) 1, .exit, .exit] 0 0
      ⟨(update ⟨Expr.nil, []⟩ { exprs := [Expr.mkEq (Reg.real64 1) (solve (Term.C64 1))], predicates := [] }).exprs, []⟩)
    .taken (.pos 2) ((let row := solveExpr ⟨Reg.real64 1, .ne, Term.C64 2⟩; if Expr.nil.contains row then Expr.nil else Expr.nil ++ [row]))
    [.branch 1 .taken ⟨Term.C64 1, .ne, Term.C64 2⟩]
-- JMP32 ignores high bits; its excluded Taken target need not be in range.
#guard oneCandidateCheck
    (ebpfStep #[.jcond .w32 .jgt 1 (.reg 2) 99, .exit] 0 0
      ⟨(update ⟨Expr.nil, []⟩ { exprs := [Expr.mkEq (Reg.real64 1) (solve (Term.C64 0x100000001))], predicates := [] }).exprs
        |> (fun acc => (update ⟨acc, []⟩ { exprs := [Expr.mkEq (Reg.real64 2) (solve (Term.C64 2))], predicates := [] }).exprs), []⟩)
    .notTaken (.pos 1)
    ((let row := solveExpr ⟨Reg.real64 1, .leuN 32, Term.C64 2⟩; if Expr.nil.contains row then Expr.nil else Expr.nil ++ [row]))
    [.branch 1 .notTaken ⟨Term.C64 0x100000001, .leuN 32, Term.C64 2⟩]
#guard oneCandidateCheck
    (ebpfStep #[.jcond .w32 .jeq 1 (.imm 1) 0, .exit] 0 0
      ⟨(update ⟨Expr.nil, []⟩ { exprs := [Expr.mkEq (Reg.real64 1) (solve (Term.C64 0x100000001))], predicates := [] }).exprs, []⟩)
    .taken (.pos 1) ((let row := solveExpr ⟨Reg.real64 1, .eqN 32, Term.C64 1⟩; if Expr.nil.contains row then Expr.nil else Expr.nil ++ [row]))
    [.branch 1 .taken ⟨Term.C64 0x100000001, .eqN 32, Term.C64 1⟩]
#guard oneCandidateCheck
    (ebpfStep #[.jcond .w64 .jeq 1 (.imm 0xffffffff) 0, .exit] 0 0
      ⟨(update ⟨Expr.nil, []⟩ { exprs := [Expr.mkEq (Reg.real64 1) (solve (Term.C64 0xffffffffffffffff))], predicates := [] }).exprs, []⟩)
    .taken (.pos 1)
    ((let row := solveExpr ⟨Reg.real64 1, .eq, Term.C64 0xffffffffffffffff⟩; if Expr.nil.contains row then Expr.nil else Expr.nil ++ [row]))
    [.branch 1 .taken ⟨Term.C64 0xffffffffffffffff, .eq, Term.C64 0xffffffffffffffff⟩]
#guard match ebpfStep #[.jcond .w64 .jeq 1 (.imm 0) 1, .exit, .continuation]
0 0 ⟨(update ⟨Expr.nil, []⟩ { exprs := [Expr.mkEq (Reg.real64 1) (solve (Term.V64 1))], predicates := [] }).exprs, []⟩ with
  | .reject .unboundTarget => true
  | _ => false
#guard match ebpfStep #[.jcond .w64 .jeq 1 (.imm 0) 1, .continuation, .exit]
0 0 ⟨(update ⟨Expr.nil, []⟩ { exprs := [Expr.mkEq (Reg.real64 1) (solve (Term.V64 1))], predicates := [] }).exprs, []⟩ with
  | .reject .unboundTarget => true
  | _ => false
#guard match ebpfStep #[.jcond .w64 .jeq 1 (.reg 2) 0, .exit]
0 0 ⟨(update ⟨Expr.nil, []⟩ { exprs := [Expr.mkEq (Reg.real64 1) (solve (Term.C64 1))], predicates := [] }).exprs, []⟩ with
  | .reject .undefinedSrc => true
  | _ => false
#guard match ebpfStep #[.jcond .w32 .jeq 1 (.imm 1) 0, .exit] 0 0
    ⟨[⟨Reg.real64 1, .eq, Term.C32 1⟩], []⟩ with
  | .reject .undefinedSrc => true
  | _ => false
#guard oneCandidateCheck (ebpfStep #[.ja 1, .exit, .exit] 0 0 State.empty)
    .ok (.pos 2) Expr.nil []
#guard match ebpfStep #[.ja (-2), .exit] 0 0 State.empty with
  | .reject .unboundTarget => true
  | _ => false
#guard match ebpfStep #[.ja 1, .exit, .continuation] 0 0 State.empty with
  | .reject .unboundTarget => true
  | _ => false
#guard match ebpfStep #[.continuation] 0 0 State.empty with
  | .reject .localReject => true
  | _ => false
#guard match ebpfStep #[] 0 0 State.empty with
  | .reject .unboundTarget => true
  | _ => false

#guard oneCandidateCheck
    (ebpfStep #[.lddw 1 0 0x1122334455667788, .continuation, .exit]
0 0 State.empty)
    .ok (.pos 2) ((update ⟨Expr.nil, []⟩ { exprs := [Expr.mkEq (Reg.real64 1) (solve (Term.C64 0x1122334455667788))], predicates := [] }).exprs) []
#guard oneCandidateCheck
    (ebpfStep #[.lddw 1 0 0, .continuation, .exit] 0 0 State.empty)
    .ok (.pos 2) ((update ⟨Expr.nil, []⟩ { exprs := [Expr.mkEq (Reg.real64 1) (solve (Term.C64 0))], predicates := [] }).exprs) []
#guard oneCandidateCheck
    (ebpfStep #[.lddw 1 0 0, .continuation, .exit] 0 0
      ⟨(bindField Expr.nil (.lddw 0) (Term.V64 9)).getD [], []⟩)
    .ok (.pos 2) ((update ⟨Expr.nil, []⟩ { exprs := [Expr.mkEq (Reg.real64 1) (solve (Term.V64 9))], predicates := [] }).exprs) []
#guard oneCandidateCheck
    (ebpfStep #[.lddw 1 1 0, .continuation, .exit] 0 0
      ⟨(bindField Expr.nil (.lddw 0) (Term.V64 9)).getD [], []⟩)
    .ok (.pos 2) ((update ⟨Expr.nil, []⟩ { exprs := [Expr.mkEq (Reg.real64 1) (solve (Term.V64 9))], predicates := [] }).exprs) []
#guard match ebpfStep #[.lddw 1 1 0, .continuation, .exit] 0 0 State.empty with
  | .reject .unsupported => true
  | _ => false
#guard match ebpfStep #[.lddw 10 0 0, .continuation, .exit]
0 0 State.empty with
  | .reject .localReject => true
  | _ => false
#guard match ebpfStep #[.lddw 1 0 0, .exit] 0 0 State.empty with
  | .reject .localReject => true
  | _ => false
#guard match ebpfStep #[.lddw 1 0 0, .continuation] 0 0 State.empty with
  | .reject .unboundTarget => true
  | _ => false
#guard match ebpfStep #[.callHelper 1, .exit] 0 0
    ⟨(update ⟨Expr.nil, []⟩ { exprs := [Expr.mkEq (Reg.real64 0) (solve (Term.C64 1))], predicates := [] }).exprs, []⟩ with
  | .reject .undefinedSrc => true
  | _ => false
#guard match ebpfStep #[.callHelper 1] 0 0 State.empty with
  | .reject .unboundTarget => true
  | _ => false
#guard oneCandidateCheck
    (ebpfStep #[.callHelper 999, .exit] 7 0 State.empty)
    .ok (.pos 1) ((update ⟨Expr.nil, []⟩ { exprs := [Expr.mkEq (Reg.real64 0) (solve (Term.C64 18446744073709551615))], predicates := [] }).exprs)
    [.helper 7 (.unsupported 999) []]
#guard oneCandidateCheck
    (ebpfStep #[.exit] 0 0
      ⟨(update ⟨Expr.nil, []⟩ { exprs := [Expr.mkEq (Reg.real64 0) (solve (Term.C64 1))], predicates := [] }).exprs, []⟩)
    .ok .exit Expr.nil [.ret (Term.C64 1)]
#guard match ebpfStep #[.exit] 0 0
    ⟨[⟨Reg.real64 0, .eq, Term.C32 1⟩], []⟩ with
  | .reject .undefinedSrc => true
  | _ => false

/-- The observation freezes the full source, while Expr writes exactly the
two little-endian byte cells. Out-of-bounds resolution returns no candidate. -/
private def packetStoreObservationCheck : Bool := Id.run do
  let p := checkEntry
  let .ok root := buildE0 p | return false
  let rooted := host p root.exprs
  let source := Term.C64 0x1122334455667788
  let .ok (loaded, []) := exprEffects 0 rooted (.ldx 4 2 1 0) | return false
  let some packetBase := loaded.updates.lookupEq (Reg.real64 2) | return false
  let E := (update ⟨((update ⟨rooted, []⟩ { exprs := loaded.delta, predicates := [] }).exprs), []⟩ { exprs := [Expr.mkEq (Reg.real64 0) (solve source)], predicates := [] }).exprs
    |> (fun acc => (update ⟨acc, []⟩ { exprs := [Expr.mkEq (Reg.real64 2) (solve (addStar .w64 packetBase (Term.C64 2)))], predicates := [] }).exprs)
  let .ok (.packet access) := resolveAccess E 2 3 2 true | return false
  let .candidates [c] := ebpfStep #[.stx 2 2 0 3, .exit] 77 0 ⟨E, []⟩ | return false
  let .reject .undefinedSrc := ebpfStep #[.stx 2 2 0 61, .exit] 78 0 ⟨E, []⟩ | return false
  let .candidates [stack] := ebpfStep #[.stx 4 10 0 (-4), .exit] 79 0 ⟨E, []⟩ | return false
  let stored := (update ⟨E, []⟩ { exprs := c.E_k, predicates := [] }).exprs
  let some low := readInterval stored (.packet 40 48) | return false
  let some high := readInterval stored (.packet 48 56) | return false
  let some stackTerm := readInterval ((update ⟨E, []⟩ { exprs := stack.E_k, predicates := [] }).exprs) (.stack (508 * 8) (508 * 8 + 32))
    | return false
  return access.constOffset? == some 5 && access.bytes == 2 &&
    eval (solve low) == some 0x88 && eval (solve high) == some 0x77 &&
    eval (solve stackTerm) == some 0x55667788 &&
    E.lookupEq (Reg.real64 0) == some source &&
    c.dir == .ok && c.loc == .pos 1 &&
    c.P_k == [.packetWrite 77 5 16 source] &&
    stack.dir == .ok && stack.loc == .pos 1 && stack.P_k.isEmpty

#guard packetStoreObservationCheck

/-- Packet stores have observations while Stack and Context cells do not. -/
private def storeObservationCategoryCheck : Bool := Id.run do
  let p := checkEntry
  let .ok root := buildE0 p | return false
  let rooted := host p root.exprs
  let .ok (loaded, []) := exprEffects 0 rooted (.ldx 4 2 1 0) | return false
  let E := (update ⟨((update ⟨rooted, []⟩ { exprs := loaded.delta, predicates := [] }).exprs), []⟩ { exprs := [Expr.mkEq (Reg.real64 0) (solve (Term.V64 9))], predicates := [] }).exprs
  let cases : List (Nat × Nat × Int) := [(2, 2, 3), (4, 10, -4), (4, 1, 0)]
  for (bytes, base, offset) in cases do
    let .ok access := resolveAccess E base offset bytes true | return false
    let .candidates [c] := ebpfStep #[.stx bytes base 0 offset, .exit] 88 0 ⟨E, []⟩
      | return false
    match access with
    | .packet a =>
      match a.constOffset? with
      | some o =>
        if c.P_k != [.packetWrite 88 o (8 * bytes) (Term.V64 9)] then return false
      | none => if !c.P_k.isEmpty then return false
    | .cell _ => if !c.P_k.isEmpty then return false
  return true

#guard storeObservationCategoryCheck
-- A map cell equality does not establish a map-address identity for STX.
#guard match ebpfStep #[.stx 4 2 0 0, .exit] 99 0
    ⟨(update ⟨Expr.nil, []⟩ { exprs := [Expr.mkEq (Reg.real64 2) (solve (Term.V64 99))], predicates := [] }).exprs
      |> (fun acc => (update ⟨acc, []⟩ { exprs := [Expr.mkEq (Reg.real64 0) (solve (Term.C64 1))], predicates := [] }).exprs)
      |> (fun acc => (update ⟨acc, []⟩ { exprs := [Expr.mkEq (.map 0 [] 0 32) (solve (Term.C32 0))], predicates := [] }).exprs), []⟩ with
  | .reject .undefinedSrc => true
  | _ => false

end EBPF
