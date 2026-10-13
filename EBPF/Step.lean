import EBPF.Encode
import EBPF.Memory
import PathMerge.Path

namespace EBPF
open ClassifierExpr PathMerge

/-- Static resource binding at the first raw slot of an LDDW instruction. -/
structure ResourceLocation where
  slot : Nat
  term : Option Term
  deriving Repr, Inhabited

structure StepContext where
  entry : EntryParams
  resourceLocations : List ResourceLocation := []
  deriving Repr, Inhabited

private def fullReg (E : ExprSet) (r : Nat) : Option Term := do
  if r > 10 then none else do
    let t ← E.lookupEq (Reg.real64 r)
    if t.width == .w64 then some t else none

private def jumpSource (E : ExprSet) : Source → Option Term
  | .imm bits => some (Term.C64 (M 64 (s 32 bits.toNat)))
  | .reg r => fullReg E r

private def jumpRel : Width → JumpOp → Rel
  | .w64, .jeq => .eq
  | .w64, .jne => .ne
  | .w64, .jgt => .gtu
  | .w32, .jeq => .eqN 32
  | .w32, .jne => .neN 32
  | .w32, .jgt => .gtuN 32

/-- Jump offsets count raw slots, including LDDW continuation slots. -/
private def jumpTarget (I : Array Insn) (j : Nat) (offset : Int) : Option Location :=
  let target := Int.ofNat j + 1 + offset
  if target < 0 || target ≥ Int.ofNat I.size then none
  else if I[target.toNat]? == some .continuation then none
  else some (.pos target.toNat)

private def comparisonCandidate (I : Array Insn) (j : Nat) (offset : Int)
    (dir : BranchDirection) (lhs : Term) (e : Expr) : Except RejectReason Candidate := do
  let some target := jumpTarget I j offset | throw .unboundTarget
  let direction := match dir with | .taken => Direction.taken | .notTaken => .notTaken
  pure ⟨direction, target, ExprSet.empty.insertConstraint e,
    [.branch (j + 1) dir ⟨lhs, e.rel, e.term⟩]⟩

private def branchCandidates (I : Array Insn) (j : Nat) (E : ExprSet)
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
    let takenCandidate ← comparisonCandidate I j offset .taken lhs taken
    let fallCandidate ← comparisonCandidate I j 0 .notTaken lhs fall
    pure [takenCandidate, fallCandidate]

private def wideImmediate (I : Array Insn) (context : StepContext) (j dst : Nat)
    (srcType : UInt8) (bits : UInt64) : Except RejectReason Candidate := do
  if dst > 9 || I[j + 1]? != some .continuation then throw .localReject
  let value ← match context.resourceLocations.find? (·.slot == j) with
    | some ⟨_, none⟩ => throw .unboundTarget
    | some ⟨_, some t⟩ =>
      if t.width == .w64 then pure t else throw .undefinedSrc
    | none =>
      if srcType == 0 then pure (Term.C64 bits.toNat) else throw .unsupported
  if j + 2 ≥ I.size then throw .unboundTarget
  pure ⟨.ok, .pos (j + 2), ExprSet.empty.insertEq (Reg.real64 dst) value, []⟩

/-- All operands come from the executing pre-state. EXIT captures full-width r0;
falling off the sequence is never a return. Native helper contracts are undefined
in doc/NodeInference/step.md and doc/Predicate/Helper谓词.md. -/
def ebpfStep (I : Array Insn) (context : StepContext) (event : NodeId)
    (j : Nat) (σ : SemState) : StepResult :=
  match I[j]? with
  | none => .reject .unboundTarget
  | some (.illegal _) => .reject .localReject
  | some .continuation => .reject .localReject
  | some (.callHelper _) => .reject .unsupported
  | some (.jcond width op dst src offset) =>
    match branchCandidates I j σ.exprs width op dst src offset with
    | .error reason => .reject reason
    | .ok cs => .candidates cs
  | some (.ja offset) =>
    match jumpTarget I j offset with
    | none => .reject .unboundTarget
    | some target => .candidates [⟨.ok, target, ExprSet.empty, []⟩]
  | some (.lddw dst srcType bits) =>
    match wideImmediate I context j dst srcType bits with
    | .error reason => .reject reason
    | .ok candidate => .candidates [candidate]
  | some .exit =>
    match fullReg σ.exprs 0 with
    | some t => .candidates [⟨.ok, .exit, ExprSet.empty, [.ret t]⟩]
    | none => .reject .undefinedSrc
  | some i@(.mov _ _ _) | some i@(.add _ _ _)
  | some i@(.ldx _ _ _ _) | some i@(.stx _ _ _ _) =>
    match exprEffects context.entry event σ.exprs i with
    | .error reason => .reject reason
    | .ok (effect, predicates) => if j + 1 < I.size then
        .candidates [⟨.ok, .pos (j + 1), effect.delta, predicates⟩]
      else .reject .unboundTarget

private def checkContext : StepContext :=
  ⟨⟨Term.V64 1, Term.V64 0, Term.V32 2, 64, 0, 0, 0⟩, []⟩

private def aluExitSequenceCheck : Bool := Id.run do
  let I := decodeProgram #[0x00000007000000b7, 0x0000000100000007, 0x95]
  let p := checkContext.entry
  let .ok root := buildE0 p | return false
  let .candidates [mov] := ebpfStep I checkContext 0 0 root | return false
  let .ok afterMov := PathMerge.applyLocal root mov.E_k mov.P_k | return false
  let .candidates [add] := ebpfStep I checkContext 1 1 afterMov | return false
  let .ok afterAdd := PathMerge.applyLocal afterMov add.E_k add.P_k | return false
  let .candidates [exit] := ebpfStep I checkContext 2 2 afterAdd | return false
  let .ok final := PathMerge.applyLocal afterAdd exit.E_k exit.P_k | return false
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
#guard match expr (ExprSet.empty.insertEq (Reg.real64 1) (Term.V64 7))
    (.mov .w64 0 (.reg 1)) with
  | some E => E.lookupEq (Reg.real64 0) == some (idStar .w64 (Term.V64 7))
  | none => false
#guard (expr ExprSet.empty (.add .w64 0 (.imm 1))).isNone
#guard (expr ExprSet.empty (.mov .w64 10 (.imm 1))).isNone
#guard match decodeInsnWord 0x00000000000010bf with
  | .mov .w64 0 (.reg 1) => true
  | _ => false
#guard [0x00000000000100b7, 0x0000000000000ab7,
    0x00000001000010bf, 0x0000000000000195].all (fun w =>
  match decodeInsnWord w with
  | .illegal _ => true
  | _ => false)
#guard match buildE0 ⟨Term.V32 1, Term.V64 0, Term.V32 2, 64, 0, 0, 0⟩ with
  | .error .invalidEntry => true
  | _ => false
#guard match expr ExprSet.empty (.mov .w64 0 (.imm 0xffffffff)) with
  | some E => E.lookupEq (Reg.real64 0) == some (Term.C64 0xffffffffffffffff)
  | none => false
#guard match expr ExprSet.empty (.mov .w32 0 (.imm 0xffffffff)) with
  | some E => E.lookupEq (Reg.real64 0) == some (Term.C64 0xffffffff)
  | none => false
#guard match expr (ExprSet.empty.insertEq (Reg.real64 0) (Term.C64 0xffffffff))
    (.add .w32 0 (.imm 1)) with
  | some E => E.lookupEq (Reg.real64 0) == some (Term.C64 0)
  | none => false
#guard match ebpfStep #[.exit] checkContext 0 0 SemState.empty with
  | .reject .undefinedSrc => true
  | _ => false
#guard match ebpfStep (decodeProgram #[0]) checkContext 0 0 SemState.empty with
  | .reject .localReject => true
  | _ => false
#guard match ebpfStep #[.mov .w64 0 (.imm 1)] checkContext 0 0 SemState.empty with
  | .reject .unboundTarget => true
  | _ => false

private def oneCandidateCheck (result : StepResult) (dir : Direction) (loc : Location)
    (E : ExprSet) (P : List Predicate) : Bool :=
  match result with
  | .candidates [c] => c.dir == dir && c.loc == loc && c.E_k == E && c.P_k == P
  | _ => false

private def branchCheck : Bool := Id.run do
  let I := #[.jcond .w64 .jeq 1 (.reg 2) 1, .exit, .exit]
  let lhs := Term.V64 7
  let rhs := Term.V64 8
  let E := ExprSet.empty.insertEq (Reg.real64 1) lhs |>.insertEq (Reg.real64 2) rhs
  let .candidates [taken, fall] := ebpfStep I checkContext 11 0 ⟨E, []⟩ | return false
  let .ok afterTaken := applyLocal ⟨E, []⟩ taken.E_k taken.P_k | return false
  return taken.dir == .taken && taken.loc == .pos 2 &&
    taken.E_k.entries.isEmpty && taken.E_k.constraints == [⟨Reg.real64 1, .eq, rhs⟩] &&
    taken.P_k == [.branch 1 .taken ⟨lhs, .eq, rhs⟩] &&
    fall.dir == .notTaken && fall.loc == .pos 1 &&
    fall.E_k.entries.isEmpty && fall.E_k.constraints == [⟨Reg.real64 1, .ne, rhs⟩] &&
    fall.P_k == [.branch 1 .notTaken ⟨lhs, .ne, rhs⟩] &&
    afterTaken.exprs.lookupEq (Reg.real64 1) == some lhs

#guard branchCheck
#guard oneCandidateCheck
    (ebpfStep #[.jcond .w64 .jne 1 (.imm 2) 1, .exit, .exit] checkContext 0 0
      ⟨ExprSet.empty.insertEq (Reg.real64 1) (Term.C64 1), []⟩)
    .taken (.pos 2) (ExprSet.empty.insertConstraint ⟨Reg.real64 1, .ne, Term.C64 2⟩)
    [.branch 1 .taken ⟨Term.C64 1, .ne, Term.C64 2⟩]
-- JMP32 ignores high bits; its excluded Taken target need not be in range.
#guard oneCandidateCheck
    (ebpfStep #[.jcond .w32 .jgt 1 (.reg 2) 99, .exit] checkContext 0 0
      ⟨ExprSet.empty.insertEq (Reg.real64 1) (Term.C64 0x100000001)
        |>.insertEq (Reg.real64 2) (Term.C64 2), []⟩)
    .notTaken (.pos 1)
    (ExprSet.empty.insertConstraint ⟨Reg.real64 1, .leuN 32, Term.C64 2⟩)
    [.branch 1 .notTaken ⟨Term.C64 0x100000001, .leuN 32, Term.C64 2⟩]
#guard oneCandidateCheck
    (ebpfStep #[.jcond .w32 .jeq 1 (.imm 1) 0, .exit] checkContext 0 0
      ⟨ExprSet.empty.insertEq (Reg.real64 1) (Term.C64 0x100000001), []⟩)
    .taken (.pos 1) (ExprSet.empty.insertConstraint ⟨Reg.real64 1, .eqN 32, Term.C64 1⟩)
    [.branch 1 .taken ⟨Term.C64 0x100000001, .eqN 32, Term.C64 1⟩]
#guard oneCandidateCheck
    (ebpfStep #[.jcond .w64 .jeq 1 (.imm 0xffffffff) 0, .exit] checkContext 0 0
      ⟨ExprSet.empty.insertEq (Reg.real64 1) (Term.C64 0xffffffffffffffff), []⟩)
    .taken (.pos 1)
    (ExprSet.empty.insertConstraint ⟨Reg.real64 1, .eq, Term.C64 0xffffffffffffffff⟩)
    [.branch 1 .taken ⟨Term.C64 0xffffffffffffffff, .eq, Term.C64 0xffffffffffffffff⟩]
#guard match ebpfStep #[.jcond .w64 .jeq 1 (.imm 0) 1, .exit, .continuation]
    checkContext 0 0 ⟨ExprSet.empty.insertEq (Reg.real64 1) (Term.V64 1), []⟩ with
  | .reject .unboundTarget => true
  | _ => false
#guard match ebpfStep #[.jcond .w64 .jeq 1 (.imm 0) 1, .continuation, .exit]
    checkContext 0 0 ⟨ExprSet.empty.insertEq (Reg.real64 1) (Term.V64 1), []⟩ with
  | .reject .unboundTarget => true
  | _ => false
#guard match ebpfStep #[.jcond .w64 .jeq 1 (.reg 2) 0, .exit]
    checkContext 0 0 ⟨ExprSet.empty.insertEq (Reg.real64 1) (Term.C64 1), []⟩ with
  | .reject .undefinedSrc => true
  | _ => false
#guard match ebpfStep #[.jcond .w32 .jeq 1 (.imm 1) 0, .exit] checkContext 0 0
    ⟨{ entries := [⟨Reg.real64 1, .eq, Term.C32 1⟩] }, []⟩ with
  | .reject .undefinedSrc => true
  | _ => false
#guard oneCandidateCheck (ebpfStep #[.ja 1, .exit, .exit] checkContext 0 0 SemState.empty)
    .ok (.pos 2) ExprSet.empty []
#guard match ebpfStep #[.ja (-2), .exit] checkContext 0 0 SemState.empty with
  | .reject .unboundTarget => true
  | _ => false
#guard match ebpfStep #[.ja 1, .exit, .continuation] checkContext 0 0 SemState.empty with
  | .reject .unboundTarget => true
  | _ => false
#guard match ebpfStep #[.continuation] checkContext 0 0 SemState.empty with
  | .reject .localReject => true
  | _ => false
#guard match ebpfStep #[] checkContext 0 0 SemState.empty with
  | .reject .unboundTarget => true
  | _ => false

#guard oneCandidateCheck
    (ebpfStep #[.lddw 1 0 0x1122334455667788, .continuation, .exit]
      checkContext 0 0 SemState.empty)
    .ok (.pos 2) (ExprSet.empty.insertEq (Reg.real64 1) (Term.C64 0x1122334455667788)) []
#guard match ebpfStep #[.lddw 1 0 0, .continuation, .exit]
    { checkContext with resourceLocations := [⟨0, none⟩] } 0 0 SemState.empty with
  | .reject .unboundTarget => true
  | _ => false
#guard oneCandidateCheck
    (ebpfStep #[.lddw 1 0 0, .continuation, .exit]
      { checkContext with resourceLocations := [⟨0, some (Term.V64 9)⟩] } 0 0 SemState.empty)
    .ok (.pos 2) (ExprSet.empty.insertEq (Reg.real64 1) (Term.V64 9)) []
#guard oneCandidateCheck
    (ebpfStep #[.lddw 1 1 0, .continuation, .exit]
      { checkContext with resourceLocations := [⟨0, some (Term.V64 9)⟩] } 0 0 SemState.empty)
    .ok (.pos 2) (ExprSet.empty.insertEq (Reg.real64 1) (Term.V64 9)) []
#guard match ebpfStep #[.lddw 1 1 0, .continuation, .exit]
    checkContext 0 0 SemState.empty with
  | .reject .unsupported => true
  | _ => false
#guard match ebpfStep #[.lddw 1 0 0, .continuation, .exit]
    { checkContext with resourceLocations := [⟨0, some (Term.V32 9)⟩] } 0 0 SemState.empty with
  | .reject .undefinedSrc => true
  | _ => false
#guard match ebpfStep #[.lddw 10 0 0, .continuation, .exit]
    checkContext 0 0 SemState.empty with
  | .reject .localReject => true
  | _ => false
#guard match ebpfStep #[.lddw 1 0 0, .exit] checkContext 0 0 SemState.empty with
  | .reject .localReject => true
  | _ => false
#guard match ebpfStep #[.lddw 1 0 0, .continuation] checkContext 0 0 SemState.empty with
  | .reject .unboundTarget => true
  | _ => false
#guard match ebpfStep #[.callHelper 1, .exit] checkContext 0 0
    ⟨ExprSet.empty.insertEq (Reg.real64 0) (Term.C64 1), []⟩ with
  | .reject .unsupported => true
  | _ => false
#guard oneCandidateCheck
    (ebpfStep #[.exit] checkContext 0 0
      ⟨ExprSet.empty.insertEq (Reg.real64 0) (Term.C64 1), []⟩)
    .ok .exit ExprSet.empty [.ret (Term.C64 1)]
#guard match ebpfStep #[.exit] checkContext 0 0
    ⟨{ entries := [⟨Reg.real64 0, .eq, Term.C32 1⟩] }, []⟩ with
  | .reject .undefinedSrc => true
  | _ => false

/-- The observation freezes the full source, while Expr writes exactly the
two little-endian byte cells. Out-of-bounds resolution returns no candidate. -/
private def packetStoreObservationCheck : Bool := Id.run do
  let p := checkContext.entry
  let .ok root := buildE0 p | return false
  let source := Term.C64 0x1122334455667788
  let .ok (loaded, []) := exprEffects p 0 root.exprs (.ldx 4 2 1 0) | return false
  let some packetBase := loaded.updates.lookupEq (Reg.real64 2) | return false
  let E := (root.exprs.override loaded.delta).insertEq (Reg.real64 0) source
    |>.insertEq (Reg.real64 2) (addStar .w64 packetBase (Term.C64 2))
  let .ok (.packet access) := resolveAccess p E 2 3 2 true | return false
  let .candidates [c] := ebpfStep #[.stx 2 2 0 3, .exit] checkContext 77 0 ⟨E, []⟩
    | return false
  let .reject .undefinedSrc := ebpfStep #[.stx 2 2 0 61, .exit]
    checkContext 78 0 ⟨E, []⟩ | return false
  let .candidates [stack] := ebpfStep #[.stx 4 10 0 (-4), .exit]
    checkContext 79 0 ⟨E, []⟩ | return false
  return access.κ == p.κPacket && access.offset == 5 && access.bytes == 2 &&
    E.lookupEq (Reg.real64 0) == some source &&
    c.dir == .ok && c.loc == .pos 1 &&
    c.P_k == [.packetWrite 77 access.κ access.offset source] &&
    c.E_k.entries.length == 2 && c.E_k.constraints.isEmpty &&
    c.E_k.lookupEq (Reg.packet access.κ 5) == some (Term.C32 0x88) &&
    c.E_k.lookupEq (Reg.packet access.κ 6) == some (Term.C32 0x77) &&
    stack.dir == .ok && stack.loc == .pos 1 && stack.P_k.isEmpty &&
    stack.E_k.entries.length == 1 &&
    stack.E_k.lookupEq (stackUnitReg p.φStack 0) == some (Term.C32 0x55667788)

#guard packetStoreObservationCheck

/-- Successful STX candidates have observations exactly when resolution selects
Packet, not cells. Both base aliases and store offsets contribute to resolution. -/
private def storeObservationCategoryCheck : Bool := Id.run do
  let p := checkContext.entry
  let .ok root := buildE0 p | return false
  let .ok (loaded, []) := exprEffects p 0 root.exprs (.ldx 4 2 1 0) | return false
  let E := (root.exprs.override loaded.delta).insertEq (Reg.real64 0) (Term.V64 9)
  let cases : List (Nat × Nat × Int) := [(2, 2, 3), (4, 10, -4), (4, 1, 0)]
  for (bytes, base, offset) in cases do
    let .ok access := resolveAccess p E base offset bytes true | return false
    let .candidates [c] := ebpfStep #[.stx bytes base 0 offset, .exit]
      checkContext 88 0 ⟨E, []⟩ | return false
    let isPacket := match access with | .packet _ => true | .cells _ => false
    if (!c.P_k.isEmpty) != isPacket then return false
    match access with
    | .packet a =>
      if c.P_k != [.packetWrite 88 a.κ a.offset (Term.V64 9)] then return false
    | .cells _ => if !c.P_k.isEmpty then return false
  return true

#guard storeObservationCategoryCheck
-- A map cell equality does not establish a map-address identity for STX.
#guard match ebpfStep #[.stx 4 2 0 0, .exit] checkContext 99 0
    ⟨ExprSet.empty.insertEq (Reg.real64 2) (Term.V64 99)
      |>.insertEq (Reg.real64 0) (Term.C64 1)
      |>.insertEq (Reg.map32 0) (Term.C32 0), []⟩ with
  | .reject .undefinedSrc => true
  | _ => false

end EBPF
