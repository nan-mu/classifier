import EBPF.Encode
import EBPF.Expr
import EBPF.Initial
import CommonMath.Expand

namespace EBPF
open CommonMath

/-- EXIT means outer program return in this slice; capture r0 as a return observation.
Falling off the sequence and invalid encodings never become Exit. -/
def ebpfStep (I : Array Insn) (j : Nat) (σ : SemState) : StepResult :=
  match I[j]? with
  | none => .reject .unboundTarget
  | some (.illegal _) => .reject .localReject
  | some .exit =>
    match σ.exprs.lookupEq (Reg.real64 0) with
    | some t => if t.width == .w64 then
        .candidates [⟨.only, .exit, ExprSet.empty, [.ret (solve t)]⟩]
      else .reject .undefinedSrc
    | none => .reject .undefinedSrc
  | some i =>
    match expr σ.exprs i with
    | none => .reject .undefinedSrc
    | some Ei => if j + 1 < I.size then
        .candidates [⟨.only, .pos (j + 1), Ei, []⟩]
      else .reject .unboundTarget

def ebpfInit (I : Array Insn) (p : EntryParams) (j0 budget : Nat) :
    Except RejectReason WorkState := do
  let σ ← buildE0 p
  expandInit I.size j0 σ budget

private def smokeParams : EntryParams := ⟨Term.V64 1, Term.V64 0⟩

/-- mov64 r0,7; add64 r0,1; exit: exactly three expansions exhaust the budget. -/
def smokeProgram : Array Insn := decodeProgram #[0x00000007000000b7,
  0x0000000100000007, 0x95]

private def smokeCompleteExit : Bool :=
  match ebpfInit smokeProgram smokeParams 0 3 with
  | .error _ => false
  | .ok ws => match expandN smokeProgram.size (ebpfStep smokeProgram) ws 4 with
    | .inl (.complete g) =>
      g.nodes.size == 4 && g.edges.size == 3 && g.root == 0 &&
      g.nodes.all (fun n => n.state.predicates ==
        (if n.loc.isExit then [.ret (Term.C64 8)] else [])) &&
      match g.nodes[0]?, g.nodes[3]? with
      | some root, some last => root.loc == .pos 0 && last.loc == .exit &&
          root.state.exprs.lookupEq (Reg.real64 0) == none &&
          last.state.exprs.lookupEq (Reg.real64 0) == some (Term.C64 8) &&
          last.state.exprs.lookupEq (Reg.real64 1) == some smokeParams.tCtx
      | _, _ => false
    | _ => false

#guard smokeCompleteExit
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
#guard match buildE0 ⟨Term.V32 1, Term.V64 0⟩ with
  | .error .invalidEntry => true
  | _ => false
#guard match ebpfInit smokeProgram smokeParams smokeProgram.size 3 with
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
#guard match ebpfStep #[.exit] 0 SemState.empty with
  | .reject .undefinedSrc => true
  | _ => false
#guard match ebpfStep (decodeProgram #[0]) 0 SemState.empty with
  | .reject .localReject => true
  | _ => false
#guard match ebpfStep #[.mov .w64 0 (.imm 1)] 0 SemState.empty with
  | .reject .unboundTarget => true
  | _ => false
#guard match ebpfInit smokeProgram smokeParams 0 2 with
  | .ok ws => match expandN smokeProgram.size (ebpfStep smokeProgram) ws 4 with
    | .inl (.fail .limitExceeded g) => !(g.nodes.any (fun n => n.loc.isExit))
    | _ => false
  | _ => false

end EBPF
