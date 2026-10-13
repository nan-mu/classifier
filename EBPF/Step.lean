import EBPF.Encode
import EBPF.Expr
import EBPF.Initial
import PathMerge.Path

namespace EBPF
open ClassifierExpr PathMerge

/-- EXIT means outer program return in this slice; require r0's complete equality.
Falling off the sequence and invalid encodings never become Exit. -/
def ebpfStep (I : Array Insn) (j : Nat) (σ : SemState) : StepResult :=
  match I[j]? with
  | none => .reject .unboundTarget
  | some (.illegal _) => .reject .localReject
  | some .exit =>
    match σ.exprs.lookupEq (Reg.real64 0) with
    | some t => if t.width == .w64 then
        .candidates [⟨.ok, .exit, ExprSet.empty, []⟩]
      else .reject .undefinedSrc
    | none => .reject .undefinedSrc
  | some i =>
    match expr σ.exprs i with
    | none => .reject .undefinedSrc
    | some Ei => if j + 1 < I.size then
        .candidates [⟨.ok, .pos (j + 1), Ei, []⟩]
      else .reject .unboundTarget

private def aluExitSequenceCheck : Bool := Id.run do
  let I := decodeProgram #[0x00000007000000b7, 0x0000000100000007, 0x95]
  let p : EntryParams := ⟨Term.V64 1, Term.V64 0⟩
  let .ok root := buildE0 p | return false
  let .candidates [mov] := ebpfStep I 0 root | return false
  let .ok afterMov := PathMerge.applyLocal root mov.E_k mov.P_k | return false
  let .candidates [add] := ebpfStep I 1 afterMov | return false
  let .ok afterAdd := PathMerge.applyLocal afterMov add.E_k add.P_k | return false
  let .candidates [exit] := ebpfStep I 2 afterAdd | return false
  let .ok final := PathMerge.applyLocal afterAdd exit.E_k exit.P_k | return false
  return mov.dir == .ok && mov.loc == .pos 1 &&
    add.dir == .ok && add.loc == .pos 2 &&
    exit.dir == .ok && exit.loc == .exit &&
    root.exprs.lookupEq (Reg.real64 0) == none &&
    afterMov.exprs.lookupEq (Reg.real64 0) == some (Term.C64 7) &&
    final.exprs.lookupEq (Reg.real64 0) == some (Term.C64 8) &&
    final.exprs.lookupEq (Reg.real64 1) == some p.tCtx &&
    [root, afterMov, afterAdd, final].all (fun state => state.predicates.isEmpty)

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
#guard match buildE0 ⟨Term.V32 1, Term.V64 0⟩ with
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

end EBPF
