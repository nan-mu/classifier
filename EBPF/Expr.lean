import EBPF.Insn

namespace EBPF
open ClassifierExpr

private def readReg (E : ExprSet) (r : Nat) : Option Term := do
  if r > 10 then none else do
    let t ← E.lookupEq (Reg.real64 r)
    if t.width == .w64 then some t else none

private def sourceTerm (E : ExprSet) : Source → Option Term
  | .imm bits => some (Term.C64 (M 64 (s 32 bits.toNat)))
  | .reg r => readReg E r

/-- ALU32 computes low 32 bits and zero-extends into the canonical r-register. -/
private def writeValue (w : Width) (t : Term) : Term :=
  match w with
  | .w64 => idStar .w64 t
  | .w32 => zStar 32 .w64 64 t

/-- ALU-only value rule; every operand is read from the executing input E. -/
def expr (E : ExprSet) (i : Insn) : Option ExprSet := do
  match i with
  -- EBPF.Memory.exprEffects owns non-ALU value dispatch and rejects illegal encodings.
  | .illegal _ => none
  -- EBPF.Memory.exprEffects supplies the empty value effect; Step captures the return.
  | .exit => none
  -- EBPF.Memory.exprEffects owns resolved memory loads.
  | .ldx _ _ _ _ => none
  -- EBPF.Memory.exprEffects owns resolved memory stores.
  | .stx _ _ _ _ => none
  -- EBPF.Memory.exprEffects refuses this class; Step owns conditional control flow.
  | .jcond _ _ _ _ _ => none
  -- EBPF.Memory.exprEffects refuses this class; Step owns unconditional control flow.
  | .ja _ => none
  -- EBPF.Memory.exprEffects refuses this class; Step owns bound wide-immediate loads.
  | .lddw _ _ _ => none
  -- EBPF.Memory.exprEffects refuses standalone continuation slots.
  | .continuation => none
  -- EBPF.Memory.exprEffects refuses helpers without a native helper contract.
  | .callHelper _ => none
  | .mov w dst src =>
    if dst ≥ 10 then none else do
      let t ← sourceTerm E src
      some (ExprSet.empty.insertEq (Reg.real64 dst) (writeValue w t))
  | .add w dst src =>
    if dst ≥ 10 then none else do
      let a ← readReg E dst
      let b ← sourceTerm E src
      some (ExprSet.empty.insertEq (Reg.real64 dst) (writeValue w (addStar w a b)))

end EBPF
