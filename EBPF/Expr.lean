import EBPF.Insn

namespace EBPF
open CommonMath

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

/-- Local Expr effects read only the input E; EXIT itself has no Expr effect. -/
def expr (E : ExprSet) (i : Insn) : Option ExprSet := do
  match i with
  | .illegal _ => none
  | .exit => some ExprSet.empty
  | .mov w dst src =>
    if dst ≥ 10 then none else do
      let t ← sourceTerm E src
      some (ExprSet.empty.insertEq (Reg.real64 dst) (writeValue w t))
  | .add w dst src =>
    if dst ≥ 10 then none else do
      let a ← readReg E dst
      let b ← sourceTerm E src
      some (ExprSet.empty.insertEq (Reg.real64 dst) (writeValue w (addStar w a b)))

def step := expr

end EBPF
