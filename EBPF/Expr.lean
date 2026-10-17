import EBPF.Insn

namespace EBPF
open Core

private def readReg (E : ExprSet) (r : Nat) : Option Term := do
  if r > 10 then none else do
    let t ← E.lookupEq (Reg.real64 r)
    if t.width == .w64 then some t else none

private def sourceTerm (E : ExprSet) : Source → Option Term
  | .imm bits => some (Term.C64 (M 64 (s 32 bits.toNat)))
  | .reg r => readReg E r

/-- ALU32 operands have a 32-bit carrier before applying the shared operator. -/
def aluOperand (w : Width) (t : Term) : Term :=
  match w with
  | .w64 => t
  | .w32 => zStar 32 .w32 64 t

/-- ALU32 results clear the upper half of the canonical real register. -/
def aluResult (w : Width) (t : Term) : Term :=
  match w with
  | .w64 => t
  | .w32 => zStar 32 .w64 32 t

def BinaryOp.toOp (w : Width) : BinaryOp → Op
  | .add => .add w
  | .sub => .sub w
  | .mul => .mullo w
  | .div => .udiv w 0
  | .mod => .urem w
  | .sdiv => .sdiv w 0
  | .smod => .srem w
  | .and => .and w.bits
  | .or => .or w.bits
  | .xor => .xor w.bits
  | .lsh => .shl w
  | .rsh => .lshr w
  | .arsh => .ashr w

/-- Every ALU source is obtained from the same executing input E.
The model and decoder use little-endian eBPF byte order. -/
def expr (E : ExprSet) (i : Insn) : Option ExprSet := do
  if !E.keysUnique || !E.wellTyped then none else
  match i with
  | .mov w dst src =>
    if dst ≥ 10 then none else do
      let t ← sourceTerm E src
      let value := idStar w (aluOperand w t)
      some (ExprSet.empty.insertEq (Reg.real64 dst) (aluResult w value))
  | .binary w op dst src =>
    if dst ≥ 10 then none else do
      if let .imm bits := src then
        if [.lsh, .rsh, .arsh].contains op && bits.toNat ≥ w.bits then none
        else pure ()
      let a ← readReg E dst
      let b ← sourceTerm E src
      let value := star w (op.toOp w) [aluOperand w a, aluOperand w b]
      some (ExprSet.empty.insertEq (Reg.real64 dst) (aluResult w value))
  | .neg w dst =>
    if dst ≥ 10 then none else do
      let a ← readReg E dst
      some (ExprSet.empty.insertEq (Reg.real64 dst)
        (aluResult w (negStar w (aluOperand w a))))
  | .movsx w bits dst src =>
    if dst ≥ 10 || !([8, 16].contains bits || (w == .w64 && bits == 32)) then none
    else do
      let a ← readReg E src
      some (ExprSet.empty.insertEq (Reg.real64 dst)
        (aluResult w (sStar bits w 64 a)))
  | .endian op bits dst =>
    if dst ≥ 10 || ![16, 32, 64].contains bits then none else do
      let a ← readReg E dst
      let value := match op with
        | .little => star .w64 (.low bits 64) [a]
        | .big | .swap => star .w64 (.bswap bits 64) [a]
      some (ExprSet.empty.insertEq (Reg.real64 dst) value)
  | _ => none

private def alu32FamilyCheck : Bool :=
  let E := ExprSet.empty.insertEq (Reg.real64 1) (Term.C64 0x10000000f)
    |>.insertEq (Reg.real64 2) (Term.C64 2)
  let cases : List (BinaryOp × Nat) :=
    [(.add, 17), (.sub, 13), (.mul, 30), (.div, 7), (.mod, 1),
      (.sdiv, 7), (.smod, 1), (.and, 2), (.or, 15), (.xor, 13),
      (.lsh, 60), (.rsh, 3), (.arsh, 3)]
  cases.all fun (op, expected) =>
    match expr E (.binary .w32 op 1 (.reg 2)) with
    | some updates => updates.lookupEq (Reg.real64 1) == some (Term.C64 expected) &&
        updates.entries.length == 1
    | none => false

private def unaryAndDivisionCheck : Bool :=
  let E := ExprSet.empty.insertEq (Reg.real64 1) (Term.C64 0x100000001)
    |>.insertEq (Reg.real64 2) (Term.C64 0x80000080)
  let cases : List (Insn × Nat) :=
    [(.neg .w32 1, 0xffffffff),
      (.movsx .w32 8 1 2, 0xffffff80),
      (.movsx .w64 32 1 2, 0xffffffff80000080),
      (.endian .little 16 2, 0x80),
      (.endian .big 16 2, 0x8000),
      (.endian .swap 32 2, 0x80000080),
      (.binary .w64 .div 1 (.imm 0), 0),
      (.binary .w32 .mod 1 (.imm 0), 1),
      (.binary .w64 .mod 1 (.imm 0), 0x100000001)]
  cases.all fun (i, expected) =>
    let dst := match i with | .endian _ _ r => r | _ => 1
    match expr E i with
    | some updates => updates.lookupEq (Reg.real64 dst) == some (Term.C64 expected)
    | none => false

#guard alu32FamilyCheck
#guard unaryAndDivisionCheck
#guard match expr (ExprSet.empty.insertEq (Reg.real64 1) (Term.V64 9)
    |>.insertEq (Reg.real64 2) (Term.V64 10)) (.binary .w32 .sdiv 1 (.reg 2)) with
  | some updates => updates.lookupEq (Reg.real64 1) ==
      some (zStar 32 .w64 32 (star .w32 (.sdiv .w32 0)
        [zStar 32 .w32 64 (Term.V64 9), zStar 32 .w32 64 (Term.V64 10)]))
  | none => false
#guard (expr (ExprSet.empty.insertEq (Reg.real64 1) (Term.C64 1))
  (.binary .w32 .lsh 1 (.imm 32))).isNone

end EBPF
