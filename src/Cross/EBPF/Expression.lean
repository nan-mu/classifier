import Cross.EBPF.Insn
import Expression.Interval

namespace Cross.EBPF
open Term Term.Value Expression Observation Interface Interface.Step

/-- A machine register is read through its `[0,64)` interval, so a split low and high half concatenate. -/
def readReg (E : List Expr) (r : Nat) : Option Term := do
  if r > 10 then none
  readInterval E (Reg.real64 r)

/-- 64-bit ALU writes `Real(r,[0,64))`. 32-bit ALU writes the result into `[0,32)` and clears `[32,64)`. -/
def assignReal (w : Width) (dst : Nat) (value : Term) : Option (List Expr) :=
  match w with
  | .w64 => ((«seal» ((Reg.real64 dst)).bits value >>= fun stored => some [Expr.mkEq (Reg.real64 dst) stored]))
  | .w32 => do
    let low ← ((«seal» ((Reg.real32 dst)).bits value >>= fun stored => some [Expr.mkEq (Reg.real32 dst) stored]))
    let high ← («seal» (Reg.real dst 32 64).bits (Term.C32 0) >>= fun stored => some [Expr.mkEq (Reg.real dst 32 64) stored])
    pure (low ++ high)

private def sourceTerm (E : List Expr) : Source → Option Term
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
def expr (E : List Expr) (i : Insn) : Option (List Expr) := do
  if !E.keysUnique || !E.wellTyped then none else
  match i with
  | .mov w dst src =>
    if dst ≥ 10 then none else do
      let t ← sourceTerm E src
      let value := idStar w (aluOperand w t)
      assignReal w dst value
  | .binary w op dst src =>
    if dst ≥ 10 then none else do
      if let .imm bits := src then
        if [.lsh, .rsh, .arsh].contains op && bits.toNat ≥ w.bits then none
        else pure ()
      let a ← readReg E dst
      let b ← sourceTerm E src
      let value := star w (op.toOp w) [aluOperand w a, aluOperand w b]
      assignReal w dst value
  | .neg w dst =>
    if dst ≥ 10 then none else do
      let a ← readReg E dst
      assignReal w dst (negStar w (aluOperand w a))
  | .movsx w bits dst src =>
    if dst ≥ 10 || !([8, 16].contains bits || (w == .w64 && bits == 32)) then none
    else do
      let a ← readReg E src
      assignReal w dst (sStar bits w 64 a)
  | .endian op bits dst =>
    if dst ≥ 10 || ![16, 32, 64].contains bits then none else do
      let a ← readReg E dst
      let value := match op with
        | .little => star .w64 (.low bits 64) [a]
        | .big | .swap => star .w64 (.bswap bits 64) [a]
      assignReal .w64 dst (idStar .w64 value)
  | _ => none

private def alu32FamilyCheck : Bool :=
  let E := (update ⟨Expr.nil, []⟩ { exprs := [Expr.mkEq (Reg.real64 1) (solve (Term.C64 0x10000000f))], predicates := [] }).exprs
    |> (fun acc => (update ⟨acc, []⟩ { exprs := [Expr.mkEq (Reg.real64 2) (solve (Term.C64 2))], predicates := [] }).exprs)
  let cases : List (BinaryOp × Nat) :=
    [(.add, 17), (.sub, 13), (.mul, 30), (.div, 7), (.mod, 1),
      (.sdiv, 7), (.smod, 1), (.and, 2), (.or, 15), (.xor, 13),
      (.lsh, 60), (.rsh, 3), (.arsh, 3)]
  cases.all fun (op, expected) =>
    match expr E (.binary .w32 op 1 (.reg 2)) with
    | some updates => updates.lookupEq (Reg.real32 1) == some (Term.C32 expected) &&
        updates.lookupEq (.real 1 32 64) == some (Term.C32 0) &&
        updates.length == 2
    | none => false

private def unaryAndDivisionCheck : Bool :=
  let E := (update ⟨Expr.nil, []⟩ { exprs := [Expr.mkEq (Reg.real64 1) (solve (Term.C64 0x100000001))], predicates := [] }).exprs
    |> (fun acc => (update ⟨acc, []⟩ { exprs := [Expr.mkEq (Reg.real64 2) (solve (Term.C64 0x80000080))], predicates := [] }).exprs)
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
    | some updates =>
      match i with
      | .binary .w64 _ _ _ | .movsx .w64 _ _ _ | .endian _ _ _ =>
        updates.lookupEq (Reg.real64 dst) == some (Term.C64 expected) &&
          updates.length == 1
      | _ =>
        updates.lookupEq (Reg.real32 dst) == some (Term.C32 expected) &&
          updates.lookupEq (.real dst 32 64) == some (Term.C32 0) &&
          updates.length == 2
    | none => false

#guard alu32FamilyCheck
#guard unaryAndDivisionCheck
#guard match expr ((update ⟨Expr.nil, []⟩ { exprs := [Expr.mkEq (Reg.real64 1) (solve (Term.V64 9))], predicates := [] }).exprs
    |> (fun acc => (update ⟨acc, []⟩ { exprs := [Expr.mkEq (Reg.real64 2) (solve (Term.V64 10))], predicates := [] }).exprs)) (.binary .w32 .sdiv 1 (.reg 2)) with
  | some updates => updates.lookupEq (Reg.real32 1) ==
      some (star .w32 (.sdiv .w32 0)
        [zStar 32 .w32 64 (Term.V64 9), zStar 32 .w32 64 (Term.V64 10)]) &&
      updates.lookupEq (.real 1 32 64) == some (Term.C32 0)
  | none => false
#guard (expr ((update ⟨Expr.nil, []⟩ { exprs := [Expr.mkEq (Reg.real64 1) (solve (Term.C64 1))], predicates := [] }).exprs)
  (.binary .w32 .lsh 1 (.imm 32))).isNone

end Cross.EBPF
