/-!
# LeanRV32IMC.Types — register indices, op tags, instruction

Sail constructor names are kept for the decoded `instruction` object.
No SailM / ExecutionResult.
-/

namespace LeanRV32IMC

/-- Architectural X register index (RV32: 5 bits). -/
inductive regidx where
  | Regidx (_ : BitVec 5)
  deriving Inhabited, BEq, DecidableEq, Repr

/-- Compressed register index (maps to x8–x15). -/
inductive cregidx where
  | Cregidx (_ : BitVec 3)
  deriving Inhabited, BEq, DecidableEq, Repr

inductive Signedness where
  | Signed
  | Unsigned
  deriving BEq, DecidableEq, Inhabited, Repr

inductive VectorHalf where
  | High
  | Low
  deriving BEq, DecidableEq, Inhabited, Repr

inductive bop where
  | BEQ | BNE | BLT | BGE | BLTU | BGEU
  deriving BEq, DecidableEq, Inhabited, Repr

inductive iop where
  | ADDI | SLTI | SLTIU | XORI | ORI | ANDI
  deriving BEq, DecidableEq, Inhabited, Repr

inductive sop where
  | SLLI | SRLI | SRAI
  deriving BEq, DecidableEq, Inhabited, Repr

inductive rop where
  | ADD | SUB | SLL | SLT | SLTU | XOR | SRL | SRA | OR | AND
  deriving BEq, DecidableEq, Inhabited, Repr

inductive uop where
  | LUI | AUIPC
  deriving BEq, DecidableEq, Inhabited, Repr

/-- Sail `mul_op` payload for MUL / MULH / MULHSU / MULHU. -/
structure mul_op where
  result_part : VectorHalf
  signed_rs1 : Signedness
  signed_rs2 : Signedness
  deriving BEq, Inhabited, Repr

abbrev word := BitVec 32
abbrev half := BitVec 16
/-- Memory access width in bytes (1 / 2 / 4 for RV32). -/
abbrev word_width := Nat

def creg2reg_idx (c : cregidx) : regidx :=
  match c with | .Cregidx b => .Regidx (BitVec.ofNat 5 (8 + b.toNat))

def zreg : regidx := .Regidx 0#5
def ra : regidx := .Regidx 1#5
def sp : regidx := .Regidx 2#5

def regidx.toNat : regidx → Nat
  | .Regidx b => b.toNat

/-! ## Instruction -/

inductive instruction where
  | ILLEGAL (_ : word)
  | C_ILLEGAL (_ : half)
  | UTYPE (_ : BitVec 20 × regidx × uop)
  | JAL (_ : BitVec 21 × regidx)
  | JALR (_ : BitVec 12 × regidx × regidx)
  | BTYPE (_ : BitVec 13 × regidx × regidx × bop)
  | ITYPE (_ : BitVec 12 × regidx × regidx × iop)
  | SHIFTIOP (_ : BitVec 6 × regidx × regidx × sop)
  | RTYPE (_ : regidx × regidx × regidx × rop)
  | LOAD (_ : BitVec 12 × regidx × regidx × Bool × word_width)
  | STORE (_ : BitVec 12 × regidx × regidx × word_width)
  | FENCE_TSO (_ : Unit)
  | FENCE (_ : BitVec 4 × BitVec 4 × BitVec 4 × regidx × regidx)
  | ECALL (_ : Unit)
  | MRET (_ : Unit)
  | SRET (_ : Unit)
  | EBREAK (_ : Unit)
  | WFI (_ : Unit)
  | SFENCE_VMA (_ : regidx × regidx)
  | MUL (_ : regidx × regidx × regidx × mul_op)
  | DIV (_ : regidx × regidx × regidx × Bool)
  | REM (_ : regidx × regidx × regidx × Bool)
  | C_NOP (_ : BitVec 6)
  | C_ADDI4SPN (_ : cregidx × BitVec 8)
  | C_LW (_ : BitVec 5 × cregidx × cregidx)
  | C_SW (_ : BitVec 5 × cregidx × cregidx)
  | C_ADDI (_ : BitVec 6 × regidx)
  | C_JAL (_ : BitVec 11)
  | C_LI (_ : BitVec 6 × regidx)
  | C_ADDI16SP (_ : BitVec 6)
  | C_LUI (_ : BitVec 6 × regidx)
  | C_SRLI (_ : BitVec 6 × cregidx)
  | C_SRAI (_ : BitVec 6 × cregidx)
  | C_ANDI (_ : BitVec 6 × cregidx)
  | C_SUB (_ : cregidx × cregidx)
  | C_XOR (_ : cregidx × cregidx)
  | C_OR (_ : cregidx × cregidx)
  | C_AND (_ : cregidx × cregidx)
  | C_J (_ : BitVec 11)
  | C_BEQZ (_ : BitVec 8 × cregidx)
  | C_BNEZ (_ : BitVec 8 × cregidx)
  | C_SLLI (_ : BitVec 6 × regidx)
  | C_LWSP (_ : BitVec 6 × regidx)
  | C_SWSP (_ : BitVec 6 × regidx)
  | C_JR (_ : regidx)
  | C_JALR (_ : regidx)
  | C_MV (_ : regidx × regidx)
  | C_EBREAK (_ : Unit)
  | C_ADD (_ : regidx × regidx)
  deriving Inhabited, Repr

end LeanRV32IMC
