/-!
# LeanRV32IMC — single-file RV32IMC slice

Types + instruction + decode are complete.
Execute keeps Sail signatures; unfinished Sail runtime uses `def_wanted`.
-/

namespace LeanRV32IMC

/-- Unfinished Sail runtime / semantics placeholder. -/
axiom def_wanted.{u} (α : Sort u) : α

/-! ## Types -/

/-
  Base types for the RV32IMC Lean slice.

  Register indices, ALU/branch op tags, and bitvector abbreviations used by
  Instruction and Decode.
-/


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


/-! ## Instruction -/

/-
  Sail-style `instruction` inductive for RV32IMC (I + M + Zca).

  Compressed constructors use the `C_` prefix. Illegal encodings are
  `ILLEGAL` (32-bit) and `C_ILLEGAL` (16-bit).
-/


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


/-! ## Decode -/

/-
  RV32IMC decode corresponding to Sail's encdec mappings.

  Sail names:
    encdec            : instruction <-> bits(32)
    encdec_compressed : instruction <-> bits(16)

  Lean backends call the bit→instruction direction
  `encdec_backwards` / `encdec_compressed_backwards`.

  Executable twin: ../decode_imc.py
-/


/-- Low 2 bits ≠ 0b11 ⇒ compressed. -/
def isRVC (h : BitVec 16) : Bool :=
  h &&& 3#16 != 3#16

private def slice16 (h : BitVec 16) (hi lo : Nat) : Nat :=
  (h >>> lo).toNat &&& ((1 <<< (hi - lo + 1)) - 1)

private def slice32 (w : BitVec 32) (hi lo : Nat) : Nat :=
  (w >>> lo).toNat &&& ((1 <<< (hi - lo + 1)) - 1)

private def mkReg (n : Nat) : regidx :=
  .Regidx (BitVec.ofNat 5 n)

private def mkCReg (n : Nat) : cregidx :=
  .Cregidx (BitVec.ofNat 3 n)

/-- Sail `encdec_compressed_backwards` (RV32 Zca). -/
def encdec_compressed_backwards (h : BitVec 16) : instruction :=
  let op := slice16 h 1 0
  let funct3 := slice16 h 15 13
  match op, funct3 with
  | 0, 0 =>
    let nzuimm :=
      (slice16 h 10 7 <<< 6) ||| (slice16 h 12 11 <<< 4) |||
        (slice16 h 5 5 <<< 3) ||| (slice16 h 6 6 <<< 2)
    let rd := mkCReg (slice16 h 4 2)
    if nzuimm == 0 then .C_ILLEGAL h
    else .C_ADDI4SPN (rd, BitVec.ofNat 8 nzuimm)
  | 0, 2 =>
    let uimm :=
      (slice16 h 5 5 <<< 6) ||| (slice16 h 12 10 <<< 3) |||
        (slice16 h 6 6 <<< 2)
    .C_LW (BitVec.ofNat 5 uimm, mkCReg (slice16 h 9 7), mkCReg (slice16 h 4 2))
  | 0, 6 =>
    let uimm :=
      (slice16 h 5 5 <<< 6) ||| (slice16 h 12 10 <<< 3) |||
        (slice16 h 6 6 <<< 2)
    .C_SW (BitVec.ofNat 5 uimm, mkCReg (slice16 h 9 7), mkCReg (slice16 h 4 2))
  | 1, 0 =>
    let rdn := slice16 h 11 7
    let immn := (slice16 h 12 12 <<< 5) ||| slice16 h 6 2
    if rdn == 0 && immn == 0 then .C_NOP 0#6
    else .C_ADDI (BitVec.ofNat 6 immn, mkReg rdn)
  | 1, 1 =>
    .C_JAL (BitVec.ofNat 11 (slice16 h 12 2))
  | 1, 2 =>
    .C_LI (BitVec.ofNat 6 ((slice16 h 12 12 <<< 5) ||| slice16 h 6 2), mkReg (slice16 h 11 7))
  | 1, 3 =>
    let rdn := slice16 h 11 7
    let immn := (slice16 h 12 12 <<< 5) ||| slice16 h 6 2
    if rdn == 2 then .C_ADDI16SP (BitVec.ofNat 6 immn)
    else .C_LUI (BitVec.ofNat 6 immn, mkReg rdn)
  | 1, 4 =>
    let rd := mkCReg (slice16 h 9 7)
    let funct2 := slice16 h 11 10
    let shamt := (slice16 h 12 12 <<< 5) ||| slice16 h 6 2
    match funct2 with
    | 0 => .C_SRLI (BitVec.ofNat 6 shamt, rd)
    | 1 => .C_SRAI (BitVec.ofNat 6 shamt, rd)
    | 2 => .C_ANDI (BitVec.ofNat 6 shamt, rd)
    | _ =>
      let rs2 := mkCReg (slice16 h 4 2)
      match slice16 h 6 5 with
      | 0 => .C_SUB (rd, rs2)
      | 1 => .C_XOR (rd, rs2)
      | 2 => .C_OR (rd, rs2)
      | _ => .C_AND (rd, rs2)
  | 1, 5 => .C_J (BitVec.ofNat 11 (slice16 h 12 2))
  | 1, 6 => .C_BEQZ (BitVec.ofNat 8 (slice16 h 12 2), mkCReg (slice16 h 9 7))
  | 1, 7 => .C_BNEZ (BitVec.ofNat 8 (slice16 h 12 2), mkCReg (slice16 h 9 7))
  | 2, 0 =>
    .C_SLLI (
      BitVec.ofNat 6 ((slice16 h 12 12 <<< 5) ||| slice16 h 6 2),
      mkReg (slice16 h 11 7))
  | 2, 2 =>
    let uimm :=
      (slice16 h 3 2 <<< 6) ||| (slice16 h 12 12 <<< 5) ||| (slice16 h 6 4 <<< 2)
    .C_LWSP (BitVec.ofNat 6 uimm, mkReg (slice16 h 11 7))
  | 2, 6 =>
    let uimm := (slice16 h 8 7 <<< 6) ||| (slice16 h 12 9 <<< 2)
    .C_SWSP (BitVec.ofNat 6 uimm, mkReg (slice16 h 6 2))
  | 2, 4 =>
    let rdn := slice16 h 11 7
    let rs2n := slice16 h 6 2
    let rd := mkReg rdn
    let rs2 := mkReg rs2n
    if slice16 h 12 12 == 0 then
      if rs2n == 0 then .C_JR rd else .C_MV (rd, rs2)
    else if rdn == 0 && rs2n == 0 then .C_EBREAK ()
    else if rs2n == 0 then .C_JALR rd
    else .C_ADD (rd, rs2)
  | _, _ => .C_ILLEGAL h

/-- Sail `encdec_backwards` (RV32 I+M). -/
def encdec_backwards (w : BitVec 32) : instruction :=
  let opcode := slice32 w 6 0
  let rd := mkReg (slice32 w 11 7)
  let funct3 := slice32 w 14 12
  let rs1 := mkReg (slice32 w 19 15)
  let rs2 := mkReg (slice32 w 24 20)
  let funct7 := slice32 w 31 25
  let immI := BitVec.ofNat 12 (slice32 w 31 20)
  match opcode with
  | 0b0110111 => .UTYPE (BitVec.ofNat 20 (slice32 w 31 12), rd, .LUI)
  | 0b0010111 => .UTYPE (BitVec.ofNat 20 (slice32 w 31 12), rd, .AUIPC)
  | 0b1101111 =>
    let imm :=
      (slice32 w 31 31 <<< 20) ||| (slice32 w 19 12 <<< 12) |||
        (slice32 w 20 20 <<< 11) ||| (slice32 w 30 21 <<< 1)
    .JAL (BitVec.ofNat 21 imm, rd)
  | 0b1100111 => if funct3 == 0 then .JALR (immI, rs1, rd) else .ILLEGAL w
  | 0b1100011 =>
    let imm :=
      (slice32 w 31 31 <<< 12) ||| (slice32 w 7 7 <<< 11) |||
        (slice32 w 30 25 <<< 5) ||| (slice32 w 11 8 <<< 1)
    let op? : Option bop :=
      match funct3 with
      | 0 => some .BEQ
      | 1 => some .BNE
      | 4 => some .BLT
      | 5 => some .BGE
      | 6 => some .BLTU
      | 7 => some .BGEU
      | _ => none
    match op? with
    | some op => .BTYPE (BitVec.ofNat 13 imm, rs2, rs1, op)
    | none => .ILLEGAL w
  | 0b0010011 =>
    match funct3 with
    | 0 => .ITYPE (immI, rs1, rd, .ADDI)
    | 2 => .ITYPE (immI, rs1, rd, .SLTI)
    | 3 => .ITYPE (immI, rs1, rd, .SLTIU)
    | 4 => .ITYPE (immI, rs1, rd, .XORI)
    | 6 => .ITYPE (immI, rs1, rd, .ORI)
    | 7 => .ITYPE (immI, rs1, rd, .ANDI)
    | 1 =>
      if funct7 == 0 then .SHIFTIOP (BitVec.ofNat 6 (slice32 w 24 20), rs1, rd, .SLLI)
      else .ILLEGAL w
    | 5 =>
      let shamt := BitVec.ofNat 6 (slice32 w 24 20)
      if funct7 == 0 then .SHIFTIOP (shamt, rs1, rd, .SRLI)
      else if funct7 == 0b0100000 then .SHIFTIOP (shamt, rs1, rd, .SRAI)
      else .ILLEGAL w
    | _ => .ILLEGAL w
  | 0b0110011 =>
    if funct7 == 1 then
      match funct3 with
      | 0 | 1 | 2 | 3 =>
        .MUL (rs2, rs1, rd,
          { result_part := .Low, signed_rs1 := .Signed, signed_rs2 := .Signed })
      | 4 => .DIV (rs2, rs1, rd, false)
      | 5 => .DIV (rs2, rs1, rd, true)
      | 6 => .REM (rs2, rs1, rd, false)
      | 7 => .REM (rs2, rs1, rd, true)
      | _ => .ILLEGAL w
    else
      let op? : Option rop :=
        match funct7, funct3 with
        | 0, 0 => some .ADD
        | 0b0100000, 0 => some .SUB
        | 0, 1 => some .SLL
        | 0, 2 => some .SLT
        | 0, 3 => some .SLTU
        | 0, 4 => some .XOR
        | 0, 5 => some .SRL
        | 0b0100000, 5 => some .SRA
        | 0, 6 => some .OR
        | 0, 7 => some .AND
        | _, _ => none
      match op? with
      | some op => .RTYPE (rs2, rs1, rd, op)
      | none => .ILLEGAL w
  | 0b0000011 =>
    match funct3 with
    | 0 => .LOAD (immI, rs1, rd, false, 1)
    | 1 => .LOAD (immI, rs1, rd, false, 2)
    | 2 => .LOAD (immI, rs1, rd, false, 4)
    | 4 => .LOAD (immI, rs1, rd, true, 1)
    | 5 => .LOAD (immI, rs1, rd, true, 2)
    | _ => .ILLEGAL w
  | 0b0100011 =>
    let imm := BitVec.ofNat 12 ((slice32 w 31 25 <<< 5) ||| slice32 w 11 7)
    match funct3 with
    | 0 => .STORE (imm, rs2, rs1, 1)
    | 1 => .STORE (imm, rs2, rs1, 2)
    | 2 => .STORE (imm, rs2, rs1, 4)
    | _ => .ILLEGAL w
  | 0b0001111 => .FENCE (0#4, 0#4, 0#4, rd, rs1)
  | 0b1110011 =>
    if w == 0x00000073#32 then .ECALL ()
    else if w == 0x00100073#32 then .EBREAK ()
    else if w == 0x30200073#32 then .MRET ()
    else if w == 0x10200073#32 then .SRET ()
    else if w == 0x10500073#32 then .WFI ()
    else .ILLEGAL w
  | _ => .ILLEGAL w


/-! ## Execute (Sail-shaped; bodies unfinished → `def_wanted`) -/

noncomputable section Execute

abbrev SailM := Id
abbrev xlenbits := BitVec 32
abbrev xlen : Nat := 32
abbrev xlen_bytes : Nat := 4
abbrev log2_xlen : Nat := 5

inductive ExecutionResult where
  | Retire_Success : Unit → ExecutionResult
  | Illegal_Instruction : Unit → ExecutionResult
  | Virtual_Instruction : Unit → ExecutionResult
  | Ext_XRET_Priv_Failure : Unit → ExecutionResult
  | Enter_Wait : Unit → ExecutionResult
  deriving Inhabited, Repr

def RETIRE_SUCCESS : ExecutionResult := .Retire_Success ()
def Illegal_Instruction (_ : Unit := ()) : ExecutionResult := .Illegal_Instruction ()
def Virtual_Instruction (_ : Unit := ()) : ExecutionResult := .Virtual_Instruction ()

def sign_extend {n : Nat} (m : Nat) (_x : BitVec n) : BitVec m := def_wanted _
def zero_extend {n : Nat} (m : Nat) (_x : BitVec n) : BitVec m := def_wanted _
def bool_to_bit (_ : Bool) : BitVec 1 := def_wanted _
def creg2reg_idx (c : cregidx) : regidx :=
  match c with | .Cregidx b => .Regidx (BitVec.ofNat 5 (8 + b.toNat))
def zreg : regidx := .Regidx 0#5
def ra : regidx := .Regidx 1#5
def sp : regidx := .Regidx 2#5
def zeros (n : Nat) : BitVec n := BitVec.zero n

/-- Expand compressed op into a 32-bit `instruction` then run (unfinished). -/
def ExecuteAs (_i : instruction) : ExecutionResult := def_wanted _

-- 32-bit execute: signatures kept, semantics unfinished
def execute_ILLEGAL (_s : BitVec 32) : ExecutionResult := Illegal_Instruction ()
def execute_C_ILLEGAL (_s : BitVec 16) : ExecutionResult := Illegal_Instruction ()
def execute_UTYPE (_imm : BitVec 20) (_rd : regidx) (_op : uop) : SailM ExecutionResult := pure (def_wanted _)
def execute_JAL (_imm : BitVec 21) (_rd : regidx) : SailM ExecutionResult := pure (def_wanted _)
def execute_JALR (_imm : BitVec 12) (_rs1 : regidx) (_rd : regidx) : SailM ExecutionResult := pure (def_wanted _)
def execute_BTYPE (_imm : BitVec 13) (_rs2 : regidx) (_rs1 : regidx) (_op : bop) : SailM ExecutionResult := pure (def_wanted _)
def execute_ITYPE (_imm : BitVec 12) (_rs1 : regidx) (_rd : regidx) (_op : iop) : SailM ExecutionResult := pure (def_wanted _)
def execute_SHIFTIOP (_shamt : BitVec 6) (_rs1 : regidx) (_rd : regidx) (_op : sop) : SailM ExecutionResult := pure (def_wanted _)
def execute_RTYPE (_rs2 : regidx) (_rs1 : regidx) (_rd : regidx) (_op : rop) : SailM ExecutionResult := pure (def_wanted _)
def execute_LOAD (_imm : BitVec 12) (_rs1 : regidx) (_rd : regidx) (_is_unsigned : Bool) (_width : Nat) : SailM ExecutionResult := pure (def_wanted _)
def execute_STORE (_imm : BitVec 12) (_rs2 : regidx) (_rs1 : regidx) (_width : Nat) : SailM ExecutionResult := pure (def_wanted _)
def execute_FENCE_TSO (_ : Unit) : SailM ExecutionResult := pure (def_wanted _)
def execute_FENCE (_fm : BitVec 4) (_pred : BitVec 4) (_succ : BitVec 4) (_rs : regidx) (_rd : regidx) : SailM ExecutionResult := pure (def_wanted _)
def execute_ECALL (_ : Unit) : SailM ExecutionResult := pure (def_wanted _)
def execute_MRET (_ : Unit) : SailM ExecutionResult := pure (def_wanted _)
def execute_SRET (_ : Unit) : SailM ExecutionResult := pure (def_wanted _)
def execute_EBREAK (_ : Unit) : SailM ExecutionResult := pure (def_wanted _)
def execute_WFI (_ : Unit) : SailM ExecutionResult := pure (def_wanted _)
def execute_SFENCE_VMA (_rs1 : regidx) (_rs2 : regidx) : SailM ExecutionResult := pure (def_wanted _)
def execute_MUL (_rs2 : regidx) (_rs1 : regidx) (_rd : regidx) (_mul_op : mul_op) : SailM ExecutionResult := pure (def_wanted _)
def execute_DIV (_rs2 : regidx) (_rs1 : regidx) (_rd : regidx) (_is_unsigned : Bool) : SailM ExecutionResult := pure (def_wanted _)
def execute_REM (_rs2 : regidx) (_rs1 : regidx) (_rd : regidx) (_is_unsigned : Bool) : SailM ExecutionResult := pure (def_wanted _)

-- Compressed: structural expand to 32-bit forms (same shape as Sail)
infixr:65 " +++ " => BitVec.append

def execute_C_NOP (_ : BitVec 6) : ExecutionResult := RETIRE_SUCCESS
def execute_C_ADDI4SPN (rdc : cregidx) (nzimm : BitVec 8) : ExecutionResult :=
  let imm : BitVec 12 := (0b00#2 +++ (nzimm +++ 0b00#2))
  ExecuteAs (.ITYPE (imm, sp, creg2reg_idx rdc, .ADDI))
def execute_C_LW (uimm : BitVec 5) (rsc : cregidx) (rdc : cregidx) : ExecutionResult :=
  let imm : BitVec 12 := zero_extend (m := 12) (uimm +++ 0b00#2)
  ExecuteAs (.LOAD (imm, creg2reg_idx rsc, creg2reg_idx rdc, false, 4))
def execute_C_SW (uimm : BitVec 5) (rsc1 : cregidx) (rsc2 : cregidx) : ExecutionResult :=
  let imm : BitVec 12 := zero_extend (m := 12) (uimm +++ 0b00#2)
  ExecuteAs (.STORE (imm, creg2reg_idx rsc2, creg2reg_idx rsc1, 4))
def execute_C_ADDI (imm : BitVec 6) (rsd : regidx) : ExecutionResult :=
  ExecuteAs (.ITYPE (sign_extend (m := 12) imm, rsd, rsd, .ADDI))
def execute_C_JAL (imm : BitVec 11) : ExecutionResult :=
  ExecuteAs (.JAL (sign_extend (m := 21) (imm +++ 0#1), ra))
def execute_C_LI (imm : BitVec 6) (rd : regidx) : ExecutionResult :=
  ExecuteAs (.ITYPE (sign_extend (m := 12) imm, zreg, rd, .ADDI))
def execute_C_ADDI16SP (imm : BitVec 6) : ExecutionResult :=
  ExecuteAs (.ITYPE (sign_extend (m := 12) (imm +++ 0x0#4), sp, sp, .ADDI))
def execute_C_LUI (imm : BitVec 6) (rd : regidx) : ExecutionResult :=
  ExecuteAs (.UTYPE (sign_extend (m := 20) imm, rd, .LUI))
def execute_C_SRLI (shamt : BitVec 6) (rsd : cregidx) : ExecutionResult :=
  let r := creg2reg_idx rsd
  ExecuteAs (.SHIFTIOP (shamt, r, r, .SRLI))
def execute_C_SRAI (shamt : BitVec 6) (rsd : cregidx) : ExecutionResult :=
  let r := creg2reg_idx rsd
  ExecuteAs (.SHIFTIOP (shamt, r, r, .SRAI))
def execute_C_ANDI (imm : BitVec 6) (rsd : cregidx) : ExecutionResult :=
  let r := creg2reg_idx rsd
  ExecuteAs (.ITYPE (sign_extend (m := 12) imm, r, r, .ANDI))
def execute_C_SUB (rsd : cregidx) (rs2 : cregidx) : ExecutionResult :=
  let a := creg2reg_idx rsd; let b := creg2reg_idx rs2
  ExecuteAs (.RTYPE (b, a, a, .SUB))
def execute_C_XOR (rsd : cregidx) (rs2 : cregidx) : ExecutionResult :=
  let a := creg2reg_idx rsd; let b := creg2reg_idx rs2
  ExecuteAs (.RTYPE (b, a, a, .XOR))
def execute_C_OR (rsd : cregidx) (rs2 : cregidx) : ExecutionResult :=
  let a := creg2reg_idx rsd; let b := creg2reg_idx rs2
  ExecuteAs (.RTYPE (b, a, a, .OR))
def execute_C_AND (rsd : cregidx) (rs2 : cregidx) : ExecutionResult :=
  let a := creg2reg_idx rsd; let b := creg2reg_idx rs2
  ExecuteAs (.RTYPE (b, a, a, .AND))
def execute_C_J (imm : BitVec 11) : ExecutionResult :=
  ExecuteAs (.JAL (sign_extend (m := 21) (imm +++ 0#1), zreg))
def execute_C_BEQZ (imm : BitVec 8) (rs : cregidx) : ExecutionResult :=
  ExecuteAs (.BTYPE (sign_extend (m := 13) (imm +++ 0#1), zreg, creg2reg_idx rs, .BEQ))
def execute_C_BNEZ (imm : BitVec 8) (rs : cregidx) : ExecutionResult :=
  ExecuteAs (.BTYPE (sign_extend (m := 13) (imm +++ 0#1), zreg, creg2reg_idx rs, .BNE))
def execute_C_SLLI (shamt : BitVec 6) (rsd : regidx) : ExecutionResult :=
  ExecuteAs (.SHIFTIOP (shamt, rsd, rsd, .SLLI))
def execute_C_LWSP (uimm : BitVec 6) (rd : regidx) : ExecutionResult :=
  let imm : BitVec 12 := zero_extend (m := 12) (uimm +++ 0b00#2)
  ExecuteAs (.LOAD (imm, sp, rd, false, 4))
def execute_C_SWSP (uimm : BitVec 6) (rs2 : regidx) : ExecutionResult :=
  let imm : BitVec 12 := zero_extend (m := 12) (uimm +++ 0b00#2)
  ExecuteAs (.STORE (imm, rs2, sp, 4))
def execute_C_JR (rs1 : regidx) : ExecutionResult :=
  ExecuteAs (.JALR (zeros 12, rs1, zreg))
def execute_C_JALR (rs1 : regidx) : ExecutionResult :=
  ExecuteAs (.JALR (zeros 12, rs1, ra))
def execute_C_MV (rd : regidx) (rs2 : regidx) : ExecutionResult :=
  ExecuteAs (.RTYPE (rs2, zreg, rd, .ADD))
def execute_C_EBREAK (_ : Unit) : ExecutionResult :=
  ExecuteAs (.EBREAK ())
def execute_C_ADD (rsd : regidx) (rs2 : regidx) : ExecutionResult :=
  ExecuteAs (.RTYPE (rs2, rsd, rsd, .ADD))

def execute (merge_var : instruction) : SailM ExecutionResult := do
  match merge_var with
  | .UTYPE (imm, rd, op) => execute_UTYPE imm rd op
  | .JAL (imm, rd) => execute_JAL imm rd
  | .BTYPE (imm, rs2, rs1, op) => execute_BTYPE imm rs2 rs1 op
  | .ITYPE (imm, rs1, rd, op) => execute_ITYPE imm rs1 rd op
  | .SHIFTIOP (shamt, rs1, rd, op) => execute_SHIFTIOP shamt rs1 rd op
  | .RTYPE (rs2, rs1, rd, op) => execute_RTYPE rs2 rs1 rd op
  | .LOAD (imm, rs1, rd, is_unsigned, width) => execute_LOAD imm rs1 rd is_unsigned width
  | .STORE (imm, rs2, rs1, width) => execute_STORE imm rs2 rs1 width
  | .FENCE_TSO arg0 => execute_FENCE_TSO arg0
  | .FENCE (fm, pred, succ, rs, rd) => execute_FENCE fm pred succ rs rd
  | .ECALL arg0 => execute_ECALL arg0
  | .MRET arg0 => execute_MRET arg0
  | .SRET arg0 => execute_SRET arg0
  | .EBREAK arg0 => execute_EBREAK arg0
  | .WFI arg0 => execute_WFI arg0
  | .SFENCE_VMA (rs1, rs2) => execute_SFENCE_VMA rs1 rs2
  | .JALR (imm, rs1, rd) => execute_JALR imm rs1 rd
  | .MUL (rs2, rs1, rd, mop) => execute_MUL rs2 rs1 rd mop
  | .DIV (rs2, rs1, rd, u) => execute_DIV rs2 rs1 rd u
  | .REM (rs2, rs1, rd, u) => execute_REM rs2 rs1 rd u
  | .C_NOP g => pure (execute_C_NOP g)
  | .C_ADDI4SPN (rdc, nzimm) => pure (execute_C_ADDI4SPN rdc nzimm)
  | .C_LW (uimm, rsc, rdc) => pure (execute_C_LW uimm rsc rdc)
  | .C_SW (uimm, rsc1, rsc2) => pure (execute_C_SW uimm rsc1 rsc2)
  | .C_ADDI (imm, rsd) => pure (execute_C_ADDI imm rsd)
  | .C_JAL imm => pure (execute_C_JAL imm)
  | .C_LI (imm, rd) => pure (execute_C_LI imm rd)
  | .C_ADDI16SP imm => pure (execute_C_ADDI16SP imm)
  | .C_LUI (imm, rd) => pure (execute_C_LUI imm rd)
  | .C_SRLI (shamt, rsd) => pure (execute_C_SRLI shamt rsd)
  | .C_SRAI (shamt, rsd) => pure (execute_C_SRAI shamt rsd)
  | .C_ANDI (imm, rsd) => pure (execute_C_ANDI imm rsd)
  | .C_SUB (rsd, rs2) => pure (execute_C_SUB rsd rs2)
  | .C_XOR (rsd, rs2) => pure (execute_C_XOR rsd rs2)
  | .C_OR (rsd, rs2) => pure (execute_C_OR rsd rs2)
  | .C_AND (rsd, rs2) => pure (execute_C_AND rsd rs2)
  | .C_J imm => pure (execute_C_J imm)
  | .C_BEQZ (imm, rs) => pure (execute_C_BEQZ imm rs)
  | .C_BNEZ (imm, rs) => pure (execute_C_BNEZ imm rs)
  | .C_SLLI (shamt, rsd) => pure (execute_C_SLLI shamt rsd)
  | .C_LWSP (uimm, rd) => pure (execute_C_LWSP uimm rd)
  | .C_SWSP (uimm, rs2) => pure (execute_C_SWSP uimm rs2)
  | .C_JR rs1 => pure (execute_C_JR rs1)
  | .C_JALR rs1 => pure (execute_C_JALR rs1)
  | .C_MV (rd, rs2) => pure (execute_C_MV rd rs2)
  | .C_EBREAK arg0 => pure (execute_C_EBREAK arg0)
  | .C_ADD (rsd, rs2) => pure (execute_C_ADD rsd rs2)
  | .ILLEGAL s => pure (execute_ILLEGAL s)
  | .C_ILLEGAL s => pure (execute_C_ILLEGAL s)

end LeanRV32IMC.Execute
