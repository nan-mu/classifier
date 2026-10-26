import Cross.RV32.Insn

namespace Cross.RV32

private def slice16 (h : BitVec 16) (hi lo : Nat) : Nat :=
  (h >>> lo).toNat &&& ((1 <<< (hi - lo + 1)) - 1)

private def slice32 (w : BitVec 32) (hi lo : Nat) : Nat :=
  (w >>> lo).toNat &&& ((1 <<< (hi - lo + 1)) - 1)

private def mkReg (n : Nat) : regidx :=
  .Regidx (BitVec.ofNat 5 n)

private def mkCReg (n : Nat) : cregidx :=
  .Cregidx (BitVec.ofNat 3 n)

/-- Recovered signed displacement divided by two (implicit low zero bit). -/
private def cjOffset (h : BitVec 16) : BitVec 11 :=
  BitVec.ofNat 11 (((slice16 h 12 12) <<< 10) |||
    (slice16 h 11 11 <<< 3) ||| (slice16 h 10 9 <<< 7) |||
    (slice16 h 8 8 <<< 9) ||| (slice16 h 7 7 <<< 5) |||
    (slice16 h 6 6 <<< 6) ||| (slice16 h 5 3) ||| (slice16 h 2 2 <<< 4))

private def cbOffset (h : BitVec 16) : BitVec 8 :=
  BitVec.ofNat 8 ((slice16 h 12 12 <<< 7) ||| (slice16 h 11 10 <<< 2) |||
    (slice16 h 6 5 <<< 5) ||| (slice16 h 4 3) ||| (slice16 h 2 2 <<< 4))

/-- Sail `encodeCompressed` (RV32 Zca). -/
def encodeCompressed (h : BitVec 16) : Insn :=
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
    -- The five-bit field stores the word offset; Expr scales it back to bytes.
    .C_LW (BitVec.ofNat 5 (uimm >>> 2), mkCReg (slice16 h 9 7), mkCReg (slice16 h 4 2))
  | 0, 6 =>
    let uimm :=
      (slice16 h 5 5 <<< 6) ||| (slice16 h 12 10 <<< 3) |||
        (slice16 h 6 6 <<< 2)
    .C_SW (BitVec.ofNat 5 (uimm >>> 2), mkCReg (slice16 h 9 7), mkCReg (slice16 h 4 2))
  | 1, 0 =>
    let rdn := slice16 h 11 7
    let immn := (slice16 h 12 12 <<< 5) ||| slice16 h 6 2
    if rdn == 0 && immn == 0 then .C_NOP 0#6
    else .C_ADDI (BitVec.ofNat 6 immn, mkReg rdn)
  | 1, 1 =>
    .C_JAL (cjOffset h)
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
  | 1, 5 => .C_J (cjOffset h)
  | 1, 6 => .C_BEQZ (cbOffset h, mkCReg (slice16 h 9 7))
  | 1, 7 => .C_BNEZ (cbOffset h, mkCReg (slice16 h 9 7))
  | 2, 0 =>
    .C_SLLI (
      BitVec.ofNat 6 ((slice16 h 12 12 <<< 5) ||| slice16 h 6 2),
      mkReg (slice16 h 11 7))
  | 2, 2 =>
    -- Store the word offset so all eight byte-offset bits survive the six-bit field.
    let uimm :=
      (slice16 h 3 2 <<< 6) ||| (slice16 h 12 12 <<< 5) ||| (slice16 h 6 4 <<< 2)
    .C_LWSP (BitVec.ofNat 6 (uimm >>> 2), mkReg (slice16 h 11 7))
  | 2, 6 =>
    -- Store the word offset so all eight byte-offset bits survive the six-bit field.
    let uimm := (slice16 h 8 7 <<< 6) ||| (slice16 h 12 9 <<< 2)
    .C_SWSP (BitVec.ofNat 6 (uimm >>> 2), mkReg (slice16 h 6 2))
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

/-- Sail `encode` (RV32 I+M). -/
def encode (w : BitVec 32) : Insn :=
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
      | 0 => .MUL (rs2, rs1, rd,
          { result_part := .Low, signed_rs1 := .Signed, signed_rs2 := .Signed })
      | 1 => .MUL (rs2, rs1, rd,
          { result_part := .High, signed_rs1 := .Signed, signed_rs2 := .Signed })
      | 2 => .MUL (rs2, rs1, rd,
          { result_part := .High, signed_rs1 := .Signed, signed_rs2 := .Unsigned })
      | 3 => .MUL (rs2, rs1, rd,
          { result_part := .High, signed_rs1 := .Unsigned, signed_rs2 := .Unsigned })
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
  | 0b0001111 =>
    -- FENCE.TSO encoding 0x8330000F; remaining fence encodings stay FENCE.
    if w == 0x8330000F#32 then .FENCE_TSO ()
    else .FENCE (0#4, 0#4, 0#4, rd, rs1)
  | 0b1110011 =>
    if w == 0x00000073#32 then .ECALL ()
    else if w == 0x00100073#32 then .EBREAK ()
    else if w == 0x30200073#32 then .MRET ()
    else if w == 0x10200073#32 then .SRET ()
    else if w == 0x10500073#32 then .WFI ()
    else .ILLEGAL w
  | _ => .ILLEGAL w

/-- Discriminant tag for FFI (stable small integers). -/
def insnTag (i : Insn) : UInt32 :=
  UInt32.ofNat <|
    match i with
    | .ILLEGAL _ => 0
    | .C_ILLEGAL _ => 1
    | .UTYPE (_, _, .LUI) => 2
    | .UTYPE (_, _, .AUIPC) => 3
    | .JAL _ => 4
    | .JALR _ => 5
    | .BTYPE _ => 6
    | .ITYPE (_, _, _, .ADDI) => 7
    | .ITYPE (_, _, _, .SLTI) => 8
    | .ITYPE (_, _, _, .SLTIU) => 9
    | .ITYPE (_, _, _, .XORI) => 10
    | .ITYPE (_, _, _, .ORI) => 11
    | .ITYPE (_, _, _, .ANDI) => 12
    | .SHIFTIOP (_, _, _, .SLLI) => 13
    | .SHIFTIOP (_, _, _, .SRLI) => 14
    | .SHIFTIOP (_, _, _, .SRAI) => 15
    | .RTYPE (_, _, _, .ADD) => 16
    | .RTYPE (_, _, _, .SUB) => 17
    | .RTYPE (_, _, _, .SLL) => 18
    | .RTYPE (_, _, _, .SLT) => 19
    | .RTYPE (_, _, _, .SLTU) => 20
    | .RTYPE (_, _, _, .XOR) => 21
    | .RTYPE (_, _, _, .SRL) => 22
    | .RTYPE (_, _, _, .SRA) => 23
    | .RTYPE (_, _, _, .OR) => 24
    | .RTYPE (_, _, _, .AND) => 25
    | .LOAD _ => 26
    | .STORE _ => 27
    | .FENCE_TSO _ => 28
    | .FENCE _ => 29
    | .ECALL _ => 30
    | .MRET _ => 31
    | .SRET _ => 32
    | .EBREAK _ => 33
    | .WFI _ => 34
    | .SFENCE_VMA _ => 35
    | .MUL (_, _, _, mop) =>
        match mop.result_part, mop.signed_rs1, mop.signed_rs2 with
        | .Low, _, _ => 36
        | .High, .Signed, .Signed => 37
        | .High, .Signed, .Unsigned => 38
        | .High, .Unsigned, .Unsigned => 39
        | .High, .Unsigned, .Signed => 36
    | .DIV (_, _, _, false) => 40
    | .DIV (_, _, _, true) => 41
    | .REM (_, _, _, false) => 42
    | .REM (_, _, _, true) => 43
    | .C_NOP _ => 44
    | .C_ADDI4SPN _ => 45
    | .C_LW _ => 46
    | .C_SW _ => 47
    | .C_ADDI _ => 48
    | .C_JAL _ => 49
    | .C_LI _ => 50
    | .C_ADDI16SP _ => 51
    | .C_LUI _ => 52
    | .C_SRLI _ => 53
    | .C_SRAI _ => 54
    | .C_ANDI _ => 55
    | .C_SUB _ => 56
    | .C_XOR _ => 57
    | .C_OR _ => 58
    | .C_AND _ => 59
    | .C_J _ => 60
    | .C_BEQZ _ => 61
    | .C_BNEZ _ => 62
    | .C_SLLI _ => 63
    | .C_LWSP _ => 64
    | .C_SWSP _ => 65
    | .C_JR _ => 66
    | .C_JALR _ => 67
    | .C_MV _ => 68
    | .C_EBREAK _ => 69
    | .C_ADD _ => 70

@[export lean_rv32_decode32]
def exportEncode32 (w : UInt32) : UInt32 :=
  insnTag (encode (BitVec.ofNat 32 w.toNat))

@[export lean_rv32_decode16]
def exportEncode16 (h : UInt32) : UInt32 :=
  insnTag (encodeCompressed (BitVec.ofNat 16 (h.toNat &&& 0xffff)))

end Cross.RV32


-- The maximum SP-relative word offset decodes to 252 bytes, without truncation.
#guard (match Cross.RV32.encodeCompressed 0xdf86#16 with
  | .C_SWSP (off, r) => off.toNat == 63 && r.toNat == 1
  | _ => false)
#guard (match Cross.RV32.encodeCompressed 0x50fe#16 with
  | .C_LWSP (off, r) => off.toNat == 63 && r.toNat == 1
  | _ => false)

-- Compressed word loads and stores use the same five-bit word-offset convention.
#guard (match Cross.RV32.encodeCompressed 0xc0d4#16 with
  | .C_SW (off, base, source) => off.toNat == 1 &&
      (Cross.RV32.creg2reg_idx base).toNat == 9 && (Cross.RV32.creg2reg_idx source).toNat == 13
  | _ => false)
#guard (match Cross.RV32.encodeCompressed 0xdcec#16 with
  | .C_SW (off, _, _) => off.toNat == 31
  | _ => false)
