import CommonMath
import LeanRV32IMC.Types

/-!
# LeanRV32IMC.Value — Expr value functions

Implements `value(E_g, i) = E_i` from `doc/rv32imc-expr-value-functions.md`.
Partial: `none` means reject; `some []` means success with no new Expr.
-/

namespace LeanRV32IMC
open CommonMath

/-! ## Helpers -/

def regOf (r : regidx) : Reg := Reg.real32 r.toNat

def isX0 (r : regidx) : Bool := r.toNat == 0

/-- Sign-extend a bit-pattern of width `srcBits` into 32-bit Nat. -/
def sextBits (srcBits : Nat) (v : Nat) : Nat :=
  M 32 (s srcBits (MNat srcBits v))

def immI32 (imm : BitVec 12) : Nat := sextBits 12 imm.toNat

def uimmU32 (imm : BitVec 20) : Nat := MNat 32 (imm.toNat <<< 12)

/-- Read equality term for a real register; x0 is always C(0). -/
def readReg (Eg : ExprSet) (r : regidx) : Option Term :=
  if isX0 r then some (Term.C32 0)
  else lookupEq Eg (regOf r)

def readPC (Eg : ExprSet) : Option Term :=
  lookupEq Eg Reg.pc32

/-- Validate x0 equality in Eg if present. -/
def checkX0 (Eg : ExprSet) : Bool :=
  match lookupEq Eg Reg.x0 with
  | none => true
  | some t =>
      match eval (solve t) with
      | some 0 => true
      | _ => false

def assign (rd : regidx) (t : Term) : ExprSet :=
  if isX0 rd then [] else [Expr.mkEq (regOf rd) (solve t)]

def assignReg (r : Reg) (t : Term) : ExprSet :=
  [Expr.mkEq r (solve t)]

/-- Require key-unique Eg and legal x0. -/
def guardEg (Eg : ExprSet) : Bool :=
  keysUnique Eg && checkX0 Eg

/-! ## Per-constructor value -/

def valueUTYPE (Eg : ExprSet) (imm : BitVec 20) (rd : regidx) (op : uop) : Option ExprSet :=
  if !guardEg Eg then none
  else
    let U := uimmU32 imm
    match op with
    | .LUI => some (assign rd (Term.C32 U))
    | .AUIPC =>
        match readPC Eg with
        | none => none
        | some tπ => some (assign rd (star .w32 (.auipc32 U) [tπ]))

def valueITYPE (Eg : ExprSet) (imm : BitVec 12) (rs1 rd : regidx) (op : iop) : Option ExprSet :=
  if !guardEg Eg then none
  else
    match readReg Eg rs1 with
    | none => none
    | some ta =>
        let I := immI32 imm
        let t :=
          match op with
          | .ADDI => star .w32 (.addImm32 I) [ta]
          | .SLTI => star .w32 (.slti32 I) [ta]
          | .SLTIU => star .w32 (.sltiu32 I) [ta]
          | .ANDI => star .w32 (.andImm32 I) [ta]
          | .ORI => star .w32 (.orImm32 I) [ta]
          | .XORI => star .w32 (.xorImm32 I) [ta]
        some (assign rd t)

def valueSHIFTIOP (Eg : ExprSet) (shamt : BitVec 6) (rs1 rd : regidx) (op : sop) : Option ExprSet :=
  if !guardEg Eg then none
  else
    match readReg Eg rs1 with
    | none => none
    | some ta =>
        let k := shamt.toNat % 32
        let t :=
          match op with
          | .SLLI => star .w32 (.shlImm32 k) [ta]
          | .SRLI => star .w32 (.lshrImm32 k) [ta]
          | .SRAI => star .w32 (.ashrImm32 k) [ta]
        some (assign rd t)

def valueRTYPE (Eg : ExprSet) (rs2 rs1 rd : regidx) (op : rop) : Option ExprSet :=
  if !guardEg Eg then none
  else
    match readReg Eg rs1, readReg Eg rs2 with
    | some ta, some tb =>
        let t :=
          match op with
          | .ADD => star .w32 (.add .w32) [ta, tb]
          | .SUB => star .w32 (.sub .w32) [ta, tb]
          | .SLT => star .w32 (.lts .w32) [ta, tb]
          | .SLTU => star .w32 (.ltu .w32) [ta, tb]
          | .AND => star .w32 (.and 32) [ta, tb]
          | .OR => star .w32 (.or 32) [ta, tb]
          | .XOR => star .w32 (.xor 32) [ta, tb]
          | .SLL => star .w32 (.shl .w32) [ta, tb]
          | .SRL => star .w32 (.lshr .w32) [ta, tb]
          | .SRA => star .w32 (.ashr .w32) [ta, tb]
        some (assign rd t)
    | _, _ => none

def valueMUL (Eg : ExprSet) (rs2 rs1 rd : regidx) (mop : mul_op) : Option ExprSet :=
  if !guardEg Eg then none
  else
    match readReg Eg rs1, readReg Eg rs2 with
    | some ta, some tb =>
        let t :=
          match mop.result_part, mop.signed_rs1, mop.signed_rs2 with
          | .Low, _, _ => star .w32 (.mullo .w32) [ta, tb]
          | .High, .Signed, .Signed => star .w32 .mulh32 [ta, tb]
          | .High, .Signed, .Unsigned => star .w32 .mulhsu32 [ta, tb]
          | .High, .Unsigned, .Unsigned => star .w32 .mulhu32 [ta, tb]
          | .High, .Unsigned, .Signed => star .w32 .mulhsu32 [tb, ta]
        some (assign rd t)
    | _, _ => none

def valueDIV (Eg : ExprSet) (rs2 rs1 rd : regidx) (isUnsigned : Bool) : Option ExprSet :=
  if !guardEg Eg then none
  else
    match readReg Eg rs1, readReg Eg rs2 with
    | some ta, some tb =>
        let t :=
          if isUnsigned then star .w32 .divu32 [ta, tb]
          else star .w32 .div32 [ta, tb]
        some (assign rd t)
    | _, _ => none

def valueREM (Eg : ExprSet) (rs2 rs1 rd : regidx) (isUnsigned : Bool) : Option ExprSet :=
  if !guardEg Eg then none
  else
    match readReg Eg rs1, readReg Eg rs2 with
    | some ta, some tb =>
        let t :=
          if isUnsigned then star .w32 .remu32 [ta, tb]
          else star .w32 .rem32 [ta, tb]
        some (assign rd t)
    | _, _ => none

def valueJAL (Eg : ExprSet) (rd : regidx) : Option ExprSet :=
  if !guardEg Eg then none
  else if isX0 rd then some []
  else
    match readPC Eg with
    | none => none
    | some tπ => some (assign rd (star .w32 .linkPlus4 [tπ]))

def valueJALR (Eg : ExprSet) (rs1 rd : regidx) : Option ExprSet :=
  if !guardEg Eg then none
  else
    -- Base must be defined even when link is discarded.
    match readReg Eg rs1 with
    | none => none
    | some _ =>
        if isX0 rd then some []
        else
          match readPC Eg with
          | none => none
          | some tπ => some (assign rd (star .w32 .linkPlus4 [tπ]))

/-- LOAD / C_LW / C_LWSP: virtual-mark matching TBD → reject for now (except empty when later). -/
def valueLOAD (_Eg : ExprSet) (_rd : regidx) : Option ExprSet :=
  none

/-- STORE / C_SW / C_SWSP: virtual-mark matching TBD → reject. -/
def valueSTORE (_Eg : ExprSet) : Option ExprSet :=
  none

def valueEmpty (Eg : ExprSet) : Option ExprSet :=
  if guardEg Eg then some [] else none

def valueReject : Option ExprSet := none

/-! ## Compressed immediates (already partially recovered in decode fields) -/

def cImm6 (imm : BitVec 6) : Nat := sextBits 6 imm.toNat

/-- C.ADDI4SPN nzuimm field is already scaled (low 2 bits zero). -/
def cAddi4spnImm (nzimm : BitVec 8) : Nat := nzimm.toNat

/-- C.ADDI16SP: sign-extend 6-bit field then append 4 zero bits. -/
def cAddi16spImm (imm : BitVec 6) : Nat := sextBits 10 (imm.toNat <<< 4)

/-- C.LUI: \(U_C=M_{32}(s_6(h)2^{12})\). -/
def cLuiU (imm : BitVec 6) : Nat := M 32 (s 6 imm.toNat * Int.ofNat (1 <<< 12))

def valueC_ADDI4SPN (Eg : ExprSet) (rdc : cregidx) (nzimm : BitVec 8) : Option ExprSet :=
  if !guardEg Eg then none
  else if nzimm.toNat == 0 then none
  else
    match readReg Eg sp with
    | none => none
    | some tsp =>
        let ι := cAddi4spnImm nzimm
        some (assign (creg2reg_idx rdc) (star .w32 (.addImm32 ι) [tsp]))

def valueC_ADDI (Eg : ExprSet) (imm : BitVec 6) (rsd : regidx) : Option ExprSet :=
  if !guardEg Eg then none
  else if isX0 rsd then some []  -- HINT / NOP-class when rd=x0
  else
    match readReg Eg rsd with
    | none => none
    | some td =>
        let ι := cImm6 imm
        some (assign rsd (star .w32 (.addImm32 ι) [td]))

def valueC_LI (Eg : ExprSet) (imm : BitVec 6) (rd : regidx) : Option ExprSet :=
  if !guardEg Eg then none
  else some (assign rd (Term.C32 (cImm6 imm)))

def valueC_ADDI16SP (Eg : ExprSet) (imm : BitVec 6) : Option ExprSet :=
  if !guardEg Eg then none
  else if imm.toNat == 0 then none
  else
    match readReg Eg sp with
    | none => none
    | some tsp =>
        let ι := cAddi16spImm imm
        some (assign sp (star .w32 (.addImm32 ι) [tsp]))

def valueC_LUI (Eg : ExprSet) (imm : BitVec 6) (rd : regidx) : Option ExprSet :=
  if !guardEg Eg then none
  else if isX0 rd || rd.toNat == 2 then none
  else if imm.toNat == 0 then none
  else some (assign rd (Term.C32 (cLuiU imm)))

def valueC_shift (Eg : ExprSet) (shamt : BitVec 6) (rsd : cregidx) (op : sop) : Option ExprSet :=
  if !guardEg Eg then none
  else if shamt.toNat == 0 then none  -- reserved for SRLI/SRAI; C.SLLI shamt=0 is HINT
  else
    let r := creg2reg_idx rsd
    valueSHIFTIOP Eg shamt r r op

def valueC_SLLI (Eg : ExprSet) (shamt : BitVec 6) (rsd : regidx) : Option ExprSet :=
  if !guardEg Eg then none
  else if isX0 rsd then some []  -- HINT
  else if shamt.toNat == 0 then some []  -- HINT on RV32
  else valueSHIFTIOP Eg shamt rsd rsd .SLLI

def valueC_ANDI (Eg : ExprSet) (imm : BitVec 6) (rsd : cregidx) : Option ExprSet :=
  if !guardEg Eg then none
  else
    let r := creg2reg_idx rsd
    match readReg Eg r with
    | none => none
    | some td =>
        let I := cImm6 imm
        some (assign r (star .w32 (.andImm32 I) [td]))

def valueC_binary (Eg : ExprSet) (rsd rs2 : cregidx) (op : rop) : Option ExprSet :=
  let a := creg2reg_idx rsd
  let b := creg2reg_idx rs2
  valueRTYPE Eg b a a op

def valueC_MV (Eg : ExprSet) (rd rs2 : regidx) : Option ExprSet :=
  if !guardEg Eg then none
  else if isX0 rd then some []  -- HINT
  else if isX0 rs2 then
    -- C.MV rd, x0 := copy zero
    some (assign rd (Term.C32 0))
  else
    match readReg Eg rs2 with
    | none => none
    | some tb => some (assign rd (star .w32 (.id .w32) [tb]))

def valueC_ADD (Eg : ExprSet) (rsd rs2 : regidx) : Option ExprSet :=
  if !guardEg Eg then none
  else if isX0 rsd then some []  -- HINT
  else valueRTYPE Eg rs2 rsd rsd .ADD

def valueC_JAL (Eg : ExprSet) : Option ExprSet :=
  if !guardEg Eg then none
  else
    match readPC Eg with
    | none => none
    | some tπ => some (assign ra (star .w32 .linkPlus2 [tπ]))

def valueC_JALR (Eg : ExprSet) (rs1 : regidx) : Option ExprSet :=
  if !guardEg Eg then none
  else if isX0 rs1 then none
  else
    match readReg Eg rs1 with
    | none => none
    | some _ =>
        match readPC Eg with
        | none => none
        | some tπ => some (assign ra (star .w32 .linkPlus2 [tπ]))

/-! ## Top-level value -/

/-- \(\operatorname{value}(E_g,i)\). `none` = reject. -/
def value (Eg : ExprSet) (i : instruction) : Option ExprSet :=
  match i with
  | .UTYPE (imm, rd, op) => valueUTYPE Eg imm rd op
  | .ITYPE (imm, rs1, rd, op) => valueITYPE Eg imm rs1 rd op
  | .SHIFTIOP (shamt, rs1, rd, op) => valueSHIFTIOP Eg shamt rs1 rd op
  | .RTYPE (rs2, rs1, rd, op) => valueRTYPE Eg rs2 rs1 rd op
  | .MUL (rs2, rs1, rd, mop) => valueMUL Eg rs2 rs1 rd mop
  | .DIV (rs2, rs1, rd, u) => valueDIV Eg rs2 rs1 rd u
  | .REM (rs2, rs1, rd, u) => valueREM Eg rs2 rs1 rd u
  | .JAL (_, rd) => valueJAL Eg rd
  | .JALR (_, rs1, rd) => valueJALR Eg rs1 rd
  | .BTYPE _ => valueEmpty Eg
  | .LOAD (_, _, rd, _, _) => valueLOAD Eg rd
  | .STORE _ => valueSTORE Eg
  | .FENCE_TSO _ => valueEmpty Eg
  | .FENCE _ => valueEmpty Eg
  | .ECALL _ => valueReject
  | .EBREAK _ => valueReject
  | .MRET _ => valueReject
  | .SRET _ => valueReject
  | .WFI _ => valueReject
  | .SFENCE_VMA _ => valueReject
  | .ILLEGAL _ => valueReject
  | .C_ILLEGAL _ => valueReject
  | .C_NOP _ => valueEmpty Eg
  | .C_ADDI4SPN (rdc, nzimm) => valueC_ADDI4SPN Eg rdc nzimm
  | .C_ADDI (imm, rsd) => valueC_ADDI Eg imm rsd
  | .C_LI (imm, rd) => valueC_LI Eg imm rd
  | .C_ADDI16SP imm => valueC_ADDI16SP Eg imm
  | .C_LUI (imm, rd) => valueC_LUI Eg imm rd
  | .C_SRLI (shamt, rsd) => valueC_shift Eg shamt rsd .SRLI
  | .C_SRAI (shamt, rsd) => valueC_shift Eg shamt rsd .SRAI
  | .C_SLLI (shamt, rsd) => valueC_SLLI Eg shamt rsd
  | .C_ANDI (imm, rsd) => valueC_ANDI Eg imm rsd
  | .C_SUB (rsd, rs2) => valueC_binary Eg rsd rs2 .SUB
  | .C_XOR (rsd, rs2) => valueC_binary Eg rsd rs2 .XOR
  | .C_OR (rsd, rs2) => valueC_binary Eg rsd rs2 .OR
  | .C_AND (rsd, rs2) => valueC_binary Eg rsd rs2 .AND
  | .C_MV (rd, rs2) => valueC_MV Eg rd rs2
  | .C_ADD (rsd, rs2) => valueC_ADD Eg rsd rs2
  | .C_JAL _ => valueC_JAL Eg
  | .C_JALR rs1 => valueC_JALR Eg rs1
  | .C_J _ => valueEmpty Eg
  | .C_JR rs1 =>
      if isX0 rs1 then valueReject
      else
        match readReg Eg rs1 with
        | none => none
        | some _ => valueEmpty Eg
  | .C_BEQZ _ => valueEmpty Eg
  | .C_BNEZ _ => valueEmpty Eg
  | .C_LW _ => valueLOAD Eg zreg
  | .C_LWSP (_uimm, rd) =>
      if isX0 rd then valueReject
      else valueLOAD Eg rd
  | .C_SW _ => valueSTORE Eg
  | .C_SWSP _ => valueSTORE Eg
  | .C_EBREAK _ => valueReject

/-- Apply override after a successful value. -/
def step (Eg : ExprSet) (i : instruction) : Option ExprSet :=
  match value Eg i with
  | none => none
  | some Ei =>
      if keysUnique Ei then some (override Eg Ei) else none

end LeanRV32IMC
