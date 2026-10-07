import CommonMath
import LeanRV32IMC.Types
import LeanRV32IMC.Regs
import LeanRV32IMC.MArith

namespace LeanRV32IMC
open CommonMath

/- value(Eg, i): none = reject; some empty = success with no new Expr -/

def sextBits (srcBits : Nat) (v : Nat) : Nat :=
  M 32 (s srcBits (MNat srcBits v))

def immI32 (imm : BitVec 12) : Nat := sextBits 12 imm.toNat
def uimmU32 (imm : BitVec 20) : Nat := MNat 32 (imm.toNat <<< 12)
def cImm6 (imm : BitVec 6) : Nat := sextBits 6 imm.toNat
def cAddi4spnImm (nzimm : BitVec 8) : Nat := nzimm.toNat
def cAddi16spImm (imm : BitVec 6) : Nat := sextBits 10 (imm.toNat <<< 4)
def cLuiU (imm : BitVec 6) : Nat := M 32 (s 6 imm.toNat * Int.ofNat (1 <<< 12))

def readReg (Eg : ExprSet) (r : regidx) : Option Term :=
  if isX0 r then some (Term.C32 0)
  else Eg.lookupEq (regOf r)

def readPC (Eg : ExprSet) : Option Term := Eg.lookupEq regPc

def checkX0 (Eg : ExprSet) : Bool :=
  match Eg.lookupEq regX0 with
  | none => true
  | some t =>
      match eval (solve t) with
      | some 0 => true
      | _ => false

def assign (rd : regidx) (t : Term) : ExprSet :=
  if isX0 rd then ExprSet.empty
  else ExprSet.empty.insertEq (regOf rd) (solve t)

def guardEg (Eg : ExprSet) : Bool := Eg.keysUnique && checkX0 Eg

def valueUTYPE (Eg : ExprSet) (imm : BitVec 20) (rd : regidx) (op : uop) : Option ExprSet :=
  if !guardEg Eg then none
  else
    let U := uimmU32 imm
    match op with
    | .LUI => some (assign rd (Term.C32 U))
    | .AUIPC =>
        match readPC Eg with
        | none => none
        | some tπ => some (assign rd (addStar .w32 tπ (Term.C32 U)))

def valueITYPE (Eg : ExprSet) (imm : BitVec 12) (rs1 rd : regidx) (op : iop) : Option ExprSet :=
  if !guardEg Eg then none
  else
    match readReg Eg rs1 with
    | none => none
    | some ta =>
        let I := Term.C32 (immI32 imm)
        let t :=
          match op with
          | .ADDI => addStar .w32 ta I
          | .SLTI => ltsStar .w32 ta I
          | .SLTIU => ltuStar .w32 ta I
          | .ANDI => andStar 32 .w32 ta I
          | .ORI => orStar 32 .w32 ta I
          | .XORI => xorStar 32 .w32 ta I
        some (assign rd t)

def valueSHIFTIOP (Eg : ExprSet) (shamt : BitVec 6) (rs1 rd : regidx) (op : sop) : Option ExprSet :=
  if !guardEg Eg then none
  else
    match readReg Eg rs1 with
    | none => none
    | some ta =>
        let k := Term.C32 (shamt.toNat % 32)
        let t :=
          match op with
          | .SLLI => shlStar .w32 ta k
          | .SRLI => lshrStar .w32 ta k
          | .SRAI => ashrStar .w32 ta k
        some (assign rd t)

def valueRTYPE (Eg : ExprSet) (rs2 rs1 rd : regidx) (op : rop) : Option ExprSet :=
  if !guardEg Eg then none
  else
    match readReg Eg rs1, readReg Eg rs2 with
    | some ta, some tb =>
        let t :=
          match op with
          | .ADD => addStar .w32 ta tb
          | .SUB => subStar .w32 ta tb
          | .SLT => ltsStar .w32 ta tb
          | .SLTU => ltuStar .w32 ta tb
          | .AND => andStar 32 .w32 ta tb
          | .OR => orStar 32 .w32 ta tb
          | .XOR => xorStar 32 .w32 ta tb
          | .SLL => shlStar .w32 ta tb
          | .SRL => lshrStar .w32 ta tb
          | .SRA => ashrStar .w32 ta tb
        some (assign rd t)
    | _, _ => none

def valueMUL (Eg : ExprSet) (rs2 rs1 rd : regidx) (mop : mul_op) : Option ExprSet :=
  if !guardEg Eg then none
  else
    match readReg Eg rs1, readReg Eg rs2 with
    | some ta, some tb =>
        let t? :=
          match mop.result_part, mop.signed_rs1, mop.signed_rs2 with
          | .Low, _, _ => some (mulloStar .w32 ta tb)
          | .High, .Signed, .Signed => closedBin mulh ta tb
          | .High, .Signed, .Unsigned => closedBin mulhsu ta tb
          | .High, .Unsigned, .Unsigned => closedBin mulhu ta tb
          | .High, .Unsigned, .Signed => closedBin mulhsu tb ta
        match t? with
        | some t => some (assign rd t)
        | none => none
    | _, _ => none

def valueDIV (Eg : ExprSet) (rs2 rs1 rd : regidx) (isUnsigned : Bool) : Option ExprSet :=
  if !guardEg Eg then none
  else
    match readReg Eg rs1, readReg Eg rs2 with
    | some ta, some tb =>
        match closedBin (if isUnsigned then divu else divs) ta tb with
        | some t => some (assign rd t)
        | none => none
    | _, _ => none

def valueREM (Eg : ExprSet) (rs2 rs1 rd : regidx) (isUnsigned : Bool) : Option ExprSet :=
  if !guardEg Eg then none
  else
    match readReg Eg rs1, readReg Eg rs2 with
    | some ta, some tb =>
        match closedBin (if isUnsigned then remu else rems) ta tb with
        | some t => some (assign rd t)
        | none => none
    | _, _ => none

def valueJAL (Eg : ExprSet) (rd : regidx) : Option ExprSet :=
  if !guardEg Eg then none
  else if isX0 rd then some ExprSet.empty
  else
    match readPC Eg with
    | none => none
    | some tπ => some (assign rd (addStar .w32 tπ (Term.C32 4)))

def valueJALR (Eg : ExprSet) (rs1 rd : regidx) : Option ExprSet :=
  if !guardEg Eg then none
  else
    match readReg Eg rs1 with
    | none => none
    | some _ =>
        if isX0 rd then some ExprSet.empty
        else
          match readPC Eg with
          | none => none
          | some tπ => some (assign rd (addStar .w32 tπ (Term.C32 4)))

def valueLOAD (_Eg : ExprSet) (_rd : regidx) : Option ExprSet := none
def valueSTORE (_Eg : ExprSet) : Option ExprSet := none
def valueEmpty (Eg : ExprSet) : Option ExprSet := if guardEg Eg then some ExprSet.empty else none
def valueReject : Option ExprSet := none

def valueC_ADDI4SPN (Eg : ExprSet) (rdc : cregidx) (nzimm : BitVec 8) : Option ExprSet :=
  if !guardEg Eg then none
  else if nzimm.toNat == 0 then none
  else
    match readReg Eg sp with
    | none => none
    | some tsp =>
        some (assign (creg2reg_idx rdc) (addStar .w32 tsp (Term.C32 (cAddi4spnImm nzimm))))

def valueC_ADDI (Eg : ExprSet) (imm : BitVec 6) (rsd : regidx) : Option ExprSet :=
  if !guardEg Eg then none
  else if isX0 rsd then some ExprSet.empty
  else
    match readReg Eg rsd with
    | none => none
    | some td => some (assign rsd (addStar .w32 td (Term.C32 (cImm6 imm))))

def valueC_LI (Eg : ExprSet) (imm : BitVec 6) (rd : regidx) : Option ExprSet :=
  if !guardEg Eg then none
  else some (assign rd (Term.C32 (cImm6 imm)))

def valueC_ADDI16SP (Eg : ExprSet) (imm : BitVec 6) : Option ExprSet :=
  if !guardEg Eg then none
  else if imm.toNat == 0 then none
  else
    match readReg Eg sp with
    | none => none
    | some tsp => some (assign sp (addStar .w32 tsp (Term.C32 (cAddi16spImm imm))))

def valueC_LUI (Eg : ExprSet) (imm : BitVec 6) (rd : regidx) : Option ExprSet :=
  if !guardEg Eg then none
  else if isX0 rd || rd.toNat == 2 then none
  else if imm.toNat == 0 then none
  else some (assign rd (Term.C32 (cLuiU imm)))

def valueC_shift (Eg : ExprSet) (shamt : BitVec 6) (rsd : cregidx) (op : sop) : Option ExprSet :=
  if !guardEg Eg then none
  else if shamt.toNat == 0 then none
  else
    let r := creg2reg_idx rsd
    valueSHIFTIOP Eg shamt r r op

def valueC_SLLI (Eg : ExprSet) (shamt : BitVec 6) (rsd : regidx) : Option ExprSet :=
  if !guardEg Eg then none
  else if isX0 rsd then some ExprSet.empty
  else if shamt.toNat == 0 then some ExprSet.empty
  else valueSHIFTIOP Eg shamt rsd rsd .SLLI

def valueC_ANDI (Eg : ExprSet) (imm : BitVec 6) (rsd : cregidx) : Option ExprSet :=
  if !guardEg Eg then none
  else
    let r := creg2reg_idx rsd
    match readReg Eg r with
    | none => none
    | some td => some (assign r (andStar 32 .w32 td (Term.C32 (cImm6 imm))))

def valueC_binary (Eg : ExprSet) (rsd rs2 : cregidx) (op : rop) : Option ExprSet :=
  valueRTYPE Eg (creg2reg_idx rs2) (creg2reg_idx rsd) (creg2reg_idx rsd) op

def valueC_MV (Eg : ExprSet) (rd rs2 : regidx) : Option ExprSet :=
  if !guardEg Eg then none
  else if isX0 rd then some ExprSet.empty
  else if isX0 rs2 then some (assign rd (Term.C32 0))
  else
    match readReg Eg rs2 with
    | none => none
    | some tb => some (assign rd (idStar .w32 tb))

def valueC_ADD (Eg : ExprSet) (rsd rs2 : regidx) : Option ExprSet :=
  if !guardEg Eg then none
  else if isX0 rsd then some ExprSet.empty
  else valueRTYPE Eg rs2 rsd rsd .ADD

def valueC_JAL (Eg : ExprSet) : Option ExprSet :=
  if !guardEg Eg then none
  else
    match readPC Eg with
    | none => none
    | some tπ => some (assign ra (addStar .w32 tπ (Term.C32 2)))

def valueC_JALR (Eg : ExprSet) (rs1 : regidx) : Option ExprSet :=
  if !guardEg Eg then none
  else if isX0 rs1 then none
  else
    match readReg Eg rs1 with
    | none => none
    | some _ =>
        match readPC Eg with
        | none => none
        | some tπ => some (assign ra (addStar .w32 tπ (Term.C32 2)))

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
  | .ECALL _ | .EBREAK _ | .MRET _ | .SRET _ | .WFI _ | .SFENCE_VMA _ => valueReject
  | .ILLEGAL _ | .C_ILLEGAL _ => valueReject
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
      else match readReg Eg rs1 with | none => none | some _ => valueEmpty Eg
  | .C_BEQZ _ | .C_BNEZ _ => valueEmpty Eg
  | .C_LW _ => valueLOAD Eg zreg
  | .C_LWSP (_uimm, rd) => if isX0 rd then valueReject else valueLOAD Eg rd
  | .C_SW _ | .C_SWSP _ => valueSTORE Eg
  | .C_EBREAK _ => valueReject

def step (Eg : ExprSet) (i : instruction) : Option ExprSet :=
  match value Eg i with
  | none => none
  | some Ei => if Ei.keysUnique then some (ExprSet.override Eg Ei) else none

end LeanRV32IMC
