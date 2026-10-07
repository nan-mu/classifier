import CommonMath
import RV32IMC.Insn

namespace RV32IMC
open CommonMath

/-! Use CommonMath.Reg: x0..x31 and PC as real32 alphas. -/

private def xReg (r : regidx) : Reg := Reg.real32 r.toNat
private def pcReg : Reg := Reg.real32 32
private def isX0 (r : regidx) : Bool := r.toNat == 0

/-! RV32M closed arithmetic (ISA rules on top of CommonMath TQ/TR). -/

private def mulhu (a b : Nat) : Nat :=
  MNat 32 ((MNat 32 a * MNat 32 b) / (1 <<< 32))
private def mulh (a b : Nat) : Nat :=
  M 32 (s 32 a * s 32 b / Int.ofNat (1 <<< 32))
private def mulhsu (a b : Nat) : Nat :=
  M 32 (s 32 a * Int.ofNat (MNat 32 b) / Int.ofNat (1 <<< 32))
private def divu (a b : Nat) : Nat :=
  let a := MNat 32 a; let b := MNat 32 b
  if b == 0 then (1 <<< 32) - 1 else a / b
private def remu (a b : Nat) : Nat :=
  let a := MNat 32 a; let b := MNat 32 b
  if b == 0 then a else a - b * (a / b)
private def divs (a b : Nat) : Nat :=
  let x := s 32 a; let y := s 32 b
  if y == 0 then (1 <<< 32) - 1
  else if x == -(Int.ofNat (1 <<< 31)) && y == -1 then 1 <<< 31
  else M 32 (TQ x y)
private def rems (a b : Nat) : Nat :=
  let x := s 32 a; let y := s 32 b
  if y == 0 then MNat 32 a
  else if x == -(Int.ofNat (1 <<< 31)) && y == -1 then 0
  else M 32 (TR x y)
private def closedBin (f : Nat → Nat → Nat) (ta tb : Term) : Option Term :=
  match eval (solve ta), eval (solve tb) with
  | some a, some b => some (Term.C32 (f a b))
  | _, _ => none


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
  else Eg.lookupEq (xReg r)

def readPC (Eg : ExprSet) : Option Term := Eg.lookupEq pcReg

def checkX0 (Eg : ExprSet) : Bool :=
  match Eg.lookupEq (xReg zreg) with
  | none => true
  | some t =>
      match eval (solve t) with
      | some 0 => true
      | _ => false

def assign (rd : regidx) (t : Term) : ExprSet :=
  if isX0 rd then ExprSet.empty
  else ExprSet.empty.insertEq (xReg rd) (solve t)

def guardEg (Eg : ExprSet) : Bool := Eg.keysUnique && checkX0 Eg

def exprUTYPE (Eg : ExprSet) (imm : BitVec 20) (rd : regidx) (op : uop) : Option ExprSet :=
  if !guardEg Eg then none
  else
    let U := uimmU32 imm
    match op with
    | .LUI => some (assign rd (Term.C32 U))
    | .AUIPC =>
        match readPC Eg with
        | none => none
        | some tπ => some (assign rd (addStar .w32 tπ (Term.C32 U)))

def exprITYPE (Eg : ExprSet) (imm : BitVec 12) (rs1 rd : regidx) (op : iop) : Option ExprSet :=
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

def exprSHIFTIOP (Eg : ExprSet) (shamt : BitVec 6) (rs1 rd : regidx) (op : sop) : Option ExprSet :=
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

def exprRTYPE (Eg : ExprSet) (rs2 rs1 rd : regidx) (op : rop) : Option ExprSet :=
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

def exprMUL (Eg : ExprSet) (rs2 rs1 rd : regidx) (mop : mul_op) : Option ExprSet :=
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

def exprDIV (Eg : ExprSet) (rs2 rs1 rd : regidx) (isUnsigned : Bool) : Option ExprSet :=
  if !guardEg Eg then none
  else
    match readReg Eg rs1, readReg Eg rs2 with
    | some ta, some tb =>
        match closedBin (if isUnsigned then divu else divs) ta tb with
        | some t => some (assign rd t)
        | none => none
    | _, _ => none

def exprREM (Eg : ExprSet) (rs2 rs1 rd : regidx) (isUnsigned : Bool) : Option ExprSet :=
  if !guardEg Eg then none
  else
    match readReg Eg rs1, readReg Eg rs2 with
    | some ta, some tb =>
        match closedBin (if isUnsigned then remu else rems) ta tb with
        | some t => some (assign rd t)
        | none => none
    | _, _ => none

def exprJAL (Eg : ExprSet) (rd : regidx) : Option ExprSet :=
  if !guardEg Eg then none
  else if isX0 rd then some ExprSet.empty
  else
    match readPC Eg with
    | none => none
    | some tπ => some (assign rd (addStar .w32 tπ (Term.C32 4)))

def exprJALR (Eg : ExprSet) (rs1 rd : regidx) : Option ExprSet :=
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

def exprLOAD (_Eg : ExprSet) (_rd : regidx) : Option ExprSet := none
def exprSTORE (_Eg : ExprSet) : Option ExprSet := none
def exprEmpty (Eg : ExprSet) : Option ExprSet := if guardEg Eg then some ExprSet.empty else none
def exprReject : Option ExprSet := none

def exprC_ADDI4SPN (Eg : ExprSet) (rdc : cregidx) (nzimm : BitVec 8) : Option ExprSet :=
  if !guardEg Eg then none
  else if nzimm.toNat == 0 then none
  else
    match readReg Eg sp with
    | none => none
    | some tsp =>
        some (assign (creg2reg_idx rdc) (addStar .w32 tsp (Term.C32 (cAddi4spnImm nzimm))))

def exprC_ADDI (Eg : ExprSet) (imm : BitVec 6) (rsd : regidx) : Option ExprSet :=
  if !guardEg Eg then none
  else if isX0 rsd then some ExprSet.empty
  else
    match readReg Eg rsd with
    | none => none
    | some td => some (assign rsd (addStar .w32 td (Term.C32 (cImm6 imm))))

def exprC_LI (Eg : ExprSet) (imm : BitVec 6) (rd : regidx) : Option ExprSet :=
  if !guardEg Eg then none
  else some (assign rd (Term.C32 (cImm6 imm)))

def exprC_ADDI16SP (Eg : ExprSet) (imm : BitVec 6) : Option ExprSet :=
  if !guardEg Eg then none
  else if imm.toNat == 0 then none
  else
    match readReg Eg sp with
    | none => none
    | some tsp => some (assign sp (addStar .w32 tsp (Term.C32 (cAddi16spImm imm))))

def exprC_LUI (Eg : ExprSet) (imm : BitVec 6) (rd : regidx) : Option ExprSet :=
  if !guardEg Eg then none
  else if isX0 rd || rd.toNat == 2 then none
  else if imm.toNat == 0 then none
  else some (assign rd (Term.C32 (cLuiU imm)))

def exprC_shift (Eg : ExprSet) (shamt : BitVec 6) (rsd : cregidx) (op : sop) : Option ExprSet :=
  if !guardEg Eg then none
  else if shamt.toNat == 0 then none
  else
    let r := creg2reg_idx rsd
    exprSHIFTIOP Eg shamt r r op

def exprC_SLLI (Eg : ExprSet) (shamt : BitVec 6) (rsd : regidx) : Option ExprSet :=
  if !guardEg Eg then none
  else if isX0 rsd then some ExprSet.empty
  else if shamt.toNat == 0 then some ExprSet.empty
  else exprSHIFTIOP Eg shamt rsd rsd .SLLI

def exprC_ANDI (Eg : ExprSet) (imm : BitVec 6) (rsd : cregidx) : Option ExprSet :=
  if !guardEg Eg then none
  else
    let r := creg2reg_idx rsd
    match readReg Eg r with
    | none => none
    | some td => some (assign r (andStar 32 .w32 td (Term.C32 (cImm6 imm))))

def exprC_binary (Eg : ExprSet) (rsd rs2 : cregidx) (op : rop) : Option ExprSet :=
  exprRTYPE Eg (creg2reg_idx rs2) (creg2reg_idx rsd) (creg2reg_idx rsd) op

def exprC_MV (Eg : ExprSet) (rd rs2 : regidx) : Option ExprSet :=
  if !guardEg Eg then none
  else if isX0 rd then some ExprSet.empty
  else if isX0 rs2 then some (assign rd (Term.C32 0))
  else
    match readReg Eg rs2 with
    | none => none
    | some tb => some (assign rd (idStar .w32 tb))

def exprC_ADD (Eg : ExprSet) (rsd rs2 : regidx) : Option ExprSet :=
  if !guardEg Eg then none
  else if isX0 rsd then some ExprSet.empty
  else exprRTYPE Eg rs2 rsd rsd .ADD

def exprC_JAL (Eg : ExprSet) : Option ExprSet :=
  if !guardEg Eg then none
  else
    match readPC Eg with
    | none => none
    | some tπ => some (assign ra (addStar .w32 tπ (Term.C32 2)))

def exprC_JALR (Eg : ExprSet) (rs1 : regidx) : Option ExprSet :=
  if !guardEg Eg then none
  else if isX0 rs1 then none
  else
    match readReg Eg rs1 with
    | none => none
    | some _ =>
        match readPC Eg with
        | none => none
        | some tπ => some (assign ra (addStar .w32 tπ (Term.C32 2)))

def expr (Eg : ExprSet) (i : Insn) : Option ExprSet :=
  match i with
  | .UTYPE (imm, rd, op) => exprUTYPE Eg imm rd op
  | .ITYPE (imm, rs1, rd, op) => exprITYPE Eg imm rs1 rd op
  | .SHIFTIOP (shamt, rs1, rd, op) => exprSHIFTIOP Eg shamt rs1 rd op
  | .RTYPE (rs2, rs1, rd, op) => exprRTYPE Eg rs2 rs1 rd op
  | .MUL (rs2, rs1, rd, mop) => exprMUL Eg rs2 rs1 rd mop
  | .DIV (rs2, rs1, rd, u) => exprDIV Eg rs2 rs1 rd u
  | .REM (rs2, rs1, rd, u) => exprREM Eg rs2 rs1 rd u
  | .JAL (_, rd) => exprJAL Eg rd
  | .JALR (_, rs1, rd) => exprJALR Eg rs1 rd
  | .BTYPE _ => exprEmpty Eg
  | .LOAD (_, _, rd, _, _) => exprLOAD Eg rd
  | .STORE _ => exprSTORE Eg
  | .FENCE_TSO _ => exprEmpty Eg
  | .FENCE _ => exprEmpty Eg
  | .ECALL _ | .EBREAK _ | .MRET _ | .SRET _ | .WFI _ | .SFENCE_VMA _ => exprReject
  | .ILLEGAL _ | .C_ILLEGAL _ => exprReject
  | .C_NOP _ => exprEmpty Eg
  | .C_ADDI4SPN (rdc, nzimm) => exprC_ADDI4SPN Eg rdc nzimm
  | .C_ADDI (imm, rsd) => exprC_ADDI Eg imm rsd
  | .C_LI (imm, rd) => exprC_LI Eg imm rd
  | .C_ADDI16SP imm => exprC_ADDI16SP Eg imm
  | .C_LUI (imm, rd) => exprC_LUI Eg imm rd
  | .C_SRLI (shamt, rsd) => exprC_shift Eg shamt rsd .SRLI
  | .C_SRAI (shamt, rsd) => exprC_shift Eg shamt rsd .SRAI
  | .C_SLLI (shamt, rsd) => exprC_SLLI Eg shamt rsd
  | .C_ANDI (imm, rsd) => exprC_ANDI Eg imm rsd
  | .C_SUB (rsd, rs2) => exprC_binary Eg rsd rs2 .SUB
  | .C_XOR (rsd, rs2) => exprC_binary Eg rsd rs2 .XOR
  | .C_OR (rsd, rs2) => exprC_binary Eg rsd rs2 .OR
  | .C_AND (rsd, rs2) => exprC_binary Eg rsd rs2 .AND
  | .C_MV (rd, rs2) => exprC_MV Eg rd rs2
  | .C_ADD (rsd, rs2) => exprC_ADD Eg rsd rs2
  | .C_JAL _ => exprC_JAL Eg
  | .C_JALR rs1 => exprC_JALR Eg rs1
  | .C_J _ => exprEmpty Eg
  | .C_JR rs1 =>
      if isX0 rs1 then exprReject
      else match readReg Eg rs1 with | none => none | some _ => exprEmpty Eg
  | .C_BEQZ _ | .C_BNEZ _ => exprEmpty Eg
  | .C_LW _ => exprLOAD Eg zreg
  | .C_LWSP (_uimm, rd) => if isX0 rd then exprReject else exprLOAD Eg rd
  | .C_SW _ | .C_SWSP _ => exprSTORE Eg
  | .C_EBREAK _ => exprReject

def step (Eg : ExprSet) (i : Insn) : Option ExprSet :=
  match expr Eg i with
  | none => none
  | some Ei => if Ei.keysUnique then some (ExprSet.override Eg Ei) else none

private def egEq (r : regidx) (v : Nat) : ExprSet :=
  if r.toNat == 0 then ExprSet.empty
  else ExprSet.empty.insertEq (xReg r) (Term.C32 v)

private def resultRd (Ei : ExprSet) (rd : regidx) : UInt32 :=
  if isX0 rd then 0
  else
    match Ei.lookupEq (xReg rd) with
    | some t =>
        match eval (solve t) with
        | some c => UInt32.ofNat c
        | none => 0xffffffff
    | none => 0xffffffff

@[export lean_rv32_value_addi]
def exportExprAddi (rs1Val imm rs1 rd : UInt32) : UInt32 :=
  let rs1i : regidx := .Regidx (BitVec.ofNat 5 (rs1.toNat &&& 31))
  let rdi : regidx := .Regidx (BitVec.ofNat 5 (rd.toNat &&& 31))
  let i : Insn := .ITYPE (BitVec.ofNat 12 (imm.toNat &&& 0xfff), rs1i, rdi, .ADDI)
  match expr (egEq rs1i rs1Val.toNat) i with
  | none => 0xffffffff
  | some Ei => resultRd Ei rdi

@[export lean_rv32_value_add]
def exportExprAdd (rs1Val rs2Val rs1 rs2 rd : UInt32) : UInt32 :=
  let r1 : regidx := .Regidx (BitVec.ofNat 5 (rs1.toNat &&& 31))
  let r2 : regidx := .Regidx (BitVec.ofNat 5 (rs2.toNat &&& 31))
  let rdi : regidx := .Regidx (BitVec.ofNat 5 (rd.toNat &&& 31))
  let Eg := ExprSet.override (egEq r1 rs1Val.toNat) (egEq r2 rs2Val.toNat)
  let i : Insn := .RTYPE (r2, r1, rdi, .ADD)
  match expr Eg i with
  | none => 0xffffffff
  | some Ei => resultRd Ei rdi

@[export lean_rv32_value_auipc]
def exportExprAuipc (pcVal uimm20 rd : UInt32) : UInt32 :=
  let rdi : regidx := .Regidx (BitVec.ofNat 5 (rd.toNat &&& 31))
  let Eg := ExprSet.empty.insertEq pcReg (Term.C32 pcVal.toNat)
  let i : Insn := .UTYPE (BitVec.ofNat 20 (uimm20.toNat &&& 0xfffff), rdi, .AUIPC)
  match expr Eg i with
  | none => 0xffffffff
  | some Ei => resultRd Ei rdi

@[export lean_rv32_value_lui]
def exportExprLui (uimm20 rd : UInt32) : UInt32 :=
  let rdi : regidx := .Regidx (BitVec.ofNat 5 (rd.toNat &&& 31))
  let i : Insn := .UTYPE (BitVec.ofNat 20 (uimm20.toNat &&& 0xfffff), rdi, .LUI)
  match expr ExprSet.empty i with
  | none => 0xffffffff
  | some Ei => resultRd Ei rdi

@[export lean_rv32_value_div]
def exportExprDiv (rs1Val rs2Val : UInt32) : UInt32 :=
  let r1 : regidx := .Regidx 1#5
  let r2 : regidx := .Regidx 2#5
  let rd : regidx := .Regidx 3#5
  let Eg := ExprSet.override (egEq r1 rs1Val.toNat) (egEq r2 rs2Val.toNat)
  match expr Eg (.DIV (r2, r1, rd, false)) with
  | none => 0xffffffff
  | some Ei => resultRd Ei rd

@[export lean_rv32_value_ecall_rejects]
def exportEcallRejects (_unused : UInt32) : UInt32 :=
  match expr ExprSet.empty (.ECALL ()) with
  | none => 1
  | some _ => 0

@[export lean_rv32_expr_override_keeps]
def exportOverrideKeeps (_unused : UInt32) : UInt32 :=
  let Eg :=
    ExprSet.empty
      |>.insertEq (Reg.real32 1) (Term.C32 10)
      |>.insertEq (Reg.real32 2) (Term.C32 20)
  let Ei := ExprSet.empty.insertEq (Reg.real32 1) (Term.C32 11)
  let E := ExprSet.override Eg Ei
  match E.lookupEq (Reg.real32 1), E.lookupEq (Reg.real32 2) with
  | some t1, some t2 =>
      match eval t1, eval t2 with
      | some 11, some 20 => 1
      | _, _ => 0
  | _, _ => 0

end RV32IMC

