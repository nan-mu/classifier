import CommonMath
import LeanRV32IMC.Types
import LeanRV32IMC.Decode
import LeanRV32IMC.Regs
import LeanRV32IMC.Value

namespace LeanRV32IMC
open CommonMath

@[export lean_rv32_decode32]
def exportDecode32 (w : UInt32) : UInt32 :=
  instructionTag (encdec_backwards (BitVec.ofNat 32 w.toNat))

@[export lean_rv32_decode16]
def exportDecode16 (h : UInt32) : UInt32 :=
  instructionTag (encdec_compressed_backwards (BitVec.ofNat 16 (h.toNat &&& 0xffff)))

private def egEq (r : regidx) (v : Nat) : ExprSet :=
  if r.toNat == 0 then ExprSet.empty
  else ExprSet.empty.insertEq (regOf r) (Term.C32 v)

private def resultRd (Ei : ExprSet) (rd : regidx) : UInt32 :=
  if isX0 rd then 0
  else
    match Ei.lookupEq (regOf rd) with
    | some t =>
        match eval (solve t) with
        | some c => UInt32.ofNat c
        | none => 0xffffffff
    | none => 0xffffffff

@[export lean_rv32_value_addi]
def exportValueAddi (rs1Val imm rs1 rd : UInt32) : UInt32 :=
  let rs1i : regidx := .Regidx (BitVec.ofNat 5 (rs1.toNat &&& 31))
  let rdi : regidx := .Regidx (BitVec.ofNat 5 (rd.toNat &&& 31))
  let Eg := egEq rs1i rs1Val.toNat
  let i : instruction := .ITYPE (BitVec.ofNat 12 (imm.toNat &&& 0xfff), rs1i, rdi, .ADDI)
  match value Eg i with
  | none => 0xffffffff
  | some Ei => resultRd Ei rdi

@[export lean_rv32_value_add]
def exportValueAdd (rs1Val rs2Val rs1 rs2 rd : UInt32) : UInt32 :=
  let r1 : regidx := .Regidx (BitVec.ofNat 5 (rs1.toNat &&& 31))
  let r2 : regidx := .Regidx (BitVec.ofNat 5 (rs2.toNat &&& 31))
  let rdi : regidx := .Regidx (BitVec.ofNat 5 (rd.toNat &&& 31))
  let Eg := ExprSet.override (egEq r1 rs1Val.toNat) (egEq r2 rs2Val.toNat)
  let i : instruction := .RTYPE (r2, r1, rdi, .ADD)
  match value Eg i with
  | none => 0xffffffff
  | some Ei => resultRd Ei rdi

@[export lean_rv32_value_auipc]
def exportValueAuipc (pcVal uimm20 rd : UInt32) : UInt32 :=
  let rdi : regidx := .Regidx (BitVec.ofNat 5 (rd.toNat &&& 31))
  let Eg := ExprSet.empty.insertEq regPc (Term.C32 pcVal.toNat)
  let i : instruction := .UTYPE (BitVec.ofNat 20 (uimm20.toNat &&& 0xfffff), rdi, .AUIPC)
  match value Eg i with
  | none => 0xffffffff
  | some Ei => resultRd Ei rdi

@[export lean_rv32_value_lui]
def exportValueLui (uimm20 rd : UInt32) : UInt32 :=
  let rdi : regidx := .Regidx (BitVec.ofNat 5 (rd.toNat &&& 31))
  let i : instruction := .UTYPE (BitVec.ofNat 20 (uimm20.toNat &&& 0xfffff), rdi, .LUI)
  match value ExprSet.empty i with
  | none => 0xffffffff
  | some Ei => resultRd Ei rdi

@[export lean_rv32_value_div]
def exportValueDiv (rs1Val rs2Val : UInt32) : UInt32 :=
  let r1 : regidx := .Regidx 1#5
  let r2 : regidx := .Regidx 2#5
  let rd : regidx := .Regidx 3#5
  let Eg := ExprSet.override (egEq r1 rs1Val.toNat) (egEq r2 rs2Val.toNat)
  let i : instruction := .DIV (r2, r1, rd, false)
  match value Eg i with
  | none => 0xffffffff
  | some Ei => resultRd Ei rd

@[export lean_rv32_value_ecall_rejects]
def exportEcallRejects (_unused : UInt32) : UInt32 :=
  match value ExprSet.empty (.ECALL ()) with
  | none => 1
  | some _ => 0

/-- ExprSet override keeps foreign keys. Returns 1 on success. -/
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

end LeanRV32IMC
