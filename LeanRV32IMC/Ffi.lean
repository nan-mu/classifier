import CommonMath
import LeanRV32IMC.Types
import LeanRV32IMC.Decode
import LeanRV32IMC.Value

/-!
# LeanRV32IMC.Ffi — C ABI exports for the Rust test crate
-/

namespace LeanRV32IMC
open CommonMath

/-- Decode a 32-bit word; return instruction tag (see `instructionTag`). -/
@[export lean_rv32_decode32]
def exportDecode32 (w : UInt32) : UInt32 :=
  instructionTag (encdec_backwards (BitVec.ofNat 32 w.toNat))

/-- Decode a 16-bit halfword; return instruction tag. -/
@[export lean_rv32_decode16]
def exportDecode16 (h : UInt32) : UInt32 :=
  instructionTag (encdec_compressed_backwards (BitVec.ofNat 16 (h.toNat &&& 0xffff)))

/--
Concrete ADDI value test.
Builds `Eg = { rs1 = C(rs1Val) }` (and optional PC), runs value, returns rd constant or
`0xFFFF_FFFF` on reject / non-constant.
-/
@[export lean_rv32_value_addi]
def exportValueAddi (rs1Val imm rs1 rd : UInt32) : UInt32 :=
  let rs1i : regidx := .Regidx (BitVec.ofNat 5 (rs1.toNat &&& 31))
  let rdi : regidx := .Regidx (BitVec.ofNat 5 (rd.toNat &&& 31))
  let Eg : ExprSet :=
    if rs1i.toNat == 0 then []
    else [Expr.mkEq (regOf rs1i) (Term.C32 rs1Val.toNat)]
  let i : instruction := .ITYPE (BitVec.ofNat 12 (imm.toNat &&& 0xfff), rs1i, rdi, .ADDI)
  match value Eg i with
  | none => 0xffffffff
  | some Ei =>
      if isX0 rdi then 0
      else
        match lookupEq Ei (regOf rdi) with
        | some t =>
            match eval (solve t) with
            | some c => UInt32.ofNat c
            | none => 0xffffffff
        | none => 0xffffffff

/-- Concrete ADD (R-type) value test. -/
@[export lean_rv32_value_add]
def exportValueAdd (rs1Val rs2Val rs1 rs2 rd : UInt32) : UInt32 :=
  let r1 : regidx := .Regidx (BitVec.ofNat 5 (rs1.toNat &&& 31))
  let r2 : regidx := .Regidx (BitVec.ofNat 5 (rs2.toNat &&& 31))
  let rdi : regidx := .Regidx (BitVec.ofNat 5 (rd.toNat &&& 31))
  let Eg : ExprSet := Id.run do
    let mut E : ExprSet := []
    if r1.toNat != 0 then E := Expr.mkEq (regOf r1) (Term.C32 rs1Val.toNat) :: E
    if r2.toNat != 0 then E := Expr.mkEq (regOf r2) (Term.C32 rs2Val.toNat) :: E
    pure E
  let i : instruction := .RTYPE (r2, r1, rdi, .ADD)
  match value Eg i with
  | none => 0xffffffff
  | some Ei =>
      if isX0 rdi then 0
      else
        match lookupEq Ei (regOf rdi) with
        | some t =>
            match eval (solve t) with
            | some c => UInt32.ofNat c
            | none => 0xffffffff
        | none => 0xffffffff

/-- Concrete AUIPC: needs PC in Eg. -/
@[export lean_rv32_value_auipc]
def exportValueAuipc (pcVal uimm20 rd : UInt32) : UInt32 :=
  let rdi : regidx := .Regidx (BitVec.ofNat 5 (rd.toNat &&& 31))
  let Eg : ExprSet := [Expr.mkEq Reg.pc32 (Term.C32 pcVal.toNat)]
  let i : instruction := .UTYPE (BitVec.ofNat 20 (uimm20.toNat &&& 0xfffff), rdi, .AUIPC)
  match value Eg i with
  | none => 0xffffffff
  | some Ei =>
      if isX0 rdi then 0
      else
        match lookupEq Ei (regOf rdi) with
        | some t =>
            match eval (solve t) with
            | some c => UInt32.ofNat c
            | none => 0xffffffff
        | none => 0xffffffff

/-- LUI concrete. -/
@[export lean_rv32_value_lui]
def exportValueLui (uimm20 rd : UInt32) : UInt32 :=
  let rdi : regidx := .Regidx (BitVec.ofNat 5 (rd.toNat &&& 31))
  let i : instruction := .UTYPE (BitVec.ofNat 20 (uimm20.toNat &&& 0xfffff), rdi, .LUI)
  match value [] i with
  | none => 0xffffffff
  | some Ei =>
      if isX0 rdi then 0
      else
        match lookupEq Ei (regOf rdi) with
        | some t =>
            match eval (solve t) with
            | some c => UInt32.ofNat c
            | none => 0xffffffff
        | none => 0xffffffff

/-- DIV signed concrete. -/
@[export lean_rv32_value_div]
def exportValueDiv (rs1Val rs2Val : UInt32) : UInt32 :=
  let r1 : regidx := .Regidx 1#5
  let r2 : regidx := .Regidx 2#5
  let rd : regidx := .Regidx 3#5
  let Eg : ExprSet :=
    [ Expr.mkEq (regOf r1) (Term.C32 rs1Val.toNat)
    , Expr.mkEq (regOf r2) (Term.C32 rs2Val.toNat) ]
  let i : instruction := .DIV (r2, r1, rd, false)
  match value Eg i with
  | none => 0xffffffff
  | some Ei =>
      match lookupEq Ei (regOf rd) with
      | some t =>
          match eval (solve t) with
          | some c => UInt32.ofNat c
          | none => 0xffffffff
      | none => 0xffffffff

/-- Return 1 if ECALL rejects. -/
@[export lean_rv32_value_ecall_rejects]
def exportEcallRejects (_unused : UInt32) : UInt32 :=
  match value [] (.ECALL ()) with
  | none => 1
  | some _ => 0

end LeanRV32IMC
