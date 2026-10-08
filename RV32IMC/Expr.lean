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

/-- MVP context binding: the lowest start of six consecutive SW equalities.
Address-to-slot Predicates and other resource access rules remain undefined. -/
private def ctxBaseAlpha (Eg : ExprSet) : Option Nat := Id.run do
  let mut base : Option Nat := none
  for e in Eg.entries do
    if e.reg.kind == .stack && e.reg.width == .w32 && e.reg.alpha < (1 <<< 32) && e.rel == .eq then
      let α := e.reg.alpha
      let complete := (List.range 6).all fun j =>
        match Eg.lookupEq (Reg.sw (α + j)) with
        | some t => t.width == .w32
        | none => false
      if complete then
        base := some (match base with | none => α | some b => min b α)
  pure base

/-- Word-only context load. Resolve the access before discarding an x0 destination. -/
def exprLOAD (Eg : ExprSet) (rs1 rd : regidx) (offset : Nat) : Option ExprSet := do
  if !guardEg Eg || offset % 4 != 0 || offset ≥ 24 then none
  else
    let source ← readReg Eg rs1
    let ctx ← Eg.lookupEq (Reg.real32 10)
    -- Term has no BEq instance; its derived Repr compares the complete syntax, including widths.
    if source.width != .w32 || ctx.width != .w32 || reprStr (solve source) != reprStr (solve ctx) then
      none
    else
      let α ← ctxBaseAlpha Eg
      let t ← Eg.lookupEq (Reg.sw (α + offset / 4))
      some (assign rd t)

/-- Stack slots use alphas ≥ 2^32; context bindings occupy the lower namespace.
Normalize only affine 32-bit addresses, without changing symbolic value terms. -/
private def affineAddress : Term → Option (Option Nat × Nat)
  | .const .w32 c => some (none, MNat 32 c)
  | .var .w32 ξ => some (some ξ, 0)
  | .app .w32 (.add .w32) [a, .const .w32 b] => do
      let (root, off) ← affineAddress a
      some (root, MNat 32 (off + b))
  | .app .w32 (.sub .w32) [a, .const .w32 b] => do
      let (root, off) ← affineAddress a
      some (root, MNat 32 (off + (1 <<< 32) - MNat 32 b))
  | _ => none

/-- SP and its affine aliases bind aligned word slots. Symbolic alignment is an
entry-contract premise; concrete addresses are checked. No heap is inferred. -/
def stackSlot (Eg : ExprSet) (rs1 : regidx) (offset : Nat) : Option Reg := do
  let base ← readReg Eg rs1
  let tsp ← readReg Eg sp
  let (root, off) ← affineAddress base
  let (spRoot, spOff) ← affineAddress tsp
  if root != spRoot || (MNat 32 (off + offset) + (1 <<< 32) - spOff) % 4 != 0 then none
  else
    let address := MNat 32 (off + offset)
    if root.isNone && address % 4 != 0 then none
    else
      let tag := match root with | none => 0 | some ξ => ξ + 1
      some (Reg.sw ((1 <<< 32) + tag * (1 <<< 32) + address))

def exprStackLOAD (Eg : ExprSet) (rs1 rd : regidx) (offset : Nat) : Option ExprSet := do
  if !guardEg Eg then none
  else
    let slot ← stackSlot Eg rs1 offset
    let t ← Eg.lookupEq slot
    if t.width != .w32 then none else some (assign rd t)

def exprWordLOAD (Eg : ExprSet) (rs1 rd : regidx) (offset : Nat) : Option ExprSet :=
  match exprStackLOAD Eg rs1 rd offset with
  | some Ei => some Ei
  | none => exprLOAD Eg rs1 rd offset

/-- Packet provenance follows the data slot, not the mutable a0 register.
An immutable byte image is an observation model; bounds/permissions are not proved here. -/
private def packetAddress (data address : Term) : Bool :=
  if address == data then true
  else match address with
    | .app .w32 (.add .w32) [base, _] => packetAddress data base
    | _ => false

/-- Little-endian reads from the bound immutable packet input. Structurally equal byte addresses
share the same Term, and wider loads compose those bytes rather than fresh variables. -/
def exprPacketLOAD (Eg : ExprSet) (rs1 rd : regidx) (offset width : Nat)
    (isUnsigned : Bool) : Option ExprSet := do
  if !guardEg Eg || !(width == 1 || width == 2 || width == 4) then none
  else
    let α ← ctxBaseAlpha Eg
    let data ← Eg.lookupEq (Reg.sw α)
    let source ← readReg Eg rs1
    if data.width != .w32 || source.width != .w32 || !packetAddress data source then none
    else
      let address := addStar .w32 source (Term.C32 offset)
      let byte := fun j => star .w32 .inputByte [data,
        addStar .w32 address (Term.C32 j)]
      let raw := (List.range width).foldl (fun acc j =>
        orStar 32 .w32 acc (shlStar .w32 (byte j) (Term.C32 (8 * j)))) (Term.C32 0)
      let value := if isUnsigned || width == 4 then raw
        else sStar (8 * width) .w32 32 raw
      some (assign rd value)

/-- Narrow loads project the addressed bytes of a known word before extending.
Cross-word accesses require a separate resource rule and reject. -/
def exprSizedLOAD (Eg : ExprSet) (rs1 rd : regidx) (offset width : Nat)
    (isUnsigned : Bool) : Option ExprSet := do
  if !(width == 1 || width == 2 || width == 4) then none
  else
    let within := offset % 4
    let known := if within + width ≤ 4 then
      exprWordLOAD Eg rs1 rd (offset - within) else none
    match known with
    | some Ei =>
      if rd.toNat == 0 then some Ei
      else
        let word ← Ei.lookupEq (xReg rd)
        let raw := star .w32 (.extract (8 * within) (8 * width) 32) [word]
        let value := if isUnsigned || width == 4 then raw
          else sStar (8 * width) .w32 32 raw
        some (assign rd value)
    | none => exprPacketLOAD Eg rs1 rd offset width isUnsigned

def exprSTORE (Eg : ExprSet) (rs1 rs2 : regidx) (offset width : Nat) : Option ExprSet := do
  if !guardEg Eg || width != 4 then none
  else
    let slot ← stackSlot Eg rs1 offset
    let value ← readReg Eg rs2
    if value.width != .w32 then none
    else some (ExprSet.empty.insertEq slot (solve value))
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
  | .LOAD (imm, rs1, rd, isUnsigned, width) =>
      if width == 4 then
        match exprWordLOAD Eg rs1 rd (immI32 imm) with
        | some Ei => some Ei
        | none => exprPacketLOAD Eg rs1 rd (immI32 imm) width isUnsigned
      else exprSizedLOAD Eg rs1 rd (immI32 imm) width isUnsigned
  | .STORE (imm, rs2, rs1, width) => exprSTORE Eg rs1 rs2 (immI32 imm) width
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
  | .C_LW (uimm, rs1, rd) =>
      exprWordLOAD Eg (creg2reg_idx rs1) (creg2reg_idx rd) (uimm.toNat <<< 2)
  | .C_LWSP (uimm, rd) =>
      if isX0 rd then none else exprStackLOAD Eg sp rd (uimm.toNat <<< 2)
  | .C_SW (uimm, rs1, rs2) =>
      exprSTORE Eg (creg2reg_idx rs1) (creg2reg_idx rs2) (uimm.toNat <<< 2) 4
  | .C_SWSP (uimm, rs2) => exprSTORE Eg sp rs2 (uimm.toNat <<< 2) 4
  | .C_EBREAK _ => exprReject

/-- Single-instruction `value(Eg, i) = Ei`: return the local set from `expr`
after checking key uniqueness. CommonMath applies the global-state override. -/
def step (Eg : ExprSet) (i : Insn) : Option ExprSet :=
  match expr Eg i with
  | none => none
  | some Ei => if Ei.keysUnique then some Ei else none

-- ADDI replaces x1 locally; the unrelated x2 must not appear in the result.
#guard
  (let Eg := ExprSet.empty
      |>.insertEq (Reg.real32 1) (Term.C32 10)
      |>.insertEq (Reg.real32 2) (Term.C32 20)
   match step Eg (.ITYPE (1#12, .Regidx 1#5, .Regidx 1#5, .ADDI)) with
   | some Ei =>
       match Ei.entries with
       | [⟨r, rel, .const w c⟩] =>
           r == Reg.real32 1 && rel == .eq && w == .w32 && c == 11
       | _ => false
   | none => false)

-- A successful empty local effect stays empty even when Eg is nonempty.
#guard
  (match step (ExprSet.empty.insertEq (Reg.real32 2) (Term.C32 20)) (.C_NOP 0#6) with
   | some Ei => Ei.entries.isEmpty
   | none => false)

/-- Spill/reload uses the address, not the changing SP expression or register name. -/
private def stackRoundTripCheck : Bool :=
  let entry := ExprSet.empty
    |>.insertEq (Reg.real32 2) (Term.V32 0)
    |>.insertEq (Reg.real32 8) (Term.V32 40)
    |>.insertEq (Reg.sw 0) (Term.C32 99)
  let adjusted := entry.insertEq (Reg.real32 2)
    (addStar .w32 (Term.V32 0) (Term.C32 (M 32 (-16))))
  match step adjusted (.C_SWSP (3#6, .Regidx 8#5)) with
  | none => false
  | some spill =>
    let saved := updateExpr adjusted spill
    let alias := saved.insertEq (Reg.real32 9)
      (addStar .w32 (Term.V32 0) (Term.C32 (M 32 (-4))))
    match step alias (.C_LW (0#5, .Cregidx 1#3, .Cregidx 2#3)),
        step saved (.C_LWSP (3#6, .Regidx 10#5)),
        step saved (.STORE (12#12, zreg, sp, 4)) with
    | some loadAlias, some reload, some overwrite =>
      loadAlias.lookupEq (Reg.real32 10) == some (Term.V32 40) &&
      reload.lookupEq (Reg.real32 10) == some (Term.V32 40) &&
      (updateExpr saved overwrite).lookupEq (Reg.sw 0) == some (Term.C32 99) &&
      (exprStackLOAD adjusted sp (.Regidx 10#5) 12).isNone &&
      (step saved (.C_LWSP (3#6, zreg))).isNone &&
      (exprSTORE saved sp (.Regidx 8#5) 2 4).isNone &&
      match stackSlot saved sp 12 with
      | some slot => (updateExpr saved overwrite).lookupEq slot == some (Term.C32 0)
      | none => false
    | _, _, _ => false

#guard stackRoundTripCheck

/-- Signed/unsigned subword loads retain the byte position and RV32 extension. -/
private def narrowStackLoadsCheck : Bool :=
  let E := ExprSet.empty.insertEq (Reg.real32 2) (Term.C32 0x3000)
  match exprSTORE E sp (.Regidx 8#5) 0 4 with
  | some _ => false -- Missing source must reject even before a later read.
  | none =>
    let E := E.insertEq (Reg.real32 8) (Term.C32 0x80ff7f01)
    match exprSTORE E sp (.Regidx 8#5) 0 4 with
    | none => false
    | some spill =>
      let saved := updateExpr E spill
      let cases := [(0, 1, true, 1), (1, 1, false, 127),
        (2, 1, false, 0xffffffff), (3, 1, true, 128),
        (2, 2, true, 0x80ff), (2, 2, false, 0xffff80ff)]
      cases.all (fun (off, width, u, expected) =>
        match step saved (.LOAD (BitVec.ofNat 12 off, sp, .Regidx 10#5, u, width)) with
        | some Ei => Ei.lookupEq (Reg.real32 10) == some (Term.C32 expected)
        | none => false) &&
      (exprSizedLOAD saved sp (.Regidx 10#5) 3 2 true).isNone

#guard narrowStackLoadsCheck

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

