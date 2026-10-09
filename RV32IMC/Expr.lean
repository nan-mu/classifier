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

def guardEg (Eg : ExprSet) : Bool :=
  Eg.keysUnique && Eg.wellTyped && checkX0 Eg

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

/-- Stack slots use alphas ≥ 2^32; context bindings occupy the lower namespace.
Normalize only affine 32-bit addresses, without changing symbolic value terms. -/
private def affineAddress : Term → Option (Option Nat × Nat)
  | .const .w32 c => some (none, MNat 32 c)
  | .var .w32 ξ => some (some ξ, 0)
  | .app .w32 (.add .w32) [a, .const .w32 b] => do
      let (root, off) ← affineAddress a
      some (root, MNat 32 (off + b))
  | .app .w32 (.add .w32) [.const .w32 a, b] => do
      let (root, off) ← affineAddress b
      some (root, MNat 32 (off + a))
  | .app .w32 (.sub .w32) [a, .const .w32 b] => do
      let (root, off) ← affineAddress a
      some (root, MNat 32 (off + (1 <<< 32) - MNat 32 b))
  | _ => none

#guard affineAddress (.app .w32 (.add .w32) [Term.V32 4, Term.C32 14]) ==
  some (some 4, 14)
#guard affineAddress (.app .w32 (.add .w32) [Term.C32 14, Term.V32 4]) ==
  some (some 4, 14)
#guard affineAddress (.app .w32 (.add .w32)
  [Term.C32 14, .app .w32 (.add .w32) [Term.V32 4, Term.C32 2]]) ==
  some (some 4, 16)
#guard affineAddress (.app .w32 (.add .w32)
  [Term.C32 0xffffffff, .app .w32 (.add .w32) [Term.V32 4, Term.C32 2]]) ==
  some (some 4, 1)

/-- Word-only context load. Resolve the access before discarding an x0 destination. -/
def exprLOAD (Eg : ExprSet) (rs1 rd : regidx) (offset : Nat)
    (boundCtx : Option Term := none) : Option ExprSet := do
  if !guardEg Eg || offset % 4 != 0 || offset ≥ 24 then none
  else
    let source ← readReg Eg rs1
    let ctx ← boundCtx.orElse (fun _ => Eg.lookupEq (Reg.real32 10))
    if source.width != .w32 || ctx.width != .w32 ||
        affineAddress source != affineAddress ctx || (affineAddress source).isNone then
      none
    else
      let α ← ctxBaseAlpha Eg
      let t ← Eg.lookupEq (Reg.sw (α + offset / 4))
      some (assign rd t)

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
      let slot := Reg.sw ((1 <<< 32) + tag * (1 <<< 32) + address)
      if root.isNone && rs1 != sp && base != tsp && (Eg.lookupEq slot).isNone then none
      else some slot

def exprStackLOAD (Eg : ExprSet) (rs1 rd : regidx) (offset : Nat) : Option ExprSet := do
  if !guardEg Eg then none
  else
    let slot ← stackSlot Eg rs1 offset
    let t ← Eg.lookupEq slot
    if t.width != .w32 then none else some (assign rd t)

def exprWordLOAD (Eg : ExprSet) (rs1 rd : regidx) (offset : Nat)
    (boundCtx : Option Term := none) : Option ExprSet :=
  match exprStackLOAD Eg rs1 rd offset with
  | some Ei => some Ei
  | none => exprLOAD Eg rs1 rd offset boundCtx

/-- Packet identity is the fixed context slot namespace. Only a uniquely normalized
constant byte offset is admitted; symbolic offsets need a future binding rule. -/
def packetBinding (Eg : ExprSet) (rs1 : regidx) (offset width : Nat) : Option PacketAccess := do
  let α ← ctxBaseAlpha Eg
  let data ← Eg.lookupEq (Reg.sw α)
  let source ← readReg Eg rs1
  let (root, dataOff) ← affineAddress data
  let (sourceRoot, sourceOff) ← affineAddress source
  if root != sourceRoot then none
  else
    let o := MNat 32 (sourceOff + offset + (1 <<< 32) - dataOff)
    if o + width > (1 <<< 32) then none
    else
      -- Concrete pointers require a concrete interval, rather than treating every
      -- numerical address as a packet alias. Symbolic bounds remain a premise.
      let ending ← Eg.lookupEq (Reg.sw (α + 1))
      match affineAddress ending with
      | some (endRoot, endOff) =>
        if endRoot != root || endOff < dataOff || o + width > endOff - dataOff then none
        else some ⟨α, o, width, .little, some data⟩
      | none =>
        if root.isNone then none else some ⟨α, o, width, .little, some data⟩

def exprPacketLOAD (Eg : ExprSet) (rs1 rd : regidx) (offset width : Nat)
    (isUnsigned : Bool) : Option ExprSet := do
  if !guardEg Eg then none
  else
    let access ← packetBinding Eg rs1 offset width
    let result ← access.read Eg .w32 isUnsigned
    some (assign rd result.value)

/-- Resolve a subfield against the same canonical word used by aligned spills. -/
def stackAccess (Eg : ExprSet) (rs1 : regidx) (offset width : Nat) : Option CellAccess := do
  let base ← readReg Eg rs1
  let (_, off) ← affineAddress base
  let within := MNat 32 (off + offset) % 4
  if within + width > 4 then none
  else
    let slot ← stackSlot Eg rs1 (MNat 32 (offset + (1 <<< 32) - within))
    some ⟨slot, 8 * within, 8 * width⟩

/-- Fixed context fields use the entry context binding, independently of mutable a0. -/
private def contextAccess (Eg : ExprSet) (rs1 : regidx) (offset width : Nat)
    (boundCtx : Option Term) : Option CellAccess := do
  let source ← readReg Eg rs1
  let ctx ← boundCtx.orElse (fun _ => Eg.lookupEq (Reg.real32 10))
  let (root, off) ← affineAddress source
  let (ctxRoot, ctxOff) ← affineAddress ctx
  let relative := MNat 32 (off + offset + (1 <<< 32) - ctxOff)
  let within := relative % 4
  if root != ctxRoot || relative ≥ 24 || within + width > 4 then none
  else
    let α ← ctxBaseAlpha Eg
    some ⟨Reg.sw (α + relative / 4), 8 * within, 8 * width⟩

/-- Exactly one lookup-result base plus concrete displacement. Other helper results,
numeric pointers and sums of symbolic bases do not establish a Map identity. -/
private def lookupAddress : Term → Option (Nat × Nat)
  | .app .w32 (.id .w32) [a] => lookupAddress a
  | .app .w32 (.externalResult event 0) [id, map, key] =>
      if eval (solve id) == some 1 && map.width == .w32 && key.width == .w32 then
        some (event, 0)
      else none
  | .app .w32 (.add .w32) [a, b] =>
      match lookupAddress a, eval (solve b) with
      | some (event, off), some displacement => some (event, MNat 32 (off + displacement))
      | _, _ => do
          let displacement ← eval (solve a)
          let (event, off) ← lookupAddress b
          some (event, MNat 32 (off + displacement))
  | .app .w32 (.sub .w32) [a, b] => do
      let (event, off) ← lookupAddress a
      let displacement ← eval (solve b)
      some (event, MNat 32 (off + (1 <<< 32) - MNat 32 displacement))
  | _ => none

/-- Resolve one event-local Map word. Word zero must retain its helper introduction.
Later untouched words use externalResult event (1 + wordBase / 4) [C32 1]; these
closed content terms remain opaque under eval. No ELF value size is inferred. -/
private def mapAccessInputs (Eg : ExprSet) (rs1 : regidx) (offset width : Nat)
    (needsOld : Bool) : Option (CellAccess × ExprSet) := do
  if !guardEg Eg || !(width == 1 || width == 2 || width == 4) then none
  else
    let source ← readReg Eg rs1
    let (event, displacement) ← lookupAddress (solve source)
    let first ← Eg.lookupEq (Reg.mapWord event 0)
    if first.width != .w32 then none
    else
      let relative := MNat 32 (displacement + offset)
      let within := relative % 4
      if within + width > 4 then none
      else
        let wordBase := relative - within
        let reg := Reg.mapWord event wordBase
        let access : CellAccess := ⟨reg, 8 * within, 8 * width⟩
        match Eg.lookupEq reg with
        | some old => if old.width != .w32 then none else some (access, .empty)
        | none =>
          if !needsOld then some (access, .empty)
          else if wordBase == 0 || !(Eg.forReg reg).isEmpty then none
          else
            let content := star .w32 (.externalResult event (1 + wordBase / 4)) [Term.C32 1]
            some (access, ExprSet.empty.insertEq reg content)

/-- Address resolution alone does not materialize missing content. -/
def mapAccess (Eg : ExprSet) (rs1 : regidx) (offset width : Nat) : Option CellAccess :=
  (mapAccessInputs Eg rs1 offset width false).map Prod.fst

def exprSizedLOADEffects (Eg : ExprSet) (rs1 rd : regidx) (offset width : Nat)
    (isUnsigned : Bool) (boundCtx : Option Term := none) : Option ExprEffect := do
  if !guardEg Eg || !(width == 1 || width == 2 || width == 4) then none
  else
    let cell := (stackAccess Eg rs1 offset width).orElse
      (fun _ => contextAccess Eg rs1 offset width boundCtx)
    match cell with
    | some a =>
      let value ← a.read Eg .w32 isUnsigned
      some ⟨.empty, assign rd value⟩
    | none =>
      match mapAccessInputs Eg rs1 offset width true with
      | some (access, inputs) =>
        let value ← access.read (updateExpr Eg inputs) .w32 isUnsigned
        some ⟨inputs, assign rd value⟩
      | none =>
        let access ← packetBinding Eg rs1 offset width
        let read ← access.read Eg .w32 isUnsigned
        some ⟨read.inputs, assign rd read.value⟩

def exprSizedLOAD (Eg : ExprSet) (rs1 rd : regidx) (offset width : Nat)
    (isUnsigned : Bool) (boundCtx : Option Term := none) : Option ExprSet := do
  let effect ← exprSizedLOADEffects Eg rs1 rd offset width isUnsigned boundCtx
  some effect.updates

def exprSTOREEffects (Eg : ExprSet) (rs1 rs2 : regidx) (offset width : Nat)
    : Option ExprEffect := do
  if !guardEg Eg || !(width == 1 || width == 2 || width == 4) then none
  else
    let value ← readReg Eg rs2
    if value.width != .w32 then none
    else match stackAccess Eg rs1 offset width with
    | some a =>
      let updates ← a.write Eg value
      some ⟨.empty, updates⟩
    | none =>
      match mapAccessInputs Eg rs1 offset width (width != 4) with
      | some (access, inputs) =>
        let updates ← access.write (updateExpr Eg inputs) value
        some ⟨inputs, updates⟩
      | none =>
        let access ← packetBinding Eg rs1 offset width
        let updates ← access.write Eg value
        some ⟨.empty, updates⟩

def exprSTORE (Eg : ExprSet) (rs1 rs2 : regidx) (offset width : Nat) : Option ExprSet := do
  let effect ← exprSTOREEffects Eg rs1 rs2 offset width
  some effect.updates

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

def expr (Eg : ExprSet) (i : Insn) (boundCtx : Option Term := none) : Option ExprSet :=
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
      exprSizedLOAD Eg rs1 rd (immI32 imm) width isUnsigned boundCtx
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
      exprSizedLOAD Eg (creg2reg_idx rs1) (creg2reg_idx rd) (uimm.toNat <<< 2) 4 true boundCtx
  | .C_LWSP (uimm, rd) =>
      if isX0 rd then none else exprStackLOAD Eg sp rd (uimm.toNat <<< 2)
  | .C_SW (uimm, rs1, rs2) =>
      exprSTORE Eg (creg2reg_idx rs1) (creg2reg_idx rs2) (uimm.toNat <<< 2) 4
  | .C_SWSP (uimm, rs2) => exprSTORE Eg sp rs2 (uimm.toNat <<< 2) 4
  | .C_EBREAK _ => exprReject

/-- Classify input observations separately from the instruction's actual writes. -/
def stepEffects (Eg : ExprSet) (i : Insn) (boundCtx : Option Term := none) : Option ExprEffect := do
  let effect ← match i with
    | .LOAD (imm, rs1, rd, unsigned, width) =>
      exprSizedLOADEffects Eg rs1 rd (immI32 imm) width unsigned boundCtx
    | .C_LW (imm, rs1, rd) =>
      exprSizedLOADEffects Eg (creg2reg_idx rs1) (creg2reg_idx rd) (imm.toNat <<< 2) 4 true boundCtx
    | .STORE (imm, rs2, rs1, width) =>
      exprSTOREEffects Eg rs1 rs2 (immI32 imm) width
    | .C_SW (imm, rs1, rs2) =>
      exprSTOREEffects Eg (creg2reg_idx rs1) (creg2reg_idx rs2) (imm.toNat <<< 2) 4
    | .C_SWSP (imm, rs2) => exprSTOREEffects Eg sp rs2 (imm.toNat <<< 2) 4
    | _ => do
      let updates ← expr Eg i boundCtx
      some (ExprEffect.mk .empty updates)
  if effect.validFor Eg then some effect else none

/-- Expansion transports both fresh input relations and local writes in one delta.
`expr` and `stepEffects.updates` retain the instruction-only assignment interface. -/
def step (Eg : ExprSet) (i : Insn) (boundCtx : Option Term := none) : Option ExprSet := do
  let effect ← stepEffects Eg i boundCtx
  some effect.delta

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

private def mapFieldsCheck : Bool := Id.run do
  let pointer := star .w32 (.externalResult 9 0) [Term.C32 1, Term.C32 42, Term.V32 0]
  let reg := Reg.mapWord 9 0
  let E := ExprSet.empty
    |>.insertEq (Reg.real32 8) (idStar .w32 pointer)
    |>.insertEq (Reg.real32 10) (Term.C32 5)
    |>.insertEq (Reg.real32 11) (Term.C32 0xaabbccdd)
    |>.insertEq reg (Term.C32 0x80ff7f01)
  let cases := [(0, 1, true, 1), (1, 1, false, 127),
    (2, 1, false, 0xffffffff), (3, 1, true, 128),
    (2, 2, true, 0x80ff), (2, 2, false, 0xffff80ff), (0, 4, true, 0x80ff7f01)]
  if !cases.all (fun (off, width, u, expected) =>
      match exprSizedLOADEffects E (.Regidx 8#5) (.Regidx 12#5) off width u with
      | some effect => effect.inputs.entries.isEmpty && effect.updates.entries.length == 1 &&
          effect.updates.lookupEq (Reg.real32 12) == some (Term.C32 expected)
      | none => false) then return false
  for (off, width, expected) in [(1, 1, 0x80ffdd01), (2, 2, 0xccdd7f01), (0, 4, 0xaabbccdd)] do
    let some writes := exprSTORE E (.Regidx 8#5) (.Regidx 11#5) off width | return false
    if writes.entries.length != 1 || writes.lookupEq reg != some (Term.C32 expected) then
      return false
    let saved := updateExpr E writes
    if !guardEg saved || saved.lookupEq (Reg.real32 10) != some (Term.C32 5) then return false
    let some read := exprSizedLOAD saved (.Regidx 8#5) (.Regidx 12#5) 0 4 true | return false
    if read.lookupEq (Reg.real32 12) != some (Term.C32 expected) then return false
  let alias := E.insertEq (Reg.real32 8)
    (subStar .w32 (addStar .w32 (Term.C32 3) (idStar .w32 pointer)) (Term.C32 1))
  return (mapAccess alias (.Regidx 8#5) 0 2).map (fun a => a.reg == reg && a.bitOffset == 16) ==
    some true

#guard mapFieldsCheck

private def mapLaterWordsCheck : Bool := Id.run do
  let pointer := star .w32 (.externalResult 9 0) [Term.C32 1, Term.C32 42, Term.V32 0]
  let first := Term.regVar 9 (Reg.real32 10)
  let second := star .w32 (.externalResult 9 2) [Term.C32 1]
  let reg := Reg.mapWord 9 4
  let E := ExprSet.empty
    |>.insertEq (Reg.real32 8) pointer
    |>.insertEq (Reg.real32 11) (Term.C32 0x80)
    |>.insertEq (Reg.mapWord 9 0) first
  let some read := stepEffects E (.LOAD (4#12, .Regidx 8#5, .Regidx 12#5, true, 4))
    | return false
  if !read.validFor E || read.inputs.lookupEq reg != some second ||
      read.inputs.entries.length != 1 || read.updates.entries.length != 1 ||
      read.updates.lookupEq (Reg.real32 12) != some second ||
      (eval second).isSome || solve second != second then return false
  let loaded := updateExpr E read.delta
  let alias := loaded.insertEq (Reg.real32 8)
    (subStar .w32 (addStar .w32 pointer (Term.C32 8)) (Term.C32 4))
  let some again := exprSizedLOADEffects alias (.Regidx 8#5) (.Regidx 13#5) 0 4 true
    | return false
  if !again.inputs.entries.isEmpty || again.updates.lookupEq (Reg.real32 13) != some second
    then return false
  let some byte := stepEffects E (.STORE (7#12, .Regidx 11#5, .Regidx 8#5, 1))
    | return false
  if !byte.validFor E || byte.inputs.lookupEq reg != some second ||
      byte.updates.entries.length != 1 then return false
  let written := updateExpr E byte.delta
  let some signed := exprSizedLOADEffects written (.Regidx 8#5) (.Regidx 14#5) 7 1 false
    | return false
  if !signed.inputs.entries.isEmpty || signed.updates.entries.length != 1 ||
      (signed.updates.lookupEq (Reg.real32 14)).bind eval != none then return false
  let expected := orStar 32 .w32
    (andStar 32 .w32 second (Term.C32 0x00ffffff)) (Term.C32 0x80000000)
  if written.lookupEq reg != some expected then return false
  let some full := exprSTOREEffects E (.Regidx 8#5) (.Regidx 11#5) 8 4 | return false
  if !full.inputs.entries.isEmpty || full.updates.lookupEq (Reg.mapWord 9 8) !=
      some (Term.C32 0x80) then return false
  let some zero := exprSizedLOADEffects E (.Regidx 8#5) zreg 4 4 true | return false
  if zero.inputs.lookupEq reg != some second || !zero.updates.entries.isEmpty then return false
  let constrained := E.insert ⟨reg, .ne, Term.C32 0⟩
  return written.lookupEq (Reg.mapWord 9 0) == some first &&
    (exprSizedLOADEffects constrained (.Regidx 8#5) zreg 4 4 true).isNone &&
    (exprSTOREEffects constrained (.Regidx 8#5) (.Regidx 11#5) 5 1).isNone &&
    (exprSizedLOADEffects { entries := E.entries.filter (fun e => e.reg != Reg.mapWord 9 0) }
      (.Regidx 8#5) zreg 4 4 true).isNone

#guard mapLaterWordsCheck

private def mapRejectsCheck : Bool :=
  let pointer := star .w32 (.externalResult 9 0) [Term.C32 1, Term.C32 42, Term.V32 0]
  let E := ExprSet.empty
    |>.insertEq (Reg.real32 8) pointer
    |>.insertEq (Reg.real32 11) (Term.C32 1)
    |>.insertEq (Reg.mapWord 9 0) (Term.C32 2)
  let bad := [Term.C32 0, Term.C32 0xffffffff, Term.V32 1,
    star .w32 (.externalResult 9 0) [Term.C32 5],
    star .w32 (.externalResult 9 1) [Term.C32 1, Term.C32 42, Term.V32 0],
    star .w32 (.externalResult 10 0) [Term.C32 1, Term.C32 42, Term.V32 0],
    addStar .w32 pointer (Term.V32 1), addStar .w32 pointer pointer]
  bad.all (fun t =>
    let E := E.insertEq (Reg.real32 8) t
    (exprSizedLOAD E (.Regidx 8#5) zreg 0 4 true).isNone &&
      (exprSTORE E (.Regidx 8#5) (.Regidx 11#5) 0 4).isNone) &&
    [(3, 2), (1, 4), (7, 2), (5, 4), (0xffffffff, 2), (4, 3)].all (fun (off, width) =>
      (exprSizedLOAD E (.Regidx 8#5) zreg off width true).isNone &&
      (exprSTORE E (.Regidx 8#5) (.Regidx 11#5) off width).isNone) &&
    (exprSTORE (ExprSet.empty.insertEq (Reg.real32 8) pointer)
      (.Regidx 8#5) zreg 0 4).isNone &&
    (mapAccess { entries := E.entries ++ E.entries } (.Regidx 8#5) 0 4).isNone

#guard mapRejectsCheck

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
