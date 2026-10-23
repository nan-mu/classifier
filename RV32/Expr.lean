import Core.Anchor
import Core.Virtual
import Core.MapLayout
import RV32.Insn
import Node.Path

namespace RV32
open Core Node

/-! Use Core.Reg: x0..x31 and PC as real32 alphas. -/

private def xReg (r : regidx) : Reg := Reg.real32 r.toNat
private def pcReg : Reg := Reg.real32 32
private def isX0 (r : regidx) : Bool := r.toNat == 0


def sextBits (srcBits : Nat) (v : Nat) : Nat :=
  M 32 (s srcBits (MNat srcBits v))

def immI32 (imm : BitVec 12) : Nat := sextBits 12 imm.toNat
def uimmU32 (imm : BitVec 20) : Nat := MNat 32 (imm.toNat <<< 12)
def cImm6 (imm : BitVec 6) : Nat := sextBits 6 imm.toNat
def cAddi4spnImm (nzimm : BitVec 8) : Nat := nzimm.toNat
def cAddi16spImm (imm : BitVec 6) : Nat := sextBits 10 (imm.toNat <<< 4)
def cLuiU (imm : BitVec 6) : Nat := M 32 (s 6 imm.toNat * Int.ofNat (1 <<< 12))

def readReg (Eg : List Expr) (r : regidx) : Option Term :=
  if isX0 r then some (Term.C32 0)
  else Eg.lookupEq (xReg r)

def readPC (Eg : List Expr) : Option Term := Eg.lookupEq pcReg

def checkX0 (Eg : List Expr) : Bool :=
  match Eg.lookupEq (xReg zreg) with
  | none => true
  | some t =>
      match eval (solve t) with
      | some 0 => true
      | _ => false

def assign (rd : regidx) (t : Term) : List Expr :=
  if isX0 rd then Expr.nil
  else Expr.nil.insertEq (xReg rd) (solve t)

def guardEg (Eg : List Expr) : Bool :=
  Eg.keysUnique && Eg.wellTyped && checkX0 Eg

def exprUTYPE (Eg : List Expr) (imm : BitVec 20) (rd : regidx) (op : uop) : Option (List Expr) :=
  if !guardEg Eg then none
  else
    let U := uimmU32 imm
    match op with
    | .LUI => some (assign rd (Term.C32 U))
    | .AUIPC =>
        match readPC Eg with
        | none => none
        | some tπ => some (assign rd (addStar .w32 tπ (Term.C32 U)))

def exprITYPE (Eg : List Expr) (imm : BitVec 12) (rs1 rd : regidx) (op : iop) : Option (List Expr) :=
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

def exprSHIFTIOP (Eg : List Expr) (shamt : BitVec 6) (rs1 rd : regidx) (op : sop) : Option (List Expr) :=
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

def exprRTYPE (Eg : List Expr) (rs2 rs1 rd : regidx) (op : rop) : Option (List Expr) :=
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

def exprMUL (Eg : List Expr) (rs2 rs1 rd : regidx) (mop : mul_op) : Option (List Expr) :=
  if !guardEg Eg then none
  else
    match readReg Eg rs1, readReg Eg rs2 with
    | some ta, some tb =>
        let t :=
          match mop.result_part, mop.signed_rs1, mop.signed_rs2 with
          | .Low, _, _ => mulloStar .w32 ta tb
          | .High, .Signed, .Signed => star .w32 (.mulh .w32) [ta, tb]
          | .High, .Signed, .Unsigned => star .w32 (.mulhsu .w32) [ta, tb]
          | .High, .Unsigned, .Unsigned => star .w32 (.mulhu .w32) [ta, tb]
          | .High, .Unsigned, .Signed => star .w32 (.mulhsu .w32) [tb, ta]
        some (assign rd t)
    | _, _ => none

def exprDIV (Eg : List Expr) (rs2 rs1 rd : regidx) (isUnsigned : Bool) : Option (List Expr) :=
  if !guardEg Eg then none
  else
    match readReg Eg rs1, readReg Eg rs2 with
    | some ta, some tb =>
        let op := if isUnsigned then Op.udiv .w32 ((1 <<< 32) - 1)
          else Op.sdiv .w32 ((1 <<< 32) - 1)
        some (assign rd (star .w32 op [ta, tb]))
    | _, _ => none

def exprREM (Eg : List Expr) (rs2 rs1 rd : regidx) (isUnsigned : Bool) : Option (List Expr) :=
  if !guardEg Eg then none
  else
    match readReg Eg rs1, readReg Eg rs2 with
    | some ta, some tb =>
        let op := if isUnsigned then Op.urem .w32 else Op.srem .w32
        some (assign rd (star .w32 op [ta, tb]))
    | _, _ => none

def exprJAL (Eg : List Expr) (rd : regidx) : Option (List Expr) :=
  if !guardEg Eg then none
  else if isX0 rd then some Expr.nil
  else
    match readPC Eg with
    | none => none
    | some tπ => some (assign rd (addStar .w32 tπ (Term.C32 4)))

def exprJALR (Eg : List Expr) (rs1 rd : regidx) : Option (List Expr) :=
  if !guardEg Eg then none
  else
    match readReg Eg rs1 with
    | none => none
    | some _ =>
        if isX0 rd then some Expr.nil
        else
          match readPC Eg with
          | none => none
          | some tπ => some (assign rd (addStar .w32 tπ (Term.C32 4)))

private structure SlotAt where
  slot : BitSlot
  start : Nat
  bits : Nat
  deriving Inhabited, Repr

private def readSlot (mem : Mem) (slot : BitSlot) (start bits : Nat) : Option Term :=
  match mem.read slot start (start + bits) with
  | .ok tile => tile.project.toOption
  | .error _ => none

private def writeSlot (slot : BitSlot) (start bits : Nat) (source : Term) : Option MemWrite :=
  match Tile.ofTerm source bits with
  | .ok tile => some ⟨slot, start, tile⟩
  | .error _ => none

/-- All six context fields are defined 32-bit values. Field 0 is data. -/
private def contextReady (mem : Mem) : Bool :=
  (List.range 6).all fun j => (readSlot mem (.context j) 0 32).isSome

/-- One symbolic root with coefficient one, plus a concrete modular displacement. -/
private def affineAddress : Term → Option (Option Nat × Nat)
  | .const .w32 c => some (none, MNat 32 c)
  | .var .w32 ξ => some (some ξ, 0)
  | .app .w32 (.id .w32) [a]
  | .app .w32 (.low 32 32) [a]
  | .app .w32 (.zext 32 .w32 32) [a]
  | .app .w32 (.sext 32 .w32 32) [a] => affineAddress a
  | .app .w32 (.add .w32) [a, b] => do
      let (ra, oa) ← affineAddress a
      let (rb, ob) ← affineAddress b
      if ra.isSome && rb.isSome then none
      else some (ra.orElse (fun _ => rb), MNat 32 (oa + ob))
  | .app .w32 (.sub .w32) [a, b] => do
      let (root, off) ← affineAddress a
      let displacement ← eval b
      some (root, MNat 32 (off + (1 <<< 32) - MNat 32 displacement))
  | t => do
      if t.width != .w32 then none
      else
        let c ← eval t
        some (none, MNat 32 c)

#guard affineAddress (.app .w32 (.id .w32)
  [.app .w32 (.add .w32) [Term.V32 0, Term.C32 0xfffffff0]]) == some (some 0, 0xfffffff0)
#guard affineAddress (.app .w32 (.add .w32)
  [.app .w32 (.id .w32) [Term.V32 4], Term.C32 2]) == some (some 4, 2)
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
def exprLOAD (mem : Mem) (Eg : List Expr) (rs1 rd : regidx) (offset : Nat)
    (boundCtx : Option Term := none) : Option (List Expr) := do
  if !guardEg Eg || offset % 4 != 0 || offset ≥ 24 || !contextReady mem then none
  else
    let source ← readReg Eg rs1
    let ctx ← boundCtx.orElse (fun _ => Eg.lookupEq (Reg.real32 10))
    if source.width != .w32 || ctx.width != .w32 ||
        affineAddress source != affineAddress ctx || (affineAddress source).isNone then
      none
    else
      let t ← readSlot mem (.context (offset / 4)) 0 32
      some (assign rd t)

/-- SP and its affine aliases name one stack. The address is a byte offset.
A concrete pointer that is not an SP alias may only touch bytes already stored. -/
private def stackByte (mem : Mem) (Eg : List Expr) (base : Term) (offset width : Nat) :
    Option Nat := do
  let tsp ← readReg Eg sp
  let (root, off) ← affineAddress base
  let (spRoot, _) ← affineAddress tsp
  if root != spRoot || !(width == 1 || width == 2 || width == 4) then none
  else
    let address := MNat 32 (off + offset)
    if address % width != 0 then none
    else if root.isNone && affineAddress base != affineAddress tsp then
      let _ ← readSlot mem .stack (address * 8) (8 * width)
      some address
    else some address

def stackSlot (mem : Mem) (Eg : List Expr) (rs1 : regidx) (offset : Nat) : Option Nat := do
  let base ← readReg Eg rs1
  stackByte mem Eg base offset 4

def exprStackLOAD (mem : Mem) (Eg : List Expr) (rs1 rd : regidx) (offset : Nat) :
    Option (List Expr) := do
  if !guardEg Eg then none
  else
    let base ← readReg Eg rs1
    let address ← stackByte mem Eg base offset 4
    let t ← readSlot mem .stack (address * 8) 32
    some (assign rd t)

def exprWordLOAD (mem : Mem) (Eg : List Expr) (rs1 rd : regidx) (offset : Nat)
    (boundCtx : Option Term := none) : Option (List Expr) :=
  match exprStackLOAD mem Eg rs1 rd offset with
  | some Ei => some Ei
  | none => exprLOAD mem Eg rs1 rd offset boundCtx

/-- Byte offset of a numeric packet access. One packet slot, no resource id. -/
private def packetOffsetAt (mem : Mem) (source : Term) (offset width : Nat) : Option Nat := do
  if !contextReady mem || !(width == 1 || width == 2 || width == 4 || width == 8) then none
  else
    let data ← readSlot mem (.context 0) 0 32
    let (root, dataOff) ← affineAddress data
    let (sourceRoot, sourceOff) ← affineAddress source
    if root != sourceRoot then none
    else
      let o := MNat 32 (sourceOff + offset + (1 <<< 32) - dataOff)
      if o + width > (1 <<< 32) then none
      else
        let ending ← readSlot mem (.context 1) 0 32
        match affineAddress ending with
        | some (endRoot, endOff) =>
          if endRoot != root || endOff < dataOff || o + width > endOff - dataOff then none
          else some o
        | none =>
          if root.isNone then none else some o

/-- Fill missing packet bytes from the data root. Defined bytes stay. -/
private def fillPacket (mem : Mem) (o width : Nat) : Option (List MemWrite × Mem) := do
  let data ← readSlot mem (.context 0) 0 32
  let mut writes : List MemWrite := []
  let mut mem := mem
  for j in List.range width do
    let bit := (o + j) * 8
    match mem.read .packet bit (bit + 8) with
    | .ok _ => pure ()
    | .error (.gap _) =>
      if o + j ≥ 2 ^ data.width.bits then none
      else
        let address := addStar data.width data (Term.C data.width (o + j))
        let raw := star .w32 (.inputByte 0) [data, address]
        let w ← writeSlot .packet bit 8 raw
        mem ← (mem.apply [w]).toOption
        writes := writes ++ [w]
    | .error _ => none
  some (writes, mem)

/-- Symbolic offsets keep the packet-offset tree. Numeric offsets use memory. -/
def packetBindingAt (mem : Mem) (Eg : List Expr) (source : Term) (offset width : Nat)
    (preds : List Predicate := []) : Option PacketAccess := do
  if (packetOffsetAt mem source offset width).isSome || !Eg.keysUnique || !Eg.wellTyped ||
      ![1, 2, 4, 8].contains width || !contextReady mem then none
  else
    let data ← readSlot mem (.context 0) 0 32
    let ending ← readSlot mem (.context 1) 0 32
    let displacement ← packetDisplacement Eg data source
    let address := addStar .w32 source (Term.C32 offset)
    let (strict, checkedEnd) ← packetBoundWitness Eg data address ending width preds
    let compound : CompoundPacketReg :=
      ⟨0, displacement.plus (.c offset), width, 1, strict, 0, checkedEnd⟩
    pure ⟨0, 0, width, .little, some data, some compound⟩

def packetBinding (mem : Mem) (Eg : List Expr) (rs1 : regidx) (offset width : Nat)
    (preds : List Predicate := []) : Option PacketAccess := do
  let source ← readReg Eg rs1
  packetBindingAt mem Eg source offset width preds

private def stackAt (mem : Mem) (Eg : List Expr) (base : Term) (offset width : Nat) :
    Option SlotAt := do
  let address ← stackByte mem Eg base offset width
  some ⟨.stack, address * 8, 8 * width⟩

/-- A field access stays inside one context field. -/
private def contextAt (mem : Mem) (Eg : List Expr) (source : Term) (offset width : Nat)
    (boundCtx : Option Term) : Option SlotAt := do
  if !contextReady mem || !(width == 1 || width == 2 || width == 4) then none
  else
    let ctx ← boundCtx.orElse (fun _ => Eg.lookupEq (Reg.real32 10))
    let (root, off) ← affineAddress source
    let (ctxRoot, ctxOff) ← affineAddress ctx
    let relative := MNat 32 (off + offset + (1 <<< 32) - ctxOff)
    let within := relative % 4
    if root != ctxRoot || relative ≥ 24 || relative % width != 0 || within + width > 4 then none
    else some ⟨.context (relative / 4), 8 * within, 8 * width⟩

/-- Exactly one lookup-result base plus concrete displacement. Other helper results,
numeric pointers and sums of symbolic bases do not establish a Map identity. -/
def lookupAddress : Term → Option (Nat × Nat × Term)
  | .app .w32 (.id .w32) [a] => lookupAddress a
  | .app .w32 (.externalResult event 0) [id, map, key] =>
      if eval (solve id) == some 1 && map.width == .w32 && key.width == .w32 then
        some (event, 0, map)
      else none
  | .app .w32 (.add .w32) [a, b] =>
      match lookupAddress a, eval (solve b) with
      | some (event, off, map), some displacement =>
          some (event, MNat 32 (off + displacement), map)
      | _, _ => do
          let displacement ← eval (solve a)
          let (event, off, map) ← lookupAddress b
          some (event, MNat 32 (off + displacement), map)
  | .app .w32 (.sub .w32) [a, b] => do
      let (event, off, map) ← lookupAddress a
      let displacement ← eval (solve b)
      some (event, MNat 32 (off + (1 <<< 32) - MNat 32 displacement), map)
  | _ => none

theorem lookupAddress_const (w : Width) (n : Nat) :
    lookupAddress (.const w n) = none := rfl

theorem lookupAddress_ne_zero (source : Term) (event offset : Nat) (map : Term)
    (h : lookupAddress source = some (event, offset, map)) :
    source ≠ Term.C32 0 := by
  intro hz
  subst source
  cases h

/-- Map identity is the object id plus one key tile copied from the lookup. -/
private def mapSlot (Eg : List Expr) (preds : List Predicate) (source : Term) :
    Option (Nat × Nat × Term × BitSlot × Nat) :=
  if !guardEg Eg then none else
  match lookupAddress (solve source) with
  | none => none
  | some (event, displacement, mapTerm) =>
    match eval (solve mapTerm) with
    | none => none
    | some id =>
      match lookupKeyAt preds event with
      | none => none
      | some (saved, frozen) =>
        if saved != mapTerm || frozen.isEmpty then none else
        match Anchor.layout? Eg mapTerm with
        | none => none
        | some layout =>
          if frozen.length != layout.keySize then none else
          match (keyTile frozen).toOption with
          | none => none
          | some key => some (event, displacement, mapTerm, .map id key, layout.valueSize)

private def wordGap (mem : Mem) (slot : BitSlot) (wordBase : Nat) : Bool :=
  match mem.read slot (wordBase * 8) (wordBase * 8 + 32) with
  | .error (.gap _) => true
  | _ => false

/-- Word 0 must already be stored. A read of an untouched later word materializes
one 32-bit `externalResult`. A write names the interval and does not fill neighbors. -/
private def mapAt (mem : Mem) (Eg : List Expr) (preds : List Predicate)
    (source : Term) (offset width : Nat) (fill : Bool) : Option (SlotAt × List MemWrite) := do
  if !(width == 1 || width == 2 || width == 4) then none
  else
    let (event, displacement, _, slot, valueSize) ← mapSlot Eg preds source
    let _ ← readSlot mem slot 0 32
    let relative := MNat 32 (displacement + offset)
    if relative + width > valueSize || relative % width != 0 then none
    else
      let view : SlotAt := ⟨slot, relative * 8, 8 * width⟩
      if !fill then some (view, [])
      else match readSlot mem slot view.start view.bits with
        | some _ => some (view, [])
        | none =>
          let wordBase := relative - relative % 4
          let within := relative % 4
          if within + width > 4 || wordBase == 0 || !wordGap mem slot wordBase then none
          else
            let content := star .w32 (.externalResult event (1 + wordBase / 4)) [Term.C32 1]
            let w ← writeSlot slot (wordBase * 8) 32 content
            some (view, [w])

/-- Address resolution alone does not materialize missing content. -/
def mapAccess (mem : Mem) (Eg : List Expr) (preds : List Predicate)
    (rs1 : regidx) (offset width : Nat) : Option SlotAt := do
  let source ← readReg Eg rs1
  let (view, _) ← mapAt mem Eg preds source offset width false
  some view

private def placed (mem : Mem) (writes : List MemWrite) : Option Mem :=
  (mem.apply writes).toOption

private def loadTerm (mem : Mem) (view : SlotAt) (writes : List MemWrite)
    (isUnsigned : Bool) : Option Term := do
  let mem ← placed mem writes
  let field ← readSlot mem view.slot view.start view.bits
  some (fitBits view.bits .w32 (!isUnsigned) field)

def exprSizedLOADEffects (mem : Mem) (Eg : List Expr) (rs1 rd : regidx) (offset width : Nat)
    (isUnsigned : Bool) (boundCtx : Option Term := none)
    (preds : List Predicate := []) : Option ExprEffect := do
  if !guardEg Eg || !(width == 1 || width == 2 || width == 4) then none
  else
    let source ← readReg Eg rs1
    if let some view := stackAt mem Eg source offset width then
      let value ← loadTerm mem view [] isUnsigned
      some ⟨Expr.nil, assign rd value, []⟩
    else if let some view := contextAt mem Eg source offset width boundCtx then
      let value ← loadTerm mem view [] isUnsigned
      some ⟨Expr.nil, assign rd value, []⟩
    else if let some (view, writes) := mapAt mem Eg preds source offset width true then
      let value ← loadTerm mem view writes isUnsigned
      some ⟨Expr.nil, assign rd value, writes⟩
    else if let some o := packetOffsetAt mem source offset width then
      let (writes, _) ← fillPacket mem o width
      let value ← loadTerm mem ⟨.packet, o * 8, 8 * width⟩ writes isUnsigned
      -- The offset grammar names a materialized input byte by its packet alpha.
      let data ← readSlot mem (.context 0) 0 32
      let mut inputs := Expr.nil
      for j in List.range width do
        let reg := Reg.packet 0 (o + j)
        if (Eg.lookupEq reg).isNone then
          let address := addStar data.width data (Term.C data.width (o + j))
          let raw := star .w32 (.inputByte 0) [data, address]
          inputs := inputs.insertEq reg raw
      some ⟨inputs, assign rd value, writes⟩
    else
      let access ← packetBinding mem Eg rs1 offset width preds
      let read ← access.read Eg .w32 isUnsigned
      some ⟨read.inputs, assign rd read.value, []⟩

def exprSizedLOAD (mem : Mem) (Eg : List Expr) (rs1 rd : regidx) (offset width : Nat)
    (isUnsigned : Bool) (boundCtx : Option Term := none)
    (preds : List Predicate := []) : Option (List Expr) := do
  let effect ← exprSizedLOADEffects mem Eg rs1 rd offset width isUnsigned boundCtx preds
  some effect.updates

def exprPacketLOAD (mem : Mem) (Eg : List Expr) (rs1 rd : regidx) (offset width : Nat)
    (isUnsigned : Bool) (preds : List Predicate := []) : Option (List Expr) := do
  if !guardEg Eg || !(width == 1 || width == 2 || width == 4 || width == 8) then none
  else
    let source ← readReg Eg rs1
    if let some o := packetOffsetAt mem source offset width then
      let (writes, _) ← fillPacket mem o width
      let value ← loadTerm mem ⟨.packet, o * 8, 8 * width⟩ writes isUnsigned
      some (assign rd value)
    else
      let access ← packetBinding mem Eg rs1 offset width preds
      let read ← access.read Eg .w32 isUnsigned
      some (assign rd read.value)

/-- A buffer keeps one resource origin throughout its complete frozen range. -/
private inductive BufferOrigin where
  | stack | context | map | packet
  deriving BEq

private def byteOf (mem : Mem) (Eg : List Expr) (preds : List Predicate)
    (source : Term) (offset : Nat) (boundCtx : Option Term) :
    Option (BufferOrigin × Term × List MemWrite) := do
  let mut found : List (BufferOrigin × Term × List MemWrite) := []
  if let some view := stackAt mem Eg source offset 1 then
    if let some field := readSlot mem view.slot view.start view.bits then
      found := (.stack, fitBits 8 .w32 false field, []) :: found
  if let some ctx := boundCtx then
    if let some view := contextAt mem Eg source offset 1 (some ctx) then
      if let some field := readSlot mem view.slot view.start view.bits then
        found := (.context, fitBits 8 .w32 false field, []) :: found
  if let some (view, _) := mapAt mem Eg preds source offset 1 false then
    if let some field := readSlot mem view.slot view.start view.bits then
      found := (.map, fitBits 8 .w32 false field, []) :: found
  if let some o := packetOffsetAt mem source offset 1 then
    if let some (writes, filled) := fillPacket mem o 1 then
      if let some field := readSlot filled .packet (o * 8) 8 then
        found := (.packet, fitBits 8 .w32 false field, writes) :: found
  match found with
  | [one] => some one
  | _ => none

/-- Freeze only complete current bytes from one uniquely resolved resource.
Map bytes require the lookup key and an existing value. Context requires the
entry binding. Missing packet bytes materialize from the data root. -/
def readBufferBytes (mem : Mem) (Eg : List Expr) (addr : Term) (n : Nat)
    (boundCtx : Option Term := none) (preds : List Predicate := []) : Option (List Term) := do
  if !guardEg Eg || addr.width != .w32 then none
  else
    let source := solve addr
    if let some (_, displacement, map) := lookupAddress source then
      let layout ← Anchor.layout? Eg map
      if displacement + n > layout.valueSize || displacement + n > (1 <<< 32) then none
    if n == 0 then return []
    let mut bytes : List Term := []
    let mut origin : Option BufferOrigin := none
    let mut mem := mem
    for j in List.range n do
      let (which, byte, writes) ← byteOf mem Eg preds source j boundCtx
      if let some previous := origin then
        if which != previous then none
      origin := some which
      mem ← placed mem writes
      bytes := byte :: bytes
    some bytes.reverse

-- A copied SP alias keeps the identity wrapper (`ID_32(add32(sp,-16))`); freezing
-- key bytes still resolves the same stack word, as the just_tx lookup key requires.
#guard Id.run do
  let spTerm : Term := Term.V32 0
  let .ok mem := Mem.write .empty .stack (M 32 (-16) * 8) ⟨[.const 32 0x01020304]⟩ | return false
  let E := Expr.nil.insertEq (Reg.real32 2) spTerm
  let addr : Term := .app .w32 (.id .w32)
    [.app .w32 (.add .w32) [spTerm, Term.C32 (M 32 (-16))]]
  return readBufferBytes mem E addr 4 == some [Term.C32 4, Term.C32 3, Term.C32 2, Term.C32 1]

/-- Lookup event, element byte offset, and the pointer's Map term.
The Map term is the third component of `lookupAddress`. Callers that emit
MapWrite reject when it disagrees with the frozen-key observation Map. -/
def mapElementAccess (mem : Mem) (Eg : List Expr) (preds : List Predicate)
    (rs1 : regidx) (offset width : Nat) : Option (NodeId × Nat × Term) :=
  match readReg Eg rs1 with
  | none => none
  | some source =>
    match mapSlot Eg preds source with
    | none => none
    | some (event, displacement, mapTerm, _, _) =>
      match mapAt mem Eg preds source offset width false with
      | none => none
      | some _ => some (event, MNat 32 (displacement + offset), mapTerm)

private theorem mapSlot_address (Eg : List Expr) (preds : List Predicate) (source : Term)
    (event displacement : Nat) (mapTerm : Term) (slot : BitSlot) (valueSize : Nat)
    (h : mapSlot Eg preds source = some (event, displacement, mapTerm, slot, valueSize)) :
    lookupAddress (solve source) = some (event, displacement, mapTerm) := by
  simp only [mapSlot] at h
  split at h
  · cases h
  · split at h
    · cases h
    · rename_i looked _
      split at h
      · cases h
      · split at h
        · cases h
        · split at h
          · cases h
          · split at h
            · cases h
            · split at h
              · cases h
              · split at h
                · cases h
                · cases h
                  assumption

theorem mapElementAccess_preimage (mem : Mem) (Eg : List Expr) (preds : List Predicate)
    (rs1 : regidx) (offset width event elementOff : Nat) (map : Term)
    (h : mapElementAccess mem Eg preds rs1 offset width = some (event, elementOff, map)) :
    ∃ source displacement, readReg Eg rs1 = some source ∧
      lookupAddress (solve source) = some (event, displacement, map) := by
  revert h
  match hread : readReg Eg rs1 with
  | none =>
    intro h
    simp [mapElementAccess, hread] at h
  | some source =>
    intro h
    match hslot : mapSlot Eg preds source with
    | none => simp [mapElementAccess, hread, hslot] at h
    | some (e, displacement, m, slot, valueSize) =>
      match hmap : mapAt mem Eg preds source offset width false with
      | none => simp [mapElementAccess, hread, hslot, hmap] at h
      | some _ =>
        simp [mapElementAccess, hread, hslot, hmap] at h
        rcases h with ⟨rfl, _, rfl⟩
        exact ⟨source, displacement, rfl,
          mapSlot_address Eg preds source e displacement m slot valueSize hslot⟩

/-- Stack, map, and numeric packet stores are memory writes. A symbolic packet
store still records one expression per byte. -/
def exprSTOREEffects (mem : Mem) (Eg : List Expr) (rs1 rs2 : regidx) (offset width : Nat)
    (preds : List Predicate := []) : Option ExprEffect := do
  if !guardEg Eg || !(width == 1 || width == 2 || width == 4) then none
  else
    let value ← readReg Eg rs2
    if value.width != .w32 then none
    else
      let source ← readReg Eg rs1
      if let some view := stackAt mem Eg source offset width then
        let w ← writeSlot view.slot view.start view.bits value
        some ⟨Expr.nil, Expr.nil, [w]⟩
      else if let some (view, _) := mapAt mem Eg preds source offset width false then
        let w ← writeSlot view.slot view.start view.bits value
        some ⟨Expr.nil, Expr.nil, [w]⟩
      else if let some o := packetOffsetAt mem source offset width then
        let w ← writeSlot .packet (o * 8) (8 * width) value
        some ⟨Expr.nil, Expr.nil, [w]⟩
      else
        let access ← packetBinding mem Eg rs1 offset width preds
        let updates ← access.write Eg value
        some ⟨Expr.nil, updates, []⟩

def exprSTORE (mem : Mem) (Eg : List Expr) (rs1 rs2 : regidx) (offset width : Nat)
    (preds : List Predicate := []) : Option (List Expr) := do
  let effect ← exprSTOREEffects mem Eg rs1 rs2 offset width preds
  some effect.updates

def exprEmpty (Eg : List Expr) : Option (List Expr) := if guardEg Eg then some Expr.nil else none
def exprReject : Option (List Expr) := none

def exprC_ADDI4SPN (Eg : List Expr) (rdc : cregidx) (nzimm : BitVec 8) : Option (List Expr) :=
  if !guardEg Eg then none
  else if nzimm.toNat == 0 then none
  else
    match readReg Eg sp with
    | none => none
    | some tsp =>
        some (assign (creg2reg_idx rdc) (addStar .w32 tsp (Term.C32 (cAddi4spnImm nzimm))))

def exprC_ADDI (Eg : List Expr) (imm : BitVec 6) (rsd : regidx) : Option (List Expr) :=
  if !guardEg Eg then none
  else if isX0 rsd then some Expr.nil
  else
    match readReg Eg rsd with
    | none => none
    | some td => some (assign rsd (addStar .w32 td (Term.C32 (cImm6 imm))))

def exprC_LI (Eg : List Expr) (imm : BitVec 6) (rd : regidx) : Option (List Expr) :=
  if !guardEg Eg then none
  else some (assign rd (Term.C32 (cImm6 imm)))

def exprC_ADDI16SP (Eg : List Expr) (imm : BitVec 6) : Option (List Expr) :=
  if !guardEg Eg then none
  else if imm.toNat == 0 then none
  else
    match readReg Eg sp with
    | none => none
    | some tsp => some (assign sp (addStar .w32 tsp (Term.C32 (cAddi16spImm imm))))

def exprC_LUI (Eg : List Expr) (imm : BitVec 6) (rd : regidx) : Option (List Expr) :=
  if !guardEg Eg then none
  else if isX0 rd || rd.toNat == 2 then none
  else if imm.toNat == 0 then none
  else some (assign rd (Term.C32 (cLuiU imm)))

def exprC_shift (Eg : List Expr) (shamt : BitVec 6) (rsd : cregidx) (op : sop) : Option (List Expr) :=
  if !guardEg Eg then none
  else if shamt.toNat == 0 then none
  else
    let r := creg2reg_idx rsd
    exprSHIFTIOP Eg shamt r r op

def exprC_SLLI (Eg : List Expr) (shamt : BitVec 6) (rsd : regidx) : Option (List Expr) :=
  if !guardEg Eg then none
  else if isX0 rsd then some Expr.nil
  else if shamt.toNat == 0 then some Expr.nil
  else exprSHIFTIOP Eg shamt rsd rsd .SLLI

def exprC_ANDI (Eg : List Expr) (imm : BitVec 6) (rsd : cregidx) : Option (List Expr) :=
  if !guardEg Eg then none
  else
    let r := creg2reg_idx rsd
    match readReg Eg r with
    | none => none
    | some td => some (assign r (andStar 32 .w32 td (Term.C32 (cImm6 imm))))

def exprC_binary (Eg : List Expr) (rsd rs2 : cregidx) (op : rop) : Option (List Expr) :=
  exprRTYPE Eg (creg2reg_idx rs2) (creg2reg_idx rsd) (creg2reg_idx rsd) op

def exprC_MV (Eg : List Expr) (rd rs2 : regidx) : Option (List Expr) :=
  if !guardEg Eg then none
  else if isX0 rd then some Expr.nil
  else if isX0 rs2 then some (assign rd (Term.C32 0))
  else
    match readReg Eg rs2 with
    | none => none
    | some tb => some (assign rd (idStar .w32 tb))

def exprC_ADD (Eg : List Expr) (rsd rs2 : regidx) : Option (List Expr) :=
  if !guardEg Eg then none
  else if isX0 rsd then some Expr.nil
  else exprRTYPE Eg rs2 rsd rsd .ADD

def exprC_JAL (Eg : List Expr) : Option (List Expr) :=
  if !guardEg Eg then none
  else
    match readPC Eg with
    | none => none
    | some tπ => some (assign ra (addStar .w32 tπ (Term.C32 2)))

def exprC_JALR (Eg : List Expr) (rs1 : regidx) : Option (List Expr) :=
  if !guardEg Eg then none
  else if isX0 rs1 then none
  else
    match readReg Eg rs1 with
    | none => none
    | some _ =>
        match readPC Eg with
        | none => none
        | some tπ => some (assign ra (addStar .w32 tπ (Term.C32 2)))

def expr (Eg : List Expr) (i : Insn) (boundCtx : Option Term := none)
    (mem : Mem := .empty) (preds : List Predicate := []) : Option (List Expr) :=
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
      exprSizedLOAD mem Eg rs1 rd (immI32 imm) width isUnsigned boundCtx preds
  | .STORE (imm, rs2, rs1, width) =>
      exprSTORE mem Eg rs1 rs2 (immI32 imm) width preds
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
      exprSizedLOAD mem Eg (creg2reg_idx rs1) (creg2reg_idx rd) (uimm.toNat <<< 2) 4 true boundCtx preds
  | .C_LWSP (uimm, rd) =>
      if isX0 rd then none else exprStackLOAD mem Eg sp rd (uimm.toNat <<< 2)
  | .C_SW (uimm, rs1, rs2) =>
      exprSTORE mem Eg (creg2reg_idx rs1) (creg2reg_idx rs2) (uimm.toNat <<< 2) 4 preds
  | .C_SWSP (uimm, rs2) => exprSTORE mem Eg sp rs2 (uimm.toNat <<< 2) 4 preds
  | .C_EBREAK _ => exprReject

/-- Classify input observations separately from the instruction's actual writes. -/
def stepEffects (Eg : List Expr) (i : Insn) (boundCtx : Option Term := none)
    (preds : List Predicate := []) (mem : Mem := .empty) : Option ExprEffect := do
  let effect ← match i with
    | .LOAD (imm, rs1, rd, unsigned, width) =>
      exprSizedLOADEffects mem Eg rs1 rd (immI32 imm) width unsigned boundCtx preds
    | .C_LW (imm, rs1, rd) =>
      exprSizedLOADEffects mem Eg (creg2reg_idx rs1) (creg2reg_idx rd)
        (imm.toNat <<< 2) 4 true boundCtx preds
    | .STORE (imm, rs2, rs1, width) =>
      exprSTOREEffects mem Eg rs1 rs2 (immI32 imm) width preds
    | .C_SW (imm, rs1, rs2) =>
      exprSTOREEffects mem Eg (creg2reg_idx rs1) (creg2reg_idx rs2) (imm.toNat <<< 2) 4 preds
    | .C_SWSP (imm, rs2) => exprSTOREEffects mem Eg sp rs2 (imm.toNat <<< 2) 4 preds
    | _ => do
      let updates ← expr Eg i boundCtx mem preds
      some (ExprEffect.mk Expr.nil updates [])
  if effect.validFor Eg then some effect else none

/-- Expansion transports both fresh input relations and local writes in one delta.
`expr` and `stepEffects.updates` retain the instruction-only assignment interface. -/
def step (Eg : List Expr) (i : Insn) (boundCtx : Option Term := none)
    (preds : List Predicate := []) (mem : Mem := .empty) : Option (List Expr) := do
  let effect ← stepEffects Eg i boundCtx preds mem
  some effect.delta

-- ADDI replaces x1 locally; the unrelated x2 must not appear in the result.
#guard
  (let Eg := Expr.nil
      |>.insertEq (Reg.real32 1) (Term.C32 10)
      |>.insertEq (Reg.real32 2) (Term.C32 20)
   match step Eg (.ITYPE (1#12, .Regidx 1#5, .Regidx 1#5, .ADDI)) with
   | some Ei =>
       match Ei with
       | [⟨r, rel, .const w c⟩] =>
           r == Reg.real32 1 && rel == .eq && w == .w32 && c == 11
       | _ => false
   | none => false)

-- A successful empty local result stays empty even when Eg is nonempty.
#guard
  (match step (Expr.nil.insertEq (Reg.real32 2) (Term.C32 20)) (.C_NOP 0#6) with
   | some Ei => Ei.isEmpty
   | none => false)

private def memTerm (mem : Mem) (slot : BitSlot) (start bits : Nat) : Option Term :=
  match mem.read slot start (start + bits) with
  | .ok tile => tile.project.toOption
  | .error _ => none

private def applyEffect (mem : Mem) (Eg : List Expr) (preds : List Predicate)
    (effect : ExprEffect) : Option (List Expr × Mem) :=
  match applyLocal ⟨Eg, preds, mem⟩ effect.delta [] effect.writes with
  | .ok σ => some (σ.exprs, σ.mem)
  | .error _ => none

/-- Spill/reload uses the address, not the changing SP expression or register name. -/
private def stackRoundTripCheck : Bool := Id.run do
  let .ok mem := Mem.write .empty .stack 0 ⟨[.const 32 99]⟩ | return false
  let adjusted := Expr.nil
    |>.insertEq (Reg.real32 2) (addStar .w32 (Term.V32 0) (Term.C32 (M 32 (-16))))
    |>.insertEq (Reg.real32 8) (Term.V32 40)
  let some spill := stepEffects adjusted (.C_SWSP (3#6, .Regidx 8#5)) (mem := mem) | return false
  let some (_, savedMem) := applyEffect mem adjusted [] spill | return false
  let aliasE := adjusted.insertEq (Reg.real32 9)
    (addStar .w32 (Term.V32 0) (Term.C32 (M 32 (-4))))
  let some loadAlias := step aliasE (.C_LW (0#5, .Cregidx 1#3, .Cregidx 2#3)) (mem := savedMem)
    | return false
  let some reload := step adjusted (.C_LWSP (3#6, .Regidx 10#5)) (mem := savedMem) | return false
  let some overwrite := stepEffects adjusted (.STORE (12#12, zreg, sp, 4)) (mem := savedMem)
    | return false
  let some (_, overMem) := applyEffect savedMem adjusted [] overwrite | return false
  let some address := stackSlot savedMem adjusted sp 12 | return false
  return loadAlias.lookupEq (Reg.real32 10) == some (Term.V32 40) &&
    reload.lookupEq (Reg.real32 10) == some (Term.V32 40) &&
    memTerm overMem .stack 0 32 == some (Term.C32 99) &&
    (exprStackLOAD mem adjusted sp (.Regidx 10#5) 12).isNone &&
    (step adjusted (.C_LWSP (3#6, zreg)) (mem := savedMem)).isNone &&
    (exprSTORE mem adjusted sp (.Regidx 8#5) 2 4).isNone &&
    memTerm overMem .stack (address * 8) 32 == some (Term.C32 0)

#guard stackRoundTripCheck

/-- Signed/unsigned subword loads retain the byte position and RV32 extension. -/
private def narrowStackLoadsCheck : String := Id.run do
  let E := Expr.nil.insertEq (Reg.real32 2) (Term.C32 0x3000)
  if (exprSTORE .empty E sp (.Regidx 8#5) 0 4).isSome then return "missing source stored"
  let E := E.insertEq (Reg.real32 8) (Term.C32 0x80ff7f01)
  let some spill := exprSTOREEffects .empty E sp (.Regidx 8#5) 0 4 | return "spill miss"
  let some (_, mem) := applyEffect .empty E [] spill | return "apply miss"
  let cases := [(0, 1, true, 1), (1, 1, false, 127),
    (2, 1, false, 0xffffffff), (3, 1, true, 128),
    (2, 2, true, 0x80ff), (2, 2, false, 0xffff80ff)]
  let mut msg := ""
  for (off, width, u, expected) in cases do
    match step E (.LOAD (BitVec.ofNat 12 off, sp, .Regidx 10#5, u, width)) (mem := mem) with
    | none => msg := msg ++ s!"miss {off}/{width}/{u}\n"
    | some Ei =>
      if Ei.lookupEq (Reg.real32 10) != some (Term.C32 expected) then
        msg := msg ++ s!"{off}/{width}/{u} {reprStr (Ei.lookupEq (Reg.real32 10))}\n"
  if (exprSizedLOAD mem E sp (.Regidx 10#5) 3 2 true).isSome then
    msg := msg ++ "misaligned\n"
  return msg

#guard narrowStackLoadsCheck == ""

private def mapFieldsCheck : String := Id.run do
  let key := [Term.C32 9]
  let .ok keyT := keyTile key | return "key"
  let slot := BitSlot.map 42 keyT
  let .ok tile := Tile.ofTerm (Term.C32 0x80ff7f01) 32 | return "tile"
  let .ok mem := Mem.write .empty slot 0 tile | return "mem"
  let pointer := star .w32 (.externalResult 9 0) [Term.C32 1, Term.C32 42, Term.V32 0]
  let some E := Anchor.installMaps (Expr.nil
      |>.insertEq (Reg.real32 8) (idStar .w32 pointer)
      |>.insertEq (Reg.real32 10) (Term.C32 5)
      |>.insertEq (Reg.real32 11) (Term.C32 0xaabbccdd))
      [{ mapId := 42, keySize := 1, valueSize := 16 }] | return "layout"
  let preds : List Predicate := [.helper 9 .lookup ([Term.C32 42, Term.V32 0] ++ key)]
  let cases := [(0, 1, true, 1), (1, 1, false, 127),
    (2, 1, false, 0xffffffff), (3, 1, true, 128),
    (2, 2, true, 0x80ff), (2, 2, false, 0xffff80ff), (0, 4, true, 0x80ff7f01)]
  let mut msg := ""
  for (off, width, u, expected) in cases do
    match exprSizedLOADEffects mem E (.Regidx 8#5) (.Regidx 12#5) off width u (preds := preds) with
    | none => msg := msg ++ s!"load miss {off}/{width}\n"
    | some effect =>
      if !(effect.writes.isEmpty && effect.updates.length == 1 &&
          effect.updates.lookupEq (Reg.real32 12) == some (Term.C32 expected)) then
        msg := msg ++ s!"load {off}/{width} {reprStr effect.updates}\n"
  for (off, width, expected) in [(1, 1, 0x80ffdd01), (2, 2, 0xccdd7f01), (0, 4, 0xaabbccdd)] do
    match exprSTOREEffects mem E (.Regidx 8#5) (.Regidx 11#5) off width preds with
    | none => msg := msg ++ s!"store miss {off}/{width}\n"
    | some effect =>
      match applyEffect mem E preds effect with
      | none => msg := msg ++ s!"apply miss {off}/{width}\n"
      | some (saved, savedMem) =>
        if memTerm savedMem slot 0 32 != some (Term.C32 expected) then
          msg := msg ++ s!"mem {off}/{width} {reprStr (memTerm savedMem slot 0 32)}\n"
        match exprSizedLOAD savedMem saved (.Regidx 8#5) (.Regidx 12#5) 0 4 true (preds := preds) with
        | none => msg := msg ++ s!"reread miss {off}\n"
        | some read =>
          if read.lookupEq (Reg.real32 12) != some (Term.C32 expected) then
            msg := msg ++ s!"reread {off} {reprStr (read.lookupEq (Reg.real32 12))}\n"
        if !(guardEg saved && saved.lookupEq (Reg.real32 10) == some (Term.C32 5)) then
          msg := msg ++ s!"saved {off}\n"
  let aliasE := E.insertEq (Reg.real32 8)
    (subStar .w32 (addStar .w32 (Term.C32 3) (idStar .w32 pointer)) (Term.C32 1))
  if (mapAccess mem aliasE preds (.Regidx 8#5) 0 2).map
      (fun a => a.start == 16 && a.bits == 16) != some true then
    msg := msg ++ s!"alias {reprStr (mapAccess mem aliasE preds (.Regidx 8#5) 0 2)}\n"
  return msg

#guard mapFieldsCheck == ""

private def mapLaterWordsCheck : String := Id.run do
  let key := [Term.C32 9]
  let .ok keyT := keyTile key | return "key"
  let slot := BitSlot.map 42 keyT
  let pointer := star .w32 (.externalResult 9 0) [Term.C32 1, Term.C32 42, Term.V32 0]
  let first := Term.regVar 9 (Reg.real32 10)
  let second := star .w32 (.externalResult 9 2) [Term.C32 1]
  let .ok tile := Tile.ofTerm first 32 | return "tile"
  let .ok mem := Mem.write .empty slot 0 tile | return "mem"
  let some E := Anchor.installMaps (Expr.nil
      |>.insertEq (Reg.real32 8) pointer
      |>.insertEq (Reg.real32 11) (Term.C32 0x80))
      [{ mapId := 42, keySize := 1, valueSize := 16 }] | return "layout"
  let preds : List Predicate := [.helper 9 .lookup ([Term.C32 42, Term.V32 0] ++ key)]
  let mut msg := ""
  match stepEffects E (.LOAD (4#12, .Regidx 8#5, .Regidx 12#5, true, 4))
      (preds := preds) (mem := mem) with
  | none => return "read miss"
  | some read =>
    if read.updates.lookupEq (Reg.real32 12) != some second then
      msg := msg ++ s!"read {reprStr (read.updates.lookupEq (Reg.real32 12))} writes {read.writes.length}\n"
    match applyEffect mem E preds read with
    | none => return msg ++ "apply miss"
    | some (loaded, loadedMem) =>
      let aliasE := loaded.insertEq (Reg.real32 8)
        (subStar .w32 (addStar .w32 pointer (Term.C32 8)) (Term.C32 4))
      match exprSizedLOADEffects loadedMem aliasE (.Regidx 8#5) (.Regidx 13#5) 0 4 true
          (preds := preds) with
      | none => msg := msg ++ "again miss\n"
      | some again =>
        if !(again.writes.isEmpty && again.updates.lookupEq (Reg.real32 13) == some second) then
          msg := msg ++ s!"again {reprStr again.updates}\n"
      match stepEffects loaded (.STORE (7#12, .Regidx 11#5, .Regidx 8#5, 1))
          (preds := preds) (mem := loadedMem) with
      | none => msg := msg ++ "byte miss\n"
      | some byte =>
        match applyEffect loadedMem loaded preds byte with
        | none => msg := msg ++ "byte apply\n"
        | some (_, written) =>
          match exprSizedLOADEffects written loaded (.Regidx 8#5) (.Regidx 14#5) 7 1 false
              (preds := preds) with
          | none => msg := msg ++ "signed miss\n"
          | some signed =>
            if signed.updates.lookupEq (Reg.real32 14) != some (Term.C32 0xffffff80) then
              msg := msg ++ s!"signed {reprStr (signed.updates.lookupEq (Reg.real32 14))}\n"
          if memTerm written slot (7 * 8) 8 != some (Term.C32 0x80) then
            msg := msg ++ s!"byte8 {reprStr (memTerm written slot (7 * 8) 8)}\n"
          if memTerm written slot 32 24 != some (star .w32 (.low 24 32) [second]) then
            msg := msg ++ s!"low24 {reprStr (memTerm written slot 32 24)}\n"
          if memTerm written slot 0 32 != some first then
            msg := msg ++ s!"word0 {reprStr (memTerm written slot 0 32)}\n"
  match exprSTOREEffects mem E (.Regidx 8#5) (.Regidx 11#5) 8 4 preds with
  | none => msg := msg ++ "full miss\n"
  | some full =>
    match applyEffect mem E preds full with
    | none => msg := msg ++ "full apply\n"
    | some (_, fullMem) =>
      if memTerm fullMem slot 64 32 != some (Term.C32 0x80) then
        msg := msg ++ s!"full {reprStr (memTerm fullMem slot 64 32)}\n"
  match exprSizedLOADEffects mem E (.Regidx 8#5) zreg 4 4 true (preds := preds) with
  | none => msg := msg ++ "zero miss\n"
  | some zero =>
    if zero.writes.length != 1 || !zero.updates.isEmpty then
      msg := msg ++ s!"zero {zero.writes.length} {zero.updates.length}\n"
  if (exprSizedLOADEffects .empty E (.Regidx 8#5) zreg 4 4 true (preds := preds)).isSome then
    msg := msg ++ "empty load\n"
  if (exprSTOREEffects .empty E (.Regidx 8#5) (.Regidx 11#5) 5 1 preds).isSome then
    msg := msg ++ "empty store\n"
  return msg

#guard mapLaterWordsCheck == ""

private def mapRejectsCheck : Bool := Id.run do
  let key := [Term.C32 9]
  let .ok keyT := keyTile key | return false
  let .ok tile := Tile.ofTerm (Term.C32 2) 32 | return false
  let .ok mem := Mem.write .empty (.map 42 keyT) 0 tile | return false
  let pointer := star .w32 (.externalResult 9 0) [Term.C32 1, Term.C32 42, Term.V32 0]
  let some E := Anchor.installMaps (Expr.nil
      |>.insertEq (Reg.real32 8) pointer
      |>.insertEq (Reg.real32 11) (Term.C32 1))
      [{ mapId := 42, keySize := 1, valueSize := 16 }] | return false
  let preds : List Predicate := [.helper 9 .lookup ([Term.C32 42, Term.V32 0] ++ key)]
  let bad := [Term.C32 0, Term.C32 0xffffffff, Term.V32 1,
    star .w32 (.externalResult 9 0) [Term.C32 5],
    star .w32 (.externalResult 9 1) [Term.C32 1, Term.C32 42, Term.V32 0],
    star .w32 (.externalResult 10 0) [Term.C32 1, Term.C32 42, Term.V32 0],
    addStar .w32 pointer (Term.V32 1), addStar .w32 pointer pointer]
  if !bad.all (fun t =>
      let E := E.insertEq (Reg.real32 8) t
      (exprSizedLOAD mem E (.Regidx 8#5) zreg 0 4 true (preds := preds)).isNone &&
        (exprSTORE mem E (.Regidx 8#5) (.Regidx 11#5) 0 4 preds).isNone) then return false
  if ![(3, 2), (1, 4), (7, 2), (5, 4), (0xffffffff, 2), (4, 3)].all (fun (off, width) =>
      (exprSizedLOAD mem E (.Regidx 8#5) zreg off width true (preds := preds)).isNone &&
        (exprSTORE mem E (.Regidx 8#5) (.Regidx 11#5) off width preds).isNone) then
    return false
  return (exprSTORE .empty (Expr.nil.insertEq (Reg.real32 8) pointer)
      (.Regidx 8#5) zreg 0 4).isNone &&
    (mapAccess mem (E ++ E) preds (.Regidx 8#5) 0 4).isNone

#guard mapRejectsCheck

private def egEq (r : regidx) (v : Nat) : List Expr :=
  if r.toNat == 0 then Expr.nil
  else Expr.nil.insertEq (xReg r) (Term.C32 v)

private def resultRd (Ei : List Expr) (rd : regidx) : UInt32 :=
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
  let Eg := (egEq r1 rs1Val.toNat).override (egEq r2 rs2Val.toNat)
  let i : Insn := .RTYPE (r2, r1, rdi, .ADD)
  match expr Eg i with
  | none => 0xffffffff
  | some Ei => resultRd Ei rdi

@[export lean_rv32_value_auipc]
def exportExprAuipc (pcVal uimm20 rd : UInt32) : UInt32 :=
  let rdi : regidx := .Regidx (BitVec.ofNat 5 (rd.toNat &&& 31))
  let Eg := Expr.nil.insertEq pcReg (Term.C32 pcVal.toNat)
  let i : Insn := .UTYPE (BitVec.ofNat 20 (uimm20.toNat &&& 0xfffff), rdi, .AUIPC)
  match expr Eg i with
  | none => 0xffffffff
  | some Ei => resultRd Ei rdi

@[export lean_rv32_value_lui]
def exportExprLui (uimm20 rd : UInt32) : UInt32 :=
  let rdi : regidx := .Regidx (BitVec.ofNat 5 (rd.toNat &&& 31))
  let i : Insn := .UTYPE (BitVec.ofNat 20 (uimm20.toNat &&& 0xfffff), rdi, .LUI)
  match expr Expr.nil i with
  | none => 0xffffffff
  | some Ei => resultRd Ei rdi

@[export lean_rv32_value_div]
def exportExprDiv (rs1Val rs2Val : UInt32) : UInt32 :=
  let r1 : regidx := .Regidx 1#5
  let r2 : regidx := .Regidx 2#5
  let rd : regidx := .Regidx 3#5
  let Eg := (egEq r1 rs1Val.toNat).override (egEq r2 rs2Val.toNat)
  match expr Eg (.DIV (r2, r1, rd, false)) with
  | none => 0xffffffff
  | some Ei => resultRd Ei rd

@[export lean_rv32_value_ecall_rejects]
def exportEcallRejects (_unused : UInt32) : UInt32 :=
  match expr Expr.nil (.ECALL ()) with
  | none => 1
  | some _ => 0

@[export lean_rv32_expr_override_keeps]
def exportOverrideKeeps (_unused : UInt32) : UInt32 :=
  let Eg :=
    Expr.nil
      |>.insertEq (Reg.real32 1) (Term.C32 10)
      |>.insertEq (Reg.real32 2) (Term.C32 20)
  let Ei := Expr.nil.insertEq (Reg.real32 1) (Term.C32 11)
  let E := Eg.override Ei
  match E.lookupEq (Reg.real32 1), E.lookupEq (Reg.real32 2) with
  | some t1, some t2 =>
      match eval t1, eval t2 with
      | some 11, some 20 => 1
      | _, _ => 0
  | _, _ => 0

private def frozenResourceBuffersCheck : String := Id.run do
  let key := [Term.C32 1, Term.C32 2, Term.C32 3]
  let .ok keyT := keyTile key | return "key"
  let slot := BitSlot.map 42 keyT
  let data := Term.V32 4
  let fields := [data, addStar .w32 data (Term.C32 8), Term.C32 0x04030201,
    Term.C32 0x08070605, Term.C32 0, Term.C32 0]
  let mut built : Mem := .empty
  for (j, t) in (List.range 6).zip fields do
    let .ok tile := Tile.ofTerm t 32 | return "field"
    let .ok next := built.write (.context j) 0 tile | return "field write"
    built := next
  let .ok low := Tile.ofTerm (Term.C32 0x04030201) 32 | return "low"
  let .ok high := Tile.ofTerm (Term.C32 0x08070605) 32 | return "high"
  let .ok mem := built.write slot 0 low | return "map0"
  let .ok mem := mem.write slot 32 high | return "map1"
  let .ok mem := mem.write .stack 0 low | return "stack0"
  let .ok mem := mem.write .stack 32 high | return "stack1"
  let .ok mem := mem.write .packet 8 ⟨[.const 8 0xaa]⟩ | return "packet8"
  let .ok mem := mem.write .packet 16 ⟨[.const 8 0xbb]⟩ | return "packet16"
  let pointer := star .w32 (.externalResult 9 0) [Term.C32 1, Term.C32 42, Term.V32 7]
  let some E := Anchor.installMaps (Expr.nil
      |>.insertEq (Reg.real32 2) (Term.V32 0)
      |>.insertEq (Reg.real32 10) (Term.C32 3))
      [{ mapId := 42, keySize := 3, valueSize := 6 }] | return "layout"
  let preds : List Predicate := [.helper 9 .lookup ([Term.C32 42, Term.V32 7] ++ key)]
  let expected := some [Term.C32 4, Term.C32 5, Term.C32 6]
  if readBufferBytes mem E (addStar .w32 pointer (Term.C32 3)) 3 (preds := preds) != expected then
    return s!"map {reprStr (readBufferBytes mem E (addStar .w32 pointer (Term.C32 3)) 3 (preds := preds))}"
  let contextPtr := addStar .w32 (Term.V32 1) (Term.C32 11)
  if readBufferBytes mem E contextPtr 3 (some (Term.V32 1)) (preds := preds) != expected ||
      (readBufferBytes mem E contextPtr 3 (preds := preds)).isSome ||
      (readBufferBytes mem E (Term.C32 3) 1 (preds := preds)).isSome then return "context"
  let .ok missing := Mem.write .empty slot 0 low | return "missing"
  let mut missing := missing
  for (j, t) in (List.range 6).zip fields do
    let .ok tile := Tile.ofTerm t 32 | return "missing field"
    let .ok next := missing.write (.context j) 0 tile | return "missing write"
    missing := next
  if (readBufferBytes missing E (addStar .w32 pointer (Term.C32 3)) 3 (preds := preds)).isSome then
    return "missing read"
  let overlapE := E.insertEq (Reg.real32 2) data
  let .ok overlap := mem.write .stack 0 ⟨[.const 32 0x01020304]⟩ | return "overlap stack"
  let .ok overlap := overlap.write .packet 0 ⟨[.const 8 4]⟩ | return "overlap packet"
  if (readBufferBytes overlap overlapE data 1 (preds := preds)).isSome ||
      (readBufferBytes mem E (addStar .w32 data (Term.C32 7)) 2 (preds := preds)).isSome then
    return "overlap"
  match readBufferBytes mem E data 1 (preds := preds) with
  | none => return "open none"
  | some openBytes =>
    match (PacketAccess.mk 0 0 1 .little (some data) none).read E .w32 true with
    | none => return s!"packet none {reprStr openBytes}"
    | some materialized =>
      if solve openBytes.head! != solve materialized.value then
        return s!"open {reprStr (solve openBytes.head!)} packet {reprStr (solve materialized.value)}"
      else return ""

#guard frozenResourceBuffersCheck == ""

private def mNumericBoundariesCheck : Bool :=
  let r1 : regidx := .Regidx 8#5
  let r2 : regidx := .Regidx 9#5
  let rd : regidx := .Regidx 10#5
  let cases : List (Bool × Bool × Nat × Nat × Nat) := [
    (false, false, 0x80000000, 0xffffffff, 0x80000000),
    (true, false, 0x80000000, 0xffffffff, 0),
    (false, false, 0xfffffff9, 3, 0xfffffffe),
    (true, false, 0xfffffff9, 3, 0xffffffff),
    (false, false, 7, 0, 0xffffffff),
    (false, true, 7, 0, 0xffffffff),
    (true, false, 0xfffffff9, 0, 0xfffffff9),
    (true, true, 0xfffffff9, 0, 0xfffffff9)]
  cases.all fun (remainder, unsigned, a, b, expected) =>
    let E := Expr.nil
      |>.insertEq (Reg.real32 8) (Term.C32 a)
      |>.insertEq (Reg.real32 9) (Term.C32 b)
    let result := if remainder then exprREM E r2 r1 rd unsigned
      else exprDIV E r2 r1 rd unsigned
    match result with
    | some result => result.lookupEq (Reg.real32 10) == some (Term.C32 expected)
    | none => false

#guard mNumericBoundariesCheck

end RV32
