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
  else readInterval Eg (xReg r)

def readPC (Eg : List Expr) : Option Term := readInterval Eg pcReg

def checkX0 (Eg : List Expr) : Bool :=
  match Eg.lookupEq (xReg zreg) with
  | none => true
  | some t =>
      match eval (solve t) with
      | some 0 => true
      | _ => false

def assign (rd : regidx) (t : Term) : List Expr :=
  if isX0 rd then Expr.nil
  else (writeUpdates Expr.nil (xReg rd) t).getD Expr.nil

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

/-- Word-only context load. The six xdp_md fields are context intervals. -/
def exprLOAD (Eg : List Expr) (rs1 rd : regidx) (offset : Nat)
    (boundCtx : Option Term := none) : Option (List Expr) := do
  if !guardEg Eg || offset % 4 != 0 || offset ≥ 24 || !contextReady Eg then none
  else
    let source ← readReg Eg rs1
    let ctx ← boundCtx.orElse (fun _ => readReg Eg (.Regidx 10#5))
    if source.width != .w32 || ctx.width != .w32 ||
        affineAddress source != affineAddress ctx || (affineAddress source).isNone then
      none
    else
      let field ← ContextField.ofXdp (offset / 4)
      let t ← readInterval Eg (.context field 0 32)
      some (assign rd t)

/-- SP and its affine aliases name one stack. The address is a byte offset.
A concrete pointer that is not an SP alias may only touch bytes already stored. -/
private def stackAddress (Eg : List Expr) (base : Term) (offset width : Nat) : Option Nat := do
  let tsp ← readReg Eg sp
  let (root, off) ← affineAddress base
  let (spRoot, _) ← affineAddress tsp
  if root != spRoot || !(width == 1 || width == 2 || width == 4) then none
  else
    let address := MNat 32 (off + offset)
    if address % width != 0 then none
    else if root.isNone && affineAddress base != affineAddress tsp then
      let _ ← readInterval Eg (.stack (address * 8) (address * 8 + 8 * width))
      some address
    else some address

private def stackReg (Eg : List Expr) (base : Term) (offset width : Nat) : Option Reg := do
  let address ← stackAddress Eg base offset width
  some (.stack (address * 8) (address * 8 + 8 * width))

def stackSlot (Eg : List Expr) (rs1 : regidx) (offset : Nat) : Option Nat := do
  let base ← readReg Eg rs1
  stackAddress Eg base offset 4

def exprStackLOAD (Eg : List Expr) (rs1 rd : regidx) (offset : Nat) : Option (List Expr) := do
  if !guardEg Eg then none
  else
    let base ← readReg Eg rs1
    let reg ← stackReg Eg base offset 4
    let t ← CellAccess.read ⟨reg⟩ Eg .w32 true
    some (assign rd t)

/-- Byte offset of a numeric packet access. One packet, no resource id. -/
private def packetOffsetAt (Eg : List Expr) (source : Term) (offset width : Nat) : Option Nat := do
  if !contextReady Eg || !(width == 1 || width == 2 || width == 4 || width == 8) then none
  else
    let data ← contextValue Eg .data
    let (root, dataOff) ← affineAddress data
    let (sourceRoot, sourceOff) ← affineAddress source
    if root != sourceRoot then none
    else
      let o := MNat 32 (sourceOff + offset + (1 <<< 32) - dataOff)
      if o + width > (1 <<< 32) then none
      else
        let ending ← contextValue Eg .dataEnd
        match affineAddress ending with
        | some (endRoot, endOff) =>
          if endRoot != root || endOff < dataOff || o + width > endOff - dataOff then none
          else some o
        | none =>
          if root.isNone then none else some o

/-- Symbolic offsets keep the packet-offset tree and create no packet register. -/
def packetBindingAt (Eg : List Expr) (source : Term) (offset width : Nat)
    (preds : List Predicate := []) : Option PacketAccess := do
  if (packetOffsetAt Eg source offset width).isSome || !Eg.keysUnique || !Eg.wellTyped ||
      ![1, 2, 4, 8].contains width || !contextReady Eg then none
  else
    let data ← contextValue Eg .data
    let ending ← contextValue Eg .dataEnd
    let displacement ← packetDisplacement Eg data source
    let address := addStar .w32 source (Term.C32 offset)
    let _ ← packetBoundWitness Eg data address ending width preds
    some { displacement := displacement.plus (.c offset), bytes := width, inputBase := some data }

def packetBinding (Eg : List Expr) (rs1 : regidx) (offset width : Nat)
    (preds : List Predicate := []) : Option PacketAccess := do
  let source ← readReg Eg rs1
  packetBindingAt Eg source offset width preds

/-- A field access stays inside one context field. -/
private def contextReg (Eg : List Expr) (source : Term) (offset width : Nat)
    (boundCtx : Option Term) : Option Reg := do
  if !contextReady Eg || !(width == 1 || width == 2 || width == 4) then none
  else
    let ctx ← boundCtx.orElse (fun _ => readReg Eg (.Regidx 10#5))
    let (root, off) ← affineAddress source
    let (ctxRoot, ctxOff) ← affineAddress ctx
    let relative := MNat 32 (off + offset + (1 <<< 32) - ctxOff)
    let within := relative % 4
    if root != ctxRoot || relative ≥ 24 || relative % width != 0 || within + width > 4 then none
    else
      let field ← ContextField.ofXdp (relative / 4)
      some (.context field (8 * within) (8 * within + 8 * width))

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

def mapKeyByte (byte : Term) : Option Term :=
  match eval (solve byte) with
  | some c => some (Term.C32 (c % 256))
  | none =>
    if byte.width == .w32 then some (zStar 8 .w32 byte.width.bits byte)
    else if byte.width == .w64 then some (zStar 8 .w32 64 byte)
    else none

/-- Map identity is the object id plus the key-byte terms copied at lookup. -/
private def mapSlotCore (Eg : List Expr) (preds : List Predicate)
    (event _displacement : Nat) (mapTerm : Term) : Option (List Term × Nat) :=
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
        match frozen.mapM mapKeyByte with
        | none => none
        | some key =>
          match readInterval Eg (.map id key 0 32) with
          | none => none
          | some _ => some (key, layout.valueSize)

private def mapSlot (Eg : List Expr) (preds : List Predicate) (source : Term) :
    Option (Nat × Nat × Term × List Term × Nat) :=
  if !guardEg Eg then none else
  match lookupAddress (solve source) with
  | none => none
  | some (event, displacement, mapTerm) =>
    match mapSlotCore Eg preds event displacement mapTerm with
    | none => none
    | some (key, valueSize) => some (event, displacement, mapTerm, key, valueSize)

private def mapReg (Eg : List Expr) (preds : List Predicate) (source : Term)
    (offset width : Nat) : Option Reg := do
  if !(width == 1 || width == 2 || width == 4) then none
  else
    let (_, displacement, mapTerm, key, valueSize) ← mapSlot Eg preds source
    let id ← eval (solve mapTerm)
    let relative := MNat 32 (displacement + offset)
    if relative + width > valueSize || relative % width != 0 then none
    else some (.map id key (relative * 8) (relative * 8 + 8 * width))

/-- A missing later word, with no overlapping equality, is the external result of that word. -/
private def mapMaterialize (Eg : List Expr) (preds : List Predicate) (source : Term)
    (offset width : Nat) : Option (Reg × List Expr) := do
  let (event, displacement, mapTerm, key, valueSize) ← mapSlot Eg preds source
  if !(width == 1 || width == 2 || width == 4) then none
  else
    let id ← eval (solve mapTerm)
    let relative := MNat 32 (displacement + offset)
    if relative + width > valueSize || relative % width != 0 then none
    else
      let reg := Reg.map id key (relative * 8) (relative * 8 + 8 * width)
      if (readInterval Eg reg).isSome then some (reg, Expr.nil)
      else
        let wordBase := relative - relative % 4
        let within := relative % 4
        let word := Reg.map id key (wordBase * 8) (wordBase * 8 + 32)
        let gap := Eg.bindings.all fun e => !e.reg.overlaps word
        if within + width > 4 || wordBase == 0 || !gap then none
        else
          let content := star .w32 (.externalResult event (1 + wordBase / 4)) [Term.C32 1]
          let rows ← writeUpdates Eg word content
          some (reg, rows)

def exprSizedLOADEffects (Eg : List Expr) (rs1 rd : regidx) (offset width : Nat)
    (isUnsigned : Bool) (boundCtx : Option Term := none)
    (preds : List Predicate := []) : Option ExprEffect := do
  if !guardEg Eg || !(width == 1 || width == 2 || width == 4) then none
  else
    let source ← readReg Eg rs1
    if let some reg := stackReg Eg source offset width then
      let value ← CellAccess.read ⟨reg⟩ Eg .w32 isUnsigned
      some { updates := assign rd value }
    else if let some reg := contextReg Eg source offset width boundCtx then
      let value ← CellAccess.read ⟨reg⟩ Eg .w32 isUnsigned
      some { updates := assign rd value }
    else if let some (reg, rows) := mapMaterialize Eg preds source offset width then
      let seeded := Eg.override rows
      let value ← CellAccess.read ⟨reg⟩ seeded .w32 isUnsigned
      some { updates := rows.override (assign rd value) }
    else if let some o := packetOffsetAt Eg source offset width then
      let data ← contextValue Eg .data
      let access : PacketAccess :=
        { displacement := .c o, bytes := width, inputBase := some data }
      let read ← access.read Eg .w32 isUnsigned
      some { inputs := read.inputs, updates := assign rd read.value }
    else
      let access ← packetBinding Eg rs1 offset width preds
      let read ← access.read Eg .w32 isUnsigned
      some { inputs := read.inputs, updates := assign rd read.value }

def exprSizedLOAD (Eg : List Expr) (rs1 rd : regidx) (offset width : Nat)
    (isUnsigned : Bool) (boundCtx : Option Term := none)
    (preds : List Predicate := []) : Option (List Expr) := do
  let effect ← exprSizedLOADEffects Eg rs1 rd offset width isUnsigned boundCtx preds
  some effect.updates

def exprPacketLOAD (Eg : List Expr) (rs1 rd : regidx) (offset width : Nat)
    (isUnsigned : Bool) (preds : List Predicate := []) : Option (List Expr) := do
  if !guardEg Eg || !(width == 1 || width == 2 || width == 4 || width == 8) then none
  else
    let source ← readReg Eg rs1
    if let some o := packetOffsetAt Eg source offset width then
      let data ← contextValue Eg .data
      let access : PacketAccess :=
        { displacement := .c o, bytes := width, inputBase := some data }
      let read ← access.read Eg .w32 isUnsigned
      some (assign rd read.value)
    else
      let access ← packetBinding Eg rs1 offset width preds
      let read ← access.read Eg .w32 isUnsigned
      some (assign rd read.value)

/-- A buffer keeps one resource origin throughout its complete frozen range. -/
private inductive BufferOrigin where
  | stack | context | map | packet
  deriving BEq

private def byteOf (Eg : List Expr) (preds : List Predicate)
    (source : Term) (offset : Nat) (boundCtx : Option Term) :
    Option (BufferOrigin × Term) := do
  let mut found : List (BufferOrigin × Term) := []
  if let some reg := stackReg Eg source offset 1 then
    if let some field := CellAccess.read ⟨reg⟩ Eg .w32 true then
      found := (.stack, field) :: found
  if let some ctx := boundCtx then
    if let some reg := contextReg Eg source offset 1 (some ctx) then
      if let some field := CellAccess.read ⟨reg⟩ Eg .w32 true then
        found := (.context, field) :: found
  if let some reg := mapReg Eg preds source offset 1 then
    if let some field := CellAccess.read ⟨reg⟩ Eg .w32 true then
      found := (.map, field) :: found
  if let some o := packetOffsetAt Eg source offset 1 then
    let data ← contextValue Eg .data
    let access : PacketAccess :=
      { displacement := .c o, bytes := 1, inputBase := some data }
    if let some read := access.read Eg .w32 true then
      found := (.packet, read.value) :: found
  match found with
  | [one] => some one
  | _ => none

/-- Freeze only complete current bytes from one uniquely resolved resource.
Map bytes require the lookup key and an existing value. Context requires the
entry binding. A constant packet byte reads `Packet([8*o, 8*o+8))`. -/
def readBufferBytes (Eg : List Expr) (addr : Term) (n : Nat)
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
    for j in List.range n do
      let (which, byte) ← byteOf Eg preds source j boundCtx
      if let some previous := origin then
        if which != previous then none
      origin := some which
      bytes := byte :: bytes
    some bytes.reverse

/-- Lookup event, element byte offset, and the pointer's Map term. -/
def mapElementAccess (Eg : List Expr) (preds : List Predicate)
    (rs1 : regidx) (offset width : Nat) : Option (NodeId × Nat × Term) :=
  match readReg Eg rs1 with
  | none => none
  | some source =>
    match mapSlot Eg preds source with
    | none => none
    | some (event, displacement, mapTerm, _, valueSize) =>
      let relative := MNat 32 (displacement + offset)
      if !(width == 1 || width == 2 || width == 4) || relative + width > valueSize ||
          relative % width != 0 then none
      else some (event, relative, mapTerm)

private theorem mapSlot_address (Eg : List Expr) (preds : List Predicate) (source : Term)
    (event displacement : Nat) (mapTerm : Term) (key : List Term) (valueSize : Nat)
    (h : mapSlot Eg preds source = some (event, displacement, mapTerm, key, valueSize)) :
    lookupAddress (solve source) = some (event, displacement, mapTerm) := by
  simp only [mapSlot] at h
  split at h
  · cases h
  · split at h
    · cases h
    · split at h
      · cases h
      · cases h
        assumption

theorem mapElementAccess_preimage (Eg : List Expr) (preds : List Predicate)
    (rs1 : regidx) (offset width event elementOff : Nat) (map : Term)
    (h : mapElementAccess Eg preds rs1 offset width = some (event, elementOff, map)) :
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
    | some (e, displacement, m, key, valueSize) =>
      simp [mapElementAccess, hread, hslot] at h
      rcases h with ⟨_, rfl, rfl, rfl⟩
      exact ⟨source, displacement, rfl,
        mapSlot_address Eg preds source e displacement m key valueSize hslot⟩

/-- Stack, map, and constant packet stores are interval equalities.
A symbolic packet address does not create a packet register. -/
def exprSTOREEffects (Eg : List Expr) (rs1 rs2 : regidx) (offset width : Nat)
    (preds : List Predicate := []) : Option ExprEffect := do
  if !guardEg Eg || !(width == 1 || width == 2 || width == 4) then none
  else
    let value ← readReg Eg rs2
    if value.width != .w32 then none
    else
      let source ← readReg Eg rs1
      if let some reg := stackReg Eg source offset width then
        let updates ← CellAccess.write ⟨reg⟩ Eg value
        some { updates }
      else if let some reg := mapReg Eg preds source offset width then
        let updates ← CellAccess.write ⟨reg⟩ Eg value
        some { updates }
      else if let some o := packetOffsetAt Eg source offset width then
        let data ← contextValue Eg .data
        let access : PacketAccess :=
          { displacement := .c o, bytes := width, inputBase := some data }
        let updates ← access.write Eg value
        some { updates }
      else
        let access ← packetBinding Eg rs1 offset width preds
        let updates ← access.write Eg value
        some { updates }

def exprSTORE (Eg : List Expr) (rs1 rs2 : regidx) (offset width : Nat)
    (preds : List Predicate := []) : Option (List Expr) := do
  let effect ← exprSTOREEffects Eg rs1 rs2 offset width preds
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
    (preds : List Predicate := []) : Option (List Expr) :=
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
      exprSizedLOAD Eg rs1 rd (immI32 imm) width isUnsigned boundCtx preds
  | .STORE (imm, rs2, rs1, width) =>
      exprSTORE Eg rs1 rs2 (immI32 imm) width preds
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
      exprSizedLOAD Eg (creg2reg_idx rs1) (creg2reg_idx rd) (uimm.toNat <<< 2) 4 true boundCtx preds
  | .C_LWSP (uimm, rd) =>
      if isX0 rd then none else exprStackLOAD Eg sp rd (uimm.toNat <<< 2)
  | .C_SW (uimm, rs1, rs2) =>
      exprSTORE Eg (creg2reg_idx rs1) (creg2reg_idx rs2) (uimm.toNat <<< 2) 4 preds
  | .C_SWSP (uimm, rs2) => exprSTORE Eg sp rs2 (uimm.toNat <<< 2) 4 preds
  | .C_EBREAK _ => exprReject

/-- Classify input observations separately from the instruction's actual writes. -/
def stepEffects (Eg : List Expr) (i : Insn) (boundCtx : Option Term := none)
    (preds : List Predicate := []) : Option ExprEffect := do
  let effect ← match i with
    | .LOAD (imm, rs1, rd, unsigned, width) =>
      exprSizedLOADEffects Eg rs1 rd (immI32 imm) width unsigned boundCtx preds
    | .C_LW (imm, rs1, rd) =>
      exprSizedLOADEffects Eg (creg2reg_idx rs1) (creg2reg_idx rd)
        (imm.toNat <<< 2) 4 true boundCtx preds
    | .STORE (imm, rs2, rs1, width) =>
      exprSTOREEffects Eg rs1 rs2 (immI32 imm) width preds
    | .C_SW (imm, rs1, rs2) =>
      exprSTOREEffects Eg (creg2reg_idx rs1) (creg2reg_idx rs2) (imm.toNat <<< 2) 4 preds
    | .C_SWSP (imm, rs2) => exprSTOREEffects Eg sp rs2 (imm.toNat <<< 2) 4 preds
    | _ => do
      let updates ← expr Eg i boundCtx preds
      some { updates }
  if effect.validFor Eg then some effect else none

/-- Expansion transports both fresh input relations and local writes in one delta.
`expr` and `stepEffects.updates` retain the instruction-only assignment interface. -/
def step (Eg : List Expr) (i : Insn) (boundCtx : Option Term := none)
    (preds : List Predicate := []) : Option (List Expr) := do
  let effect ← stepEffects Eg i boundCtx preds
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

private def applyLocalExprs (Eg : List Expr) (preds : List Predicate)
    (effect : ExprEffect) : Option (List Expr) :=
  match applyLocal ⟨Eg, preds⟩ effect.delta preds with
  | .ok σ => some σ.exprs
  | .error _ => none

private def stackRoundTripCheck : Bool := Id.run do
  let spTerm := Term.V32 0
  let some base := writeInterval (Expr.nil.insertEq (Reg.real32 2) spTerm)
      (.stack 0 32) (Term.C32 99) | return false
  let some loaded := step base (.C_LWSP (0#6, .Regidx 10#5)) | return false
  let stored := base.insertEq (Reg.real32 8) (Term.C32 99)
  let some spill := stepEffects stored (.C_SWSP (0#6, .Regidx 8#5)) | return false
  let some saved := applyLocalExprs stored [] spill | return false
  let some again := step saved (.C_LWSP (0#6, .Regidx 10#5)) | return false
  return loaded.lookupEq (Reg.real32 10) == some (Term.C32 99) &&
    again.lookupEq (Reg.real32 10) == some (Term.C32 99) &&
    stackSlot saved sp 0 == some 0

#guard stackRoundTripCheck

private def stackBytesCheck : Bool := Id.run do
  let spTerm := Term.V32 0
  let E := Expr.nil.insertEq (Reg.real32 2) spTerm
  let addr := .app .w32 (.id .w32)
    [.app .w32 (.add .w32) [spTerm, Term.C32 (M 32 (-16))]]
  let lo := (M 32 (-16)) * 8
  let some stored := writeInterval E (.stack lo (lo + 32)) (Term.C32 0x01020304) | return false
  let some bytes := readBufferBytes stored addr 4 | return false
  let some values := bytes.mapM fun t => eval (solve t) | return false
  return values == [4, 3, 2, 1]

#guard stackBytesCheck

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

private def frozenResourceBuffersCheck : Bool := Id.run do
  let key := [Term.C32 1, Term.C32 2, Term.C32 3]
  let some keyBytes := key.mapM mapKeyByte | return false
  let data := Term.V32 4
  let E0 := Expr.nil.insertEq (Reg.real32 2) (Term.V32 0)
  let some E := putContext E0 .data data | return false
  let some E := putContext E .dataEnd (addStar .w32 data (Term.C32 16)) | return false
  let some E := putContext E .dataMeta (Term.C32 0) | return false
  let some E := putContext E .ingressIfindex (Term.C32 1) | return false
  let some E := putContext E .rxQueueIndex (Term.C32 0) | return false
  let some E := putContext E .egressIfindex (Term.C32 0) | return false
  let some E := putContext E .ctx (Term.V32 1) | return false
  let some E := putContext E .sp (Term.V32 0) | return false
  let some E := putContext E .packetBytes (Term.C32 16) | return false
  let some E := putContext E (.mapKeyBytes 42) (Term.C32 3) | return false
  let some E := putContext E (.mapValueBytes 42) (Term.C32 8) | return false
  let cell := Reg.map 42 keyBytes 0 32
  let some E := writeInterval E cell (Term.C32 0x04030201) | return false
  let some E := writeInterval E (.stack 0 32) (Term.C32 0x04030201) | return false
  let some E := writeInterval E (.packet 8 16) (star .w32 (.low 8 32) [Term.C32 0xaa]) | return false
  let some E := writeInterval E (.packet 16 24) (star .w32 (.low 8 32) [Term.C32 0xbb]) | return false
  let pointer := star .w32 (.externalResult 9 0) [Term.C32 1, Term.C32 42, Term.V32 0]
  let E := E.insertEq (Reg.real32 8) pointer
  let preds : List Predicate := [.helper 9 .lookup ([Term.C32 42, Term.V32 0] ++ key)]
  let some mapBytes := readBufferBytes E (addStar .w32 pointer (Term.C32 0)) 4
      (preds := preds) | return false
  let some mapVals := mapBytes.mapM fun t => eval (solve t) | return false
  let some pkt := readBufferBytes E (addStar .w32 data (Term.C32 1)) 1 | return false
  let some pktVal := pkt.mapM fun t => eval (solve t) | return false
  return mapVals == [1, 2, 3, 4] && pktVal == [0xaa] &&
    (readBufferBytes E data 1).isSome

#guard frozenResourceBuffersCheck

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
