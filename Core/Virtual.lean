import Core.Expr
import Core.Insn

namespace Core

/-- Input materialization is separate from the instruction's simultaneous assignments. -/
structure ExprEffect where
  inputs : ExprSet := .empty
  updates : ExprSet := .empty
  deriving Inhabited, Repr

def ExprEffect.delta (effect : ExprEffect) : ExprSet :=
  effect.inputs.override effect.updates

def ExprEffect.validFor (effect : ExprEffect) (Eg : ExprSet) : Bool :=
  Eg.keysUnique && Eg.wellTyped && effect.inputs.wellTyped && effect.updates.wellTyped &&
    effect.inputs.keysUnique && effect.updates.keysUnique &&
    effect.inputs.entries.all (fun e => (Eg.find? e.key).isNone)

/-- A resolved field in a canonical Stack, Map or Context cell; address binding is ISA-owned. -/
structure CellAccess where
  reg : Reg
  bitOffset : Nat
  bits : Nat
  deriving Inhabited, Repr

def CellAccess.valid (a : CellAccess) (valueWidth : Width) : Bool :=
  (a.reg.kind == .stack || a.reg.kind == .map || a.reg.kind == .context) &&
    a.bits > 0 && a.bits ≤ valueWidth.bits && a.bitOffset + a.bits ≤ a.reg.width.bits

def CellAccess.read (a : CellAccess) (Eg : ExprSet) (w : Width)
    (isUnsigned : Bool) : Option Term := do
  if !Eg.keysUnique || !Eg.wellTyped || !a.valid w then none
  else
    let old ← Eg.lookupEq a.reg
    if old.width != a.reg.width then none
    else if a.bitOffset == 0 && a.bits == a.reg.width.bits && w == a.reg.width then some old
    else
      let field := star a.reg.width (.extract a.bitOffset a.bits a.reg.width.bits) [old]
      some (if isUnsigned then zStar a.bits w a.reg.width.bits field
        else sStar a.bits w a.reg.width.bits field)

/-- A frozen cell byte is the low-eight-bit zero-extension of its stored field. -/
theorem CellAccess.read_byte (a : CellAccess) (Eg : ExprSet) (w : Width)
    (value : Term) (hb : a.bits = 8) (h : a.read Eg w true = some value) :
    ∃ stored, Eg.lookupEq a.reg = some stored ∧
      value = zStar 8 w a.reg.width.bits
        (star a.reg.width (.extract a.bitOffset 8 a.reg.width.bits) [stored]) := by
  unfold CellAccess.read at h
  split at h
  · simp at h
  · cases hs : Eg.lookupEq a.reg with
    | none => simp [hs] at h
    | some stored =>
      have hn : (8 : Nat) ≠ a.reg.width.bits := by
        cases a.reg.width <;> simp [Width.bits]
      by_cases hw : stored.width = a.reg.width
      · simp [hs, hw, hb, hn] at h
        exact ⟨stored, rfl, h.symm⟩
      · simp [hs, hw] at h

def CellAccess.write (a : CellAccess) (Eg : ExprSet) (source : Term) : Option ExprSet := do
  if !Eg.keysUnique || !Eg.wellTyped || !a.valid source.width then none
  else
    let low := zStar a.bits a.reg.width source.width.bits source
    if a.bitOffset == 0 && a.bits == a.reg.width.bits then
      some (ExprSet.empty.insertEq a.reg
        (if source.width == a.reg.width then source else low))
    else
      let old ← Eg.lookupEq a.reg
      if old.width != a.reg.width then none
      else
        let mask := ((1 <<< a.bits) - 1) <<< a.bitOffset
        let kept := andStar a.reg.width.bits a.reg.width old
          (Term.C a.reg.width (a.reg.width.mask ^^^ mask))
        let inserted := shlStar a.reg.width low (Term.C a.reg.width a.bitOffset)
        some (ExprSet.empty.insertEq a.reg (orStar a.reg.width.bits a.reg.width kept inserted))

inductive ByteOrder where
  | little | big
  deriving BEq, Repr, Inhabited

def PacketOffset.plus (a b : PacketOffset) : PacketOffset :=
  match a, b with
  | .c x, .c y => .c (x + y)
  | .c 0, b => b
  | a, .c 0 => a
  | .c x, b => .add b (.c x)
  | a, b => .add a b

private def packetLow (q : Nat) (a : PacketOffset) : PacketOffset :=
  match a with
  | .packet _ => if q ≥ 8 then a else .low q a
  | .low n b => .low (min q n) b
  | .c n => .c (MNat q n)
  | _ => .low q a

private def packetZext (q v : Nat) (a : PacketOffset) : PacketOffset :=
  if q ≥ v then a else
  match a with
  | .packet _ => if q ≥ 8 then a else .zext q v a
  | .low n _ => if q ≥ n then a else .zext q v a
  | .c n => .c (MNat q n)
  | _ => .zext q v a

private def packetSext (q v : Nat) (w : Width) (a : PacketOffset) : PacketOffset :=
  if q == v && v == w.bits then a else .sext q v a

/-- Only a current packet-byte equality can justify an open offset leaf. -/
def packetOffsetFrom (E : ExprSet) (t : Term) : Option PacketOffset :=
  let normalized := solve t
  let isOpen := match t with | .const _ _ => false | _ => true
  match E.entries.find? (fun e => isOpen && e.reg.kind == .packet &&
      e.reg.compound.isNone && e.rel == .eq && e.term == normalized) with
  | some e => some (.packet e.reg.alpha)
  | none => match t with
    | .const _ n => some (.c n)
    | .app _ (.id _) [a] => packetOffsetFrom E a
    | .app _ (.zext q _ v) [a] =>
      packetZext q v <$> packetOffsetFrom E a
    | .app _ (.sext q w v) [a] =>
      packetSext q v w <$> packetOffsetFrom E a
    | .app _ (.low q _) [a]
    | .app _ (.extract 0 q _) [a] => packetLow q <$> packetOffsetFrom E a
    | .app _ (.add _) [a, b] => do
      pure ((← packetOffsetFrom E a).plus (← packetOffsetFrom E b))
    | .app _ (.sub _) [a, .const _ n] =>
      (fun a => .sub a n) <$> packetOffsetFrom E a
    | .app _ (.shl _) [a, b] => do
      pure (.shl (← packetOffsetFrom E a) (← packetOffsetFrom E b))
    | .app _ (.and _) [a, .const _ mask]
    | .app _ (.and _) [.const _ mask, a] => do
      let inner ← packetOffsetFrom E a
      let q := Nat.log2 (mask + 1)
      if q != 0 && (1 <<< q) - 1 == mask then pure (packetLow q inner)
      else pure (.mask inner mask)
    | .app _ (.or _) [a, b] => do
      pure (.or (← packetOffsetFrom E a) (← packetOffsetFrom E b))
    | .app _ (.lshr _) [a, .const _ n] =>
      (fun a => .lshr a n) <$> packetOffsetFrom E a
    | _ => none
termination_by sizeOf t

/-- A single entry data root plus an offset in the packet-only grammar. -/
def packetDisplacement (E : ExprSet) (root address : Term) : Option PacketOffset :=
  if address == root then some (.c 0) else
  match address with
  | .app _ (.id _) [a] => packetDisplacement E root a
  | .app _ (.zext q _ v) [a] =>
    packetZext q v <$> packetDisplacement E root a
  | .app _ (.sext q w v) [a] =>
    packetSext q v w <$> packetDisplacement E root a
  | .app _ (.sub _) [a, .const _ n] =>
    (fun a => .sub a n) <$> packetDisplacement E root a
  | .app _ (.add _) [a, b] =>
    ((do pure ((← packetDisplacement E root a).plus (← packetOffsetFrom E b)))).orElse
      (fun _ => do pure ((← packetDisplacement E root b).plus (← packetOffsetFrom E a)))
  | _ => none
termination_by sizeOf address

def PacketOffset.toTerm (E : ExprSet) (w : Width) : PacketOffset → Option Term
  | .c n => some (Term.C w n)
  | .packet alpha => do
    let byte ← E.lookupEq ⟨.packet, .w32, alpha, none⟩
    pure (if w == .w32 then byte else zStar 8 w 32 byte)
  | .add a b => do pure (addStar w (← a.toTerm E w) (← b.toTerm E w))
  | .low q a => do pure (star w (.low q w.bits) [← a.toTerm E w])
  | .shl a b => do pure (shlStar w (← a.toTerm E w) (← b.toTerm E w))
  | .sub a n => do pure (subStar w (← a.toTerm E w) (Term.C w n))
  | .id a => do pure (idStar w (← a.toTerm E w))
  | .zext q v a => do
    let input ← if v == 32 then some Width.w32 else if v == 64 then some .w64 else none
    pure (zStar q w v (← a.toTerm E input))
  | .sext q v a => do
    let input ← if v == 32 then some Width.w32 else if v == 64 then some .w64 else none
    pure (sStar q w v (← a.toTerm E input))
  | .or a b => do pure (orStar w.bits w (← a.toTerm E w) (← b.toTerm E w))
  | .mask a n => do pure (andStar w.bits w (← a.toTerm E w) (Term.C w n))
  | .lshr a n => do pure (lshrStar w (← a.toTerm E w) (Term.C w n))

/-- Find a passed current unsigned bound with the same symbolic address spine
and at least the requested exclusive end. Preserve the actual checked endpoint,
including when a wider check authorizes a narrower access. -/
partial def termContains (needle hay : Term) : Bool :=
  hay == needle ||
    match hay with
    | .app _ _ args => args.any (termContains needle)
    | _ => false

/-- A passed check mentions this packet's end pointer. The access still has to be
one data root plus an offset in the packet grammar. The checked end recorded for
that access is the access itself: later length arithmetic is not re-proved. -/
private def endMentioned (E : ExprSet) (preds : List Predicate) (ending : Term) : Bool :=
  let endTerm := solve ending
  let inTerm (t : Term) := termContains endTerm (solve t)
  preds.any (fun (p : Predicate) => match p with
    | Predicate.branch _ _ cond => inTerm cond.lhs || inTerm cond.rhs
    | _ => false) ||
    E.constraints.any fun e =>
      inTerm e.term || match E.lookupEq e.reg with
        | some lhs => inTerm lhs
        | none => false

private def unsignedEnd (E : ExprSet) (ending : Term) (e : Expr) :
    Option (Term × Bool) := do
  let lhs ← E.lookupEq e.reg
  if (e.rel == .leu || e.rel == .ltu) && solve e.term == solve ending then
    some (lhs, e.rel == .ltu)
  else if (e.rel == .geu || e.rel == .gtu) && solve lhs == solve ending then
    some (e.term, e.rel == .gtu)
  else none

def packetBoundWitness (E : ExprSet) (base address ending : Term) (bytes : Nat)
    (preds : List Predicate := []) : Option (Bool × PacketOffset) :=
  let actual := additiveSpine address.width (solve address)
  let bounds := E.constraints.filterMap fun e => do
    let (checked, strict) ← unsignedEnd E ending e
    if checked.width != address.width then none else
      let bound := additiveSpine address.width (solve checked)
      some (bound, strict, checked)
  match bounds.find? fun (bound, _, _) => bound.1 == actual.1 && actual.2 + bytes ≤ bound.2 with
  | some (_, strict, checked) => do
    pure (strict, ← packetDisplacement E base (solve checked))
  | none =>
    if bounds.any fun (bound, _, _) => bound.1 == actual.1 then none else do
      if !endMentioned E preds ending then none else
        let disp ← packetDisplacement E base address
        some (false, disp.plus (.c bytes))

/-- Decimal digit blocks keep arbitrary Nat identities in well-formed 32-bit
metadata constants; 10 terminates a block. -/
private def packetMetadata (ns : List Nat) : List Term :=
  ns.flatMap fun n =>
    ((toString n).toList.map (fun c => Term.C32 (c.toNat - '0'.toNat))) ++ [Term.C32 10]

private def parsePacketMetadata : Nat → List Term → Option (List Nat)
  | 0, [] => some []
  | 0, _ => none
  | fuel + 1, ts => if ts.isEmpty then some [] else do
    let (digits, rest) := ts.span (· != Term.C32 10)
    if digits.isEmpty then none else
      let chars ← digits.mapM fun t => match t with
        | .const .w32 n => if n < 10 then some (Char.ofNat ('0'.toNat + n)) else none
        | _ => none
      let n ← (String.ofList chars).toNat?
      let _ :: rest := rest | none
      pure (n :: (← parsePacketMetadata fuel rest))

def CompoundPacketReg.annotate (p : CompoundPacketReg) (value : Term) : Term :=
  .app .w32 (.packetRead p.bytes p.endCtx)
    (value :: packetMetadata ([p.κ, if p.strict then 1 else 0, p.byteIndex] ++
      p.offset.code ++ p.checkedEnd.code))

def compoundPacketFromMetadata (bytes endCtx : Nat) (metadata : List Term) :
    Option CompoundPacketReg := do
  let values ← parsePacketMetadata metadata.length metadata
  let κ :: strict :: byteIndex :: code := values | none
  if strict > 1 || byteIndex ≥ bytes || ![1, 2, 4, 8].contains bytes then none else
    let (offset, rest) ← PacketOffset.decode code.length code
    let (checkedEnd, []) ← PacketOffset.decode rest.length rest | none
    pure ⟨κ, offset, bytes, endCtx, strict == 1, byteIndex, checkedEnd⟩

/-- A unique packet identity and byte offset. Access validity is an external premise.
Only `inputBase` authorizes first-read materialization of untouched input bytes. -/
structure PacketAccess where
  κ : Nat
  offset : Nat
  bytes : Nat
  order : ByteOrder := .little
  inputBase : Option Term := none
  compound : Option CompoundPacketReg := none
  deriving Inhabited, Repr

def PacketAccess.valid (a : PacketAccess) (w : Width) : Bool :=
  (a.bytes == 1 || a.bytes == 2 || a.bytes == 4 || a.bytes == 8) &&
    8 * a.bytes ≤ w.bits
    && (match a.compound with
      | none => true
      | some p => p.κ == a.κ && p.bytes == a.bytes && p.byteIndex == 0)

def PacketAccess.byteReg (a : PacketAccess) (j : Nat) : Reg :=
  match a.compound with
  | none => Reg.packet a.κ (a.offset + j)
  | some p => Reg.compoundPacket { p with byteIndex := j }

private def bytePosition (a : PacketAccess) (j : Nat) : Nat :=
  if a.order == .little then j else a.bytes - 1 - j

structure PacketRead where
  inputs : ExprSet
  value : Term
  deriving Inhabited, Repr

def PacketAccess.read (a : PacketAccess) (Eg : ExprSet) (w : Width)
    (isUnsigned : Bool) : Option PacketRead := do
  if !Eg.keysUnique || !Eg.wellTyped || !a.valid w then none
  else
    let mut inputs := ExprSet.empty
    let mut raw := Term.C w 0
    for j in List.range a.bytes do
      let reg := a.byteReg j
      let byte ← match Eg.lookupEq reg with
        | some t => if t.width == .w32 then some t else none
        | none => do
          -- Other relations alone do not authorize inventing a current equality.
          if !(Eg.forReg reg).isEmpty then none
          else
            let base ← a.inputBase
            let displacement ← match a.compound with
              | none =>
                if a.offset + j ≥ (1 <<< base.width.bits) then none
                else some (Term.C base.width (a.offset + j))
              | some p => do
                let off ← p.offset.toTerm Eg base.width
                pure (addStar base.width off (Term.C base.width j))
            let address := addStar base.width base displacement
            let rawByte := star .w32 (.low 8 32) [star .w32 (.inputByte a.κ) [base, address]]
            let t := match a.compound with
              | none => rawByte
              | some p => ({ p with byteIndex := j } : CompoundPacketReg).annotate rawByte
            inputs := inputs.insertEq reg t
            some t
      let widened := zStar 8 w 32 byte
      raw := orStar w.bits w raw (shlStar w widened (Term.C w (8 * bytePosition a j)))
    some ⟨inputs, if isUnsigned then raw else sStar (8 * a.bytes) w w.bits raw⟩

/-- A one-byte packet freeze zero-extends the saved or materialized byte.
The surrounding OR/shift is the read assembler's zero-offset identity wrapper. -/
theorem PacketAccess.read_byte (a : PacketAccess) (Eg : ExprSet) (w : Width)
    (result : PacketRead) (hb : a.bytes = 1)
    (h : a.read Eg w true = some result) :
    ∃ stored, result.value =
      orStar w.bits w (Term.C w 0) (shlStar w (zStar 8 w 32 stored) (Term.C w 0)) := by
  cases he : Eg.lookupEq (a.byteReg 0) with
  | some byte =>
    by_cases hw : byte.width = .w32
    · simp [PacketAccess.read, hb, List.range_succ, bytePosition, he, hw] at h
      obtain ⟨_, hr⟩ := h
      cases hr
      exact ⟨byte, rfl⟩
    · simp [PacketAccess.read, hb, List.range_succ, bytePosition, he, hw] at h
  | none =>
    by_cases hempty : Eg.forReg (a.byteReg 0) = []
    · cases hi : a.inputBase with
      | none =>
        simp [PacketAccess.read, hb, List.range_succ, bytePosition, he, hi] at h
      | some base =>
        cases hc : a.compound with
        | none =>
          by_cases hbound : a.offset < 1 <<< base.width.bits
          · simp [PacketAccess.read, hb, List.range_succ, bytePosition,
              he, hempty, hi, hc, Nat.not_le.mpr hbound] at h
            obtain ⟨_, hr⟩ := h
            cases hr
            exact ⟨_, rfl⟩
          · simp [PacketAccess.read, hb, List.range_succ, bytePosition,
              he, hempty, hi, hc, Nat.le_of_not_gt hbound] at h
        | some p =>
          cases ho : p.offset.toTerm Eg base.width with
          | none =>
            simp [PacketAccess.read, hb, List.range_succ, bytePosition,
              he, hi, hc, ho] at h
          | some off =>
            simp [PacketAccess.read, hb, List.range_succ, bytePosition,
              he, hempty, hi, hc, ho] at h
            obtain ⟨_, hr⟩ := h
            cases hr
            exact ⟨_, rfl⟩
    · simp [PacketAccess.read, hb, List.range_succ, bytePosition, he, hempty] at h

def PacketAccess.write (a : PacketAccess) (Eg : ExprSet) (source : Term) : Option ExprSet := do
  if !Eg.keysUnique || !Eg.wellTyped || !a.valid source.width then none
  else
    let mut updates := ExprSet.empty
    for j in List.range a.bytes do
      let byte := star .w32 (.extract (8 * bytePosition a j) 8 source.width.bits) [source]
      updates := updates.insertEq (a.byteReg j) byte
    some updates

end Core
