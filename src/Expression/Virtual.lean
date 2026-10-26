import Expression.Basic
import Observation.Insn
import Expression.Interval

namespace Expression
open Term Term.Value Observation Interface

/-- Input materialization is separate from the instruction's simultaneous assignments. -/
structure ExprEffect where
  inputs : List Expr := []
  updates : List Expr := []
  deriving Inhabited, Repr

def ExprEffect.delta (effect : ExprEffect) : List Expr :=
  effect.inputs ++ effect.updates

def ExprEffect.validFor (effect : ExprEffect) (Eg : List Expr) : Bool :=
  Eg.keysUnique && Eg.wellTyped && effect.inputs.wellTyped && effect.updates.wellTyped &&
    effect.inputs.keysUnique && effect.updates.keysUnique &&
    effect.inputs.all (fun e => (Eg.lookupRel e.reg e.rel).isNone)

/-- A virtual interval. The bit range is the register, not a second offset. -/
structure CellAccess where
  reg : Reg
  deriving Inhabited, Repr

def CellAccess.valid (a : CellAccess) : Bool :=
  a.reg.valid &&
    match a.reg with
    | .real .. => false
    | _ => true

def CellAccess.read (a : CellAccess) (Eg : List Expr) (w : Width)
    (isUnsigned : Bool) : Option Term := do
  if !Eg.keysUnique || !Eg.wellTyped || !a.valid then none
  let old ← readInterval Eg a.reg
  if old.semanticBits == w.bits && old.width == w then some old
  else if isUnsigned then some (zStar old.semanticBits w old.width.bits old)
  else some (sStar old.semanticBits w old.width.bits old)

def CellAccess.write (a : CellAccess) (Eg : List Expr) (source : Term) : Option (List Expr) := do
  if !Eg.keysUnique || !a.valid then none
  let n := a.reg.bits
  let raw := if source.semanticBits == n then source
    else zStar n (Width.ofBits n) source.width.bits source
  let stored ← «seal» n raw
  some [Expr.mkEq a.reg stored]

inductive ByteOrder where
  | little | big
  deriving BEq, Repr, Inhabited

/-- Symbolic packet displacement before the address is a concrete bit interval.
This is not a register. -/
inductive PacketOffset where
  | c (value : Nat)
  | packet (byte : Nat)
  | add (lhs rhs : PacketOffset)
  | low (bits : Nat) (arg : PacketOffset)
  | shl (arg amount : PacketOffset)
  | sub (arg : PacketOffset) (constant : Nat)
  | id (arg : PacketOffset)
  | zext (bits input : Nat) (arg : PacketOffset)
  | sext (bits input : Nat) (arg : PacketOffset)
  | or (lhs rhs : PacketOffset)
  | mask (arg : PacketOffset) (constant : Nat)
  | lshr (arg : PacketOffset) (constant : Nat)
  deriving DecidableEq, BEq, Repr, Inhabited

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
def packetOffsetFrom (E : List Expr) (t : Term) : Option PacketOffset :=
  let normalized := solve t
  let isOpen := match t with | .const _ _ => false | _ => true
  match E.bindings.find? (fun e => isOpen && e.rel == .eq && e.term == normalized &&
      match e.reg with
      | .packet b hi => hi == b + 8 && b % 8 == 0
      | _ => false) with
  | some e => some (.packet (e.reg.lo / 8))
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
    | .app w (.mullo _) [a, .const wc c]
    | .app w (.mullo _) [.const wc c, a] =>
      match natPow2Shift? c with
      | some k =>
        if k != 0 && decide (k < w.bits) && wc == w then
          (fun a => .shl a (.c k)) <$> packetOffsetFrom E a
        else none
      | none => none
    | .app w (.udiv _ z) [a, .const wc c] =>
      match natPow2Shift? c with
      | some k =>
        if z == 0 && k != 0 && decide (k < w.bits) && wc == w then
          (fun a => .lshr a k) <$> packetOffsetFrom E a
        else none
      | none => none
    -- A materialized numeric packet byte is `inputByte` at `base + n`.
    -- The leaf is that byte offset.
    | .app _ (.inputByte _) [base, address] =>
      let disp : Term → Option Nat
        | a => if a == base then some 0 else
          match a with
          | .app _ (.add _) [b, .const _ n]
          | .app _ (.add _) [.const _ n, b] => if b == base then some (MNat 32 n) else none
          | _ => none
      (.packet ·) <$> disp address
    | _ => none
termination_by sizeOf t

/-- A single entry data root plus an offset in the packet-only grammar. -/
def packetDisplacement (E : List Expr) (root address : Term) : Option PacketOffset :=
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

def PacketOffset.toTerm (E : List Expr) (w : Width) : PacketOffset → Option Term
  | .c n => some (Term.C w n)
  | .packet n => do
    let byte ← readInterval E (.packet (8 * n) (8 * n + 8))
    pure (if w == .w32 then byte else zStar 8 w byte.width.bits byte)
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
private def endMentioned (E : List Expr) (preds : List Observation) (ending : Term) : Bool :=
  let endTerm := solve ending
  let inTerm (t : Term) := termContains endTerm (solve t)
  preds.any (fun (p : Observation) => match p with
    | Observation.branch _ _ cond => inTerm cond.lhs || inTerm cond.rhs
    | _ => false) ||
    E.constraints.any fun e =>
      inTerm e.term || match E.lookupEq e.reg with
        | some lhs => inTerm lhs
        | none => false

private def unsignedEnd (E : List Expr) (ending : Term) (e : Expr) :
    Option (Term × Bool) := do
  let lhs ← E.lookupEq e.reg
  if (e.rel == .leu || e.rel == .ltu) && solve e.term == solve ending then
    some (lhs, e.rel == .ltu)
  else if (e.rel == .geu || e.rel == .gtu) && solve lhs == solve ending then
    some (e.term, e.rel == .gtu)
  else none

def packetBoundWitness (E : List Expr) (base address ending : Term) (bytes : Nat)
    (preds : List Observation := []) : Option (Bool × PacketOffset) :=
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

/-- One input packet. A constant displacement materializes `Packet([8*o, 8*o+8))`.
A symbolic displacement stays an address calculation and creates no packet register. -/
structure PacketAccess where
  displacement : PacketOffset
  bytes : Nat
  order : ByteOrder := .little
  inputBase : Option Term := none
  deriving Inhabited, Repr

def PacketAccess.valid (a : PacketAccess) (w : Width) : Bool :=
  (a.bytes == 1 || a.bytes == 2 || a.bytes == 4 || a.bytes == 8) &&
    8 * a.bytes ≤ w.bits

def PacketAccess.constOffset? (a : PacketAccess) : Option Nat :=
  match a.displacement with
  | .c n => some n
  | _ => none

def PacketAccess.byteReg? (a : PacketAccess) (j : Nat) : Option Reg :=
  match a.constOffset? with
  | some o => some (.packet (8 * (o + j)) (8 * (o + j) + 8))
  | none => none

private def bytePosition (a : PacketAccess) (j : Nat) : Nat :=
  if a.order == .little then j else a.bytes - 1 - j

private def packetByteTerm (base : Term) (address : Term) : Term :=
  star .w32 (.low 8 32) [star .w32 (.inputByte 0) [base, address]]

structure PacketRead where
  inputs : List Expr
  value : Term
  deriving Inhabited, Repr

def PacketAccess.readStored (a : PacketAccess) (Eg : List Expr) (j : Nat) :
    Option (List Expr × Term) :=
  match a.byteReg? j with
  | some reg =>
    match readInterval Eg reg with
    | some t => some (Expr.nil, t)
    | none => do
      if !(Eg.forReg reg).isEmpty then none
      else
        let base ← a.inputBase
        let o ← a.constOffset?
        if o + j ≥ (1 <<< base.width.bits) then none
        else
          let rawByte := packetByteTerm base
            (addStar base.width base (Term.C base.width (o + j)))
          let stored ← «seal» reg.bits rawByte
          some ([Expr.mkEq reg stored], rawByte)
  | none => do
    let base ← a.inputBase
    let off ← a.displacement.toTerm Eg base.width
    let address := addStar base.width
      (addStar base.width base off) (Term.C base.width j)
    some (Expr.nil, packetByteTerm base address)

def PacketAccess.read (a : PacketAccess) (Eg : List Expr) (w : Width)
    (isUnsigned : Bool) : Option PacketRead := do
  if !Eg.keysUnique || !Eg.wellTyped || !a.valid w then none
  else
    let mut inputs := Expr.nil
    let mut raw := Term.C w 0
    for j in List.range a.bytes do
      let (delta, byte) ← a.readStored Eg j
      inputs := (update ⟨inputs, []⟩ { exprs := delta, predicates := [] }).exprs
      let widened := zStar 8 w 32 byte
      raw := orStar w.bits w raw (shlStar w widened (Term.C w (8 * bytePosition a j)))
    some ⟨inputs, if isUnsigned then raw else sStar (8 * a.bytes) w w.bits raw⟩

/-- A one-byte packet freeze zero-extends the saved or materialized byte.
The surrounding OR/shift is the read assembler's zero-offset identity wrapper. -/
theorem PacketAccess.read_byte (a : PacketAccess) (Eg : List Expr) (w : Width)
    (result : PacketRead) (hb : a.bytes = 1)
    (h : a.read Eg w true = some result) :
    ∃ stored, result.value =
      orStar w.bits w (Term.C w 0) (shlStar w (zStar 8 w 32 stored) (Term.C w 0)) := by
  cases hs : a.readStored Eg 0 with
  | none =>
    simp [PacketAccess.read, hb, List.range_succ, bytePosition, hs] at h
  | some stored =>
    simp [PacketAccess.read, hb, List.range_succ, bytePosition, hs] at h
    obtain ⟨_, hr⟩ := h
    cases hr
    exact ⟨stored.2, rfl⟩

def PacketAccess.write (a : PacketAccess) (Eg : List Expr) (source : Term) :
    Option (List Expr) := do
  if !Eg.keysUnique || !Eg.wellTyped || !a.valid source.width then none
  else
    match a.displacement with
    | .c o =>
      let mut updates : List Expr := Expr.nil
      for j in List.range a.bytes do
        let reg := Reg.packet (8 * (o + j)) (8 * (o + j) + 8)
        let byte := star .w32 (.extract (8 * bytePosition a j) 8 source.width.bits) [source]
        let stored ← «seal» reg.bits byte
        updates := updates ++ [Expr.mkEq reg stored]
      some updates
    | _ => some Expr.nil

end Expression
