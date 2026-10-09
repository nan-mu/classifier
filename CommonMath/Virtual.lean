import CommonMath.Expr

namespace CommonMath

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

/-- A resolved field in a canonical Stack or Map cell; address binding is ISA-owned. -/
structure CellAccess where
  reg : Reg
  bitOffset : Nat
  bits : Nat
  deriving Inhabited, Repr

def CellAccess.valid (a : CellAccess) (valueWidth : Width) : Bool :=
  (a.reg.kind == .stack || a.reg.kind == .map) &&
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

/-- A unique packet identity and byte offset. Access validity is an external premise.
Only `inputBase` authorizes first-read materialization of untouched input bytes. -/
structure PacketAccess where
  resource : Nat
  offset : Nat
  bytes : Nat
  order : ByteOrder := .little
  inputBase : Option Term := none
  deriving Inhabited, Repr

def PacketAccess.valid (a : PacketAccess) (w : Width) : Bool :=
  (a.bytes == 1 || a.bytes == 2 || a.bytes == 4 || a.bytes == 8) &&
    8 * a.bytes ≤ w.bits

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
      let reg := Reg.packet a.resource (a.offset + j)
      let byte ← match Eg.lookupEq reg with
        | some t => if t.width == .w32 then some t else none
        | none => do
          -- Other relations alone do not authorize inventing a current equality.
          if !(Eg.forReg reg).isEmpty then none
          else
            let base ← a.inputBase
            if a.offset + j ≥ (1 <<< base.width.bits) then none
            else
              let address := addStar base.width base (Term.C base.width (a.offset + j))
              let t := star .w32 (.low 8 32) [star .w32 (.inputByte a.resource) [base, address]]
              inputs := inputs.insertEq reg t
              some t
      let widened := zStar 8 w 32 byte
      raw := orStar w.bits w raw (shlStar w widened (Term.C w (8 * bytePosition a j)))
    some ⟨inputs, if isUnsigned then raw else sStar (8 * a.bytes) w w.bits raw⟩

def PacketAccess.write (a : PacketAccess) (Eg : ExprSet) (source : Term) : Option ExprSet := do
  if !Eg.keysUnique || !Eg.wellTyped || !a.valid source.width then none
  else
    let mut updates := ExprSet.empty
    for j in List.range a.bytes do
      let byte := star .w32 (.extract (8 * bytePosition a j) 8 source.width.bits) [source]
      updates := updates.insertEq (Reg.packet a.resource (a.offset + j)) byte
    some updates

end CommonMath
