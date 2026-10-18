import Core.Expr
import Core.MapLayout
import Core.Parse

namespace Core

/-- A field of the symbolic eBPF entry. These values are not Compact ELF fields. -/
inductive EntryField where
  | ctx (w : Width)
  | sp (w : Width)
  | data (w : Width)
  | packetBytes
  | alphaCtx
  | packetId
  | stackId
  deriving DecidableEq, Repr, Inhabited

/-- Immutable machine binding written once at create. -/
inductive Anchor where
  | helper
  | imageBase
  | wrapperReturn
  | mapLayout (mapId : Nat)
  | lddw (slot : Nat)
  | entry (field : EntryField)
  deriving DecidableEq, Repr, Inhabited

private def entryTag : EntryField → Nat
  | .ctx .w32 => 0
  | .ctx .w64 => 1
  | .sp .w32 => 2
  | .sp .w64 => 3
  | .data .w32 => 4
  | .data .w64 => 5
  | .packetBytes => 6
  | .alphaCtx => 7
  | .packetId => 8
  | .stackId => 9

def Anchor.width : Anchor → Width
  | .helper | .imageBase | .wrapperReturn => .w32
  | .mapLayout _ | .lddw _ => .w64
  | .entry (.ctx w) | .entry (.sp w) | .entry (.data w) => w
  | .entry .packetBytes | .entry .alphaCtx | .entry .packetId | .entry .stackId => .w32

/-- Disjoint alpha bands. One `mapId` is one register, so a second layout cannot be installed. -/
def Anchor.index : Anchor → Nat
  | .helper => 0
  | .imageBase => 1
  | .wrapperReturn => 2
  | .mapLayout id => (1 <<< 32) + id
  | .lddw slot => (2 <<< 32) + slot
  | .entry f => (3 <<< 32) + entryTag f

def Reg.anchor (a : Anchor) : Reg :=
  ⟨.anchor, a.width, a.index, none⟩

/-- `Term.C64 0` is the stored unbound marker. Callers use `lddwBind`, not this term. -/
def Anchor.unboundLddw : Term := Term.C64 0

inductive LddwBind where
  | absent
  | unbound
  | bound (t : Term)
  deriving Repr, Inhabited, BEq

def lddwBind (E : List Expr) (slot : Nat) : LddwBind :=
  match E.lookupEq (Reg.anchor (.lddw slot)) with
  | none => .absent
  | some t => if t == Anchor.unboundLddw then .unbound else .bound t

def anchorNat (E : List Expr) (a : Anchor) : Option Nat := do
  eval (solve (← E.lookupEq (Reg.anchor a)))

def Anchor.packLayout (keySize valueSize : Nat) : Option Term :=
  if keySize > 64 || valueSize == 0 || valueSize > 4096 then none
  else some (Term.C64 (keySize + (valueSize <<< 16)))

def Anchor.layout? (E : List Expr) (mapTerm : Term) : Option MapLayout := do
  let id ← eval (solve mapTerm)
  if id == 0 || id ≥ (1 <<< 32) then none else
    let packed ← E.lookupEq (Reg.anchor (.mapLayout id))
    let n ← eval (solve packed)
    let keySize := n % (1 <<< 16)
    let valueSize := n / (1 <<< 16)
    if keySize > 64 || valueSize == 0 || valueSize > 4096 then none
    else some { mapId := id, keySize, valueSize }

/-- The only writer of `RegKind.anchor`. Repeated indexes and map id 0 are rejected. -/
def Anchor.install (E : List Expr) (rows : List (Anchor × Term)) : Option (List Expr) := do
  let indexes := rows.map (·.1.index)
  if indexes.eraseDups.length != indexes.length then none else
    rows.foldlM (init := E) fun acc (a, t) => do
      if let .mapLayout 0 := a then failure
      if t.width != a.width then failure
      if (acc.lookupEq (Reg.anchor a)).isSome then failure
      pure (acc.insertEq (Reg.anchor a) t)

def Anchor.mapRows (ids keys values : List Nat) : Option (List (Anchor × Term)) :=
  match ids, keys, values with
  | [], [], [] => some []
  | id :: ids, k :: keys, v :: values => do
    if id == 0 || id ≥ (1 <<< 32) then failure
    let packed ← Anchor.packLayout k v
    let rest ← mapRows ids keys values
    pure ((.mapLayout id, packed) :: rest)
  | _, _, _ => none

def Anchor.installMaps (E : List Expr) (maps : List MapLayout) : Option (List Expr) := do
  let rows ← Anchor.mapRows (maps.map (·.mapId)) (maps.map (·.keySize)) (maps.map (·.valueSize))
  Anchor.install E rows

private def roundTrip (a : Anchor) : Bool :=
  parseReg (renderReg (Reg.anchor a)) == some (Reg.anchor a)

#guard [Anchor.helper, .imageBase, .wrapperReturn, .mapLayout 42, .lddw 34,
    .entry (.ctx .w64), .entry .packetBytes].all roundTrip

#guard Id.run do
  let some packed := Anchor.packLayout 4 8 | return false
  let some E := Anchor.install [] [(.mapLayout 7, packed), (.lddw 34, Anchor.unboundLddw),
      (.lddw 35, Term.C64 9), (.helper, Term.C32 0x100)] | return false
  return Anchor.layout? E (Term.C64 7) == some ⟨7, 4, 8⟩ &&
    lddwBind E 34 == .unbound &&
    lddwBind E 35 == .bound (Term.C64 9) &&
    lddwBind E 36 == .absent &&
    (Anchor.install E [(.mapLayout 7, packed)]).isNone &&
    (Anchor.install [] [(.mapLayout 0, packed)]).isNone

end Core
