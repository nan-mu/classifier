import Observation.Insn
import Expression.Resource.Anchor
import Expression.Interval
import Interface.Update

namespace Observation
open Term Term.Value Expression Interface

/-- What differs between architectures. The snapshot and the return term do not. -/
structure HelperConvention where
  width : Width
  returnReg : Reg
  readBytes : List Expr → Term → Nat → Option (List Term)
  keyByte : Term → Option Term
  /-- Bits of the anchored value word. `none` means this value size is not anchored. -/
  anchorBits : Nat → Option Nat

def HelperKind.freezesBuffers : HelperKind → Bool
  | .lookup | .update | .delete => true
  | _ => false

/-- Right-hand sides of map-cell equalities for `mapId`, in binding order.
Collected before the call's own cell equality is added, so the return term does not mention itself. -/
def mapCellTerms (E : List Expr) (mapId : Nat) : List Term :=
  E.bindings.filterMap fun e =>
    match e.reg with
    | .map id _ _ _ => if id == mapId then some e.term else none
    | _ => none

/-- `some` replaces pointer slots with the bytes they denote.
`none` is not a freeze, and the pointer is not kept. -/
def freezeHelperArgs (conv : HelperConvention) (E : List Expr)
    (kind : HelperKind) (args : List Term) : Option (List Term) :=
  match kind, args with
  | .lookup, [map, keyPtr] | .delete, [map, keyPtr] => do
      let layout ← Anchor.layout? E map
      let key ← conv.readBytes E keyPtr layout.keySize
      pure (map :: key)
  | .update, [map, keyPtr, valuePtr, flags] => do
      let layout ← Anchor.layout? E map
      let key ← conv.readBytes E keyPtr layout.keySize
      let value ← conv.readBytes E valuePtr layout.valueSize
      pure (map :: (key ++ value ++ [flags]))
  | .lookup, _ | .update, _ | .delete, _ => none
  | _, args => some args

/-- Lane 0. The argument list is the helper id, the snapshot, then the map-cell
terms already in `E` for that map. Checksum keeps the low 16 bits. An unsupported
id is the all-ones constant. -/
def callReturnTerm (conv : HelperConvention) (E : List Expr)
    (kind : HelperKind) (id : Nat) (snapshot : List Term) : Term :=
  let w := conv.width
  let cells :=
    if kind.freezesBuffers then
      match snapshot.head?.bind (eval ∘ solve) with
      | some mid => mapCellTerms E mid
      | none => []
    else []
  let external := star w (.externalResult 0) (Term.C w id :: snapshot ++ cells)
  match kind with
  | .checksum => star w (.low 16 w.bits) [external]
  | .unsupported _ => Term.C w ((1 <<< w.bits) - 1)
  | _ => external

/-- Cell equality at value offset zero, plus a `.leu` from the return register to
`return + valueSize`. `none` is a failed anchor. `some []` is not a lookup anchor. -/
def lookupAnchor (conv : HelperConvention) (E : List Expr)
    (kind : HelperKind) (id : Nat) (snapshot : List Term) : Option (List Expr) := do
  if kind != .lookup then return []
  match snapshot with
  | map :: key =>
    match Anchor.layout? E map, eval (solve map) with
    | some layout, some mid =>
      let some bits := conv.anchorBits layout.valueSize | return []
      if key.length != layout.keySize then return []
      let some narrowed := key.mapM conv.keyByte | none
      let ret := callReturnTerm conv E kind id snapshot
      let cell := Reg.map mid narrowed 0 bits
      let some stored := «seal» cell.bits ret | none
      let bound := addStar conv.width ret (Term.C conv.width layout.valueSize)
      pure [Expr.mkEq cell stored, Expr.mkRel conv.returnReg .leu bound]
    | _, _ => pure []
  | _ => pure []

/-- Byte extent of a lookup return. The witness register's equality is `base`,
and the relation term is that base plus a concrete byte count.
The `Bool` is `true` when the relation is strict. -/
def mapValueExtent (E : List Expr) (base : Term) : Option (Nat × Bool) :=
  E.constraints.findSome? fun e => do
    if e.rel != .leu && e.rel != .ltu then none
    let lhs ← E.lookupEq e.reg
    if solve lhs != solve base then none
    let (spine, disp) := additiveSpine base.width (solve e.term)
    let (baseSpine, baseDisp) := additiveSpine base.width (solve base)
    if spine != baseSpine || disp < baseDisp then none
    some (disp - baseDisp, e.rel == .ltu)

def accessWithin (E : List Expr) (base : Term) (rel : Int) (bytes : Nat) : Bool :=
  if rel < 0 then false else
    match mapValueExtent E base with
    | none => false
    | some (n, true) => rel.toNat + bytes < n
    | some (n, false) => rel.toNat + bytes ≤ n

/-- Key bytes are the layout-sized prefix of the return term's tail.
Later terms are the map-cell dependence and are not part of the key. -/
def lookupKey (E : List Expr) (map : Term) (rest : List Term)
    (narrow : Term → Option Term) : Option (List Term) := do
  let layout ← Anchor.layout? E map
  let raw := rest.take layout.keySize
  if raw.length != layout.keySize then none
  raw.mapM narrow

private def sampleConv (w : Width) : HelperConvention where
  width := w
  returnReg := if w == .w64 then Reg.real64 0 else Reg.real32 10
  readBytes := fun _ address n =>
    match address with
    | .const _ 1 => some ((List.range n).map fun i => Term.C w (i + 1))
    | _ => none
  keyByte := some
  anchorBits := fun n => if n == 0 then none else some (8 * min n (w.bits / 8))

#guard freezeHelperArgs (sampleConv .w64) Expr.nil .lookup [Term.C64 42, Term.C64 1] == none
#guard freezeHelperArgs (sampleConv .w64) Expr.nil .printk [Term.C64 1, Term.C64 2] ==
  some [Term.C64 1, Term.C64 2]
#guard freezeHelperArgs (sampleConv .w64) Expr.nil .lookup [Term.C64 42, Term.C64 2] == none
#guard callReturnTerm (sampleConv .w64) Expr.nil (.unsupported 9) 9 [] ==
  Term.C64 ((1 <<< 64) - 1)

private def cellRow : List Expr :=
  [Expr.mkEq (Reg.map 42 [] 0 32) (Term.C64 7)]

#guard callReturnTerm (sampleConv .w64) Expr.nil .lookup 1 [Term.C64 42, Term.C64 9] !=
  callReturnTerm (sampleConv .w64) cellRow .lookup 1 [Term.C64 42, Term.C64 9]

end Observation
