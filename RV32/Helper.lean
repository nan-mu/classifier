import Core.Anchor
import RV32.Initial
import RV32.Expr
import Node.Path
import Core.MapLayout

namespace RV32
open Core Node

structure HelperCall where
  kind : HelperKind
  id : Nat
  args : List Term
  deriving Repr

def parseHelperCall (Eg : List Expr) : Except RejectReason HelperCall := do
  if !guardEg Eg then throw .localReject
  let some idTerm := Eg.lookupEq (Reg.real32 10) | throw .undefinedSrc
  if idTerm.width != .w32 then throw .undefinedSrc
  let some id := eval (solve idTerm) | throw .unsupported
  let kind := helperKind id
  let mut args := []
  for j in [:helperArity kind] do
    match Eg.lookupEq (Reg.real32 (11 + j)) with
    | some t =>
      if t.width != .w32 then throw .undefinedSrc
      args := args ++ [solve t]
    | none =>
      if j < helperRequired kind then throw .undefinedSrc else break
  pure ⟨kind, id, args⟩

/-- Byte-valued frozen key/value tail after the ABI prefix. -/
private def frozenTailOk (tail : List Term) : Bool :=
  tail.all fun t =>
    t.width == .w32 &&
      match t with
      | .const _ c => c < 256
      | _ => true

/-- Resolve layout and every required buffer before appending any frozen bytes. -/
private def freezeMapTail (mem : Mem) (Eg : List Expr) (boundCtx : Option Term)
    (preds : List Predicate) (kind : HelperKind) (args : List Term) : Option (List Term) := do
  let map ← args.head?
  let layout ← Anchor.layout? Eg map
  match kind, args with
  | .lookup, [_, keyPtr] | .delete, [_, keyPtr] =>
      readBufferBytes mem Eg keyPtr layout.keySize boundCtx preds
  | .update, [_, keyPtr, valuePtr, _] => do
      let key ← readBufferBytes mem Eg keyPtr layout.keySize boundCtx preds
      let value ← readBufferBytes mem Eg valuePtr layout.valueSize boundCtx preds
      some (key ++ value)
  | _, _ => none

/-- ABI observation survives an undefined complete-buffer refinement unchanged. -/
def helperPredicate (event : NodeId) (Eg : List Expr)
    (boundCtx : Option Term := none) (mem : Mem := .empty)
    (preds : List Predicate := []) : Except RejectReason Predicate := do
  let call ← parseHelperCall Eg
  let args := match freezeMapTail mem Eg boundCtx preds call.kind call.args with
    | some tail => if frozenTailOk tail then call.args ++ tail else call.args
    | none => call.args
  pure (.helper event call.kind args)

/-- Prefix ABI args drive externalResult; optional frozen tail is ignored here. -/
private def helperCallOfPredicate (p : Predicate) : Except RejectReason (NodeId × HelperCall) := do
  let .helper event kind args := p | throw .unsupported
  if kind.id ≥ (1 <<< 32) || helperKind kind.id != kind then throw .unsupported
  let arity := helperArity kind
  if args.length < helperRequired kind then throw .undefinedSrc
  let abi := args.take arity
  let tail := args.drop arity
  if abi.any (fun t => t.width != .w32) || !frozenTailOk tail then throw .undefinedSrc
  pure (event, ⟨kind, kind.id, abi⟩)

/-- The return item is determined by the call's identity and ABI arguments. -/
private def callReturnTerm (p : Predicate) : Except RejectReason Term := do
  let (event, call) ← helperCallOfPredicate p
  let external := star .w32 (.externalResult event 0) (Term.C32 call.id :: call.args)
  let result := match call.kind with
    | .unsupported _ => Term.C32 ((1 <<< 32) - 1)
    | .checksum => star .w32 (.low 16 32) [external]
    | _ => external
  pure result

/-- Lookup anchors the return at value offset zero when the frozen key is complete. -/
def helperMapWrites (E : List Expr) (p : Predicate) : Except RejectReason (List MemWrite) := do
  let (event, call) ← helperCallOfPredicate p
  if call.kind != .lookup then return []
  match p with
  | .helper _ .lookup (map :: _keyPtr :: key) =>
    match Anchor.layout? E map, eval (solve map) with
    | some layout, some id =>
      if key.length != layout.keySize || layout.valueSize < 4 then return []
      let key ← match keyTile key with
        | .ok tile => pure tile
        | .error _ => return []
      let value ← match Tile.ofTerm (.regVar event (Reg.real32 10)) 32 with
        | .ok tile => pure tile
        | .error _ => throw .localReject
      pure [⟨.map id key, 0, value⟩]
    | _, _ => pure []
  | _ => pure []

/-- The helper value projection writes a0. The lookup value is a memory write. -/
def helperExpr (p : Predicate) : Except RejectReason (List Expr) := do
  let result ← callReturnTerm p
  pure (Expr.nil.insertEq (Reg.real32 10) result)

#guard [1, 2, 3, 5, 6, 28, 65].map (fun id => helperArity (helperKind id)) == [2, 4, 2, 0, 5, 5, 2]
#guard helperArity (helperKind 999) == 0
#guard (eval (star .w32 (.externalResult 0 0) [Term.C32 5])).isNone
#guard solve (star .w32 (.externalResult 0 0) [Term.C32 5]) ==
  star .w32 (.externalResult 0 0) [Term.C32 5]
#guard match helperExpr (.ret (Term.V32 1)) with
  | .error .unsupported => true
  | _ => false

private def putTerm (mem : Mem) (slot : BitSlot) (start : Nat) (t : Term) (bits : Nat) :
    Option Mem := do
  let tile ← (Tile.ofTerm t bits).toOption
  (mem.write slot start tile).toOption

private def completeMapBuffersCheck : Bool := Id.run do
  let key := addStar .w32 (Term.V32 0) (Term.C32 3)
  let value := addStar .w32 (Term.V32 4) (Term.C32 1)
  let data := Term.V32 4
  let fields := [data, addStar .w32 data (Term.C32 8), Term.C32 0, Term.C32 0,
    Term.C32 0, Term.C32 0]
  let mut built : Mem := .empty
  for (j, t) in (List.range 6).zip fields do
    let some next := putTerm built (.context j) 0 t 32 | return false
    built := next
  let some mem := putTerm built .stack 0 (Term.C32 0x04030201) 32 | return false
  let some mem := putTerm mem .stack 32 (Term.C32 0x08070605) 32 | return false
  let some mem := putTerm mem .packet 8 (Term.C32 0xaa) 8 | return false
  let some mem := putTerm mem .packet 16 (Term.C32 0xbb) 8 | return false
  let some E := Anchor.installMaps (Expr.nil
    |>.insertEq (Reg.real32 2) (Term.V32 0)
    |>.insertEq (Reg.real32 11) (Term.C32 42)
    |>.insertEq (Reg.real32 12) key
    |>.insertEq (Reg.real32 13) value
    |>.insertEq (Reg.real32 14) (Term.C32 0))
    [{ mapId := 42, keySize := 3, valueSize := 2 }] | return false
  for (id, kind, abi, tail) in [
      (1, HelperKind.lookup, [Term.C32 42, key], [Term.C32 4, Term.C32 5, Term.C32 6]),
      (3, HelperKind.delete, [Term.C32 42, key], [Term.C32 4, Term.C32 5, Term.C32 6]),
      (2, HelperKind.update, [Term.C32 42, key, value, Term.C32 0],
        [Term.C32 4, Term.C32 5, Term.C32 6, Term.C32 0xaa, Term.C32 0xbb])] do
    let state := E.insertEq (Reg.real32 10) (Term.C32 id)
    let .ok p := helperPredicate 70 state (mem := mem) | return false
    if p != .helper 70 kind (abi ++ tail) then return false
    let .ok result := helperExpr p | return false
    if result.lookupEq (Reg.real32 10) !=
        some (star .w32 (.externalResult 70 0) (Term.C32 id :: abi)) then return false
    let some changed := putTerm mem .stack 32 (Term.C32 0) 32 | return false
    let .ok fresh := helperPredicate 71 state (mem := changed) | return false
    if fresh != .helper 71 kind
        (abi ++ [Term.C32 4, Term.C32 0, Term.C32 0] ++ tail.drop 3) then return false
  let update := E.insertEq (Reg.real32 10) (Term.C32 2)
  let abiPrefix := [Term.C32 42, key, value, Term.C32 0]
  let some missingStack := putTerm .empty .stack 0 (Term.C32 0x04030201) 32 | return false
  let mut missingStack := missingStack
  for (j, t) in (List.range 6).zip fields do
    let some next := putTerm missingStack (.context j) 0 t 32 | return false
    missingStack := next
  let .ok incompletePredicate := helperPredicate 70 update (mem := missingStack) | return false
  let some openStack := putTerm .empty .stack 0 (Term.C32 0x04030201) 32 | return false
  let some openStack := putTerm openStack .stack 32 (Term.C32 0x08070605) 32 | return false
  let mut openPacket := openStack
  for (j, t) in (List.range 6).zip fields do
    let some next := putTerm openPacket (.context j) 0 t 32 | return false
    openPacket := next
  let .ok openPredicate := helperPredicate 70 update (mem := openPacket) | return false
  let some openTail := readBufferBytes openPacket update value 2 | return false
  return incompletePredicate == .helper 70 .update abiPrefix &&
    (readBufferBytes missingStack update key 3).isNone &&
    openPredicate == .helper 70 .update (abiPrefix ++ [Term.C32 4, Term.C32 5, Term.C32 6] ++ openTail) &&
    openTail.length == 2

#guard completeMapBuffersCheck

private def mapBufferBoundsCheck : Bool := Id.run do
  let pointer := star .w32 (.externalResult 9 0) [Term.C32 1, Term.C32 17, Term.V32 7]
  let key := Term.V32 0
  let atEnd := addStar .w32 pointer (Term.C32 3)
  let beyondEnd := addStar .w32 pointer (Term.C32 4)
  let target : MapLayout := { mapId := 42, keySize := 3, valueSize := 3 }
  let source : MapLayout := { mapId := 17, keySize := 8, valueSize := 6 }
  let maps := [target, source]
  let sourceKey := List.replicate 8 (Term.C32 7)
  let .ok sourceTile := keyTile sourceKey | return false
  let sourceSlot := BitSlot.map 17 sourceTile
  let some mem := putTerm .empty .stack 0 (Term.C32 0x04030201) 32 | return false
  let some mem := putTerm mem sourceSlot 0 (Term.C32 0x04030201) 32 | return false
  let some mem := putTerm mem sourceSlot 32 (Term.C32 0x08070605) 32 | return false
  let prior : List Predicate :=
    [.helper 9 .lookup ([Term.C32 17, Term.V32 7] ++ sourceKey)]
  let bare := Expr.nil
    |>.insertEq (Reg.real32 2) key
    |>.insertEq (Reg.real32 11) (Term.C32 42)
    |>.insertEq (Reg.real32 14) (Term.C32 0)
  let unknown := star .w32 (.externalResult 9 0) [Term.C32 1, Term.V32 17, Term.V32 7]
  let wrapped := addStar .w32 pointer (Term.C32 ((1 <<< 32) - 1))
  for (id, kind) in [(1, HelperKind.lookup), (3, HelperKind.delete),
      (2, HelperKind.update)] do
    let bufferReg := if id == 2 then Reg.real32 13 else Reg.real32 12
    let abi := if id == 2 then [Term.C32 42, key, atEnd, Term.C32 0]
      else [Term.C32 42, atEnd]
    let tail := if id == 2 then [Term.C32 1, Term.C32 2, Term.C32 3,
      Term.C32 4, Term.C32 5, Term.C32 6] else [Term.C32 4, Term.C32 5, Term.C32 6]
    let placed := bare.insertEq (Reg.real32 10) (Term.C32 id)
      |>.insertEq (Reg.real32 12) (if id == 2 then key else atEnd)
      |>.insertEq (Reg.real32 13) atEnd
    let some state := Anchor.installMaps placed maps | return false
    let .ok frozen := helperPredicate 70 state (mem := mem) (preds := prior) | return false
    if frozen != .helper 70 kind (abi ++ tail) then return false
    let .ok result := helperExpr frozen | return false
    if result.lookupEq (Reg.real32 10) !=
        some (star .w32 (.externalResult 70 0) (Term.C32 id :: abi)) then return false
    for layouts in [[target], [{ source with valueSize := 5 }]] do
      let some variant := Anchor.installMaps placed layouts | return false
      let .ok abiPrefix := helperPredicate 70 variant (mem := mem) (preds := prior) | return false
      if abiPrefix != .helper 70 kind abi then return false
    for address in [beyondEnd, unknown, wrapped] do
      let changed := state.insertEq bufferReg address
      let expected := if id == 2 then [Term.C32 42, key, address, Term.C32 0]
        else [Term.C32 42, address]
      let .ok abiPrefix := helperPredicate 70 changed (mem := mem) (preds := prior) | return false
      if abiPrefix != .helper 70 kind expected then return false
    if id == 2 then
      let changed := state.insertEq (Reg.real32 12) beyondEnd
      let .ok abiPrefix := helperPredicate 70 changed (mem := mem) (preds := prior) | return false
      if abiPrefix != .helper 70 kind [Term.C32 42, beyondEnd, atEnd, Term.C32 0] then
        return false
  return true

#guard mapBufferBoundsCheck

end RV32
