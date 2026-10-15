import RV32IMC.Initial
import RV32IMC.Expr
import PathMerge.Path
import ClassifierExpr.MapLayout

namespace RV32IMC
open ClassifierExpr PathMerge

structure HelperCall where
  kind : HelperKind
  id : Nat
  args : List Term
  deriving Repr

def parseHelperCall (Eg : ExprSet) : Except RejectReason HelperCall := do
  if !guardEg Eg then throw .localReject
  let some idTerm := Eg.lookupEq (Reg.real32 10) | throw .undefinedSrc
  if idTerm.width != .w32 then throw .undefinedSrc
  let some id := eval (solve idTerm) | throw .unsupported
  let kind := helperKind id
  let mut args := []
  for j in [:helperArity kind] do
    let some t := Eg.lookupEq (Reg.real32 (11 + j)) | throw .undefinedSrc
    if t.width != .w32 then throw .undefinedSrc
    args := args ++ [solve t]
  pure ⟨kind, id, args⟩

/-- Byte-valued frozen key/value tail after the ABI prefix. -/
private def frozenTailOk (tail : List Term) : Bool :=
  tail.all fun t =>
    t.width == .w32 &&
      match t with
      | .const _ c => c < 256
      | _ => true

/-- Resolve layout and every required buffer before appending any frozen bytes. -/
private def freezeMapTail (Eg : ExprSet) (maps : List MapLayout)
    (boundCtx : Option Term) (kind : HelperKind) (args : List Term) :
    Option (List Term) := do
  let map ← args.head?
  let id ← eval (solve map)
  let [layout] := maps.filter (fun layout => layout.mapId == id) | none
  match kind, args with
  | .lookup, [_, keyPtr] | .delete, [_, keyPtr] =>
      readBufferBytes Eg keyPtr layout.keySize maps boundCtx
  | .update, [_, keyPtr, valuePtr, _] => do
      let key ← readBufferBytes Eg keyPtr layout.keySize maps boundCtx
      let value ← readBufferBytes Eg valuePtr layout.valueSize maps boundCtx
      some (key ++ value)
  | _, _ => none

/-- ABI observation survives an undefined complete-buffer refinement unchanged. -/
def helperPredicate (event : NodeId) (Eg : ExprSet) (maps : List MapLayout := [])
    (boundCtx : Option Term := none) : Except RejectReason Predicate := do
  let call ← parseHelperCall Eg
  let args := match freezeMapTail Eg maps boundCtx call.kind call.args with
    | some tail => if frozenTailOk tail then call.args ++ tail else call.args
    | none => call.args
  pure (.helper event call.kind args)

/-- Prefix ABI args drive externalResult; optional frozen tail is ignored here. -/
private def helperCallOfPredicate (p : Predicate) : Except RejectReason (NodeId × HelperCall) := do
  let .helper event kind args := p | throw .unsupported
  if kind.id ≥ (1 <<< 32) || helperKind kind.id != kind then throw .unsupported
  let arity := helperArity kind
  if args.length < arity then throw .undefinedSrc
  let abi := args.take arity
  let tail := args.drop arity
  if abi.any (fun t => t.width != .w32) || !frozenTailOk tail then throw .undefinedSrc
  pure (event, ⟨kind, kind.id, abi⟩)

/-- Map term and frozen key bytes from a lookup observation (empty key ⇒ not frozen). -/
def lookupFrozenKey (p : Predicate) : Option (Term × List Term) :=
  match p with
  | .helper _ .lookup (map :: _keyPtr :: frozen) => some (map, frozen)
  | .helper _ .lookup _ => none
  | _ => none

/-- The return item is determined by the call's identity and ABI arguments. -/
private def callReturnTerm (p : Predicate) : Except RejectReason Term := do
  let (event, call) ← helperCallOfPredicate p
  let external := star .w32 (.externalResult event 0) (Term.C32 call.id :: call.args)
  let result := match call.kind with
    | .unsupported _ => Term.C32 ((1 <<< 32) - 1)
    | .checksum => star .w32 (.low 16 32) [external]
    | _ => external
  pure result

/-- Lookup introduces the first Map word, [0,4), related to this call's return register. -/
def helperMapExpr (p : Predicate) : Except RejectReason ExprSet := do
  let (event, call) ← helperCallOfPredicate p
  pure (if call.kind == .lookup then
    ExprSet.empty.insertEq (Reg.mapWord event 0) (.regVar event (Reg.real32 10))
    else ExprSet.empty)

/-- The helper value projection writes a0; a lookup also introduces its Map relation. -/
def helperExpr (p : Predicate) : Except RejectReason ExprSet := do
  let result ← callReturnTerm p
  let map ← helperMapExpr p
  pure (updateExpr (ExprSet.empty.insertEq (Reg.real32 10) result) map)

#guard [1, 2, 3, 5, 6, 28, 65].map (fun id => helperArity (helperKind id)) == [2, 4, 2, 0, 5, 5, 2]
#guard helperArity (helperKind 999) == 0
#guard (eval (star .w32 (.externalResult 0 0) [Term.C32 5])).isNone
#guard solve (star .w32 (.externalResult 0 0) [Term.C32 5]) ==
  star .w32 (.externalResult 0 0) [Term.C32 5]
#guard match helperExpr (.ret (Term.V32 1)) with
  | .error .unsupported => true
  | _ => false

private def completeMapBuffersCheck : Bool := Id.run do
  let key := addStar .w32 (Term.V32 0) (Term.C32 3)
  let value := addStar .w32 (Term.V32 4) (Term.C32 1)
  let maps : List MapLayout := [{ mapId := 42, keySize := 3, valueSize := 2 }]
  let E := ExprSet.empty
    |>.insertEq (Reg.real32 2) (Term.V32 0)
    |>.insertEq (Reg.real32 11) (Term.C32 42)
    |>.insertEq (Reg.real32 12) key
    |>.insertEq (Reg.real32 13) value
    |>.insertEq (Reg.real32 14) (Term.C32 0)
    |>.insertEq (Reg.sw ((1 <<< 33) + 0)) (Term.C32 0x04030201)
    |>.insertEq (Reg.sw ((1 <<< 33) + 4)) (Term.C32 0x08070605)
    |>.insertEq (Reg.ctx32 0) (Term.V32 4)
    |>.insertEq (Reg.ctx32 1) (addStar .w32 (Term.V32 4) (Term.C32 8))
    |>.insertEq (Reg.ctx32 2) (Term.C32 0)
    |>.insertEq (Reg.ctx32 3) (Term.C32 0)
    |>.insertEq (Reg.ctx32 4) (Term.C32 0)
    |>.insertEq (Reg.ctx32 5) (Term.C32 0)
    |>.insertEq (Reg.packet 0 1) (Term.C32 0xaa)
    |>.insertEq (Reg.packet 0 2) (Term.C32 0xbb)
  for (id, kind, abi, tail) in [
      (1, HelperKind.lookup, [Term.C32 42, key], [Term.C32 4, Term.C32 5, Term.C32 6]),
      (3, HelperKind.delete, [Term.C32 42, key], [Term.C32 4, Term.C32 5, Term.C32 6]),
      (2, HelperKind.update, [Term.C32 42, key, value, Term.C32 0],
        [Term.C32 4, Term.C32 5, Term.C32 6, Term.C32 0xaa, Term.C32 0xbb])] do
    let state := E.insertEq (Reg.real32 10) (Term.C32 id)
    let .ok p := helperPredicate 70 state maps | return false
    if p != .helper 70 kind (abi ++ tail) then return false
    let .ok result := helperExpr p | return false
    if result.lookupEq (Reg.real32 10) !=
        some (star .w32 (.externalResult 70 0) (Term.C32 id :: abi)) then return false
    let changed := state.insertEq (Reg.sw ((1 <<< 33) + 4)) (Term.C32 0)
    let .ok fresh := helperPredicate 71 changed maps | return false
    if fresh != .helper 71 kind
        (abi ++ [Term.C32 4, Term.C32 0, Term.C32 0] ++ tail.drop 3) then return false
  let update := E.insertEq (Reg.real32 10) (Term.C32 2)
  let abiPrefix := [Term.C32 42, key, value, Term.C32 0]
  let missing := { update with
    entries := update.entries.filter (fun e => e.reg != Reg.packet 0 2) }
  let .ok incompletePredicate := helperPredicate 70 missing maps | return false
  let .ok ambiguous := helperPredicate 70 update (maps ++ maps) | return false
  return incompletePredicate == .helper 70 .update abiPrefix &&
    ambiguous == .helper 70 .update abiPrefix &&
    (readBufferBytes missing value 2 maps).isNone

#guard completeMapBuffersCheck

private def mapBufferBoundsCheck : Bool := Id.run do
  let pointer := star .w32 (.externalResult 9 0) [Term.C32 1, Term.C32 17, Term.V32 7]
  let key := Term.V32 0
  let atEnd := addStar .w32 pointer (Term.C32 3)
  let beyondEnd := addStar .w32 pointer (Term.C32 4)
  let target : MapLayout := { mapId := 42, keySize := 3, valueSize := 3 }
  let source : MapLayout := { mapId := 17, keySize := 8, valueSize := 6 }
  let maps := [target, source]
  let E := ExprSet.empty
    |>.insertEq (Reg.real32 2) key
    |>.insertEq (Reg.real32 11) (Term.C32 42)
    |>.insertEq (Reg.real32 14) (Term.C32 0)
    |>.insertEq (Reg.sw (1 <<< 33)) (Term.C32 0x04030201)
    |>.insertEq (Reg.mapWord 9 0) (Term.C32 0x04030201)
    |>.insertEq (Reg.mapWord 9 4) (Term.C32 0x08070605)
    |>.insertEq (Reg.mapWord 9 ((1 <<< 32) - 4)) (Term.C32 0x08070605)
  for (id, kind) in [(1, HelperKind.lookup), (3, HelperKind.delete),
      (2, HelperKind.update)] do
    let bufferReg := if id == 2 then Reg.real32 13 else Reg.real32 12
    let abi := if id == 2 then [Term.C32 42, key, atEnd, Term.C32 0]
      else [Term.C32 42, atEnd]
    let tail := if id == 2 then [Term.C32 1, Term.C32 2, Term.C32 3,
      Term.C32 4, Term.C32 5, Term.C32 6] else [Term.C32 4, Term.C32 5, Term.C32 6]
    let state := E.insertEq (Reg.real32 10) (Term.C32 id)
      |>.insertEq (Reg.real32 12) (if id == 2 then key else atEnd)
      |>.insertEq (Reg.real32 13) atEnd
    let .ok frozen := helperPredicate 70 state maps | return false
    if frozen != .helper 70 kind (abi ++ tail) then return false
    let .ok result := helperExpr frozen | return false
    if result.lookupEq (Reg.real32 10) !=
        some (star .w32 (.externalResult 70 0) (Term.C32 id :: abi)) then return false
    for layouts in [[target], [target, source, source],
        [target, { source with valueSize := 5 }]] do
      let .ok abiPrefix := helperPredicate 70 state layouts | return false
      if abiPrefix != .helper 70 kind abi then return false
    let unknown := star .w32 (.externalResult 9 0) [Term.C32 1, Term.V32 17, Term.V32 7]
    let wrapped := addStar .w32 pointer (Term.C32 ((1 <<< 32) - 1))
    for (address, layouts) in [(beyondEnd, maps), (unknown, maps),
        (wrapped, [target, { source with valueSize := (1 <<< 32) + 2 }])] do
      let changed := state.insertEq bufferReg address
      let expected := if id == 2 then [Term.C32 42, key, address, Term.C32 0]
        else [Term.C32 42, address]
      let .ok abiPrefix := helperPredicate 70 changed layouts | return false
      if abiPrefix != .helper 70 kind expected then return false
    if id == 2 then
      let changed := state.insertEq (Reg.real32 12) beyondEnd
      let .ok abiPrefix := helperPredicate 70 changed maps | return false
      if abiPrefix != .helper 70 kind [Term.C32 42, beyondEnd, atEnd, Term.C32 0] then
        return false
  return true

#guard mapBufferBoundsCheck

end RV32IMC
