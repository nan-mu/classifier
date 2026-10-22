import EBPF.Memory

namespace EBPF
open Core Node

/-- Native ABI prefix: immediate helper id, r1 through rn at full width. -/
structure HelperCall where
  kind : HelperKind
  id : Nat
  args : List Term
  deriving Repr

def parseHelperCall (E : List Expr) (id : Nat) : Except RejectReason HelperCall := do
  if !E.keysUnique || !E.wellTyped then throw .localReject
  let kind := helperKind id
  let mut args := []
  for j in [:helperArity kind] do
    match E.lookupEq (Reg.real64 (1 + j)) with
    | some t =>
      if t.width != .w64 then throw .undefinedSrc
      args := args ++ [solve t]
    | none =>
      if j < helperRequired kind then throw .undefinedSrc else break
  pure ⟨kind, id, args⟩

/-- Freeze complete current key/value buffers from one pre-call snapshot.
An unavailable layout or byte keeps the ABI prefix, including for update where
neither tail is appended unless both complete buffers are available. -/
def freezeHelperArgs (mem : Mem) (E : List Expr) (call : HelperCall)
    (preds : List Predicate := []) : List Term :=
  let frozen : Option (List Term) := do
    match call.kind, call.args with
    | .lookup, [map, keyPtr] | .delete, [map, keyPtr] =>
      let layout ← Anchor.layout? E map
      availableBufferBytes mem E keyPtr layout.keySize preds
    | .update, [map, keyPtr, valuePtr, _flags] =>
      let layout ← Anchor.layout? E map
      let key ← availableBufferBytes mem E keyPtr layout.keySize preds
      let value ← availableBufferBytes mem E valuePtr layout.valueSize preds
      pure (key ++ value)
    | _, _ => none
  match frozen with
  | some bytes => call.args ++ bytes
  | none => call.args

/-- Only ABI arguments, not the frozen observation tail, determine the return. -/
def callReturnTerm (event : NodeId) (call : HelperCall) : Term :=
  let external := star .w64 (.externalResult event 0) (Term.C64 call.id :: call.args)
  match call.kind with
  | .checksum => star .w64 (.low 16 64) [external]
  | .unsupported _ => Term.C64 ((1 <<< 64) - 1)
  | _ => external

/-- Lookup records r0. The value bytes are a memory write, not a map register. -/
def helperExpr (event : NodeId) (call : HelperCall) : List Expr :=
  Expr.nil.insertEq (Reg.real64 0) (callReturnTerm event call)

/-- Anchor the lookup return at value offset zero when the frozen key is complete. -/
def lookupAnchor (E : List Expr) (event : NodeId) (call : HelperCall)
    (frozen : List Term) : Except RejectReason (List MemWrite) := do
  if call.kind != .lookup then return []
  match frozen with
  | map :: _keyPtr :: key =>
    match Anchor.layout? E map, eval (solve map) with
    | none, _ | _, none => pure []
    | some layout, some id =>
      if key.length != layout.keySize || layout.valueSize < 8 then return []
      let bits := 64
      let key ← match keyTile key with
        | .ok tile => pure tile
        | .error _ => throw .undefinedSrc
      let value ← match Tile.ofTerm (Term.regVar event (Reg.real64 0)) bits with
        | .ok tile => pure tile
        | .error _ => throw .localReject
      pure [⟨.map id key, 0, value⟩]
  | _ => pure []

#guard match parseHelperCall Expr.nil 1 with
  | .error .undefinedSrc => true
  | _ => false
#guard match parseHelperCall Expr.nil 999 with
  | .ok call => call.kind == .unsupported 999 && call.args.isEmpty &&
      callReturnTerm 7 call == Term.C64 18446744073709551615
  | _ => false
#guard match parseHelperCall
    (Expr.nil.insertEq (Reg.real64 1) (Term.V64 1)
      |>.insertEq (Reg.real64 2) (Term.C64 10)) 6 with
  | .ok call => call.kind == .printk && call.args == [Term.V64 1, Term.C64 10]
  | _ => false
#guard match parseHelperCall
    (Expr.nil.insertEq (Reg.real64 1) (Term.V64 3)
      |>.insertEq (Reg.real64 2) (Term.V64 4)) 1 with
  | .ok call => call.args == [Term.V64 3, Term.V64 4] &&
      (helperExpr 7 call).lookupEq (Reg.real64 0) ==
        some (callReturnTerm 7 call) &&
      (helperExpr 7 call).lookupEq (Reg.mapDword 7 0) == none
  | _ => false
#guard Id.run do
  let p : EntryParams := ⟨Term.V64 1, Term.V64 0, Term.V32 2, 64, 0, 0, 0⟩
  let keyPtr := addStar .w64 p.tSp (Term.C64 (M 64 (-4)))
  let call : HelperCall := ⟨.lookup, 1, [Term.C64 42, keyPtr]⟩
  let maps : List MapLayout := [⟨42, 4, 8⟩]
  let .ok mem := Mem.write .empty .stack (508 * 8) ⟨[.const 32 0x11223344]⟩ | return false
  let E := host p Expr.nil maps
  let args := freezeHelperArgs mem E call
  return args == call.args ++ [Term.C64 0x44, Term.C64 0x33, Term.C64 0x22, Term.C64 0x11] &&
    args.all (fun t => t.width == .w64) &&
    freezeHelperArgs .empty E call == call.args &&
    freezeHelperArgs mem (host p Expr.nil) call == call.args

private def helperMutationFreezeCheck : Bool := Id.run do
  let p : EntryParams := ⟨Term.V64 1, Term.V64 0, Term.V32 2, 64, 0, 0, 0⟩
  let keyPtr := addStar .w64 p.tSp (Term.C64 (M 64 (-4)))
  let valuePtr := addStar .w64 p.tSp (Term.C64 (M 64 (-12)))
  let maps : List MapLayout := [⟨42, 4, 8⟩]
  let update : HelperCall := ⟨.update, 2, [Term.C64 42, keyPtr, valuePtr, Term.C64 0]⟩
  let delete : HelperCall := ⟨.delete, 3, [Term.C64 42, keyPtr]⟩
  let .ok mem := Mem.write .empty .stack (508 * 8) ⟨[.const 32 0x04030201]⟩ | return false
  let .ok mem := mem.write .stack (500 * 8) ⟨[.const 32 0x08070605]⟩ | return false
  let .ok mem := mem.write .stack (504 * 8) ⟨[.const 32 0x0c0b0a09]⟩ | return false
  let .ok missingMem := Mem.write .empty .stack (508 * 8) ⟨[.const 32 0x04030201]⟩ | return false
  let E := host p Expr.nil maps
  let key := [Term.C64 1, Term.C64 2, Term.C64 3, Term.C64 4]
  let value := [Term.C64 5, Term.C64 6, Term.C64 7, Term.C64 8,
    Term.C64 9, Term.C64 10, Term.C64 11, Term.C64 12]
  let missing := host p Expr.nil maps
  return freezeHelperArgs mem E update == update.args ++ key ++ value &&
    freezeHelperArgs mem E delete == delete.args ++ key &&
    freezeHelperArgs missingMem missing update == update.args &&
    callReturnTerm 9 update ==
      star .w64 (.externalResult 9 0) (Term.C64 2 :: update.args)

private def existingBufferKindsCheck : Bool := Id.run do
  let p : EntryParams := ⟨Term.V64 1, Term.V64 0, Term.C32 0x1000, 64, 0, 0, 0⟩
  let .ok initial := buildE0 p | return false
  let mapPtr := star .w64 (.externalResult 7 0) [Term.C64 1, Term.C64 42, Term.V64 9]
  let maps : List MapLayout := [⟨42, 4, 8⟩]
  let key := [Term.C64 9, Term.C64 9, Term.C64 9, Term.C64 9]
  let lookup := Predicate.helper 7 .lookup ([Term.C64 42, Term.V64 9] ++ key)
  let .ok keyTile := keyTile key | return false
  let .ok mem := initial.mem.write (.map 42 keyTile) 0 ⟨[.const 32 0x04030201]⟩ | return false
  let .ok mem := mem.write .packet 0 ⟨[.const 32 0x08070605]⟩ | return false
  let E := host p initial.exprs maps
  let mapCall : HelperCall := ⟨.delete, 3, [Term.C64 42, mapPtr]⟩
  let packetCall : HelperCall := ⟨.lookup, 1, [Term.C64 42, Term.C64 0x1000]⟩
  let contextCall : HelperCall := ⟨.delete, 3, [Term.C64 42, p.tCtx]⟩
  let openPacket := freezeHelperArgs initial.mem E packetCall
  let some openBytes := availableBufferBytes initial.mem E (Term.C64 0x1000) 4 | return false
  return freezeHelperArgs mem E mapCall [lookup] ==
      mapCall.args ++ [Term.C64 1, Term.C64 2, Term.C64 3, Term.C64 4] &&
    freezeHelperArgs mem E packetCall ==
      packetCall.args ++ [Term.C64 5, Term.C64 6, Term.C64 7, Term.C64 8] &&
    openPacket == packetCall.args ++ openBytes &&
    openBytes.length == 4 &&
    freezeHelperArgs initial.mem E contextCall ==
      contextCall.args ++ [Term.C64 0, Term.C64 16, Term.C64 0, Term.C64 0] &&
    (availableBufferBytes mem E mapPtr 9 [lookup]).isNone

#guard helperMutationFreezeCheck
#guard existingBufferKindsCheck

end EBPF
