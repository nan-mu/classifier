import EBPF.Memory
import Core.Update

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
    match readInterval E (Reg.real64 (1 + j)) with
    | some t =>
      if t.width != .w64 || t.semanticBits != 64 then throw .undefinedSrc
      args := args ++ [solve t]
    | none =>
      if j < helperRequired kind then throw .undefinedSrc else break
  pure ⟨kind, id, args⟩

/-- Freeze complete current key/value buffers from one pre-call snapshot.
An unavailable layout or byte keeps the ABI prefix, including for update where
neither tail is appended unless both complete buffers are available. -/
def freezeHelperArgs (E : List Expr) (call : HelperCall)
    (preds : List Predicate := []) : List Term :=
  let frozen : Option (List Term) := do
    match call.kind, call.args with
    | .lookup, [map, keyPtr] | .delete, [map, keyPtr] =>
      let layout ← Anchor.layout? E map
      availableBufferBytes E keyPtr layout.keySize preds
    | .update, [map, keyPtr, valuePtr, _flags] =>
      let layout ← Anchor.layout? E map
      let key ← availableBufferBytes E keyPtr layout.keySize preds
      let value ← availableBufferBytes E valuePtr layout.valueSize preds
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

/-- Lookup records r0. The value interval is a separate map equality. -/
def helperExpr (event : NodeId) (call : HelperCall) : List Expr :=
  (update ⟨Expr.nil, []⟩ { exprs := [Expr.mkEq (Reg.real64 0) (solve (callReturnTerm event call))], predicates := [] }).exprs

/-- Anchor the lookup return at value offset zero when the frozen key is complete. -/
def lookupAnchor (E : List Expr) (event : NodeId) (call : HelperCall)
    (frozen : List Term) : Except RejectReason (List Expr) := do
  if call.kind != .lookup then return []
  match frozen with
  | map :: _keyPtr :: key =>
    match Anchor.layout? E map, eval (solve map) with
    | none, _ | _, none => pure []
    | some layout, some id =>
      if key.length != layout.keySize || layout.valueSize == 0 then return []
      let bits := 8 * min layout.valueSize 8
      let some key := key.mapM mapWriteKeyByte | throw .undefinedSrc
      let value := Term.regVar event (Reg.real64 0)
      match ((«seal» (Reg.map id key 0 bits).bits value >>= fun stored => some [Expr.mkEq (.map id key 0 bits) stored])) with
      | some rows => pure rows
      | none => throw .localReject
  | _ => pure []

#guard match parseHelperCall Expr.nil 1 with
  | .error .undefinedSrc => true
  | _ => false
#guard match parseHelperCall Expr.nil 999 with
  | .ok call => call.kind == .unsupported 999 && call.args.isEmpty &&
      callReturnTerm 7 call == Term.C64 18446744073709551615
  | _ => false
#guard match parseHelperCall
    ((update ⟨Expr.nil, []⟩ { exprs := [Expr.mkEq (Reg.real64 1) (solve (Term.V64 1))], predicates := [] }).exprs
      |> (fun acc => (update ⟨acc, []⟩ { exprs := [Expr.mkEq (Reg.real64 2) (solve (Term.C64 10))], predicates := [] }).exprs)) 6 with
  | .ok call => call.kind == .printk && call.args == [Term.V64 1, Term.C64 10]
  | _ => false
#guard match parseHelperCall
    ((update ⟨Expr.nil, []⟩ { exprs := [Expr.mkEq (Reg.real64 1) (solve (Term.V64 1))], predicates := [] }).exprs
      |> (fun acc => (update ⟨acc, []⟩ { exprs := [Expr.mkEq (Reg.real32 2) (solve (Term.C32 10))], predicates := [] }).exprs)
      |> (fun acc => (update ⟨acc, []⟩ { exprs := [Expr.mkEq (.real 2 32 64) (solve (Term.C32 0))], predicates := [] }).exprs)) 6 with
  | .ok call => call.kind == .printk && call.args.length == 2 &&
      eval (solve call.args[1]!) == some 10
  | _ => false
#guard match parseHelperCall
    ((update ⟨Expr.nil, []⟩ { exprs := [Expr.mkEq (Reg.real64 1) (solve (Term.V64 3))], predicates := [] }).exprs
      |> (fun acc => (update ⟨acc, []⟩ { exprs := [Expr.mkEq (Reg.real64 2) (solve (Term.V64 4))], predicates := [] }).exprs)) 1 with
  | .ok call => call.args == [Term.V64 3, Term.V64 4] &&
      (helperExpr 7 call).lookupEq (Reg.real64 0) ==
        some (callReturnTerm 7 call) &&
      !(helperExpr 7 call).any fun e => match e.reg with | .map .. => true | _ => false
  | _ => false

private def stackWord (E : List Expr) (bit value : Nat) : Option (List Expr) :=
  ((«seal» (Reg.stack bit (bit + 32)).bits (Term.C32 value) >>= fun stored => some (update ⟨E, []⟩ { exprs := [Expr.mkEq (.stack bit (bit + 32)) stored], predicates := [] }).exprs))

#guard Id.run do
  let p : EntryParams := ⟨Term.V64 1, Term.V64 0, Term.V32 2, 64⟩
  let keyPtr := addStar .w64 p.tSp (Term.C64 (M 64 (-4)))
  let call : HelperCall := ⟨.lookup, 1, [Term.C64 42, keyPtr]⟩
  let maps : List MapLayout := [⟨42, 4, 8⟩]
  let bare := host p Expr.nil maps
  let some seeded := stackWord bare (508 * 8) 0x11223344 | return false
  let args := freezeHelperArgs seeded call
  return args == call.args ++ [Term.C64 0x44, Term.C64 0x33, Term.C64 0x22, Term.C64 0x11] &&
    args.all (fun t => t.width == .w64) &&
    freezeHelperArgs bare call == call.args &&
    freezeHelperArgs (host p Expr.nil) call == call.args

private def helperMutationFreezeCheck : Bool := Id.run do
  let p : EntryParams := ⟨Term.V64 1, Term.V64 0, Term.V32 2, 64⟩
  let keyPtr := addStar .w64 p.tSp (Term.C64 (M 64 (-4)))
  let valuePtr := addStar .w64 p.tSp (Term.C64 (M 64 (-12)))
  let maps : List MapLayout := [⟨42, 4, 8⟩]
  let update : HelperCall := ⟨.update, 2, [Term.C64 42, keyPtr, valuePtr, Term.C64 0]⟩
  let delete : HelperCall := ⟨.delete, 3, [Term.C64 42, keyPtr]⟩
  let bare := host p Expr.nil maps
  let some seeded := stackWord bare (508 * 8) 0x04030201 | return false
  let some seeded := stackWord seeded (500 * 8) 0x08070605 | return false
  let some seeded := stackWord seeded (504 * 8) 0x0c0b0a09 | return false
  let some missing := stackWord bare (508 * 8) 0x04030201 | return false
  let key := [Term.C64 1, Term.C64 2, Term.C64 3, Term.C64 4]
  let value := [Term.C64 5, Term.C64 6, Term.C64 7, Term.C64 8,
    Term.C64 9, Term.C64 10, Term.C64 11, Term.C64 12]
  return freezeHelperArgs seeded update == update.args ++ key ++ value &&
    freezeHelperArgs seeded delete == delete.args ++ key &&
    freezeHelperArgs missing update == update.args &&
    callReturnTerm 9 update ==
      star .w64 (.externalResult 9 0) (Term.C64 2 :: update.args)

private def existingBufferKindsCheck : Bool := Id.run do
  let p : EntryParams := ⟨Term.V64 1, Term.V64 0, Term.C32 0x1000, 64⟩
  let .ok initial := buildE0 p | return false
  let mapPtr := star .w64 (.externalResult 7 0) [Term.C64 1, Term.C64 42, Term.V64 9]
  let maps : List MapLayout := [⟨42, 4, 8⟩]
  let key := [Term.C64 9, Term.C64 9, Term.C64 9, Term.C64 9]
  let some keyBytes := key.mapM mapWriteKeyByte | return false
  let lookup := Predicate.helper 7 .lookup ([Term.C64 42, Term.V64 9] ++ key)
  let E := host p initial.exprs maps
  let some seeded := ((«seal» (Reg.map 42 keyBytes 0 32).bits (Term.C32 0x04030201) >>= fun stored => some (update ⟨E, []⟩ { exprs := [Expr.mkEq (.map 42 keyBytes 0 32) stored], predicates := [] }).exprs)) | return false
  let some seeded := ((«seal» (Reg.packet 0 32).bits (Term.C32 0x08070605) >>= fun stored => some (update ⟨seeded, []⟩ { exprs := [Expr.mkEq (.packet 0 32) stored], predicates := [] }).exprs)) | return false
  let mapCall : HelperCall := ⟨.delete, 3, [Term.C64 42, mapPtr]⟩
  let packetCall : HelperCall := ⟨.lookup, 1, [Term.C64 42, Term.C64 0x1000]⟩
  let contextCall : HelperCall := ⟨.delete, 3, [Term.C64 42, p.tCtx]⟩
  let openPacket := freezeHelperArgs E packetCall
  let some openBytes := availableBufferBytes E (Term.C64 0x1000) 4 | return false
  return freezeHelperArgs seeded mapCall [lookup] ==
      mapCall.args ++ [Term.C64 1, Term.C64 2, Term.C64 3, Term.C64 4] &&
    freezeHelperArgs seeded packetCall ==
      packetCall.args ++ [Term.C64 5, Term.C64 6, Term.C64 7, Term.C64 8] &&
    openPacket == packetCall.args ++ openBytes &&
    openBytes.length == 4 &&
    freezeHelperArgs E contextCall ==
      contextCall.args ++ [Term.C64 0, Term.C64 16, Term.C64 0, Term.C64 0] &&
    (availableBufferBytes seeded mapPtr 9 [lookup]).isNone

#guard helperMutationFreezeCheck
#guard existingBufferKindsCheck

private def narrowLookupAnchorCheck : Bool := Id.run do
  let p : EntryParams := ⟨Term.V64 1, Term.V64 0, Term.V32 2, 64⟩
  let key := [Term.C64 1, Term.C64 2, Term.C64 3, Term.C64 4]
  let some keyBytes := key.mapM mapWriteKeyByte | return false
  let call : HelperCall := ⟨.lookup, 1, [Term.C64 42, Term.V64 9]⟩
  let narrow := host p Expr.nil [⟨42, 4, 4⟩]
  let wide := host p Expr.nil [⟨42, 4, 8⟩]
  let has (rows : List Expr) (bits : Nat) :=
    rows.any fun e => e.reg == .map 42 keyBytes 0 bits
  match lookupAnchor narrow 7 call (call.args ++ key),
      lookupAnchor wide 7 call (call.args ++ key) with
  | .ok narrowRows, .ok wideRows => has narrowRows 32 && has wideRows 64
  | _, _ => false

#guard narrowLookupAnchorCheck

end EBPF
