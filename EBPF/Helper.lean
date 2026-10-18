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
def freezeHelperArgs (E : List Expr) (call : HelperCall) : List Term :=
  let frozen : Option (List Term) := do
    match call.kind, call.args with
    | .lookup, [map, keyPtr] | .delete, [map, keyPtr] =>
      let layout ← Anchor.layout? E map
      availableBufferBytes E keyPtr layout.keySize
    | .update, [map, keyPtr, valuePtr, _flags] =>
      let layout ← Anchor.layout? E map
      let key ← availableBufferBytes E keyPtr layout.keySize
      let value ← availableBufferBytes E valuePtr layout.valueSize
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

/-- Lookup anchors Map word zero in its event namespace to the return register. -/
def helperExpr (event : NodeId) (call : HelperCall) : List Expr :=
  let result := Expr.nil.insertEq (Reg.real64 0) (callReturnTerm event call)
  let map := if call.kind == .lookup then
    Expr.nil.insertEq (Reg.mapDword event 0) (Term.regVar event (Reg.real64 0))
    else Expr.nil
  updateExpr result map

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
      (helperExpr 7 call).lookupEq (Reg.mapDword 7 0) ==
        some (Term.regVar 7 (Reg.real64 0))
  | _ => false
#guard Id.run do
  let p : EntryParams := ⟨Term.V64 1, Term.V64 0, Term.V32 2, 64, 0, 0, 0⟩
  let keyPtr := addStar .w64 p.tSp (Term.C64 (M 64 (-4)))
  let call : HelperCall := ⟨.lookup, 1, [Term.C64 42, keyPtr]⟩
  let maps : List MapLayout := [⟨42, 4, 8⟩]
  let E := host p (Expr.nil.insertEq (stackUnitReg 0 0) (Term.C32 0x11223344)) maps
  let args := freezeHelperArgs E call
  return args == call.args ++ [Term.C64 0x44, Term.C64 0x33, Term.C64 0x22, Term.C64 0x11] &&
    args.all (fun t => t.width == .w64) &&
    freezeHelperArgs (host p Expr.nil maps) call == call.args &&
    freezeHelperArgs (host p (Expr.nil.insertEq (stackUnitReg 0 0) (Term.C32 0x11223344))) call ==
      call.args

private def helperMutationFreezeCheck : Bool := Id.run do
  let p : EntryParams := ⟨Term.V64 1, Term.V64 0, Term.V32 2, 64, 0, 0, 0⟩
  let keyPtr := addStar .w64 p.tSp (Term.C64 (M 64 (-4)))
  let valuePtr := addStar .w64 p.tSp (Term.C64 (M 64 (-12)))
  let maps : List MapLayout := [⟨42, 4, 8⟩]
  let update : HelperCall := ⟨.update, 2, [Term.C64 42, keyPtr, valuePtr, Term.C64 0]⟩
  let delete : HelperCall := ⟨.delete, 3, [Term.C64 42, keyPtr]⟩
  let E := host p (Expr.nil.insertEq (stackUnitReg 0 0) (Term.C32 0x04030201)
    |>.insertEq (stackUnitReg 0 2) (Term.C32 0x08070605)
    |>.insertEq (stackUnitReg 0 1) (Term.C32 0x0c0b0a09)) maps
  let key := [Term.C64 1, Term.C64 2, Term.C64 3, Term.C64 4]
  let value := [Term.C64 5, Term.C64 6, Term.C64 7, Term.C64 8,
    Term.C64 9, Term.C64 10, Term.C64 11, Term.C64 12]
  let missing := host p (Expr.nil.insertEq (stackUnitReg 0 0) (Term.C32 0x04030201)) maps
  return freezeHelperArgs E update == update.args ++ key ++ value &&
    freezeHelperArgs E delete == delete.args ++ key &&
    freezeHelperArgs missing update == update.args &&
    callReturnTerm 9 update ==
      star .w64 (.externalResult 9 0) (Term.C64 2 :: update.args)

private def existingBufferKindsCheck : Bool := Id.run do
  let p : EntryParams := ⟨Term.V64 1, Term.V64 0, Term.C32 0x1000, 64, 0, 0, 0⟩
  let .ok initial := buildE0 p | return false
  let mapPtr := star .w64 (.externalResult 7 0) [Term.C64 1, Term.C64 42, Term.V64 9]
  let maps : List MapLayout := [⟨42, 4, 8⟩]
  let E := host p (initial.exprs.insertEq (Reg.mapDword 7 0) (Term.C64 0x04030201)
    |>.insertEq (Reg.packet 0 0) (Term.C32 5)
    |>.insertEq (Reg.packet 0 1) (Term.C32 6)
    |>.insertEq (Reg.packet 0 2) (Term.C32 7)
    |>.insertEq (Reg.packet 0 3) (Term.C32 8)) maps
  let seeded := host p initial.exprs maps
  let mapCall : HelperCall := ⟨.delete, 3, [Term.C64 42, mapPtr]⟩
  let packetCall : HelperCall := ⟨.lookup, 1, [Term.C64 42, Term.C64 0x1000]⟩
  let contextCall : HelperCall := ⟨.delete, 3, [Term.C64 42, p.tCtx]⟩
  let openPacket := freezeHelperArgs seeded packetCall
  let some openBytes := availableBufferBytes seeded (Term.C64 0x1000) 4 | return false
  return freezeHelperArgs E mapCall ==
      mapCall.args ++ [Term.C64 1, Term.C64 2, Term.C64 3, Term.C64 4] &&
    freezeHelperArgs E packetCall ==
      packetCall.args ++ [Term.C64 5, Term.C64 6, Term.C64 7, Term.C64 8] &&
    openPacket == packetCall.args ++ openBytes &&
    openBytes.length == 4 &&
    freezeHelperArgs E contextCall ==
      contextCall.args ++ [Term.C64 0, Term.C64 16, Term.C64 0, Term.C64 0] &&
    (availableBufferBytes E mapPtr 9).isNone

#guard helperMutationFreezeCheck
#guard existingBufferKindsCheck

end EBPF
