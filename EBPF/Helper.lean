import EBPF.Memory

namespace EBPF
open ClassifierExpr PathMerge

/-- Native ABI prefix: immediate helper id, r1 through rn at full width. -/
structure HelperCall where
  kind : HelperKind
  id : Nat
  args : List Term
  deriving Repr

def parseHelperCall (E : ExprSet) (id : Nat) : Except RejectReason HelperCall := do
  if !E.keysUnique || !E.wellTyped then throw .localReject
  let kind := helperKind id
  let mut args := []
  for j in [:helperArity kind] do
    let some t := E.lookupEq (Reg.real64 (1 + j)) | throw .undefinedSrc
    if t.width != .w64 then throw .undefinedSrc
    args := args ++ [solve t]
  pure ⟨kind, id, args⟩

/-- Freeze lookup key bytes when the Meta layout and stack contents are available. -/
def freezeLookupArgs (p : EntryParams) (E : ExprSet) (maps : List MapLayout)
    (call : HelperCall) : List Term :=
  match call.kind, call.args with
  | .lookup, [map, keyPtr] =>
    match findMapLayout maps map with
    | some layout =>
      match stackBytes p E keyPtr layout.keySize with
      | some bytes => call.args ++ bytes
      | none => call.args
    | none => call.args
  | _, _ => call.args

/-- Only ABI arguments, not the frozen observation tail, determine the return. -/
def callReturnTerm (event : NodeId) (call : HelperCall) : Term :=
  let external := star .w64 (.externalResult event 0) (Term.C64 call.id :: call.args)
  match call.kind with
  | .checksum => star .w64 (.low 16 64) [external]
  | .unsupported _ => Term.C64 ((1 <<< 64) - 1)
  | _ => external

/-- Lookup anchors Map word zero in its event namespace to the return register. -/
def helperExpr (event : NodeId) (call : HelperCall) : ExprSet :=
  let result := ExprSet.empty.insertEq (Reg.real64 0) (callReturnTerm event call)
  let map := if call.kind == .lookup then
    ExprSet.empty.insertEq (Reg.mapDword event 0) (Term.regVar event (Reg.real64 0))
    else ExprSet.empty
  updateExpr result map

#guard match parseHelperCall ExprSet.empty 1 with
  | .error .undefinedSrc => true
  | _ => false
#guard match parseHelperCall ExprSet.empty 999 with
  | .ok call => call.kind == .unsupported 999 && call.args.isEmpty &&
      callReturnTerm 7 call == Term.C64 18446744073709551615
  | _ => false
#guard match parseHelperCall
    (ExprSet.empty.insertEq (Reg.real64 1) (Term.V64 3)
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
  let E := ExprSet.empty.insertEq (stackUnitReg 0 0) (Term.C32 0x11223344)
  let args := freezeLookupArgs p E maps call
  return args == call.args ++ [Term.C64 0x44, Term.C64 0x33, Term.C64 0x22, Term.C64 0x11] &&
    args.all (fun t => t.width == .w64) &&
    freezeLookupArgs p ExprSet.empty maps call == call.args &&
    freezeLookupArgs p E [] call == call.args

end EBPF
