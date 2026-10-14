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

/-- Append frozen key bytes when Meta layout and stack provenance allow; otherwise keep ABI args. -/
private def freezeLookupArgs (Eg : ExprSet) (maps : List MapLayout) (args : List Term) :
    List Term :=
  match args with
  | [map, keyPtr] =>
    match findMapLayout maps map with
    | some layout =>
      match readStackBytes Eg keyPtr layout.keySize with
      | some bytes =>
        if bytes.length == layout.keySize && frozenTailOk bytes then args ++ bytes else args
      | none => args
    | none => args
  | _ => args

/-- Capture the dispatcher type and ABI args; lookup may append frozen key bytes from Meta. -/
def helperPredicate (event : NodeId) (Eg : ExprSet) (maps : List MapLayout := []) :
    Except RejectReason Predicate := do
  let call ← parseHelperCall Eg
  let args := match call.kind with
    | .lookup => freezeLookupArgs Eg maps call.args
    | _ => call.args
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

end RV32IMC
