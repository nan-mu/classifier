import RV32IMC.Initial
import RV32IMC.Expr
import CommonMath.Path

namespace RV32IMC
open CommonMath

abbrev HelperKind := CommonMath.HelperKind

structure HelperCall where
  kind : HelperKind
  id : Nat
  args : List Term
  deriving Repr

def helperKind (id : Nat) : HelperKind :=
  match id with
  | 1 => .lookup | 2 => .update | 3 => .delete | 5 => .clock
  | 6 => .printk | 28 => .checksum | 65 => .adjustTail
  | n => .unsupported n

def helperArity : HelperKind → Nat
  | .lookup | .delete | .adjustTail => 2
  | .update => 4
  | .printk | .checksum => 5
  | .clock | .unsupported _ => 0

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

/-- Capture the dispatcher type and its required arguments before the call writes a0. -/
def helperPredicate (event : NodeId) (Eg : ExprSet) : Except RejectReason Predicate := do
  let call ← parseHelperCall Eg
  pure (.helper event call.kind call.args)

private def helperCallOfPredicate (p : Predicate) : Except RejectReason (NodeId × HelperCall) := do
  let .helper event kind args := p | throw .localReject
  if kind.id ≥ (1 <<< 32) || helperKind kind.id != kind then throw .unsupported
  if args.length != helperArity kind || args.any (fun t => t.width != .w32) then
    throw .undefinedSrc
  pure (event, ⟨kind, kind.id, args⟩)

def helperResult (p : Predicate) : Except RejectReason Term := do
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
  let result ← helperResult p
  let map ← helperMapExpr p
  pure (updateExpr (ExprSet.empty.insertEq (Reg.real32 10) result) map)

#guard [1, 2, 3, 5, 6, 28, 65].map (fun id => helperArity (helperKind id)) == [2, 4, 2, 0, 5, 5, 2]
#guard helperArity (helperKind 999) == 0
#guard (eval (star .w32 (.externalResult 0 0) [Term.C32 5])).isNone
#guard solve (star .w32 (.externalResult 0 0) [Term.C32 5]) ==
  star .w32 (.externalResult 0 0) [Term.C32 5]

end RV32IMC
