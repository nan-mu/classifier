import RV32IMC.Initial
import RV32IMC.Expr
import CommonMath.Path

namespace RV32IMC
open CommonMath

inductive HelperKind where
  | lookup | update | delete | clock | printk | checksum | adjustTail
  | unsupported (id : Nat)
  deriving BEq, Repr

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
  let some idTerm := Eg.lookupEq (Reg.real32 10) | throw .undefinedSrc
  let some id := eval (solve idTerm) | throw .unsupported
  let kind := helperKind id
  let mut args := []
  for j in [:helperArity kind] do
    let some t := Eg.lookupEq (Reg.real32 (11 + j)) | throw .undefinedSrc
    if t.width != .w32 then throw .undefinedSrc
    args := args ++ [t]
  pure ⟨kind, id, args⟩

def helperExpr (event : NodeId) (call : HelperCall) (p : EntryParams)
    (Eg : ExprSet) : ExprSet := Id.run do
  let external := fun lane => star .w32 (.externalResult event lane)
    (Term.C32 call.id :: call.args)
  let result := match call.kind with
    | .unsupported _ => Term.C32 ((1 <<< 32) - 1)
    | .checksum => star .w32 (.low 16 32) [external 0]
    | _ => external 0
  let mut E := ExprSet.empty.insertEq (Reg.real32 10) result
  for r in [5, 6, 7, 11, 12, 13, 14, 15, 16, 17, 28, 29, 30, 31] do
    E := E.insertEq (Reg.real32 r) (external r)
  if call.kind == .adjustTail then
    let slot := Reg.sw (p.αCtx + 1)
    if (Eg.lookupEq slot).isSome then
      E := E.insertEq slot (external 33)
  pure E

def helperPredicates (_call : HelperCall) (_pre _result : ExprSet) : List Predicate := []

#guard [1, 2, 3, 5, 6, 28, 65].map (fun id => helperArity (helperKind id)) == [2, 4, 2, 0, 5, 5, 2]
#guard helperArity (helperKind 999) == 0
#guard (eval (star .w32 (.externalResult 0 0) [Term.C32 5])).isNone
#guard solve (star .w32 (.externalResult 0 0) [Term.C32 5]) ==
  star .w32 (.externalResult 0 0) [Term.C32 5]

end RV32IMC
