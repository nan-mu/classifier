import Cross.RV32.Expression
import Observation.Helper
import Interface.Update
import Node.Path

namespace Cross.RV32
open Term Term.Value Expression Observation Interface Node

structure HelperCall where
  kind : HelperKind
  id : Nat
  args : List Term
  deriving Repr

def helperConvention (bound : Option Term) : HelperConvention where
  width := .w32
  returnReg := Reg.real32 10
  readBytes := fun E addr n => readBufferBytes E addr n bound
  keyByte := mapKeyByte
  anchorBits := fun n => if n < 4 then none else some 32

def parseHelperCall (Eg : List Expr) : Except RejectReason HelperCall := do
  if !guardEg Eg then throw .localReject
  let some idTerm := readInterval Eg (Reg.real32 10) | throw .undefinedSrc
  if idTerm.width != .w32 then throw .undefinedSrc
  let some id := eval (solve idTerm) | throw .unsupported
  let kind := helperKind id
  let mut args := []
  for j in [:helperArity kind] do
    match readInterval Eg (Reg.real32 (11 + j)) with
    | some t =>
      if t.width != .w32 then throw .undefinedSrc
      args := args ++ [solve t]
    | none =>
      if j < helperRequired kind then throw .undefinedSrc else break
  pure ⟨kind, id, args⟩

/-- Snapshot, return term in a0, and the lookup anchor.
An unreadable buffer keeps the ABI arguments and does not reject the call. -/
def helperCandidates (event : Nat) (E : List Expr) (bound : Option Term) :
    Except RejectReason (List Expr × Observation) := do
  let call ← parseHelperCall E
  let conv := helperConvention bound
  let snapshot ← match freezeSnapshot conv E call.kind call.args with
    | .snap args | .abi args => pure args
    | .incomplete => throw .undefinedSrc
  let anchor := match freezeSnapshot conv E call.kind call.args with
    | .snap snap => (lookupAnchor conv event E call.kind call.id snap).getD []
    | _ => []
  let ret := callReturnTerm conv event E call.kind call.id snapshot
  let written := (update ⟨Expr.nil, []⟩
    { exprs := [Expr.mkEq (Reg.real32 10) (solve ret)], predicates := [] }).exprs
  pure (written ++ anchor, .helper event call.kind snapshot)

end Cross.RV32
