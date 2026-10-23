import Core.Anchor
import Core.Update
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

/-- Byte-valued frozen key/value tail after the ABI prefix. -/
private def frozenTailOk (tail : List Term) : Bool :=
  tail.all fun t =>
    t.width == .w32 &&
      match t with
      | .const _ c => c < 256
      | _ => true

/-- Resolve layout and every required buffer before appending any frozen bytes. -/
private def freezeMapTail (Eg : List Expr) (boundCtx : Option Term)
    (preds : List Predicate) (kind : HelperKind) (args : List Term) : Option (List Term) := do
  let map ← args.head?
  let layout ← Anchor.layout? Eg map
  match kind, args with
  | .lookup, [_, keyPtr] | .delete, [_, keyPtr] =>
      readBufferBytes Eg keyPtr layout.keySize boundCtx preds
  | .update, [_, keyPtr, valuePtr, _] => do
      let key ← readBufferBytes Eg keyPtr layout.keySize boundCtx preds
      let value ← readBufferBytes Eg valuePtr layout.valueSize boundCtx preds
      some (key ++ value)
  | _, _ => none

/-- ABI observation survives an undefined complete-buffer refinement unchanged. -/
def helperPredicate (event : NodeId) (Eg : List Expr)
    (boundCtx : Option Term := none)
    (preds : List Predicate := []) : Except RejectReason Predicate := do
  let call ← parseHelperCall Eg
  let args := match freezeMapTail Eg boundCtx preds call.kind call.args with
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
def helperMapWrites (E : List Expr) (p : Predicate) : Except RejectReason (List Expr) := do
  let (event, call) ← helperCallOfPredicate p
  if call.kind != .lookup then return []
  match p with
  | .helper _ .lookup (map :: _keyPtr :: key) =>
    match Anchor.layout? E map, eval (solve map) with
    | some layout, some id =>
      if key.length != layout.keySize || layout.valueSize < 4 then return []
      let some key := key.mapM mapKeyByte | return []
      let value := Term.regVar event (Reg.real32 10)
      match ((«seal» (Reg.map id key 0 32).bits value >>= fun stored => some [Expr.mkEq (.map id key 0 32) stored])) with
      | some rows => pure rows
      | none => throw .localReject
    | _, _ => pure []
  | _ => pure []

/-- The helper value projection writes a0. The lookup value is a memory write. -/
def helperExpr (p : Predicate) : Except RejectReason (List Expr) := do
  let result ← callReturnTerm p
  pure ((update ⟨Expr.nil, []⟩ { exprs := [Expr.mkEq (Reg.real32 10) (solve result)], predicates := [] }).exprs)

#guard [1, 2, 3, 5, 6, 28, 65].map (fun id => helperArity (helperKind id)) == [2, 4, 2, 0, 5, 5, 2]
#guard helperArity (helperKind 999) == 0
#guard (eval (star .w32 (.externalResult 0 0) [Term.C32 5])).isNone
#guard solve (star .w32 (.externalResult 0 0) [Term.C32 5]) ==
  star .w32 (.externalResult 0 0) [Term.C32 5]
#guard match helperExpr (.ret (Term.V32 1)) with
  | .error .unsupported => true
  | _ => false

private def putXdp (E : List Expr) (fields : List Term) : Option (List Expr) := do
  let mut out := E
  for (j, t) in xdpFields.zip fields do
    out ← putContext out j t
  some out

private def byteTerm (c : Nat) : Term :=
  star .w32 (.low 8 32) [Term.C32 c]

private def completeMapBuffersCheck : Bool := Id.run do
  let key := addStar .w32 (Term.V32 0) (Term.C32 3)
  let value := addStar .w32 (Term.V32 4) (Term.C32 1)
  let data := Term.V32 4
  let fields := [data, addStar .w32 data (Term.C32 8), Term.C32 0, Term.C32 0,
    Term.C32 0, Term.C32 0]
  let some built := putXdp Expr.nil fields | return false
  let some built := ((«seal» (Reg.stack 0 32).bits (Term.C32 0x04030201) >>= fun stored => some (update ⟨built, []⟩ { exprs := [Expr.mkEq (.stack 0 32) stored], predicates := [] }).exprs)) | return false
  let some built := ((«seal» (Reg.stack 32 64).bits (Term.C32 0x08070605) >>= fun stored => some (update ⟨built, []⟩ { exprs := [Expr.mkEq (.stack 32 64) stored], predicates := [] }).exprs)) | return false
  let some built := ((«seal» (Reg.packet 8 16).bits (byteTerm 0xaa) >>= fun stored => some (update ⟨built, []⟩ { exprs := [Expr.mkEq (.packet 8 16) stored], predicates := [] }).exprs)) | return false
  let some built := ((«seal» (Reg.packet 16 24).bits (byteTerm 0xbb) >>= fun stored => some (update ⟨built, []⟩ { exprs := [Expr.mkEq (.packet 16 24) stored], predicates := [] }).exprs)) | return false
  let some E := Anchor.installMaps (built
    |> (fun acc => (update ⟨acc, []⟩ { exprs := [Expr.mkEq (Reg.real32 2) (solve (Term.V32 0))], predicates := [] }).exprs)
    |> (fun acc => (update ⟨acc, []⟩ { exprs := [Expr.mkEq (Reg.real32 11) (solve (Term.C32 42))], predicates := [] }).exprs)
    |> (fun acc => (update ⟨acc, []⟩ { exprs := [Expr.mkEq (Reg.real32 12) (solve key)], predicates := [] }).exprs)
    |> (fun acc => (update ⟨acc, []⟩ { exprs := [Expr.mkEq (Reg.real32 13) (solve value)], predicates := [] }).exprs)
    |> (fun acc => (update ⟨acc, []⟩ { exprs := [Expr.mkEq (Reg.real32 14) (solve (Term.C32 0))], predicates := [] }).exprs))
    [{ mapId := 42, keySize := 3, valueSize := 2 }] | return false
  for (id, kind, abi, tail) in [
      (1, HelperKind.lookup, [Term.C32 42, key], [Term.C32 4, Term.C32 5, Term.C32 6]),
      (3, HelperKind.delete, [Term.C32 42, key], [Term.C32 4, Term.C32 5, Term.C32 6]),
      (2, HelperKind.update, [Term.C32 42, key, value, Term.C32 0],
        [Term.C32 4, Term.C32 5, Term.C32 6, Term.C32 0xaa, Term.C32 0xbb])] do
    let state := (update ⟨E, []⟩ { exprs := [Expr.mkEq (Reg.real32 10) (solve (Term.C32 id))], predicates := [] }).exprs
    let .ok p := helperPredicate 70 state | return false
    if p != .helper 70 kind (abi ++ tail) then return false
    let .ok result := helperExpr p | return false
    if result.lookupEq (Reg.real32 10) !=
        some (star .w32 (.externalResult 70 0) (Term.C32 id :: abi)) then return false
    let some changed := ((«seal» (Reg.stack 32 64).bits (Term.C32 0) >>= fun stored => some (update ⟨state, []⟩ { exprs := [Expr.mkEq (.stack 32 64) stored], predicates := [] }).exprs)) | return false
    let .ok fresh := helperPredicate 71 changed | return false
    if fresh != .helper 71 kind
        (abi ++ [Term.C32 4, Term.C32 0, Term.C32 0] ++ tail.drop 3) then return false
  let update := (update ⟨E, []⟩ { exprs := [Expr.mkEq (Reg.real32 10) (solve (Term.C32 2))], predicates := [] }).exprs
  let abiPrefix := [Term.C32 42, key, value, Term.C32 0]
  let missingStack := update.filter fun e => e.reg != .stack 32 64
  let .ok incompletePredicate := helperPredicate 70 missingStack | return false
  let openPacket := update.filter fun e => match e.reg with | .packet .. => false | _ => true
  let .ok openPredicate := helperPredicate 70 openPacket | return false
  let some openTail := readBufferBytes openPacket value 2 | return false
  return incompletePredicate == .helper 70 .update abiPrefix &&
    (readBufferBytes missingStack key 3).isNone &&
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
  let some sourceBytes := sourceKey.mapM mapKeyByte | return false
  let some buffers := ((«seal» (Reg.stack 0 32).bits (Term.C32 0x04030201) >>= fun stored => some (update ⟨Expr.nil, []⟩ { exprs := [Expr.mkEq (.stack 0 32) stored], predicates := [] }).exprs)) | return false
  let some buffers := ((«seal» (Reg.map 17 sourceBytes 0 32).bits (Term.C32 0x04030201) >>= fun stored => some (update ⟨buffers, []⟩ { exprs := [Expr.mkEq (.map 17 sourceBytes 0 32) stored], predicates := [] }).exprs)) | return false
  let some buffers := ((«seal» (Reg.map 17 sourceBytes 32 64).bits (Term.C32 0x08070605) >>= fun stored => some (update ⟨buffers, []⟩ { exprs := [Expr.mkEq (.map 17 sourceBytes 32 64) stored], predicates := [] }).exprs)) | return false
  let prior : List Predicate :=
    [.helper 9 .lookup ([Term.C32 17, Term.V32 7] ++ sourceKey)]
  let bare := buffers
    |> (fun acc => (update ⟨acc, []⟩ { exprs := [Expr.mkEq (Reg.real32 2) (solve key)], predicates := [] }).exprs)
    |> (fun acc => (update ⟨acc, []⟩ { exprs := [Expr.mkEq (Reg.real32 11) (solve (Term.C32 42))], predicates := [] }).exprs)
    |> (fun acc => (update ⟨acc, []⟩ { exprs := [Expr.mkEq (Reg.real32 14) (solve (Term.C32 0))], predicates := [] }).exprs)
  let unknown := star .w32 (.externalResult 9 0) [Term.C32 1, Term.V32 17, Term.V32 7]
  let wrapped := addStar .w32 pointer (Term.C32 ((1 <<< 32) - 1))
  for (id, kind) in [(1, HelperKind.lookup), (3, HelperKind.delete),
      (2, HelperKind.update)] do
    let bufferReg := if id == 2 then Reg.real32 13 else Reg.real32 12
    let abi := if id == 2 then [Term.C32 42, key, atEnd, Term.C32 0]
      else [Term.C32 42, atEnd]
    let tail := if id == 2 then [Term.C32 1, Term.C32 2, Term.C32 3,
      Term.C32 4, Term.C32 5, Term.C32 6] else [Term.C32 4, Term.C32 5, Term.C32 6]
    let placed := (update ⟨bare, []⟩ { exprs := [Expr.mkEq (Reg.real32 10) (solve (Term.C32 id))], predicates := [] }).exprs
      |> (fun acc => (update ⟨acc, []⟩ { exprs := [Expr.mkEq (Reg.real32 12) (solve (if id == 2 then key else atEnd))], predicates := [] }).exprs)
      |> (fun acc => (update ⟨acc, []⟩ { exprs := [Expr.mkEq (Reg.real32 13) (solve atEnd)], predicates := [] }).exprs)
    let some state := Anchor.installMaps placed maps | return false
    let .ok frozen := helperPredicate 70 state (preds := prior) | return false
    if frozen != .helper 70 kind (abi ++ tail) then return false
    let .ok result := helperExpr frozen | return false
    if result.lookupEq (Reg.real32 10) !=
        some (star .w32 (.externalResult 70 0) (Term.C32 id :: abi)) then return false
    for layouts in [[target], [{ source with valueSize := 5 }]] do
      let some variant := Anchor.installMaps placed layouts | return false
      let .ok abiPrefix := helperPredicate 70 variant (preds := prior) | return false
      if abiPrefix != .helper 70 kind abi then return false
    for address in [beyondEnd, unknown, wrapped] do
      let changed := (update ⟨state, []⟩ { exprs := [Expr.mkEq bufferReg (solve address)], predicates := [] }).exprs
      let expected := if id == 2 then [Term.C32 42, key, address, Term.C32 0]
        else [Term.C32 42, address]
      let .ok abiPrefix := helperPredicate 70 changed (preds := prior) | return false
      if abiPrefix != .helper 70 kind expected then return false
    if id == 2 then
      let changed := (update ⟨state, []⟩ { exprs := [Expr.mkEq (Reg.real32 12) (solve beyondEnd)], predicates := [] }).exprs
      let .ok abiPrefix := helperPredicate 70 changed (preds := prior) | return false
      if abiPrefix != .helper 70 kind [Term.C32 42, beyondEnd, atEnd, Term.C32 0] then
        return false
  return true

#guard mapBufferBoundsCheck

end RV32
