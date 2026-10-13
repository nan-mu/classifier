import EBPF.Initial
import EBPF.Expr
import ClassifierExpr.Virtual

namespace EBPF
open ClassifierExpr PathMerge

inductive ResolvedAccess where
  | cells (parts : List CellAccess)
  | packet (access : PacketAccess)
  deriving Repr, Inhabited

/-- Signed, integral displacement from a fixed entry root. Only identity wrappers
and additions of closed constants establish symbolic aliases. -/
def relativeOffset (root address : Term) : Option Int :=
  if root.width != .w64 || address.width != .w64 then none
  else if address == root then some 0
  else match address with
    | .app .w64 (.id .w64) [a] => relativeOffset root a
    | .app .w64 (.add .w64) [a, b] =>
      match eval (solve b) with
      | some c => (relativeOffset root a).map (· + s 64 c)
      | none => do
        let c ← eval (solve a)
        let d ← relativeOffset root b
        pure (d + s 64 c)
    | _ => match solve root, solve address with
      | .const .w64 r, .const .w64 a => some (s 64 (M 64 (Int.ofNat a - Int.ofNat r)))
      | _, _ => none
  termination_by sizeOf address

/-- Unit zero starts at tSp-4. A fixed stride is injective because unit < 128. -/
def stackUnitReg (resource unit : Nat) : Reg := Reg.sw (128 * resource + unit)

private def contextParts (p : EntryParams) (d : Int) (bytes : Nat) : Option ResolvedAccess :=
  if d ≥ 0 && d.toNat % 4 == 0 && d.toNat / 4 < 2 && bytes == 4 then
    some (.cells [⟨Reg.ctx32 (p.αCtx + d.toNat / 4), 0, 32⟩])
  else none

private def stackParts (p : EntryParams) (d : Int) (bytes : Nat) : Option ResolvedAccess :=
  if d < -512 || d ≥ 0 || d + Int.ofNat bytes > 0 then none
  else
    let n := (d + 512).toNat
    let within := n % 4
    let unit := 127 - n / 4
    if bytes == 8 then
      if within == 0 && unit > 0 then
        some (.cells [⟨stackUnitReg p.φStack unit, 0, 32⟩,
          ⟨stackUnitReg p.φStack (unit - 1), 0, 32⟩])
      else none
    else if within + bytes ≤ 4 then
      some (.cells [⟨stackUnitReg p.φStack unit, 8 * within, 8 * bytes⟩])
    else none

/-- Packet first reads return newly materialized equalities separately. Cell
reads need current contents and never invent uninitialized stack values. -/
def readAccess (E : ExprSet) (a : ResolvedAccess) : Except RejectReason (ExprSet × Term) := do
  match a with
  | .packet access =>
    let some result := access.read E .w64 true | throw .undefinedSrc
    pure (result.inputs, result.value)
  | .cells parts =>
    if parts.isEmpty || parts.foldl (fun n part => n + part.bits) 0 > 64 then
      throw .undefinedSrc
    if let [part] := parts then
      if part.bitOffset == 0 then
        let some value := part.read E .w64 true | throw .undefinedSrc
        return (.empty, value)
    let mut value := Term.C64 0
    let mut shift := 0
    for part in parts do
      let some field := part.read E .w64 true | throw .undefinedSrc
      value := orStar 64 .w64 value (shlStar .w64 field (Term.C64 shift))
      shift := shift + part.bits
    pure (.empty, value)

/-- The packet base is exactly the widened context data cell yielded by LDX W.
Using the same read path prevents drift between classification and loaded aliases.
Missing context data contents authorize no packet candidate. -/
def packetRoot (p : EntryParams) (E : ExprSet) : Option Term := do
  let (_, value) ← (readAccess E (.cells [⟨Reg.ctx32 p.αCtx, 0, 32⟩])).toOption
  pure value

/-- Resolve against the executing full base equality, never against a mutable
entry-register name. Content availability is checked by readAccess/writeAccess. -/
def resolveAccess (p : EntryParams) (E : ExprSet) (base : Nat) (offset : Int)
    (bytes : Nat) (isWrite : Bool) : Except RejectReason ResolvedAccess := do
  let _ := isWrite
  if base > 10 || !E.keysUnique || !E.wellTyped ||
      ![1, 2, 4, 8].contains bytes then throw .undefinedSrc
  let some address := E.lookupEq (Reg.real64 base) | throw .undefinedSrc
  if address.width != .w64 then throw .undefinedSrc
  let mut candidates : List ResolvedAccess := []
  if let some displacement := relativeOffset p.tCtx address then
    if let some a := contextParts p (displacement + offset) bytes then
      candidates := a :: candidates
  if let some displacement := relativeOffset p.tSp address then
    if let some a := stackParts p (displacement + offset) bytes then
      candidates := a :: candidates
  if let some root := packetRoot p E then
    if let some displacement := relativeOffset root address then
      let o := displacement + offset
      if o ≥ 0 && o.toNat + bytes ≤ p.packetBytes then
        candidates := .packet ⟨p.κPacket, o.toNat, bytes, .little, some p.tData⟩ :: candidates
  match candidates with
  | [a] => pure a
  | _ => throw .undefinedSrc

/-- All partial fields read the old snapshot. Whole units, including both halves
of a DW store, require no old cell equality. -/
def writeAccess (E : ExprSet) (a : ResolvedAccess) (source : Term) : Except RejectReason ExprSet := do
  if source.width != .w64 then throw .undefinedSrc
  match a with
  | .packet access =>
    let some updates := access.write E source | throw .undefinedSrc
    pure updates
  | .cells parts =>
    if parts.isEmpty || parts.foldl (fun n part => n + part.bits) 0 > 64 then
      throw .undefinedSrc
    let mut updates := ExprSet.empty
    let mut shift := 0
    for part in parts do
      if (updates.lookupEq part.reg).isSome then throw .undefinedSrc
      let field := if shift == 0 then source else lshrStar .w64 source (Term.C64 shift)
      let some written := part.write E field | throw .undefinedSrc
      updates := updates.override written
      shift := shift + part.bits
    pure updates

/-- Memory effects distinguish first-read inputs from simultaneous assignments.
Packet stores carry their observation with the byte updates, using the same
complete pre-state source. The existing MOV/ADD rules are reused; control flow
and helper classes are refused. -/
def exprEffects (p : EntryParams) (event : NodeId) (E : ExprSet) (i : Insn) :
    Except RejectReason (ExprEffect × List Predicate) := do
  if !E.keysUnique || !E.wellTyped then throw .undefinedSrc
  match i with
  | .ldx bytes dst base offset =>
    if dst > 9 then throw .undefinedSrc
    let access ← resolveAccess p E base offset bytes false
    let (inputs, value) ← readAccess E access
    pure (⟨inputs, ExprSet.empty.insertEq (Reg.real64 dst) value⟩, [])
  | .stx bytes base src offset =>
    if src > 10 then throw .undefinedSrc
    let some source := E.lookupEq (Reg.real64 src) | throw .undefinedSrc
    if source.width != .w64 then throw .undefinedSrc
    let access ← resolveAccess p E base offset bytes true
    let updates ← writeAccess E access source
    let predicates := match access with
      | .packet a => [.packetWrite event a.κ a.offset source]
      | .cells _ => []
    pure (⟨.empty, updates⟩, predicates)
  | .mov _ _ _ | .add _ _ _ =>
    let some updates := expr E i | throw .undefinedSrc
    pure (⟨.empty, updates⟩, [])
  | .exit => pure (⟨.empty, .empty⟩, [])
  | .illegal _ => throw .localReject
  | .jcond _ _ _ _ _ => throw .unsupported
  | .ja _ => throw .unsupported
  | .lddw _ _ _ => throw .unsupported
  | .continuation => throw .unsupported
  | .callHelper _ => throw .unsupported

private def memoryEntry : EntryParams :=
  ⟨Term.V64 1, Term.V64 0, Term.V32 2, 16, 3, 4, 5⟩

#guard relativeOffset memoryEntry.tSp
  (idStar .w64 (addStar .w64 memoryEntry.tSp (Term.C64 (M 64 (-4))))) == some (-4)
#guard match buildE0 memoryEntry with
  | .ok σ => match resolveAccess memoryEntry σ.exprs 10 (-4) 4 false with
    | .ok (.cells [part]) => part.reg == stackUnitReg 5 0 &&
        part.bitOffset == 0 && part.bits == 32
    | _ => false
  | _ => false
#guard match buildE0 memoryEntry with
  | .ok σ => match resolveAccess memoryEntry σ.exprs 1 8 4 false with
    | .error .undefinedSrc => true
    | _ => false
  | _ => false
#guard Id.run do
  let .ok σ := buildE0 memoryEntry | return false
  let .ok (loaded, []) := exprEffects memoryEntry 0 σ.exprs (.ldx 4 2 1 0) | return false
  let E := σ.exprs.override loaded.delta
  let .error .undefinedSrc := resolveAccess memoryEntry E 2 13 4 false | return false
  return true

private def stackRoundTripCheck : Bool := Id.run do
  let .ok σ := buildE0 memoryEntry | return false
  let E := σ.exprs.insertEq (Reg.real64 0) (Term.C64 0x1122334455667788)
  let .ok (stored, []) := exprEffects memoryEntry 0 E (.stx 8 10 0 (-8)) | return false
  let next := E.override stored.delta
  let .ok (loaded, []) := exprEffects memoryEntry 0 next (.ldx 8 2 10 (-8)) | return false
  let .error .undefinedSrc := exprEffects memoryEntry 0 E (.stx 1 10 0 (-4)) | return false
  return stored.inputs.entries.isEmpty && stored.updates.entries.length == 2 &&
    loaded.inputs.entries.isEmpty &&
    loaded.updates.lookupEq (Reg.real64 2) == some (Term.C64 0x1122334455667788)

#guard stackRoundTripCheck

private def packetMaterializationCheck : Bool := Id.run do
  let .ok σ := buildE0 memoryEntry | return false
  let .ok (loaded, []) := exprEffects memoryEntry 0 σ.exprs (.ldx 4 2 1 0) | return false
  let E := σ.exprs.override loaded.delta
  let .ok (first, []) := exprEffects memoryEntry 0 E (.ldx 4 0 2 0) | return false
  let .ok (second, []) := exprEffects memoryEntry 0 (E.override first.delta) (.ldx 4 0 2 0)
    | return false
  return first.inputs.entries.length == 4 && first.updates.entries.length == 1 &&
    second.inputs.entries.isEmpty && first.validFor E

#guard packetMaterializationCheck

private def packetRootAliasCheck : Bool := Id.run do
  let .ok σ := buildE0 memoryEntry | return false
  let .ok (loaded, []) := exprEffects memoryEntry 0 σ.exprs (.ldx 4 6 1 0) | return false
  let E := σ.exprs.override loaded.delta
  let some value := E.lookupEq (Reg.real64 6) | return false
  let .ok (.packet access) := resolveAccess memoryEntry E 6 0 2 false | return false
  return packetRoot memoryEntry E == some value && value.width == .w64 &&
    access.inputBase == some memoryEntry.tData && memoryEntry.tData.width == .w32

#guard packetRootAliasCheck

private def partialStackCheck : Bool := Id.run do
  let .ok σ := buildE0 memoryEntry | return false
  let E := σ.exprs.insertEq (stackUnitReg 5 0) (Term.C32 0x11223344)
    |>.insertEq (Reg.real64 0) (Term.C64 0xaa)
    |>.insertEq (Reg.real64 3)
      (idStar .w64 (addStar .w64 memoryEntry.tSp (Term.C64 (M 64 (-4)))))
  let .ok (stored, []) := exprEffects memoryEntry 0 E (.stx 1 3 0 1) | return false
  let .ok (loaded, []) := exprEffects memoryEntry 0 (E.override stored.delta) (.ldx 4 2 10 (-4))
    | return false
  return stored.inputs.entries.isEmpty &&
    loaded.updates.lookupEq (Reg.real64 2) == some (Term.C64 0x1122aa44)

#guard partialStackCheck
#guard Id.run do
  let p : EntryParams := ⟨Term.C64 0x1000, Term.V64 0, Term.C32 0x1000, 16, 3, 4, 5⟩
  let .ok σ := buildE0 p | return false
  let .error .undefinedSrc := resolveAccess p σ.exprs 1 0 4 false | return false
  return true

end EBPF
