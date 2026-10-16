import EBPF.Initial
import EBPF.Expr
import ClassifierExpr.Virtual
import ClassifierExpr.MapLayout

namespace EBPF
open ClassifierExpr PathMerge

inductive ResolvedAccess where
  | cells (parts : List CellAccess)
  | packet (access : PacketAccess)
  deriving Repr, Inhabited

/-- A Map parameter must select exactly one supplied layout. -/
def uniqueMapLayout (maps : List MapLayout) (mapTerm : Term) : Option MapLayout := do
  let id ← eval (solve mapTerm)
  match maps.filter (fun layout => layout.mapId == id) with
  | [layout] => some layout
  | _ => none

/-- Signed, integral displacement from a fixed entry root. Identity wrappers and
addition or subtraction of closed constants establish symbolic aliases. -/
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
    | .app .w64 (.sub .w64) [a, b] => do
      let c ← eval (solve b)
      let d ← relativeOffset root a
      pure (d - s 64 c)
    | _ => match solve root, solve address with
      | .const .w64 r, .const .w64 a => some (s 64 (M 64 (Int.ofNat a - Int.ofNat r)))
      | _, _ => none
  termination_by sizeOf address

/-- Lookup-result provenance at full eBPF width. Numeric pointers, other helpers
and sums of symbolic bases do not establish a Map identity. -/
def lookupAddress64 : Term → Option (Nat × Int × Term)
  | .app .w64 (.id .w64) [a] => lookupAddress64 a
  | .app .w64 (.externalResult event 0) [id, map, key] =>
    if eval (solve id) == some 1 && map.width == .w64 && key.width == .w64 then
      some (event, 0, map)
    else none
  | .app .w64 (.add .w64) [a, b] =>
    match eval (solve a), eval (solve b) with
    | none, some c => do
      let (event, offset, map) ← lookupAddress64 a
      pure (event, offset + s 64 c, map)
    | some c, none => do
      let (event, offset, map) ← lookupAddress64 b
      pure (event, offset + s 64 c, map)
    | _, _ => none
  | .app .w64 (.sub .w64) [a, b] =>
    match eval (solve a), eval (solve b) with
    | none, some c => do
      let (event, offset, map) ← lookupAddress64 a
      pure (event, offset - s 64 c, map)
    | _, _ => none
  | _ => none

theorem lookupAddress64_const (w : Width) (n : Nat) :
    lookupAddress64 (.const w n) = none := rfl

theorem lookupAddress64_ne_zero (source : Term) (event : Nat) (offset : Int) (map : Term)
    (h : lookupAddress64 source = some (event, offset, map)) :
    source ≠ Term.C64 0 := by
  intro hz
  subst source
  cases h

/-- Unit zero starts at tSp-4. A fixed stride is injective because unit < 128. -/
def stackUnitReg (resource unit : Nat) : Reg := Reg.sw (128 * resource + unit)

private def contextParts (p : EntryParams) (d : Int) (bytes : Nat)
    (byteView : Bool := false) : Option ResolvedAccess :=
  if d ≥ 0 && d.toNat / 4 < 2 && d.toNat % 4 + bytes ≤ 4 &&
      ((d.toNat % 4 == 0 && bytes == 4) || (byteView && bytes == 1)) then
    some (.cells [⟨Reg.ctx32 (p.αCtx + d.toNat / 4),
      8 * (d.toNat % 4), 8 * bytes⟩])
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

/-- Frozen little-endian stack bytes. Cell reads widen each extracted 32-bit
stack field with zStar 8 .w64 32; unavailable bytes are never materialized. -/
def stackBytes (p : EntryParams) (E : ExprSet) (addr : Term) (n : Nat) :
    Option (List Term) := do
  let displacement ← relativeOffset p.tSp addr
  (List.range n).mapM fun j => do
    let .cells parts ← stackParts p (displacement + Int.ofNat j) 1 | none
    let (_, value) ← (readAccess E (.cells parts)).toOption
    pure value

/-- The packet base is exactly the widened context data cell yielded by LDX W.
Using the same read path prevents drift between classification and loaded aliases.
Missing context data contents authorize no packet candidate. -/
def packetRoot (p : EntryParams) (E : ExprSet) : Option Term := do
  let (_, value) ← (readAccess E (.cells [⟨Reg.ctx32 p.αCtx, 0, 32⟩])).toOption
  pure value

/-- Resolve against the executing full base equality, never against a mutable
entry-register name. Content availability is checked by readAccess/writeAccess.
Lookup anchors word zero; other Map words have no implicit content relation
and accesses reject undefinedSrc until such a relation is explicitly available. -/
def resolveAddress (p : EntryParams) (E : ExprSet) (address : Term) (offset : Int)
    (bytes : Nat) (maps : List MapLayout := []) (contextByteView : Bool := false) :
    Except RejectReason ResolvedAccess := do
  if !E.keysUnique || !E.wellTyped || address.width != .w64 ||
      ![1, 2, 4, 8].contains bytes then throw .undefinedSrc
  let mut candidates : List ResolvedAccess := []
  if let some displacement := relativeOffset p.tCtx address then
    if let some a := contextParts p (displacement + offset) bytes contextByteView then
      candidates := a :: candidates
  if let some displacement := relativeOffset p.tSp address then
    if let some a := stackParts p (displacement + offset) bytes then
      candidates := a :: candidates
  if let some root := packetRoot p E then
    if let some displacement := relativeOffset root address then
      let o := displacement + offset
      if o ≥ 0 && o.toNat + bytes ≤ p.packetBytes then
        candidates := .packet ⟨p.κPacket, o.toNat, bytes, .little, some p.tData, none⟩ :: candidates
    else if let some displacement := packetDisplacement E root address then
      if offset ≥ 0 then
        let accessAddress := addStar .w64 address (Term.C64 offset.toNat)
        let endingAccess : CellAccess := ⟨Reg.ctx32 (p.αCtx + 1), 0, 32⟩
        if let some ending := endingAccess.read E .w64 true then
          if let some (strict, checkedEnd) := packetBoundWitness E root accessAddress ending bytes then
            let compound : CompoundPacketReg :=
              ⟨p.κPacket, displacement.plus (.c offset.toNat), bytes, p.αCtx + 1, strict, 0, checkedEnd⟩
            candidates := .packet ⟨p.κPacket, 0, bytes, .little, some p.tData, some compound⟩ ::
              candidates
  if let some (event, displacement, mapTerm) := lookupAddress64 address then
    if let some layout := uniqueMapLayout maps mapTerm then
      let rel := displacement + offset
      if rel ≥ 0 && rel.toNat + bytes ≤ layout.valueSize &&
          rel.toNat % 8 + bytes ≤ 8 then
        let o := rel.toNat
        candidates := .cells [⟨Reg.mapDword event (o - o % 8),
          8 * (o % 8), 8 * bytes⟩] :: candidates
  match candidates with
  | [a] => pure a
  | _ => throw .undefinedSrc

def resolveAccess (p : EntryParams) (E : ExprSet) (base : Nat) (offset : Int)
    (bytes : Nat) (isWrite : Bool) (maps : List MapLayout := []) :
    Except RejectReason ResolvedAccess := do
  let _ := isWrite
  if base > 10 then throw .undefinedSrc
  let some address := E.lookupEq (Reg.real64 base) | throw .undefinedSrc
  resolveAddress p E address offset bytes maps

private inductive BufferOrigin where
  | stack (resource : Nat)
  | context (firstCell : Nat)
  | map (event : NodeId) (object : Term)
  | packet (resource : Nat)
  deriving BEq

private def bufferOrigin (p : EntryParams) (address : Term) :
    ResolvedAccess → Option BufferOrigin
  | .packet a => some (.packet a.κ)
  | .cells [part] =>
    match part.reg.kind with
    | .stack => some (.stack p.φStack)
    | .context => some (.context p.αCtx)
    | .map => do
      let (event, _, object) ← lookupAddress64 address
      some (.map event object)
    | _ => none
  | _ => none

/-- Freeze one complete buffer with a single resource origin.
Packet bytes may materialize `inputByte` terms via `PacketAccess.read` when
`inputBase` is bound. Stack, map, and context still require current equalities.
Context bytes are views of the two existing canonical context words. -/
def availableBufferBytes (p : EntryParams) (E : ExprSet) (address : Term)
    (n : Nat) (maps : List MapLayout := []) : Option (List Term) := do
  if !E.keysUnique || !E.wellTyped || address.width != .w64 then none else do
    let mut origin : Option BufferOrigin := none
    let mut bytes := []
    for j in List.range n do
      let access ← (resolveAddress p E address (Int.ofNat j) 1 maps true).toOption
      let candidate ← bufferOrigin p address access
      if let some previous := origin then
        if previous != candidate then none
      origin := some candidate
      let (inputs, value) ← (readAccess E access).toOption
      let allowInputs := match access with
        | .packet _ => true
        | .cells _ => false
      if !allowInputs && !inputs.entries.isEmpty then none
      bytes := value :: bytes
    some bytes.reverse

/-- All partial fields read the old snapshot. Whole Stack units, including both
halves of a DW store, require no old equality. Map writes require an existing
content relation; layout bounds alone never materialize another Map word. -/
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
      if part.reg.kind == .map && (E.lookupEq part.reg).isNone then throw .undefinedSrc
      let field := if shift == 0 then source else lshrStar .w64 source (Term.C64 shift)
      let some written := part.write E field | throw .undefinedSrc
      updates := updates.override written
      shift := shift + part.bits
    pure updates

/-- Re-carrier saved native stack bytes without consulting the current key buffer.
Open bytes reuse the saved 32-bit extract; readAccess's zero OR/shift wrappers
leave that byte unchanged. -/
def mapWriteKeyByte (byte : Term) : Option Term :=
  match eval (solve byte) with
  | some c => some (Term.C32 (c % 256))
  | none => match byte with
    | .app .w64 (.zext 8 .w64 32)
        [field@(.app .w32 (.extract _ 8 32) [_])]
    | .app .w64 (.or 64) [.const .w64 0,
        .app .w64 (.shl .w64)
          [.app .w64 (.zext 8 .w64 32)
            [field@(.app .w32 (.extract _ 8 32) [_])], .const .w64 0]] =>
        some (solve field)
    | _ => if byte.width == .w64 then some (zStar 8 .w32 64 byte) else none

theorem mapWriteKeyByte_constant (byte : Term) (c : Nat)
    (h : eval (solve byte) = some c) :
    mapWriteKeyByte byte = some (Term.C32 (c % 256)) := by
  simp [mapWriteKeyByte, h]

/-- Open re-carriering either recovers the saved eight-bit field or takes
the low eight bits of the saved native byte; no current buffer is read. -/
theorem mapWriteKeyByte_open (byte result : Term)
    (hc : eval (solve byte) = none) (h : mapWriteKeyByte byte = some result) :
    (∃ offset stored,
      let field := Term.app .w32 (.extract offset 8 32) [stored]
      (byte = .app .w64 (.zext 8 .w64 32) [field] ∨
        byte = .app .w64 (.or 64) [.C64 0,
          .app .w64 (.shl .w64)
            [.app .w64 (.zext 8 .w64 32) [field], .C64 0]]) ∧
        result = solve field) ∨ result = zStar 8 .w32 64 byte := by
  unfold mapWriteKeyByte at h
  rw [hc] at h
  dsimp only at h
  split at h
  · simp only [Option.some.injEq] at h
    exact Or.inl ⟨_, _, Or.inl rfl, h.symm⟩
  · simp only [Option.some.injEq] at h
    exact Or.inl ⟨_, _, Or.inr rfl, h.symm⟩
  · split at h
    · simp only [Option.some.injEq] at h
      exact Or.inr h.symm
    · simp at h

/-- Map writes reuse the lookup's frozen key, never the current key buffer. -/
def mapWriteObservation (E : ExprSet) (Pg : List Predicate) (maps : List MapLayout)
    (base : Nat) (offset : Int) (bytes : Nat) : Option (Term × List Term × Nat) := do
  let address ← E.lookupEq (Reg.real64 base)
  let (lookupEvent, displacement, mapTerm) ← lookupAddress64 address
  let layout ← uniqueMapLayout maps mapTerm
  let rel := displacement + offset
  if rel < 0 || rel.toNat + bytes > layout.valueSize || rel.toNat % 8 + bytes > 8 then none
  else
    let (map, frozen) ← lookupKeyAt Pg lookupEvent
    if map != mapTerm || frozen.isEmpty || frozen.length != layout.keySize then none
    else do
      let key ← frozen.mapM mapWriteKeyByte
      some (map, key, rel.toNat)

/-- This key depends only on the saved observations and the pre-image event. -/
def mapWriteKeyAt (Pg : List Predicate) (event : NodeId) : Option (List Term) := do
  let (_, frozen) ← lookupKeyAt Pg event
  frozen.mapM mapWriteKeyByte

theorem mapWriteObservation_frozen (E : ExprSet) (Pg : List Predicate)
    (maps : List MapLayout) (base : Nat) (offset : Int) (bytes : Nat)
    (map : Term) (key : List Term) (elementOff : Nat)
    (h : mapWriteObservation E Pg maps base offset bytes = some (map, key, elementOff)) :
    ∃ event address displacement frozen,
      E.lookupEq (Reg.real64 base) = some address ∧
      lookupAddress64 address = some (event, displacement, map) ∧
      LookupTie Pg event map frozen ∧
      lookupKeyAt Pg event = some (map, frozen) ∧
      frozen.mapM mapWriteKeyByte = some key ∧ mapWriteKeyAt Pg event = some key := by
  unfold mapWriteObservation at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  rcases h with ⟨address, ha, ⟨event, displacement, pointerMap⟩, hl, layout, _, h⟩
  split at h
  · cases h
  · simp only [Option.bind_eq_some_iff] at h
    rcases h with ⟨⟨m, frozen⟩, hk, h⟩
    split at h
    · cases h
    · rename_i valid
      have hm : m = pointerMap := by
        by_cases hm : m = pointerMap
        · exact hm
        · simp [hm] at valid
      simp only [Option.bind_eq_some_iff] at h
      rcases h with ⟨converted, hc, he⟩
      cases he
      exact ⟨event, address, displacement, frozen, ha, hm ▸ hl,
        lookupKeyAt_tie Pg event map frozen hk, hk, hc, by simp [mapWriteKeyAt, hk, hc]⟩

theorem mapWriteKeyAt_expr_update (E updates : ExprSet) (Pg : List Predicate)
    (event : NodeId) :
    mapWriteKeyAt (SemState.mk (updateExpr E updates) Pg).predicates event =
      mapWriteKeyAt Pg event := rfl

theorem mapWriteKeyAt_deterministic (Pg : List Predicate) (event : NodeId)
    (key₁ key₂ : List Term)
    (h₁ : mapWriteKeyAt Pg event = some key₁)
    (h₂ : mapWriteKeyAt Pg event = some key₂) : key₁ = key₂ :=
  Option.some.inj (h₁.symm.trans h₂)

/-- A native Map DW write observes the low half before the high half, while the
value effect still uses the complete pre-state source. Narrow stores keep it intact. -/
private def mapWriteObservations (event : NodeId) (map : Term) (frozen : List Term)
    (elementOff bytes : Nat) (source : Term) : List Predicate :=
  if bytes == 8 then
    [.mapWrite event map frozen elementOff 32 (star .w32 (.extract 0 32 64) [source]),
      .mapWrite event map frozen (elementOff + 4) 32 (star .w32 (.extract 32 32 64) [source])]
  else [.mapWrite event map frozen elementOff (8 * bytes) source]

theorem mapWriteObservations_saved_key (event : NodeId) (map : Term)
    (key : List Term) (elementOff bytes : Nat) (source : Term) (p : Predicate)
    (h : p ∈ mapWriteObservations event map key elementOff bytes source) :
    p.savedMapKey? = some key := by
  unfold mapWriteObservations at h
  split at h
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl <;> rfl
  · simp only [List.mem_singleton] at h
    subst p
    rfl

private def storeEffect (p : EntryParams) (event : NodeId) (E : ExprSet)
    (maps : List MapLayout) (Pg : List Predicate) (bytes base : Nat)
    (offset : Int) (source : Term) : Except RejectReason (ExprEffect × List Predicate) := do
  let access ← resolveAccess p E base offset bytes true maps
  let updates ← writeAccess E access source
  let predicates ← match access with
    | .packet a => pure [.packetWrite event a.κ a.offset (8 * bytes) source a.compound]
    | .cells parts =>
      if parts.any (fun part => part.reg.kind == .map) then do
        let some (map, frozen, elementOff) := mapWriteObservation E Pg maps base offset bytes
          | throw .undefinedSrc
        pure (mapWriteObservations event map frozen elementOff bytes source)
      else pure []
  pure (⟨.empty, updates⟩, predicates)

private def memoryReg (E : ExprSet) (r : Nat) : Except RejectReason Term := do
  if r > 10 then throw .undefinedSrc
  let some value := E.lookupEq (Reg.real64 r) | throw .undefinedSrc
  if value.width != .w64 then throw .undefinedSrc
  pure value

/-- Sequential numeric RMW on canonical stack or Map cells.
DW stack memory is assembled once from the two old SW32 cells, updated once at
64 bits, then split into simultaneous assignments. No concurrency observation is added. -/
private def atomicEffect (p : EntryParams) (E : ExprSet) (maps : List MapLayout)
    (w : Width) (op : AtomicOp) (base src : Nat) (offset : Int) :
    Except RejectReason (ExprEffect × List Predicate) := do
  if op.returnsSource && src ≥ 10 then throw .undefinedSrc
  let source ← memoryReg E src
  let access ← resolveAccess p E base offset (w.bits / 8) true maps
  match access with
  | .packet _ => throw .unsupported
  | .cells parts =>
    if parts.any (fun part => part.reg.kind != .stack && part.reg.kind != .map) then
      throw .unsupported
    if parts.any (fun part => part.bitOffset % w.bits != 0) then throw .undefinedSrc
  let (inputs, oldMemory) ← readAccess E access
  let a := aluOperand w oldMemory
  let b := aluOperand w source
  let value ← match op with
    | .add _ => pure (addStar w a b)
    | .or _ => pure (orStar w.bits w a b)
    | .and _ => pure (andStar w.bits w a b)
    | .xor _ => pure (xorStar w.bits w a b)
    | .xchg => pure b
    | .cmpxchg => do
      let expected ← memoryReg E 0
      pure (star w (.selectEq w) [a, aluOperand w expected, b, a])
  let updates ← writeAccess E access (aluResult w value)
  let updates := if op.returnsSource then
      updates.insertEq (Reg.real64 src) (aluResult w a)
    else if op == .cmpxchg then updates.insertEq (Reg.real64 0) (aluResult w a)
    else updates
  pure (⟨inputs, updates⟩, [])

/-- Value effects read their sources and partial-field old values from E.
Control flow and helper calls belong to Step. -/
def exprEffects (p : EntryParams) (event : NodeId) (E : ExprSet) (i : Insn)
    (maps : List MapLayout := []) (Pg : List Predicate := []) :
    Except RejectReason (ExprEffect × List Predicate) := do
  if !E.keysUnique || !E.wellTyped then throw .undefinedSrc
  match i with
  | .ldx bytes dst base offset | .loadAcq bytes dst base offset =>
    if dst > 9 then throw .undefinedSrc
    let access ← resolveAccess p E base offset bytes false maps
    let (inputs, value) ← readAccess E access
    pure (⟨inputs, ExprSet.empty.insertEq (Reg.real64 dst) value⟩, [])
  | .memsx bytes dst base offset =>
    if dst > 9 || ![1, 2, 4].contains bytes then throw .undefinedSrc
    let access ← resolveAccess p E base offset bytes false maps
    let (inputs, value) ← readAccess E access
    pure (⟨inputs, ExprSet.empty.insertEq (Reg.real64 dst)
      (sStar (8 * bytes) .w64 64 value)⟩, [])
  | .stx bytes base src offset | .storeRel bytes base src offset =>
    let source ← memoryReg E src
    storeEffect p event E maps Pg bytes base offset source
  | .st bytes base bits offset =>
    storeEffect p event E maps Pg bytes base offset (Term.C64 (M 64 (s 32 bits.toNat)))
  | .atomic w op base src offset => atomicEffect p E maps w op base src offset
  | .mov _ _ _ | .binary _ _ _ _ | .neg _ _ | .movsx _ _ _ _ | .endian _ _ _ =>
    let some updates := expr E i | throw .undefinedSrc
    pure (⟨.empty, updates⟩, [])
  | .exit => pure (⟨.empty, .empty⟩, [])
  | .illegal _ => throw .localReject
  | _ => throw .localReject

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

private def lookupPointer : Term :=
  star .w64 (.externalResult 7 0) [Term.C64 1, Term.C64 42, Term.V64 9]

private def lookupMemoryCheck : Bool := Id.run do
  let .ok σ := buildE0 memoryEntry | return false
  let maps : List MapLayout := [⟨42, 4, 16⟩]
  let E := σ.exprs.insertEq (Reg.real64 0) lookupPointer
    |>.insertEq (Reg.mapDword 7 0) (Term.regVar 7 (Reg.real64 0))
  let .ok (.cells [part]) := resolveAccess memoryEntry E 0 0 8 false maps | return false
  let .ok (_, value) := readAccess E (.cells [part]) | return false
  let .ok updates := writeAccess E (.cells [part]) (Term.C64 99) | return false
  let .ok (_, next) := readAccess (E.override updates) (.cells [part]) | return false
  let .ok unanchored := resolveAccess memoryEntry E 0 8 8 false maps | return false
  let .error .undefinedSrc := readAccess E unanchored | return false
  let .error .undefinedSrc := writeAccess E unanchored (Term.C64 99) | return false
  let .error .undefinedSrc := resolveAccess memoryEntry E 0 7 2 false maps | return false
  let .error .undefinedSrc := resolveAccess memoryEntry E 0 (-1) 1 false maps | return false
  let .error .undefinedSrc := resolveAccess memoryEntry E 0 16 1 false maps | return false
  let .error .undefinedSrc := resolveAccess memoryEntry E 0 0 8 false | return false
  return part.reg == Reg.mapDword 7 0 && part.bits == 64 &&
    value == Term.regVar 7 (Reg.real64 0) && next == Term.C64 99

#guard lookupMemoryCheck

/-- The key pointer is not a current stack alias: only Pg supplies the frozen key. -/
private def mapStoreExprs : ExprSet :=
  ExprSet.empty.insertEq (Reg.real64 0)
    (star .w64 (.externalResult 7 0)
      [Term.C64 1, Term.C64 1077412584, Term.V64 9])
    |>.insertEq (Reg.real64 1) (idStar .w64 (Term.V64 11))
    |>.insertEq (Reg.mapDword 7 0) (Term.regVar 7 (Reg.real64 0))

private def mapStoreFrozenKey : List Term :=
  [Term.C64 1, Term.C64 2, Term.C64 3, Term.C64 4]

private def mapStoreKey : List Term :=
  [Term.C32 1, Term.C32 2, Term.C32 3, Term.C32 4]

private def mapStoreLookup : Predicate :=
  .helper 7 .lookup ([Term.C64 1077412584, Term.V64 9] ++ mapStoreFrozenKey)

private def mapStoreLayouts : List MapLayout :=
  [{ mapId := 1077412584, keySize := 4, valueSize := 8 }]

private def mapStoreObservationsCheck : Bool := Id.run do
  let E := mapStoreExprs
  let ev := 77
  let some source := E.lookupEq (Reg.real64 1) | return false
  let .ok (effect, predicates) :=
    exprEffects memoryEntry ev E (.stx 8 0 1 0) mapStoreLayouts [mapStoreLookup]
    | return false
  let .ok (_, partialPredicates) :=
    exprEffects memoryEntry (ev + 1) E (.stx 4 0 1 4) mapStoreLayouts [mapStoreLookup]
    | return false
  return predicates ==
      [.mapWrite ev (Term.C64 1077412584) mapStoreKey 0 32
        (star .w32 (.extract 0 32 64) [source]),
       .mapWrite ev (Term.C64 1077412584) mapStoreKey 4 32
        (star .w32 (.extract 32 32 64) [source])] &&
    partialPredicates ==
      [.mapWrite (ev + 1) (Term.C64 1077412584) mapStoreKey 4 32 source] &&
    effect.inputs == ExprSet.empty &&
    effect.updates.lookupEq (Reg.mapDword 7 0) == some source &&
    effect.validFor E

/-- Interpret the saved key and both DW observations under explicit ν/θ.
The old key survives a live-stack overwrite; extract/extend wrappers are not
part of this behavior contract. The value effect must store the full old source. -/
private def symbolicMapStoreFrozenKeyCheck : Bool := Id.run do
  let keyPtr := addStar .w64 memoryEntry.tSp (Term.C64 (M 64 (-4)))
  let original := mapStoreExprs.insertEq (stackUnitReg 5 0) (Term.V32 12)
  let some frozen := stackBytes memoryEntry original keyPtr 4 | return false
  let Pg := [.helper 7 .lookup ([Term.C64 1077412584, keyPtr] ++ frozen)]
  let E := original.insertEq (Reg.real64 0)
    (star .w64 (.externalResult 7 0) [Term.C64 1, Term.C64 1077412584, keyPtr])
    |>.insertEq (stackUnitReg 5 0) (Term.C32 0)
  let .ok (effect, predicates) :=
    exprEffects memoryEntry 77 E (.stx 8 0 1 0) mapStoreLayouts Pg | return false
  let [.mapWrite 77 mapLo keyLo 0 32 valueLo, .mapWrite 77 mapHi keyHi 4 32 valueHi] :=
    predicates | return false
  let some updated := effect.updates.lookupEq (Reg.mapDword 7 0) | return false
  let next := E.override effect.delta
  let some stored := next.lookupEq (Reg.mapDword 7 0) | return false
  let some liveKey := stackBytes memoryEntry next keyPtr 4 | return false
  if !effect.validFor E || !effect.inputs.entries.isEmpty ||
      effect.updates.entries.length != 1 ||
      !frozen.all (fun t => t.width == .w64) ||
      !(keyLo ++ keyHi).all (fun t => t.width == .w32) ||
      valueLo.width != .w32 || valueHi.width != .w32 then return false
  let θ : ExternalInterpretation :=
    { externalResult := fun _ _ _ _ => some 0
      inputByte := fun _ _ _ => some 0 }
  let cases : List (Nat × List Nat × Nat × Nat × Nat) := [
    (0xa1b2c3d4, [0xd4, 0xc3, 0xb2, 0xa1],
      0x1122334455667788, 0x55667788, 0x11223344),
    (0x01020304, [4, 3, 2, 1],
      0xfedcba9876543210, 0x76543210, 0xfedcba98)]
  return cases.all fun (keyValue, keyBytes, sourceValue, lowValue, highValue) =>
    let ν : Var → Nat := fun v => match v.width, v.name, v.register with
      | .w32, 12, none => keyValue
      | .w64, 11, none => sourceValue
      | _, _, _ => 0
    interpretTerms ν θ frozen == some keyBytes &&
      interpretTerms ν θ keyLo == some keyBytes &&
      interpretTerms ν θ keyHi == some keyBytes &&
      interpretTerm ν θ mapLo == some 1077412584 &&
      interpretTerm ν θ mapHi == some 1077412584 &&
      interpretTerm ν θ valueLo == some lowValue &&
      interpretTerm ν θ valueHi == some highValue &&
      interpretTerm ν θ updated == some sourceValue &&
      interpretTerm ν θ stored == some sourceValue &&
      interpretTerms ν θ liveKey == some [0, 0, 0, 0]

private def mapStoreRejectsMissingObservationCheck : Bool :=
  let malformedLookups : List (List Predicate) := [
    [],
    [.helper 7 .lookup [Term.C64 1077412584, Term.V64 9]],
    [.helper 7 .lookup
      ([Term.C64 1077412584, Term.V64 9] ++ mapStoreFrozenKey.take 3)],
    [.helper 7 .lookup
      ([Term.C64 1077412584, Term.V64 9] ++ mapStoreFrozenKey ++ [Term.C64 5])],
    [.helper 8 .lookup ([Term.C64 1077412584, Term.V64 9] ++ mapStoreFrozenKey)],
    [.helper 7 .lookup ([Term.C64 42, Term.V64 9] ++ mapStoreFrozenKey)]]
  malformedLookups.all fun Pg =>
    match exprEffects memoryEntry 77 mapStoreExprs (.stx 8 0 1 0) mapStoreLayouts Pg with
    | .error .undefinedSrc => true
    | _ => false

private def mapStoreRejectsLayoutAndBoundsCheck : Bool :=
  let cases : List (Insn × List MapLayout) := [
    (.stx 8 0 1 0, []),
    (.stx 8 0 1 0, [⟨42, 4, 8⟩]),
    (.stx 1 0 1 (-1), mapStoreLayouts),
    (.stx 2 0 1 7, [⟨1077412584, 4, 16⟩]),
    (.stx 8 0 1 0, [⟨1077412584, 4, 4⟩]),
    (.stx 1 0 1 8, mapStoreLayouts)]
  cases.all fun (i, maps) =>
    match exprEffects memoryEntry 77 mapStoreExprs i maps [mapStoreLookup] with
    | .error .undefinedSrc => true
    | _ => false

private def nonMapCellStoreObservationsCheck : Bool := Id.run do
  let .ok σ := buildE0 memoryEntry | return false
  let E := σ.exprs.insertEq (Reg.real64 0) (Term.C64 99)
  let .ok (_, []) :=
    exprEffects memoryEntry 77 E (.stx 8 10 0 (-8)) mapStoreLayouts [mapStoreLookup]
    | return false
  let .ok (_, []) :=
    exprEffects memoryEntry 78 E (.stx 4 1 0 0) mapStoreLayouts [mapStoreLookup]
    | return false
  return true

#guard mapStoreObservationsCheck
#guard symbolicMapStoreFrozenKeyCheck
#guard mapStoreRejectsMissingObservationCheck
#guard mapStoreRejectsLayoutAndBoundsCheck
#guard nonMapCellStoreObservationsCheck
#guard lookupAddress64 (idStar .w64 lookupPointer) == some (7, 0, Term.C64 42)
#guard lookupAddress64
  (subStar .w64 (addStar .w64 lookupPointer (Term.C64 8)) (Term.C64 4)) ==
    some (7, 4, Term.C64 42)
#guard lookupAddress64 (addStar .w64 (Term.C64 8) lookupPointer) ==
  some (7, 8, Term.C64 42)
#guard (lookupAddress64 (Term.C64 42)).isNone
#guard (lookupAddress64 (addStar .w64 lookupPointer (Term.V64 3))).isNone
#guard (lookupAddress64 (star .w64 (.externalResult 7 0)
  [Term.C64 2, Term.C64 42, Term.V64 9])).isNone
#guard (lookupAddress64 (star .w64 (.externalResult 7 1)
  [Term.C64 1, Term.C64 42, Term.V64 9])).isNone
#guard Id.run do
  let .ok σ := buildE0 memoryEntry | return false
  let ptr := addStar .w64 memoryEntry.tSp (Term.C64 (M 64 (-4)))
  let E := σ.exprs.insertEq (stackUnitReg 5 0) (Term.C32 0x11223344)
  return stackBytes memoryEntry E ptr 4 ==
    some [Term.C64 0x44, Term.C64 0x33, Term.C64 0x22, Term.C64 0x11] &&
    (stackBytes memoryEntry σ.exprs ptr 4).isNone &&
    (stackBytes memoryEntry E ptr 5).isNone

private def atomicStackSnapshotCheck : Bool := Id.run do
  let .ok σ := buildE0 memoryEntry | return false
  let E := σ.exprs.insertEq (stackUnitReg 5 1) (Term.C32 0xffffffff)
    |>.insertEq (stackUnitReg 5 0) (Term.C32 1)
    |>.insertEq (Reg.real64 2) (Term.C64 1)
    |>.insertEq (Reg.real64 0) (Term.C64 0x1ffffffff)
  let .ok (add, []) := exprEffects memoryEntry 1 E
    (.atomic .w64 (.add true) 10 2 (-8)) | return false
  let .ok (cmp, []) := exprEffects memoryEntry 2 E
    (.atomic .w64 .cmpxchg 10 2 (-8)) | return false
  let failedCompare := E.insertEq (Reg.real64 0) (Term.C64 0)
  let .ok (miss, []) := exprEffects memoryEntry 3 failedCompare
    (.atomic .w64 .cmpxchg 10 2 (-8)) | return false
  let missingHigh := σ.exprs.insertEq (stackUnitReg 5 1) (Term.C32 1)
    |>.insertEq (Reg.real64 2) (Term.C64 1)
  let .error .undefinedSrc := exprEffects memoryEntry 4 missingHigh
    (.atomic .w64 (.add true) 10 2 (-8)) | return false
  return add.updates.lookupEq (stackUnitReg 5 1) == some (Term.C32 0) &&
    add.updates.lookupEq (stackUnitReg 5 0) == some (Term.C32 2) &&
    add.updates.lookupEq (Reg.real64 2) == some (Term.C64 0x1ffffffff) &&
    cmp.updates.lookupEq (stackUnitReg 5 1) == some (Term.C32 1) &&
    cmp.updates.lookupEq (stackUnitReg 5 0) == some (Term.C32 0) &&
    cmp.updates.lookupEq (Reg.real64 0) == some (Term.C64 0x1ffffffff) &&
    miss.updates.lookupEq (stackUnitReg 5 1) == some (Term.C32 0xffffffff) &&
    miss.updates.lookupEq (stackUnitReg 5 0) == some (Term.C32 1) &&
    miss.updates.lookupEq (Reg.real64 0) == some (Term.C64 0x1ffffffff) &&
    add.validFor E && cmp.validFor E && miss.validFor failedCompare

private def atomicMapFieldCheck : Bool := Id.run do
  let E := mapStoreExprs.insertEq (Reg.mapDword 7 0) (Term.C64 0x11223344ffffffff)
    |>.insertEq (Reg.real64 2) (Term.C64 1)
  let .ok (effect, []) := exprEffects memoryEntry 9 E
    (.atomic .w32 (.add true) 0 2 0) mapStoreLayouts | return false
  let .error .undefinedSrc := exprEffects memoryEntry 9 E
    (.atomic .w32 (.add false) 0 2 1) mapStoreLayouts | return false
  return effect.updates.lookupEq (Reg.mapDword 7 0) == some (Term.C64 0x1122334400000000) &&
    effect.updates.lookupEq (Reg.real64 2) == some (Term.C64 0xffffffff) &&
    effect.updates.entries.length == 2 && effect.validFor E

private def immediateAndSignedMemoryCheck : Bool := Id.run do
  let .ok σ := buildE0 memoryEntry | return false
  let .ok (stored, []) := exprEffects memoryEntry 0 σ.exprs
    (.st 8 10 0xffffff80 (-8)) | return false
  let E := σ.exprs.override stored.delta
  let .ok (signed, []) := exprEffects memoryEntry 1 E (.memsx 1 2 10 (-8)) | return false
  let .ok (unsigned, []) := exprEffects memoryEntry 2 E (.loadAcq 1 2 10 (-8)) | return false
  let E := E.insertEq (Reg.real64 2) (Term.C64 0x55)
  let .ok (released, []) := exprEffects memoryEntry 3 E (.storeRel 1 10 2 (-7)) | return false
  return signed.updates.lookupEq (Reg.real64 2) == some (Term.C64 0xffffffffffffff80) &&
    unsigned.updates.lookupEq (Reg.real64 2) == some (Term.C64 0x80) &&
    released.updates.lookupEq (stackUnitReg 5 1) == some (Term.C32 0xffff5580)

#guard atomicStackSnapshotCheck
#guard atomicMapFieldCheck
#guard immediateAndSignedMemoryCheck

#guard relativeOffset memoryEntry.tSp (subStar .w64 memoryEntry.tSp (Term.C64 8)) ==
  some (-8)

#guard Id.run do
  let p : EntryParams := ⟨Term.C64 0x1000, Term.C64 0x2000, Term.C32 0x2000,
    4, 0, 0, 0⟩
  let .ok initial := buildE0 p | return false
  let E := initial.exprs.insertEq (stackUnitReg 0 0) (Term.C32 0x11223344)
    |>.insertEq (Reg.packet 0 0) (Term.C32 0x55)
  let some [open0] := availableBufferBytes p initial.exprs (Term.C64 0x2000) 1 | return false
  let access : PacketAccess := ⟨0, 0, 1, .little, some p.tData, none⟩
  let some expected := (access.read initial.exprs .w64 true).map (·.value) | return false
  return availableBufferBytes p E (Term.C64 0x1fff) 1 == some [Term.C64 0x11] &&
    availableBufferBytes p E (Term.C64 0x2000) 1 == some [Term.C64 0x55] &&
    (availableBufferBytes p E (Term.C64 0x1fff) 2).isNone &&
    open0 == expected

end EBPF

