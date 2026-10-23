import EBPF.Initial
import EBPF.Expr
import Core.Virtual
import Core.MapLayout

namespace EBPF
open Core Node

inductive ResolvedAccess where
  | mem (slot : BitSlot) (start bits : Nat)
  | packet (access : PacketAccess)
  deriving Repr, Inhabited

private def liftMem {α : Type} : Except MemError α → Except RejectReason α
  | .ok a => pure a
  | .error (.gap _) => throw .undefinedSrc
  | .error _ => throw .localReject

private def tileOf (source : Term) (bits : Nat) : Except RejectReason Tile :=
  liftMem (Tile.ofTerm source bits)

def keyTile (bytes : List Term) : Except RejectReason Tile := do
  let mut slices : List Slice := []
  for t in bytes do
    let one ← tileOf t 8
    slices := slices ++ one.slices
  liftMem (normalizeTile ⟨slices⟩)

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

private def contextParts (d : Int) (bytes : Nat)
    (byteView : Bool := false) : Option ResolvedAccess :=
  if d ≥ 0 && d.toNat / 4 < 2 && d.toNat % 4 + bytes ≤ 4 &&
      ((d.toNat % 4 == 0 && bytes == 4) || (byteView && bytes == 1)) then
    some (.mem (.context (d.toNat / 4)) (8 * (d.toNat % 4)) (8 * bytes))
  else none

private def stackParts (d : Int) (bytes : Nat) : Option ResolvedAccess :=
  if d < -512 || d ≥ 0 || d + Int.ofNat bytes > 0 then none
  else
    let n := (d + 512).toNat
    let within := n % 4
    let fits := if bytes == 8 then within == 0 else within + bytes ≤ 4
    if fits then some (.mem .stack (n * 8) (8 * bytes)) else none

/-- A packet gap is filled from the entry data root. Stack, map, and context
gaps stay undefined. The filled bytes are memory writes, not register rows. -/
private def readPacket (mem : Mem) (E : List Expr) (start bits : Nat) :
    Except RejectReason (List MemWrite × Term) := do
  let some p := entryParams? E | throw .undefinedSrc
  if start % 8 != 0 || bits == 0 || bits % 8 != 0 || bits > 64 then throw .undefinedSrc
  let mut writes : List MemWrite := []
  for j in List.range (bits / 8) do
    let bit := start + 8 * j
    match mem.read .packet bit (bit + 8) with
    | .ok _ => pure ()
    | .error (.gap _) =>
      let base := p.tData
      if start / 8 + j ≥ 2 ^ base.width.bits then throw .undefinedSrc
      let address := addStar base.width base (Term.C base.width (start / 8 + j))
      let raw := star .w32 (.low 8 32) [star .w32 (.inputByte p.κPacket) [base, address]]
      let tile ← tileOf raw 8
      writes := writes ++ [⟨.packet, bit, tile⟩]
    | .error _ => throw .localReject
  let mem ← liftMem (mem.apply writes)
  let value ← liftMem ((← liftMem (mem.read .packet start (start + bits))).toW64)
  pure (writes, value)

def readAccess (mem : Mem) (E : List Expr) (a : ResolvedAccess) :
    Except RejectReason (List MemWrite × Term) := do
  match a with
  | .packet access =>
    let some result := access.read E .w64 true | throw .undefinedSrc
    pure ([], result.value)
  | .mem slot start bits =>
    if bits == 0 || bits > 64 then throw .undefinedSrc
    else if slot == .packet then readPacket mem E start bits
    else
      let value ← liftMem ((← liftMem (mem.read slot start (start + bits))).toW64)
      pure ([], value)

/-- Frozen little-endian stack bytes. Cell reads widen each extracted 32-bit
stack field with zStar 8 .w64 32; unavailable bytes are never materialized. -/
def stackBytes (mem : Mem) (E : List Expr) (addr : Term) (n : Nat) :
    Option (List Term) := do
  let p ← entryParams? E
  let displacement ← relativeOffset p.tSp addr
  (List.range n).mapM fun j => do
    let .mem slot start bits ← stackParts (displacement + Int.ofNat j) 1 | none
    let (_, value) ← (readAccess mem E (.mem slot start bits)).toOption
    pure value

/-- The packet base is the widened context data field. Missing data authorizes
no packet candidate. -/
def packetRoot (mem : Mem) (E : List Expr) : Option Term := do
  let _p ← entryParams? E
  let (_, value) ← (readAccess mem E (.mem (.context 0) 0 32)).toOption
  pure value

/-- Resolve against the executing full base equality, never against a mutable
entry-register name. Content availability is checked by readAccess/writeAccess.
Lookup anchors word zero; other Map words have no implicit content relation
and accesses reject undefinedSrc until such a relation is explicitly available. -/
def resolveAddress (mem : Mem) (E : List Expr) (address : Term) (offset : Int)
    (bytes : Nat) (contextByteView : Bool := false)
    (preds : List Predicate := []) :
    Except RejectReason ResolvedAccess := do
  let some p := entryParams? E | throw .undefinedSrc
  if !E.keysUnique || !E.wellTyped || address.width != .w64 ||
      ![1, 2, 4, 8].contains bytes then throw .undefinedSrc
  let mut candidates : List ResolvedAccess := []
  if let some displacement := relativeOffset p.tCtx address then
    if let some a := contextParts (displacement + offset) bytes contextByteView then
      candidates := a :: candidates
  if let some displacement := relativeOffset p.tSp address then
    if let some a := stackParts (displacement + offset) bytes then
      candidates := a :: candidates
  if let some root := packetRoot mem E then
    if let some displacement := relativeOffset root address then
      let o := displacement + offset
      if o ≥ 0 && o.toNat + bytes ≤ p.packetBytes then
        candidates := .mem .packet (o.toNat * 8) (8 * bytes) :: candidates
    else if let some displacement := packetDisplacement E root address then
      if offset ≥ 0 then
        let accessAddress := addStar .w64 address (Term.C64 offset.toNat)
        if let .ok (_, ending) := readAccess mem E (.mem (.context 1) 0 32) then
          if let some (strict, checkedEnd) := packetBoundWitness E root accessAddress ending bytes preds then
            let compound : CompoundPacketReg :=
              ⟨p.κPacket, displacement.plus (.c offset.toNat), bytes, 1, strict, 0, checkedEnd⟩
            candidates := .packet ⟨p.κPacket, 0, bytes, .little, some p.tData, some compound⟩ ::
              candidates
  if let some (event, displacement, mapTerm) := lookupAddress64 address then
    if let some layout := Anchor.layout? E mapTerm then
      let rel := displacement + offset
      if rel ≥ 0 && rel.toNat + bytes ≤ layout.valueSize &&
          rel.toNat % 8 + bytes ≤ 8 then
        if let some id := eval (solve mapTerm) then
          if let some (saved, frozen) := lookupKeyAt preds event then
            if saved == mapTerm && frozen.length == layout.keySize then
              if let .ok key := keyTile frozen then
                candidates := .mem (.map id key) (rel.toNat * 8) (8 * bytes) :: candidates
  match candidates with
  | [a] => pure a
  | _ => throw .undefinedSrc

def resolveAccess (mem : Mem) (E : List Expr) (base : Nat) (offset : Int)
    (bytes : Nat) (isWrite : Bool)
    (preds : List Predicate := []) :
    Except RejectReason ResolvedAccess := do
  let _ := isWrite
  if base > 10 then throw .undefinedSrc
  let some address := E.lookupEq (Reg.real64 base) | throw .undefinedSrc
  resolveAddress mem E address offset bytes false preds

private inductive BufferOrigin where
  | stack (resource : Nat)
  | context (firstCell : Nat)
  | map (event : NodeId) (object : Term)
  | packet (resource : Nat)
  deriving BEq

private def bufferOrigin (address : Term) : ResolvedAccess → Option BufferOrigin
  | .packet a => some (.packet a.κ)
  | .mem .stack _ _ => some (.stack 0)
  | .mem (.context _) _ _ => some (.context 0)
  | .mem .packet _ _ => some (.packet 0)
  | .mem (.map _ _) _ _ => do
    let (event, _, object) ← lookupAddress64 address
    some (.map event object)

/-- Freeze one complete buffer with a single resource origin.
Packet bytes may materialize `inputByte` terms via `PacketAccess.read` when
`inputBase` is bound. Stack, map, and context still require current equalities.
Context bytes are views of the two existing canonical context words. -/
def availableBufferBytes (mem : Mem) (E : List Expr) (address : Term)
    (n : Nat) (preds : List Predicate := []) : Option (List Term) := do
  let _p ← entryParams? E
  if !E.keysUnique || !E.wellTyped || address.width != .w64 then none else do
    let mut origin : Option BufferOrigin := none
    let mut bytes := []
    for j in List.range n do
      let access ← (resolveAddress mem E address (Int.ofNat j) 1 true preds).toOption
      let candidate ← bufferOrigin address access
      if let some previous := origin then
        if previous != candidate then none
      origin := some candidate
      let (writes, value) ← (readAccess mem E access).toOption
      let allowWrites := match access with
        | .packet _ | .mem .packet _ _ => true
        | .mem _ _ _ => false
      if !allowWrites && !writes.isEmpty then none
      bytes := value :: bytes
    some bytes.reverse

/-- All partial fields read the old snapshot. Whole Stack units, including both
halves of a DW store, require no old equality. Map writes require an existing
content relation; layout bounds alone never materialize another Map word. -/
def writeAccess (E : List Expr) (a : ResolvedAccess) (source : Term) :
    Except RejectReason (List Expr × List MemWrite) := do
  if source.width != .w64 then throw .undefinedSrc
  match a with
  | .packet access =>
    let some updates := access.write E source | throw .undefinedSrc
    pure (updates, [])
  | .mem slot start bits =>
    if bits == 0 || bits > 64 then throw .undefinedSrc
    let tile ← tileOf source bits
    pure (Expr.nil, [⟨slot, start, tile⟩])

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
def mapWriteObservation (E : List Expr) (Pg : List Predicate)
    (base : Nat) (offset : Int) (bytes : Nat) : Option (Term × List Term × Nat) := do
  let address ← E.lookupEq (Reg.real64 base)
  let (lookupEvent, displacement, mapTerm) ← lookupAddress64 address
  let layout ← Anchor.layout? E mapTerm
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

theorem mapWriteObservation_frozen (E : List Expr) (Pg : List Predicate)
    (base : Nat) (offset : Int) (bytes : Nat)
    (map : Term) (key : List Term) (elementOff : Nat)
    (h : mapWriteObservation E Pg base offset bytes = some (map, key, elementOff)) :
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

theorem mapWriteKeyAt_expr_update (E updates : List Expr) (Pg : List Predicate)
    (event : NodeId) :
    mapWriteKeyAt (SemState.mk (updateExpr E updates) Pg .empty).predicates event =
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

private def storeEffect (event : NodeId) (mem : Mem) (E : List Expr)
    (Pg : List Predicate) (bytes base : Nat)
    (offset : Int) (source : Term) : Except RejectReason (ExprEffect × List Predicate) := do
  let access ← resolveAccess mem E base offset bytes true Pg
  let (updates, writes) ← writeAccess E access source
  let predicates ← match access with
    | .packet a => pure [.packetWrite event a.κ a.offset (8 * bytes) source a.compound]
    | .mem .packet start bits => do
      let some p := entryParams? E | throw .undefinedSrc
      pure [.packetWrite event p.κPacket (start / 8) bits source none]
    | .mem (.map _ _) _ _ => do
      let some (map, frozen, elementOff) := mapWriteObservation E Pg base offset bytes
        | throw .undefinedSrc
      pure (mapWriteObservations event map frozen elementOff bytes source)
    | .mem _ _ _ => pure []
  pure (⟨Expr.nil, updates, writes⟩, predicates)

private def memoryReg (E : List Expr) (r : Nat) : Except RejectReason Term := do
  if r > 10 then throw .undefinedSrc
  let some value := E.lookupEq (Reg.real64 r) | throw .undefinedSrc
  if value.width != .w64 then throw .undefinedSrc
  pure value

/-- Sequential numeric RMW on canonical stack or Map cells.
DW stack memory is assembled once from the two old SW32 cells, updated once at
64 bits, then split into simultaneous assignments. No concurrency observation is added. -/
private def atomicEffect (mem : Mem) (E : List Expr)
    (w : Width) (op : AtomicOp) (base src : Nat) (offset : Int)
    (Pg : List Predicate := []) :
    Except RejectReason (ExprEffect × List Predicate) := do
  if op.returnsSource && src ≥ 10 then throw .undefinedSrc
  let source ← memoryReg E src
  let access ← resolveAccess mem E base offset (w.bits / 8) true Pg
  match access with
  | .packet _ => throw .unsupported
  | .mem slot start bits =>
    match slot with
    | .stack | .map _ _ =>
      if bits != w.bits || start % w.bits != 0 then throw .undefinedSrc
    | _ => throw .unsupported
  let (_, oldMemory) ← readAccess mem E access
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
  let (_, writes) ← writeAccess E access (aluResult w value)
  let updates := if op.returnsSource then
      Expr.nil.insertEq (Reg.real64 src) (aluResult w a)
    else if op == .cmpxchg then Expr.nil.insertEq (Reg.real64 0) (aluResult w a)
    else Expr.nil
  pure (⟨Expr.nil, updates, writes⟩, [])

/-- Value effects read their sources and partial-field old values from E.
Control flow and helper calls belong to Step. -/
def exprEffects (event : NodeId) (mem : Mem) (E : List Expr) (i : Insn)
    (Pg : List Predicate := []) :
    Except RejectReason (ExprEffect × List Predicate) := do
  if !E.keysUnique || !E.wellTyped then throw .undefinedSrc
  match i with
  | .ldx bytes dst base offset | .loadAcq bytes dst base offset =>
    if dst > 9 then throw .undefinedSrc
    let access ← resolveAccess mem E base offset bytes false Pg
    let (writes, value) ← readAccess mem E access
    pure (⟨Expr.nil, Expr.nil.insertEq (Reg.real64 dst) value, writes⟩, [])
  | .memsx bytes dst base offset =>
    if dst > 9 || ![1, 2, 4].contains bytes then throw .undefinedSrc
    let access ← resolveAccess mem E base offset bytes false Pg
    let (writes, value) ← readAccess mem E access
    pure (⟨Expr.nil, Expr.nil.insertEq (Reg.real64 dst)
      (sStar (8 * bytes) .w64 64 value), writes⟩, [])
  | .stx bytes base src offset | .storeRel bytes base src offset =>
    let source ← memoryReg E src
    storeEffect event mem E Pg bytes base offset source
  | .st bytes base bits offset =>
    storeEffect event mem E Pg bytes base offset (Term.C64 (M 64 (s 32 bits.toNat)))
  | .atomic w op base src offset => atomicEffect mem E w op base src offset Pg
  | .mov _ _ _ | .binary _ _ _ _ | .neg _ _ | .movsx _ _ _ _ | .endian _ _ _ =>
    let some updates := expr E i | throw .undefinedSrc
    pure (⟨Expr.nil, updates, []⟩, [])
  | .exit => pure (⟨Expr.nil, Expr.nil, []⟩, [])
  | .illegal _ => throw .localReject
  | _ => throw .localReject

private def accessAt (p : EntryParams) (mem : Mem) (E : List Expr) (base : Nat) (offset : Int)
    (bytes : Nat) (isWrite : Bool) (maps : List MapLayout := [])
    (preds : List Predicate := []) :=
  resolveAccess mem (host p E maps) base offset bytes isWrite preds

private def effectsAt (p : EntryParams) (event : NodeId) (mem : Mem) (E : List Expr) (i : Insn)
    (maps : List MapLayout := []) (Pg : List Predicate := []) :=
  exprEffects event mem (host p E maps) i Pg

private def bytesAt (p : EntryParams) (mem : Mem) (E : List Expr) (addr : Term) (n : Nat) :=
  stackBytes mem (host p E) addr n

private def rootAt (p : EntryParams) (mem : Mem) (E : List Expr) :=
  packetRoot mem (host p E)

private def bufferAt (p : EntryParams) (mem : Mem) (E : List Expr) (address : Term) (n : Nat)
    (maps : List MapLayout := []) :=
  availableBufferBytes mem (host p E maps) address n

private def memoryEntry : EntryParams :=
  ⟨Term.V64 1, Term.V64 0, Term.V32 2, 16, 3, 4, 5⟩

private def applied (mem : Mem) (effect : ExprEffect) : Option Mem :=
  (mem.apply effect.writes).toOption

private def stackWord (mem : Mem) (unit value : Nat) : Option Mem :=
  (mem.write .stack ((508 - 4 * unit) * 8) ⟨[.const 32 value]⟩).toOption

#guard relativeOffset memoryEntry.tSp
  (idStar .w64 (addStar .w64 memoryEntry.tSp (Term.C64 (M 64 (-4))))) == some (-4)
#guard match buildE0 memoryEntry with
  | .ok σ => match accessAt memoryEntry σ.mem σ.exprs 10 (-4) 4 false with
    | .ok (.mem .stack start bits) => start == 508 * 8 && bits == 32
    | _ => false
  | _ => false
#guard match buildE0 memoryEntry with
  | .ok σ => match accessAt memoryEntry σ.mem σ.exprs 1 8 4 false with
    | .error .undefinedSrc => true
    | _ => false
  | _ => false
#guard Id.run do
  let .ok σ := buildE0 memoryEntry | return false
  let .ok (loaded, []) := effectsAt memoryEntry 0 σ.mem σ.exprs (.ldx 4 2 1 0) | return false
  let E := σ.exprs.override loaded.delta
  let .error .undefinedSrc := accessAt memoryEntry σ.mem E 2 13 4 false | return false
  return loaded.updates.lookupEq (Reg.real64 2) == rootAt memoryEntry σ.mem E

private def stackRoundTripCheck : Bool := Id.run do
  let .ok σ := buildE0 memoryEntry | return false
  let E := σ.exprs.insertEq (Reg.real64 0) (Term.C64 0x1122334455667788)
  let .ok (stored, []) := effectsAt memoryEntry 0 σ.mem E (.stx 8 10 0 (-8)) | return false
  let some mem := applied σ.mem stored | return false
  let .ok (loaded, []) := effectsAt memoryEntry 0 mem E (.ldx 8 2 10 (-8)) | return false
  let .ok (byte, []) := effectsAt memoryEntry 0 σ.mem E (.stx 1 10 0 (-4)) | return false
  let some byteMem := applied σ.mem byte | return false
  let .error .undefinedSrc := effectsAt memoryEntry 0 byteMem E (.ldx 4 2 10 (-4)) | return false
  let .ok (one, []) := effectsAt memoryEntry 0 byteMem E (.ldx 1 2 10 (-4)) | return false
  return stored.inputs.isEmpty && stored.updates.isEmpty && stored.writes.length == 1 &&
    loaded.updates.lookupEq (Reg.real64 2) == some (Term.C64 0x1122334455667788) &&
    one.updates.lookupEq (Reg.real64 2) == some (Term.C64 0x88)

#guard stackRoundTripCheck

private def packetMaterializationCheck : Bool := Id.run do
  let .ok σ := buildE0 memoryEntry | return false
  let .ok (loaded, []) := effectsAt memoryEntry 0 σ.mem σ.exprs (.ldx 4 2 1 0) | return false
  let E := σ.exprs.override loaded.delta
  let .ok (first, []) := effectsAt memoryEntry 0 σ.mem E (.ldx 4 0 2 0) | return false
  let some mem := applied σ.mem first | return false
  let .ok (second, []) := effectsAt memoryEntry 0 mem E (.ldx 4 0 2 0) | return false
  return first.writes.length == 4 && first.updates.length == 1 &&
    second.writes.isEmpty && first.validFor E

#guard packetMaterializationCheck

private def packetRootAliasCheck : Bool := Id.run do
  let .ok σ := buildE0 memoryEntry | return false
  let .ok (loaded, []) := effectsAt memoryEntry 0 σ.mem σ.exprs (.ldx 4 6 1 0) | return false
  let E := σ.exprs.override loaded.delta
  let some value := E.lookupEq (Reg.real64 6) | return false
  let .ok (.mem .packet start bits) := accessAt memoryEntry σ.mem E 6 0 2 false | return false
  return rootAt memoryEntry σ.mem E == some value && value.width == .w64 &&
    start == 0 && bits == 16 && memoryEntry.tData.width == .w32

#guard packetRootAliasCheck

private def partialStackCheck : Bool := Id.run do
  let .ok σ := buildE0 memoryEntry | return false
  let some mem := stackWord σ.mem 0 0x11223344 | return false
  let E := σ.exprs.insertEq (Reg.real64 0) (Term.C64 0xaa)
    |>.insertEq (Reg.real64 3)
      (idStar .w64 (addStar .w64 memoryEntry.tSp (Term.C64 (M 64 (-4)))))
  let .ok (stored, []) := effectsAt memoryEntry 0 mem E (.stx 1 3 0 1) | return false
  let some mem := applied mem stored | return false
  let .ok (loaded, []) := effectsAt memoryEntry 0 mem E (.ldx 4 2 10 (-4)) | return false
  return stored.inputs.isEmpty &&
    loaded.updates.lookupEq (Reg.real64 2) == some (Term.C64 0x1122aa44)

#guard partialStackCheck
#guard Id.run do
  let p : EntryParams := ⟨Term.C64 0x1000, Term.V64 0, Term.C32 0x1000, 16, 3, 4, 5⟩
  let .ok σ := buildE0 p | return false
  let .error .undefinedSrc := accessAt p σ.mem σ.exprs 1 0 4 false | return false
  return true

private def lookupPointer : Term :=
  star .w64 (.externalResult 7 0) [Term.C64 1, Term.C64 42, Term.V64 9]

private def lookupMemoryCheck : Bool := Id.run do
  let .ok σ := buildE0 memoryEntry | return false
  let maps : List MapLayout := [⟨42, 4, 16⟩]
  let keyBytes := [Term.C64 1, Term.C64 2, Term.C64 3, Term.C64 4]
  let lookup := Predicate.helper 7 .lookup ([Term.C64 42, Term.V64 9] ++ keyBytes)
  let .ok key := keyTile keyBytes | return false
  let held := Term.regVar 7 (Reg.real64 0)
  let .ok tile := Tile.ofTerm held 64 | return false
  let .ok mem := σ.mem.write (.map 42 key) 0 tile | return false
  let E := σ.exprs.insertEq (Reg.real64 0) lookupPointer
  let .ok (.mem slot start bits) := accessAt memoryEntry mem E 0 0 8 false maps [lookup]
    | return false
  let .ok (_, value) := readAccess mem E (.mem slot start bits) | return false
  let .ok (_, writes) := writeAccess E (.mem slot start bits) (Term.C64 99) | return false
  let .ok mem := mem.apply writes | return false
  let .ok (_, next) := readAccess mem E (.mem slot start bits) | return false
  let .error .undefinedSrc := readAccess mem E (.mem slot (8 * 8) 64) | return false
  let .ok (_, extended) := writeAccess E (.mem slot (8 * 8) 64) (Term.C64 99) | return false
  let .ok mem := mem.apply extended | return false
  let .ok (_, filled) := readAccess mem E (.mem slot (8 * 8) 64) | return false
  let .error .undefinedSrc := accessAt memoryEntry mem E 0 7 2 false maps [lookup] | return false
  let .error .undefinedSrc := accessAt memoryEntry mem E 0 (-1) 1 false maps [lookup] | return false
  let .error .undefinedSrc := accessAt memoryEntry mem E 0 16 1 false maps [lookup] | return false
  let .error .undefinedSrc := accessAt memoryEntry mem E 0 0 8 false maps | return false
  return slot == .map 42 key && start == 0 && bits == 64 &&
    value == held && next == Term.C64 99 && filled == Term.C64 99

#guard lookupMemoryCheck

/-- The key pointer is not a current stack alias: only Pg supplies the frozen key. -/
private def mapStoreExprs : List Expr :=
  Expr.nil.insertEq (Reg.real64 0)
    (star .w64 (.externalResult 7 0)
      [Term.C64 1, Term.C64 1077412584, Term.V64 9])
    |>.insertEq (Reg.real64 1) (idStar .w64 (Term.V64 11))

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
    effectsAt memoryEntry ev .empty E (.stx 8 0 1 0) mapStoreLayouts [mapStoreLookup]
    | return false
  let .ok (_, partialPredicates) :=
    effectsAt memoryEntry (ev + 1) .empty E (.stx 4 0 1 4) mapStoreLayouts [mapStoreLookup]
    | return false
  return predicates ==
      [.mapWrite ev (Term.C64 1077412584) mapStoreKey 0 32
        (star .w32 (.extract 0 32 64) [source]),
       .mapWrite ev (Term.C64 1077412584) mapStoreKey 4 32
        (star .w32 (.extract 32 32 64) [source])] &&
    partialPredicates ==
      [.mapWrite (ev + 1) (Term.C64 1077412584) mapStoreKey 4 32 source] &&
    effect.inputs == Expr.nil && effect.updates.isEmpty && effect.writes.length == 1 &&
    effect.validFor E &&
      match effect.writes with
      | [w] =>
        match (Mem.empty.apply [w]).bind fun mem =>
            (mem.read w.slot 0 64).bind (·.toW64) with
        | .ok stored => stored == source
        | _ => false
      | _ => false

/-- Interpret the saved key and both DW observations under explicit ν/θ.
The old key survives a live-stack overwrite; extract/extend wrappers are not
part of this behavior contract. The value effect must store the full old source. -/
private def symbolicMapStoreFrozenKeyCheck : Bool := Id.run do
  let keyPtr := addStar .w64 memoryEntry.tSp (Term.C64 (M 64 (-4)))
  let .ok originalMem := Mem.write .empty .stack (508 * 8) ⟨[.proj 32 (Term.V32 12) 0]⟩
    | return false
  let some frozen := bytesAt memoryEntry originalMem mapStoreExprs keyPtr 4 | return false
  let Pg := [.helper 7 .lookup ([Term.C64 1077412584, keyPtr] ++ frozen)]
  let E := mapStoreExprs.insertEq (Reg.real64 0)
    (star .w64 (.externalResult 7 0) [Term.C64 1, Term.C64 1077412584, keyPtr])
  let .ok (effect, predicates) :=
    effectsAt memoryEntry 77 .empty E (.stx 8 0 1 0) mapStoreLayouts Pg | return false
  let [.mapWrite 77 mapLo keyLo 0 32 valueLo, .mapWrite 77 mapHi keyHi 4 32 valueHi] :=
    predicates | return false
  let some updated := (match effect.writes with
    | [w] => (Tile.toW64 w.tile).toOption
    | _ => none) | return false
  let stored := updated
  let .ok liveMem := originalMem.write .stack (508 * 8) ⟨[.const 32 0]⟩ | return false
  let some liveKey := bytesAt memoryEntry liveMem E keyPtr 4 | return false
  if !effect.validFor E || !effect.inputs.isEmpty ||
      !effect.updates.isEmpty || effect.writes.length != 1 ||
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
    match effectsAt memoryEntry 77 .empty mapStoreExprs (.stx 8 0 1 0) mapStoreLayouts Pg with
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
    match effectsAt memoryEntry 77 .empty mapStoreExprs i maps [mapStoreLookup] with
    | .error .undefinedSrc => true
    | _ => false

private def nonMapCellStoreObservationsCheck : Bool := Id.run do
  let .ok σ := buildE0 memoryEntry | return false
  let E := σ.exprs.insertEq (Reg.real64 0) (Term.C64 99)
  let .ok (_, []) :=
    effectsAt memoryEntry 77 σ.mem E (.stx 8 10 0 (-8)) mapStoreLayouts [mapStoreLookup]
    | return false
  let .ok (_, []) :=
    effectsAt memoryEntry 78 σ.mem E (.stx 4 1 0 0) mapStoreLayouts [mapStoreLookup]
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
  let some mem := stackWord σ.mem 0 0x11223344 | return false
  return bytesAt memoryEntry mem σ.exprs ptr 4 ==
    some [Term.C64 0x44, Term.C64 0x33, Term.C64 0x22, Term.C64 0x11] &&
    (bytesAt memoryEntry σ.mem σ.exprs ptr 4).isNone &&
    (bytesAt memoryEntry mem σ.exprs ptr 5).isNone

private def readConst (mem : Mem) (start bits : Nat) : Option Nat :=
  match (mem.read .stack start (start + bits)).toOption with
  | some tile => match tile.slices with
    | [.const _ value] => some value
    | _ => none
  | none => none

private def atomicStackSnapshotCheck : Bool := Id.run do
  let .ok σ := buildE0 memoryEntry | return false
  let some mem := stackWord σ.mem 1 0xffffffff | return false
  let some mem := stackWord mem 0 1 | return false
  let E := σ.exprs.insertEq (Reg.real64 2) (Term.C64 1)
    |>.insertEq (Reg.real64 0) (Term.C64 0x1ffffffff)
  let .ok (add, []) := effectsAt memoryEntry 1 mem E
    (.atomic .w64 (.add true) 10 2 (-8)) | return false
  let some added := applied mem add | return false
  let .ok (cmp, []) := effectsAt memoryEntry 2 mem E
    (.atomic .w64 .cmpxchg 10 2 (-8)) | return false
  let some compared := applied mem cmp | return false
  let failedCompare := E.insertEq (Reg.real64 0) (Term.C64 0)
  let .ok (miss, []) := effectsAt memoryEntry 3 mem failedCompare
    (.atomic .w64 .cmpxchg 10 2 (-8)) | return false
  let some missed := applied mem miss | return false
  let some missingHigh := stackWord σ.mem 1 1 | return false
  let .error .undefinedSrc := effectsAt memoryEntry 4 missingHigh
    (σ.exprs.insertEq (Reg.real64 2) (Term.C64 1))
    (.atomic .w64 (.add true) 10 2 (-8)) | return false
  return readConst added (504 * 8) 64 == some 0x200000000 &&
    add.updates.lookupEq (Reg.real64 2) == some (Term.C64 0x1ffffffff) &&
    readConst compared (504 * 8) 64 == some 1 &&
    cmp.updates.lookupEq (Reg.real64 0) == some (Term.C64 0x1ffffffff) &&
    readConst missed (504 * 8) 64 == some 0x1ffffffff &&
    miss.updates.lookupEq (Reg.real64 0) == some (Term.C64 0x1ffffffff) &&
    add.validFor E && cmp.validFor E && miss.validFor failedCompare

private def atomicMapFieldCheck : Bool := Id.run do
  let .ok key := keyTile mapStoreFrozenKey | return false
  let .ok mem := Mem.write .empty (.map 1077412584 key) 0
    ⟨[.const 64 0x11223344ffffffff]⟩ | return false
  let E := mapStoreExprs.insertEq (Reg.real64 2) (Term.C64 1)
  let .ok (effect, []) := effectsAt memoryEntry 9 mem E
    (.atomic .w32 (.add true) 0 2 0) mapStoreLayouts [mapStoreLookup] | return false
  let .error .undefinedSrc := effectsAt memoryEntry 9 mem E
    (.atomic .w32 (.add false) 0 2 1) mapStoreLayouts [mapStoreLookup] | return false
  let some mem := applied mem effect | return false
  let stored := match (mem.read (.map 1077412584 key) 0 64).bind (·.toW64) with
    | .ok term => some term
    | _ => none
  return stored == some (Term.C64 0x1122334400000000) &&
    effect.updates.lookupEq (Reg.real64 2) == some (Term.C64 0xffffffff) &&
    effect.updates.length == 1 && effect.validFor E

private def immediateAndSignedMemoryCheck : Bool := Id.run do
  let .ok σ := buildE0 memoryEntry | return false
  let .ok (stored, []) := effectsAt memoryEntry 0 σ.mem σ.exprs
    (.st 8 10 0xffffff80 (-8)) | return false
  let some mem := applied σ.mem stored | return false
  let .ok (signed, []) := effectsAt memoryEntry 1 mem σ.exprs (.memsx 1 2 10 (-8)) | return false
  let .ok (unsigned, []) := effectsAt memoryEntry 2 mem σ.exprs (.loadAcq 1 2 10 (-8)) | return false
  let E := σ.exprs.insertEq (Reg.real64 2) (Term.C64 0x55)
  let .ok (released, []) := effectsAt memoryEntry 3 mem E (.storeRel 1 10 2 (-7)) | return false
  let some releasedMem := applied mem released | return false
  return signed.updates.lookupEq (Reg.real64 2) == some (Term.C64 0xffffffffffffff80) &&
    unsigned.updates.lookupEq (Reg.real64 2) == some (Term.C64 0x80) &&
    readConst releasedMem (504 * 8) 32 == some 0xffff5580

#guard atomicStackSnapshotCheck
#guard atomicMapFieldCheck
#guard immediateAndSignedMemoryCheck

#guard relativeOffset memoryEntry.tSp (subStar .w64 memoryEntry.tSp (Term.C64 8)) ==
  some (-8)

#guard Id.run do
  let p : EntryParams := ⟨Term.C64 0x1000, Term.C64 0x2000, Term.C32 0x2000,
    4, 0, 0, 0⟩
  let .ok initial := buildE0 p | return false
  let some mem := stackWord initial.mem 0 0x11223344 | return false
  let .ok mem := mem.write .packet 0 ⟨[.const 8 0x55]⟩ | return false
  let some [open0] := bufferAt p initial.mem initial.exprs (Term.C64 0x2000) 1 | return false
  return bufferAt p mem initial.exprs (Term.C64 0x1fff) 1 == some [Term.C64 0x11] &&
    bufferAt p mem initial.exprs (Term.C64 0x2000) 1 == some [Term.C64 0x55] &&
    (bufferAt p mem initial.exprs (Term.C64 0x1fff) 2).isNone &&
    (eval (solve open0)).isNone

end EBPF

