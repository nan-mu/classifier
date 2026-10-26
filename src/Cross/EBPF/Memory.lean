import Cross.EBPF.Create
import Interface.Update
import Cross.EBPF.Expression
import Expression.Virtual
import Expression.Resource.MapLayout
import Observation.Helper
namespace Cross.EBPF
open Term Term.Value Expression Observation Interface Interface.Step Wire Node

inductive ResolvedAccess where
  | cell (reg : Reg)
  | packet (access : PacketAccess)
  deriving Repr, Inhabited

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

/-- Offset, Map term, key-and-cell tail, and the undisplaced return term.
The tail's key prefix length comes from the layout. -/
def lookupAddress64 : Term → Option (Int × Term × List Term × Term)
  | .app .w64 (.id .w64) [a] => lookupAddress64 a
  | .app .w64 (.externalResult 0) (id :: map :: rest) =>
    if eval (solve id) == some 1 && map.width == .w64 then
      some (0, map, rest, .app .w64 (.externalResult 0) (id :: map :: rest))
    else none
  | .app .w64 (.add .w64) [a, b] =>
    match eval (solve a), eval (solve b) with
    | none, some c => do
      let (offset, map, rest, base) ← lookupAddress64 a
      pure (offset + s 64 c, map, rest, base)
    | some c, none => do
      let (offset, map, rest, base) ← lookupAddress64 b
      pure (offset + s 64 c, map, rest, base)
    | _, _ => none
  | .app .w64 (.sub .w64) [a, b] =>
    match eval (solve a), eval (solve b) with
    | none, some c => do
      let (offset, map, rest, base) ← lookupAddress64 a
      pure (offset - s 64 c, map, rest, base)
    | _, _ => none
  | _ => none

theorem lookupAddress64_const (w : Width) (n : Nat) :
    lookupAddress64 (.const w n) = none := rfl

theorem lookupAddress64_ne_zero (source : Term) (offset : Int) (map : Term)
    (rest : List Term) (base : Term)
    (h : lookupAddress64 source = some (offset, map, rest, base)) :
    source ≠ Term.C64 0 := by
  intro hz
  subst source
  cases h

private def contextParts (d : Int) (bytes : Nat)
    (byteView : Bool := false) : Option ResolvedAccess := do
  if !(d ≥ 0 && d.toNat / 4 < 2 && d.toNat % 4 + bytes ≤ 4 &&
      ((d.toNat % 4 == 0 && bytes == 4) || (byteView && bytes == 1))) then none
  let field ← ContextField.ofXdp (d.toNat / 4)
  let lo := 8 * (d.toNat % 4)
  some (.cell (.context field lo (lo + 8 * bytes)))

private def stackParts (d : Int) (bytes : Nat) : Option ResolvedAccess :=
  if d < -512 || d ≥ 0 || d + Int.ofNat bytes > 0 then none
  else
    let n := (d + 512).toNat
    let within := n % 4
    let fits := if bytes == 8 then within == 0 else within + bytes ≤ 4
    if fits then
      let lo := n * 8
      some (.cell (.stack lo (lo + 8 * bytes)))
    else none

def readAccess (E : List Expr) (a : ResolvedAccess) :
    Except RejectReason (List Expr × Term) := do
  match a with
  | .packet access =>
    let some result := access.read E .w64 true | throw .undefinedSrc
    pure (result.inputs, result.value)
  | .cell reg =>
    let some value := CellAccess.read ⟨reg⟩ E .w64 true | throw .undefinedSrc
    pure (Expr.nil, value)

/-- Frozen little-endian stack bytes. Cell reads widen each extracted 32-bit
stack field with zStar 8 .w64 32; unavailable bytes are never materialized. -/
def stackBytes (E : List Expr) (addr : Term) (n : Nat) : Option (List Term) := do
  let p ← entryParams? E
  let displacement ← relativeOffset p.tSp addr
  (List.range n).mapM fun j => do
    let .cell reg ← stackParts (displacement + Int.ofNat j) 1 | none
    let (_, value) ← (readAccess E (.cell reg)).toOption
    pure value

/-- The packet base is the widened context data field. Missing data authorizes
no packet candidate. -/
def packetRoot (E : List Expr) : Option Term := do
  let _p ← entryParams? E
  let data ← contextValue E .data
  «seal» 64 (zStar data.semanticBits .w64 data.width.bits data)

/-- Resolve against the executing full base equality, never against a mutable
entry-register name. Content availability is checked by readAccess/writeAccess.
Lookup anchors word zero; other Map words have no implicit content relation
and accesses reject undefinedSrc until such a relation is explicitly available.
Re-carrier saved native stack bytes without consulting the current key buffer. -/
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

private def packetAccess (base : Term)
    (displacement : PacketOffset) (bytes : Nat) : ResolvedAccess :=
  .packet { displacement, bytes, order := .little, inputBase := some base }

def resolveAddress (E : List Expr) (address : Term) (offset : Int)
    (bytes : Nat) (contextByteView : Bool := false)
    (preds : List Observation := []) :
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
  if let some root := packetRoot E then
    if let some displacement := relativeOffset root address then
      let o := displacement + offset
      if o ≥ 0 && o.toNat + bytes ≤ p.packetBytes then
        candidates := packetAccess p.tData (.c o.toNat) bytes :: candidates
    else if let some displacement := packetDisplacement E root address then
      if offset ≥ 0 then
        let accessAddress := addStar .w64 address (Term.C64 offset.toNat)
        if let some ending := contextValue E .dataEnd then
          if let some _ := packetBoundWitness E root accessAddress ending bytes preds then
            candidates := packetAccess p.tData
              (displacement.plus (.c offset.toNat)) bytes :: candidates
  if let some (displacement, mapTerm, rest, base) := lookupAddress64 address then
    if let some _layout := Anchor.layout? E mapTerm then
      let rel := displacement + offset
      if accessWithin E base rel bytes && rel.toNat % 8 + bytes ≤ 8 then
        if let some id := eval (solve mapTerm) then
          if let some key := lookupKey E mapTerm rest mapWriteKeyByte then
            let lo := rel.toNat * 8
            candidates := .cell (.map id key lo (lo + 8 * bytes)) :: candidates
  match candidates with
  | [a] => pure a
  | _ => throw .undefinedSrc

def resolveAccess (E : List Expr) (base : Nat) (offset : Int)
    (bytes : Nat) (isWrite : Bool)
    (preds : List Observation := []) :
    Except RejectReason ResolvedAccess := do
  let _ := isWrite
  if base > 10 then throw .undefinedSrc
  let some address := readReg E base | throw .undefinedSrc
  resolveAddress E address offset bytes false preds

private inductive BufferOrigin where
  | stack
  | context
  | map (object : Term)
  | packet
  deriving BEq

private def bufferOrigin (address : Term) : ResolvedAccess → Option BufferOrigin
  | .packet _ => some .packet
  | .cell (.stack ..) => some .stack
  | .cell (.context ..) => some .context
  | .cell (.packet ..) => some .packet
  | .cell (.map ..) => do
    let (_, object, _, _) ← lookupAddress64 address
    some (.map object)
  | .cell (.real ..) => none

/-- Freeze one complete buffer with a single resource origin.
A concrete packet byte may materialize `Packet([8*o, 8*o+8))`. Stack, map, and
context still require a current equality. -/
def availableBufferBytes (E : List Expr) (address : Term)
    (n : Nat) (preds : List Observation := []) : Option (List Term) := do
  let _p ← entryParams? E
  if !E.keysUnique || !E.wellTyped || address.width != .w64 then none else do
    let mut origin : Option BufferOrigin := none
    let mut bytes := []
    for j in List.range n do
      let access ← (resolveAddress E address (Int.ofNat j) 1 true preds).toOption
      let candidate ← bufferOrigin address access
      if let some previous := origin then
        if previous != candidate then none
      origin := some candidate
      let (inputs, value) ← (readAccess E access).toOption
      let allowInputs := match access with
        | .packet _ | .cell (.packet ..) => true
        | _ => false
      if !allowInputs && !inputs.isEmpty then none
      bytes := value :: bytes
    some bytes.reverse

def writeAccess (E : List Expr) (a : ResolvedAccess) (source : Term) :
    Except RejectReason (List Expr) := do
  if source.width != .w64 then throw .undefinedSrc
  match a with
  | .packet access =>
    let some updates := access.write E source | throw .undefinedSrc
    pure updates
  | .cell reg =>
    let some updates := CellAccess.write ⟨reg⟩ E source | throw .undefinedSrc
    pure updates

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

/-- Map writes read the key from the lookup return term, not from a later buffer. -/
def mapWriteObservation (E : List Expr)
    (base : Nat) (offset : Int) (bytes : Nat) : Option (Term × List Term × Nat) := do
  let address ← E.lookupEq (Reg.real64 base)
  let (displacement, mapTerm, rest, baseTerm) ← lookupAddress64 address
  let rel := displacement + offset
  if !accessWithin E baseTerm rel bytes || rel.toNat % 8 + bytes > 8 then none
  else
    let key ← lookupKey E mapTerm rest mapWriteKeyByte
    some (mapTerm, key, rel.toNat)

/-- A native Map DW write observes the low half before the high half, while the
value effect still uses the complete pre-state source. Narrow stores keep it intact. -/
private def mapWriteObservations (map : Term) (frozen : List Term)
    (elementOff bytes : Nat) (source : Term) : List Observation :=
  if bytes == 8 then
    [.mapWrite map frozen elementOff 32 (star .w32 (.extract 0 32 64) [source]),
      .mapWrite map frozen (elementOff + 4) 32 (star .w32 (.extract 32 32 64) [source])]
  else [.mapWrite map frozen elementOff (8 * bytes) source]

theorem mapWriteObservations_saved_key (map : Term)
    (key : List Term) (elementOff bytes : Nat) (source : Term) (p : Observation)
    (h : p ∈ mapWriteObservations map key elementOff bytes source) :
    p.savedMapKey? = some key := by
  unfold mapWriteObservations at h
  split at h
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl <;> rfl
  · simp only [List.mem_singleton] at h
    subst p
    rfl

private def storeEffect (E : List Expr)
    (Pg : List Observation) (bytes base : Nat)
    (offset : Int) (source : Term) : Except RejectReason (ExprEffect × List Observation) := do
  let access ← resolveAccess E base offset bytes true Pg
  let updates ← writeAccess E access source
  let predicates ← match access with
    | .packet a =>
      match a.constOffset? with
      | some o => pure [Observation.packetWrite o (8 * bytes) source]
      | none => pure []
    | .cell (.map ..) => do
      let some (map, frozen, elementOff) := mapWriteObservation E base offset bytes
        | throw .undefinedSrc
      pure (mapWriteObservations map frozen elementOff bytes source)
    | .cell _ => pure []
  pure ({ updates }, predicates)

private def memoryReg (E : List Expr) (r : Nat) : Except RejectReason Term := do
  let some value := readReg E r | throw .undefinedSrc
  if value.width != .w64 then throw .undefinedSrc
  pure value

/-- Sequential numeric RMW on canonical stack or Map cells.
DW stack memory is assembled once from the two old SW32 cells, updated once at
64 bits, then split into simultaneous assignments. No concurrency observation is added. -/
private def atomicEffect (E : List Expr)
    (w : Width) (op : AtomicOp) (base src : Nat) (offset : Int)
    (Pg : List Observation := []) :
    Except RejectReason (ExprEffect × List Observation) := do
  if op.returnsSource && src ≥ 10 then throw .undefinedSrc
  let source ← memoryReg E src
  let access ← resolveAccess E base offset (w.bits / 8) true Pg
  match access with
  | .cell (.stack lo hi) | .cell (.map _ _ lo hi) =>
    if hi - lo != w.bits || lo % w.bits != 0 then throw .undefinedSrc
  | _ => throw .unsupported
  let (_, oldMemory) ← readAccess E access
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
  let cell ← writeAccess E access (aluResult w value)
  let regUpdates ← if op.returnsSource then
      match assignReal w src a with
      | some rows => pure rows
      | none => throw .undefinedSrc
    else if op == .cmpxchg then
      match assignReal w 0 a with
      | some rows => pure rows
      | none => throw .undefinedSrc
    else pure Expr.nil
  pure ({ updates := regUpdates ++ cell }, [])

/-- Value effects read their sources and partial-field old values from E.
Control flow and helper calls belong to Step. -/
def exprEffects (_event : NodeId) (E : List Expr) (i : Insn)
    (Pg : List Observation := []) :
    Except RejectReason (ExprEffect × List Observation) := do
  if !E.keysUnique || !E.wellTyped then throw .undefinedSrc
  match i with
  | .ldx bytes dst base offset | .loadAcq bytes dst base offset =>
    if dst > 9 then throw .undefinedSrc
    let access ← resolveAccess E base offset bytes false Pg
    let (inputs, value) ← readAccess E access
    let some updates := assignReal .w64 dst value | throw .undefinedSrc
    pure ({ inputs, updates }, [])
  | .memsx bytes dst base offset =>
    if dst > 9 || ![1, 2, 4].contains bytes then throw .undefinedSrc
    let access ← resolveAccess E base offset bytes false Pg
    let (inputs, value) ← readAccess E access
    let some updates := assignReal .w64 dst (sStar (8 * bytes) .w64 64 value)
      | throw .undefinedSrc
    pure ({ inputs, updates }, [])
  | .stx bytes base src offset | .storeRel bytes base src offset =>
    let source ← memoryReg E src
    storeEffect E Pg bytes base offset source
  | .st bytes base bits offset =>
    storeEffect E Pg bytes base offset (Term.C64 (M 64 (s 32 bits.toNat)))
  | .atomic w op base src offset => atomicEffect E w op base src offset Pg
  | .mov _ _ _ | .binary _ _ _ _ | .neg _ _ | .movsx _ _ _ _ | .endian _ _ _ =>
    let some updates := expr E i | throw .undefinedSrc
    pure ({ updates }, [])
  | .exit => pure ({}, [])
  | .illegal _ => throw .localReject
  | _ => throw .localReject

private def accessAt (p : EntryParams) (E : List Expr) (base : Nat) (offset : Int)
    (bytes : Nat) (isWrite : Bool) (maps : List MapLayout := [])
    (preds : List Observation := []) :=
  resolveAccess (host p E maps) base offset bytes isWrite preds

private def effectsAt (p : EntryParams) (event : NodeId) (E : List Expr) (i : Insn)
    (maps : List MapLayout := []) (Pg : List Observation := []) :=
  exprEffects event (host p E maps) i Pg

private def bytesAt (p : EntryParams) (E : List Expr) (addr : Term) (n : Nat) :=
  stackBytes (host p E) addr n

private def rootAt (p : EntryParams) (E : List Expr) :=
  packetRoot (host p E)

private def bufferAt (p : EntryParams) (E : List Expr) (address : Term) (n : Nat)
    (maps : List MapLayout := []) :=
  availableBufferBytes (host p E maps) address n

private def memoryEntry : EntryParams :=
  ⟨Term.V64 1, Term.V64 0, Term.V32 2, 16⟩

private def applyEffect (E : List Expr) (effect : ExprEffect) : List Expr :=
  (update ⟨E, []⟩ { exprs := effect.delta, predicates := [] }).exprs

private def putStackWord (E : List Expr) (unit value : Nat) : Option (List Expr) :=
  let lo := (508 - 4 * unit) * 8
  ((«seal» (Reg.stack lo (lo + 32)).bits (Term.C32 value) >>= fun stored => some (update ⟨E, []⟩ { exprs := [Expr.mkEq (.stack lo (lo + 32)) stored], predicates := [] }).exprs))

#guard relativeOffset memoryEntry.tSp
  (idStar .w64 (addStar .w64 memoryEntry.tSp (Term.C64 (M 64 (-4))))) == some (-4)
#guard match buildE0 memoryEntry with
  | .ok σ => match accessAt memoryEntry σ.exprs 10 (-4) 4 false with
    | .ok (.cell (.stack lo hi)) => lo == 508 * 8 && hi == lo + 32
    | _ => false
  | _ => false
#guard match buildE0 memoryEntry with
  | .ok σ => match accessAt memoryEntry σ.exprs 1 8 4 false with
    | .error .undefinedSrc => true
    | _ => false
  | _ => false
#guard Id.run do
  let .ok σ := buildE0 memoryEntry | return false
  let .ok (loaded, []) := effectsAt memoryEntry 0 σ.exprs (.ldx 4 2 1 0) | return false
  let E := applyEffect σ.exprs loaded
  let .error .undefinedSrc := accessAt memoryEntry E 2 13 4 false | return false
  return loaded.updates.lookupEq (Reg.real64 2) == rootAt memoryEntry E

private def stackRoundTripCheck : Bool := Id.run do
  let .ok σ := buildE0 memoryEntry | return false
  let E := (update ⟨σ.exprs, []⟩ { exprs := [Expr.mkEq (Reg.real64 0) (solve (Term.C64 0x1122334455667788))], predicates := [] }).exprs
  let .ok (stored, []) := effectsAt memoryEntry 0 E (.stx 8 10 0 (-8)) | return false
  let E8 := applyEffect E stored
  let .ok (loaded, []) := effectsAt memoryEntry 0 E8 (.ldx 8 2 10 (-8)) | return false
  let .ok (byte, []) := effectsAt memoryEntry 0 E (.stx 1 10 0 (-4)) | return false
  let E1 := applyEffect E byte
  let .error .undefinedSrc := effectsAt memoryEntry 0 E1 (.ldx 4 2 10 (-4)) | return false
  let .ok (one, []) := effectsAt memoryEntry 0 E1 (.ldx 1 2 10 (-4)) | return false
  let some loadedValue := loaded.updates.lookupEq (Reg.real64 2) | return false
  let some byteValue := one.updates.lookupEq (Reg.real64 2) | return false
  return stored.inputs.isEmpty && !stored.updates.isEmpty &&
    loadedValue == Term.C64 0x1122334455667788 &&
    byteValue == Term.C64 0x88

#guard stackRoundTripCheck

private def packetMaterializationCheck : Bool := Id.run do
  let .ok σ := buildE0 memoryEntry | return false
  let .ok (loaded, []) := effectsAt memoryEntry 0 σ.exprs (.ldx 4 2 1 0) | return false
  let E := applyEffect σ.exprs loaded
  let .ok (first, []) := effectsAt memoryEntry 0 E (.ldx 4 0 2 0) | return false
  let E2 := applyEffect E first
  let .ok (second, []) := effectsAt memoryEntry 0 E2 (.ldx 4 0 2 0) | return false
  return first.inputs.length == 4 && first.updates.length == 1 &&
    second.inputs.isEmpty && first.validFor E

#guard packetMaterializationCheck

private def packetRootAliasCheck : Bool := Id.run do
  let .ok σ := buildE0 memoryEntry | return false
  let .ok (loaded, []) := effectsAt memoryEntry 0 σ.exprs (.ldx 4 6 1 0) | return false
  let E := applyEffect σ.exprs loaded
  let some value := E.lookupEq (Reg.real64 6) | return false
  let .ok (.packet access) := accessAt memoryEntry E 6 0 2 false | return false
  return rootAt memoryEntry E == some value && value.width == .w64 &&
    access.constOffset? == some 0 && access.bytes == 2 &&
    memoryEntry.tData.width == .w32

#guard packetRootAliasCheck

private def partialStackCheck : Bool := Id.run do
  let .ok σ := buildE0 memoryEntry | return false
  let some stacked := putStackWord σ.exprs 0 0x11223344 | return false
  let E := (update ⟨stacked, []⟩ { exprs := [Expr.mkEq (Reg.real64 0) (solve (Term.C64 0xaa))], predicates := [] }).exprs
    |> (fun acc => (update ⟨acc, []⟩ { exprs := [Expr.mkEq (Reg.real64 3) (solve (idStar .w64 (addStar .w64 memoryEntry.tSp (Term.C64 (M 64 (-4))))))], predicates := [] }).exprs)
  let .ok (stored, []) := effectsAt memoryEntry 0 E (.stx 1 3 0 1) | return false
  let E2 := applyEffect E stored
  let .ok (loaded, []) := effectsAt memoryEntry 0 E2 (.ldx 4 2 10 (-4)) | return false
  let some value := loaded.updates.lookupEq (Reg.real64 2) | return false
  return stored.inputs.isEmpty && value == Term.C64 0x1122aa44

#guard partialStackCheck
#guard Id.run do
  let p : EntryParams := ⟨Term.C64 0x1000, Term.V64 0, Term.C32 0x1000, 16⟩
  let .ok σ := buildE0 p | return false
  let .error .undefinedSrc := accessAt p σ.exprs 1 0 4 false | return false
  return true

private def lookupKeyBytes : List Term :=
  [Term.C64 1, Term.C64 2, Term.C64 3, Term.C64 4]

private def lookupPointer : Term :=
  star .w64 (.externalResult 0) (Term.C64 1 :: Term.C64 42 :: lookupKeyBytes)

private def lookupMemoryCheck : Bool := Id.run do
  let .ok σ := buildE0 memoryEntry | return false
  let maps : List MapLayout := [⟨42, 4, 16⟩]
  let some key := lookupKeyBytes.mapM mapWriteKeyByte | return false
  let held := solve lookupPointer
  let cell := Reg.map 42 key 0 64
  let some seeded := ((«seal» (cell).bits held >>= fun stored => some (update ⟨σ.exprs, []⟩ { exprs := [Expr.mkEq cell stored], predicates := [] }).exprs)) | return false
  let pointed := (update ⟨seeded, []⟩ { exprs := [Expr.mkEq (Reg.real64 0) (solve lookupPointer)], predicates := [] }).exprs
  let E := (update ⟨pointed, []⟩ { exprs := [Expr.mkRel (Reg.real64 0) .leu (addStar .w64 lookupPointer (Term.C64 16))], predicates := [] }).exprs
  let .ok (.cell slot) := accessAt memoryEntry E 0 0 8 false maps | return false
  let .ok (_, value) := readAccess E (.cell slot) | return false
  let .ok writes := writeAccess E (.cell slot) (Term.C64 99) | return false
  let some nextState :=
    writes.foldlM (fun acc e => («seal» (e.reg).bits e.term >>= fun stored => some (update ⟨acc, []⟩ { exprs := [Expr.mkEq e.reg stored], predicates := [] }).exprs)) E | return false
  let .ok (_, next) := readAccess nextState (.cell slot) | return false
  let later := Reg.map 42 key 64 128
  let .error .undefinedSrc := readAccess E (.cell later) | return false
  let .ok extended := writeAccess E (.cell later) (Term.C64 99) | return false
  let some filledState :=
    extended.foldlM (fun acc e => («seal» (e.reg).bits e.term >>= fun stored => some (update ⟨acc, []⟩ { exprs := [Expr.mkEq e.reg stored], predicates := [] }).exprs)) E | return false
  let .ok (_, filled) := readAccess filledState (.cell later) | return false
  let .error .undefinedSrc := accessAt memoryEntry E 0 7 2 false maps | return false
  let .error .undefinedSrc := accessAt memoryEntry E 0 (-1) 1 false maps | return false
  let .error .undefinedSrc := accessAt memoryEntry E 0 16 1 false maps | return false
  let .error .undefinedSrc := accessAt memoryEntry pointed 0 0 8 false maps | return false
  return slot == cell && value == held && next == Term.C64 99 && filled == Term.C64 99

#guard lookupMemoryCheck

private def mapStoreFrozenKey : List Term :=
  [Term.C64 1, Term.C64 2, Term.C64 3, Term.C64 4]

private def mapStorePointer : Term :=
  star .w64 (.externalResult 0) (Term.C64 1 :: Term.C64 1077412584 :: mapStoreFrozenKey)

private def mapStoreExprs : List Expr :=
  (update ⟨Expr.nil, []⟩ { exprs := [Expr.mkEq (Reg.real64 0) (solve mapStorePointer)], predicates := [] }).exprs
    |> (fun acc => (update ⟨acc, []⟩ { exprs := [Expr.mkRel (Reg.real64 0) .leu
        (addStar .w64 mapStorePointer (Term.C64 8))], predicates := [] }).exprs)
    |> (fun acc => (update ⟨acc, []⟩ { exprs := [Expr.mkEq (Reg.real64 1) (solve (idStar .w64 (Term.V64 11)))], predicates := [] }).exprs)

private def mapStoreKey : List Term :=
  [Term.C32 1, Term.C32 2, Term.C32 3, Term.C32 4]

private def mapStoreLookup : Observation :=
  .helper .lookup ([Term.C64 1077412584, Term.V64 9] ++ mapStoreFrozenKey)

private def mapStoreLayouts : List MapLayout :=
  [{ mapId := 1077412584, keySize := 4, valueSize := 8 }]

private def mapStoreObservationsCheck : Bool := Id.run do
  let E := mapStoreExprs
  let ev := 77
  let some source := E.lookupEq (Reg.real64 1) | return false
  let .ok (effect, predicates) :=
    effectsAt memoryEntry ev E (.stx 8 0 1 0) mapStoreLayouts [mapStoreLookup]
    | return false
  let .ok (_, partialPredicates) :=
    effectsAt memoryEntry (ev + 1) E (.stx 4 0 1 4) mapStoreLayouts [mapStoreLookup]
    | return false
  return predicates ==
      [.mapWrite (Term.C64 1077412584) mapStoreKey 0 32
        (star .w32 (.extract 0 32 64) [source]),
       .mapWrite (Term.C64 1077412584) mapStoreKey 4 32
        (star .w32 (.extract 32 32 64) [source])] &&
    partialPredicates ==
      [.mapWrite (Term.C64 1077412584) mapStoreKey 4 32 source] &&
    effect.inputs == Expr.nil &&
    effect.updates.lookupEq (.map 1077412584 mapStoreKey 0 64) == some source &&
    effect.validFor E

private def symbolicMapStoreFrozenKeyCheck : Bool := Id.run do
  let keyPtr := addStar .w64 memoryEntry.tSp (Term.C64 (M 64 (-4)))
  let lo := 508 * 8
  let some original := ((«seal» (Reg.stack lo (lo + 32)).bits (Term.V32 12) >>= fun stored => some (update ⟨mapStoreExprs, []⟩ { exprs := [Expr.mkEq (.stack lo (lo + 32)) stored], predicates := [] }).exprs))
    | return false
  let some frozen := bytesAt memoryEntry original keyPtr 4 | return false
  let Pg := [.helper .lookup ([Term.C64 1077412584, keyPtr] ++ frozen)]
  let pointer := star .w64 (.externalResult 0) (Term.C64 1 :: Term.C64 1077412584 :: frozen)
  let E := (update ⟨mapStoreExprs, []⟩ { exprs := [Expr.mkEq (Reg.real64 0) (solve pointer)], predicates := [] }).exprs
    |> (fun acc => (update ⟨acc, []⟩ { exprs := [Expr.mkRel (Reg.real64 0) .leu
        (addStar .w64 pointer (Term.C64 8))], predicates := [] }).exprs)
  let .ok (effect, predicates) :=
    effectsAt memoryEntry 77 E (.stx 8 0 1 0) mapStoreLayouts Pg | return false
  let [.mapWrite mapLo keyLo 0 32 valueLo, .mapWrite mapHi keyHi 4 32 valueHi] :=
    predicates | return false
  let some stored := effect.updates.lookupEq (.map 1077412584 keyLo 0 64) | return false
  let some live := ((«seal» (Reg.stack lo (lo + 32)).bits (Term.C32 0) >>= fun stored => some (update ⟨original, []⟩ { exprs := [Expr.mkEq (.stack lo (lo + 32)) stored], predicates := [] }).exprs)) | return false
  let some liveKey := bytesAt memoryEntry live keyPtr 4 | return false
  if !effect.validFor E || !effect.inputs.isEmpty ||
      !frozen.all (fun t => t.width == .w64) ||
      !(keyLo ++ keyHi).all (fun t => t.width == .w32) ||
      valueLo.width != .w32 || valueHi.width != .w32 then return false
  let θ : ExternalInterpretation :=
    { externalResult := fun _ _ _ => some 0
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
      interpretTerm ν θ stored == some sourceValue &&
      interpretTerms ν θ liveKey == some [0, 0, 0, 0]

private def mapStoreRejectsMissingWitnessCheck : Bool :=
  let bare := (update ⟨Expr.nil, []⟩ { exprs := [Expr.mkEq (Reg.real64 0) (solve mapStorePointer)], predicates := [] }).exprs
    |> (fun acc => (update ⟨acc, []⟩ { exprs := [Expr.mkEq (Reg.real64 1) (solve (idStar .w64 (Term.V64 11)))], predicates := [] }).exprs)
  match effectsAt memoryEntry 77 bare (.stx 8 0 1 0) mapStoreLayouts with
  | .error .undefinedSrc => true
  | _ => false

private def mapStoreRejectsLayoutAndBoundsCheck : Bool :=
  let cases : List (Insn × List MapLayout) := [
    (.stx 8 0 1 0, []),
    (.stx 8 0 1 0, [⟨42, 4, 8⟩]),
    (.stx 1 0 1 (-1), mapStoreLayouts),
    (.stx 2 0 1 7, [⟨1077412584, 4, 16⟩]),
    (.stx 1 0 1 8, mapStoreLayouts)]
  cases.all fun (i, maps) =>
    match effectsAt memoryEntry 77 mapStoreExprs i maps [mapStoreLookup] with
    | .error .undefinedSrc => true
    | _ => false

private def nonMapCellStoreObservationsCheck : Bool := Id.run do
  let .ok σ := buildE0 memoryEntry | return false
  let E := (update ⟨σ.exprs, []⟩ { exprs := [Expr.mkEq (Reg.real64 0) (solve (Term.C64 99))], predicates := [] }).exprs
  let .ok (_, []) :=
    effectsAt memoryEntry 77 E (.stx 8 10 0 (-8)) mapStoreLayouts [mapStoreLookup]
    | return false
  let .ok (_, []) :=
    effectsAt memoryEntry 78 E (.stx 4 1 0 0) mapStoreLayouts [mapStoreLookup]
    | return false
  return true

#guard mapStoreObservationsCheck
#guard symbolicMapStoreFrozenKeyCheck
#guard mapStoreRejectsMissingWitnessCheck
#guard mapStoreRejectsLayoutAndBoundsCheck
#guard nonMapCellStoreObservationsCheck
#guard match lookupAddress64 (idStar .w64 lookupPointer) with
  | some (0, map, rest, _) => map == Term.C64 42 && rest == lookupKeyBytes
  | _ => false
#guard match lookupAddress64
    (subStar .w64 (addStar .w64 lookupPointer (Term.C64 8)) (Term.C64 4)) with
  | some (4, map, _, _) => map == Term.C64 42
  | _ => false
#guard match lookupAddress64 (addStar .w64 (Term.C64 8) lookupPointer) with
  | some (8, map, _, _) => map == Term.C64 42
  | _ => false
#guard (lookupAddress64 (Term.C64 42)).isNone
#guard (lookupAddress64 (addStar .w64 lookupPointer (Term.V64 3))).isNone
#guard (lookupAddress64 (star .w64 (.externalResult 0)
  [Term.C64 2, Term.C64 42, Term.V64 9])).isNone
#guard (lookupAddress64 (star .w64 (.externalResult 1)
  [Term.C64 1, Term.C64 42, Term.V64 9])).isNone
#guard Id.run do
  let .ok σ := buildE0 memoryEntry | return false
  let ptr := addStar .w64 memoryEntry.tSp (Term.C64 (M 64 (-4)))
  let some stacked := putStackWord σ.exprs 0 0x11223344 | return false
  let some bytes := bytesAt memoryEntry stacked ptr 4 | return false
  let some values := bytes.mapM fun t => eval (solve t) | return false
  return values == [0x44, 0x33, 0x22, 0x11] &&
    (bytesAt memoryEntry σ.exprs ptr 4).isNone &&
    (bytesAt memoryEntry stacked ptr 5).isNone

private def cellNat (E : List Expr) (r : Reg) : Option Nat := do
  eval (solve (← readInterval E r))

private def atomicStackSnapshotCheck : Bool := Id.run do
  let .ok σ := buildE0 memoryEntry | return false
  let some mem := putStackWord σ.exprs 1 0xffffffff | return false
  let some mem := putStackWord mem 0 1 | return false
  let E := (update ⟨mem, []⟩ { exprs := [Expr.mkEq (Reg.real64 2) (solve (Term.C64 1))], predicates := [] }).exprs
    |> (fun acc => (update ⟨acc, []⟩ { exprs := [Expr.mkEq (Reg.real64 0) (solve (Term.C64 0x1ffffffff))], predicates := [] }).exprs)
  let .ok (add, []) := effectsAt memoryEntry 1 E
    (.atomic .w64 (.add true) 10 2 (-8)) | return false
  let added := applyEffect E add
  let .ok (cmp, []) := effectsAt memoryEntry 2 E
    (.atomic .w64 .cmpxchg 10 2 (-8)) | return false
  let compared := applyEffect E cmp
  let failedCompare := (update ⟨E, []⟩ { exprs := [Expr.mkEq (Reg.real64 0) (solve (Term.C64 0))], predicates := [] }).exprs
  let .ok (miss, []) := effectsAt memoryEntry 3 failedCompare
    (.atomic .w64 .cmpxchg 10 2 (-8)) | return false
  let missed := applyEffect failedCompare miss
  let some missingHigh := putStackWord σ.exprs 1 1 | return false
  let .error .undefinedSrc := effectsAt memoryEntry 4
    ((update ⟨missingHigh, []⟩ { exprs := [Expr.mkEq (Reg.real64 2) (solve (Term.C64 1))], predicates := [] }).exprs)
    (.atomic .w64 (.add true) 10 2 (-8)) | return false
  let wide := Reg.stack (504 * 8) (504 * 8 + 64)
  return cellNat added wide == some 0x200000000 &&
    add.updates.lookupEq (Reg.real64 2) == some (Term.C64 0x1ffffffff) &&
    cellNat compared wide == some 1 &&
    cmp.updates.lookupEq (Reg.real64 0) == some (Term.C64 0x1ffffffff) &&
    cellNat missed wide == some 0x1ffffffff &&
    miss.updates.lookupEq (Reg.real64 0) == some (Term.C64 0x1ffffffff) &&
    add.validFor E && cmp.validFor E && miss.validFor failedCompare

private def atomicMapFieldCheck : Bool := Id.run do
  let some key := mapStoreFrozenKey.mapM mapWriteKeyByte | return false
  let cell := Reg.map 1077412584 key 0 64
  let some seeded := ((«seal» (cell).bits (Term.C64 0x11223344ffffffff) >>= fun stored => some (update ⟨mapStoreExprs, []⟩ { exprs := [Expr.mkEq cell stored], predicates := [] }).exprs))
    | return false
  let E := (update ⟨seeded, []⟩ { exprs := [Expr.mkEq (Reg.real64 2) (solve (Term.C64 1))], predicates := [] }).exprs
  let .ok (effect, []) := effectsAt memoryEntry 9 E
    (.atomic .w32 (.add true) 0 2 0) mapStoreLayouts [mapStoreLookup] | return false
  let .error .undefinedSrc := effectsAt memoryEntry 9 E
    (.atomic .w32 (.add false) 0 2 1) mapStoreLayouts [mapStoreLookup] | return false
  let storedState := applyEffect E effect
  let some old := readInterval effect.updates (Reg.real64 2) | return false
  return cellNat storedState cell == some 0x1122334400000000 &&
    eval (solve old) == some 0xffffffff &&
    effect.validFor E

private def immediateAndSignedMemoryCheck : Bool := Id.run do
  let .ok σ := buildE0 memoryEntry | return false
  let .ok (stored, []) := effectsAt memoryEntry 0 σ.exprs
    (.st 8 10 0xffffff80 (-8)) | return false
  let mem := applyEffect σ.exprs stored
  let .ok (signed, []) := effectsAt memoryEntry 1 mem (.memsx 1 2 10 (-8)) | return false
  let .ok (unsigned, []) := effectsAt memoryEntry 2 mem (.loadAcq 1 2 10 (-8)) | return false
  let E := (update ⟨mem, []⟩ { exprs := [Expr.mkEq (Reg.real64 2) (solve (Term.C64 0x55))], predicates := [] }).exprs
  let .ok (released, []) := effectsAt memoryEntry 3 E (.storeRel 1 10 2 (-7)) | return false
  let releasedMem := applyEffect E released
  return signed.updates.lookupEq (Reg.real64 2) == some (Term.C64 0xffffffffffffff80) &&
    unsigned.updates.lookupEq (Reg.real64 2) == some (Term.C64 0x80) &&
    cellNat releasedMem (.stack (504 * 8) (504 * 8 + 32)) == some 0xffff5580

#guard atomicStackSnapshotCheck
#guard atomicMapFieldCheck
#guard immediateAndSignedMemoryCheck

#guard relativeOffset memoryEntry.tSp (subStar .w64 memoryEntry.tSp (Term.C64 8)) ==
  some (-8)

#guard Id.run do
  let p : EntryParams := ⟨Term.C64 0x1000, Term.C64 0x2000, Term.C32 0x2000, 4⟩
  let .ok initial := buildE0 p | return false
  let some stacked := putStackWord initial.exprs 0 0x11223344 | return false
  let some [open0] := bufferAt p initial.exprs (Term.C64 0x2000) 1 | return false
  let byte := star .w32 (.low 8 32) [Term.C32 0x55]
  let some mem := ((«seal» (Reg.packet 0 8).bits byte >>= fun stored => some (update ⟨stacked, []⟩ { exprs := [Expr.mkEq (.packet 0 8) stored], predicates := [] }).exprs)) | return false
  let some before := bufferAt p stacked (Term.C64 0x1fff) 1 | return false
  let some packetByte := bufferAt p mem (Term.C64 0x2000) 1 | return false
  let some beforeN := before.mapM fun t => eval (solve t) | return false
  let some packetN := packetByte.mapM fun t => eval (solve t) | return false
  return beforeN == [0x11] && packetN == [0x55] &&
    (bufferAt p mem (Term.C64 0x1fff) 2).isNone &&
    (eval (solve open0)).isNone

end Cross.EBPF
