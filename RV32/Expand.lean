import Core.Anchor
import Core.Update
import RV32.Initial
import RV32.Expr
import RV32.Helper
import RV32.Encode
import RV32.Esp32c3Program
import Node.Budget
import Core.Render
import Core.Parse

namespace RV32
open Core Node

/-! Symbolic indirect targets reject. Map writes need a prior lookup with frozen key bytes
(an installed map layout + complete current buffer contents) recorded on the helper Predicate. -/

/-- Byte length, used to bind sequence indices to a contiguous instruction layout. -/
def insnLength : Insn → Nat
  | .C_ILLEGAL _ | .C_NOP _ | .C_ADDI4SPN _ | .C_LW _ | .C_SW _
  | .C_ADDI _ | .C_JAL _ | .C_LI _ | .C_ADDI16SP _ | .C_LUI _
  | .C_SRLI _ | .C_SRAI _ | .C_ANDI _ | .C_SUB _ | .C_XOR _
  | .C_OR _ | .C_AND _ | .C_J _ | .C_BEQZ _ | .C_BNEZ _
  | .C_SLLI _ | .C_LWSP _ | .C_SWSP _ | .C_JR _ | .C_JALR _
  | .C_MV _ | .C_EBREAK _ | .C_ADD _ => 2
  | _ => 4

def programOffsets (I : Array Insn) : Array Nat := Id.run do
  let mut offsets := #[]
  let mut offset := 0
  for i in I do
    offsets := offsets.push offset
    offset := offset + insnLength i
  pure offsets

private def findPosition (offsets : Array Nat) (target : Nat) : Option Nat := Id.run do
  for k in [:offsets.size] do
    if offsets[k]? == some target then return some k
  pure none

private def directTarget (offsets : Array Nat) (j : Nat) (delta : Int) : Option Location := do
  let here ← offsets[j]?
  let target := Int.ofNat here + delta
  if target < 0 then none
  else (findPosition offsets target.toNat).map Location.pos

private def nextPosition (I : Array Insn) (j : Nat) : Option Location :=
  if j + 1 < I.size then some (.pos (j + 1)) else none

private def emit (dir : Direction) (loc : Option Location) (Ei : List Expr)
    (preds : List Predicate := []) : StepResult :=
  match loc with
  | some k => .candidates [⟨dir, k, Ei, preds⟩]
  | none => .reject .unboundTarget

/-- Capture a0's complete pre-return term only after the wrapper Exit is recognized. -/
private def emitIndirect (loc : Option Location) (Eg Ei : List Expr) : StepResult :=
  match loc with
  | some .exit =>
    match Eg.lookupEq (Reg.real32 10) with
    | some t => .candidates [⟨.ok, .exit, Ei, [.ret t]⟩]
    | none => .reject .undefinedSrc
  | _ => emit .ok loc Ei

private def branchRel : bop → Rel
  | .BEQ => .eq
  | .BNE => .ne
  | .BLT => .lts
  | .BGE => .ges
  | .BLTU => .ltu
  | .BGEU => .geu

private def emitComparison (dir : BranchDirection) (loc : Option Location) (Ei : List Expr)
    (e : Expr) (position : Nat) (lhs : Term) : StepResult :=
  let direction := match dir with | .taken => Direction.taken | .notTaken => .notTaken
  match loc with
  | some k => .candidates [⟨direction, k, (let row := solveExpr e; if Ei.contains row then Ei else Ei ++ [row]),
      [.branch position dir ⟨lhs, e.rel, e.term⟩]⟩]
  | none => .reject .unboundTarget

private def indirectTarget (offsets : Array Nat) (base returnAddr : Option Nat)
    (target : Nat) (isReturn : Bool) : Option Location :=
  -- Only an explicit return instruction reaching the bound wrapper label may Exit.
  if isReturn && returnAddr == some target then some .exit
  else do
    let base ← base
    let offset := MNat 32 (target + (1 <<< 32) - base)
    (findPosition offsets offset).map Location.pos

private def needsPC : Insn → Bool
  | .UTYPE (_, _, .AUIPC) | .C_JAL _ | .C_JALR _ => true
  | .JAL (_, rd) | .JALR (_, _, rd) => rd.toNat != 0
  | _ => false

private def valueRejection : Insn → RejectReason
  | .ILLEGAL _ | .C_ILLEGAL _ => .localReject
  | .LOAD _ | .STORE (_, _, _, 1) | .STORE (_, _, _, 2) | .STORE (_, _, _, 4)
  | .C_LW _ | .C_SW _ | .C_LWSP _ | .C_SWSP _ => .undefinedSrc
  | .STORE _
  | .ECALL _ | .EBREAK _ | .MRET _ | .SRET _ | .WFI _ | .SFENCE_VMA _
  | .C_EBREAK _ => .unsupported
  | _ => .undefinedSrc

/-- Recover map term + frozen key from Pg for the lookup that owns this Map address.
Reject when the pointer's Map provenance disagrees with the frozen-key observation Map
(aligned with eBPF `mapWriteObservation`). -/
def mapWriteObservation (Eg : List Expr) (Pg : List Predicate)
    (rs1 rs2 : regidx) (offset width : Nat) :
    Option (Term × List Term × Nat × Term) := do
  let (lookupEvent, elementOff, mapTerm) ← mapElementAccess Eg Pg rs1 offset width
  let source ← readReg Eg rs2
  if source.width != .w32 then none
  else
    let (map, frozen) ← lookupKeyAt Pg lookupEvent
    if map != mapTerm || frozen.isEmpty then none
    else
      let layout ← Anchor.layout? Eg map
      if frozen.length != layout.keySize || elementOff + width > layout.valueSize then none
      else some (map, frozen, elementOff, solve source)

theorem mapWriteObservation_frozen (Eg : List Expr) (Pg : List Predicate)
    (rs1 rs2 : regidx) (offset width : Nat)
    (map : Term) (key : List Term) (elementOff : Nat) (value : Term)
    (h : mapWriteObservation Eg Pg rs1 rs2 offset width =
      some (map, key, elementOff, value)) :
    ∃ event source displacement,
      readReg Eg rs1 = some source ∧
      lookupAddress (solve source) = some (event, displacement, map) ∧
      lookupKeyAt Pg event = some (map, key) ∧ LookupTie Pg event map key := by
  unfold mapWriteObservation at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  rcases h with ⟨⟨event, off, pointerMap⟩, ha, source, hs, h⟩
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
      rcases h with ⟨layout, _, h⟩
      split at h
      · cases h
      · cases h
        rcases mapElementAccess_preimage Eg Pg rs1 offset width event elementOff map
          (hm ▸ ha) with ⟨address, displacement, hr, hl⟩
        exact ⟨event, address, displacement, hr, hl, hk,
          lookupKeyAt_tie Pg event map key hk⟩

/-- A constant packet store is one predicate covering the written bytes.
A symbolic packet address creates no packet register and no packetWrite. -/
private def packetSpan (Ei : List Expr) : Option Nat :=
  Ei.foldl (fun acc e =>
    match e.reg, acc with
    | .packet lo _, none => some lo
    | .packet lo _, some best => some (min lo best)
    | _, acc => acc) none |>.map (· / 8)

private def touchesMap (Ei : List Expr) : Bool :=
  Ei.any fun e => match e.reg with | .map .. => true | _ => false

/-- Each successful store delta touches one resource category, selected by the value step.
MapWrite needs frozen lookup keys. PacketWrite needs a concrete byte offset and an event. -/
private def emitStore (I : Array Insn) (j : Nat) (Eg Ei : List Expr)
    (Pg : List Predicate) (rs1 rs2 : regidx) (offset width : Nat)
    (event : Option NodeId) : StepResult :=
  match packetSpan Ei, touchesMap Ei with
  | some byteOff, false =>
    match event, readReg Eg rs2, nextPosition I j with
    | some event, some source, some loc =>
      .candidates [⟨.ok, loc, Ei, [.packetWrite event byteOff (8 * width) source]⟩]
    | _, _, none => .reject .unboundTarget
    | _, _, _ => .reject .undefinedSrc
  | none, true =>
    match event, mapWriteObservation Eg Pg rs1 rs2 offset width, nextPosition I j with
    | some event, some (map, key, o, source), some loc =>
      .candidates [⟨.ok, loc, Ei, [.mapWrite event map key o (8 * width) source]⟩]
    | _, _, none => .reject .unboundTarget
    | _, _, _ => .reject .undefinedSrc
  | _, _ => emit .ok (nextPosition I j) Ei

/-- Static layout/return bindings are captured by the Step closure, never stored in SemState.
PC is derived solely for the value call. Without a dynamic event, resource writes reject;
ordinary value, Branch, and Return callers need no event identity. -/
private partial def containsInputByte : Term → Bool
  | .app _ (.inputByte _) _ => true
  | .app _ _ args => args.any containsInputByte
  | _ => false

private def isReturnInsn : Insn → Bool
  | .JALR (imm, rs1, rd) => rd.toNat == 0 && rs1.toNat == 1 && imm.toNat == 0
  | .C_JR rs1 => rs1.toNat == 1
  | _ => false

/-- `li rd, 0` or `addi rd, x0, 0`. The abort stub is this followed by `ret`. -/
private def isZeroing : Insn → Bool
  | .ITYPE (imm, rs1, _, .ADDI) => imm.toNat == 0 && rs1.toNat == 0
  | .C_LI (imm, _) => imm.toNat == 0
  | _ => false

/-- Stack restore, `li a0, n`, or `addi sp, sp, n` in front of a shared `ret`. -/
private def epilogueInsn : Insn → Bool
  | .C_LWSP _ | .C_ADDI16SP _ | .C_LW _ => true
  | .C_LI (_, rd) => rd.toNat == 10
  | .C_ADDI (_, rd) => rd.toNat == 2 || rd.toNat == 10
  | .ITYPE (_, rs1, rd, .ADDI) =>
    (rd.toNat == 10 && rs1.toNat == 0) || (rd.toNat == 2 && rs1.toNat == 2)
  | _ => false

/-- Forward `c.j` / `jal x0` into that epilogue. A backward jump is a loop. -/
private def forwardJump (I : Array Insn) (j : Nat) (i : Insn) : Option Nat :=
  let offsets := programOffsets I
  let delta := match i with
    | .C_J imm | .C_JAL imm => some (2 * s 11 imm.toNat)
    | .JAL (imm, rd) => if rd.toNat == 0 then some (s 21 imm.toNat) else none
    | _ => none
  match delta with
  | none => none
  | some d =>
    match directTarget offsets j d with
    | some (.pos k) => if k > j then some k else none
    | _ => none

private def straightAbort (I : Array Insn) (j : Nat) : Bool :=
  let rec go (j n : Nat) : Bool :=
    if n ≥ 8 then false
    else match I[j]? with
      | some i =>
        if isReturnInsn i then true
        else if isZeroing i || epilogueInsn i then go (j + 1) (n + 1)
        else match forwardJump I j i with
          | some k => go k (n + 1)
          | none => false
      | none => false
  go j 0

private def abortLoc (I : Array Insn) : Option Location → Bool
  | some .exit => true
  | some (.pos j) => straightAbort I j
  | none => false

private def undecidedBranch (I : Array Insn) (j : Nat) (Ei : List Expr) (t1 : Term)
    (rel : Rel) (t2 : Term) (takenE fallE : Expr) (takenLoc fallLoc : Option Location) :
    StepResult :=
  let fallOnly := containsInputByte t1 || containsInputByte t2
  let keepTaken := fallOnly && abortLoc I fallLoc && !abortLoc I takenLoc
  -- A pruned abort arm is still a successor: it joins the shared exit.
  -- Omitting it leaves a branch with only `taken` or only `not_taken`.
  let abortExit (dir : Direction) (bdir : BranchDirection) (e : Expr) : Candidate :=
    ⟨dir, .exit, (let row := solveExpr e; if Ei.contains row then Ei else Ei ++ [row]), [.branch (j + 1) bdir ⟨t1, e.rel, e.term⟩]⟩
  match takenLoc, fallLoc with
  | some taken, some fall =>
    if keepTaken then
      .candidates [
        ⟨.taken, taken, (let row := solveExpr takenE; if Ei.contains row then Ei else Ei ++ [row]),
          [.branch (j + 1) .taken ⟨t1, rel, t2⟩]⟩,
        abortExit .notTaken .notTaken fallE]
    else if fallOnly && abortLoc I takenLoc then
      .candidates [
        abortExit .taken .taken takenE,
        ⟨.notTaken, fall, (let row := solveExpr fallE; if Ei.contains row then Ei else Ei ++ [row]),
          [.branch (j + 1) .notTaken ⟨t1, rel.compl, t2⟩]⟩]
    else if fallOnly then
      .candidates [⟨.notTaken, fall, (let row := solveExpr fallE; if Ei.contains row then Ei else Ei ++ [row]),
        [.branch (j + 1) .notTaken ⟨t1, rel.compl, t2⟩]⟩]
    else
      .candidates [
        ⟨.taken, taken, (let row := solveExpr takenE; if Ei.contains row then Ei else Ei ++ [row]),
          [.branch (j + 1) .taken ⟨t1, rel, t2⟩]⟩,
        ⟨.notTaken, fall, (let row := solveExpr fallE; if Ei.contains row then Ei else Ei ++ [row]),
          [.branch (j + 1) .notTaken ⟨t1, rel.compl, t2⟩]⟩]
  | _, _ => .reject .unboundTarget

def rv32StepBound (I : Array Insn) (base returnAddr : Option Nat)
    (j : Nat) (σ : SemState) (boundCtx : Option Term := none)
    (event : Option NodeId := none) : StepResult :=
  match I[j]? with
  | none => .reject .unboundTarget
  | some i =>
    if !guardEg σ.exprs then .reject .localReject
    else
      let offsets := programOffsets I
      let Eg := match base, offsets[j]? with
        | some b, some offset => (update ⟨σ.exprs, []⟩ { exprs := [Expr.mkEq (Reg.real32 32) (solve (Term.C32 (b + offset)))], predicates := [] }).exprs
        | _, _ => σ.exprs
      if needsPC i && (readPC Eg).isNone then .reject .unboundTarget
      else
        match RV32.stepEffects Eg i boundCtx σ.predicates with
        | none => .reject (valueRejection i)
        | some effect =>
          let Ei := effect.delta
          match i with
          | .JAL (imm, _) => emit .ok (directTarget offsets j (s 21 imm.toNat)) Ei
          | .BTYPE (imm, rs2, rs1, op) =>
            match readReg Eg rs1, readReg Eg rs2 with
            | some ta, some tb =>
              let t1 := solve ta
              let t2 := solve tb
              let rel := branchRel op
              let takenLoc := directTarget offsets j (s 13 imm.toNat)
              let fallLoc := nextPosition I j
              let takenE := Expr.mkRel (Reg.real32 rs1.toNat) rel t2
              let fallE := Expr.mkRel (Reg.real32 rs1.toNat) rel.compl t2
              match takenE.decideWith t1 with
              | some true => emitComparison .taken takenLoc Ei takenE (j + 1) t1
              | some false => emitComparison .notTaken fallLoc Ei fallE (j + 1) t1
              | none =>
                undecidedBranch I j Ei t1 rel t2 takenE fallE takenLoc fallLoc
            | _, _ => .reject .undefinedSrc
          | .JALR (imm, rs1, rd) =>
            match readReg Eg rs1 with
            | none => .reject .undefinedSrc
            | some t =>
              match eval (solve t) with
              | none => .reject .unboundTarget
              | some a =>
                let target := MNat 32 (a + immI32 imm) &&& ((1 <<< 32) - 2)
                let isReturn := rd.toNat == 0 && rs1.toNat == 1 && imm.toNat == 0
                emitIndirect (indirectTarget offsets base returnAddr target isReturn) Eg Ei
          | .C_JR rs1 | .C_JALR rs1 =>
            match readReg Eg rs1 with
            | none => .reject .undefinedSrc
            | some t =>
              match eval (solve t) with
              | none => .reject .unboundTarget
              | some a =>
                let isReturn := match i with | .C_JR _ => rs1.toNat == 1 | _ => false
                emitIndirect (indirectTarget offsets base returnAddr
                  (MNat 32 a &&& ((1 <<< 32) - 2)) isReturn) Eg Ei
          | .C_J imm | .C_JAL imm =>
            emit .ok (directTarget offsets j (2 * s 11 imm.toNat)) Ei
          | .C_BEQZ (imm, rs1) | .C_BNEZ (imm, rs1) =>
            match readReg Eg (creg2reg_idx rs1) with
            | none => .reject .undefinedSrc
            | some ta =>
              let op := match i with | .C_BEQZ _ => bop.BEQ | _ => bop.BNE
              let t1 := solve ta
              let t2 := Term.C32 0
              let rel := branchRel op
              let reg := Reg.real32 (creg2reg_idx rs1).toNat
              let takenE := Expr.mkRel reg rel t2
              let fallE := Expr.mkRel reg rel.compl t2
              let takenLoc := directTarget offsets j (2 * s 8 imm.toNat)
              let fallLoc := nextPosition I j
              match takenE.decideWith t1 with
              | some true => emitComparison .taken takenLoc Ei takenE (j + 1) t1
              | some false => emitComparison .notTaken fallLoc Ei fallE (j + 1) t1
              | none =>
                undecidedBranch I j Ei t1 rel t2 takenE fallE takenLoc fallLoc
          | .STORE (imm, rs2, rs1, width) =>
            emitStore I j Eg Ei σ.predicates rs1 rs2 (immI32 imm) width event
          | .C_SW (imm, rs1, rs2) =>
            emitStore I j Eg Ei σ.predicates (creg2reg_idx rs1) (creg2reg_idx rs2)
              (imm.toNat <<< 2) 4 event
          | .C_SWSP (imm, rs2) =>
            emitStore I j Eg Ei σ.predicates sp rs2 (imm.toNat <<< 2) 4 event
          | _ => emit .ok (nextPosition I j) Ei

/-- Unbound adapter: sequential effects and relative RV32 direct targets work;
PC-dependent effects and indirect targets require rv32StepBound's static bindings. -/
def rv32Step (I : Array Insn) (j : Nat) (σ : SemState) : StepResult :=
  rv32StepBound I none none j σ none none

/-- The root is the actual pre-instruction wrapper entry state. -/
def rv32Init (I : Array Insn) (p : EntryParams) (j0 budget : Nat) :
    Except RejectReason WorkState := do
  let σ0 ← entrySemState p
  expandInit I.size j0 σ0 budget

private def const32? : Term → Option Nat
  | .const .w32 c => some c
  | _ => none

/-- For a contiguous input array, bind addr(j0) to entry with its low bit cleared.
Symbolic entry addresses cannot supply PC or absolute indirect-target bindings. -/
private def entryBase (I : Array Insn) (p : EntryParams) (j0 : Nat) : Option Nat := do
  let entry ← const32? p.tEntry
  let offset ← (programOffsets I)[j0]?
  pure (MNat 32 ((entry &&& ((1 <<< 32) - 2)) + (1 <<< 32) - offset))

/-- JSON after at most steps expandOne calls; all node Exprs are global pre-execution snapshots.
The caller binds the contiguous instruction layout and wrapper label via EntryParams. -/
def rv32Snapshot (I : Array Insn) (p : EntryParams) (j0 steps budget : Nat) : String :=
  match rv32Init I p j0 budget with
  | .error reason => snapshotJson #[] #[] [] 0 "fail" (some reason)
  | .ok ws => snapshotAfter I.size
      (fun event j σ => rv32StepBound I (entryBase I p j0) (const32? p.tReturn)
        j σ none (some event)) ws steps

/-- One instruction per word, with compressed encodings in the low halfword. -/
def decodeInsnWord (w : UInt32) : Insn :=
  let n := w.toNat
  if n &&& 3 != 3 then encodeCompressed (BitVec.ofNat 16 (n &&& 0xffff))
  else encode (BitVec.ofNat 32 n)

/-- Decode mixed 16/32-bit instruction arrays without changing their sequence indices. -/
def decodeProgram (insns : Array UInt32) : Array Insn :=
  insns.map decodeInsnWord

def esp32c3Program : Array Insn := decodeProgram esp32c3Words

/-- Synthetic, explicitly bound wrapper inputs for the built-in smoke program. -/
def smokeEntryParams : EntryParams := {
  tEntry := Term.C32 0x1000
  tReturn := Term.C32 0x2000
  tFrame := Term.C32 0x3000
  tSp := Term.V32 EntryVar.sp
  tCtx := Term.V32 EntryVar.ctx
  tData := Term.V32 EntryVar.data
  tLen := Term.V32 EntryVar.len
  ιWifi := 1 -- Synthetic IFINDEX_WIFI for this smoke fixture.
  -- The synthetic fixture first spills s0 at index 7: c.swsp s0,8(sp).
  -- Keep R_entry = {x8} minimal: x8 retains the concrete entry-position term,
  -- so this smoke run reaches index 25's LHU symbolic-offset block.
  -- Product create and boundProgram use the whole savedRegs set instead.
  rEntries := [Reg.real32 8]
}

/-- addi a0,zero,7; addi a0,a0,1; jalr zero,ra,0. -/
def smokeProgram : Array Insn := decodeProgram #[0x00700513, 0x00150513, 0x00008067]

private def initialEqCheck (E : List Expr) (r : Reg) (expected : Term) : Bool :=
  match E.lookupEq r with
  | some actual => reprStr actual == reprStr (solve expected)
  | none => false

private def isRealReg (r : Reg) : Bool :=
  match r with
  | .real .. => true
  | _ => false

private def isContextReg (r : Reg) : Bool :=
  match r with
  | .context .. => true
  | _ => false

private def ctxEq (E : List Expr) (j : ContextField) (expected : Term) : Bool :=
  initialEqCheck E (.context j 0 32) expected

private def smokeE0RealCheck : Bool :=
  let p := smokeEntryParams
  match buildE0 p with
  | .error _ => false
  | .ok σ =>
    σ.exprs.keysUnique && σ.predicates.isEmpty && σ.exprs.length == 14 &&
      (σ.exprs.filter (fun e => isRealReg e.reg)).length == 8 &&
      (buildEBase p).length == 7 &&
      initialEqCheck σ.exprs (Reg.real32 0) (Term.C32 0) &&
      initialEqCheck σ.exprs (Reg.real32 2) p.tSp &&
      initialEqCheck σ.exprs (Reg.real32 5) p.tSp &&
      initialEqCheck σ.exprs (Reg.real32 1) p.tReturn &&
      initialEqCheck σ.exprs (Reg.real32 6) p.tReturn &&
      initialEqCheck σ.exprs (Reg.real32 7) p.tFrame &&
      initialEqCheck σ.exprs (Reg.real32 10) p.tCtx &&
      p.rEntries.all (fun r => initialEqCheck σ.exprs r p.tEntry) &&
      (σ.exprs.lookupEq (Reg.real32 9)).isNone &&
      (σ.exprs.lookupEq (Reg.real32 32)).isNone

private def smokeE0CtxCheck : Bool :=
  let p := smokeEntryParams
  match buildE0 p with
  | .error _ => false
  | .ok σ =>
    contextTerms p == [p.tData, addStar .w32 p.tData p.tLen, Term.C32 0,
        Term.C32 p.ιWifi, Term.C32 0, Term.C32 0] &&
      (σ.exprs.filter (fun e => isContextReg e.reg)).length == 6 &&
      ctxEq σ.exprs .data p.tData &&
      ctxEq σ.exprs .dataEnd (addStar .w32 p.tData p.tLen) &&
      ctxEq σ.exprs .dataMeta (Term.C32 0) &&
      ctxEq σ.exprs .ingressIfindex (Term.C32 p.ιWifi) &&
      ctxEq σ.exprs .rxQueueIndex (Term.C32 0) &&
      ctxEq σ.exprs .egressIfindex (Term.C32 0)

private def smokeEntryFreshKeyCheck : Bool :=
  let p := { smokeEntryParams with rEntries := [Reg.real32 9] }
  match buildE0 p with
  | .error _ => false
  | .ok σ =>
    σ.exprs.keysUnique && σ.exprs.length == 14 &&
      initialEqCheck σ.exprs (Reg.real32 9) p.tEntry &&
      (buildEBase p).length == 7 &&
      (σ.exprs.lookupEq (Reg.real32 8)).isNone

private def smokeMultipleEntriesCheck : Bool :=
  let p := { smokeEntryParams with rEntries := [Reg.real32 8, Reg.real32 9] }
  match buildE0 p with
  | .error _ => false
  | .ok σ =>
    σ.exprs.keysUnique && σ.exprs.length == 15 &&
      (σ.exprs.filter (fun e => isRealReg e.reg)).length == 9 &&
      p.rEntries.all (fun r => initialEqCheck σ.exprs r p.tEntry) &&
      (buildEBase p).length == 7

private def smokeRaEntryCheck : Bool :=
  let p := { smokeEntryParams with rEntries := [Reg.real32 1] }
  match buildE0 p with
  | .error _ => false
  | .ok σ => σ.exprs.length == 13 &&
      p.rEntries.all (fun r => initialEqCheck σ.exprs r p.tReturn) &&
      initialEqCheck σ.exprs (Reg.real32 6) p.tReturn

private def smokeEmptyEntriesCheck : Bool :=
  let p := { smokeEntryParams with rEntries := [] }
  match buildE0 p with
  | .error _ => false
  | .ok σ => σ.exprs.keysUnique && σ.exprs.length == 13 &&
      (σ.exprs.filter (fun e => isRealReg e.reg)).length == 7 &&
      initialEqCheck σ.exprs (Reg.real32 1) p.tReturn

private def smokeMixedRaEntriesCheck : Bool :=
  let p := { smokeEntryParams with rEntries := [Reg.real32 1, Reg.real32 8, Reg.real32 9] }
  match buildE0 p with
  | .error _ => false
  | .ok σ => σ.exprs.keysUnique && σ.exprs.length == 15 &&
      p.rEntries.all (fun r => initialEqCheck σ.exprs r
        (if r == Reg.real32 1 then p.tReturn else p.tEntry))

private def smokeConcreteDataEndCheck : Bool :=
  let p := { smokeEntryParams with tData := Term.C32 4096, tLen := Term.C32 64 }
  match buildE0 p with
  | .error _ => false
  | .ok σ => ctxEq σ.exprs .data (Term.C32 4096) &&
      ctxEq σ.exprs .dataEnd (Term.C32 4160) &&
      (σ.exprs.filter (fun e => isContextReg e.reg)).length == 6

private def smokeInitialRootCheck : Bool :=
  match rv32Init smokeProgram smokeEntryParams 0 3 with
  | .error _ => false
  | .ok ws =>
    match ws.nodes[0]? with
    | none => false
    | some root => root.loc == .pos 0 && ws.nodes.size == 1 && ws.edges.isEmpty &&
        ws.work == [0] && ws.fuel == 3 && root.state.exprs.length == 14 &&
        ctxEq root.state.exprs .data smokeEntryParams.tData

private def smokeInvalidEntryCheck : Bool :=
  [{ smokeEntryParams with rEntries := [Reg.real32 32] },
   { smokeEntryParams with rEntries := [Reg.real32 8, Reg.real32 32] },
   { smokeEntryParams with rEntries := [Reg.real32 8, Reg.real32 8] },
   { smokeEntryParams with rEntries := [Reg.real32 1, Reg.real32 1] },
   { smokeEntryParams with tData := Term.C64 4096 },
   { smokeEntryParams with tSp := Term.C32 1 },
   { smokeEntryParams with tEntry := Term.C32 0 }].all fun p =>
    match buildE0 p with
    | .error .invalidEntry => true
    | _ => false

private def smokeCompleteExitCheck : Bool :=
  let p := smokeEntryParams
  let stepFn := rv32StepBound smokeProgram (entryBase smokeProgram p 0) (const32? p.tReturn)
  match rv32Init smokeProgram p 0 3 with
  | .error _ => false
  | .ok ws =>
    -- Three instruction expansions followed by the empty-work completion check.
    match expandN smokeProgram.size stepFn ws 4 with
    | .inl (.complete g) =>
      g.nodes.size == 4 && g.edges.size == 3 &&
        g.nodes.any (fun n => Node.isExit n.loc &&
          initialEqCheck n.state.exprs (Reg.real32 10) (Term.C32 8)) &&
        g.nodes.all (fun n => if Node.isExit n.loc then
          n.state.predicates == [.ret (Term.C32 8)] else n.state.predicates.isEmpty)
    | _ => false

private def smokeRejectsWithoutExitCheck : Bool :=
  let cases : List (Array Insn × RejectReason) := [
    (decodeProgram #[0xffffffff, 0x00150513, 0x00008067], .localReject),
    (decodeProgram #[0x00700513, 0x00150513, 0x00150513], .unboundTarget),
    -- x28 has no entry equality; even a following return cannot turn its read into Exit.
    (decodeProgram #[0x000e0513, 0x00150513, 0x00008067], .undefinedSrc)]
  cases.all fun (I, expected) =>
    let p := smokeEntryParams
    let stepFn := rv32StepBound I (entryBase I p 0) (const32? p.tReturn)
    match rv32Init I p 0 3 with
    | .error _ => false
    | .ok ws =>
      match expandN I.size stepFn ws 4 with
      | .inl (.fail reason g) => reason == expected &&
          !(g.nodes.any fun n => Node.isExit n.loc)
      | _ => false

private def smokeEmptyPredicateMergeCheck : Bool :=
  match buildE0 smokeEntryParams with
  | .error _ => false
  | .ok σ =>
    let predicates := (update { exprs := [], predicates := σ.predicates } { exprs := [], predicates := [] }).predicates
    let unchanged := update σ { exprs := Expr.nil, predicates := [] }
    predicates.isEmpty && unchanged.predicates.isEmpty &&
      reprStr unchanged.exprs == reprStr σ.exprs

#guard smokeE0RealCheck
#guard smokeE0CtxCheck
#guard smokeEntryFreshKeyCheck
#guard smokeMultipleEntriesCheck
#guard smokeRaEntryCheck
#guard smokeEmptyEntriesCheck
#guard smokeMixedRaEntriesCheck
#guard smokeConcreteDataEndCheck
#guard smokeInitialRootCheck
#guard smokeInvalidEntryCheck
#guard smokeCompleteExitCheck
#guard smokeRejectsWithoutExitCheck
#guard smokeEmptyPredicateMergeCheck

private def esp32c3DecodeCheck : Bool :=
  esp32c3Program.size == 48 && insnTag (decodeInsnWord 0x4110) == 46 &&
    match esp32c3Program[0]? with
    | some (Insn.C_LW (uimm, rs1, rd)) => uimm.toNat == 0 &&
        (creg2reg_idx rs1).toNat == 10 && (creg2reg_idx rd).toNat == 12
    | _ => false

private def esp32c3FirstLoadCheck : Bool :=
  match buildE0 smokeEntryParams, esp32c3Program[0]? with
  | .ok σ, some i =>
    match RV32.step σ.exprs i  with
    | some Ei => Ei.keysUnique && Ei.length == 1 &&
        initialEqCheck Ei (Reg.real32 12) smokeEntryParams.tData
    | none => false
  | _, _ => false

private def contextWordLoadsCheck : Bool :=
  let p := smokeEntryParams
  let values := [p.tData, addStar .w32 p.tData p.tLen, Term.C32 0,
    Term.C32 p.ιWifi, Term.C32 0, Term.C32 0]
  match buildE0 p with
  | .error _ => false
  | .ok σ => ((List.range 6).zip values).all fun jt =>
      let i := Insn.LOAD (BitVec.ofNat 12 (4 * jt.1), .Regidx 10#5, .Regidx 12#5, false, 4)
      match RV32.step σ.exprs i  with
      | some Ei => Ei.length == 1 && initialEqCheck Ei (Reg.real32 12) jt.2
      | none => false

private def contextLoadRejectionCheck : Bool :=
  match buildE0 smokeEntryParams with
  | .error _ => false
  | .ok σ =>
    let incomplete := σ.exprs.filter fun e => e.reg != .context .egressIfindex 0 32
    let bad := [
      Insn.LOAD (2#12, .Regidx 10#5, .Regidx 12#5, false, 4),
      .LOAD (24#12, .Regidx 10#5, .Regidx 12#5, false, 4),
      .LOAD (4092#12, .Regidx 10#5, .Regidx 12#5, false, 4),
      .LOAD (0#12, .Regidx 28#5, .Regidx 12#5, false, 4),
      .LOAD (0#12, sp, .Regidx 12#5, false, 4),
      .LOAD (0#12, .Regidx 28#5, .Regidx 12#5, false, 1)]
    bad.all (fun i => (RV32.step σ.exprs i ).isNone) &&
      (exprLOAD incomplete (.Regidx 10#5) zreg 0).isNone &&
      match exprLOAD σ.exprs (.Regidx 10#5) zreg 0 with
      | some Ei => Ei.isEmpty
      | none => false

private def contextShiftedBaseCheck : Bool :=
  let p := smokeEntryParams
  match buildE0 p with
  | .error _ => false
  | .ok σ =>
    -- A real-register alias of the context root reads the same field.
    let Eg := (update ⟨σ.exprs, []⟩ { exprs := [Expr.mkEq (Reg.real32 15) (solve p.tCtx)], predicates := [] }).exprs
    match exprLOAD Eg (.Regidx 15#5) (.Regidx 12#5) 4 with
    | some Ei => Ei.length == 1 &&
        initialEqCheck Ei (Reg.real32 12) (addStar .w32 p.tData p.tLen)
    | none => false

private def compressedLwOffsetCheck : Bool :=
  [(0x4150, 4), (0x5110, 32), (0x4130, 64), (0x5d70, 124)].all fun row =>
    match decodeInsnWord row.1 with
    | .C_LW (uimm, rs1, rd) => (uimm.toNat <<< 2) == row.2 &&
        (creg2reg_idx rs1).toNat == 10 && (creg2reg_idx rd).toNat == 12
    | _ => false

/-- bltu x1,x2,+8: fixed symbolic Terms produce Taken before NotTaken. -/
private def symbolicBltuDualSuccessorCheck : Bool :=
  let I := decodeProgram #[0x0020e463, 0x00100513, 0x00008067]
  let lhs := Term.V32 101
  let rhs := Term.V32 102
  let E := (update ⟨Expr.nil, []⟩ { exprs := [Expr.mkEq (Reg.real32 1) (solve lhs)], predicates := [] }).exprs
    |> (fun acc => (update ⟨acc, []⟩ { exprs := [Expr.mkEq (Reg.real32 2) (solve rhs)], predicates := [] }).exprs)
  match rv32StepBound I none none 0 ⟨E, []⟩ with
  | .candidates [taken, fall] =>
    taken.dir == .taken && taken.loc == .pos 2 &&
      fall.dir == .notTaken && fall.loc == .pos 1 &&
      taken.E_k == [Expr.mkRel (Reg.real32 1) .ltu rhs] &&
      fall.E_k == [Expr.mkRel (Reg.real32 1) .geu rhs] &&
      taken.P_k == [.branch 1 .taken ⟨lhs, .ltu, rhs⟩] &&
      fall.P_k == [.branch 1 .notTaken ⟨lhs, .geu, rhs⟩] &&
      let child := update (SemState.mk E []) { exprs := taken.E_k, predicates := taken.P_k }
      let overwritten := update child { exprs := ((update ⟨Expr.nil, []⟩ { exprs := [Expr.mkEq (Reg.real32 1) (solve (Term.C32 0))], predicates := [] }).exprs), predicates := [] }
      overwritten.exprs.constraints.isEmpty &&
        child.exprs.constraints == [Expr.mkRel (Reg.real32 1) .ltu rhs] &&
        child.exprs.lookupEq (Reg.real32 1) == some lhs &&
        overwritten.predicates == [.branch 1 .taken ⟨lhs, .ltu, rhs⟩] &&
        overwritten.exprs.lookupEq (Reg.real32 1) == some (Term.C32 0)
  | _ => false

/-- All six full-width branch operations use the required relation/complement. -/
private def symbolicBtypeRelationsCheck : Bool :=
  let lhs := Term.V32 101
  let rhs := Term.V32 102
  let E := (update ⟨Expr.nil, []⟩ { exprs := [Expr.mkEq (Reg.real32 1) (solve lhs)], predicates := [] }).exprs
    |> (fun acc => (update ⟨acc, []⟩ { exprs := [Expr.mkEq (Reg.real32 2) (solve rhs)], predicates := [] }).exprs)
  let cases : List (bop × Rel) := [(.BEQ, .eq), (.BNE, .ne),
    (.BLT, .lts), (.BGE, .ges), (.BLTU, .ltu), (.BGEU, .geu)]
  cases.all fun (op, rel) =>
    let I := #[Insn.BTYPE (8#13, .Regidx 2#5, .Regidx 1#5, op),
      decodeInsnWord 0x00100513, decodeInsnWord 0x00008067]
    match rv32StepBound I none none 0 ⟨E, []⟩ with
    | .candidates [taken, fall] => taken.dir == .taken && fall.dir == .notTaken &&
        taken.E_k == [Expr.mkRel (Reg.real32 1) rel rhs] &&
        fall.E_k == [Expr.mkRel (Reg.real32 1) rel.compl rhs] &&
        taken.P_k == [.branch 1 .taken ⟨lhs, rel, rhs⟩] &&
        fall.P_k == [.branch 1 .notTaken ⟨lhs, rel.compl, rhs⟩] &&
        let child := update (SemState.mk E []) { exprs := taken.E_k, predicates := taken.P_k }
        child.exprs.lookupEq (Reg.real32 1) == some lhs && child.exprs.keysUnique
    | _ => false

/-- Concrete evaluation retains just the feasible side and its comparison. -/
private def concreteBltuFeasibleSideCheck : Bool :=
  let I := decodeProgram #[0x0020e463, 0x00100513, 0x00008067]
  [(1, 2, Direction.taken, Location.pos 2, Rel.ltu),
   (2, 1, Direction.notTaken, Location.pos 1, Rel.geu),
   (2, 2, Direction.notTaken, Location.pos 1, Rel.geu)].all fun (a, b, dir, loc, rel) =>
    let E := (update ⟨Expr.nil, []⟩ { exprs := [Expr.mkEq (Reg.real32 1) (solve (Term.C32 a))], predicates := [] }).exprs
      |> (fun acc => (update ⟨acc, []⟩ { exprs := [Expr.mkEq (Reg.real32 2) (solve (Term.C32 b))], predicates := [] }).exprs)
    match rv32StepBound I none none 0 ⟨E, []⟩ with
    | .candidates [c] => c.dir == dir && c.loc == loc &&
        c.E_k == [Expr.mkRel (Reg.real32 1) rel (Term.C32 b)] &&
        c.P_k == [.branch 1 (if dir == .taken then .taken else .notTaken)
          ⟨Term.C32 a, rel, Term.C32 b⟩]
    | _ => false

/-- A symbolic branch cannot bind to the middle of a full-width instruction. -/
private def symbolicBltuUnboundTargetCheck : Bool :=
  let I := #[Insn.BTYPE (2#13, .Regidx 2#5, .Regidx 1#5, .BLTU),
    decodeInsnWord 0x00008067]
  let E := (update ⟨Expr.nil, []⟩ { exprs := [Expr.mkEq (Reg.real32 1) (solve (Term.V32 101))], predicates := [] }).exprs
    |> (fun acc => (update ⟨acc, []⟩ { exprs := [Expr.mkEq (Reg.real32 2) (solve (Term.V32 102))], predicates := [] }).exprs)
  match rv32StepBound I none none 0 ⟨E, []⟩ with
  | .reject .unboundTarget => true
  | _ => false

#guard symbolicBltuDualSuccessorCheck
#guard symbolicBtypeRelationsCheck
#guard concreteBltuFeasibleSideCheck
#guard symbolicBltuUnboundTargetCheck

/-- Expand through symbolic BLTU and its taken-side return, preserving both nodes. -/
private def esp32c3OpeningCheck : Bool :=
  let p := smokeEntryParams
  let stepFn := rv32StepBound esp32c3Program (some 0x1000) (some 0x2000)
  match rv32Init esp32c3Program p 0 48 with
  | .error _ => false
  | .ok ws0 =>
    match expandN esp32c3Program.size stepFn ws0 6 with
    | .inl _ => false
    | .inr ws =>
      match ws.nodes[0]?, ws.nodes[4]?, ws.nodes[5]?, ws.nodes[6]?, ws.nodes[7]? with
      | some root, some branch, some taken, some fall, some returned =>
        root.state.exprs.length == 14 &&
        initialEqCheck root.state.exprs (Reg.real32 10) p.tCtx &&
        branch.loc == .pos 4 &&
        initialEqCheck branch.state.exprs (Reg.real32 12) p.tData &&
        initialEqCheck branch.state.exprs (Reg.real32 11) (addStar .w32 p.tData p.tLen) &&
        initialEqCheck branch.state.exprs (Reg.real32 13) (addStar .w32 p.tData (Term.C32 14)) &&
        initialEqCheck branch.state.exprs (Reg.real32 10) (Term.C32 2) &&
        ctxEq branch.state.exprs .data p.tData &&
        (branch.state.exprs.lookupEq (Reg.real32 32)).isNone &&
        ws.nodes.size == 8 && ws.edges.size == 7 && ws.work == [6] && ws.fuel == 42 &&
        taken.loc == .pos 47 && fall.loc == .pos 5 && returned.loc == .exit &&
        (programOffsets esp32c3Program)[47]? == some 126 &&
        taken.state.exprs.constraints == [Expr.mkRel (Reg.real32 11) .ltu
          (solve (addStar .w32 p.tData (Term.C32 14)))] &&
        fall.state.exprs.constraints == [Expr.mkRel (Reg.real32 11) .geu
          (solve (addStar .w32 p.tData (Term.C32 14)))] &&
        taken.state.predicates == [.branch 5 .taken
          ⟨solve (addStar .w32 p.tData p.tLen), .ltu,
            solve (addStar .w32 p.tData (Term.C32 14))⟩] &&
        fall.state.predicates == [.branch 5 .notTaken
          ⟨solve (addStar .w32 p.tData p.tLen), .geu,
            solve (addStar .w32 p.tData (Term.C32 14))⟩] &&
        returned.state.predicates == taken.state.predicates ++ [.ret (Term.C32 2)] &&
        initialEqCheck returned.state.exprs (Reg.real32 10) (Term.C32 2) &&
        match ws.edges[4]?, ws.edges[5]? with
        | some te, some fe => te.src == 4 && fe.src == 4 &&
          te.dst == 5 && fe.dst == 6 && te.dir == .taken && fe.dir == .notTaken
        | _, _ => false
      | _, _, _, _, _ => false

/-- The real +116 BLTU forks before either continuation is expanded.
The taken side exits; the fallthrough adjusts SP and successfully spills a word. -/
private def esp32c3BltuContinuationsCheck : Bool :=
  let I : Array Insn := esp32c3Program
  let stepFn := rv32StepBound I (some 0x1000) (some 0x2000)
  let isRealBranch := match I[4]? with
    | some (Insn.BTYPE (imm, rs2, rs1, bop.BLTU)) =>
      s 13 imm.toNat == 116 && rs1.toNat == 11 && rs2.toNat == 13
    | _ => false
  isRealBranch && match rv32Init I smokeEntryParams 0 48 with
  | .error _ => false
  | .ok ws0 =>
    match expandN I.size stepFn ws0 7 with
    | .inl _ => false
    | .inr ws =>
      match ws.nodes[4]?, ws.nodes[7]?, ws.nodes[8]? with
      | some branch, some returned, some afterAdjust =>
        branch.loc == .pos 4 && returned.loc == .exit &&
        afterAdjust.loc == .pos 6 && ws.work == [8] &&
        ws.edges.any (fun e => e.src == 4 && e.dir == .taken) &&
        ws.edges.any (fun e => e.src == 4 && e.dir == .notTaken) &&
        initialEqCheck afterAdjust.state.exprs (Reg.real32 2)
          (addStar .w32 smokeEntryParams.tSp (Term.C32 (cImm6 48#6))) &&
        match I[6]?, expandOne I.size stepFn ws with
        | some (Insn.C_SWSP (uimm, rs2)), .inr next =>
          match next.nodes[9]?,
              stackSlot afterAdjust.state.exprs sp (uimm.toNat <<< 2),
              readReg afterAdjust.state.exprs rs2 with
          | some stored, some address, some value =>
            stored.loc == .pos 7 && next.work == [9] &&
            next.nodes.size == ws.nodes.size + 1 && next.edges.size == ws.edges.size + 1 &&
            initialEqCheck stored.state.exprs
              (.stack (address * 8) (address * 8 + 32)) value &&
            stored.state.predicates == afterAdjust.state.predicates &&
            match expandN I.size stepFn next 2 with
            | .inr continued => continued.nodes.size == next.nodes.size + 2
            | _ => false
          | _, _, _ => false
        | _, _ => false
      | _, _, _ => false

#guard esp32c3BltuContinuationsCheck

private def symbolicBranchesCheck : Bool :=
  let ta := Term.V32 1
  let tb := Term.V32 2
  let σ : SemState := ⟨(update ⟨Expr.nil, []⟩ { exprs := [Expr.mkEq (Reg.real32 11) (solve ta)], predicates := [] }).exprs
    |> (fun acc => (update ⟨acc, []⟩ { exprs := [Expr.mkEq (Reg.real32 13) (solve tb)], predicates := [] }).exprs), []⟩
  [bop.BEQ, .BNE, .BLT, .BGE, .BLTU, .BGEU].all fun op =>
    let I := #[Insn.BTYPE (8#13, .Regidx 13#5, .Regidx 11#5, op),
      decodeInsnWord 0x00100513, decodeInsnWord 0x00008067]
    match rv32Step I 0 σ with
    | .candidates [a, b] =>
      a.dir == .taken && b.dir == .notTaken &&
      a.loc == .pos 2 && b.loc == .pos 1 &&
      a.E_k == [Expr.mkRel (Reg.real32 11) (branchRel op) tb] &&
      b.E_k == [Expr.mkRel (Reg.real32 11) (branchRel op).compl tb] &&
      a.P_k == [.branch 1 .taken ⟨ta, branchRel op, tb⟩] &&
      b.P_k == [.branch 1 .notTaken ⟨ta, (branchRel op).compl, tb⟩]
    | _ => false

private def compressedBranchesCheck : Bool :=
  let σ : SemState := ⟨(update ⟨Expr.nil, []⟩ { exprs := [Expr.mkEq (Reg.real32 8) (solve (Term.V32 3))], predicates := [] }).exprs, []⟩
  [0xc011, 0xe011].all fun word =>
    let I := decodeProgram #[UInt32.ofNat word, 0x0001, 0x0001]
    match rv32Step I 0 σ with
    | .candidates [a, b] => a.dir == .taken && b.dir == .notTaken &&
      a.loc == .pos 2 && b.loc == .pos 1 &&
      let rel := if word == 0xc011 then Rel.eq else Rel.ne
      a.E_k == [Expr.mkRel (Reg.real32 8) rel (Term.C32 0)] &&
      b.E_k == [Expr.mkRel (Reg.real32 8) rel.compl (Term.C32 0)] &&
      a.P_k == [.branch 1 .taken ⟨Term.V32 3, rel, Term.C32 0⟩] &&
      b.P_k == [.branch 1 .notTaken ⟨Term.V32 3, rel.compl, Term.C32 0⟩]
    | _ => false

#guard symbolicBranchesCheck
#guard compressedBranchesCheck

/-- A packet compare whose fallthrough is `c.j` into `li a0, 1; ret` keeps the body. -/
private def sharedReturnKeepsBody : Bool :=
  match «seal» 32 (Term.app .w32 (.inputByte 0) [Term.C32 0, Term.C32 12]) with
  | none => false
  | some pkt =>
  let σ : SemState := ⟨(update ⟨Expr.nil, []⟩ { exprs := [Expr.mkEq (Reg.real32 12) (solve pkt)], predicates := [] }).exprs
      |> (fun acc => (update ⟨acc, []⟩ { exprs := [Expr.mkEq (Reg.real32 14) (solve (Term.C32 8))], predicates := [] }).exprs), []⟩
  let jump := match encodeCompressed 0xa011#16 with
    | .C_J imm => Insn.C_J imm
    | other => other
  let I := #[
    Insn.BTYPE (6#13, .Regidx 14#5, .Regidx 12#5, .BEQ),
    jump,
    Insn.C_NOP 0#6,
    decodeInsnWord 0x00100513,
    decodeInsnWord 0x00008067]
  match rv32Step I 0 σ with
  | .candidates [body, exitArm] =>
    body.dir == .taken && body.loc == .pos 2 &&
      exitArm.dir == .notTaken && exitArm.loc == .exit
  | _ => false

#guard sharedReturnKeepsBody
#guard match encodeCompressed 0xa011#16 with
  | .C_J imm => 2 * s 11 imm.toNat == 4
  | _ => false
#guard match encodeCompressed 0xbffd#16 with
  | .C_J imm => 2 * s 11 imm.toNat == -2
  | _ => false
#guard match encodeCompressed 0xdc7d#16 with
  | .C_BEQZ (imm, _) => 2 * s 8 imm.toNat == -2
  | _ => false

#guard esp32c3DecodeCheck
#guard esp32c3FirstLoadCheck
#guard contextWordLoadsCheck
#guard contextLoadRejectionCheck
#guard contextShiftedBaseCheck
#guard compressedLwOffsetCheck
#guard esp32c3OpeningCheck

/-! Explored instruction support (indices in esp32c3Program):
0–1 C.LW context; 2/11/23/27/31 ADDI; 3/17/32–35 C.LI;
4/24 BLTU, 18 BNE, 28 BEQ; 5/10/29/46 C.ADDI;
6–7 C.SWSP; 8 C.ADDI4SPN; 9 LHU, 16/19 LBU;
12–13 SLTU; 14 C.OR; 15 C.BNEZ; 20 C.SLLI; 21 C.SRLI;
22 C.ADD; 26 C.LUI; 30 LUI; 44–45 C.LWSP; 47 C.JR + Exit with a0 equality.
25 LHU has a symbolic packet offset. A passed data_end check on the path
binds it as a compound packet access and continues at 26.
36 C.JAL has its link-value semantics, but target offset 104 - 616 = -512
is outside this image. External call/result contracts are required to reach 37–43;
we retain UnboundTarget rather than fabricate a helper result or fallthrough.
-/

/-- Packet-value branches keep the fallthrough and record the abort arm as Exit.
After 38 steps the external jump at the queued call is still unbound. -/
private def esp32c3DeepFrontierCheck : Bool :=
  let I := esp32c3Program
  let stepFn := rv32StepBound I (some 0x1000) (some 0x2000)
  match rv32Init I smokeEntryParams 0 512 with
  | .error _ => false
  | .ok ws0 => match expandN I.size stepFn ws0 38 with
    | .inl (.fail .unboundTarget g) => g.nodes.size == 41
    | _ => false

private def helperObservationMergeCheck : Bool :=
  let p := Predicate.helper 8 .clock []
  let q := Predicate.helper 7 .clock []
  ((update { exprs := [], predicates := [q] } { exprs := [], predicates := [p, p, q] }).predicates == [q, p]) &&
  renderPredicateJson p == "{\"kind\":\"helper\",\"event\":8,\"helperId\":5,\"args\":[]}"

/-- C.JR and full JALR freeze the complete symbolic pre-return a0 on wrapper Exit. -/
private def boundReturnExprCheck : Bool :=
  let E := (update ⟨Expr.nil, []⟩ { exprs := [Expr.mkEq (Reg.real32 1) (solve (Term.C32 0x2000))], predicates := [] }).exprs
    |> (fun acc => (update ⟨acc, []⟩ { exprs := [Expr.mkEq (Reg.real32 10) (solve (Term.V32 123))], predicates := [] }).exprs)
  [decodeProgram #[0x00008067], decodeProgram #[0x8082]].all (fun I =>
    match rv32StepBound I (some 0x1000) (some 0x2000) 0 ⟨E, []⟩ with
    | .candidates [c] => c.loc == .exit && c.P_k == [.ret (Term.V32 123)] &&
        initialEqCheck (((update ⟨E, []⟩ { exprs := c.E_k, predicates := [] }).exprs)) (Reg.real32 10) (Term.V32 123)
    | _ => false) &&
  [decodeProgram #[0x00008067], decodeProgram #[0x8082]].all (fun I =>
    match rv32StepBound I (some 0x1000) (some 0x2000) 0
        ⟨(update ⟨Expr.nil, []⟩ { exprs := [Expr.mkEq (Reg.real32 1) (solve (Term.C32 0x2000))], predicates := [] }).exprs, []⟩ with
    | .reject .undefinedSrc => true
    | _ => false) &&
  (match rv32StepBound (decodeProgram #[0x00008067]) (some 0x1000) (some 0x2002)
      0 ⟨E, []⟩ with
    | .reject .unboundTarget => true
    | _ => false) &&
  (match rv32StepBound (decodeProgram #[0x00008067, 0x0001])
      (some 0x1000) (some 0x2000) 0
      ⟨(update ⟨Expr.nil, []⟩ { exprs := [Expr.mkEq (Reg.real32 1) (solve (Term.C32 0x1004))], predicates := [] }).exprs, []⟩ with
    | .candidates [c] => c.loc == .pos 1 && c.P_k.isEmpty
    | _ => false) &&
  (match rv32StepBound (decodeProgram #[0x00008067])
      (some 0x1000) (some 0x2000) 0
      ⟨(update ⟨Expr.nil, []⟩ { exprs := [Expr.mkEq (Reg.real32 1) (solve (Term.C32 0x2000))], predicates := [] }).exprs
        |> (fun acc => (update ⟨acc, []⟩ { exprs := [Expr.mkEq (Reg.real32 10) (solve (Term.V32 7))], predicates := [] }).exprs)
        |> (fun acc => (let row := solveExpr (Expr.mkRel (Reg.real32 10) .eq (Term.V32 123)); if acc.contains row then acc else acc ++ [row])), []⟩ with
    | .candidates [c] => c.loc == .exit && c.P_k == [.ret (Term.V32 7)]
    | _ => false)

/-- Packet loads are repeatable symbolic Terms; unrelated/unbound bases reject. -/
private def packetLoadsCheck : Bool :=
  match buildE0 smokeEntryParams with
  | .error _ => false
  | .ok σ =>
    let E := (update ⟨σ.exprs, []⟩ { exprs := [Expr.mkEq (Reg.real32 12) (solve smokeEntryParams.tData)], predicates := [] }).exprs
    [1, 2, 4].all (fun width =>
      [false, true].all fun unsigned =>
        let i := Insn.LOAD (12#12, .Regidx 12#5, .Regidx 14#5, unsigned, width)
        match stepEffects E i , step E i  with
        | some effect, some a => effect.inputs.length == width && a.length == width + 1 &&
          a.keysUnique && a.lookupEq (Reg.real32 14) == effect.updates.lookupEq (Reg.real32 14) &&
          (match a.lookupEq (Reg.real32 14) with
            | some t => (eval t).isNone
            | none => false)
        | _, _ => false) &&
    (exprPacketLOAD E sp (.Regidx 14#5) 0 1 true).isNone &&
    (exprPacketLOAD E (.Regidx 28#5) zreg 0 1 true).isNone &&
    (exprPacketLOAD E (.Regidx 12#5) zreg 0 3 true).isNone &&
    (match exprPacketLOAD E (.Regidx 12#5) zreg 0 1 true with
      | some Ei => Ei.isEmpty
      | none => false) &&
    (eval (star .w32 (.inputByte 0) [Term.C32 4096, Term.C32 4108])).isNone

#guard packetLoadsCheck

#guard esp32c3DeepFrontierCheck
#guard helperObservationMergeCheck
#guard boundReturnExprCheck

@[export lean_rv32_expand_builtin_snapshot]
def exportRv32Snapshot (steps budget : UInt32) : String :=
  rv32Snapshot esp32c3Program smokeEntryParams 0 steps.toNat budget.toNat

-- Parent Rust glue: insns is a boxed Lean Array UInt32; steps/budget are uint32_t, result Lean String.
@[export lean_rv32_expand_words_snapshot]
def exportRv32WordsSnapshot (insns : Array UInt32) (steps budget : UInt32) : String :=
  rv32Snapshot (decodeProgram insns) smokeEntryParams 0 steps.toNat budget.toNat

private def helperTarget (i : Insn) (pc : Nat) (Eg : List Expr) : Option Nat :=
  match i with
  | .JAL (imm, rd) =>
    if rd.toNat != 1 then none
    else some (Int.toNat ((Int.ofNat pc + s 21 imm.toNat) % (1 <<< 32)))
  | .C_JAL imm => some (Int.toNat ((Int.ofNat pc + 2 * s 11 imm.toNat) % (1 <<< 32)))
  | .JALR (imm, rs1, rd) => do
    if rd.toNat != 1 then none else
      let t ← readReg Eg rs1
      let a ← eval (solve t)
      pure (MNat 32 (a + immI32 imm) &&& ((1 <<< 32) - 2))
  | .C_JALR rs1 => do
    let t ← readReg Eg rs1
    let a ← eval (solve t)
    pure (MNat 32 a &&& ((1 <<< 32) - 2))
  | _ => none

/-- One ISA step. Image base, helper, return, and the context root are anchors in `σ.exprs`.
A later write to x1 does not move the return label. -/
def inferStep (I : Array Insn) (event : NodeId) (j : Nat) (σ : SemState) : StepResult :=
  let base := contextNat σ.exprs .imageBase
  let ret := contextNat σ.exprs .wrapperReturn
  let helper := contextNat σ.exprs .helper
  let bound := contextValue σ.exprs .ctx
  let fallback := rv32StepBound I base ret j σ bound (some event)
  match I[j]?, (programOffsets I)[j]?, base, helper with
  | some i, some offset, some b, some h =>
    if helperTarget i (b + offset) σ.exprs != some h then fallback
    else if !guardEg σ.exprs then .reject .localReject
    else match nextPosition I j with
      | none => .reject .unboundTarget
      | some loc =>
        let Eg := (update ⟨σ.exprs, []⟩ { exprs := [Expr.mkEq (Reg.real32 32) (solve (Term.C32 (b + offset)))], predicates := [] }).exprs
        match RV32.step Eg i bound σ.predicates,
            helperPredicate event σ.exprs bound σ.predicates with
        | some link, .ok predicate =>
          match helperExpr predicate, helperMapWrites σ.exprs predicate with
          | .ok result, .ok mapRows =>
            let Ei := (update ⟨(((update ⟨link, []⟩ { exprs := result, predicates := [] }).exprs)), []⟩ { exprs := mapRows, predicates := [] }).exprs
            .candidates [⟨.ok, loc, Ei, [predicate]⟩]
          | .error reason, _ | _, .error reason => .reject reason
        | _, .error reason => .reject reason
        | none, _ => .reject .undefinedSrc
  | _, _, _, _ => fallback

/-- Ordinary and compressed stores emit one complete-source event and little-endian bytes.
The misaligned concrete SP case selects Packet rather than an aligned Stack word. -/
private def packetNat (E : List Expr) (offset bytes : Nat) : Option Nat := do
  let t ← readInterval E (.packet (offset * 8) (offset * 8 + 8 * bytes))
  eval (solve t)

private def packetStoreObservationsCheck : Bool := Id.run do
  let p := { smokeEntryParams with tData := Term.C32 0x4000, tLen := Term.C32 64 }
  let .ok σ := buildE0 p | return false
  let value := Term.C32 0xaabbccdd
  let regs := (update ⟨σ.exprs, []⟩ { exprs := [Expr.mkEq (Reg.real32 12) (solve p.tData)], predicates := [] }).exprs
    |> (fun acc => (update ⟨acc, []⟩ { exprs := [Expr.mkEq (Reg.real32 2) (solve (Term.C32 0x4001))], predicates := [] }).exprs)
    |> (fun acc => (update ⟨acc, []⟩ { exprs := [Expr.mkEq (Reg.real32 11) (solve value)], predicates := [] }).exprs)
  let some stored := «seal» (Reg.packet (20 * 8) (20 * 8 + 8)).bits (Term.C32 99) | return false
  let E := (update ⟨regs, []⟩ { exprs := [Expr.mkEq (Reg.packet (20 * 8) (20 * 8 + 8)) stored], predicates := [] }).exprs
  let cases : List (Insn × Nat × Nat) := [
    (.STORE (2#12, .Regidx 11#5, .Regidx 12#5, 1), 2, 1),
    (.STORE (2#12, .Regidx 11#5, .Regidx 12#5, 2), 2, 2),
    (.STORE (4#12, .Regidx 11#5, .Regidx 12#5, 4), 4, 4),
    (.C_SW (1#5, .Cregidx 4#3, .Cregidx 3#3), 4, 4),
    (.C_SWSP (1#6, .Regidx 11#5), 5, 4)]
  for (i, offset, bytes) in cases do
    let I := #[i, decodeInsnWord 0x0001]
    let .candidates [c] := inferStep I 77 0 ⟨E, []⟩ | return false
    let kept := 0xaabbccdd &&& ((1 <<< (8 * bytes)) - 1)
    if c.P_k != [.packetWrite 77 offset (8 * bytes) value] ||
        c.E_k.isEmpty || c.loc != .pos 1 then return false
    let child := update ⟨E, []⟩ { exprs := c.E_k, predicates := c.P_k }
    if packetNat child.exprs offset bytes != some kept ||
        packetNat child.exprs 20 1 != some 99 then return false
    let .candidates [again] := inferStep I 78 0 child | return false
    let repeated := update child { exprs := again.E_k, predicates := again.P_k }
    if repeated.predicates != [.packetWrite 77 offset (8 * bytes) value,
        .packetWrite 78 offset (8 * bytes) value] then return false
  let I := #[Insn.STORE (2#12, .Regidx 11#5, .Regidx 12#5, 2), decodeInsnWord 0x0001]
  let symbolic := Term.V32 900
  let symbolicE := (update ⟨E, []⟩ { exprs := [Expr.mkEq (Reg.real32 11) (solve symbolic)], predicates := [] }).exprs
  let .candidates [c] := inferStep I 77 0 ⟨symbolicE, []⟩ | return false
  if c.P_k != [.packetWrite 77 2 16 symbolic] ||
      (c.E_k.lookupEq (.packet 16 24)).isNone ||
      (c.E_k.lookupEq (.packet 24 32)).isNone then return false
  let child := update ⟨symbolicE, []⟩ { exprs := c.E_k, predicates := c.P_k }
  let overwritten := update child { exprs := ((update ⟨Expr.nil, []⟩ { exprs := [Expr.mkEq (Reg.real32 11) (solve (Term.C32 0))], predicates := [] }).exprs), predicates := [] }
  if overwritten.predicates != [.packetWrite 77 2 16 symbolic] then return false
  let zeroI := #[Insn.STORE (0#12, zreg, .Regidx 12#5, 1), decodeInsnWord 0x0001]
  let .candidates [zero] := inferStep zeroI 79 0 ⟨E, []⟩ | return false
  let zeroState := update ⟨E, []⟩ { exprs := zero.E_k, predicates := zero.P_k }
  return zero.P_k == [.packetWrite 79 0 8 (Term.C32 0)] &&
    packetNat zeroState.exprs 0 1 == some 0

private def packetStoreRejectsMissingInputsCheck : Bool := Id.run do
  let .ok σ := buildE0 smokeEntryParams | return false
  let E := (update ⟨σ.exprs, []⟩ { exprs := [Expr.mkEq (Reg.real32 12) (solve smokeEntryParams.tData)], predicates := [] }).exprs
    |> (fun acc => (update ⟨acc, []⟩ { exprs := [Expr.mkEq (Reg.real32 11) (solve (Term.C32 7))], predicates := [] }).exprs)
  let store := Insn.STORE (0#12, .Regidx 11#5, .Regidx 12#5, 4)
  let I := #[store, decodeInsnWord 0x0001]
  let missing : List Expr := E.filter (fun e => e.reg != Reg.real32 11)
  let results := [rv32StepBound I none none 0 ⟨E, []⟩,
    inferStep I 77 0 ⟨missing, []⟩,
    inferStep #[Insn.STORE (0#12, .Regidx 11#5, .Regidx 28#5, 4),
      decodeInsnWord 0x0001] 77 0 ⟨E, []⟩]
  return results.all fun result =>
    match result with | .reject .undefinedSrc => true | _ => false

/-- Without a frozen key the map slot cannot be named, so the local step rejects too. -/
private def mapStoreObservationGapCheck : Bool :=
  let pointer := star .w32 (.externalResult 9 0) [Term.C32 1, Term.C32 42, Term.V32 0]
  let E := (update ⟨Expr.nil, []⟩ { exprs := [Expr.mkEq (Reg.real32 8) (solve pointer)], predicates := [] }).exprs
    |> (fun acc => (update ⟨acc, []⟩ { exprs := [Expr.mkEq (Reg.real32 11) (solve (Term.C32 0xaabbccdd))], predicates := [] }).exprs)
    |> (fun acc => (update ⟨acc, []⟩ { exprs := [Expr.mkEq (Reg.real32 2) (solve pointer)], predicates := [] }).exprs)
  let stores := [1, 2, 4].map (fun width =>
    Insn.STORE (0#12, .Regidx 11#5, .Regidx 8#5, width)) ++
    [.C_SW (0#5, .Cregidx 0#3, .Cregidx 3#3), .C_SWSP (0#6, .Regidx 11#5)]
  stores.all fun i =>
    (step E i).isNone &&
      match inferStep #[i, decodeInsnWord 0x0001] 77 0 ⟨E, []⟩ with
      | .reject .undefinedSrc => true
      | _ => false

/-- Frozen lookup key plus the installed layout authorize MapWrite on SB/SH/SW. -/
private def mapStoreObservationsCheck : Bool := Id.run do
  let pointer := star .w32 (.externalResult 9 0) [Term.C32 1, Term.C32 42, Term.V32 0]
  let key := [Term.C32 1, Term.C32 2, Term.C32 3, Term.C32 4]
  let lookup : Predicate := .helper 9 .lookup ([Term.C32 42, Term.V32 0] ++ key)
  let some E := Anchor.installMaps ((update ⟨Expr.nil, []⟩ { exprs := [Expr.mkEq (Reg.real32 8) (solve pointer)], predicates := [] }).exprs
    |> (fun acc => (update ⟨acc, []⟩ { exprs := [Expr.mkEq (Reg.real32 11) (solve (Term.C32 0xaabbccdd))], predicates := [] }).exprs))
    [{ mapId := 42, keySize := 4, valueSize := 16 }] | return false
  let some keyBytes := key.mapM mapKeyByte | return false
  let some seeded := ((«seal» (Reg.map 42 keyBytes 0 32).bits (Term.C32 0) >>= fun stored => some (update ⟨E, []⟩ { exprs := [Expr.mkEq (.map 42 keyBytes 0 32) stored], predicates := [] }).exprs)) | return false
  let stores : List (Insn × Nat) := [
    (.STORE (0#12, .Regidx 11#5, .Regidx 8#5, 1), 1),
    (.STORE (0#12, .Regidx 11#5, .Regidx 8#5, 2), 2),
    (.STORE (0#12, .Regidx 11#5, .Regidx 8#5, 4), 4),
    (.C_SW (0#5, .Cregidx 0#3, .Cregidx 3#3), 4)]
  for (i, width) in stores do
    let I := #[i, decodeInsnWord 0x0001]
    let .candidates [c] := inferStep I 77 0 ⟨seeded, [lookup]⟩ | return false
    let want := .mapWrite 77 (Term.C32 42) key 0 (8 * width) (Term.C32 0xaabbccdd)
    if c.P_k != [want] || c.loc != .pos 1 ||
        !(c.E_k.any fun e => match e.reg with | .map .. => true | _ => false) then
      return false
    let child := update ⟨seeded, [lookup]⟩ { exprs := c.E_k, predicates := c.P_k }
    if !child.predicates.contains lookup || !child.predicates.contains want then return false
    if width == 0 then return false
  let prior := [lookup, .mapWrite 77 (Term.C32 42) key 0 32 (Term.C32 0xaabbccdd)]
  let .candidates [again] := inferStep #[Insn.STORE (0#12, .Regidx 11#5, .Regidx 8#5, 4),
      decodeInsnWord 0x0001] 78 0 ⟨seeded, prior⟩ | return false
  let kept := update ⟨seeded, prior⟩ { exprs := again.E_k, predicates := again.P_k }
  return kept.predicates.contains (.mapWrite 77 (Term.C32 42) key 0 32 (Term.C32 0xaabbccdd)) &&
    kept.predicates.contains (.mapWrite 78 (Term.C32 42) key 0 32 (Term.C32 0xaabbccdd))

/-- The skipped sequential instruction makes source node identity differ from instruction index. -/
private def packetSnapshotEventCheck : Bool :=
  let I := #[Insn.LOAD (0#12, .Regidx 10#5, .Regidx 12#5, true, 4),
    Insn.BTYPE (8#13, zreg, zreg, .BEQ),
    Insn.ITYPE (0#12, zreg, zreg, .ADDI),
    Insn.STORE (0#12, zreg, .Regidx 12#5, 1),
    decodeInsnWord 0x00008067]
  let json := rv32Snapshot I smokeEntryParams 0 3 5
  json.contains (renderPredicateJson (.packetWrite 2 0 8 (Term.C32 0))) &&
    !(json.contains (renderPredicateJson (.packetWrite 3 0 8 (Term.C32 0))))

/-- Matching pointer Map and frozen-key observation Map still authorizes MapWrite. -/
private def mapWriteProvenanceMatchCheck : Bool := Id.run do
  let pointer := star .w32 (.externalResult 9 0) [Term.C32 1, Term.C32 42, Term.V32 0]
  let key := [Term.C32 1, Term.C32 2, Term.C32 3, Term.C32 4]
  let lookup : Predicate := .helper 9 .lookup ([Term.C32 42, Term.V32 0] ++ key)
  let some E := Anchor.installMaps ((update ⟨Expr.nil, []⟩ { exprs := [Expr.mkEq (Reg.real32 8) (solve pointer)], predicates := [] }).exprs
    |> (fun acc => (update ⟨acc, []⟩ { exprs := [Expr.mkEq (Reg.real32 11) (solve (Term.C32 123))], predicates := [] }).exprs))
    [{ mapId := 42, keySize := 4, valueSize := 16 }] | return false
  let some keyBytes := key.mapM mapKeyByte | return false
  let some seeded := ((«seal» (Reg.map 42 keyBytes 0 32).bits (Term.C32 0) >>= fun stored => some (update ⟨E, []⟩ { exprs := [Expr.mkEq (.map 42 keyBytes 0 32) stored], predicates := [] }).exprs)) | return false
  let I := #[Insn.STORE (0#12, .Regidx 11#5, .Regidx 8#5, 4), decodeInsnWord 0x0001]
  match inferStep I 77 0 ⟨seeded, [lookup]⟩ with
  | .candidates [c] =>
      c.loc == .pos 1 &&
        c.P_k == [.mapWrite 77 (Term.C32 42) key 0 32 (Term.C32 123)]
  | _ => false

/-- Pointer Map 42 with frozen-key observation Map 17 must reject (no successor). -/
private def mapWriteProvenanceMismatchCheck : Bool := Id.run do
  let pointer := star .w32 (.externalResult 9 0) [Term.C32 1, Term.C32 42, Term.V32 7]
  let key := [Term.C32 1]
  let lookup : Predicate := .helper 9 .lookup ([Term.C32 17, Term.V32 7] ++ key)
  let base := (update ⟨Expr.nil, []⟩ { exprs := [Expr.mkEq (Reg.real32 8) (solve pointer)], predicates := [] }).exprs
    |> (fun acc => (update ⟨acc, []⟩ { exprs := [Expr.mkEq (Reg.real32 11) (solve (Term.C32 123))], predicates := [] }).exprs)
  let some keyBytes := key.mapM mapKeyByte | return false
  let mapsOnly17 : List MapLayout := [{ mapId := 17, keySize := 1, valueSize := 8 }]
  let mapsBoth : List MapLayout :=
    [{ mapId := 17, keySize := 1, valueSize := 8 }, { mapId := 42, keySize := 1, valueSize := 8 }]
  let I := #[Insn.STORE (0#12, .Regidx 11#5, .Regidx 8#5, 4), decodeInsnWord 0x0001]
  for maps in [mapsOnly17, mapsBoth] do
    let some E := Anchor.installMaps base maps | return false
    let some E := ((«seal» (Reg.map 17 keyBytes 0 32).bits (Term.C32 0) >>= fun stored => some (update ⟨E, []⟩ { exprs := [Expr.mkEq (.map 17 keyBytes 0 32) stored], predicates := [] }).exprs)) | return false
    match inferStep I 80 0 ⟨E, [lookup]⟩ with
    | .reject .undefinedSrc => pure ()
    | _ => return false
  return true

#guard packetStoreObservationsCheck
#guard packetStoreRejectsMissingInputsCheck
#guard mapStoreObservationGapCheck
#guard mapStoreObservationsCheck
#guard mapWriteProvenanceMatchCheck
#guard mapWriteProvenanceMismatchCheck
#guard packetSnapshotEventCheck

/-- Alignment and pairwise distinctness of the three create addresses. Extent is a step check. -/
private def bindingOk (b h ret : Nat) : Bool :=
  b != 0 && b % 4 == 0 && h != 0 && h % 4 == 0 && ret != 0 && ret % 4 == 0 &&
    h != ret && b != ret && b != h

/-- Skip when any anchor is absent so an empty context still steps. -/
private def imageOk (I : Array Insn) (E : List Expr) : Bool :=
  match contextNat E .imageBase, contextNat E .helper, contextNat E .wrapperReturn with
  | some b, some h, some ret =>
    let extent := I.foldl (fun n i => n + insnLength i) 0
    bindingOk b h ret && b + extent ≤ (1 <<< 32) &&
      !(b ≤ ret && ret < b + extent) && !(b ≤ h && h < b + extent)
  | _, _, _ => true

/-- Fail create without a fuel field (budget is Rust-owned). -/
private def createFailJson (reason : RejectReason) : String :=
  s!"\{\"status\":\"fail\",\"reason\":\"{reasonTag reason}\",\"failed\":null,\"work\":[],\"nodes\":[],\"edges\":[]}"

/-- Entry SemState plus anchors. No fuel — Rust binding owns the expansion budget. -/
@[export lean_rv32_expand_create]
def exportRv32ExpandCreate
    (base helper wrapperReturn : UInt32)
    (mapIds keySizes valueSizes : Array UInt32) : String :=
  if mapIds.size != keySizes.size || keySizes.size != valueSizes.size then
    createFailJson .invalidEntry
  else if !bindingOk base.toNat helper.toNat wrapperReturn.toNat then
    createFailJson .invalidEntry
  else
    let p := { smokeEntryParams with
      tEntry := Term.C32 base.toNat, tReturn := Term.C32 wrapperReturn.toNat,
      rEntries := savedRegs }
    match entrySemState p with
    | .error reason => createFailJson reason
    | .ok σ0 =>
      let layouts := (mapIds.toList.zip (keySizes.toList.zip valueSizes.toList)).map
        fun (id, sizes) =>
          ({ mapId := id.toNat, keySize := sizes.1.toNat, valueSize := sizes.2.toNat } : MapLayout)
      let installed := do
        let exprs ← Anchor.installMaps σ0.exprs layouts
        let exprs ← bindField exprs .imageBase (Term.C32 base.toNat)
        let exprs ← bindField exprs .helper (Term.C32 helper.toNat)
        let exprs ← bindField exprs .wrapperReturn (Term.C32 wrapperReturn.toNat)
        bindField exprs .ctx p.tCtx
      match installed with
      | none => createFailJson .invalidEntry
      | some exprs =>
        let (ej, pj) := renderSemStateJson { σ0 with exprs }
        s!"\{\"status\":\"running\",\"reason\":null,\"failed\":null,\"work\":[0],\"nodes\":[\{\"id\":0,\"loc\":\"0\",\"exprs\":[{ej}],\"predicates\":[{pj}]}],\"edges\":[]}"

private def headFailJson (reason : RejectReason) : String :=
  s!"\{\"status\":\"fail\",\"reason\":\"{reasonTag reason}\",\"successors\":[]}"

private def successorJson (dir : Direction) (loc : Location) (step : SemState) : String :=
  let loc := match loc with | .exit => "exit" | .pos j => toString j
  s!"\{\"dir\":\"{dirTag dir}\",\"loc\":\"{loc}\",{renderIncrementJson step}}"

/-- Stateless head inference. Anchors travel in the head exprs.
Fuel / work-queue updates are Rust-only. -/
@[export lean_rv32_expand_step]
def exportRv32ExpandStep (insns : Array UInt32) (event j : UInt32)
    (exprsJson predsJson : String) : String :=
  if insns.isEmpty then headFailJson .invalidEntry
  else
    let I := decodeProgram insns
    match parseSemStateJson exprsJson predsJson with
    | none => headFailJson .localReject
    | some state =>
      if !imageOk I state.exprs then headFailJson .invalidEntry
      else match inferStep I event.toNat j.toNat state with
        | .reject reason => headFailJson reason
        | .candidates cs =>
          match prepareAll state I.size cs with
          | .error reason => headFailJson reason
          | .ok _ =>
            let successors := String.intercalate ","
              (cs.map fun c => successorJson c.dir c.loc { exprs := c.E_k, predicates := c.P_k })
            s!"\{\"status\":\"ok\",\"reason\":null,\"successors\":[{successors}]}"

@[export lean_rv32_expand_bound_words_snapshot]
def exportRv32BoundWordsSnapshot (insns : Array UInt32) (exprsJson predsJson : String)
    (steps budget : UInt32) : String :=
  if insns.isEmpty then snapshotJson #[] #[] [] 0 "fail" (some .invalidEntry)
  else
    let I := decodeProgram insns
    match parseSemStateJson exprsJson predsJson with
    | none => snapshotJson #[] #[] [] 0 "fail" (some .invalidEntry)
    | some σ0 =>
      if !imageOk I σ0.exprs then snapshotJson #[] #[] [] 0 "fail" (some .invalidEntry)
      else match expandInit I.size 0 σ0 budget.toNat with
        | .error reason => snapshotJson #[] #[] [] 0 "fail" (some reason)
        | .ok ws => snapshotAfter I.size (inferStep I) ws steps.toNat

private def rootOf (response : String) : Option SemState := do
  let value ← (Lean.Json.parse response).toOption
  let nodes ← (value.getObjVal? "nodes" >>= Lean.Json.getArr?).toOption
  let node ← nodes[0]?
  let exprs ← (node.getObjVal? "exprs").toOption
  let preds ← (node.getObjVal? "predicates").toOption
  parseSemStateJson exprs.compress preds.compress

private def statelessStepCheck : Bool := Id.run do
  let insns := #[0x00700513, 0x00150513, 0x00008067]
  let response := exportRv32ExpandCreate 0x400 0x100 0x2000 #[] #[] #[]
  let some root := rootOf response | return false
  let I := decodeProgram insns
  let p := { smokeEntryParams with
    tEntry := Term.C32 0x400, tReturn := Term.C32 0x2000, rEntries := savedRegs }
  let .ok ws := expandInit I.size 0 root 3 | return false
  let (exprs, preds) := renderSemStateJson root
  let .inr next := expandOne I.size (inferStep I 0) ws | return false
  let .candidates [c] := inferStep I 0 0 root | return false
  let step : SemState := { exprs := c.E_k, predicates := c.P_k }
  return exportRv32ExpandStep insns 0 0 s!"[{exprs}]" s!"[{preds}]" ==
      s!"\{\"status\":\"ok\",\"reason\":null,\"successors\":[{successorJson .ok c.loc step}]}" &&
    (update root step).exprs == next.nodes[1]!.state.exprs &&
    (update root step).predicates == next.nodes[1]!.state.predicates &&
    p.rEntries == savedRegs &&
    root.exprs.keysUnique && root.exprs.length == 29 &&
    (root.exprs.filter (fun e => isRealReg e.reg)).length == 19 &&
    (root.exprs.filter (fun e => isContextReg e.reg)).length == 10 &&
    savedRegs.all (fun r => initialEqCheck root.exprs r p.tEntry) &&
    contextNat root.exprs .imageBase == some 0x400 &&
    exportRv32ExpandStep #[] 0 0 "[]" "[]" == headFailJson .invalidEntry &&
    !response.contains "\"fuel\":" && response.contains "\"status\":\"running\"" &&
    exportRv32ExpandCreate 0x401 0x100 0x2000 #[] #[] #[] == createFailJson .invalidEntry &&
    exportRv32ExpandCreate 0x400 0x100 0x2000 #[1] #[] #[] == createFailJson .invalidEntry

#guard statelessStepCheck

private def encodedOpenMCheck : Bool :=
  let E := Expr.nil
    |> (fun acc => (update ⟨acc, []⟩ { exprs := [Expr.mkEq (Reg.real32 8) (solve (Term.V32 41))], predicates := [] }).exprs)
    |> (fun acc => (update ⟨acc, []⟩ { exprs := [Expr.mkEq (Reg.real32 9) (solve (Term.V32 42))], predicates := [] }).exprs)
  let fixtures : List (UInt32 × Op) := [
    (0x02940533, .mullo .w32), (0x02941533, .mulh .w32),
    (0x02942533, .mulhsu .w32), (0x02943533, .mulhu .w32),
    (0x02944533, .sdiv .w32 0xffffffff), (0x02945533, .udiv .w32 0xffffffff),
    (0x02946533, .srem .w32), (0x02947533, .urem .w32)]
  fixtures.all fun (word, op) =>
    let expected := star .w32 op [Term.V32 41, Term.V32 42]
    let json := exportRv32ExpandStep #[word, 0x00008067] 80 0 s!"[{renderExprsJson E}]" "[]"
    json.contains "\"status\":\"ok\"" &&
      json.contains (renderExprJson (Expr.mkEq (Reg.real32 10) expected)) &&
      parseTerm (renderTerm expected) == some expected

private def encodedHelperBuffersCheck : Bool := Id.run do
  let key := addStar .w32 (Term.V32 0) (Term.C32 3)
  let value := addStar .w32 (Term.V32 0) (Term.C32 4)
  let some E := Anchor.installMaps (Expr.nil
    |> (fun acc => (update ⟨acc, []⟩ { exprs := [Expr.mkEq (Reg.real32 2) (solve (Term.V32 0))], predicates := [] }).exprs)
    |> (fun acc => (update ⟨acc, []⟩ { exprs := [Expr.mkEq (Reg.real32 5) (solve (Term.C32 0x100))], predicates := [] }).exprs)
    |> (fun acc => (update ⟨acc, []⟩ { exprs := [Expr.mkEq (Reg.real32 11) (solve (Term.C32 42))], predicates := [] }).exprs)
    |> (fun acc => (update ⟨acc, []⟩ { exprs := [Expr.mkEq (Reg.real32 12) (solve key)], predicates := [] }).exprs)
    |> (fun acc => (update ⟨acc, []⟩ { exprs := [Expr.mkEq (Reg.real32 13) (solve value)], predicates := [] }).exprs)
    |> (fun acc => (update ⟨acc, []⟩ { exprs := [Expr.mkEq (Reg.real32 14) (solve (Term.C32 0))], predicates := [] }).exprs))
    [{ mapId := 42, keySize := 3, valueSize := 2 }] | return false
  let some E := bindField E .imageBase (Term.C32 1024) | return false
  let some E := bindField E .helper (Term.C32 256) | return false
  let some E := bindField E .wrapperReturn (Term.C32 8192) | return false
  let some E := ((«seal» (Reg.stack 0 32).bits (Term.C32 0x04030201) >>= fun stored => some (update ⟨E, []⟩ { exprs := [Expr.mkEq (.stack 0 32) stored], predicates := [] }).exprs)) | return false
  let some E := ((«seal» (Reg.stack 32 64).bits (Term.C32 0x08070605) >>= fun stored => some (update ⟨E, []⟩ { exprs := [Expr.mkEq (.stack 32 64) stored], predicates := [] }).exprs)) | return false
  let (body, _) := renderSemStateJson ⟨E, []⟩
  for (id, kind, abi, tail) in [
      (1, HelperKind.lookup, [Term.C32 42, key], [Term.C32 4, Term.C32 5, Term.C32 6]),
      (3, HelperKind.delete, [Term.C32 42, key], [Term.C32 4, Term.C32 5, Term.C32 6]),
      (2, HelperKind.update, [Term.C32 42, key, value, Term.C32 0],
        [Term.C32 4, Term.C32 5, Term.C32 6, Term.C32 5, Term.C32 6])] do
    let state := (update ⟨E, []⟩ { exprs := [Expr.mkEq (Reg.real32 10) (solve (Term.C32 id))], predicates := [] }).exprs
    let (row, _) := renderSemStateJson ⟨state, []⟩
    let json := exportRv32ExpandStep #[0x000280e7, 0x00008067] 80 0 s!"[{row}]" "[]"
    if !json.contains "\"status\":\"ok\"" ||
        !json.contains (renderPredicateJson (.helper 80 kind (abi ++ tail))) ||
        !json.contains (renderExprJson (Expr.mkEq (Reg.real32 10)
          (star .w32 (.externalResult 80 0) (Term.C32 id :: abi)))) then return false
  let missingValue := addStar .w32 (Term.V32 0) (Term.C32 7)
  let state := (update ⟨E, []⟩ { exprs := [Expr.mkEq (Reg.real32 10) (solve (Term.C32 2))], predicates := [] }).exprs
    |> (fun acc => (update ⟨acc, []⟩ { exprs := [Expr.mkEq (Reg.real32 13) (solve missingValue)], predicates := [] }).exprs)
  let (row, _) := renderSemStateJson ⟨state, []⟩
  let json := exportRv32ExpandStep #[0x000280e7, 0x00008067] 80 0 s!"[{row}]" "[]"
  return !body.isEmpty && json.contains "\"status\":\"ok\"" &&
    json.contains (renderPredicateJson
      (.helper 80 .update [Term.C32 42, key, missingValue, Term.C32 0]))

#guard encodedOpenMCheck
#guard encodedHelperBuffersCheck

end RV32
