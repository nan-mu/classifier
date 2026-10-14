import RV32IMC.Initial
import RV32IMC.Expr
import RV32IMC.Helper
import RV32IMC.Encode
import RV32IMC.Esp32c3Program
import PathMerge.Budget
import ClassifierExpr.Render
import ClassifierExpr.Parse

namespace RV32IMC
open ClassifierExpr PathMerge

/-! Symbolic indirect targets reject. Map writes need a prior lookup with frozen key bytes
(Meta `maps` layout + stack `readStackBytes`) recorded on the helper Predicate. -/

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

private def emit (dir : Direction) (loc : Option Location) (Ei : ExprSet) : StepResult :=
  match loc with
  | some k => .candidates [⟨dir, k, Ei, []⟩]
  | none => .reject .unboundTarget

/-- Capture a0's complete pre-return term only after the wrapper Exit is recognized. -/
private def emitIndirect (loc : Option Location) (Eg Ei : ExprSet) : StepResult :=
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

private def emitComparison (dir : BranchDirection) (loc : Option Location) (Ei : ExprSet)
    (e : Expr) (position : Nat) (lhs : Term) : StepResult :=
  let direction := match dir with | .taken => Direction.taken | .notTaken => .notTaken
  match loc with
  | some k => .candidates [⟨direction, k, Ei.insertConstraint e,
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

/-- Recover map term + frozen key from Pg for the lookup that owns this Map address. -/
private def mapWriteObservation (Eg : ExprSet) (Pg : List Predicate) (maps : List MapLayout)
    (rs1 rs2 : regidx) (offset width : Nat) :
    Option (Term × List Term × Nat × Term) := do
  let (lookupEvent, elementOff, _) ← mapElementAccess Eg rs1 offset width
  let source ← readReg Eg rs2
  if source.width != .w32 then none
  else
    let p ← Pg.find? fun p => match p with
      | .helper e .lookup _ => e == lookupEvent
      | _ => false
    let (map, frozen) ← lookupFrozenKey p
    if frozen.isEmpty then none
    else
      let layout ← findMapLayout maps map
      if frozen.length != layout.keySize || elementOff + width > layout.valueSize then none
      else some (map, frozen, elementOff, solve source)

/-- Each successful store delta touches one resource category, selected by the value step.
MapWrite needs frozen lookup keys + Meta layout; PacketWrite needs a dynamic event. -/
private def emitStore (I : Array Insn) (j : Nat) (Eg Ei : ExprSet) (Pg : List Predicate)
    (maps : List MapLayout) (rs1 rs2 : regidx) (offset width : Nat)
    (event : Option NodeId) : StepResult :=
  match Ei.entries.head? with
  | some e =>
    match e.reg.kind with
    | RegKind.map =>
      match event, mapWriteObservation Eg Pg maps rs1 rs2 offset width, nextPosition I j with
      | some event, some (map, key, o, source), some loc =>
        .candidates [⟨.ok, loc, Ei, [.mapWrite event map key o source]⟩]
      | _, _, none => .reject .unboundTarget
      | _, _, _ => .reject .undefinedSrc
    | RegKind.packet =>
      match event, packetBinding Eg rs1 offset width, readReg Eg rs2, nextPosition I j with
      | some event, some access, some source, some loc =>
        .candidates [⟨.ok, loc, Ei,
          [.packetWrite event access.κ access.offset source]⟩]
      | _, _, _, none => .reject .unboundTarget
      | _, _, _, _ => .reject .undefinedSrc
    | _ => emit .ok (nextPosition I j) Ei
  | none => emit .ok (nextPosition I j) Ei

/-- Static layout/return bindings are captured by the Step closure, never stored in SemState.
PC is derived solely for the value call. Without a dynamic event, resource writes reject;
ordinary value, Branch, and Return callers need no event identity. -/
def rv32StepBound (I : Array Insn) (base returnAddr : Option Nat)
    (j : Nat) (σ : SemState) (boundCtx : Option Term := none)
    (event : Option NodeId := none) (maps : List MapLayout := []) : StepResult :=
  match I[j]? with
  | none => .reject .unboundTarget
  | some i =>
    if !guardEg σ.exprs then .reject .localReject
    else
      let offsets := programOffsets I
      let Eg := match base, offsets[j]? with
        | some b, some offset => σ.exprs.insertEq (Reg.real32 32) (Term.C32 (b + offset))
        | _, _ => σ.exprs
      if needsPC i && (readPC Eg).isNone then .reject .unboundTarget
      else
        match RV32IMC.step Eg i boundCtx with
        | none => .reject (valueRejection i)
        | some Ei =>
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
                match takenLoc, fallLoc with
                | some taken, some fall => .candidates [
                    ⟨.taken, taken, Ei.insertConstraint takenE,
                      [.branch (j + 1) .taken ⟨t1, rel, t2⟩]⟩,
                    ⟨.notTaken, fall, Ei.insertConstraint fallE,
                      [.branch (j + 1) .notTaken ⟨t1, rel.compl, t2⟩]⟩]
                | _, _ => .reject .unboundTarget
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
                match takenLoc, fallLoc with
                | some taken, some fall => .candidates [
                    ⟨.taken, taken, Ei.insertConstraint takenE,
                      [.branch (j + 1) .taken ⟨t1, rel, t2⟩]⟩,
                    ⟨.notTaken, fall, Ei.insertConstraint fallE,
                      [.branch (j + 1) .notTaken ⟨t1, rel.compl, t2⟩]⟩]
                | _, _ => .reject .unboundTarget
          | .STORE (imm, rs2, rs1, width) =>
            emitStore I j Eg Ei σ.predicates maps rs1 rs2 (immI32 imm) width event
          | .C_SW (imm, rs1, rs2) =>
            emitStore I j Eg Ei σ.predicates maps (creg2reg_idx rs1) (creg2reg_idx rs2)
              (imm.toNat <<< 2) 4 event
          | .C_SWSP (imm, rs2) =>
            emitStore I j Eg Ei σ.predicates maps sp rs2 (imm.toNat <<< 2) 4 event
          | _ => emit .ok (nextPosition I j) Ei

/-- Unbound adapter: sequential effects and relative RV32 direct targets work;
PC-dependent effects and indirect targets require rv32StepBound's static bindings. -/
def rv32Step (I : Array Insn) (j : Nat) (σ : SemState) : StepResult :=
  rv32StepBound I none none j σ none none []

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
  αCtx := 0
  -- The synthetic fixture first spills s0 at index 7: c.swsp s0,8(sp).
  -- Keep R_entry = {x8} minimal: x8 retains the concrete entry-position term,
  -- so this smoke run reaches index 25's LHU symbolic-offset block.
  -- Product create and boundProgram use the whole savedRegs set instead.
  rEntries := [Reg.real32 8]
}

/-- addi a0,zero,7; addi a0,a0,1; jalr zero,ra,0. -/
def smokeProgram : Array Insn := decodeProgram #[0x00700513, 0x00150513, 0x00008067]

private def initialEqCheck (E : ExprSet) (r : Reg) (expected : Term) : Bool :=
  match E.lookupEq r with
  | some actual => reprStr actual == reprStr (solve expected)
  | none => false

private def smokeE0RealCheck : Bool :=
  let p := smokeEntryParams
  match buildE0 p with
  | .error _ => false
  | .ok σ =>
    σ.exprs.keysUnique && σ.predicates.isEmpty && σ.exprs.entries.length == 14 &&
      (σ.exprs.entries.filter (fun e => e.reg.kind == .real)).length == 8 &&
      (buildEBase p).entries.length == 7 &&
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
    (buildECtx0 p).entries.length == 6 &&
      (σ.exprs.entries.filter (fun e => e.reg.kind == .context)).length == 6 &&
      initialEqCheck σ.exprs (Reg.ctx32 p.αCtx) p.tData &&
      initialEqCheck σ.exprs (Reg.ctx32 (p.αCtx + 1)) (addStar .w32 p.tData p.tLen) &&
      initialEqCheck σ.exprs (Reg.ctx32 (p.αCtx + 2)) (Term.C32 0) &&
      initialEqCheck σ.exprs (Reg.ctx32 (p.αCtx + 3)) (Term.C32 p.ιWifi) &&
      initialEqCheck σ.exprs (Reg.ctx32 (p.αCtx + 4)) (Term.C32 0) &&
      initialEqCheck σ.exprs (Reg.ctx32 (p.αCtx + 5)) (Term.C32 0)

private def smokeEntryFreshKeyCheck : Bool :=
  let p := { smokeEntryParams with rEntries := [Reg.real32 9] }
  match buildE0 p with
  | .error _ => false
  | .ok σ =>
    σ.exprs.keysUnique && σ.exprs.entries.length == 14 &&
      initialEqCheck σ.exprs (Reg.real32 9) p.tEntry &&
      (buildEBase p).entries.length == 7 &&
      (σ.exprs.lookupEq (Reg.real32 8)).isNone

private def smokeMultipleEntriesCheck : Bool :=
  let p := { smokeEntryParams with rEntries := [Reg.real32 8, Reg.real32 9] }
  match buildE0 p with
  | .error _ => false
  | .ok σ =>
    σ.exprs.keysUnique && σ.exprs.entries.length == 15 &&
      (σ.exprs.entries.filter (fun e => e.reg.kind == .real)).length == 9 &&
      p.rEntries.all (fun r => initialEqCheck σ.exprs r p.tEntry) &&
      (buildEBase p).entries.length == 7

private def smokeRaEntryCheck : Bool :=
  let p := { smokeEntryParams with rEntries := [Reg.real32 1] }
  match buildE0 p with
  | .error _ => false
  | .ok σ => σ.exprs.entries.length == 13 &&
      p.rEntries.all (fun r => initialEqCheck σ.exprs r p.tReturn) &&
      initialEqCheck σ.exprs (Reg.real32 6) p.tReturn

private def smokeEmptyEntriesCheck : Bool :=
  let p := { smokeEntryParams with rEntries := [] }
  match buildE0 p with
  | .error _ => false
  | .ok σ => σ.exprs.keysUnique && σ.exprs.entries.length == 13 &&
      (σ.exprs.entries.filter (fun e => e.reg.kind == .real)).length == 7 &&
      initialEqCheck σ.exprs (Reg.real32 1) p.tReturn

private def smokeMixedRaEntriesCheck : Bool :=
  let p := { smokeEntryParams with rEntries := [Reg.real32 1, Reg.real32 8, Reg.real32 9] }
  match buildE0 p with
  | .error _ => false
  | .ok σ => σ.exprs.keysUnique && σ.exprs.entries.length == 15 &&
      p.rEntries.all (fun r => initialEqCheck σ.exprs r
        (if r == Reg.real32 1 then p.tReturn else p.tEntry))

private def smokeConcreteDataEndCheck : Bool :=
  let p := { smokeEntryParams with tData := Term.C32 4096, tLen := Term.C32 64, αCtx := 100 }
  match buildE0 p with
  | .error _ => false
  | .ok σ => initialEqCheck σ.exprs (Reg.ctx32 100) (Term.C32 4096) &&
      initialEqCheck σ.exprs (Reg.ctx32 101) (Term.C32 4160) &&
      (σ.exprs.lookupEq (Reg.ctx32 0)).isNone

private def smokeInitialRootCheck : Bool :=
  match rv32Init smokeProgram smokeEntryParams 0 3 with
  | .error _ => false
  | .ok ws =>
    match ws.nodes[0]? with
    | none => false
    | some root => root.loc == .pos 0 && ws.nodes.size == 1 && ws.edges.isEmpty &&
        ws.work == [0] && ws.fuel == 3 && root.state.exprs.entries.length == 14 &&
        initialEqCheck root.state.exprs (Reg.ctx32 smokeEntryParams.αCtx) smokeEntryParams.tData

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
        g.nodes.any (fun n => PathMerge.isExit n.loc &&
          initialEqCheck n.state.exprs (Reg.real32 10) (Term.C32 8)) &&
        g.nodes.all (fun n => if PathMerge.isExit n.loc then
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
          !(g.nodes.any fun n => PathMerge.isExit n.loc)
      | _ => false

private def smokeEmptyPredicateMergeCheck : Bool :=
  match buildE0 smokeEntryParams with
  | .error _ => false
  | .ok σ =>
    match mergePredicate σ.predicates [], PathMerge.applyLocal σ ExprSet.empty [] with
    | .ok predicates, .ok unchanged =>
      predicates.isEmpty && unchanged.predicates.isEmpty &&
        reprStr unchanged.exprs == reprStr σ.exprs
    | _, _ => false

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
    match RV32IMC.step σ.exprs i with
    | some Ei => Ei.keysUnique && Ei.entries.length == 1 &&
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
      match RV32IMC.step σ.exprs i with
      | some Ei => Ei.entries.length == 1 && initialEqCheck Ei (Reg.real32 12) jt.2
      | none => false

private def contextLoadRejectionCheck : Bool :=
  match buildE0 smokeEntryParams with
  | .error _ => false
  | .ok σ =>
    let incomplete : ExprSet := { entries := (σ.exprs.entries.filter
      (fun e => e.reg != Reg.ctx32 (smokeEntryParams.αCtx + 5))) }
    let bad := [
      Insn.LOAD (2#12, .Regidx 10#5, .Regidx 12#5, false, 4),
      .LOAD (24#12, .Regidx 10#5, .Regidx 12#5, false, 4),
      .LOAD (4092#12, .Regidx 10#5, .Regidx 12#5, false, 4),
      .LOAD (0#12, .Regidx 28#5, .Regidx 12#5, false, 4),
      .LOAD (0#12, sp, .Regidx 12#5, false, 4),
      .LOAD (0#12, .Regidx 28#5, .Regidx 12#5, false, 1)]
    bad.all (fun i => (RV32IMC.step σ.exprs i).isNone) &&
      (exprLOAD incomplete (.Regidx 10#5) zreg 0).isNone &&
      match exprLOAD σ.exprs (.Regidx 10#5) zreg 0 with
      | some Ei => Ei.entries.isEmpty
      | none => false

private def contextShiftedBaseCheck : Bool :=
  let p := { smokeEntryParams with αCtx := 100 }
  match buildE0 p with
  | .error _ => false
  | .ok σ =>
    -- An isolated lower Context alpha is not a complete run; an alias shares the context term.
    let Eg := σ.exprs.insertEq (Reg.ctx32 1) (Term.C32 99)
      |>.insertEq (Reg.real32 15) p.tCtx
    match exprLOAD Eg (.Regidx 15#5) (.Regidx 12#5) 4 with
    | some Ei => Ei.entries.length == 1 &&
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
  let E := ExprSet.empty.insertEq (Reg.real32 1) lhs
    |>.insertEq (Reg.real32 2) rhs
  match rv32StepBound I none none 0 ⟨E, []⟩ with
  | .candidates [taken, fall] =>
    taken.dir == .taken && taken.loc == .pos 2 &&
      fall.dir == .notTaken && fall.loc == .pos 1 &&
      taken.E_k.entries.isEmpty && fall.E_k.entries.isEmpty &&
      taken.E_k.constraints == [Expr.mkRel (Reg.real32 1) .ltu rhs] &&
      fall.E_k.constraints == [Expr.mkRel (Reg.real32 1) .geu rhs] &&
      taken.P_k == [.branch 1 .taken ⟨lhs, .ltu, rhs⟩] &&
      fall.P_k == [.branch 1 .notTaken ⟨lhs, .geu, rhs⟩] &&
      match PathMerge.applyLocal (SemState.mk E []) taken.E_k taken.P_k with
      | .ok child =>
        match PathMerge.applyLocal child (ExprSet.empty.insertEq (Reg.real32 1) (Term.C32 0)) [] with
        | .ok overwritten => overwritten.exprs.constraints.isEmpty &&
            child.exprs.constraints == [Expr.mkRel (Reg.real32 1) .ltu rhs] &&
            child.exprs.lookupEq (Reg.real32 1) == some lhs &&
            overwritten.predicates == [.branch 1 .taken ⟨lhs, .ltu, rhs⟩] &&
            overwritten.exprs.lookupEq (Reg.real32 1) == some (Term.C32 0)
        | _ => false
      | _ => false
  | _ => false

/-- All six full-width branch operations use the required relation/complement. -/
private def symbolicBtypeRelationsCheck : Bool :=
  let lhs := Term.V32 101
  let rhs := Term.V32 102
  let E := ExprSet.empty.insertEq (Reg.real32 1) lhs
    |>.insertEq (Reg.real32 2) rhs
  let cases : List (bop × Rel) := [(.BEQ, .eq), (.BNE, .ne),
    (.BLT, .lts), (.BGE, .ges), (.BLTU, .ltu), (.BGEU, .geu)]
  cases.all fun (op, rel) =>
    let I := #[Insn.BTYPE (8#13, .Regidx 2#5, .Regidx 1#5, op),
      decodeInsnWord 0x00100513, decodeInsnWord 0x00008067]
    match rv32StepBound I none none 0 ⟨E, []⟩ with
    | .candidates [taken, fall] => taken.dir == .taken && fall.dir == .notTaken &&
        taken.E_k.constraints == [Expr.mkRel (Reg.real32 1) rel rhs] &&
        fall.E_k.constraints == [Expr.mkRel (Reg.real32 1) rel.compl rhs] &&
        taken.P_k == [.branch 1 .taken ⟨lhs, rel, rhs⟩] &&
        fall.P_k == [.branch 1 .notTaken ⟨lhs, rel.compl, rhs⟩] &&
        match PathMerge.applyLocal (SemState.mk E []) taken.E_k taken.P_k with
        | .ok child => child.exprs.lookupEq (Reg.real32 1) == some lhs && child.exprs.keysUnique
        | _ => false
    | _ => false

/-- Concrete evaluation retains just the feasible side and its comparison. -/
private def concreteBltuFeasibleSideCheck : Bool :=
  let I := decodeProgram #[0x0020e463, 0x00100513, 0x00008067]
  [(1, 2, Direction.taken, Location.pos 2, Rel.ltu),
   (2, 1, Direction.notTaken, Location.pos 1, Rel.geu),
   (2, 2, Direction.notTaken, Location.pos 1, Rel.geu)].all fun (a, b, dir, loc, rel) =>
    let E := ExprSet.empty.insertEq (Reg.real32 1) (Term.C32 a)
      |>.insertEq (Reg.real32 2) (Term.C32 b)
    match rv32StepBound I none none 0 ⟨E, []⟩ with
    | .candidates [c] => c.dir == dir && c.loc == loc &&
        c.E_k.constraints == [Expr.mkRel (Reg.real32 1) rel (Term.C32 b)] &&
        c.P_k == [.branch 1 (if dir == .taken then .taken else .notTaken)
          ⟨Term.C32 a, rel, Term.C32 b⟩]
    | _ => false

/-- A symbolic branch cannot bind to the middle of a full-width instruction. -/
private def symbolicBltuUnboundTargetCheck : Bool :=
  let I := #[Insn.BTYPE (2#13, .Regidx 2#5, .Regidx 1#5, .BLTU),
    decodeInsnWord 0x00008067]
  let E := ExprSet.empty.insertEq (Reg.real32 1) (Term.V32 101)
    |>.insertEq (Reg.real32 2) (Term.V32 102)
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
        root.state.exprs.entries.length == 14 &&
        initialEqCheck root.state.exprs (Reg.real32 10) p.tCtx &&
        branch.loc == .pos 4 &&
        initialEqCheck branch.state.exprs (Reg.real32 12) p.tData &&
        initialEqCheck branch.state.exprs (Reg.real32 11) (addStar .w32 p.tData p.tLen) &&
        initialEqCheck branch.state.exprs (Reg.real32 13) (addStar .w32 p.tData (Term.C32 14)) &&
        initialEqCheck branch.state.exprs (Reg.real32 10) (Term.C32 2) &&
        initialEqCheck branch.state.exprs (Reg.ctx32 p.αCtx) p.tData &&
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
          match next.nodes[9]?, stackSlot afterAdjust.state.exprs sp (uimm.toNat <<< 2),
              readReg afterAdjust.state.exprs rs2 with
          | some stored, some slot, some value =>
            stored.loc == .pos 7 && next.work == [9] &&
            next.nodes.size == ws.nodes.size + 1 && next.edges.size == ws.edges.size + 1 &&
            initialEqCheck stored.state.exprs slot (solve value) &&
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
  let σ : SemState := ⟨ExprSet.empty.insertEq (Reg.real32 11) ta
    |>.insertEq (Reg.real32 13) tb, []⟩
  [bop.BEQ, .BNE, .BLT, .BGE, .BLTU, .BGEU].all fun op =>
    let I := #[Insn.BTYPE (8#13, .Regidx 13#5, .Regidx 11#5, op),
      decodeInsnWord 0x00100513, decodeInsnWord 0x00008067]
    match rv32Step I 0 σ with
    | .candidates [a, b] =>
      a.dir == .taken && b.dir == .notTaken &&
      a.loc == .pos 2 && b.loc == .pos 1 &&
      a.E_k.entries.isEmpty && b.E_k.entries.isEmpty &&
      a.E_k.constraints == [Expr.mkRel (Reg.real32 11) (branchRel op) tb] &&
      b.E_k.constraints == [Expr.mkRel (Reg.real32 11) (branchRel op).compl tb] &&
      a.P_k == [.branch 1 .taken ⟨ta, branchRel op, tb⟩] &&
      b.P_k == [.branch 1 .notTaken ⟨ta, (branchRel op).compl, tb⟩]
    | _ => false

private def compressedBranchesCheck : Bool :=
  let σ : SemState := ⟨ExprSet.empty.insertEq (Reg.real32 8) (Term.V32 3), []⟩
  [0xc011, 0xe011].all fun word =>
    let I := decodeProgram #[UInt32.ofNat word, 0x0001, 0x0001]
    match rv32Step I 0 σ with
    | .candidates [a, b] => a.dir == .taken && b.dir == .notTaken &&
      a.loc == .pos 2 && b.loc == .pos 1 &&
      let rel := if word == 0xc011 then Rel.eq else Rel.ne
      a.E_k.constraints == [Expr.mkRel (Reg.real32 8) rel (Term.C32 0)] &&
      b.E_k.constraints == [Expr.mkRel (Reg.real32 8) rel.compl (Term.C32 0)] &&
      a.P_k == [.branch 1 .taken ⟨Term.V32 3, rel, Term.C32 0⟩] &&
      b.P_k == [.branch 1 .notTaken ⟨Term.V32 3, rel.compl, Term.C32 0⟩]
    | _ => false

#guard symbolicBranchesCheck
#guard compressedBranchesCheck
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
25 LHU has a symbolic packet offset and lacks a unique byte binding.
36 C.JAL has its link-value semantics, but target offset 104 - 616 = -512
is outside this image. External call/result contracts are required to reach 37–43;
we retain UnboundTarget rather than fabricate a helper result or fallthrough.
-/

/-- The data-dependent packet offset at position 25 lacks a unique byte binding.
The earlier return path succeeds; the queued external jump still has no target binding. -/
private def esp32c3DeepFrontierCheck : Bool :=
  let I := esp32c3Program
  let stepFn := rv32StepBound I (some 0x1000) (some 0x2000)
  match rv32Init I smokeEntryParams 0 512 with
  | .error _ => false
  | .ok ws0 => match expandN I.size stepFn ws0 38 with
    | .inl _ => false
    | .inr ws =>
      ws.nodes.size == 43 && ws.fuel == 474 && ws.work == [40, 41, 42] &&
      ws.nodes.any (fun n => n.loc == .exit && n.state.predicates.contains (.ret (Term.C32 2)) &&
        initialEqCheck n.state.exprs (Reg.real32 10) (Term.C32 2)) &&
      (match ws.nodes[40]?, expandOne I.size stepFn ws with
        | some blocked, .inl (.fail .undefinedSrc g) =>
          blocked.loc == .pos 25 && g.nodes.size == ws.nodes.size &&
          g.edges.size == ws.edges.size
        | _, _ => false) &&
      (match ws.nodes[41]? with
        | some blocked => blocked.loc == .pos 36 &&
          (match stepFn 36 blocked.state with
            | .reject .unboundTarget => true
            | _ => false)
        | _ => false)

private def helperObservationMergeCheck : Bool :=
  let p := Predicate.helper 8 .clock []
  let q := Predicate.helper 7 .clock []
  (match mergePredicate [q] [p, p, q] with
    | .ok ps => ps == [q, p]
    | _ => false) &&
  renderPredicateJson p == "{\"kind\":\"helper\",\"event\":8,\"helperId\":5,\"args\":[]}"

/-- C.JR and full JALR freeze the complete symbolic pre-return a0 on wrapper Exit. -/
private def boundReturnExprCheck : Bool :=
  let E := ExprSet.empty.insertEq (Reg.real32 1) (Term.C32 0x2000)
    |>.insertEq (Reg.real32 10) (Term.V32 123)
  [decodeProgram #[0x00008067], decodeProgram #[0x8082]].all (fun I =>
    match rv32StepBound I (some 0x1000) (some 0x2000) 0 ⟨E, []⟩ with
    | .candidates [c] => c.loc == .exit && c.P_k == [.ret (Term.V32 123)] &&
        initialEqCheck (updateExpr E c.E_k) (Reg.real32 10) (Term.V32 123)
    | _ => false) &&
  [decodeProgram #[0x00008067], decodeProgram #[0x8082]].all (fun I =>
    match rv32StepBound I (some 0x1000) (some 0x2000) 0
        ⟨ExprSet.empty.insertEq (Reg.real32 1) (Term.C32 0x2000), []⟩ with
    | .reject .undefinedSrc => true
    | _ => false) &&
  (match rv32StepBound (decodeProgram #[0x00008067]) (some 0x1000) (some 0x2002)
      0 ⟨E, []⟩ with
    | .reject .unboundTarget => true
    | _ => false) &&
  (match rv32StepBound (decodeProgram #[0x00008067, 0x0001])
      (some 0x1000) (some 0x2000) 0
      ⟨ExprSet.empty.insertEq (Reg.real32 1) (Term.C32 0x1004), []⟩ with
    | .candidates [c] => c.loc == .pos 1 && c.P_k.isEmpty
    | _ => false) &&
  (match rv32StepBound (decodeProgram #[0x00008067])
      (some 0x1000) (some 0x2000) 0
      ⟨ExprSet.empty.insertEq (Reg.real32 1) (Term.C32 0x2000)
        |>.insertConstraint (Expr.mkRel (Reg.real32 10) .eq (Term.V32 123)), []⟩ with
    | .reject .undefinedSrc => true
    | _ => false)

/-- Packet loads are repeatable symbolic Terms; unrelated/unbound bases reject. -/
private def packetLoadsCheck : Bool :=
  match buildE0 smokeEntryParams with
  | .error _ => false
  | .ok σ =>
    let E := σ.exprs.insertEq (Reg.real32 12) smokeEntryParams.tData
    [1, 2, 4].all (fun width =>
      [false, true].all fun unsigned =>
        let i := Insn.LOAD (12#12, .Regidx 12#5, .Regidx 14#5, unsigned, width)
        match step E i, step E i with
        | some a, some b => a.entries.length == width + 1 && a.keysUnique &&
          a.lookupEq (Reg.real32 14) == b.lookupEq (Reg.real32 14) &&
          (match a.lookupEq (Reg.real32 14) with
            | some t => (eval t).isNone
            | none => false)
        | _, _ => false) &&
    (exprPacketLOAD E sp (.Regidx 14#5) 0 1 true).isNone &&
    (exprPacketLOAD E (.Regidx 28#5) zreg 0 1 true).isNone &&
    (exprPacketLOAD E (.Regidx 12#5) zreg 0 3 true).isNone &&
    (match exprPacketLOAD E (.Regidx 12#5) zreg 0 1 true with
      | some Ei => Ei.entries.isEmpty
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

private def helperTarget (i : Insn) (pc : Nat) (Eg : ExprSet) : Option Nat :=
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

structure StepContext where
  imageBase : Option Nat := none
  returnAddress : Option Nat := none
  helperAddress : Option Nat := none
  boundContext : Option Term := none
  maps : List MapLayout := []
  deriving Inhabited, Repr

/-- One ISA step: inspect the instruction, generate its observations, then its local values.
Static bindings stay outside SemState; event identifies this dynamic source node. -/
def inferStep (I : Array Insn) (context : StepContext)
    (event : NodeId) (j : Nat) (σ : SemState) : StepResult :=
  let fallback := rv32StepBound I context.imageBase context.returnAddress j σ
    context.boundContext (some event) context.maps
  match I[j]?, (programOffsets I)[j]?, context.imageBase, context.helperAddress with
  | some i, some offset, some base, some helper =>
    if helperTarget i (base + offset) σ.exprs != some helper then fallback
    else if !guardEg σ.exprs then .reject .localReject
    else match nextPosition I j with
      | none => .reject .unboundTarget
      | some loc =>
        let Eg := σ.exprs.insertEq (Reg.real32 32) (Term.C32 (base + offset))
        match RV32IMC.step Eg i context.boundContext,
            helperPredicate event σ.exprs context.maps with
        | some link, .ok predicate =>
          match helperExpr predicate with
          | .error reason => .reject reason
          | .ok result =>
            let Ei := updateExpr link result
            .candidates [⟨.ok, loc, Ei, [predicate]⟩]
        | _, .error reason => .reject reason
        | none, _ => .reject .undefinedSrc
  | _, _, _, _ => fallback

/-- Ordinary and compressed stores emit one complete-source event and little-endian bytes.
The misaligned concrete SP case selects Packet rather than an aligned Stack word. -/
private def packetStoreObservationsCheck : Bool := Id.run do
  let p := { smokeEntryParams with tData := Term.C32 0x4000, tLen := Term.C32 64 }
  let .ok σ := buildE0 p | return false
  let value := Term.C32 0xaabbccdd
  let E := σ.exprs.insertEq (Reg.real32 12) p.tData
    |>.insertEq (Reg.real32 2) (Term.C32 0x4001)
    |>.insertEq (Reg.real32 11) value
    |>.insertEq (Reg.packet p.αCtx 20) (Term.C32 99)
  let cases : List (Insn × Nat × Nat) := [
    (.STORE (2#12, .Regidx 11#5, .Regidx 12#5, 1), 2, 1),
    (.STORE (2#12, .Regidx 11#5, .Regidx 12#5, 2), 2, 2),
    (.STORE (4#12, .Regidx 11#5, .Regidx 12#5, 4), 4, 4),
    (.C_SW (1#5, .Cregidx 4#3, .Cregidx 3#3), 4, 4),
    (.C_SWSP (1#6, .Regidx 11#5), 5, 4)]
  for (i, offset, bytes) in cases do
    let I := #[i, decodeInsnWord 0x0001]
    let .candidates [c] := inferStep I {} 77 0 ⟨E, []⟩ | return false
    if c.P_k != [.packetWrite 77 p.αCtx offset value] ||
        c.E_k.entries.length != bytes || c.loc != .pos 1 ||
        !c.E_k.entries.all (fun e => e.reg.kind == .packet) then return false
    for j in List.range bytes do
      if c.E_k.lookupEq (Reg.packet p.αCtx (offset + j)) !=
          some (Term.C32 ((0xaabbccdd >>> (8 * j)) &&& 0xff)) then return false
    let .ok child := PathMerge.applyLocal ⟨E, []⟩ c.E_k c.P_k | return false
    if child.exprs.lookupEq (Reg.packet p.αCtx 20) != some (Term.C32 99) then return false
    let .candidates [again] := inferStep I {} 78 0 child | return false
    let .ok repeated := PathMerge.applyLocal child again.E_k again.P_k | return false
    if repeated.predicates != [.packetWrite 77 p.αCtx offset value,
        .packetWrite 78 p.αCtx offset value] then return false
  let I := #[Insn.STORE (2#12, .Regidx 11#5, .Regidx 12#5, 2), decodeInsnWord 0x0001]
  let symbolic := Term.V32 900
  let symbolicE := E.insertEq (Reg.real32 11) symbolic
  let .candidates [c] := inferStep I {} 77 0 ⟨symbolicE, []⟩ | return false
  if c.P_k != [.packetWrite 77 p.αCtx 2 symbolic] ||
      c.E_k.lookupEq (Reg.packet p.αCtx 2) !=
        some (star .w32 (.extract 0 8 32) [symbolic]) ||
      c.E_k.lookupEq (Reg.packet p.αCtx 3) !=
        some (star .w32 (.extract 8 8 32) [symbolic]) then return false
  let .ok child := PathMerge.applyLocal ⟨symbolicE, []⟩ c.E_k c.P_k | return false
  let .ok overwritten := PathMerge.applyLocal child
    (ExprSet.empty.insertEq (Reg.real32 11) (Term.C32 0)) [] | return false
  if overwritten.predicates != [.packetWrite 77 p.αCtx 2 symbolic] then return false
  let zeroI := #[Insn.STORE (0#12, zreg, .Regidx 12#5, 1), decodeInsnWord 0x0001]
  let .candidates [zero] := inferStep zeroI {} 79 0 ⟨E, []⟩ | return false
  return zero.P_k == [.packetWrite 79 p.αCtx 0 (Term.C32 0)] &&
    zero.E_k.lookupEq (Reg.packet p.αCtx 0) == some (Term.C32 0)

private def packetStoreRejectsMissingInputsCheck : Bool := Id.run do
  let .ok σ := buildE0 smokeEntryParams | return false
  let E := σ.exprs.insertEq (Reg.real32 12) smokeEntryParams.tData
    |>.insertEq (Reg.real32 11) (Term.C32 7)
  let store := Insn.STORE (0#12, .Regidx 11#5, .Regidx 12#5, 4)
  let I := #[store, decodeInsnWord 0x0001]
  let missing : ExprSet := { entries := E.entries.filter (fun e => e.reg != Reg.real32 11) }
  let results := [rv32StepBound I none none 0 ⟨E, []⟩,
    inferStep I {} 77 0 ⟨missing, []⟩,
    inferStep #[Insn.STORE (0#12, .Regidx 11#5, .Regidx 28#5, 4),
      decodeInsnWord 0x0001] {} 77 0 ⟨E, []⟩]
  return results.all fun result =>
    match result with | .reject .undefinedSrc => true | _ => false

/-- Without frozen keys / Meta layout, Map stores still reject after local Expr succeeds. -/
private def mapStoreObservationGapCheck : Bool :=
  let pointer := star .w32 (.externalResult 9 0) [Term.C32 1, Term.C32 42, Term.V32 0]
  let E := ExprSet.empty.insertEq (Reg.real32 8) pointer
    |>.insertEq (Reg.real32 11) (Term.C32 0xaabbccdd)
    |>.insertEq (Reg.real32 2) pointer
    |>.insertEq (Reg.mapWord 9 0) (Term.C32 0)
  let stores := [1, 2, 4].map (fun width =>
    Insn.STORE (0#12, .Regidx 11#5, .Regidx 8#5, width)) ++
    [.C_SW (0#5, .Cregidx 0#3, .Cregidx 3#3), .C_SWSP (0#6, .Regidx 11#5)]
  stores.all fun i =>
    (step E i).isSome &&
      match inferStep #[i, decodeInsnWord 0x0001] {} 77 0 ⟨E, []⟩ with
      | .reject .undefinedSrc => true
      | _ => false

/-- Frozen lookup key + Meta layout authorize MapWrite on SB/SH/SW (and keep prior observations). -/
private def mapStoreObservationsCheck : Bool := Id.run do
  let pointer := star .w32 (.externalResult 9 0) [Term.C32 1, Term.C32 42, Term.V32 0]
  let key := [Term.C32 1, Term.C32 2, Term.C32 3, Term.C32 4]
  let lookup : Predicate := .helper 9 .lookup ([Term.C32 42, Term.V32 0] ++ key)
  let E := ExprSet.empty.insertEq (Reg.real32 8) pointer
    |>.insertEq (Reg.real32 11) (Term.C32 0xaabbccdd)
    |>.insertEq (Reg.mapWord 9 0) (Term.C32 0)
  let maps : List MapLayout := [{ mapId := 42, keySize := 4, valueSize := 16 }]
  let ctx : StepContext := { maps }
  let stores : List (Insn × Nat) := [
    (.STORE (0#12, .Regidx 11#5, .Regidx 8#5, 1), 1),
    (.STORE (0#12, .Regidx 11#5, .Regidx 8#5, 2), 2),
    (.STORE (0#12, .Regidx 11#5, .Regidx 8#5, 4), 4),
    (.C_SW (0#5, .Cregidx 0#3, .Cregidx 3#3), 4)]
  for (i, width) in stores do
    let I := #[i, decodeInsnWord 0x0001]
    let .candidates [c] := inferStep I ctx 77 0 ⟨E, [lookup]⟩ | return false
    let want := .mapWrite 77 (Term.C32 42) key 0 (Term.C32 0xaabbccdd)
    if c.P_k != [want] || c.loc != .pos 1 then return false
    let .ok child := PathMerge.applyLocal ⟨E, [lookup]⟩ c.E_k c.P_k | return false
    if !child.predicates.contains lookup || !child.predicates.contains want then return false
    if width == 0 then return false
  let .candidates [again] := inferStep #[Insn.STORE (0#12, .Regidx 11#5, .Regidx 8#5, 4),
      decodeInsnWord 0x0001] ctx 78 0
      ⟨E, [lookup, .mapWrite 77 (Term.C32 42) key 0 (Term.C32 0xaabbccdd)]⟩ | return false
  let .ok kept := PathMerge.applyLocal
      ⟨E, [lookup, .mapWrite 77 (Term.C32 42) key 0 (Term.C32 0xaabbccdd)]⟩
      again.E_k again.P_k | return false
  return kept.predicates.contains (.mapWrite 77 (Term.C32 42) key 0 (Term.C32 0xaabbccdd)) &&
    kept.predicates.contains (.mapWrite 78 (Term.C32 42) key 0 (Term.C32 0xaabbccdd))

/-- The skipped sequential instruction makes source node identity differ from instruction index. -/
private def packetSnapshotEventCheck : Bool :=
  let I := #[Insn.LOAD (0#12, .Regidx 10#5, .Regidx 12#5, true, 4),
    Insn.BTYPE (8#13, zreg, zreg, .BEQ),
    Insn.ITYPE (0#12, zreg, zreg, .ADDI),
    Insn.STORE (0#12, zreg, .Regidx 12#5, 1),
    decodeInsnWord 0x00008067]
  let json := rv32Snapshot I smokeEntryParams 0 3 5
  json.contains (renderPredicateJson (.packetWrite 2 smokeEntryParams.αCtx 0 (Term.C32 0))) &&
    !(json.contains (renderPredicateJson (.packetWrite 3 smokeEntryParams.αCtx 0 (Term.C32 0))))

#guard packetStoreObservationsCheck
#guard packetStoreRejectsMissingInputsCheck
#guard mapStoreObservationGapCheck
#guard mapStoreObservationsCheck
#guard packetSnapshotEventCheck

/-- Static program bindings outside SemState / Predicate.
Extend fields here (and in Meta JSON); do not grow create/step FFI arity.
`helperAddress` is the ELF dispatcher binding, not a `Predicate.helper`. -/
structure Meta where
  base : UInt32
  helperAddress : UInt32
  returnAddress : UInt32 := 0x2000
  maps : List MapLayout := []
  deriving Inhabited, Repr

private def parseMetaU32 (j : Lean.Json) (key : String) : Option UInt32 := do
  let n ← (j.getObjVal? key >>= Lean.Json.getNat?).toOption
  if n ≥ (1 <<< 32) then none else some n.toUInt32

private def parseMapLayout (value : Lean.Json) : Option MapLayout := do
  let mapId ← (value.getObjVal? "mapId" >>= Lean.Json.getNat?).toOption
  let keySize ← (value.getObjVal? "keySize" >>= Lean.Json.getNat?).toOption
  let valueSize ← (value.getObjVal? "valueSize" >>= Lean.Json.getNat?).toOption
  if keySize > 64 || valueSize == 0 || valueSize > 4096 then none
  else some { mapId, keySize, valueSize }

private def parseMetaJson (s : String) : Option Meta := do
  let j ← (Lean.Json.parse s).toOption
  let base ← parseMetaU32 j "base"
  let helperAddress ← parseMetaU32 j "helperAddress"
  let returnAddress := (parseMetaU32 j "returnAddress").getD 0x2000
  let maps ← match j.getObjVal? "maps" with
    | .error _ => some []
    | .ok arr => do
      let rows ← arr.getArr?.toOption
      rows.toList.mapM parseMapLayout
  some { base, helperAddress, returnAddress, maps }

private def boundProgram (insns : Array UInt32) (m : Meta) :
    Except RejectReason (Array Insn × EntryParams × StepContext) :=
  let I := decodeProgram insns
  let b := m.base.toNat
  let h := m.helperAddress.toNat
  let ret := m.returnAddress.toNat
  let extent := I.foldl (fun n i => n + insnLength i) 0
  let p := { smokeEntryParams with
    tEntry := Term.C32 b, tReturn := Term.C32 ret, rEntries := savedRegs }
  let context : StepContext := {
    imageBase := some b
    returnAddress := some ret
    helperAddress := some h
    boundContext := some p.tCtx
    maps := m.maps
  }
  if I.isEmpty || b == 0 || b % 4 != 0 || h == 0 || h % 4 != 0 ||
      ret == 0 || ret % 4 != 0 ||
      b + extent > (1 <<< 32) || h == ret ||
      (b ≤ ret && ret < b + extent) || (b ≤ h && h < b + extent) then
    .error .invalidEntry
  else .ok (I, p, context)

private def withMeta (metaJson : String)
    (k : Meta → String) : String :=
  match parseMetaJson metaJson with
  | none => snapshotJson #[] #[] [] 0 "fail" (some .invalidEntry)
  | some m => k m

/-- Meta-only checks (alignment / collisions among bindings). Program extent needs `insns` on step. -/
private def validateMeta (m : Meta) : Except RejectReason Unit :=
  let b := m.base.toNat
  let h := m.helperAddress.toNat
  let ret := m.returnAddress.toNat
  if b == 0 || b % 4 != 0 || h == 0 || h % 4 != 0 ||
      ret == 0 || ret % 4 != 0 || h == ret || b == ret || b == h then
    .error .invalidEntry
  else .ok ()

private def entryParamsOf (m : Meta) : EntryParams :=
  { smokeEntryParams with
    tEntry := Term.C32 m.base.toNat, tReturn := Term.C32 m.returnAddress.toNat,
    rEntries := savedRegs }

/-- Fail create without a fuel field (budget is Rust-owned). -/
private def createFailJson (reason : RejectReason) : String :=
  s!"\{\"status\":\"fail\",\"reason\":\"{reasonTag reason}\",\"failed\":null,\"work\":[],\"nodes\":[],\"edges\":[]}"

/-- Entry SemState + root. No fuel — Rust binding owns the expansion budget. -/
@[export lean_rv32_expand_create]
def exportRv32ExpandCreate (metaJson : String) : String :=
  withMeta metaJson fun m =>
    match validateMeta m with
    | .error reason => createFailJson reason
    | .ok () =>
      match entrySemState (entryParamsOf m) with
      | .error reason => createFailJson reason
      | .ok σ0 =>
        let (ej, pj) := renderSemStateJson σ0
        s!"\{\"status\":\"running\",\"reason\":null,\"failed\":null,\"work\":[0],\"nodes\":[\{\"id\":0,\"loc\":\"0\",\"exprs\":[{ej}],\"predicates\":[{pj}]}],\"edges\":[]}"

private def headFailJson (reason : RejectReason) : String :=
  s!"\{\"status\":\"fail\",\"reason\":\"{reasonTag reason}\",\"successors\":[]}"

private def successorJson (row : Direction × Location × SemState) : String :=
  let (dir, loc, state) := row
  let loc := match loc with | .exit => "exit" | .pos j => toString j
  let (exprs, preds) := renderSemStateJson state
  s!"\{\"dir\":\"{dirTag dir}\",\"loc\":\"{loc}\",\"exprs\":[{exprs}],\"predicates\":[{preds}]}"

/-- Stateless head inference: program + Meta + head SemState → successors or reject.
Fuel / work-queue updates are Rust-only. -/
@[export lean_rv32_expand_step]
def exportRv32ExpandStep
    (insns : Array UInt32) (metaJson : String) (event j : UInt32)
    (exprsJson predsJson : String) : String :=
  match parseMetaJson metaJson with
  | none => headFailJson .invalidEntry
  | some m =>
    match boundProgram insns m with
    | .error reason => headFailJson reason
    | .ok (I, _, context) =>
      match parseSemStateJson exprsJson predsJson with
      | none => headFailJson .localReject
      | some state =>
        match inferStep I context event.toNat j.toNat state with
        | .reject reason => headFailJson reason
        | .candidates cs =>
          match prepareAll state I.size cs with
          | .error reason => headFailJson reason
          | .ok prepared =>
            let successors := String.intercalate "," (prepared.map successorJson)
            s!"\{\"status\":\"ok\",\"reason\":null,\"successors\":[{successors}]}"

@[export lean_rv32_expand_bound_words_snapshot]
def exportRv32BoundWordsSnapshot
    (insns : Array UInt32) (metaJson : String) (steps budget : UInt32) : String :=
  withMeta metaJson fun m =>
    match boundProgram insns m with
    | .error reason => snapshotJson #[] #[] [] 0 "fail" (some reason)
    | .ok (I, p, context) =>
      match rv32Init I p 0 budget.toNat with
      | .error reason => snapshotJson #[] #[] [] 0 "fail" (some reason)
      | .ok ws => snapshotAfter I.size (inferStep I context) ws steps.toNat

private def testMeta (base helperAddress : UInt32) : String :=
  s!"\{\"base\":{base},\"helperAddress\":{helperAddress}}"

private def statelessStepCheck : Bool :=
  let insns := #[0x00700513, 0x00150513, 0x00008067]
  let metaJson := testMeta 0x400 0x100
  match parseMetaJson metaJson, boundProgram insns { base := 0x400, helperAddress := 0x100 } with
  | some _, .ok (I, p, context) =>
    match rv32Init I p 0 3 with
    | .error _ => false
    | .ok ws =>
      let state := ws.nodes[0]!.state
      let (exprs, preds) := renderSemStateJson state
      (match expandOne I.size (inferStep I context 0) ws with
       | .inr next => exportRv32ExpandStep insns metaJson 0 0
           s!"[{exprs}]" s!"[{preds}]" ==
           s!"\{\"status\":\"ok\",\"reason\":null,\"successors\":[{successorJson (.ok, next.nodes[1]!.loc, next.nodes[1]!.state)}]}"
       | _ => false) &&
      p.rEntries == savedRegs &&
      (entryParamsOf { base := 0x400, helperAddress := 0x100 }).rEntries == savedRegs &&
      state.exprs.keysUnique && state.exprs.entries.length == 25 &&
      (state.exprs.entries.filter (fun e => e.reg.kind == .real)).length == 19 &&
      savedRegs.all (fun r => initialEqCheck state.exprs r p.tEntry) &&
      exportRv32ExpandStep #[] metaJson 0 0 "[]" "[]" ==
        headFailJson .invalidEntry &&
      !(exportRv32ExpandCreate metaJson).contains "\"fuel\":" &&
      (exportRv32ExpandCreate metaJson).contains "\"status\":\"running\""
  | _, _ => false

#guard statelessStepCheck

end RV32IMC
