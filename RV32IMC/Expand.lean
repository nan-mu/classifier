import RV32IMC.Initial
import RV32IMC.Expr
import RV32IMC.Helper
import RV32IMC.Encode
import RV32IMC.Esp32c3Program
import CommonMath.Expand
import CommonMath.Render

namespace RV32IMC
open CommonMath

/-! MVP gaps: symbolic indirect targets reject; resource Predicates remain undefined. -/

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

/-- Observe a0 only on a successfully bound Exit, from the post-instruction state. -/
private def emitIndirect (loc : Option Location) (Eg Ei : ExprSet) : StepResult :=
  match loc with
  | some .exit =>
    match (updateExpr Eg Ei).lookupEq (Reg.real32 10) with
    | some t => .candidates [⟨.only, .exit, Ei, [.ret (solve t)]⟩]
    | none => .reject .undefinedSrc
  | _ => emit .only loc Ei

private def branchHolds (op : bop) (a b : Nat) : Bool :=
  let a := MNat 32 a
  let b := MNat 32 b
  match op with
  | .BEQ => a == b
  | .BNE => a != b
  | .BLT => s 32 a < s 32 b
  | .BGE => s 32 a ≥ s 32 b
  | .BLTU => a < b
  | .BGEU => a ≥ b

private def branchRel : bop → Rel
  | .BEQ => .eq
  | .BNE => .ne
  | .BLT => .lts
  | .BGE => .ges
  | .BLTU => .ltu
  | .BGEU => .geu

private def emitCmp (dir : Direction) (loc : Option Location) (Ei : ExprSet)
    (p : Predicate) : StepResult :=
  match loc with
  | some k => .candidates [⟨dir, k, Ei, [p]⟩]
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
  | .LOAD _ | .STORE (_, _, _, 4)
  | .C_LW _ | .C_SW _ | .C_LWSP _ | .C_SWSP _ => .undefinedSrc
  | .STORE _
  | .ECALL _ | .EBREAK _ | .MRET _ | .SRET _ | .WFI _ | .SFENCE_VMA _
  | .C_EBREAK _ => .unsupported
  | _ => .undefinedSrc

/-- Static layout/return bindings are captured by the Step closure, never stored in SemState.
PC is derived from the layout solely for the value call; Candidates contain only its Ei. -/
def rv32StepBound (I : Array Insn) (base returnAddr : Option Nat)
    (j : Nat) (σ : SemState) (boundCtx : Option Term := none) : StepResult :=
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
          | .JAL (imm, _) => emit .only (directTarget offsets j (s 21 imm.toNat)) Ei
          | .BTYPE (imm, rs2, rs1, op) =>
            match readReg Eg rs1, readReg Eg rs2 with
            | some ta, some tb =>
              let t1 := solve ta
              let t2 := solve tb
              let rel := branchRel op
              let takenLoc := directTarget offsets j (s 13 imm.toNat)
              let fallLoc := nextPosition I j
              let takenP := Predicate.cmp rel t1 t2
              let fallP := Predicate.cmp rel.compl t1 t2
              match eval t1, eval t2 with
              | some a, some b =>
                if branchHolds op a b then emitCmp .taken takenLoc Ei takenP
                else emitCmp .notTaken fallLoc Ei fallP
              | _, _ =>
                match takenLoc, fallLoc with
                | some taken, some fall => .candidates [
                    ⟨.taken, taken, Ei, [takenP]⟩,
                    ⟨.notTaken, fall, Ei, [fallP]⟩]
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
            emit .only (directTarget offsets j (2 * s 11 imm.toNat)) Ei
          | .C_BEQZ (imm, rs1) | .C_BNEZ (imm, rs1) =>
            match readReg Eg (creg2reg_idx rs1) with
            | none => .reject .undefinedSrc
            | some ta =>
              let op := match i with | .C_BEQZ _ => bop.BEQ | _ => bop.BNE
              let t1 := solve ta
              let t2 := Term.C32 0
              let rel := branchRel op
              let takenP := Predicate.cmp rel t1 t2
              let fallP := Predicate.cmp rel.compl t1 t2
              let takenLoc := directTarget offsets j (2 * s 8 imm.toNat)
              let fallLoc := nextPosition I j
              match eval t1 with
              | some a =>
                if branchHolds op a 0 then emitCmp .taken takenLoc Ei takenP
                else emitCmp .notTaken fallLoc Ei fallP
              | none =>
                match takenLoc, fallLoc with
                | some taken, some fall => .candidates [
                    ⟨.taken, taken, Ei, [takenP]⟩,
                    ⟨.notTaken, fall, Ei, [fallP]⟩]
                | _, _ => .reject .unboundTarget
          | _ => emit .only (nextPosition I j) Ei

/-- Unbound adapter: sequential effects and relative RV32 direct targets work;
PC-dependent effects and indirect targets require rv32StepBound's static bindings. -/
def rv32Step (I : Array Insn) (j : Nat) (σ : SemState) : StepResult :=
  rv32StepBound I none none j σ

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

private def reasonTag : RejectReason → String
  | .invalidEntry => "InvalidEntry"
  | .limitExceeded => "LimitExceeded"
  | .unsupported => "Unsupported"
  | .unboundTarget => "UnboundTarget"
  | .undefinedSrc => "UndefinedSrc"
  | .localReject => "LocalReject"

private def dirTag : Direction → String
  | .only => "Only"
  | .taken => "Taken"
  | .notTaken => "NotTaken"

private def snapshotJson (nodes : Array Node) (edges : Array Edge) (work : List NodeId)
    (fuel : Nat) (status : String) (reason : Option RejectReason) : String :=
  let nodeStrs := Id.run do
    let mut acc : List String := []
    for id in [:nodes.size] do
      if let some n := nodes[id]? then
        let (ej, pj) := renderSemStateJson n.state
        let loc := match n.loc with | .exit => "exit" | .pos j => toString j
        acc := acc ++
          [s!"\{\"id\":{id},\"loc\":\"{loc}\",\"exprs\":[{ej}],\"predicates\":[{pj}]}"]
    pure (String.intercalate "," acc)
  let edgeStrs := String.intercalate "," (edges.toList.map fun e =>
    s!"\{\"src\":{e.src},\"dir\":\"{dirTag e.dir}\",\"dst\":{e.dst}}")
  let workStr := String.intercalate "," (work.map toString)
  let reasonField := match reason with
    | none => "null"
    | some r => s!"\"{reasonTag r}\""
  s!"\{\"status\":\"{status}\",\"reason\":{reasonField},\"fuel\":{fuel},\"work\":[{workStr}],\"nodes\":[{nodeStrs}],\"edges\":[{edgeStrs}]}"

private def snapshotAfter (progLen : Nat) (stepFn : NodeId → Nat → SemState → StepResult)
    (ws : WorkState) : Nat → String
  | 0 => snapshotJson ws.nodes ws.edges ws.work ws.fuel
      (if ws.work.isEmpty then "complete" else "running") none
  | n + 1 =>
    match expandOne progLen (stepFn (ws.work.headD 0)) ws with
    | .inr ws' => snapshotAfter progLen stepFn ws' n
    | .inl (.complete g) => snapshotJson g.nodes g.edges [] ws.fuel "complete" none
    | .inl (.fail reason g) =>
      -- expandOne's terminal result has only a graph; retain diagnostic queue/fuel here.
      let attempted := !ws.work.isEmpty && ws.fuel > 0
      snapshotJson g.nodes g.edges (if attempted then ws.work.tail else ws.work)
        (if attempted then ws.fuel - 1 else ws.fuel) "fail" (some reason)

/-- JSON after at most steps expandOne calls; all node Exprs are global pre-execution snapshots.
The caller binds the contiguous instruction layout and wrapper label via EntryParams. -/
def rv32Snapshot (I : Array Insn) (p : EntryParams) (j0 steps budget : Nat) : String :=
  match rv32Init I p j0 budget with
  | .error reason => snapshotJson #[] #[] [] 0 "fail" (some reason)
  | .ok ws => snapshotAfter I.size
      (fun _ => rv32StepBound I (entryBase I p j0) (const32? p.tReturn)) ws steps

/-- One instruction per word, with compressed encodings in the low halfword. -/
def decodeInsnWord (w : UInt32) : Insn :=
  let n := w.toNat
  if n &&& 3 != 3 then encodeCompressed (BitVec.ofNat 16 (n &&& 0xffff))
  else encode (BitVec.ofNat 32 n)

/-- Decode mixed 16/32-bit instruction arrays without changing their sequence indices. -/
def decodeProgram (words : Array UInt32) : Array Insn :=
  words.map decodeInsnWord

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
  tGp := Term.V32 EntryVar.gp
  tTp := Term.V32 EntryVar.tp
  rEntry := Reg.real32 11
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
    σ.exprs.keysUnique && σ.predicates.isEmpty && σ.exprs.entries.length == 28 &&
      (σ.exprs.entries.filter (fun e => e.reg.kind == .real)).length == 22 &&
      (buildEBase p).entries.length == 21 &&
      initialEqCheck σ.exprs (Reg.real32 0) (Term.C32 0) &&
      initialEqCheck σ.exprs (Reg.real32 2) p.tSp &&
      initialEqCheck σ.exprs (Reg.real32 5) p.tSp &&
      initialEqCheck σ.exprs (Reg.real32 1) p.tReturn &&
      initialEqCheck σ.exprs (Reg.real32 6) p.tReturn &&
      initialEqCheck σ.exprs (Reg.real32 10) p.tCtx &&
      initialEqCheck σ.exprs p.rEntry p.tEntry &&
      (σ.exprs.lookupEq (Reg.real32 32)).isNone

private def smokeE0CtxCheck : Bool :=
  let p := smokeEntryParams
  match buildE0 p with
  | .error _ => false
  | .ok σ =>
    (buildECtx0 p).entries.length == 6 &&
      (σ.exprs.entries.filter (fun e => e.reg.kind == .stack)).length == 6 &&
      initialEqCheck σ.exprs (Reg.sw p.αCtx) p.tData &&
      initialEqCheck σ.exprs (Reg.sw (p.αCtx + 1)) (addStar .w32 p.tData p.tLen) &&
      initialEqCheck σ.exprs (Reg.sw (p.αCtx + 2)) (Term.C32 0) &&
      initialEqCheck σ.exprs (Reg.sw (p.αCtx + 3)) (Term.C32 p.ιWifi) &&
      initialEqCheck σ.exprs (Reg.sw (p.αCtx + 4)) (Term.C32 0) &&
      initialEqCheck σ.exprs (Reg.sw (p.αCtx + 5)) (Term.C32 0)

private def smokeEntryOverwriteCheck : Bool :=
  let p := { smokeEntryParams with rEntry := Reg.real32 8 }
  match buildE0 p with
  | .error _ => false
  | .ok σ =>
    σ.exprs.keysUnique && σ.exprs.entries.length == 27 &&
      initialEqCheck (buildEBase p) p.rEntry (Term.V32 (p.savedVar 8)) &&
      initialEqCheck σ.exprs p.rEntry p.tEntry &&
      initialEqCheck σ.exprs (Reg.real32 9) (Term.V32 (p.savedVar 9))

private def smokeRaEntryCheck : Bool :=
  let p := { smokeEntryParams with rEntry := Reg.real32 1 }
  match buildE0 p with
  | .error _ => false
  | .ok σ => σ.exprs.entries.length == 27 &&
      initialEqCheck σ.exprs p.rEntry p.tReturn &&
      initialEqCheck σ.exprs (Reg.real32 6) p.tReturn

private def smokeConcreteDataEndCheck : Bool :=
  let p := { smokeEntryParams with tData := Term.C32 4096, tLen := Term.C32 64, αCtx := 100 }
  match buildE0 p with
  | .error _ => false
  | .ok σ => initialEqCheck σ.exprs (Reg.sw 100) (Term.C32 4096) &&
      initialEqCheck σ.exprs (Reg.sw 101) (Term.C32 4160) &&
      (σ.exprs.lookupEq (Reg.sw 0)).isNone

private def smokeInitialRootCheck : Bool :=
  match rv32Init smokeProgram smokeEntryParams 0 3 with
  | .error _ => false
  | .ok ws =>
    match ws.nodes[0]? with
    | none => false
    | some root => root.loc == .pos 0 && ws.nodes.size == 1 && ws.edges.isEmpty &&
        ws.work == [0] && ws.fuel == 3 && root.state.exprs.entries.length == 28 &&
        initialEqCheck root.state.exprs (Reg.sw smokeEntryParams.αCtx) smokeEntryParams.tData

private def smokeInvalidEntryCheck : Bool :=
  [{ smokeEntryParams with rEntry := Reg.real32 32 },
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
        g.nodes.any (fun n => n.loc.isExit &&
          initialEqCheck n.state.exprs (Reg.real32 10) (Term.C32 8)) &&
        g.nodes.all (fun n => n.state.predicates ==
          (if n.loc.isExit then [.ret (Term.C32 8)] else []))
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
          !(g.nodes.any fun n => n.loc.isExit)
      | _ => false

private def smokeEmptyPredicateMergeCheck : Bool :=
  match buildE0 smokeEntryParams with
  | .error _ => false
  | .ok σ =>
    match mergePredicate σ.predicates [], σ.applyLocal ExprSet.empty [] with
    | .ok predicates, .ok unchanged =>
      predicates.isEmpty && unchanged.predicates.isEmpty &&
        reprStr unchanged.exprs == reprStr σ.exprs
    | _, _ => false

#guard smokeE0RealCheck
#guard smokeE0CtxCheck
#guard smokeEntryOverwriteCheck
#guard smokeRaEntryCheck
#guard smokeConcreteDataEndCheck
#guard smokeInitialRootCheck
#guard smokeInvalidEntryCheck
#guard smokeCompleteExitCheck
#guard smokeRejectsWithoutExitCheck
#guard smokeEmptyPredicateMergeCheck
#guard CommonMath.demoCheck

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
    let incomplete : ExprSet := ⟨σ.exprs.entries.filter
      (fun e => e.reg != Reg.sw (smokeEntryParams.αCtx + 5))⟩
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
    -- An isolated lower stack alpha is not a context run; an alias can share the context term.
    let Eg := σ.exprs.insertEq (Reg.sw 1) (Term.C32 99)
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
      taken.exprs.entries.isEmpty && fall.exprs.entries.isEmpty &&
      taken.predicates == [.cmp .ltu lhs rhs] &&
      fall.predicates == [.cmp .geu lhs rhs] &&
      match (SemState.mk E []).applyLocal taken.exprs taken.predicates with
      | .ok child =>
        -- A later register overwrite leaves the captured comparison unchanged.
        match child.applyLocal (ExprSet.empty.insertEq (Reg.real32 1) (Term.C32 0)) [] with
        | .ok overwritten => overwritten.predicates == [.cmp .ltu lhs rhs]
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
        taken.predicates == [.cmp rel lhs rhs] &&
        fall.predicates == [.cmp rel.compl lhs rhs]
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
        c.predicates == [.cmp rel (Term.C32 a) (Term.C32 b)]
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
        root.state.exprs.entries.length == 28 &&
        initialEqCheck root.state.exprs (Reg.real32 10) p.tCtx &&
        branch.loc == .pos 4 &&
        initialEqCheck branch.state.exprs (Reg.real32 12) p.tData &&
        initialEqCheck branch.state.exprs (Reg.real32 11) (addStar .w32 p.tData p.tLen) &&
        initialEqCheck branch.state.exprs (Reg.real32 13) (addStar .w32 p.tData (Term.C32 14)) &&
        initialEqCheck branch.state.exprs (Reg.real32 10) (Term.C32 2) &&
        initialEqCheck branch.state.exprs (Reg.sw p.αCtx) p.tData &&
        (branch.state.exprs.lookupEq (Reg.real32 32)).isNone &&
        ws.nodes.size == 8 && ws.edges.size == 7 && ws.work == [6] && ws.fuel == 42 &&
        taken.loc == .pos 47 && fall.loc == .pos 5 && returned.loc == .exit &&
        (programOffsets esp32c3Program)[47]? == some 126 &&
        taken.state.predicates == [.cmp .ltu
          (solve (addStar .w32 p.tData p.tLen))
          (solve (addStar .w32 p.tData (Term.C32 14)))] &&
        fall.state.predicates == [.cmp .geu
          (solve (addStar .w32 p.tData p.tLen))
          (solve (addStar .w32 p.tData (Term.C32 14)))] &&
        returned.state.predicates == taken.state.predicates ++ [.ret (Term.C32 2)] &&
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
      a.exprs.entries.isEmpty && b.exprs.entries.isEmpty &&
      a.predicates == [.cmp (branchRel op) ta tb] &&
      b.predicates == [.cmp (branchRel op).compl ta tb]
    | _ => false

private def compressedBranchesCheck : Bool :=
  let σ : SemState := ⟨ExprSet.empty.insertEq (Reg.real32 8) (Term.V32 3), []⟩
  [0xc011, 0xe011].all fun word =>
    let I := decodeProgram #[UInt32.ofNat word, 0x0001, 0x0001]
    match rv32Step I 0 σ with
    | .candidates [a, b] => a.dir == .taken && b.dir == .notTaken &&
      a.loc == .pos 2 && b.loc == .pos 1 &&
      let rel := if word == 0xc011 then Rel.eq else Rel.ne
      a.predicates == [.cmp rel (Term.V32 3) (Term.C32 0)] &&
      b.predicates == [.cmp rel.compl (Term.V32 3) (Term.C32 0)]
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
6–7 C.SWSP; 8 C.ADDI4SPN; 9/25 LHU, 16/19 LBU;
12–13 SLTU; 14 C.OR; 15 C.BNEZ; 20 C.SLLI; 21 C.SRLI;
22 C.ADD; 26 C.LUI; 30 LUI; 44–45 C.LWSP; 47 C.JR + return observation.
36 C.JAL has its link-value semantics, but target offset 104 - 616 = -512
is outside this image. External call/result contracts are required to reach 37–43;
we retain UnboundTarget rather than fabricate a helper result or fallthrough.
-/

/-- 512 fuel exposes the first remaining blocker after 39 successful expansions.
All earlier reachable value functions succeed; the short BLTU side observes return 2. -/
private def esp32c3DeepFrontierCheck : Bool :=
  let I := esp32c3Program
  let stepFn := rv32StepBound I (some 0x1000) (some 0x2000)
  match rv32Init I smokeEntryParams 0 512 with
  | .error _ => false
  | .ok ws0 => match expandN I.size stepFn ws0 39 with
    | .inl _ => false
    | .inr ws =>
      ws.nodes.size == 44 && ws.fuel == 473 && ws.work == [41, 42, 43] &&
      ws.nodes.any (fun n => n.loc == .pos 25) &&
      ws.nodes.any (fun n => n.loc == .pos 46) &&
      ws.nodes.all (fun n => match n.loc with
        | .exit => n.state.predicates.getLast? == some (.ret (Term.C32 2))
        | .pos j => match I[j]? with
          | some i => (RV32IMC.step (n.state.exprs.insertEq (Reg.real32 32)
              (Term.C32 (0x1000 + ((programOffsets I)[j]?.getD 0)))) i).isSome
          | none => false) &&
      (match ws.nodes[5]?, ws.nodes[7]? with
        | some taken, some returned =>
          returned.loc == .exit && returned.state.predicates ==
            taken.state.predicates ++ [.ret (Term.C32 2)]
        | _, _ => false) &&
      (match ws.nodes[41]?, I[36]?, expandOne I.size stepFn ws with
        | some blocked, some (Insn.C_JAL imm), .inl (.fail .unboundTarget g) =>
          blocked.loc == .pos 36 && (programOffsets I)[36]? == some 104 &&
          2 * s 11 imm.toNat == -616 && g.nodes.size == ws.nodes.size
        | _, _, _ => false) &&
      -- The queued packet-success side also supports C.LUI/ADDI/BEQ,
      -- beyond the first globally blocking external-call node.
      (match ws.nodes[43]? with
        | none => false
        | some n => match expandInit I.size 26 n.state 8 with
          | .error _ => false
          | .ok tail => match expandN I.size stepFn tail 3 with
            | .inr w => w.nodes.any (fun node => node.loc == .pos 44) &&
                w.nodes.any (fun node => node.loc == .pos 29)
            | _ => false)

private def returnObservationMergeCheck : Bool :=
  let p := Predicate.ret (Term.V32 123)
  let q := Predicate.cmp .eq (Term.V32 7) (Term.C32 0)
  (match mergePredicate [q] [p, p, q] with
    | .ok ps => ps == [q, p]
    | _ => false) && p.eval?.isNone &&
  renderPredicateJson (.ret (Term.C32 2)) == "{\"kind\":\"ret\",\"term\":\"2\"}"

/-- C.JR and full JALR observe a0, but ordinary indirect jumps do not. -/
private def boundReturnObservationCheck : Bool :=
  let E := ExprSet.empty.insertEq (Reg.real32 1) (Term.C32 0x2000)
    |>.insertEq (Reg.real32 10) (Term.V32 123)
  [decodeProgram #[0x00008067], decodeProgram #[0x8082]].all (fun I =>
    match rv32StepBound I (some 0x1000) (some 0x2000) 0 ⟨E, []⟩ with
    | .candidates [c] => c.loc == .exit && c.predicates == [.ret (Term.V32 123)]
    | _ => false) &&
  (match rv32StepBound (decodeProgram #[0x00008067]) (some 0x1000) (some 0x2002)
      0 ⟨E, []⟩ with
    | .reject .unboundTarget => true
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
        | some a, some b => a.entries.length == 1 && a.keysUnique &&
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
    (eval (star .w32 .inputByte [Term.C32 4096, Term.C32 4108])).isNone

#guard packetLoadsCheck

#guard esp32c3DeepFrontierCheck
#guard returnObservationMergeCheck
#guard boundReturnObservationCheck

-- Parent Rust glue: lean_rv32_expand_snapshot(uint32_t steps, uint32_t budget) -> Lean String.
@[export lean_rv32_expand_snapshot]
def exportRv32Snapshot (steps budget : UInt32) : String :=
  rv32Snapshot esp32c3Program smokeEntryParams 0 steps.toNat budget.toNat

-- Parent Rust glue: words is a boxed Lean Array UInt32; steps/budget are uint32_t, result Lean String.
@[export lean_rv32_expand_words_snapshot]
def exportRv32WordsSnapshot (words : Array UInt32) (steps budget : UInt32) : String :=
  rv32Snapshot (decodeProgram words) smokeEntryParams 0 steps.toNat budget.toNat

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

private def helperStep (I : Array Insn) (base helper : Nat) (p : EntryParams)
    (event : NodeId) (j : Nat) (σ : SemState) : StepResult :=
  let fallback := rv32StepBound I (some base) (some 0x2000) j σ (some p.tCtx)
  match I[j]?, (programOffsets I)[j]? with
  | some i, some offset =>
    if helperTarget i (base + offset) σ.exprs != some helper then fallback
    else if !guardEg σ.exprs then .reject .localReject
    else match nextPosition I j with
      | none => .reject .unboundTarget
      | some loc =>
        let Eg := σ.exprs.insertEq (Reg.real32 32) (Term.C32 (base + offset))
        match RV32IMC.step Eg i (some p.tCtx), parseHelperCall σ.exprs with
        | some link, .ok call =>
          let result := helperExpr event call p σ.exprs
          let Ei := updateExpr link result
          .candidates [⟨.only, loc, Ei, helperPredicates call σ.exprs result⟩]
        | _, .error reason => .reject reason
        | none, _ => .reject .undefinedSrc
  | _, _ => fallback

@[export lean_rv32_expand_bound_words_snapshot]
def exportRv32BoundWordsSnapshot (words : Array UInt32) (base helper steps budget : UInt32) : String :=
  let I := decodeProgram words
  let b := base.toNat
  let h := helper.toNat
  let extent := I.foldl (fun n i => n + insnLength i) 0
  let p := { smokeEntryParams with tEntry := Term.C32 b }
  if I.isEmpty || b == 0 || b % 4 != 0 || h == 0 || h % 4 != 0 ||
      b + extent > (1 <<< 32) || h == 0x2000 ||
      (b ≤ 0x2000 && 0x2000 < b + extent) || (b ≤ h && h < b + extent) then
    snapshotJson #[] #[] [] 0 "fail" (some .invalidEntry)
  else match rv32Init I p 0 budget.toNat with
    | .error reason => snapshotJson #[] #[] [] 0 "fail" (some reason)
    | .ok ws => snapshotAfter I.size (helperStep I b h p) ws steps.toNat

end RV32IMC
