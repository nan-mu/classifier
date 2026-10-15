import EBPF.JustTxProgram
import PathMerge.Budget
import ClassifierExpr.Parse

namespace EBPF
open ClassifierExpr PathMerge

/-- Static entry and resource bindings, outside the executing SemState. -/
structure Meta where
  entry : EntryParams
  resourceLocations : List ResourceLocation := []
  maps : List MapLayout := []
  deriving Repr, Inhabited

private def jsonNat (value : Lean.Json) (key : String) : Option Nat :=
  (value.getObjVal? key >>= Lean.Json.getNat?).toOption

private def jsonTerm (value : Lean.Json) (key : String) (width : Width) : Option Term := do
  let text ← (value.getObjVal? key >>= Lean.Json.getStr?).toOption
  let term ← parseTerm text width
  if term.width != width || !predicateWellFormed (.ret term) then none else some term

private def jsonLeaf (value : Lean.Json) (key : String) (width : Width) : Option Term := do
  match ← jsonTerm value key width with
  | term@(.const _ _) | term@(.var _ _) => some term
  | _ => none

private def parseEntry (value : Lean.Json) : Option EntryParams := do
  let tCtx ← jsonLeaf value "tCtx" .w64
  let tSp ← jsonLeaf value "tSp" .w64
  let tData ← jsonLeaf value "tData" .w32
  let packetBytes ← jsonNat value "packetBytes"
  if packetBytes ≥ (1 <<< 32) then none else pure ()
  let αCtx ← jsonNat value "alphaCtx"
  let κPacket ← jsonNat value "packetId"
  let φStack ← jsonNat value "stackId"
  some { tCtx, tSp, tData, packetBytes, αCtx, κPacket, φStack }

private def parseResourceLocation (value : Lean.Json) : Option ResourceLocation := do
  let slot ← jsonNat value "slot"
  let field ← (value.getObjVal? "term").toOption
  let term ← match field with
    | .null => some none
    | _ => some <$> jsonTerm value "term" .w64
  some { slot, term }

/-- Parse the eBPF Meta wire schema. Missing entry fields, malformed terms,
non-leaf entry terms, oversized packets and duplicate resource slots reject
without accepting a partial binding. Absent resourceLocations/maps means empty. -/
def parseMetaJson (text : String) : Option Meta := do
  let value ← (Lean.Json.parse text).toOption
  let entry ← parseEntry (← (value.getObjVal? "entry").toOption)
  let resourceLocations ← match value.getObjVal? "resourceLocations" with
    | .error _ => some []
    | .ok field => do
      let rows ← field.getArr?.toOption
      rows.toList.mapM parseResourceLocation
  let maps ← match value.getObjVal? "maps" with
    | .error _ => some []
    | .ok field => do
      let rows ← field.getArr?.toOption
      rows.toList.mapM parseMapLayout
  let slots := resourceLocations.map (·.slot)
  if slots.eraseDups.length != slots.length then none
  else some { entry, resourceLocations, maps }

/-- Decode without compacting LDDW: all control locations remain raw slots.
Resource provenance is a caller premise, not inferred from integer immediates. -/
def boundProgram (words : Array UInt64) (m : Meta) :
    Except RejectReason (Array Insn × StepContext) :=
  if words.isEmpty then .error .invalidEntry
  else .ok (decodeProgram words,
    { entry := m.entry, resourceLocations := m.resourceLocations, maps := m.maps })

/-- The root contains the actual pre-instruction eBPF entry state. -/
def ebpfInit (I : Array Insn) (p : EntryParams) (j0 budget : Nat) :
    Except RejectReason WorkState := do
  let σ0 ← buildE0 p
  expandInit I.size j0 σ0 budget

/-- At most steps expansions, with composed states and source-node event IDs.
Budget exhaustion uses the shared driver's LimitExceeded result. -/
def ebpfSnapshot (I : Array Insn) (context : StepContext) (j0 steps budget : Nat) : String :=
  match ebpfInit I context.entry j0 budget with
  | .error reason => snapshotJson #[] #[] [] 0 "fail" (some reason)
  | .ok ws => snapshotAfter I.size (ebpfStep I context) ws steps

private def createFailJson (reason : RejectReason) : String :=
  s!"\{\"status\":\"fail\",\"reason\":\"{reasonTag reason}\",\"failed\":null,\"work\":[],\"nodes\":[],\"edges\":[]}"

/-- Meta-only entry creation: no program is supplied, so successful create
cannot verify a program or its first slot. No fuel or snapshot-only fields:
the external runtime owns the product expansion budget. -/
@[export lean_ebpf_expand_create]
def exportEbpfExpandCreate (metaJson : String) : String :=
  match parseMetaJson metaJson with
  | none => createFailJson .invalidEntry
  | some m =>
    match buildE0 m.entry with
    | .error reason => createFailJson reason
    | .ok σ0 =>
      let (exprs, preds) := renderSemStateJson σ0
      s!"\{\"status\":\"running\",\"reason\":null,\"failed\":null,\"work\":[0],\"nodes\":[\{\"id\":0,\"loc\":\"0\",\"exprs\":[{exprs}],\"predicates\":[{preds}]}],\"edges\":[]}"

private def headFailJson (reason : RejectReason) : String :=
  s!"\{\"status\":\"fail\",\"reason\":\"{reasonTag reason}\",\"successors\":[]}"

private def successorJson (row : Direction × Location × SemState) : String :=
  let (dir, loc, state) := row
  let loc := match loc with | .exit => "exit" | .pos j => toString j
  let (exprs, preds) := renderSemStateJson state
  s!"\{\"dir\":\"{dirTag dir}\",\"loc\":\"{loc}\",\"exprs\":[{exprs}],\"predicates\":[{preds}]}"

/-- Stateless head inference. prepareAll composes every candidate with the
pre-state before returning successors; queue and fuel remain runtime-owned. -/
@[export lean_ebpf_expand_step]
def exportEbpfExpandStep (insns : Array UInt64) (metaJson : String) (event j : UInt32)
    (exprsJson predsJson : String) : String :=
  match parseMetaJson metaJson with
  | none => headFailJson .invalidEntry
  | some m =>
    match boundProgram insns m with
    | .error reason => headFailJson reason
    | .ok (I, context) =>
      match parseSemStateJson exprsJson predsJson with
      | none => headFailJson .localReject
      | some state =>
        match ebpfStep I context event.toNat j.toNat state with
        | .reject reason => headFailJson reason
        | .candidates cs =>
          match prepareAll state I.size cs with
          | .error reason => headFailJson reason
          | .ok prepared =>
            let successors := String.intercalate "," (prepared.map successorJson)
            s!"\{\"status\":\"ok\",\"reason\":null,\"successors\":[{successors}]}"

@[export lean_ebpf_expand_bound_words_snapshot]
def exportEbpfBoundWordsSnapshot (insns : Array UInt64) (metaJson : String)
    (steps budget : UInt32) : String :=
  match parseMetaJson metaJson with
  | none => snapshotJson #[] #[] [] 0 "fail" (some .invalidEntry)
  | some m =>
    match boundProgram insns m with
    | .error reason => snapshotJson #[] #[] [] 0 "fail" (some reason)
    | .ok (I, context) => ebpfSnapshot I context 0 steps.toNat budget.toNat

private def fixtureEntryJson : String :=
  "{\"tCtx\":\"v64:1\",\"tSp\":\"v64:0\",\"tData\":\"v32:4\",\"packetBytes\":128,\"alphaCtx\":0,\"packetId\":0,\"stackId\":0}"

private def fixtureMetaJson : String :=
  s!"\{\"entry\":{fixtureEntryJson},\"resourceLocations\":[\{\"slot\":34,\"term\":null}]}"

private def unmarkedMetaJson : String := s!"\{\"entry\":{fixtureEntryJson}}"

/-- Exact native product binding, including the shared rxcnt Map layout. -/
def productMetaJson : String :=
  "{\"entry\":{\"tCtx\":\"v64:1\",\"tSp\":\"v64:0\",\"tData\":\"v32:4\",\"packetBytes\":128,\"alphaCtx\":0,\"packetId\":0,\"stackId\":0},\"resourceLocations\":[{\"slot\":34,\"term\":\"1077412584\"}],\"maps\":[{\"mapId\":1077412584,\"keySize\":4,\"valueSize\":8}]}"

private def createCheck : Bool :=
  let response := exportEbpfExpandCreate fixtureMetaJson
  response.contains "\"status\":\"running\"" && response.contains "\"loc\":\"0\"" &&
    !response.contains "\"fuel\"" &&
    exportEbpfExpandCreate "{}" == createFailJson .invalidEntry &&
    !(exportEbpfExpandCreate "{}").contains "\"fuel\""

private def statelessStepCheck : Bool := Id.run do
  let some m := parseMetaJson fixtureMetaJson | return false
  let .ok (I, context) := boundProgram justTxProgram m | return false
  let .ok ws := ebpfInit I context.entry 0 200 | return false
  let state := ws.nodes[0]!.state
  let (exprs, preds) := renderSemStateJson state
  let .inr next := expandOne I.size (ebpfStep I context 0) ws | return false
  let response := exportEbpfExpandStep justTxProgram fixtureMetaJson 0 0
    s!"[{exprs}]" s!"[{preds}]"
  return next.nodes[1]!.loc == .pos 1 &&
    next.nodes[1]!.state.exprs.lookupEq (Reg.real64 0) == some (Term.C64 1) &&
    next.nodes[1]!.state.exprs.lookupEq (Reg.real64 1) == some justTxEntry.tCtx &&
    response == s!"\{\"status\":\"ok\",\"reason\":null,\"successors\":[{successorJson (.ok, next.nodes[1]!.loc, next.nodes[1]!.state)}]}" &&
    response.contains "\"dir\":\"OK\"" && response.contains "\"loc\":\"1\"" &&
    exportEbpfExpandStep #[] fixtureMetaJson 0 0 "[]" "[]" == headFailJson .invalidEntry

private def failedSlotCheck (response : String) (reason : String) (slot : Nat) : Bool :=
  (do
    let value ← (Lean.Json.parse response).toOption
    let status ← (value.getObjVal? "status" >>= Lean.Json.getStr?).toOption
    let actualReason ← (value.getObjVal? "reason" >>= Lean.Json.getStr?).toOption
    let failed ← jsonNat value "failed"
    let nodes ← (value.getObjVal? "nodes" >>= Lean.Json.getArr?).toOption
    let node ← nodes[failed]?
    let loc ← (node.getObjVal? "loc" >>= Lean.Json.getStr?).toOption
    pure (status == "fail" && actualReason == reason && loc == toString slot)).getD false

private def laterStepsCheck : Bool := Id.run do
  let I := decodeProgram justTxProgram
  let unmarked : StepContext := { entry := justTxEntry }
  let plain := ebpfSnapshot I unmarked 0 200 200
  let marked := ebpfSnapshot I justTxContext 0 200 200
  return failedSlotCheck plain "UndefinedSrc" 38 &&
    failedSlotCheck marked "UnboundTarget" 34 &&
    exportEbpfBoundWordsSnapshot justTxProgram unmarkedMetaJson 200 200 == plain &&
    exportEbpfBoundWordsSnapshot justTxProgram fixtureMetaJson 200 200 == marked

/-- Branch observations persist through EXIT. Only the Return projection is
singleton; compilation of this finite fixture is not a general semantic proof. -/
private def earlyExitCheck : Bool := Id.run do
  let I := decodeProgram justTxProgram
  let some m := parseMetaJson productMetaJson | return false
  let .ok (_, context) := boundProgram justTxProgram m | return false
  let .ok ws := ebpfInit I context.entry 0 1024 | return false
  let .complete graph := expand I.size (ebpfStep I context 0) ws | return false
  let some compare := graph.nodes.find? (fun node => node.loc == .pos 5) | return false
  let some lhs := compare.state.exprs.lookupEq (Reg.real64 1) | return false
  let some rhs := compare.state.exprs.lookupEq (Reg.real64 2) | return false
  return graph.nodes.any fun node =>
    node.loc == .exit &&
    node.state.exprs.lookupEq (Reg.real64 0) == some (Term.C64 1) &&
    node.state.predicates.contains (.branch 6 .taken ⟨lhs, .gtu, rhs⟩) &&
    node.state.predicates.filter (fun p => match p with | .ret _ => true | _ => false) ==
      [.ret (Term.C64 1)]

/-- Finite end-to-end smoke through the actual product Meta parser and snapshot. -/
private def productSnapshotCheck : Bool := (do
  let m ← parseMetaJson productMetaJson
  let (_, productContext) ← (boundProgram justTxProgram m).toOption
  let I := decodeProgram justTxProgram
  let response := ebpfSnapshot I productContext 0 2000 1024
  let value ← (Lean.Json.parse response).toOption
  let status ← (value.getObjVal? "status" >>= Lean.Json.getStr?).toOption
  let nodes ← (value.getObjVal? "nodes" >>= Lean.Json.getArr?).toOption
  pure (status == "complete" &&
    nodes.any (fun node =>
      (node.getObjVal? "loc" >>= Lean.Json.getStr?).toOption == some "exit" &&
      ((node.getObjVal? "predicates" >>= Lean.Json.getArr?).toOption.getD #[]).any
        (fun p => (p.getObjVal? "kind" >>= Lean.Json.getStr?).toOption == some "ret" &&
          ((p.getObjVal? "term" >>= Lean.Json.getStr?).toOption >>= fun text =>
            parseTerm text .w64) == some (Term.C64 3))) &&
    nodes.any (fun node =>
      ((node.getObjVal? "predicates" >>= Lean.Json.getArr?).toOption.getD #[]).any
        (fun p => (p.getObjVal? "helperId" >>= Lean.Json.getNat?).toOption == some 1)) &&
    nodes.any (fun node =>
      ((node.getObjVal? "exprs" >>= Lean.Json.getArr?).toOption.getD #[]).any (fun e =>
        (e.getObjVal? "reg" >>= Lean.Json.getStr?).toOption == some "real64:0" &&
        (e.getObjVal? "rel" >>= Lean.Json.getStr?).toOption == some "eq" &&
        (match (e.getObjVal? "term" >>= Lean.Json.getStr?).toOption >>= fun text =>
            parseTerm text .w64 with
          | some (.app .w64 (.externalResult _ 0) (Term.const .w64 1 :: _)) => true
          | _ => false))))).getD false

/-- A complete-frontier node carries both frozen-key 32-bit MapWrite halves at
offsets zero and four; each is well-formed and round-trips through shared wire. -/
private def productMapWriteCheck : Bool := Id.run do
  let some m := parseMetaJson productMetaJson | return false
  let .ok (I, context) := boundProgram justTxProgram m | return false
  let .ok ws := ebpfInit I context.entry 0 1024 | return false
  let .complete graph := expand I.size (ebpfStep I context 0) ws | return false
  return graph.nodes.any fun node =>
    node.state.predicates.any fun low => match low with
      | .mapWrite event map key offset source =>
        map == Term.C64 1077412584 && !key.isEmpty && offset == 0 &&
        source.width == .w32 && predicateWellFormed low &&
        ((Lean.Json.parse (renderPredicateJson low)).toOption >>= parsePredicateJson) ==
          some low &&
        node.state.predicates.any fun high => match high with
          | .mapWrite highEvent highMap highKey highOffset highSource =>
            highEvent == event && highMap == map && highKey == key && highOffset == 4 &&
            highSource.width == .w32 && predicateWellFormed high &&
            ((Lean.Json.parse (renderPredicateJson high)).toOption >>= parsePredicateJson) ==
              some high
          | _ => false
      | _ => false

private def parseRejectsCheck : Bool :=
  let badCtx := fixtureEntryJson.replace "v64:1" "v32:1"
  let badPacket := fixtureEntryJson.replace "128" "4294967296"
  let duplicate := s!"\{\"entry\":{fixtureEntryJson},\"resourceLocations\":[\{\"slot\":34,\"term\":null},\{\"slot\":34,\"term\":\"v64:9\"}]}"
  let malformed := s!"\{\"entry\":{fixtureEntryJson},\"resourceLocations\":[\{\"slot\":34,\"term\":\"add64(v32:1,0)\"}]}"
  ["{}", s!"\{\"entry\":{badCtx}}", s!"\{\"entry\":{badPacket}}",
    duplicate, malformed].all (fun text => (parseMetaJson text).isNone)

private def resourceTermCheck : Bool :=
  let compound := s!"\{\"entry\":{fixtureEntryJson},\"resourceLocations\":[\{\"slot\":34,\"term\":\"add64(v64:9,1)\"}]}"
  (parseMetaJson unmarkedMetaJson).isSome && (parseMetaJson compound).isSome &&
    ["v32:9", "add64(v64:9)", "not-a-term"].all (fun term =>
      (parseMetaJson s!"\{\"entry\":{fixtureEntryJson},\"resourceLocations\":[\{\"slot\":34,\"term\":\"{term}\"}]}").isNone)

private def mapMetaCheck : Bool := Id.run do
  let some m := parseMetaJson productMetaJson | return false
  let .ok (_, context) := boundProgram justTxProgram m | return false
  let some absent := parseMetaJson unmarkedMetaJson | return false
  return m.maps == [⟨1077412584, 4, 8⟩] && context.maps == m.maps &&
    absent.maps.isEmpty &&
    ["null", "{}", "[{\"mapId\":42,\"keySize\":65,\"valueSize\":8}]",
      "[{\"mapId\":42,\"keySize\":4,\"valueSize\":0}]",
      "[{\"mapId\":42,\"keySize\":4,\"valueSize\":4097}]"].all (fun maps =>
        (parseMetaJson s!"\{\"entry\":{fixtureEntryJson},\"maps\":{maps}}").isNone)

private def budgetCheck : Bool :=
  let response := exportEbpfBoundWordsSnapshot justTxProgram fixtureMetaJson 1 0
  response.contains "\"status\":\"fail\"" && response.contains "\"reason\":\"LimitExceeded\"" &&
    response.contains "\"fuel\":0" &&
    exportEbpfBoundWordsSnapshot #[] fixtureMetaJson 1 1 ==
      snapshotJson #[] #[] [] 0 "fail" (some .invalidEntry)

#guard (decodeProgram justTxProgram).size == 58
#guard (decodeProgram justTxProgram)[5]? == some (.jcond .w64 .jgt 1 (.reg 2) 51)
#guard (decodeProgram justTxProgram)[31]? == some (.stx 4 10 1 (-4))
#guard (decodeProgram justTxProgram)[34]? == some (.lddw 1 0 0)
#guard (decodeProgram justTxProgram)[35]? == some .continuation
#guard (decodeProgram justTxProgram)[36]? == some (.callHelper 1)
#guard (decodeProgram justTxProgram)[57]? == some .exit
#guard match ebpfStep (decodeProgram justTxProgram) justTxContext 36 36 SemState.empty with
  | .reject .undefinedSrc => true
  | _ => false
#guard match ebpfStep (decodeProgram justTxProgram) justTxContext 57 57
    ⟨ExprSet.empty.insertEq (Reg.real64 0) (Term.C64 1), []⟩ with
  | .candidates [c] => c.dir == .ok && c.loc == .exit &&
      c.E_k == ExprSet.empty && c.P_k == [.ret (Term.C64 1)]
  | _ => false
#guard createCheck
#guard statelessStepCheck
#guard laterStepsCheck
#guard earlyExitCheck
#guard productSnapshotCheck
#guard productMapWriteCheck
#guard parseRejectsCheck
#guard resourceTermCheck
#guard budgetCheck
#guard mapMetaCheck

private def extendedInstructionFfiCheck : Bool := Id.run do
  let some m := parseMetaJson unmarkedMetaJson | return false
  let .ok initial := buildE0 m.entry | return false
  let E := initial.exprs.insertEq (Reg.real64 1) (Term.C64 0x10000000f)
    |>.insertEq (Reg.real64 2) (Term.C64 0x81)
    |>.insertEq (stackUnitReg 0 0) (Term.C32 0x11223380)
  let (exprs, preds) := renderSemStateJson ⟨E, []⟩
  let cases : List (UInt64 × Reg × Nat) :=
    [(0x0000000200000114, Reg.real64 1, 13),
      (0x00000000000821bc, Reg.real64 1, 0xffffff81),
      (0x00000010000002dc, Reg.real64 2, 0x8100),
      (0x00000001fffc0a62, stackUnitReg 0 0, 1),
      (0x00000000fffca391, Reg.real64 3, 0xffffffffffffff80),
      (0x00000100fffca3d3, Reg.real64 3, 0x80),
      (0x00000110fffc2ad3, stackUnitReg 0 0, 0x11223381)]
  for (word, reg, expected) in cases do
    let response := exportEbpfExpandStep #[word, 0x95] unmarkedMetaJson 11 0
      s!"[{exprs}]" s!"[{preds}]"
    let state : SemState :=
      ⟨E.override (ExprSet.empty.insertEq reg (Term.C reg.width expected)), []⟩
    if response != s!"\{\"status\":\"ok\",\"reason\":null,\"successors\":[{successorJson (.ok, .pos 1, state)}]}" then
      return false
  let response := exportEbpfExpandStep #[0x00000001fffc2ac3, 0x95]
    unmarkedMetaJson 11 0 s!"[{exprs}]" "[]"
  let delta := ExprSet.empty.insertEq (stackUnitReg 0 0) (Term.C32 0x11223401)
    |>.insertEq (Reg.real64 2) (Term.C64 0x11223380)
  let state : SemState := ⟨E.override delta, []⟩
  return response ==
    s!"\{\"status\":\"ok\",\"reason\":null,\"successors\":[{successorJson (.ok, .pos 1, state)}]}"

#guard extendedInstructionFfiCheck

end EBPF
