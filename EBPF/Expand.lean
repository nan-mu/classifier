import EBPF.JustTxProgram
import Core.Update
import EBPF.Step
import Node.Budget
import Core.Parse

namespace EBPF
open Core Node

private def parseLeaf (text : String) (width : Width) : Option Term := do
  let term ← parseTerm text width
  if term.width != width || !predicateWellFormed (.ret term) then none else
    match term with
    | .const _ _ | .var _ _ => some term
    | _ => none

private def bindSlots (E : List Expr) : List (Nat × Nat) → Option (List Expr)
  | [] => some E
  | (slot, value) :: rest => do
    if rest.any (fun p => p.1 == slot) then none
    let E ← Anchor.bindLddw E slot value
    bindSlots E rest

private def mapLayouts : List Nat → List Nat → List Nat → Option (List MapLayout)
  | [], [], [] => some []
  | id :: ids, key :: keys, value :: values => do
    if key == 0 then none
    let rest ← mapLayouts ids keys values
    some ({ mapId := id, keySize := key, valueSize := value } :: rest)
  | _, _, _ => none

/-- The root contains the actual pre-instruction eBPF entry state. -/
def ebpfInit (I : Array Insn) (σ0 : SemState) (j0 budget : Nat) :
    Except RejectReason WorkState :=
  expandInit I.size j0 σ0 budget

/-- At most steps expansions, with composed states and source-node event IDs.
Budget exhaustion uses the shared driver's LimitExceeded result. -/
def ebpfSnapshot (I : Array Insn) (σ0 : SemState) (j0 steps budget : Nat) : String :=
  match ebpfInit I σ0 j0 budget with
  | .error reason => snapshotJson #[] #[] [] 0 "fail" (some reason)
  | .ok ws => snapshotAfter I.size (ebpfStep I) ws steps

private def createFailJson (reason : RejectReason) : String :=
  s!"\{\"status\":\"fail\",\"reason\":\"{reasonTag reason}\",\"failed\":null,\"work\":[],\"nodes\":[],\"edges\":[]}"

private def runningJson (σ0 : SemState) : String :=
  let (exprs, preds) := renderSemStateJson σ0
  s!"\{\"status\":\"running\",\"reason\":null,\"failed\":null,\"work\":[0],\"nodes\":[\{\"id\":0,\"loc\":\"0\",\"exprs\":[{exprs}],\"predicates\":[{preds}]}],\"edges\":[]}"

@[export lean_ebpf_expand_create]
def exportEbpfExpandCreate
    (tCtx tSp tData : String) (packetBytes _alphaCtx _packetId _stackId : UInt32)
    (slots : Array UInt32) (terms : Array UInt64)
    (mapIds keySizes valueSizes : Array UInt32) : String :=
  if slots.size != terms.size || mapIds.size != keySizes.size ||
      keySizes.size != valueSizes.size then createFailJson .invalidEntry
  else match parseLeaf tCtx .w64, parseLeaf tSp .w64, parseLeaf tData .w32 with
    | some tCtx, some tSp, some tData =>
      let p : EntryParams := { tCtx, tSp, tData, packetBytes := packetBytes.toNat }
      match buildE0 p with
      | .error reason => createFailJson reason
      | .ok σ0 =>
        match mapLayouts (mapIds.toList.map (·.toNat)) (keySizes.toList.map (·.toNat))
            (valueSizes.toList.map (·.toNat)) with
        | none => createFailJson .invalidEntry
        | some maps =>
          match bindSlots σ0.exprs ((slots.toList.map (·.toNat)).zip (terms.toList.map (·.toNat))) with
          | none => createFailJson .invalidEntry
          | some withSlots =>
            match Anchor.installMaps withSlots maps with
            | none => createFailJson .invalidEntry
            | some exprs => runningJson { σ0 with exprs }
    | _, _, _ => createFailJson .invalidEntry

private def headFailJson (reason : RejectReason) : String :=
  s!"\{\"status\":\"fail\",\"reason\":\"{reasonTag reason}\",\"successors\":[]}"

private def successorJson (dir : Direction) (loc : Location) (step : SemState) : String :=
  let loc := match loc with | .exit => "exit" | .pos j => toString j
  s!"\{\"dir\":\"{dirTag dir}\",\"loc\":\"{loc}\",{renderIncrementJson step}}"

@[export lean_ebpf_expand_step]
def exportEbpfExpandStep (insns : Array UInt64) (event j : UInt32)
    (exprsJson predsJson : String) : String :=
  if insns.isEmpty then headFailJson .invalidEntry
  else
    let I := decodeProgram insns
    match parseSemStateJson exprsJson predsJson with
    | none => headFailJson .localReject
    | some state =>
      match ebpfStep I event.toNat j.toNat state with
      | .reject reason => headFailJson reason
      | .candidates cs =>
        match prepareAll state I.size cs with
        | .error reason => headFailJson reason
        | .ok _ =>
          let successors := String.intercalate ","
            (cs.map fun c => successorJson c.dir c.loc { exprs := c.E_k, predicates := c.P_k })
          s!"\{\"status\":\"ok\",\"reason\":null,\"successors\":[{successors}]}"

@[export lean_ebpf_expand_bound_words_snapshot]
def exportEbpfBoundWordsSnapshot (insns : Array UInt64) (exprsJson predsJson : String)
    (steps budget : UInt32) : String :=
  if insns.isEmpty then snapshotJson #[] #[] [] 0 "fail" (some .invalidEntry)
  else match parseSemStateJson exprsJson predsJson with
    | none => snapshotJson #[] #[] [] 0 "fail" (some .invalidEntry)
    | some σ0 => ebpfSnapshot (decodeProgram insns) σ0 0 steps.toNat budget.toNat

private def rootOf (response : String) : Option SemState := do
  let value ← (Lean.Json.parse response).toOption
  let nodes ← (value.getObjVal? "nodes" >>= Lean.Json.getArr?).toOption
  let node ← nodes[0]?
  let exprs ← (node.getObjVal? "exprs").toOption
  let preds ← (node.getObjVal? "predicates").toOption
  parseSemStateJson exprs.compress preds.compress

private def fixtureCreate (slots : Array UInt32) (terms : Array UInt64)
    (mapIds keySizes valueSizes : Array UInt32) : String :=
  exportEbpfExpandCreate "v64:1" "v64:0" "v32:4" 128 0 0 0
    slots terms mapIds keySizes valueSizes

private def createCheck : Bool :=
  let response := fixtureCreate #[34] #[0] #[] #[] #[]
  response.contains "\"status\":\"running\"" && response.contains "\"loc\":\"0\"" &&
    !response.contains "\"fuel\":" &&
    exportEbpfExpandCreate "nope" "v64:0" "v32:4" 128 0 0 0 #[] #[] #[] #[] #[] ==
      createFailJson .invalidEntry &&
    fixtureCreate #[34] #[] #[] #[] #[] == createFailJson .invalidEntry &&
    fixtureCreate #[34, 34] #[0, 1] #[] #[] #[] == createFailJson .invalidEntry

private def statelessStepCheck : Bool := Id.run do
  let some root := rootOf (fixtureCreate #[34] #[0] #[] #[] #[]) | return false
  let I := decodeProgram justTxProgram
  let .ok ws := ebpfInit I root 0 200 | return false
  let (exprs, preds) := renderSemStateJson root
  let .inr next := expandOne I.size (ebpfStep I 0) ws | return false
  let .candidates [c] := ebpfStep I 0 0 root | return false
  let step : SemState := { exprs := c.E_k, predicates := c.P_k }
  let response := exportEbpfExpandStep justTxProgram 0 0 s!"[{exprs}]" s!"[{preds}]"
  let some r0 := readInterval next.nodes[1]!.state.exprs (Reg.real64 0) | return false
  return next.nodes[1]!.loc == .pos 1 &&
    eval (solve r0) == some 1 &&
    next.nodes[1]!.state.exprs.lookupEq (Reg.real64 1) == some justTxEntry.tCtx &&
    lddwBind root.exprs 34 == .unbound &&
    (update root step).exprs == next.nodes[1]!.state.exprs &&
    (update root step).predicates == next.nodes[1]!.state.predicates &&
    response == s!"\{\"status\":\"ok\",\"reason\":null,\"successors\":[{successorJson .ok c.loc step}]}" &&
    exportEbpfExpandStep #[] 0 0 "[]" "[]" == headFailJson .invalidEntry

private def failedSlotCheck (response : String) (reason : String) (slot : Nat) : Bool :=
  (do
    let value ← (Lean.Json.parse response).toOption
    let status ← (value.getObjVal? "status" >>= Lean.Json.getStr?).toOption
    let actualReason ← (value.getObjVal? "reason" >>= Lean.Json.getStr?).toOption
    let failed ← (value.getObjVal? "failed" >>= Lean.Json.getNat?).toOption
    let nodes ← (value.getObjVal? "nodes" >>= Lean.Json.getArr?).toOption
    let node ← nodes[failed]?
    let loc ← (node.getObjVal? "loc" >>= Lean.Json.getStr?).toOption
    pure (status == "fail" && actualReason == reason && loc == toString slot)).getD false

private def laterStepsCheck : Bool := Id.run do
  let I := decodeProgram justTxProgram
  let .ok σ := buildE0 justTxEntry | return false
  let plainE := host justTxEntry σ.exprs
  let plainState : SemState := { exprs := plainE, predicates := [] }
  let plain := ebpfSnapshot I plainState 0 200 200
  let (pexprs, ppreds) := renderSemStateJson plainState
  return failedSlotCheck plain "UndefinedSrc" 38 &&
    exportEbpfBoundWordsSnapshot justTxProgram s!"[{pexprs}]" s!"[{ppreds}]" 200 200 == plain

private def productRoot : Option SemState :=
  rootOf (fixtureCreate #[34] #[42] #[42] #[4] #[8])

/-- Branch observations persist through EXIT. Only the Return projection is
singleton; compilation of this finite fixture is not a general semantic proof. -/
private def earlyExitCheck : Bool := Id.run do
  let I := decodeProgram justTxProgram
  let some root := productRoot | return false
  let .ok ws := ebpfInit I root 0 1024 | return false
  let .complete graph := expand I.size (ebpfStep I 0) ws | return false
  let some compare := graph.nodes.find? (fun node => node.loc == .pos 5) | return false
  let some lhs := compare.state.exprs.lookupEq (Reg.real64 1) | return false
  let some rhs := compare.state.exprs.lookupEq (Reg.real64 2) | return false
  return graph.nodes.any fun node =>
    node.loc == .exit &&
    (match readInterval node.state.exprs (Reg.real64 0) with
      | some t => eval (solve t) == some 1
      | none => false) &&
    node.state.predicates.contains (.branch 6 .taken ⟨lhs, .gtu, rhs⟩) &&
    node.state.predicates.any fun p => match p with
      | .ret t => eval (solve t) == some 1
      | _ => false

private def productSnapshotCheck : Bool := (do
  let some root := productRoot | none
  let (exprs, preds) := renderSemStateJson root
  let response := exportEbpfBoundWordsSnapshot justTxProgram s!"[{exprs}]" s!"[{preds}]" 2000 1024
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
        (e.getObjVal? "reg" >>= Lean.Json.getStr?).toOption == some "real:0:[0,64)" &&
        (e.getObjVal? "rel" >>= Lean.Json.getStr?).toOption == some "eq" &&
        (match (e.getObjVal? "term" >>= Lean.Json.getStr?).toOption >>= fun text =>
            parseTerm text .w64 with
          | some (.app .w64 (.externalResult _ 0) (Term.const .w64 1 :: _)) => true
          | _ => false))))).getD false

private def productMapWriteCheck : Bool := Id.run do
  let I := decodeProgram justTxProgram
  let some root := productRoot | return false
  let .ok ws := ebpfInit I root 0 1024 | return false
  let .complete graph := expand I.size (ebpfStep I 0) ws | return false
  return graph.nodes.any fun node =>
    node.state.predicates.any fun low => match low with
      | .mapWrite event map key offset bits source =>
        map == Term.C64 42 && !key.isEmpty && offset == 0 &&
        bits == 32 && source.width == .w32 && predicateWellFormed low &&
        ((Lean.Json.parse (renderPredicateJson low)).toOption >>= parsePredicateJson) ==
          some low &&
        node.state.predicates.any fun high => match high with
          | .mapWrite highEvent highMap highKey highOffset highBits highSource =>
            highEvent == event && highMap == map && highKey == key && highOffset == 4 &&
            highBits == 32 && highSource.width == .w32 && predicateWellFormed high &&
            ((Lean.Json.parse (renderPredicateJson high)).toOption >>= parsePredicateJson) ==
              some high
          | _ => false
      | _ => false

private def budgetCheck : Bool := Id.run do
  let some root := rootOf (fixtureCreate #[34] #[0] #[] #[] #[]) | return false
  let (exprs, preds) := renderSemStateJson root
  let response := exportEbpfBoundWordsSnapshot justTxProgram s!"[{exprs}]" s!"[{preds}]" 1 0
  return response.contains "\"status\":\"fail\"" && response.contains "\"reason\":\"LimitExceeded\"" &&
    response.contains "\"fuel\":0" &&
    exportEbpfBoundWordsSnapshot #[] "[]" "[]" 1 1 ==
      snapshotJson #[] #[] [] 0 "fail" (some .invalidEntry)

#guard (decodeProgram justTxProgram).size == 58
#guard (decodeProgram justTxProgram)[5]? == some (.jcond .w64 .jgt 1 (.reg 2) 51)
#guard (decodeProgram justTxProgram)[31]? == some (.stx 4 10 1 (-4))
#guard (decodeProgram justTxProgram)[34]? == some (.lddw 1 0 0)
#guard (decodeProgram justTxProgram)[35]? == some .continuation
#guard (decodeProgram justTxProgram)[36]? == some (.callHelper 1)
#guard (decodeProgram justTxProgram)[57]? == some .exit
#guard match ebpfStep (decodeProgram justTxProgram) 36 36
    ⟨host justTxEntry Expr.nil, []⟩ with
  | .reject .undefinedSrc => true
  | _ => false
#guard match ebpfStep (decodeProgram justTxProgram) 57 57
    ⟨(update ⟨Expr.nil, []⟩ { exprs := [Expr.mkEq (Reg.real64 0) (solve (Term.C64 1))], predicates := [] }).exprs, []⟩ with
  | .candidates [c] => c.dir == .ok && c.loc == .exit &&
      c.E_k == Expr.nil && c.P_k == [.ret (Term.C64 1)]
  | _ => false
#guard createCheck
#guard statelessStepCheck
#guard laterStepsCheck
#guard earlyExitCheck
#guard productSnapshotCheck
#guard productMapWriteCheck
#guard budgetCheck

private def putWord (E : List Expr) (r : Reg) (value : Nat) : Option (List Expr) :=
  let term := if r.bits ≤ 32 then Term.C32 value else Term.C64 value
  ((«seal» (r).bits term >>= fun stored => some (update ⟨E, []⟩ { exprs := [Expr.mkEq r stored], predicates := [] }).exprs))

private def extendedInstructionFfiCheck : Bool := Id.run do
  let .ok initial := buildE0 justTxEntry | return false
  let stack : Reg := .stack (508 * 8) (508 * 8 + 32)
  let E0 := host justTxEntry ((update ⟨initial.exprs, []⟩ { exprs := [Expr.mkEq (Reg.real64 1) (solve (Term.C64 0x10000000f))], predicates := [] }).exprs
    |> (fun acc => (update ⟨acc, []⟩ { exprs := [Expr.mkEq (Reg.real64 2) (solve (Term.C64 0x81))], predicates := [] }).exprs))
  let some E := putWord E0 stack 0x11223380 | return false
  let start : SemState := { exprs := E, predicates := [] }
  let (exprs, preds) := renderSemStateJson start
  let cases : List (UInt64 × Reg × Nat) :=
    [(0x0000000200000114, Reg.real64 1, 13),
      (0x00000000000821bc, Reg.real64 1, 0xffffff81),
      (0x00000010000002dc, Reg.real64 2, 0x8100),
      (0x00000001fffc0a62, stack, 1),
      (0x00000000fffca391, Reg.real64 3, 0xffffffffffffff80),
      (0x00000100fffca3d3, Reg.real64 3, 0x80),
      (0x00000110fffc2ad3, stack, 0x11223381)]
  for (word, reg, expected) in cases do
    let response := exportEbpfExpandStep #[word, 0x95] 11 0
      s!"[{exprs}]" s!"[{preds}]"
    let .candidates [c] := ebpfStep (decodeProgram #[word, 0x95]) 11 0 start | return false
    let state := update start { exprs := c.E_k, predicates := c.P_k }
    let some got := readInterval state.exprs reg | return false
    if eval (solve got) != some expected ||
        response != s!"\{\"status\":\"ok\",\"reason\":null,\"successors\":[{successorJson .ok (.pos 1) { exprs := c.E_k, predicates := c.P_k }}]}" then
      return false
  let response := exportEbpfExpandStep #[0x00000001fffc2ac3, 0x95] 11 0 s!"[{exprs}]" "[]"
  let .candidates [c] := ebpfStep (decodeProgram #[0x00000001fffc2ac3, 0x95]) 11 0 start | return false
  let state := update start { exprs := c.E_k, predicates := c.P_k }
  let some stackGot := readInterval state.exprs stack | return false
  let some regGot := readInterval state.exprs (Reg.real64 2) | return false
  return eval (solve stackGot) == some 0x11223401 &&
    eval (solve regGot) == some 0x11223380 &&
    response == s!"\{\"status\":\"ok\",\"reason\":null,\"successors\":[{successorJson .ok (.pos 1) { exprs := c.E_k, predicates := c.P_k }}]}"

#guard extendedInstructionFfiCheck

end EBPF
