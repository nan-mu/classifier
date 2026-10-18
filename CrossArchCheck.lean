import Node.Compare
import EBPF.Expand
import RV32.Expand
import CrossArch.CompoundPacketFixture

open Lean

private def rv32Words : Array UInt32 :=
  #[4417, 50694, 50210, 49702, 2048, 16644, 16716, 14976531, 17669, 180744035, 12899843, 26285,
    2290517651, 14026339, 135267987, 14031459, 19170835, 180740195, 17094147, 17737, 40977, 17721,
    26297, 3630597779, 14028131, 18081, 14032739, 38182, 21300755, 12970595, 9782531, 41017, 38182,
    42272275, 113638243, 17665, 49194, 1077413303, 780502419, 17669, 34314, 18049, 18177, 18305,
    13121, 34218, 17669, 51593, 16784, 16852, 1541, 1455891, 38586, 49552, 49620, 17794, 17989,
    46504803, 6591747, 8689027, 10786307, 300675, 2397955, 4495235, 10784803, 11833635, 12882467,
    13931299, 14980131, 16028963, 17677, 16562, 17442, 17554, 321, 32898]

private def fieldString (j : Json) (key : String) : Except String String := do
  (← j.getObjVal? key).getStr?

private def fieldArray (j : Json) (key : String) : Except String (Array Json) := do
  (← j.getObjVal? key).getArr?

private def snapshotRun (arch response : String) : Except String Json := do
  let j ← Json.parse response
  let nodes ← fieldArray j "nodes"
  let edges ← fieldArray j "edges"
  pure (Json.mkObj [("arch", .str arch), ("nodes", .arr nodes), ("edges", .arr edges)])

private def report (left right : Json) : Except String Json :=
  Json.parse (Node.exportCompareRunSameDiff
    (Json.mkObj [("left", left), ("right", right)]).compress)

private def droppedRun (run : Json) : Except String Json := do
  let nodes ← fieldArray run "nodes"
  let edges ← fieldArray run "edges"
  let some entry ← nodes.toList.findM? (fun n => return (← fieldString n "loc") == "0")
    | throw "missing entry position"
  let removed ← (← entry.getObjVal? "id").getNat?
  let remaining ← nodes.toList.filterM fun n => return (← (← n.getObjVal? "id").getNat?) != removed
  let retained ← edges.toList.filterM fun e => do
    let src ← (← e.getObjVal? "src").getNat?
    let dst ← (← e.getObjVal? "dst").getNat?
    pure (src != removed && dst != removed)
  pure (Json.mkObj [("arch", ← run.getObjVal? "arch"),
    ("nodes", .arr remaining.toArray), ("edges", .arr retained.toArray)])

private def classes := ["valueBindings", "constraints", "helper", "branch", "ret", "mapWrite", "packetWrite"]
private def verdicts := ["Equal", "Differs", "AbsentLeft", "AbsentRight"]

private def tally (positions : Array Json) (name verdict : String) : Nat :=
  positions.foldl (fun count p =>
    let cs := (fieldArray p "classes").toOption.getD #[]
    count + cs.foldl (fun n c => if (fieldString c "class").toOption == some name &&
      (fieldString c "verdict").toOption == some verdict then n + 1 else n) 0) 0

private def summary (name : String) (j : Json) : Except String String := do
  let status ← fieldString j "status"
  let conclusion ← fieldString j "conclusion"
  let positions ← fieldArray j "positions"
  let tallies := classes.map fun c => c ++ "{" ++ String.intercalate "," (verdicts.map fun v =>
    v ++ "=" ++ toString (tally positions c v)) ++ "}"
  pure (name ++ ": status=" ++ status ++ " conclusion=" ++ conclusion ++
    " positions=" ++ toString positions.size ++ " " ++ String.intercalate " " tallies)

private def checkReport (j : Json) (expectedConclusion : String) : Except String Unit := do
  if (← fieldString j "status") != "compared" then throw ("comparison rejected: " ++ j.compress)
  if (← fieldString j "claim") != "structural" ||
      (← fieldString j "behavioralEquivalence") != "notEstablished" then
    throw "missing structural-only report constants"
  if (← fieldString j "conclusion") != expectedConclusion then
    throw ("unexpected comparison conclusion: " ++ j.compress)

private def rootJson (response : String) : Except String (String × String) := do
  let value ← Json.parse response
  let nodes ← fieldArray value "nodes"
  let some node := nodes[0]? | throw "missing create root"
  let exprs ← node.getObjVal? "exprs"
  let preds ← node.getObjVal? "predicates"
  pure (exprs.compress, preds.compress)

private def checks : Except String (List String) := do
  let (ebpfExprs, ebpfPreds) ← rootJson (EBPF.exportEbpfExpandCreate "v64:1" "v64:0" "v32:4" 128 0 0 0
    #[34] #[1077412584] #[1077412584] #[4] #[8])
  let ebpfResponse := EBPF.exportEbpfBoundWordsSnapshot EBPF.justTxProgram ebpfExprs ebpfPreds 2000 1024
  let ebpfSnapshot ← Json.parse ebpfResponse
  let ebpfStatus ← fieldString ebpfSnapshot "status"
  if ebpfStatus != "complete" then
    throw ("eBPF product fixture did not complete: " ++ ebpfSnapshot.compress)
  let ebpfNodes ← fieldArray ebpfSnapshot "nodes"
  let ebpfEdges ← fieldArray ebpfSnapshot "edges"
  let terminalReturns ← ebpfNodes.toList.filterMapM fun n => do
    if (← fieldString n "loc") != "exit" then pure none else do
      let ps ← fieldArray n "predicates"
      let returns ← ps.toList.filterMapM fun p => do
        if (← fieldString p "kind") != "ret" then pure none
        else pure (Core.parseTerm (← fieldString p "term") .w64)
      pure (some returns)
  if !terminalReturns.any (·.contains (Core.Term.C64 3)) then
    throw "eBPF fixture missing concrete TX return 3"
  let ebpf ← snapshotRun "ebpf" ebpfResponse
  let (rvExprs, rvPreds) ← rootJson (RV32.exportRv32ExpandCreate 1077412352 1077411840 8192
    #[1077412584] #[4] #[8])
  let rv32Response := RV32.exportRv32BoundWordsSnapshot rv32Words rvExprs rvPreds 400 400
  let rv32Snapshot ← Json.parse rv32Response
  let rv32Status ← fieldString rv32Snapshot "status"
  let rv32Reason ← rv32Snapshot.getObjVal? "reason"
  let rv32Nodes ← fieldArray rv32Snapshot "nodes"
  let rv32Edges ← fieldArray rv32Snapshot "edges"
  if rv32Status != "complete" then
    throw s!"RV32 fixture status={rv32Status} reason={rv32Reason.compress}"
  if rv32Nodes.size != 146 then
    throw s!"RV32 fixture nodeCount={rv32Nodes.size}"
  if rv32Nodes.any (fun n => (fieldString n "loc").toOption == some "34") then
    throw "RV32 fixture reached the old unbound branch at slot 34"
  let rv32 ← snapshotRun "rv32imc" rv32Response
  let self ← report ebpf ebpf
  let cross ← report rv32 ebpf
  let dropped ← report ebpf (← droppedRun ebpf)
  checkReport self "sameStructure"
  checkReport cross "coverageDiffers"
  checkReport dropped "coverageDiffers"
  let ps ← fieldArray dropped "positions"
  if !ps.any (fun p => (fieldString p "verdict").toOption == some "OnlyLeft") then
    throw "dropped entry position did not produce OnlyLeft"
  pure [s!"ebpf-terminal: status={ebpfStatus} nodeCount={ebpfNodes.size} edgeCount={ebpfEdges.size} loc=exit",
    s!"rv32imc-frontier: status={rv32Status} reason={rv32Reason.compress} nodeCount={rv32Nodes.size} edgeCount={rv32Edges.size}",
    ← summary "identical-ebpf" self, ← summary "rv32imc-vs-ebpf" cross,
    cross.compress, ← summary "dropped-ebpf-node" dropped]

def main : IO UInt32 := do
  match checks with
  | .error detail => IO.eprintln ("CrossArchCheck failed: " ++ detail); pure 1
  | .ok lines =>
    for line in lines do IO.println line
    pure 0
