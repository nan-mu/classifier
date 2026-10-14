import PathMerge.Compare
import EBPF.Expand
import RV32IMC.Expand

open Lean

-- .xpost.image at file offset 256 in tooling/fixtures/just_tx.elf, through C.JR ra.
private def rv32Words : Array UInt32 :=
  #[4417, 50694, 50210, 49702, 2048, 16644, 16716, 14976531, 17669, 180744035, 12899843, 26285,
    2290517651, 14026339, 135267987, 14031459, 19170835, 180740195, 17094147, 17737, 40977, 17721,
    26297, 3630597779, 14028131, 18081, 14032739, 38182, 21300755, 12970595, 9782531, 41017, 38182,
    42272275, 113638243, 17665, 49194, 1077413303, 780502419, 17669, 34314, 18049, 18177, 18305,
    13121, 34218, 17669, 51593, 16784, 16852, 1541, 1455891, 38586, 49552, 49620, 17794, 17989,
    46504803, 6591747, 8689027, 10786307, 300675, 2397955, 4495235, 10784803, 11833635, 12882467,
    13931299, 14980131, 16028963, 17677, 16562, 17442, 17554, 321, 32898]

private def ebpfMeta :=
  "{\"entry\":{\"tCtx\":\"v64:1\",\"tSp\":\"v64:0\",\"tData\":\"v32:4\",\"packetBytes\":128,\"alphaCtx\":0,\"packetId\":0,\"stackId\":0}}"
private def rv32Meta :=
  "{\"base\":1077412352,\"helperAddress\":1077411840,\"returnAddress\":8192,\"maps\":[{\"mapId\":1077412584,\"keySize\":4,\"valueSize\":8}]}"

private def fieldString (j : Json) (key : String) : Except String String := do
  (← j.getObjVal? key).getStr?

private def fieldArray (j : Json) (key : String) : Except String (Array Json) := do
  (← j.getObjVal? key).getArr?

private def snapshotRun (arch response : String) : Except String Json := do
  let j ← Json.parse response
  let nodes ← fieldArray j "nodes"
  let edges ← fieldArray j "edges"
  if nodes.size < 2 then throw (arch ++ ": expected a nontrivial real run")
  pure (Json.mkObj [("arch", .str arch), ("nodes", .arr nodes), ("edges", .arr edges)])

private def report (left right : Json) : Except String Json :=
  Json.parse (PathMerge.exportCompareRunSameDiff
    (Json.mkObj [("left", left), ("right", right)]).compress)

private def droppedRun (run : Json) : Except String Json := do
  let nodes ← fieldArray run "nodes"
  let edges ← fieldArray run "edges"
  -- Remove the entry position, and every incident edge; dangling endpoints are invalid input.
  let removed ← (← nodes[0]!.getObjVal? "id").getNat?
  let retained ← edges.toList.filterM fun e => do
    let src ← (← e.getObjVal? "src").getNat?
    let dst ← (← e.getObjVal? "dst").getNat?
    pure (src != removed && dst != removed)
  pure (Json.mkObj [("arch", ← run.getObjVal? "arch"),
    ("nodes", .arr (nodes.extract 1 nodes.size)), ("edges", .arr retained.toArray)])

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

private def checks : Except String (List String) := do
  let ebpfResponse := EBPF.exportEbpfBoundWordsSnapshot EBPF.justTxProgram ebpfMeta 60 60
  let ebpfSnapshot ← Json.parse ebpfResponse
  if (fieldString ebpfSnapshot "status").toOption != some "fail" ||
      (fieldString ebpfSnapshot "reason").toOption != some "Unsupported" then
    throw "eBPF fixture did not stop at the unsupported native helper"
  let failed ← (← ebpfSnapshot.getObjVal? "failed").getNat?
  let ebpfNodes ← fieldArray ebpfSnapshot "nodes"
  if !ebpfNodes.any (fun n => ((n.getObjVal? "id") >>= Json.getNat?).toOption == some failed &&
      (fieldString n "loc").toOption == some "36") then
    throw "eBPF fixture missing failed helper slot 36"
  let ebpf ← snapshotRun "ebpf" ebpfResponse
  -- Observed fixture/model frontier, not a comparison-interface property: the
  -- product wrapper binds all savedRegs to the entry-position term. In particular,
  -- x9's spill at index 3 has a source. RV32IMC now stops with UnboundTarget at
  -- index 34 (failed node 56), after producing 63 nodes and 62 edges.
  -- Unmarked eBPF reaches the unsupported native helper at raw slot 36.
  let rv32Response := RV32IMC.exportRv32BoundWordsSnapshot rv32Words rv32Meta 60 60
  let rv32Snapshot ← Json.parse rv32Response
  let rv32Status ← fieldString rv32Snapshot "status"
  let rv32Reason ← fieldString rv32Snapshot "reason"
  let rv32Failed ← (← rv32Snapshot.getObjVal? "failed").getNat?
  let rv32Nodes ← fieldArray rv32Snapshot "nodes"
  let rv32Edges ← fieldArray rv32Snapshot "edges"
  if rv32Status != "fail" || rv32Reason != "UnboundTarget" || rv32Failed != 56 ||
      rv32Nodes.size != 63 || rv32Edges.size != 62 then
    throw "RV32 fixture did not reach the observed bound-wrapper frontier"
  if !rv32Nodes.any (fun n => ((n.getObjVal? "id") >>= Json.getNat?).toOption == some rv32Failed &&
      (fieldString n "loc").toOption == some "34") then
    throw "RV32 fixture missing failed target slot 34"
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
  pure [s!"rv32imc-frontier: status={rv32Status} reason={rv32Reason} failed={rv32Failed} nodeCount={rv32Nodes.size} edgeCount={rv32Edges.size} loc=34",
    ← summary "identical-ebpf" self, ← summary "rv32imc-vs-ebpf" cross,
    cross.compress, ← summary "dropped-ebpf-node" dropped]

/-- Finite fixture diagnostics only; not imported by any library. -/
def main : IO UInt32 := do
  match checks with
  | .error detail => IO.eprintln ("CrossArchCheck failed: " ++ detail); pure 1
  | .ok lines =>
    for line in lines do IO.println line
    pure 0
