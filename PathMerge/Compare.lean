import PathMerge.Merge
import ClassifierExpr.Render

namespace PathMerge.RunCompare
open ClassifierExpr Lean

/-- Parsed snapshots retain opaque IDs only for endpoint resolution. -/
structure Run where
  arch : String
  nodes : List (Nat × Node)
  edges : List (Location × String × Location)

private def field (j : Json) (key label : String) : Except String Json :=
  (j.getObjVal? key).mapError (fun _ => "MissingOrInvalidField:" ++ label ++ "[" ++ key ++ "]")

private def stringField (j : Json) (key label : String) : Except String String := do
  (← field j key label).getStr?.mapError (fun _ => "MissingOrInvalidField:" ++ label ++ "[" ++ key ++ "]")

private def natField (j : Json) (key label : String) : Except String Nat := do
  (← field j key label).getNat?.mapError (fun _ => "MissingOrInvalidField:" ++ label ++ "[" ++ key ++ "]")

private def arrayField (j : Json) (key label : String) : Except String (Array Json) := do
  (← field j key label).getArr?.mapError (fun _ => "MissingOrInvalidField:" ++ label ++ "[" ++ key ++ "]")

private def parseRun (label : String) (j : Json) : Except String Run := do
  let arch ← stringField j "arch" label
  if arch.isEmpty then throw ("MissingOrInvalidField:" ++ label ++ "[arch]")
  let ns ← arrayField j "nodes" label
  let es ← arrayField j "edges" label
  if ns.isEmpty then throw ("EmptyRun:" ++ label)
  let mut nodes : List (Nat × Node) := []
  for k in [:ns.size] do
    let path := label ++ "[nodes][" ++ toString k ++ "]"
    let row := ns[k]!
    let id ← natField row "id" path
    if nodes.any (fun n => n.1 == id) then throw ("DuplicateNodeId:" ++ path)
    let text ← stringField row "loc" path
    let loc ← if text == "exit" then pure Location.exit else
      match text.toNat? with
      | some n => pure (.pos n)
      | none => throw ("InvalidLocation:" ++ path)
    let exprs ← arrayField row "exprs" path
    let predicates ← arrayField row "predicates" path
    let some state := parseSemStateJson (Json.arr exprs).compress (Json.arr predicates).compress
      | throw ("InvalidSnapshot:" ++ path)
    if !state.exprs.toList.all (fun e => ExactMerge.validRel e.reg.width e.rel && ExactMerge.validTerm e.term) then
      throw ("InvalidSnapshot:" ++ path)
    nodes := (id, ⟨loc, state⟩) :: nodes
  let mut edges := []
  for k in [:es.size] do
    let path := label ++ "[edges][" ++ toString k ++ "]"
    let row := es[k]!
    let src ← natField row "src" path
    let dst ← natField row "dst" path
    let dir ← stringField row "dir" path
    if !["OK", "Taken", "NotTaken"].contains dir then throw ("InvalidDirection:" ++ path)
    let some source := nodes.find? (fun n => n.1 == src) | throw ("UnknownEdgeEndpoint:" ++ path)
    let some target := nodes.find? (fun n => n.1 == dst) | throw ("UnknownEdgeEndpoint:" ++ path)
    edges := (source.2.loc, dir, target.2.loc) :: edges
  pure ⟨arch, nodes.reverse, edges.reverse⟩

private def unique [DecidableEq α] (xs : List α) : List α :=
  xs.foldl (fun acc x => if acc.any (fun y => decide (x = y)) then acc else x :: acc) []

private def difference [DecidableEq α] (xs ys : List α) : List α :=
  (unique xs).filter (fun x => !ys.any (fun y => decide (x = y)))

private def locText : Location → String
  | .pos n => toString n
  | .exit => "exit"

private def locLE : Location → Location → Bool
  | .pos a, .pos b => a ≤ b
  | .pos _, .exit => true
  | .exit, .pos _ => false
  | .exit, .exit => true

private def strings (xs : List String) : Json :=
  .arr ((unique xs).mergeSort (fun a b => a ≤ b) |>.map Json.str |>.toArray)

-- Rendering determines presentation order only; membership is always structural.
private def items (xs : List α) (render : α → String) : Json :=
  let texts := (xs.map render).mergeSort (fun a b => a ≤ b)
  .arr (texts.map (fun s => (Json.parse s).toOption.getD (.str s)) |>.toArray)

private def classReport [DecidableEq α] (name : String) (left right : List α)
    (render : α → String) : Json × Bool :=
  let left := unique left
  let right := unique right
  let equal := ExactMerge.sameSet left right
  let verdict := if equal then "Equal" else if left.isEmpty then "AbsentLeft"
    else if right.isEmpty then "AbsentRight" else "Differs"
  (Json.mkObj [("class", .str name), ("verdict", .str verdict),
    ("leftCount", toJson left.length), ("rightCount", toJson right.length),
    ("onlyLeft", items (difference left right) render),
    ("onlyRight", items (difference right left) render)], equal)

private def predicateClass : Predicate → String
  | .helper .. => "helper" | .branch .. => "branch" | .ret .. => "ret"
  | .mapWrite .. => "mapWrite" | .packetWrite .. => "packetWrite"

private def classes (left right : List Node) : List (Json × Bool) :=
  let values (ns : List Node) := ns.flatMap (fun n => n.state.exprs.entries)
  let constraints (ns : List Node) := ns.flatMap (fun n => n.state.exprs.constraints)
  let predicates (ns : List Node) := ns.flatMap (fun n => n.state.predicates)
  let constraintRenderer (e : Expr) := renderExprSetJson { entries := [], constraints := [e] }
  [classReport "valueBindings" (values left) (values right) renderExprJson,
   classReport "constraints" (constraints left) (constraints right) constraintRenderer] ++
    ["helper", "branch", "ret", "mapWrite", "packetWrite"].map (fun name =>
      classReport name ((predicates left).filter (fun p => predicateClass p == name))
        ((predicates right).filter (fun p => predicateClass p == name)) renderPredicateJson)

private def outgoing (run : Run) (loc : Location) : List String :=
  unique (run.edges.filterMap fun (src, dir, dst) =>
    if src == loc then some (dir ++ "->" ++ locText dst) else none)

private def positionReport (left right : Run) (loc : Location) : Json × Bool × Bool :=
  let ln := left.nodes.filterMap (fun (_, n) => if n.loc == loc then some n else none)
  let rn := right.nodes.filterMap (fun (_, n) => if n.loc == loc then some n else none)
  let coverage := ln.isEmpty || rn.isEmpty
  let verdict := if ln.isEmpty then "OnlyRight" else if rn.isEmpty then "OnlyLeft" else "Both"
  let base := [("loc", Json.str (locText loc)), ("verdict", .str verdict),
    ("leftNodes", toJson ln.length), ("rightNodes", toJson rn.length)]
  if coverage then (Json.mkObj base, false, true) else
    let le := outgoing left loc
    let re := outgoing right loc
    let edgesEqual := ExactMerge.sameSet le re
    let controlEqual := ln.length == rn.length && edgesEqual
    let control := Json.mkObj [("verdict", .str (if controlEqual then "Equal" else "Differs")),
      ("membersLeft", strings le), ("membersRight", strings re),
      ("onlyLeft", strings (difference le re)), ("onlyRight", strings (difference re le))]
    let cs := classes ln rn
    (Json.mkObj (base ++ [("control", control), ("classes", .arr (cs.map Prod.fst).toArray)]),
      controlEqual && cs.all Prod.snd, !edgesEqual)

private def summary (run : Run) : Json :=
  Json.mkObj [("arch", .str run.arch), ("nodeCount", toJson run.nodes.length),
    ("edgeCount", toJson run.edges.length)]

/-- Report equality of per-position unions, counts and outgoing position sets.
It does not establish a node-by-node bijection or behavioral equivalence. -/
def compare (requestJson : String) : Except String Json := do
  let j ← (Json.parse requestJson).mapError (fun e => "InvalidRequestJSON:" ++ e)
  let leftJson ← (j.getObjVal? "left").mapError (fun _ => "MissingOrInvalidField:left")
  let rightJson ← (j.getObjVal? "right").mapError (fun _ => "MissingOrInvalidField:right")
  let left ← parseRun "left" leftJson
  let right ← parseRun "right" rightJson
  let locations := (unique ((left.nodes ++ right.nodes).map (fun n => n.2.loc))).mergeSort locLE
  let positions := locations.map (positionReport left right)
  let coverage := positions.any (fun p => p.2.2)
  let equal := positions.all (fun p => p.2.1)
  pure (Json.mkObj [("status", .str "compared"), ("claim", .str "structural"),
    ("behavioralEquivalence", .str "notEstablished"),
    ("conclusion", .str (if coverage then "coverageDiffers" else if equal then "sameStructure" else "differs")),
    ("left", summary left), ("right", summary right),
    ("positions", .arr (positions.map Prod.fst).toArray),
    ("basis", strings ["doc/Expr/Expr.md#表达式分量", "doc/Predicate/谓词定义.md#类型与结构相等",
      "doc/NodeInference/路径合并FFI.md#比较规则", "doc/NodeInference/跨架构比较.md#控制与类别比较"]),
    ("openObligations", strings ["doc/NodeInference/跨架构比较.md#输入与对应假设",
      "doc/NodeInference/Jump/证明义务-路径合并完备.md#定理一精确配置共享判据的完备性",
      "doc/NodeInference/Jump/证明义务-路径合并完备.md#定理二相等末配置的有限深度后续一致性",
      "doc/NodeInference/Jump/证明义务-路径合并完备.md#充分性前提",
      "doc/NodeInference/Jump/路径合并-接口契约.md#未决义务",
      "doc/NodeInference/History.md#控制流与记录来源", "doc/NodeInference/History.md#完整依赖提取",
      "doc/NodeInference/History.md#局部结果顺序与重复事件",
      "doc/Predicate/Branch谓词.md#待证明义务", "doc/NodeInference/路径合并FFI.md#语义范围与证据边界"])])

end PathMerge.RunCompare

namespace PathMerge

/-- Boxed Lean String ABI; validate both entire runs before emitting a report. -/
@[export lean_compare_run_same_diff]
def exportCompareRunSameDiff (requestJson : String) : String :=
  match RunCompare.compare requestJson with
  | .error detail => ExactMerge.rejectJson detail
  | .ok report => report.compress

private def compareNode (id : Nat) (loc : String) (term : Nat := 0) : Lean.Json :=
  Lean.Json.mkObj [("id", Lean.toJson id), ("loc", .str loc), ("exprs", .arr #[]),
    ("predicates", .arr #[(Lean.Json.parse (ClassifierExpr.renderPredicateJson
      (.ret (ClassifierExpr.Term.C32 term)))).toOption.getD .null])]

private def compareRun (nodes : Array Lean.Json) (edges : Array Lean.Json := #[]) : Lean.Json :=
  Lean.Json.mkObj [("arch", .str "fixture"), ("nodes", .arr nodes), ("edges", .arr edges)]

private def compareRequest (left right : Lean.Json) : String :=
  (Lean.Json.mkObj [("left", left), ("right", right)]).compress

private def compareEdge (src dst : Nat) (dir : String := "OK") : Lean.Json :=
  Lean.Json.mkObj [("src", Lean.toJson src), ("dst", Lean.toJson dst), ("dir", .str dir)]

private def compareFixture := compareRun #[compareNode 0 "0", compareNode 1 "exit"]
private def compareSelf := compareRequest compareFixture compareFixture
private def compareDrop := compareRun #[compareNode 0 "0"]

private def comparisonField (request key : String) : Option String :=
  ((Lean.Json.parse (exportCompareRunSameDiff request)) >>= (fun j => j.getObjVal? key) >>=
    Lean.Json.getStr?).toOption

private def compareRejects (request tag : String) : Bool :=
  comparisonField request "status" == some "reject" &&
  comparisonField request "reason" == some "InsufficientEvidence" &&
  (comparisonField request "detail").any (fun s => s.startsWith tag)

private def classMutationCheck : Bool :=
  let request := compareRequest compareFixture (compareRun #[compareNode 0 "0" 1, compareNode 1 "exit"])
  let result := exportCompareRunSameDiff request
  comparisonField request "conclusion" == some "differs" &&
    result.contains "\"verdict\":\"Differs\"" &&
    result.contains "\"onlyRight\":[{\"kind\":\"ret\",\"term\":\"1\",\"width\":32}]"
    && (exportCompareRunSameDiff (compareRequest
      (compareRun #[compareNode 0 "0" 1, compareNode 1 "exit"]) compareFixture)).contains
        "\"onlyLeft\":[{\"kind\":\"ret\",\"term\":\"1\",\"width\":32}]"

private def coverageSwapCheck : Bool :=
  let l := compareRequest compareFixture compareDrop
  let r := compareRequest compareDrop compareFixture
  comparisonField l "conclusion" == some "coverageDiffers" &&
  comparisonField r "conclusion" == some "coverageDiffers" &&
  (exportCompareRunSameDiff l).contains "\"verdict\":\"OnlyLeft\"" &&
  (exportCompareRunSameDiff r).contains "\"verdict\":\"OnlyRight\""

private def addedEdgeCheck : Bool :=
  let request := compareRequest compareFixture
    (compareRun #[compareNode 0 "0", compareNode 1 "exit"] #[compareEdge 0 1])
  let result := exportCompareRunSameDiff request
  comparisonField request "conclusion" == some "coverageDiffers" &&
    result.contains "\"verdict\":\"Differs\"" && result.contains "\"onlyRight\":[\"OK->exit\"]"
    && (exportCompareRunSameDiff (compareRequest
      (compareRun #[compareNode 0 "0", compareNode 1 "exit"] #[compareEdge 0 1])
      compareFixture)).contains "\"onlyLeft\":[\"OK->exit\"]"

#guard comparisonField compareSelf "conclusion" == some "sameStructure"
#guard comparisonField compareSelf "claim" == some "structural"
#guard comparisonField compareSelf "behavioralEquivalence" == some "notEstablished"
#guard classMutationCheck
#guard coverageSwapCheck
#guard addedEdgeCheck
#guard compareRejects "{" "InvalidRequestJSON:"
#guard compareRejects "{}" "MissingOrInvalidField:"
#guard compareRejects (compareRequest (compareRun #[compareNode 0 "bad"]) compareFixture) "InvalidLocation:left[nodes][0]"
#guard compareRejects (compareRequest (compareRun #[(Lean.Json.parse "{\"id\":0,\"loc\":\"0\",\"exprs\":[{}],\"predicates\":[]}").toOption.getD .null]) compareFixture) "InvalidSnapshot:left[nodes][0]"
#guard compareRejects (compareRequest (compareRun #[compareNode 0 "0", compareNode 0 "exit"]) compareFixture) "DuplicateNodeId:left[nodes][1]"
#guard compareRejects (compareRequest (compareRun #[compareNode 0 "0"] #[compareEdge 0 0 "bad"]) compareFixture) "InvalidDirection:left[edges][0]"
#guard compareRejects (compareRequest (compareRun #[compareNode 0 "0"] #[compareEdge 0 1]) compareFixture) "UnknownEdgeEndpoint:left[edges][0]"
#guard compareRejects (compareRequest (compareRun #[]) compareFixture) "EmptyRun:left"
#guard exportCompareRunSameDiff compareSelf == exportCompareRunSameDiff compareSelf

end PathMerge
