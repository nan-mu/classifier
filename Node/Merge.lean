import Node.Path
import Core.Update
import Core.Parse

namespace Node.ExactMerge
open Core

-- Compare the AST itself with proof-backed equality, not the existing BEq instances
-- or rendered strings. Lean's DecidableEq deriving handler does not support the
-- nested List Term constructor; recurse explicitly through the AST and argument list.
mutual
  private def termDecEq : (a b : Term) → Decidable (a = b)
    | .const w c, .const v d =>
      if hw : w = v then
        if hc : c = d then .isTrue (by cases hw; cases hc; rfl)
        else .isFalse (by intro h; cases h; exact hc rfl)
      else .isFalse (by intro h; cases h; exact hw rfl)
    | .var w x, .var v y =>
      if hw : w = v then
        if hx : x = y then .isTrue (by cases hw; cases hx; rfl)
        else .isFalse (by intro h; cases h; exact hx rfl)
      else .isFalse (by intro h; cases h; exact hw rfl)
    | .regVar e r, .regVar f s =>
      if he : e = f then
        if hr : r = s then .isTrue (by cases he; cases hr; rfl)
        else .isFalse (by intro h; cases h; exact hr rfl)
      else .isFalse (by intro h; cases h; exact he rfl)
    | .app w op args, .app v other terms =>
      if hw : w = v then
        if ho : op = other then
          let inst : Decidable (args = terms) := termsDecEq args terms
          if ha : args = terms then .isTrue (by cases hw; cases ho; cases ha; rfl)
          else .isFalse (by intro h; cases h; exact ha rfl)
        else .isFalse (by intro h; cases h; exact ho rfl)
      else .isFalse (by intro h; cases h; exact hw rfl)
    | .const .., .var .. | .const .., .regVar .. | .const .., .app ..
    | .var .., .const .. | .var .., .regVar .. | .var .., .app ..
    | .regVar .., .const .. | .regVar .., .var .. | .regVar .., .app ..
    | .app .., .const .. | .app .., .var .. | .app .., .regVar .. =>
      .isFalse (by intro h; cases h)
  termination_by a _ => sizeOf a

  private def termsDecEq : (as bs : List Term) → Decidable (as = bs)
    | [], [] => .isTrue rfl
    | a :: as, b :: bs =>
      let headInst : Decidable (a = b) := termDecEq a b
      if hh : a = b then
        let tailInst : Decidable (as = bs) := termsDecEq as bs
        if ht : as = bs then .isTrue (by cases hh; cases ht; rfl)
        else .isFalse (by intro h; cases h; exact ht rfl)
      else .isFalse (by intro h; cases h; exact hh rfl)
    | [], _ :: _ | _ :: _, [] => .isFalse (by intro h; cases h)
  termination_by as _ => sizeOf as
end

private instance : DecidableEq Core.Term := termDecEq
deriving instance DecidableEq for Core.Expr
deriving instance DecidableEq for Core.HelperKind
deriving instance DecidableEq for Core.Cond
deriving instance DecidableEq for Core.Predicate

def sameSet [DecidableEq α] (xs ys : List α) : Bool :=
  xs.all (fun x => ys.any (fun y => decide (x = y))) &&
    ys.all (fun y => xs.any (fun x => decide (y = x)))

/-- Exact equality of the current representation: location and both Expr roles,
then all five observation classes by membership. Set order and predicate multiplicity
do not matter; argument/key order, event identity, widths, operators and all AST children do matter.
The parser still requires unique value keys and structurally unique constraints. -/
def sameConfig (a b : Node) : Bool :=
  decide (a.loc = b.loc) &&
    sameSet a.state.exprs b.state.exprs &&
    sameSet a.state.exprs.constraints b.state.exprs.constraints &&
    sameSet a.state.predicates b.state.predicates

private def field (j : Lean.Json) (key : String) : Except String Lean.Json :=
  (j.getObjVal? key).mapError (fun _ => "MissingOrInvalidField:" ++ key)

private def natField (j : Lean.Json) (key : String) : Except String Nat := do
  (← field j key).getNat?.mapError (fun _ => "MissingOrInvalidField:" ++ key)

private def stringField (j : Lean.Json) (key : String) : Except String String := do
  (← field j key).getStr?.mapError (fun _ => "MissingOrInvalidField:" ++ key)

private def arrayField (j : Lean.Json) (key : String) : Except String (Array Lean.Json) := do
  (← field j key).getArr?.mapError (fun _ => "MissingOrInvalidField:" ++ key)

private def boundedWidth (q bits : Nat) : Bool := 0 < q && q ≤ bits

/-- Snapshot value terms use the same structural carrier/arity contract as
predicate terms, including cross-carrier projections and native helper results. -/
def validTerm (t : Term) : Bool := predicateWellFormed (.ret t)

def validRel (w : Width) : Rel → Bool
  | .eqN q | .neN q | .ltuN q | .leuN q | .gtuN q | .geuN q
  | .ltsN q | .lesN q | .gtsN q | .gesN q | .bitsnz q | .bitsz q =>
    boundedWidth q w.bits
  | _ => true


private def snapshot (label : String) (j : Lean.Json) :
    Except String (Nat × Node) := do
  let id ← natField j "id"
  let locText ← stringField j "loc"
  let loc ← if locText == "exit" then pure Location.exit else
    match locText.toNat? with
    | some n => pure (.pos n)
    | none => throw ("InvalidLocation:" ++ label)
  let exprs ← arrayField j "exprs"
  let predicates ← arrayField j "predicates"
  let parsedPredicates ← predicates.toList.mapM fun p => do
    let kind ← stringField p "kind"
    if !["helper", "branch", "ret", "mapWrite", "packetWrite"].contains kind then
      throw ("UnsupportedPredicateKind:" ++ label ++ ":" ++ kind)
    -- parsePredicateJson applies predicateWellFormed for every recognized class.
    let some predicate := parsePredicateJson p | throw ("InvalidPredicate:" ++ label)
    pure predicate
  let some state := parseStateJson (Lean.Json.arr exprs).compress "[]" |
    throw ("InvalidSnapshot:" ++ label)
  if !state.exprs.all (fun e => validRel (Width.ofBits e.reg.bits) e.rel && validTerm e.term) then
    throw ("InvalidTerm:" ++ label)
  pure (id, ⟨loc, { exprs := state.exprs, predicates := parsedPredicates }⟩)

/-- Validate all evidence before selecting the first exactly equal ordered suffix entry.
Snapshots are already-applied global states. Position validity, common origin, history,
reusable-suffix validity and coverage certificates remain the caller's obligations. -/
def select (requestJson : String) : Except String (Nat × Nat) := do
  let j ← (Lean.Json.parse requestJson).mapError (fun e => "InvalidRequestJSON:" ++ e)
  let model ← stringField j "observationModel"
  if model != "HelperOnly" && model != "FiveClass" then
    throw ("UnsupportedObservationModel:" ++ model)
  let requirements ← arrayField j "requiredObservations"
  for value in requirements do
    let name ← value.getStr?.mapError (fun _ => "MissingOrInvalidField:requiredObservations")
    if !(if model == "HelperOnly" then name == "Helper"
        else ["Helper", "Branch", "Return", "MapWrite", "PacketWrite"].contains name) then
      throw ("UnsupportedRequiredObservation:" ++ name)
  let (takenId, taken) ← snapshot "taken" (← field j "taken")
  let candidates ← arrayField j "notTaken"
  if candidates.isEmpty then throw "EmptyNotTaken"
  let mut ids := [takenId]
  let mut parsed : Array (Nat × Node) := #[]
  for k in [:candidates.size] do
    let (id, node) ← snapshot ("notTaken[" ++ toString k ++ "]") candidates[k]!
    if ids.contains id then throw "DuplicateNodeId"
    ids := id :: ids
    parsed := parsed.push (id, node)
  for (id, node) in parsed do
    if sameConfig taken node then return (id, takenId)
  throw "NoExactConfigMatch"

/-- Every rejection is an evidence gap. Structural inequality is not a proved
counterexample to behavioral equivalence, so this oracle never emits Counterexample. -/
def rejectJson (detail : String) : String :=
  (Lean.Json.mkObj [("status", .str "reject"), ("reason", .str "InsufficientEvidence"),
    ("detail", .str detail)]).compress

def mergedJson (reuseFrom taken : Nat) : String :=
  (Lean.Json.mkObj [("status", .str "merged"), ("scope", .str "ExactConfig"),
    ("reuseFrom", Lean.toJson reuseFrom), ("taken", Lean.toJson taken)]).compress

end Node.ExactMerge

namespace Node
open Core

/-- Stateless exact-config oracle over the five-class structural representation.
HelperOnly remains a legacy declaration accepting only Helper requirements; it never
projects supplied states. FiveClass accepts requirements for all five classes.
GLOBAL configurations carry opaque natural IDs. Location uses a zero-based nonnegative
decimal string or `exit`, with program validity owned by the runtime.
All candidates validate before the first equal ordered NotTaken entry is selected.
No state is rewritten and no instruction is executed.

`scope: ExactConfig` proves only equality in this representation. Authentic history,
common program/semantic context, branch origin, suffix validity and e_N/e_T/e_M remain
external obligations. Declared requirements do not prove observation completeness.
Malformed evidence and unequal configs reject with InsufficientEvidence; this export
produces neither a behavioral Counterexample nor an Escape certificate.

C ABI: boxed Lean request String → boxed Lean JSON String. -/
@[export lean_expand_merge]
def exportExpandMerge (requestJson : String) : String :=
  match ExactMerge.select requestJson with
  | .error detail => ExactMerge.rejectJson detail
  | .ok (reuseFrom, taken) => ExactMerge.mergedJson reuseFrom taken

private def mergeSnapshotFixture (id : Nat) (loc : String := "1")
    (exprs preds : String := "[]") : String :=
  s!"\{\"id\":{id},\"loc\":\"{loc}\",\"exprs\":{exprs},\"predicates\":{preds}}"

private def mergeRequestFixture (taken candidates : String)
    (requirements : String := "[\"Helper\"]") (model : String := "HelperOnly") : String :=
  s!"\{\"observationModel\":\"{model}\",\"requiredObservations\":{requirements},\"taken\":{taken},\"notTaken\":[{candidates}]}"

private def mergeOutputField (response key : String) : Option String :=
  ((Lean.Json.parse response) >>= (fun j => j.getObjVal? key) >>= Lean.Json.getStr?).toOption

private def mergeRejectedResponse (response : String) : Bool :=
  mergeOutputField response "status" == some "reject" &&
    mergeOutputField response "reason" == some "InsufficientEvidence"

private def mergeRejects (request : String) (detail : String) : Bool :=
  let result := exportExpandMerge request
  mergeRejectedResponse result &&
    (mergeOutputField result "detail").any (fun text => text.startsWith detail)

private def mergeEqualRequestFixture : String :=
  mergeRequestFixture (mergeSnapshotFixture 42)
    (mergeSnapshotFixture 16 "2" ++ "," ++ mergeSnapshotFixture 17 ++ "," ++ mergeSnapshotFixture 18)

private def mergeEqualCheck : Bool :=
  let response := exportExpandMerge mergeEqualRequestFixture
  mergeOutputField response "status" == some "merged" &&
    mergeOutputField response "scope" == some "ExactConfig" &&
    (((Lean.Json.parse response) >>= (fun j => j.getObjVal? "reuseFrom") >>=
      Lean.Json.getNat?).toOption == some 17) &&
    (((Lean.Json.parse response) >>= (fun j => j.getObjVal? "taken") >>=
      Lean.Json.getNat?).toOption == some 42)

private def mergeExprFixture (term : String := "4") (role : String := "") : String :=
  s!"\{\"reg\":\"real:10:[0,32)\",\"rel\":\"eq\",\"term\":\"{term}\"{role}}"

private def mergePredicateFixture (event : Nat := 7) (id : Nat := 5)
    (args : String := "[]") : String :=
  s!"\{\"kind\":\"helper\",\"event\":{event},\"helperId\":{id},\"args\":{args}}"

private def mergeSetOrderCheck : Bool :=
  let value := mergeExprFixture
  let constraint := mergeExprFixture "9" ",\"role\":\"constraint\""
  let secondConstraint := mergeExprFixture "8" ",\"role\":\"constraint\""
  let other := "{\"reg\":\"real:11:[0,32)\",\"rel\":\"eq\",\"term\":\"v32:11\"}"
  let p := mergePredicateFixture 7
  let q := mergePredicateFixture 8
  let taken := mergeSnapshotFixture 42 "1"
    ("[" ++ value ++ "," ++ other ++ "," ++ constraint ++ "," ++ secondConstraint ++ "]")
    ("[" ++ p ++ "," ++ q ++ "]")
  let candidate := mergeSnapshotFixture 17 "1"
    ("[" ++ secondConstraint ++ "," ++ constraint ++ "," ++ other ++ "," ++ value ++ "]")
    ("[" ++ q ++ "," ++ p ++ "," ++ p ++ "]")
  mergeOutputField (exportExpandMerge (mergeRequestFixture taken candidate)) "status" == some "merged"

private def mergeDifferentLocationRequestFixture : String :=
  let value := "[" ++ mergeExprFixture ++ "]"
  mergeRequestFixture (mergeSnapshotFixture 42 "1" value)
    (mergeSnapshotFixture 17 "2" value)

private def mergeStateBoundaryCheck : Bool :=
  let value := "[" ++ mergeExprFixture ++ "]"
  let taken := mergeSnapshotFixture 42 "1" value
  mergeRejects mergeDifferentLocationRequestFixture "NoExactConfigMatch" &&
  [mergeSnapshotFixture 17 "exit" value,
    mergeSnapshotFixture 17 "1" ("[" ++ mergeExprFixture "5" ++ "]"),
    mergeSnapshotFixture 17 "1" ("[" ++ mergeExprFixture "add32(2,2)" ++ "]"),
    mergeSnapshotFixture 17 "1"
      ("[" ++ mergeExprFixture ++ "," ++ mergeExprFixture "9" ",\"role\":\"constraint\"" ++ "]"),
    mergeSnapshotFixture 17 "1" "[{\"reg\":\"real:10:[0,64)\",\"rel\":\"eq\",\"term\":\"4\"}]",
    mergeSnapshotFixture 17 "1" value ("[" ++ mergePredicateFixture ++ "]")].all
    (fun candidate => mergeRejects (mergeRequestFixture taken candidate) "NoExactConfigMatch") &&
  mergeRejects (mergeRequestFixture
    (mergeSnapshotFixture 42 "1" "[]" ("[" ++ mergePredicateFixture 7 ++ "]"))
    (mergeSnapshotFixture 17 "1" "[]" ("[" ++ mergePredicateFixture 8 ++ "]"))) "NoExactConfigMatch" &&
  mergeRejects (mergeRequestFixture
    (mergeSnapshotFixture 42 "1" "[]" ("[" ++ mergePredicateFixture 7 5 ++ "]"))
    (mergeSnapshotFixture 17 "1" "[]" ("[" ++ mergePredicateFixture 7 999 ++ "]"))) "NoExactConfigMatch" &&
  mergeRejects (mergeRequestFixture
    (mergeSnapshotFixture 42 "1" "[]" ("[" ++ mergePredicateFixture 7 1 "[\"1\",\"2\"]" ++ "]"))
    (mergeSnapshotFixture 17 "1" "[]" ("[" ++ mergePredicateFixture 7 1 "[\"2\",\"1\"]" ++ "]")))
    "NoExactConfigMatch" &&
  mergeRejects (mergeRequestFixture
    (mergeSnapshotFixture 42 "1" "[]" ("[" ++ mergePredicateFixture 7 5 "[\"1\"]" ++ "]"))
    (mergeSnapshotFixture 17 "1" "[]" ("[" ++ mergePredicateFixture 7 5 "[]" ++ "]")))
    "NoExactConfigMatch"

/-- Malformed evidence must reject, independently of which validation layer detects it.
In particular, parseTerm rejects mixed-carrier applications before snapshot's final
term check; the internal diagnostic is not the rejection contract. Snapshot cases
include an earlier valid exact match, so accepting invalid evidence would merge
rather than merely reject on inequality. Labels identify each input in the report. -/
private def mergeMalformedCases : List (String × String) :=
  let taken := mergeSnapshotFixture 42
  let candidate := mergeSnapshotFixture 17
  let badValue := "[" ++ mergeExprFixture ++ "," ++ mergeExprFixture ++ "]"
  let constraint := mergeExprFixture "4" ",\"role\":\"constraint\""
  let withInvalidCandidate := fun invalid =>
    mergeRequestFixture taken (mergeSnapshotFixture 16 ++ "," ++ invalid)
  [
    ("invalidJSON", "{"),
    ("missingFields", "{}"),
    ("emptyCandidates", mergeRequestFixture taken ""),
    ("takenIdRepeated", withInvalidCandidate (mergeSnapshotFixture 42)),
    ("candidateIdRepeated",
      withInvalidCandidate (candidate ++ "," ++ mergeSnapshotFixture 17)),
    ("invalidLocationAfterMatch",
      withInvalidCandidate (candidate ++ "," ++ mergeSnapshotFixture 18 "-1")),
    ("duplicateValueAfterMatch",
      withInvalidCandidate (candidate ++ "," ++ mergeSnapshotFixture 18 "1" badValue)),
    ("duplicateValue", withInvalidCandidate (mergeSnapshotFixture 17 "1" badValue)),
    ("duplicateConstraint", withInvalidCandidate
      (mergeSnapshotFixture 17 "1" ("[" ++ constraint ++ "," ++ constraint ++ "]"))),
    ("packet64Register", withInvalidCandidate
      (mergeSnapshotFixture 17 "1" "[{\"reg\":\"packet64:0\",\"rel\":\"eq\",\"term\":\"1\"}]")),
    ("mixedCarrierValue", withInvalidCandidate
      (mergeSnapshotFixture 17 "1" ("[" ++ mergeExprFixture "add32(v64:1,2)" ++ "]"))),
    ("relationBeyondCarrier", withInvalidCandidate
      (mergeSnapshotFixture 17 "1" "[{\"reg\":\"real:10:[0,32)\",\"rel\":\"eqN33\",\"term\":\"1\"}]")),
    ("mixedCarrierHelperArgs", withInvalidCandidate
      (mergeSnapshotFixture 17 "1" "[]" ("[" ++ mergePredicateFixture 7 1 "[\"v64:1\",\"2\"]" ++ "]"))),
    ("mixedCarrierHelperTerm", withInvalidCandidate
      (mergeSnapshotFixture 17 "1" "[]" ("[" ++ mergePredicateFixture 7 1 "[\"add32(v64:1,2)\"]" ++ "]"))),
    ("helperIdOverflow", withInvalidCandidate
      (mergeSnapshotFixture 17 "1" "[]" ("[" ++ mergePredicateFixture 7 4294967296 ++ "]"))),
    ("stringNodeId", withInvalidCandidate
      "{\"id\":\"17\",\"loc\":\"1\",\"exprs\":[],\"predicates\":[]}")
  ]

private def mergeMalformedCheck : Bool :=
  mergeMalformedCases.all fun (_, request) => mergeRejectedResponse (exportExpandMerge request)

private def mergeUnsupportedCheck : Bool :=
  let taken := mergeSnapshotFixture 42
  let candidate := mergeSnapshotFixture 17
  ["Branch", "Return", "MapWrite", "PacketWrite", "Unknown"].all
    (fun kind => mergeRejects (mergeRequestFixture taken candidate ("[\"" ++ kind ++ "\"]"))
      "UnsupportedRequiredObservation:") &&
  mergeRejects (mergeRequestFixture taken candidate "[\"Unknown\"]" "FiveClass")
    "UnsupportedRequiredObservation:" &&
  mergeRejects (mergeRequestFixture taken candidate "[\"Helper\"]" "Unknown")
    "UnsupportedObservationModel:" &&
  ["return", "cmp", "for", "unknown"].all
    (fun kind =>
      let unsupported := mergeSnapshotFixture 18 "1" "[]" ("[{\"kind\":\"" ++ kind ++ "\"}]")
      mergeRejects (mergeRequestFixture taken unsupported) "UnsupportedPredicateKind:" &&
      mergeRejects (mergeRequestFixture taken (candidate ++ "," ++ unsupported))
        ("UnsupportedPredicateKind:notTaken[1]:" ++ kind)) &&
  mergeRejects (mergeRequestFixture taken candidate "[32]") "MissingOrInvalidField:" &&
  mergeRejects (mergeRequestFixture taken candidate "null") "MissingOrInvalidField:"

private def mergeOpaqueIdsCheck : Bool :=
  let request := mergeRequestFixture (mergeSnapshotFixture 4294967297 "exit")
    (mergeSnapshotFixture 4294967298 "exit") "[]"
  let response := exportExpandMerge request
  mergeOutputField response "status" == some "merged" &&
    (((Lean.Json.parse response) >>= (fun j => j.getObjVal? "reuseFrom") >>=
      Lean.Json.getNat?).toOption == some 4294967298)

private def mergeSharedRepresentationCheck : Bool :=
  let state := "[{\"reg\":\"real:10:[0,64)\",\"rel\":\"eq\",\"term\":\"v64:1\"}," ++
    "{\"reg\":\"real:0:[0,32)\",\"rel\":\"eq\",\"term\":\"1\"}]"
  ["0", "4294967297", "exit"].all fun loc =>
    let taken := mergeSnapshotFixture 42 loc state
    let candidate := mergeSnapshotFixture 17 loc state
    mergeOutputField (exportExpandMerge (mergeRequestFixture taken candidate)) "status" == some "merged"

private def mergeOpaqueHelpersCheck : Bool :=
  let cases := [(1, "[]"), (5, "[\"1\",\"2\",\"3\"]"),
    (999, "[\"v32:1\",\"add32(1,2)\"]"), (4294967295, "[\"1\"]")]
  cases.all fun (id, args) =>
    let predicates := "[" ++ mergePredicateFixture 7 id args ++ "]"
    let taken := mergeSnapshotFixture 42 "1" "[]" predicates
    let candidate := mergeSnapshotFixture 17 "1" "[]" predicates
    mergeOutputField (exportExpandMerge (mergeRequestFixture taken candidate)) "status" == some "merged"

private def mergeReuses (request : String) (reuseFrom taken : Nat) : Bool :=
  let response := exportExpandMerge request
  mergeOutputField response "status" == some "merged" &&
    mergeOutputField response "scope" == some "ExactConfig" &&
    (((Lean.Json.parse response) >>= (fun j => j.getObjVal? "reuseFrom") >>=
      Lean.Json.getNat?).toOption == some reuseFrom) &&
    (((Lean.Json.parse response) >>= (fun j => j.getObjVal? "taken") >>=
      Lean.Json.getNat?).toOption == some taken)

private def mergeStateSnapshotFixture (id : Nat) (loc : String) (state : State) : String :=
  mergeSnapshotFixture id loc ("[" ++ renderExprsJson state.exprs ++ "]")
    ("[" ++ renderPredicatesJson state.predicates ++ "]")

private def mergeFiveClassRequirements : String :=
  "[\"Helper\",\"Branch\",\"Return\",\"MapWrite\",\"PacketWrite\"]"

private def mergeMixedPredicates : List Predicate :=
  [.helper 7 .clock [Term.C32 1],
   .branch 1 .taken ⟨Term.V32 1, .ltu, Term.C32 4⟩,
   .ret (Term.V64 2),
   .mapWrite 8 (Term.V64 3) [Term.C32 1, Term.C32 2] 0 32 (Term.V32 4),
   .packetWrite 9 0 32 (Term.V32 5)]

private def mergeMixedRequest (a b : List Predicate) (model : String := "FiveClass") : String :=
  mergeRequestFixture (mergeStateSnapshotFixture 42 "1" ⟨Expr.nil, a⟩)
    (mergeStateSnapshotFixture 17 "1" ⟨Expr.nil, b⟩)
    (if model == "HelperOnly" then "[\"Helper\"]" else mergeFiveClassRequirements) model

private def mergeMixedSetCheck : Bool :=
  let ps := mergeMixedPredicates
  mergeReuses (mergeMixedRequest ps (ps.reverse ++ ps)) 17 42 &&
    mergeReuses (mergeMixedRequest ps ps.reverse "HelperOnly") 17 42 &&
    let result := (update { exprs := [], predicates := [ps[0]!, ps[1]!] } { exprs := [], predicates := (ps.reverse ++ ps) }).predicates
    result == [ps[0]!, ps[1]!, ps[4]!, ps[3]!, ps[2]!] &&
      ExactMerge.sameConfig ⟨.pos 1, ⟨Expr.nil, result⟩⟩
        ⟨.pos 1, ⟨Expr.nil, ps⟩⟩

private def mergeChangedClassFieldCheck : Bool :=
  let branch := mergeMixedPredicates[1]!
  let mapWrite := mergeMixedPredicates[3]!
  let packetWrite := mergeMixedPredicates[4]!
  let cases : List (Predicate × List Predicate) := [
    (branch, [
      .branch 2 .taken ⟨Term.V32 1, .ltu, Term.C32 4⟩,
      .branch 1 .notTaken ⟨Term.V32 1, .ltu, Term.C32 4⟩,
      .branch 1 .taken ⟨Term.V32 2, .ltu, Term.C32 4⟩,
      .branch 1 .taken ⟨Term.V32 1, .leu, Term.C32 4⟩,
      .branch 1 .taken ⟨Term.V32 1, .ltu, Term.C32 5⟩,
      .branch 1 .taken ⟨Term.V64 1, .ltu, Term.C64 4⟩]),
    (.branch 1 .taken ⟨Term.V32 1, .ltuN 8, Term.C32 4⟩,
      [.branch 1 .taken ⟨Term.V32 1, .ltuN 16, Term.C32 4⟩]),
    (.ret (Term.V64 2), [.ret (Term.V64 3), .ret (Term.V32 2)]),
    (mapWrite, [
      .mapWrite 10 (Term.V64 3) [Term.C32 1, Term.C32 2] 0 32 (Term.V32 4),
      .mapWrite 8 (Term.V64 6) [Term.C32 1, Term.C32 2] 0 32 (Term.V32 4),
      .mapWrite 8 (Term.V32 3) [Term.C32 1, Term.C32 2] 0 32 (Term.V32 4),
      .mapWrite 8 (Term.V64 3) [Term.C32 2, Term.C32 1] 0 32 (Term.V32 4),
      .mapWrite 8 (Term.V64 3) [Term.C32 1] 0 32 (Term.V32 4),
      .mapWrite 8 (Term.V64 3) [Term.C32 1, Term.C32 2] 1 32 (Term.V32 4),
      .mapWrite 8 (Term.V64 3) [Term.C32 1, Term.C32 2] 0 16 (Term.V32 4),
      .mapWrite 8 (Term.V64 3) [Term.C32 1, Term.C32 2] 0 32 (Term.V32 6),
      .mapWrite 8 (Term.V64 3) [Term.C32 1, Term.C32 2] 0 32 (Term.V64 4)]),
    (packetWrite, [
      .packetWrite 10 0 32 (Term.V32 5),
      .packetWrite 9 1 32 (Term.V32 5),
      .packetWrite 9 0 16 (Term.V32 5),
      .packetWrite 9 0 32 (Term.V32 6),
      .packetWrite 9 0 32 (Term.V64 5)])]
  cases.all fun (original, variants) =>
    variants.all fun changed =>
      let a := mergeMixedPredicates ++ [original]
      let b := mergeMixedPredicates.filter (· != original) ++ [changed]
      mergeRejects (mergeMixedRequest a b) "NoExactConfigMatch" &&
        mergeRejects (mergeMixedRequest a b "HelperOnly") "NoExactConfigMatch"

private def mergeMalformedMixedCases : List (String × String) :=
  let valid := mergeSnapshotFixture 42
  let badRows := [
    ("branchZeroPosition",
      "{\"kind\":\"branch\",\"position\":0,\"dir\":\"taken\",\"width\":32,\"cond\":{\"lhs\":\"1\",\"rel\":\"eq\",\"rhs\":\"1\"}}"),
    ("branchInvalidDirection",
      "{\"kind\":\"branch\",\"position\":1,\"dir\":\"ok\",\"width\":32,\"cond\":{\"lhs\":\"1\",\"rel\":\"eq\",\"rhs\":\"1\"}}"),
    ("branchCarrierMismatch",
      "{\"kind\":\"branch\",\"position\":1,\"dir\":\"taken\",\"width\":32,\"cond\":{\"lhs\":\"v64:1\",\"rel\":\"eq\",\"rhs\":\"1\"}}"),
    ("branchRelationBeyondCarrier",
      "{\"kind\":\"branch\",\"position\":1,\"dir\":\"taken\",\"width\":32,\"cond\":{\"lhs\":\"1\",\"rel\":\"eqN33\",\"rhs\":\"1\"}}"),
    ("returnUnsupportedWidth", "{\"kind\":\"ret\",\"width\":16,\"term\":\"1\"}"),
    ("returnCarrierMismatch", "{\"kind\":\"ret\",\"width\":64,\"term\":\"v32:1\"}"),
    ("mapKeyCarrierMismatch",
      "{\"kind\":\"mapWrite\",\"event\":8,\"mapWidth\":32,\"map\":\"1\",\"key\":[\"v64:1\"],\"offset\":0,\"sourceWidth\":32,\"source\":\"1\"}"),
    ("mapKeyByteOverflow",
      "{\"kind\":\"mapWrite\",\"event\":8,\"mapWidth\":32,\"map\":\"1\",\"key\":[\"256\"],\"offset\":0,\"sourceWidth\":32,\"source\":\"1\"}"),
    ("packetSourceMixedCarrier",
      "{\"kind\":\"packetWrite\",\"event\":9,\"offset\":0,\"width\":32,\"source\":\"add32(v64:1,2)\"}"),
    ("packetMissingSource",
      "{\"kind\":\"packetWrite\",\"event\":9,\"offset\":0,\"width\":32}")]
  badRows.map fun (name, row) =>
    let invalid := mergeSnapshotFixture 18 "1" "[]" ("[" ++ row ++ "]")
    -- All snapshots validate, even after an earlier equal candidate.
    (name, mergeRequestFixture valid (mergeSnapshotFixture 17 ++ "," ++ invalid)
      mergeFiveClassRequirements "FiveClass")

private def mergeMalformedMixedCheck : Bool :=
  mergeMalformedMixedCases.all fun (_, request) => mergeRejectedResponse (exportExpandMerge request)

-- Reduced just_drop.elf diamond: outer branch node 12 has Taken descendants
-- 27 -> 30 and NotTaken descendants 28 -> 31. Wire locations are zero-based.
-- Retain a representative shared binding and both shared comparisons; the other
-- identical rows are elided only in this fixture, never projected by the oracle.
-- This diagnoses oracle behavior, not runtime scheduling or full-observation reuse.
private def mergeJustDropOverwriteCheck : Bool :=
  let a3 := Reg.real32 13
  let common := ((update ⟨Expr.nil, []⟩ { exprs := [Expr.mkEq (Reg.real32 27) (solve (Term.V32 59))], predicates := [] }).exprs)
    |> (fun acc => (let row := solveExpr (Expr.mkRel (Reg.real32 10) .geu
      (addStar .w32 (Term.V32 4) (Term.C32 14))); if acc.contains row then acc else acc ++ [row]))
    |> (fun acc => (let row := solveExpr (Expr.mkRel (Reg.real32 10) .geu
      (addStar .w32 (Term.V32 4) (Term.C32 18))); if acc.contains row then acc else acc ++ [row]))
  let taken : State := ⟨(update ⟨common, []⟩ { exprs := [Expr.mkEq a3 (solve (Term.C32 43144))], predicates := [] }).exprs, []⟩
  let notTaken : State := ⟨(update ⟨common, []⟩ { exprs := [Expr.mkEq a3 (solve (Term.C32 129))], predicates := [] }).exprs, []⟩
  -- ADDI a3,zero,18 at wire loc17 contributes this local value effect.
  let localExprs := (update ⟨Expr.nil, []⟩ { exprs := [Expr.mkEq a3 (solve (Term.C32 18))], predicates := [] }).exprs
  let takenAfter := update taken { exprs := localExprs, predicates := [] }
  let notTakenAfter := update notTaken { exprs := localExprs, predicates := [] }
  let beforeRequest := mergeRequestFixture (mergeStateSnapshotFixture 27 "17" taken)
      (mergeStateSnapshotFixture 28 "17" notTaken)
    let afterRequest := mergeRequestFixture (mergeStateSnapshotFixture 30 "18" takenAfter)
      (mergeStateSnapshotFixture 31 "18" notTakenAfter)
    mergeRejects beforeRequest "NoExactConfigMatch" &&
      takenAfter.exprs.lookupEq a3 == some (Term.C32 18) &&
      notTakenAfter.exprs.lookupEq a3 == some (Term.C32 18) &&
      takenAfter.exprs.constraints == common.constraints &&
      notTakenAfter.exprs.constraints == common.constraints &&
      takenAfter.exprs.lookupEq (Reg.real32 27) == some (Term.V32 59) &&
      notTakenAfter.exprs.lookupEq (Reg.real32 27) == some (Term.V32 59) &&
      takenAfter.predicates.isEmpty && notTakenAfter.predicates.isEmpty &&
      mergeReuses afterRequest 31 30

-- Equal values and empty Helper sets do not erase complementary constraints.
-- Only an actual local assignment to the compared register invalidates them.
private def mergeComplementaryOverwriteCheck : Bool :=
  let compared := Reg.real32 13
  let other := Reg.real32 27
  let common := ((update ⟨Expr.nil, []⟩ { exprs := [Expr.mkEq compared (solve (Term.V32 13))], predicates := [] }).exprs)
    |> (fun acc => (update ⟨acc, []⟩ { exprs := [Expr.mkEq other (solve (Term.V32 59))], predicates := [] }).exprs)
    |> (fun acc => (let row := solveExpr (Expr.mkRel other .geu (Term.C32 1)); if acc.contains row then acc else acc ++ [row]))
  [Rel.eq, .ltu].all fun rel =>
    let condition := Expr.mkRel compared rel (Term.C32 10)
    let complement := Expr.mkRel compared rel.compl (Term.C32 10)
    let taken : State := ⟨(let row := solveExpr condition; if common.contains row then common else common ++ [row]), []⟩
    let notTaken : State := ⟨(let row := solveExpr complement; if common.contains row then common else common ++ [row]), []⟩
    let request (a b : State) := mergeRequestFixture (mergeStateSnapshotFixture 42 "17" a)
      (mergeStateSnapshotFixture 17 "17" b)
    let overwrite := (update ⟨Expr.nil, []⟩ { exprs := [Expr.mkEq compared (solve (Term.C32 18))], predicates := [] }).exprs
    let unrelated := (update ⟨Expr.nil, []⟩ { exprs := [Expr.mkEq other (solve (Term.C32 0))], predicates := [] }).exprs
    let takenAfter := update taken { exprs := overwrite, predicates := [] }
    let notTakenAfter := update notTaken { exprs := overwrite, predicates := [] }
    let takenUnrelated := update taken { exprs := unrelated, predicates := [] }
    let notTakenUnrelated := update notTaken { exprs := unrelated, predicates := [] }
    let afterRequest := mergeRequestFixture (mergeStateSnapshotFixture 43 "18" takenAfter)
        (mergeStateSnapshotFixture 18 "18" notTakenAfter)
    taken.exprs.bindings == notTaken.exprs.bindings &&
        taken.predicates.isEmpty && notTaken.predicates.isEmpty &&
        mergeRejects (request taken notTaken) "NoExactConfigMatch" &&
        mergeRejects (request takenUnrelated notTakenUnrelated) "NoExactConfigMatch" &&
        takenAfter.exprs.constraints == common.constraints &&
        notTakenAfter.exprs.constraints == common.constraints &&
        takenAfter.exprs.lookupEq compared == some (Term.C32 18) &&
        notTakenAfter.exprs.lookupEq compared == some (Term.C32 18) &&
        mergeReuses afterRequest 18 43

-- Consumer-visible wire regressions; finite guards are not general semantic proofs.
#guard mergeEqualCheck
#guard mergeSetOrderCheck
#guard mergeStateBoundaryCheck
#guard mergeMalformedCheck
#guard mergeUnsupportedCheck
#guard mergeOpaqueIdsCheck
#guard mergeSharedRepresentationCheck
#guard mergeOpaqueHelpersCheck
#guard mergeJustDropOverwriteCheck
#guard mergeComplementaryOverwriteCheck
#guard mergeMixedSetCheck
#guard mergeChangedClassFieldCheck
#guard mergeMalformedMixedCheck

/-- Execute finite wire regressions, including mixed-class equality, field sensitivity,
and individually labeled malformed inputs. This does not establish general instruction
semantics, runtime scheduling, full-observation merge, or the caller's history and suffix
certificates. The standalone main lives in `MergeCheck.lean`, outside the library imports. -/
def runMergeChecks : IO UInt32 := do
  IO.println "Merge finite behavior regressions (not a general semantic proof)."
  IO.println s!"ExactConfig response: {exportExpandMerge mergeEqualRequestFixture}"
  IO.println s!"NoExactConfigMatch response: {exportExpandMerge mergeDifferentLocationRequestFixture}"
  let checks : List (String × Bool) := [
    ("mergeEqualCheck", mergeEqualCheck),
    ("mergeSetOrderCheck", mergeSetOrderCheck),
    ("mergeStateBoundaryCheck", mergeStateBoundaryCheck)
    ] ++ (mergeMalformedCases.map fun (name, request) =>
      ("mergeMalformed/" ++ name, mergeRejectedResponse (exportExpandMerge request))) ++
    (mergeMalformedMixedCases.map fun (name, request) =>
      ("mergeMalformedMixed/" ++ name, mergeRejectedResponse (exportExpandMerge request))) ++ [
    ("mergeUnsupportedCheck", mergeUnsupportedCheck),
    ("mergeOpaqueIdsCheck", mergeOpaqueIdsCheck),
    ("mergeSharedRepresentationCheck", mergeSharedRepresentationCheck),
    ("mergeOpaqueHelpersCheck", mergeOpaqueHelpersCheck),
    ("mergeMixedSetCheck", mergeMixedSetCheck),
    ("mergeChangedClassFieldCheck", mergeChangedClassFieldCheck),
    ("mergeJustDropOverwriteCheck", mergeJustDropOverwriteCheck),
    ("mergeComplementaryOverwriteCheck", mergeComplementaryOverwriteCheck)]
  let mut failed := false
  for (name, passed) in checks do
    if passed then
      IO.println s!"PASS {name}"
    else
      IO.eprintln s!"FAIL {name}"
      failed := true
  if failed then
    IO.eprintln "Merge finite behavior regressions failed."
    return 1
  IO.println s!"All {checks.length} finite behavior regressions passed."
  return 0

end Node
