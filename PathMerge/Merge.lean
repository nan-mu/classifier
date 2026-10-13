import PathMerge.Path
import ClassifierExpr.Parse

namespace PathMerge.ExactMerge
open ClassifierExpr

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

private instance : DecidableEq ClassifierExpr.Term := termDecEq
deriving instance DecidableEq for ClassifierExpr.Expr
deriving instance DecidableEq for ClassifierExpr.HelperKind
deriving instance DecidableEq for ClassifierExpr.Predicate

private def sameSet [DecidableEq α] (xs ys : List α) : Bool :=
  xs.all (fun x => ys.any (fun y => decide (x = y))) &&
    ys.all (fun y => xs.any (fun x => decide (y = x)))

/-- Exact equality of the current representation: location and both Expr roles,
then Helper observation membership. Set order and predicate multiplicity do not matter;
argument order, event identity, widths, operators and all AST children do matter.
The parser still requires unique value keys and structurally unique constraints. -/
def sameConfig (a b : Node) : Bool :=
  decide (a.loc = b.loc) &&
    sameSet a.state.exprs.entries b.state.exprs.entries &&
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

private def opSignature (w : Width) (op : Op) (args : List Term) : Bool :=
  let uniform (n : Nat) := args.length == n && args.all (fun t => t.width == w)
  match op with
  | .add v | .sub v | .mullo v | .shl v | .lshr v | .ashr v | .ltu v | .lts v =>
    w == v && uniform 2
  | .neg v | .id v => w == v && uniform 1
  | .and q | .or q | .xor q => boundedWidth q w.bits && uniform 2
  | .low q v => v == w.bits && boundedWidth q v && uniform 1
  | .extract o len v => v == w.bits && 0 < len && o + len ≤ v && uniform 1
  | .zext q out v | .sext q out v =>
    w == out && boundedWidth q w.bits && 0 < q && q ≤ v &&
      args.length == 1 && args.all (fun t => t.width.bits == v)
  | .bswap q v => v == w.bits && (q == 16 || q == 32 || q == 64) &&
    q ≤ v && uniform 1
  | .mergeLow q v => v == w.bits && boundedWidth q v && uniform 2
  | .externalResult _ _ => w == .w32 && !args.isEmpty &&
    args.all (fun t => t.width == .w32)
  | .inputByte _ => w == .w32 && uniform 2

mutual
  private def validTerm : Term → Bool
    | .const w c => c < 2 ^ w.bits
    | .var _ _ => true
    | .regVar _ r => r.valid && r.kind == .real
    | .app w op args => opSignature w op args && validTerms args
  termination_by t => sizeOf t

  private def validTerms : List Term → Bool
    | [] => true
    | t :: ts => validTerm t && validTerms ts
  termination_by ts => sizeOf ts
end

private def validRel (w : Width) : Rel → Bool
  | .eqN q | .neN q | .ltuN q | .leuN q | .gtuN q | .geuN q
  | .ltsN q | .lesN q | .gtsN q | .gesN q | .bitsnz q | .bitsz q =>
    boundedWidth q w.bits
  | _ => true

-- Helper observations are opaque. The bounded ID and w32 argument representation
-- are current shared-parser limits, not a target's helper arity or call semantics.
private def validPredicate : Predicate → Bool
  | .helper _ kind args => kind.id < (1 <<< 32) &&
    args.all (fun t => t.width == .w32) && validTerms args

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
  for p in predicates do
    let kind ← stringField p "kind"
    if kind != "helper" then throw ("UnsupportedPredicateKind:" ++ label ++ ":" ++ kind)
  let some state := parseSemStateJson (Lean.Json.arr exprs).compress
      (Lean.Json.arr predicates).compress | throw ("InvalidSnapshot:" ++ label)
  if !state.exprs.toList.all (fun e => validRel e.reg.width e.rel && validTerm e.term) then
    throw ("InvalidTerm:" ++ label)
  if !state.predicates.all validPredicate then throw ("InvalidPredicate:" ++ label)
  pure (id, ⟨loc, state⟩)

/-- Validate all evidence before selecting the first exactly equal ordered suffix entry.
Snapshots are already-applied global states. Position validity, common origin, history,
reusable-suffix validity and coverage certificates remain the caller's obligations. -/
def select (requestJson : String) : Except String (Nat × Nat) := do
  let j ← (Lean.Json.parse requestJson).mapError (fun e => "InvalidRequestJSON:" ++ e)
  let model ← stringField j "observationModel"
  if model != "HelperOnly" then throw ("UnsupportedObservationModel:" ++ model)
  let requirements ← arrayField j "requiredObservations"
  for value in requirements do
    let name ← value.getStr?.mapError (fun _ => "MissingOrInvalidField:requiredObservations")
    if name != "Helper" then throw ("UnsupportedRequiredObservation:" ++ name)
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

end PathMerge.ExactMerge

namespace PathMerge
open ClassifierExpr

/-- Stateless exact-config oracle over the CURRENT Helper-only representation.
The request carries the observation model, required observations and already-applied
GLOBAL configurations; IDs are opaque natural references. Location uses a zero-based
nonnegative decimal string or `exit`, with program validity owned by the runtime.
All candidates validate before the first equal ordered NotTaken entry is selected.
No state is rewritten and no instruction is executed.

`scope: ExactConfig` proves only equality in this representation. Authentic history,
common program/semantic context, branch origin, suffix validity and e_N/e_T/e_M remain
external obligations. Missing Branch/Return/MapWrite/PacketWrite observations cannot
certify the full five-observation Merged(M) contract. Requiring them rejects even equal
supplied states. Malformed evidence and unequal configs reject with InsufficientEvidence;
this export produces neither a behavioral Counterexample nor an Escape certificate.

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

private def mergeRejects (request : String) (detail : String) : Bool :=
  let result := exportExpandMerge request
  mergeOutputField result "status" == some "reject" &&
    mergeOutputField result "reason" == some "InsufficientEvidence" &&
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
  s!"\{\"reg\":\"real32:10\",\"rel\":\"eq\",\"term\":\"{term}\"{role}}"

private def mergePredicateFixture (event : Nat := 7) (id : Nat := 5)
    (args : String := "[]") : String :=
  s!"\{\"kind\":\"helper\",\"event\":{event},\"helperId\":{id},\"args\":{args}}"

private def mergeSetOrderCheck : Bool :=
  let value := mergeExprFixture
  let constraint := mergeExprFixture "9" ",\"role\":\"constraint\""
  let secondConstraint := mergeExprFixture "8" ",\"role\":\"constraint\""
  let other := "{\"reg\":\"real32:11\",\"rel\":\"eq\",\"term\":\"v32:11\"}"
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
    mergeSnapshotFixture 17 "1" ("[" ++ mergeExprFixture "4" ",\"role\":\"constraint\"" ++ "]"),
    mergeSnapshotFixture 17 "1" "[{\"reg\":\"real64:10\",\"rel\":\"eq\",\"term\":\"4\"}]",
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

private def mergeMalformedCheck : Bool :=
  let taken := mergeSnapshotFixture 42
  let candidate := mergeSnapshotFixture 17
  let badValue := "[" ++ mergeExprFixture ++ "," ++ mergeExprFixture ++ "]"
  let constraint := mergeExprFixture "4" ",\"role\":\"constraint\""
  mergeRejects "{" "InvalidRequestJSON:" &&
  mergeRejects "{}" "MissingOrInvalidField:" &&
  mergeRejects (mergeRequestFixture taken "") "EmptyNotTaken" &&
  mergeRejects (mergeRequestFixture taken (mergeSnapshotFixture 42)) "DuplicateNodeId" &&
  mergeRejects (mergeRequestFixture taken (candidate ++ "," ++ mergeSnapshotFixture 17)) "DuplicateNodeId" &&
  mergeRejects (mergeRequestFixture taken (candidate ++ "," ++ mergeSnapshotFixture 18 "-1")) "InvalidLocation:" &&
  mergeRejects (mergeRequestFixture taken (candidate ++ "," ++ mergeSnapshotFixture 18 "1" badValue))
    "InvalidSnapshot:" &&
  mergeRejects (mergeRequestFixture taken (mergeSnapshotFixture 17 "1" badValue)) "InvalidSnapshot:" &&
  mergeRejects (mergeRequestFixture taken
    (mergeSnapshotFixture 17 "1" ("[" ++ constraint ++ "," ++ constraint ++ "]"))) "InvalidSnapshot:" &&
  mergeRejects (mergeRequestFixture taken
    (mergeSnapshotFixture 17 "1" "[{\"reg\":\"packet64:0\",\"rel\":\"eq\",\"term\":\"1\"}]")) "InvalidSnapshot:" &&
  mergeRejects (mergeRequestFixture taken
    (mergeSnapshotFixture 17 "1" ("[" ++ mergeExprFixture "add32(v64:1,2)" ++ "]"))) "InvalidTerm:" &&
  mergeRejects (mergeRequestFixture taken
    (mergeSnapshotFixture 17 "1" "[{\"reg\":\"real32:10\",\"rel\":\"eqN33\",\"term\":\"1\"}]")) "InvalidTerm:" &&
  mergeRejects (mergeRequestFixture taken
    (mergeSnapshotFixture 17 "1" "[]" ("[" ++ mergePredicateFixture 7 1 "[\"v64:1\",\"2\"]" ++ "]")))
    "InvalidPredicate:" &&
  mergeRejects (mergeRequestFixture taken
    (mergeSnapshotFixture 17 "1" "[]" ("[" ++ mergePredicateFixture 7 1 "[\"add32(v64:1,2)\"]" ++ "]")))
    "InvalidPredicate:" &&
  mergeRejects (mergeRequestFixture taken
    (mergeSnapshotFixture 17 "1" "[]" ("[" ++ mergePredicateFixture 7 4294967296 ++ "]")))
    "InvalidPredicate:" &&
  mergeRejects (mergeRequestFixture taken
    "{\"id\":\"17\",\"loc\":\"1\",\"exprs\":[],\"predicates\":[]}") "MissingOrInvalidField:id"

private def mergeUnsupportedCheck : Bool :=
  let taken := mergeSnapshotFixture 42
  let candidate := mergeSnapshotFixture 17
  ["Branch", "Return", "MapWrite", "PacketWrite", "Unknown"].all
    (fun kind => mergeRejects (mergeRequestFixture taken candidate ("[\"" ++ kind ++ "\"]"))
      "UnsupportedRequiredObservation:") &&
  mergeRejects (mergeRequestFixture taken candidate "[\"Helper\"]" "FiveClass")
    "UnsupportedObservationModel:" &&
  ["branch", "return", "mapWrite", "packetWrite", "cmp", "ret"].all
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
  let state := "[{\"reg\":\"real64:10\",\"rel\":\"eq\",\"term\":\"v64:1\"}," ++
    "{\"reg\":\"real32:0\",\"rel\":\"eq\",\"term\":\"1\"}]"
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

private def mergeStateSnapshotFixture (id : Nat) (loc : String) (state : SemState) : String :=
  mergeSnapshotFixture id loc ("[" ++ renderExprSetJson state.exprs ++ "]")
    ("[" ++ renderPredicatesJson state.predicates ++ "]")

-- Reduced just_drop.elf diamond: outer branch node 12 has Taken descendants
-- 27 -> 30 and NotTaken descendants 28 -> 31. Wire locations are zero-based.
-- Retain a representative shared binding and both shared comparisons; the other
-- identical rows are elided only in this fixture, never projected by the oracle.
-- This diagnoses oracle behavior, not runtime scheduling or full-observation reuse.
private def mergeJustDropOverwriteCheck : Bool :=
  let a3 := Reg.real32 13
  let common := (ExprSet.empty.insertEq (Reg.real32 27) (Term.V32 59))
    |>.insertConstraint (Expr.mkRel (Reg.real32 10) .geu
      (addStar .w32 (Term.V32 4) (Term.C32 14)))
    |>.insertConstraint (Expr.mkRel (Reg.real32 10) .geu
      (addStar .w32 (Term.V32 4) (Term.C32 18)))
  let taken : SemState := ⟨common.insertEq a3 (Term.C32 43144), []⟩
  let notTaken : SemState := ⟨common.insertEq a3 (Term.C32 129), []⟩
  -- ADDI a3,zero,18 at wire loc17 contributes this local value effect.
  let localExprs := ExprSet.empty.insertEq a3 (Term.C32 18)
  match PathMerge.applyLocal taken localExprs [], PathMerge.applyLocal notTaken localExprs [] with
  | .ok takenAfter, .ok notTakenAfter =>
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
  | _, _ => false

-- Equal values and empty Helper sets do not erase complementary constraints.
-- Only an actual local assignment to the compared register invalidates them.
private def mergeComplementaryOverwriteCheck : Bool :=
  let compared := Reg.real32 13
  let other := Reg.real32 27
  let common := (ExprSet.empty.insertEq compared (Term.V32 13))
    |>.insertEq other (Term.V32 59)
    |>.insertConstraint (Expr.mkRel other .geu (Term.C32 1))
  [Rel.eq, .ltu].all fun rel =>
    let condition := Expr.mkRel compared rel (Term.C32 10)
    let complement := Expr.mkRel compared rel.compl (Term.C32 10)
    let taken : SemState := ⟨common.insertConstraint condition, []⟩
    let notTaken : SemState := ⟨common.insertConstraint complement, []⟩
    let request (a b : SemState) := mergeRequestFixture (mergeStateSnapshotFixture 42 "17" a)
      (mergeStateSnapshotFixture 17 "17" b)
    let overwrite := ExprSet.empty.insertEq compared (Term.C32 18)
    let unrelated := ExprSet.empty.insertEq other (Term.C32 0)
    match PathMerge.applyLocal taken overwrite [], PathMerge.applyLocal notTaken overwrite [],
        PathMerge.applyLocal taken unrelated [], PathMerge.applyLocal notTaken unrelated [] with
    | .ok takenAfter, .ok notTakenAfter, .ok takenUnrelated, .ok notTakenUnrelated =>
      let afterRequest := mergeRequestFixture (mergeStateSnapshotFixture 43 "18" takenAfter)
        (mergeStateSnapshotFixture 18 "18" notTakenAfter)
      taken.exprs.entries == notTaken.exprs.entries &&
        taken.predicates.isEmpty && notTaken.predicates.isEmpty &&
        mergeRejects (request taken notTaken) "NoExactConfigMatch" &&
        mergeRejects (request takenUnrelated notTakenUnrelated) "NoExactConfigMatch" &&
        takenAfter.exprs.constraints == common.constraints &&
        notTakenAfter.exprs.constraints == common.constraints &&
        takenAfter.exprs.lookupEq compared == some (Term.C32 18) &&
        notTakenAfter.exprs.lookupEq compared == some (Term.C32 18) &&
        mergeReuses afterRequest 18 43
    | _, _, _, _ => false

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

/-- Execute the existing ten finite wire regressions and show two actual export responses.
This does not establish general instruction semantics, runtime scheduling, full-observation
merge, or the caller's history and suffix certificates. The standalone main lives in
`MergeCheck.lean`, outside the PathMerge library imports. -/
def runMergeChecks : IO UInt32 := do
  IO.println "Merge finite behavior regressions (not a general semantic proof)."
  IO.println s!"ExactConfig response: {exportExpandMerge mergeEqualRequestFixture}"
  IO.println s!"NoExactConfigMatch response: {exportExpandMerge mergeDifferentLocationRequestFixture}"
  let checks : List (String × Bool) := [
    ("mergeEqualCheck", mergeEqualCheck),
    ("mergeSetOrderCheck", mergeSetOrderCheck),
    ("mergeStateBoundaryCheck", mergeStateBoundaryCheck),
    ("mergeMalformedCheck", mergeMalformedCheck),
    ("mergeUnsupportedCheck", mergeUnsupportedCheck),
    ("mergeOpaqueIdsCheck", mergeOpaqueIdsCheck),
    ("mergeSharedRepresentationCheck", mergeSharedRepresentationCheck),
    ("mergeOpaqueHelpersCheck", mergeOpaqueHelpersCheck),
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

end PathMerge
