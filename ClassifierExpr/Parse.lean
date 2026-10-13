import ClassifierExpr.Render
import Lean.Data.Json

namespace ClassifierExpr

private def suffixNat (stem text : String) : Option Nat :=
  if text.startsWith stem then (text.drop stem.length).toString.toNat? else none

private def parseWidth : String → Option Width
  | "32" => some .w32
  | "64" => some .w64
  | _ => none

def parseReg (text : String) : Option Reg := do
  let [head, alpha] := text.splitOn ":" | none
  let alpha ← alpha.toNat?
  let (kind, width) ← ([ ("real", RegKind.real), ("stack", .stack),
    ("map", .map), ("packet", .packet), ("context", .context) ].findSome? fun (stem, kind) => do
      if !head.startsWith stem then none else
        pure (kind, ← parseWidth (head.drop stem.length).toString))
  let r : Reg := ⟨kind, width, alpha⟩
  if r.valid then some r else none

def parseRel (text : String) : Option Rel :=
  match text with
  | "eq" => some .eq | "ne" => some .ne
  | "ltu" => some .ltu | "leu" => some .leu | "gtu" => some .gtu | "geu" => some .geu
  | "lts" => some .lts | "les" => some .les | "gts" => some .gts | "ges" => some .ges
  | _ => [ ("eqN", Rel.eqN), ("neN", .neN), ("ltuN", .ltuN), ("leuN", .leuN),
      ("gtuN", .gtuN), ("geuN", .geuN), ("ltsN", .ltsN), ("lesN", .lesN),
      ("gtsN", .gtsN), ("gesN", .gesN), ("bitsnz", .bitsnz), ("bitsz", .bitsz) ].findSome?
        fun (stem, ctor) => ctor <$> suffixNat stem text

private def parseOp (text : String) (w : Width) : Option Op := do
  if let some op := [ ("add", Op.add), ("sub", .sub), ("mullo", .mullo),
      ("neg", .neg), ("id", .id), ("shl", .shl), ("lshr", .lshr),
      ("ashr", .ashr), ("ltu", .ltu), ("lts", .lts) ].findSome?
      (fun (stem, ctor) => do
        if !text.startsWith stem then none else
          pure (ctor (← parseWidth (text.drop stem.length).toString))) then
    return op
  if let some op := [ ("and", Op.and), ("or", .or), ("xor", .xor),
      ("low", fun q => Op.low q w.bits), ("bswap", fun q => Op.bswap q w.bits),
      ("inputByte", Op.inputByte) ].findSome?
      (fun (stem, ctor) => ctor <$> suffixNat stem text) then
    return op
  if text.startsWith "extract" then
    let [o, len] := (text.drop 7).toString.splitOn "," | none
    return .extract (← o.toNat?) (← len.toNat?) w.bits
  if text.startsWith "mergeLow" then
    let [q, bits] := (text.drop 8).toString.splitOn "," | none
    return .mergeLow (← q.toNat?) (← bits.toNat?)
  if text.startsWith "externalResult" then
    let [event, lane] := (text.drop 14).toString.splitOn "_" | none
    return .externalResult (← event.toNat?) (← lane.toNat?)
  if text.startsWith "zext" || text.startsWith "sext" then
    let [q, bits] := (text.drop 4).toString.splitOn "/" | none
    let width ← parseWidth bits
    let q ← q.toNat?
    return if text.startsWith "zext" then .zext q width w.bits else .sext q width w.bits
  none

/-- Explicit carrier annotations shared by Expr and all five predicate classes. -/
private def parsePredicateOp (text : String) (w : Width) : Option Op := do
  match text.splitOn "/" with
  | [name, input] =>
    let input ← parseWidth input
    if let some q := suffixNat "low" name then return .low q input.bits
    if let some q := suffixNat "bswap" name then return .bswap q input.bits
    if name.startsWith "extract" then
      let [o, len] := (name.drop 7).toString.splitOn "," | none
      return .extract (← o.toNat?) (← len.toNat?) input.bits
    parseOp text w
  | [name, output, input] =>
    let output ← parseWidth output
    let input ← parseWidth input
    if let some q := suffixNat "zext" name then return .zext q output input.bits
    if let some q := suffixNat "sext" name then return .sext q output input.bits
    none
  | _ => parseOp text w

private def opWidth (fallback : Width) : Op → Width
  | .add w | .sub w | .mullo w | .neg w | .id w | .shl w | .lshr w | .ashr w
  | .ltu w | .lts w | .zext _ w _ | .sext _ w _ => w
  | _ => fallback

private def opArity : Op → Option Nat
  | .neg _ | .id _ | .low _ _ | .extract _ _ _ | .zext _ _ _ | .sext _ _ _
  | .bswap _ _ => some 1
  | .externalResult _ _ => none
  | _ => some 2

private def tokenChar (c : Char) : Bool := c != '(' && c != ')' && c != ','

mutual
  private partial def parseTermChars (w : Width) (chars : List Char) (annotated : Bool := false) :
      Option (Term × List Char) := do
    let (head, rest) := chars.span tokenChar
    let mut name := String.ofList head
    let mut rest := rest
    if name.startsWith "extract" || name.startsWith "mergeLow" then
      let ',' :: tail := rest | none
      let (digits, tail) := tail.span tokenChar
      name := name ++ "," ++ String.ofList digits
      rest := tail
    match rest with
    | '(' :: tail =>
      if annotated && (name == "t32" || name == "t64") then
        let width := if name == "t32" then Width.w32 else .w64
        let (term, tail) ← parseTermChars width tail annotated
        let ')' :: tail := tail | none
        if term.width != width then none else return (term, tail)
      if let some event := suffixNat "regVar" name then
        let (reg, tail) := tail.span (· != ')')
        let ')' :: tail := tail | none
        return (.regVar event (← parseReg (String.ofList reg)), tail)
      let op ← if annotated then parsePredicateOp name w else parseOp name w
      let width := opWidth w op
      let input := if annotated then
        match op with
        | .low _ v | .extract _ _ v | .zext _ _ v | .sext _ _ v | .bswap _ v =>
          if v == 64 then Width.w64 else .w32
        | _ => width
        else width
      let (args, tail) ← parseTermArgs input tail annotated
      if let some arity := opArity op then
        if args.length != arity then none else pure ()
      return (.app width op args, tail)
    | _ =>
      if annotated && (name.startsWith "c32:" || name.startsWith "c64:") then
        let [head, value] := name.splitOn ":" | none
        let width := if head == "c32" then Width.w32 else .w64
        let n ← value.toNat?
        if n ≥ 2 ^ width.bits then none else return (.const width n, rest)
      if let some n := name.toNat? then
        if n ≥ 2 ^ w.bits then none else pure (.const w n, rest)
      else
        let [width, id] := name.splitOn ":" | none
        let width ← if width == "v32" then some Width.w32
          else if width == "v64" then some Width.w64 else none
        return (.var width (← id.toNat?), rest)

  private partial def parseTermArgs (w : Width) (chars : List Char) (annotated : Bool := false) :
      Option (List Term × List Char) := do
    if let ')' :: tail := chars then return ([], tail)
    let (term, rest) ← parseTermChars w chars annotated
    match rest with
    | ')' :: tail => pure ([term], tail)
    | ',' :: tail =>
      if let ')' :: _ := tail then none else do
        let (terms, tail) ← parseTermArgs w tail annotated
        pure (term :: terms, tail)
    | _ => none
end

/-- Bare constants inherit the field carrier; mixed-carrier applications retain annotations. -/
def parseTerm (text : String) (w : Width := .w32) : Option Term := do
  let (term, []) ← parseTermChars w text.toList true | none
  pure term

private def jsonString (value : Lean.Json) (key : String) : Option String :=
  (value.getObjVal? key >>= Lean.Json.getStr?).toOption

def parseExprJson (value : Lean.Json) : Option Expr := do
  let reg ← parseReg (← jsonString value "reg")
  let rel ← parseRel (← jsonString value "rel")
  let term ← parseTerm (← jsonString value "term") reg.width
  if term.width != reg.width then none else pure ⟨reg, rel, term⟩

private def helperKind (id : Nat) : HelperKind :=
  match id with
  | 1 => .lookup | 2 => .update | 3 => .delete | 5 => .clock | 6 => .printk
  | 28 => .checksum | 65 => .adjustTail | id => .unsupported id

private def boundedWidth (q bits : Nat) : Bool := 0 < q && q ≤ bits

/-- Validate the existing operators' carrier widths, arities and numeric parameters.
Low/extract/bswap results may use a wider carrier than their projected value. -/
private def predicateOpSignature (w : Width) (op : Op) (args : List Term) : Bool :=
  let uniform (n : Nat) := args.length == n && args.all (fun t => t.width == w)
  let input (v : Nat) := args.length == 1 && args.all (fun t => t.width.bits == v)
  match op with
  | .add v | .sub v | .mullo v | .shl v | .lshr v | .ashr v | .ltu v | .lts v =>
    w == v && uniform 2
  | .neg v | .id v => w == v && uniform 1
  | .and q | .or q | .xor q => boundedWidth q w.bits && uniform 2
  | .low q v => boundedWidth q v && q ≤ w.bits && input v
  | .extract o len v => 0 < len && o + len ≤ v && len ≤ w.bits && input v
  | .zext q out v | .sext q out v =>
    w == out && boundedWidth q w.bits && q ≤ v && input v
  | .bswap q v => (q == 16 || q == 32 || q == 64) &&
    q ≤ v && q ≤ w.bits && input v
  | .mergeLow q v => v == w.bits && boundedWidth q v && uniform 2
  | .externalResult _ _ => w == .w32 && !args.isEmpty &&
    args.all (fun t => t.width == .w32)
  | .inputByte _ => w == .w32 && match args with
    | [base, address] => base.width == address.width
    | _ => false

mutual
  private def predicateTermWellFormed : Term → Bool
    | .const w c => c < 2 ^ w.bits
    | .var _ _ => true
    | .regVar _ reg => reg.valid && reg.kind == .real
    | .app w op args => predicateOpSignature w op args && predicateTermsWellFormed args
  termination_by t => sizeOf t

  private def predicateTermsWellFormed : List Term → Bool
    | [] => true
    | t :: ts => predicateTermWellFormed t && predicateTermsWellFormed ts
  termination_by ts => sizeOf ts
end

private def predicateRelWellFormed (w : Width) : Rel → Bool
  | .eqN q | .neN q | .ltuN q | .leuN q | .gtuN q | .geuN q
  | .ltsN q | .lesN q | .gtsN q | .gesN q | .bitsnz q | .bitsz q =>
    boundedWidth q w.bits
  | _ => true

/-- Structural validation only. Program bounds, instruction/condition correspondence,
helper call contracts, resource provenance/layout, symbolic key byte-valuedness and
dynamic identity uniqueness remain semantic obligations. -/
def predicateWellFormed : Predicate → Bool
  | .helper _ kind args =>
    kind.id < 2 ^ 32 && helperKind kind.id == kind &&
      args.all (fun t => t.width == .w32) && predicateTermsWellFormed args
  | .branch position _ cond =>
    0 < position && cond.lhs.width == cond.rhs.width &&
      predicateRelWellFormed cond.lhs.width cond.rel &&
      predicateTermWellFormed cond.lhs && predicateTermWellFormed cond.rhs
  | .ret term => predicateTermWellFormed term
  | .mapWrite _ map key _ source =>
    predicateTermWellFormed map && predicateTermWellFormed source &&
      key.all (fun t => t.width == .w32 && predicateTermWellFormed t &&
        match t with | .const _ c => c < 256 | _ => true)
  | .packetWrite _ _ _ source => predicateTermWellFormed source

private def jsonNat (value : Lean.Json) (key : String) : Option Nat :=
  (value.getObjVal? key >>= Lean.Json.getNat?).toOption

private def jsonWidth (value : Lean.Json) (key : String) : Option Width := do
  match ← jsonNat value key with
  | 32 => some .w32
  | 64 => some .w64
  | _ => none

private def exactFields (value : Lean.Json) (fields : List String) : Bool :=
  match value.getObj?.toOption with
  | none => false
  | some obj => obj.size == fields.length && fields.all obj.contains

private def predicateJsonTerm (value : Lean.Json) (key : String) (w : Width) : Option Term := do
  let text ← jsonString value key
  let (term, []) ← parseTermChars w text.toList true | none
  if term.width != w then none else some term

/-- Strict five-class schema. Every object has exactly its documented fields;
new classes supply numeric carrier widths, while Helper keeps its existing wire shape. -/
def parsePredicateJson (value : Lean.Json) : Option Predicate := do
  let predicate : Predicate ← match ← jsonString value "kind" with
    | "helper" => do
      if !exactFields value ["kind", "event", "helperId", "args"] then none else
        let event ← jsonNat value "event"
        let id ← jsonNat value "helperId"
        let args ← (value.getObjVal? "args" >>= Lean.Json.getArr?).toOption
        let args ← args.toList.mapM fun a => do parseTerm (← a.getStr?.toOption)
        pure (.helper event (helperKind id) args)
    | "branch" => do
      if !exactFields value ["kind", "position", "dir", "width", "cond"] then none else
        let position ← jsonNat value "position"
        let dir ← match ← jsonString value "dir" with
          | "taken" => some BranchDirection.taken
          | "notTaken" => some .notTaken
          | _ => none
        let width ← jsonWidth value "width"
        let cond ← (value.getObjVal? "cond").toOption
        if !exactFields cond ["lhs", "rel", "rhs"] then none else
          let lhs ← predicateJsonTerm cond "lhs" width
          let rel ← parseRel (← jsonString cond "rel")
          let rhs ← predicateJsonTerm cond "rhs" width
          pure (.branch position dir ⟨lhs, rel, rhs⟩)
    | "ret" => do
      if !exactFields value ["kind", "width", "term"] then none else
        pure (.ret (← predicateJsonTerm value "term" (← jsonWidth value "width")))
    | "mapWrite" => do
      if !exactFields value ["kind", "event", "mapWidth", "map", "key", "offset",
          "sourceWidth", "source"] then none else
        let event ← jsonNat value "event"
        let map ← predicateJsonTerm value "map" (← jsonWidth value "mapWidth")
        let keys ← (value.getObjVal? "key" >>= Lean.Json.getArr?).toOption
        let key ← keys.toList.mapM fun item => do
          let text ← item.getStr?.toOption
          let (term, []) ← parseTermChars .w32 text.toList true | none
          if term.width != .w32 then none else some term
        let offset ← jsonNat value "offset"
        let source ← predicateJsonTerm value "source" (← jsonWidth value "sourceWidth")
        pure (.mapWrite event map key offset source)
    | "packetWrite" => do
      if !exactFields value ["kind", "event", "packet", "offset", "width", "source"] then none else
        let event ← jsonNat value "event"
        let packet ← jsonNat value "packet"
        let offset ← jsonNat value "offset"
        let source ← predicateJsonTerm value "source" (← jsonWidth value "width")
        pure (.packetWrite event packet offset source)
    | _ => none
  if predicateWellFormed predicate then some predicate else none

def parseSemStateJson (exprsJson predsJson : String) : Option SemState := do
  let exprs ← ((Lean.Json.parse exprsJson) >>= Lean.Json.getArr?).toOption
  let preds ← ((Lean.Json.parse predsJson) >>= Lean.Json.getArr?).toOption
  let rows ← exprs.toList.mapM fun row => do
    let expr ← parseExprJson row
    let role ← match row.getObjVal? "role" with
      | .error _ => some (expr.rel != .eq)
      | .ok role => do
        if (← role.getStr?.toOption) == "constraint" then some true else none
    pure (expr, role)
  let E : ExprSet := {
    entries := (rows.filter fun row => !row.2).map Prod.fst
    constraints := (rows.filter fun row => row.2).map Prod.fst }
  if !E.keysUnique || !E.wellTyped then none else
    pure ⟨E, ← preds.toList.mapM parsePredicateJson⟩

private def parseRoundTripCheck : Bool :=
  let terms := [Term.C32 4294967295, Term.V32 12, Term.regVar 42 (Reg.real32 10),
    Term.app .w32 (.add .w32) [Term.V32 1, Term.C32 4],
    Term.app .w32 (.extract 0 8 32) [Term.V32 2],
    Term.app .w32 (.externalResult 7 1) [Term.C32 1],
    Term.app .w32 (.mergeLow 8 32) [Term.V32 3,
      Term.app .w32 (.extract 8 8 32) [Term.V32 4]],
    Term.app .w32 (.or 32) [Term.app .w32 (.low 8 32)
      [Term.app .w32 (.inputByte 3) [Term.V32 1, Term.V32 2]], Term.C32 4],
    Term.C64 18446744073709551615, Term.V64 9]
  let regs := [Reg.real32 10, Reg.sw 8, Reg.mapWord 7 4, Reg.packet 3 2, Reg.real64 1,
    Reg.ctx32 100, Reg.ctx64 101]
  let rels := [Rel.eq, .ne, .ltu, .geu, .lts, .ges, .eqN 8, .neN 16,
    .ltuN 8, .leuN 8, .gtuN 8, .geuN 8, .ltsN 8, .lesN 8, .gtsN 8, .gesN 8,
    .bitsnz 8, .bitsz 8, .leu, .gtu, .les, .gts]
  terms.all (fun t => parseTerm (renderTerm t) t.width == some t) &&
  regs.all (fun r => parseReg (renderReg r) == some r) &&
  rels.all (fun r => parseRel (renderRel r) == some r) &&
  terms.all (fun t =>
    let e := Expr.mkEq (Reg.real t.width 10) t
    match (Lean.Json.parse (renderExprJson e)).toOption >>= parseExprJson with
    | some e' => e'.reg == e.reg && e'.rel == e.rel && e'.term == e.term
    | none => false) &&
  [Predicate.helper 42 .lookup [Term.C32 1, Term.regVar 4 (Reg.real32 11)],
    .helper 43 (.unsupported 999) [],
    .helper 44 .lookup [Term.V32 10, Term.C32 0]].all (fun p =>
      ((Lean.Json.parse (renderPredicateJson p)).toOption >>= parsePredicateJson) == some p)

private def parseOpsRoundTripCheck : Bool :=
  let ops := [Op.add .w32, .sub .w32, .mullo .w32, .neg .w32, .id .w32,
    .and 32, .or 32, .xor 32, .shl .w32, .lshr .w32, .ashr .w32,
    .ltu .w32, .lts .w32, .low 8 32, .extract 8 16 32, .zext 8 .w32 32,
    .sext 16 .w32 32, .bswap 32 32, .externalResult 12 3, .inputByte 7,
    .mergeLow 16 32]
  ops.all fun op =>
    let args := if opArity op == some 1 then [Term.V32 1]
      else [Term.V32 1, Term.C32 2]
    let term := Term.app .w32 op args
    parseTerm (renderTerm term) == some term

private def crossCarrierRoundTripCheck : Bool :=
  let fixtures := [
    (Term.app .w64 (.zext 32 .w64 32) [Term.V32 4], "zext32/64/32(v32:4)"),
    (Term.app .w64 (.sext 32 .w64 32) [Term.C32 4294967295], "sext32/64/32(4294967295)"),
    (Term.app .w32 (.extract 0 32 64) [Term.V64 1], "extract0,32/64(v64:1)"),
    (Term.app .w32 (.low 32 64) [Term.C64 4294967296], "low32/64(4294967296)"),
    (Term.app .w32 (.bswap 32 64) [Term.V64 2], "bswap32/64(v64:2)"),
    (Term.app .w64 (.zext 32 .w64 32)
      [Term.app .w32 (.extract 0 32 32)
        [Term.app .w32 (.add .w32) [Term.V32 4, Term.C32 128]]],
      "zext32/64/32(extract0,32(add32(v32:4,128)))")]
  fixtures.all fun (term, text) =>
    renderTerm term == text && parseTerm text term.width == some term &&
      ((Lean.Json.parse (renderExprJson (Expr.mkEq (Reg.real term.width 1) term))).toOption
        >>= parseExprJson).any (fun e => e.term == term)

#guard crossCarrierRoundTripCheck

private def constraintRoundTripCheck : Bool :=
  let E := ExprSet.empty.insertEq (Reg.real64 1) (Term.V64 1)
    |>.insertConstraint (Expr.mkRel (Reg.real64 1) .eq (Term.C64 10))
    |>.insertConstraint (Expr.mkRel (Reg.real64 1) (.ltuN 32) (Term.C64 20))
  match parseSemStateJson ("[" ++ renderExprSetJson E ++ "]") "[]" with
  | some state => state.exprs == E && state.exprs.lookupEq (Reg.real64 1) == some (Term.V64 1)
  | none => false

private def predicateRoundTrip (p : Predicate) : Bool :=
  predicateWellFormed p &&
    ((Lean.Json.parse (renderPredicateJson p)).toOption >>= parsePredicateJson) == some p

private def fiveClassRoundTripCheck : Bool :=
  let max64 := Term.C64 18446744073709551615
  let byte := Term.app .w32 (.extract 8 8 64) [max64]
  let extended := Term.app .w64 (.zext 8 .w64 32) [byte]
  let mixedInput := Term.app .w32 (.inputByte 3)
    [Term.app .w64 (.and 64) [max64, Term.C64 15], Term.C64 4]
  [Predicate.helper 42 .lookup [Term.C32 1, Term.V32 2],
    .branch 1 .taken ⟨Term.V32 1, .eq, Term.C32 0⟩,
    .branch 2 .notTaken ⟨max64, .bitsz 32, Term.C64 1⟩,
    .ret (Term.C32 9), .ret (Term.C64 0), .ret max64, .ret extended,
    .ret mixedInput,
    .ret (Term.app .w64 (.sext 8 .w64 32) [Term.V32 1]),
    .ret (Term.app .w64 (.low 8 32) [Term.C32 255]),
    .ret (Term.app .w32 (.bswap 32 64) [max64]),
    .mapWrite 5 (Term.C32 1) [] 0 (Term.C32 2),
    .mapWrite 6 max64 [Term.C32 0, Term.C32 255, byte] 8 max64,
    .mapWrite 9 max64 [Term.V32 1, Term.V32 1] 0 (Term.C32 0),
    .mapWrite 10 (Term.C32 1) [byte] 0 max64,
    .packetWrite 7 3 0 (Term.C32 42),
    .packetWrite 8 3 4 max64].all predicateRoundTrip

private def branchComplementCheck : Bool :=
  let rels := [Rel.eq, .ne, .ltu, .leu, .gtu, .geu, .lts, .les, .gts, .ges,
    .eqN 32, .neN 32, .ltuN 32, .leuN 32, .gtuN 32, .geuN 32,
    .ltsN 32, .lesN 32, .gtsN 32, .gesN 32, .bitsnz 32, .bitsz 32]
  rels.all fun rel =>
    let lhs := Term.C64 18446744073709551615
    let rhs := Term.C64 1
    predicateRoundTrip (.branch 1 .taken ⟨lhs, rel, rhs⟩) &&
      predicateRoundTrip (.branch 1 .notTaken ⟨lhs, rel.compl, rhs⟩) &&
      rel.compl.compl == rel &&
      interpretRel 64 rel 18446744073709551615 1 !=
        interpretRel 64 rel.compl 18446744073709551615 1

private def malformedPredicateCheck : Bool :=
  let rejected (text : String) :=
    ((Lean.Json.parse text).toOption >>= parsePredicateJson).isNone
  let badTerms := [Term.const .w32 4294967296, .const .w64 18446744073709551616,
    .regVar 1 (Reg.map32 1), .app .w32 (.neg .w32) [Term.C32 1, Term.C32 2],
    .app .w32 (.add .w32) [Term.V64 1, Term.C32 0],
    .app .w32 (.add .w32) [Term.app .w32 (.low 0 32) [Term.C32 1], Term.C32 0],
    .app .w32 (.extract 31 2 32) [Term.C32 0],
    .app .w32 (.and 33) [Term.C32 0, Term.C32 0],
    .app .w64 (.zext 33 .w64 32) [Term.C32 0],
    .app .w32 (.bswap 8 32) [Term.C32 0],
    .app .w32 (.mergeLow 8 64) [Term.C32 0, Term.C32 0],
    .app .w32 (.externalResult 1 0) [],
    .app .w64 (.inputByte 1) [Term.V64 1, Term.V64 2],
    .app .w32 (.inputByte 1) [Term.V32 1, Term.V64 2]]
  let badPredicates := [Predicate.helper 0 (.unsupported 4294967296) [],
    .helper 0 .lookup [Term.V64 1],
    .branch 0 .taken ⟨Term.C32 0, .eq, Term.C32 0⟩,
    .branch 1 .taken ⟨Term.C32 0, .eqN 0, Term.C32 0⟩,
    .branch 1 .taken ⟨Term.C32 0, .bitsnz 33, Term.C32 0⟩,
    .branch 1 .taken ⟨Term.C32 0, .eq, Term.V64 1⟩,
    .mapWrite 0 (Term.C32 0) [Term.C32 256] 0 (Term.C32 0),
    .mapWrite 0 (Term.C32 0) [Term.V64 1] 0 (Term.C32 0)]
  badTerms.all (fun t =>
    !predicateWellFormed (.ret t) && rejected (renderPredicateJson (.ret t))) &&
  badPredicates.all (fun p =>
    !predicateWellFormed p && rejected (renderPredicateJson p)) &&
  [
    "{\"kind\":\"ret\",\"width\":16,\"term\":\"0\"}",
    "{\"kind\":\"ret\",\"width\":\"64\",\"term\":\"0\"}",
    "{\"kind\":\"ret\",\"width\":32,\"term\":\"v64:1\"}",
    "{\"kind\":\"ret\",\"width\":32,\"term\":\"t64(and64(0,0))\"}",
    "{\"kind\":\"ret\",\"width\":32,\"term\":\"0\",\"extra\":0}",
    "{\"kind\":\"branch\",\"position\":1,\"dir\":\"jump\",\"width\":32,\"cond\":{\"lhs\":\"0\",\"rel\":\"eq\",\"rhs\":\"0\"}}",
    "{\"kind\":\"branch\",\"position\":1,\"dir\":\"taken\",\"width\":32,\"cond\":{\"lhs\":\"0\",\"rel\":\"unknown\",\"rhs\":\"0\"}}",
    "{\"kind\":\"branch\",\"position\":1,\"dir\":\"taken\",\"width\":32,\"cond\":{\"lhs\":\"0\",\"rel\":\"eq\",\"rhs\":\"0\",\"extra\":0}}",
    "{\"kind\":\"mapWrite\",\"event\":0,\"mapWidth\":32,\"map\":\"v64:1\",\"key\":[],\"offset\":0,\"sourceWidth\":32,\"source\":\"0\"}",
    "{\"kind\":\"mapWrite\",\"event\":0,\"mapWidth\":32,\"map\":\"0\",\"key\":[0],\"offset\":0,\"sourceWidth\":32,\"source\":\"0\"}",
    "{\"kind\":\"packetWrite\",\"event\":0,\"packet\":0,\"offset\":-1,\"width\":32,\"source\":\"0\"}",
    "{\"kind\":\"packetWrite\",\"event\":0,\"offset\":0,\"width\":32,\"source\":\"0\"}",
    "{\"kind\":\"packetWrite\",\"event\":0,\"packet\":0,\"offset\":0,\"width\":64,\"source\":\"v32:1\"}",
    "{\"kind\":\"packetWrite\",\"event\":0,\"packet\":0,\"offset\":0,\"width\":32,\"source\":\"add32(1,)\"}",
    "{\"kind\":\"escape\"}"
  ].all rejected

private def fiveClassSemStateCheck : Bool :=
  let ps := [Predicate.helper 1 .clock [],
    .branch 1 .notTaken ⟨Term.V32 1, .ne, Term.C32 0⟩,
    .ret (Term.C64 18446744073709551615),
    .mapWrite 2 (Term.C64 1) [Term.C32 255] 0 (Term.C32 3),
    .packetWrite 3 0 0 (Term.C64 4)]
  match parseSemStateJson "[]" ("[" ++ renderPredicatesJson ps ++ "]") with
  | some state => state.predicates == ps
  | none => false

#guard fiveClassSemStateCheck
#guard fiveClassRoundTripCheck
#guard branchComplementCheck
#guard malformedPredicateCheck
#guard renderPredicateJson (.helper 42 .lookup [Term.C32 1, Term.V32 2]) ==
  "{\"kind\":\"helper\",\"event\":42,\"helperId\":1,\"args\":[\"1\",\"v32:2\"]}"
#guard !predicateWellFormed (.helper 0 (.unsupported 1) [])
#guard constraintRoundTripCheck
#guard (parseSemStateJson "[]" "[{\"kind\":\"cmp\",\"width\":32,\"rel\":\"eq\",\"lhs\":\"0\",\"rhs\":\"0\"}]").isNone
#guard (parseSemStateJson "[]" "[{\"kind\":\"ret\",\"term\":\"2\"}]").isNone
#guard parseRoundTripCheck
#guard parseOpsRoundTripCheck
#guard (parseSemStateJson "{}" "[]").isNone
#guard (parseTerm "add32(v32:1,)").isNone
#guard (parseReg "packet64:0").isNone

end ClassifierExpr
