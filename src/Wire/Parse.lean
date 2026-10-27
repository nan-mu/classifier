import Wire.Render
import Expression.Interval
import Lean.Data.Json

namespace Wire
open Term Term.Value Expression Observation Interface

private def suffixNat (stem text : String) : Option Nat :=
  if text.startsWith stem then (text.drop stem.length).toString.toNat? else none

private def parseWidth : String → Option Width
  | "32" => some .w32
  | "64" => some .w64
  | _ => none

private def parseHalfOpen (text : String) : Option (Nat × Nat) := do
  if !(text.startsWith "[" && text.endsWith ")") then none
  let body := ((text.drop 1).dropEnd 1).toString
  let [b, e] := body.splitOn "," | none
  pure (← b.toNat?, ← e.toNat?)

private def parseContextField (text : String) : Option ContextField :=
  match text with
  | "data" => some .data
  | "dataEnd" => some .dataEnd
  | "dataMeta" => some .dataMeta
  | "ingressIfindex" => some .ingressIfindex
  | "rxQueueIndex" => some .rxQueueIndex
  | "egressIfindex" => some .egressIfindex
  | "ctx" => some .ctx
  | "sp" => some .sp
  | "packetBytes" => some .packetBytes
  | "imageBase" => some .imageBase
  | "helper" => some .helper
  | "wrapperReturn" => some .wrapperReturn
  | _ =>
    if let some n := suffixNat "lddw:" text then some (.lddw n)
    else if let some n := suffixNat "mapKeyBytes:" text then some (.mapKeyBytes n)
    else if let some n := suffixNat "mapValueBytes:" text then some (.mapValueBytes n)
    else none

/-- Split on `;` outside parentheses. Map keys use this separator. -/
private def splitSemi (text : String) : List String :=
  let rec go (depth : Nat) (acc : List Char) (rest : List Char) (out : List String) : List String :=
    match rest with
    | [] => (out ++ [String.ofList acc.reverse]).filter (· != "")
    | '(' :: cs => go (depth + 1) ('(' :: acc) cs out
    | ')' :: cs => go (depth - 1) (')' :: acc) cs out
    | ';' :: cs =>
      if depth == 0 then go 0 [] cs (out ++ [String.ofList acc.reverse])
      else go depth (';' :: acc) cs out
    | c :: cs => go depth (c :: acc) cs out
  go 0 [] text.toList []

private def checked (r : Reg) : Option Reg :=
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
      ("urem", .urem), ("srem", .srem), ("mulh", .mulh), ("mulhu", .mulhu),
      ("mulhsu", .mulhsu), ("selectEq", .selectEq),
      ("neg", .neg), ("id", .id), ("shl", .shl), ("lshr", .lshr),
      ("ashr", .ashr), ("ltu", .ltu), ("lts", .lts) ].findSome?
      (fun (stem, ctor) => do
        if !text.startsWith stem then none else
          pure (ctor (← parseWidth (text.drop stem.length).toString))) then
    return op
  if text.startsWith "udiv" || text.startsWith "sdiv" then
    let [bits, value] := (text.drop 4).toString.splitOn "_" | none
    let width ← parseWidth bits
    let zeroResult ← value.toNat?
    return if text.startsWith "udiv" then .udiv width zeroResult else .sdiv width zeroResult
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
  if text.startsWith "packetRead" then
    let [bytes, ending] := (text.drop 10).toString.splitOn "_" | none
    return .packetRead (← bytes.toNat?) (← ending.toNat?)
  if text.startsWith "externalResult" then
    let rest := (text.drop 14).toString
    if rest.contains '_' then
      let [event, lane] := rest.splitOn "_" | none
      return .externalResult (← event.toNat?) (← lane.toNat?)
    else
      return .externalResult 0 (← rest.toNat?)
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
  | .add w | .sub w | .mullo w | .udiv w _ | .urem w | .sdiv w _ | .srem w
  | .mulh w | .mulhu w | .mulhsu w | .selectEq w
  | .neg w | .id w | .shl w | .lshr w | .ashr w
  | .ltu w | .lts w | .zext _ w _ | .sext _ w _ => w
  | _ => fallback

private def opArity : Op → Option Nat
  | .neg _ | .id _ | .low _ _ | .extract _ _ _ | .zext _ _ _ | .sext _ _ _
  | .bswap _ _ => some 1
  | .selectEq _ => some 4
  | .externalResult _ _ | .packetRead _ _ => none
  | _ => some 2

private def tokenChar (c : Char) : Bool := c != '(' && c != ')' && c != ','

/-- `)` closes `[b,e)`. A `)` with no open `[` or `(` ends the argument. -/
private def takeBalanced (chars : List Char) : Option (List Char × List Char) :=
  let rec go (opens acc rest : List Char) : Option (List Char × List Char) :=
    match rest with
    | [] => none
    | '[' :: tail => go ('[' :: opens) ('[' :: acc) tail
    | ']' :: tail =>
      match opens with
      | '[' :: restOpens => go restOpens (']' :: acc) tail
      | _ => none
    | '(' :: tail => go ('(' :: opens) ('(' :: acc) tail
    | ')' :: tail =>
      match opens with
      | '[' :: restOpens => go restOpens (')' :: acc) tail
      | '(' :: restOpens => go restOpens (')' :: acc) tail
      | _ => some (acc.reverse, tail)
    | c :: tail => go opens (c :: acc) tail
  go [] [] chars

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
      if name.startsWith "regVar" then
        let suffix := (name.drop 6).toString
        let event ← if suffix.isEmpty then some 0 else suffix.toNat?
        let (reg, tail) ← takeBalanced tail
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

  partial def parseReg (text : String) : Option Reg := do
    if text.startsWith "real:" then
      let rest := (text.drop 5).toString
      let [idx, body] := rest.splitOn "[" | none
      let idx ← ((idx.dropEnd 1).toString).toNat?
      let (b, e) ← parseHalfOpen ("[" ++ body)
      checked (.real idx b e)
    else if text.startsWith "stack:" then
      let (b, e) ← parseHalfOpen (text.drop 6).toString
      checked (.stack b e)
    else if text.startsWith "packet:" then
      let (b, e) ← parseHalfOpen (text.drop 7).toString
      checked (.packet b e)
    else if text.startsWith "context:" then
      let rest := (text.drop 8).toString
      let [name, body] := rest.splitOn "[" | none
      let field ← parseContextField (name.dropEnd 1).toString
      let (b, e) ← parseHalfOpen ("[" ++ body)
      checked (.context field b e)
    else if text.startsWith "map:" then
      let rest := (text.drop 4).toString
      let [idPart, intervalPart, keyPart] := rest.splitOn "[" | none
      let id ← ((idPart.dropEnd 1).toString).toNat?
      let (b, e) ← parseHalfOpen ("[" ++ (intervalPart.dropEnd 2).toString ++ ")")
      let body := (keyPart.dropEnd 1).toString
      let key ← if body == "" then pure [] else
        (splitSemi body).mapM fun s => do
          let (t, []) ← parseTermChars .w32 s.toList true | none
          if t.wellFormed then pure t else none
      checked (.map id key b e)
    else none
end

/-- Bare constants inherit the field carrier; mixed-carrier applications retain annotations. -/
def parseTerm (text : String) (w : Width := .w32) : Option Term := do
  let (term, []) ← parseTermChars w text.toList true | none
  if term.wellFormed then pure term else none

private def jsonString (value : Lean.Json) (key : String) : Option String :=
  (value.getObjVal? key >>= Lean.Json.getStr?).toOption

def parseExprJson (value : Lean.Json) : Option Expr := do
  let reg ← parseReg (← jsonString value "reg")
  let rel ← parseRel (← jsonString value "rel")
  let term ← parseTerm (← jsonString value "term") (Width.ofBits reg.bits)
  if term.semanticBits != reg.bits then none else pure ⟨reg, rel, term⟩

private def boundedWidth (q bits : Nat) : Bool := 0 < q && q ≤ bits


private def predicateRelWellFormed (w : Width) : Rel → Bool
  | .eqN q | .neN q | .ltuN q | .leuN q | .gtuN q | .geuN q
  | .ltsN q | .lesN q | .gtsN q | .gesN q | .bitsnz q | .bitsz q =>
    boundedWidth q w.bits
  | _ => true

/-- Structural validation only. Program bounds, instruction/condition correspondence,
helper call contracts, resource provenance/layout, symbolic key byte-valuedness and
dynamic identity uniqueness remain semantic obligations. -/
def predicateWellFormed : Observation → Bool
  | .helper _ kind args =>
    kind.id < 2 ^ 32 && helperKind kind.id == kind &&
      (args.all (fun t => t.width == .w32) || args.all (fun t => t.width == .w64)) &&
      termsWellFormed args
  | .branch position _ cond =>
    0 < position && cond.lhs.width == cond.rhs.width &&
      predicateRelWellFormed cond.lhs.width cond.rel &&
      cond.lhs.wellFormed && cond.rhs.wellFormed
  | .ret term => term.wellFormed
  | .mapWrite map key _ bits source =>
    [8, 16, 32, 64].contains bits && bits ≤ source.width.bits &&
      map.wellFormed && source.wellFormed &&
      key.all (fun t => t.width == .w32 && t.wellFormed &&
        match t with | .const _ c => c < 256 | _ => true)
  | .packetWrite offset bits source =>
    [8, 16, 32, 64].contains bits && bits ≤ source.width.bits &&
      source.wellFormed && offset < 2 ^ 32

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

/-- Strict five-class schema. Write widths describe the machine access; their
source strings carry their own term widths in the fixed w32 parsing context. -/
def parsePredicateJson (value : Lean.Json) : Option Observation := do
  let predicate : Observation ← match ← jsonString value "kind" with
    | "helper" => do
      if !exactFields value ["kind", "helperId", "args"] &&
          !exactFields value ["kind", "helperId", "event", "args"] then none else
        let id ← jsonNat value "helperId"
        let event := (jsonNat value "event").getD 0
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
      if !exactFields value ["kind", "mapWidth", "map", "key", "offset",
          "sourceWidth", "source"] then none else
        let map ← predicateJsonTerm value "map" (← jsonWidth value "mapWidth")
        let keys ← (value.getObjVal? "key" >>= Lean.Json.getArr?).toOption
        let key ← keys.toList.mapM fun item => do
          let text ← item.getStr?.toOption
          let (term, []) ← parseTermChars .w32 text.toList true | none
          if term.width != .w32 then none else some term
        let offset ← jsonNat value "offset"
        let bits ← jsonNat value "sourceWidth"
        let source ← parseTerm (← jsonString value "source") .w32
        pure (.mapWrite map key offset bits source)
    | "packetWrite" => do
      if !exactFields value ["kind", "offset", "width", "source"] then none else
        let offset ← jsonNat value "offset"
        let bits ← jsonNat value "width"
        let source ← parseTerm (← jsonString value "source") .w32
        pure (.packetWrite offset bits source)
    | _ => none
  if predicateWellFormed predicate then some predicate else none

def parseStateJson (exprsJson predsJson : String) : Option State := do
  let exprs ← ((Lean.Json.parse exprsJson) >>= Lean.Json.getArr?).toOption
  let preds ← ((Lean.Json.parse predsJson) >>= Lean.Json.getArr?).toOption
  let mut rows : List (Expr × Bool) := []
  for row in exprs.toList do
    match row.getObjVal? "role" with
    | .ok role =>
      match ← role.getStr?.toOption with
      | "constraint" => rows := rows ++ [(← parseExprJson row, true)]
      | _ => none
    | .error _ =>
      let expr ← parseExprJson row
      rows := rows ++ [(expr, expr.rel != .eq)]
  let bindings := (rows.filter fun row => !row.2).map Prod.fst
  let constraints := (rows.filter fun row => row.2).map Prod.fst
  let E : List Expr := bindings ++ constraints
  if !E.keysUnique || !E.wellTyped then none else
    let predicates ← preds.toList.mapM parsePredicateJson
    pure { exprs := E, predicates }

private def parseRoundTripCheck : Bool :=
  let terms := [Term.C32 4294967295, Term.V32 12, Term.regVar 0 (Reg.real32 10),
    Term.app .w32 (.add .w32) [Term.V32 1, Term.C32 4],
    Term.app .w32 (.extract 0 8 32) [Term.V32 2],
    Term.app .w32 (.externalResult 0 1) [Term.C32 1],
    Term.app .w32 (.mergeLow 8 32) [Term.V32 3,
      Term.app .w32 (.extract 8 8 32) [Term.V32 4]],
    Term.app .w32 (.or 32) [Term.app .w32 (.low 8 32)
      [Term.app .w32 (.inputByte 3) [Term.V32 1, Term.V32 2]], Term.C32 4],
    Term.C64 18446744073709551615, Term.V64 9]
  let regs := [Reg.real32 10, .stack 0 32, .map 7 [Term.C32 1, Term.V32 2] 0 32,
    .packet 16 24, Reg.real64 1, .context .data 0 32, .context (.lddw 3) 0 64]
  let rels := [Rel.eq, .ne, .ltu, .geu, .lts, .ges, .eqN 8, .neN 16,
    .ltuN 8, .leuN 8, .gtuN 8, .geuN 8, .ltsN 8, .lesN 8, .gtsN 8, .gesN 8,
    .bitsnz 8, .bitsz 8, .leu, .gtu, .les, .gts]
  terms.all (fun t => parseTerm (renderTerm t) t.width == some t) &&
  regs.all (fun r => parseReg (renderReg r) == some r) &&
  rels.all (fun r => parseRel (renderRel r) == some r) &&
  terms.all (fun t =>
    let e := Expr.mkEq (.real 10 0 t.semanticBits) t
    match (Lean.Json.parse (renderExprJson e)).toOption >>= parseExprJson with
    | some e' => e'.reg == e.reg && e'.rel == e.rel && e'.term == e.term
    | none => false) &&
  [Observation.helper 0 .lookup [Term.C32 1, Term.regVar 0 (Reg.real32 11)],
    .helper 0 (.unsupported 999) [],
    .helper 0 .lookup [Term.V32 10, Term.C32 0]].all (fun p =>
      ((Lean.Json.parse (renderPredicateJson p)).toOption >>= parsePredicateJson) == some p)

private def parseOpsRoundTripCheck : Bool :=
  let ops := [Op.add .w32, .sub .w32, .mullo .w32, .neg .w32, .id .w32,
    .udiv .w32 0, .udiv .w32 4294967295, .urem .w32,
    .sdiv .w32 0, .sdiv .w32 4294967295, .srem .w32,
    .mulh .w32, .mulhu .w32, .mulhsu .w32, .selectEq .w32,
    .and 32, .or 32, .xor 32, .shl .w32, .lshr .w32, .ashr .w32,
    .ltu .w32, .lts .w32, .low 8 32, .extract 8 16 32, .zext 8 .w32 32,
    .sext 16 .w32 32, .bswap 32 32, .externalResult 0 3, .inputByte 7,
    .mergeLow 16 32]
  ops.all fun op =>
    let args := if opArity op == some 1 then [Term.V32 1]
      else if opArity op == some 4 then [Term.V32 1, Term.C32 2, Term.V32 3, Term.V32 4]
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
      ((Lean.Json.parse (renderExprJson (Expr.mkEq (.real 1 0 term.semanticBits) term))).toOption
        >>= parseExprJson).any (fun e => e.term == term)

#guard crossCarrierRoundTripCheck

private def constraintRoundTripCheck : Bool :=
  let E := (update ⟨Expr.nil, []⟩ { exprs := [Expr.mkEq (Reg.real64 1) (solve (Term.V64 1))], predicates := [] }).exprs
    |> (fun acc => (let row := solveExpr (Expr.mkRel (Reg.real64 1) .eq (Term.C64 10)); if acc.contains row then acc else acc ++ [row]))
    |> (fun acc => (let row := solveExpr (Expr.mkRel (Reg.real64 1) (.ltuN 32) (Term.C64 20)); if acc.contains row then acc else acc ++ [row]))
  match parseStateJson ("[" ++ renderExprsJson E ++ "]") "[]" with
  | some state => state.exprs == E && state.exprs.lookupEq (Reg.real64 1) == some (Term.V64 1)
  | none => false

private def predicateRoundTrip (p : Observation) : Bool :=
  predicateWellFormed p &&
    ((Lean.Json.parse (renderPredicateJson p)).toOption >>= parsePredicateJson) == some p

private def fiveClassRoundTripCheck : Bool :=
  let max64 := Term.C64 18446744073709551615
  let byte := Term.app .w32 (.extract 8 8 64) [max64]
  let extended := Term.app .w64 (.zext 8 .w64 32) [byte]
  let mixedInput := Term.app .w32 (.inputByte 3)
    [Term.app .w64 (.and 64) [max64, Term.C64 15], Term.C64 4]
  [Observation.helper 0 .lookup [Term.C32 1, Term.V32 2],
    .branch 1 .taken ⟨Term.V32 1, .eq, Term.C32 0⟩,
    .branch 2 .notTaken ⟨max64, .bitsz 32, Term.C64 1⟩,
    .ret (Term.C32 9), .ret (Term.C64 0), .ret max64, .ret extended,
    .ret mixedInput,
    .ret (Term.app .w64 (.sext 8 .w64 32) [Term.V32 1]),
    .ret (Term.app .w64 (.low 8 32) [Term.C32 255]),
    .ret (Term.app .w32 (.bswap 32 64) [max64]),
    .mapWrite (Term.C32 1) [] 0 32 (Term.C32 2),
    .mapWrite max64 [Term.C32 0, Term.C32 255, byte] 8 32 max64,
    .mapWrite max64 [Term.V32 1, Term.V32 1] 0 32 (Term.C32 0),
    .mapWrite (Term.C32 1) [byte] 0 32 max64,
    .packetWrite 0 8 (Term.C32 42),
    .packetWrite 4 64 max64,
    .packetWrite 0 16 (Term.V64 1),
    .packetWrite 0 32 (Term.V32 1)].all predicateRoundTrip

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
    .regVar 0 (.map 1 [] 0 0), .app .w32 (.neg .w32) [Term.C32 1, Term.C32 2],
    .app .w32 (.add .w32) [Term.V64 1, Term.C32 0],
    .app .w32 (.add .w32) [Term.app .w32 (.low 0 32) [Term.C32 1], Term.C32 0],
    .app .w32 (.extract 31 2 32) [Term.C32 0],
    .app .w32 (.and 33) [Term.C32 0, Term.C32 0],
    .app .w64 (.zext 33 .w64 32) [Term.C32 0],
    .app .w32 (.bswap 8 32) [Term.C32 0],
    .app .w32 (.mergeLow 8 64) [Term.C32 0, Term.C32 0],
    .app .w32 (.externalResult 0 0) [],
    .app .w64 (.inputByte 1) [Term.V64 1, Term.V64 2],
    .app .w32 (.inputByte 1) [Term.V32 1, Term.V64 2]]
  let badPredicates := [Observation.helper 0 (.unsupported 4294967296) [],
    .helper 0 .lookup [Term.V64 1, Term.V32 2],
    .branch 0 .taken ⟨Term.C32 0, .eq, Term.C32 0⟩,
    .branch 1 .taken ⟨Term.C32 0, .eqN 0, Term.C32 0⟩,
    .branch 1 .taken ⟨Term.C32 0, .bitsnz 33, Term.C32 0⟩,
    .branch 1 .taken ⟨Term.C32 0, .eq, Term.V64 1⟩,
    .mapWrite (Term.C32 0) [Term.C32 256] 0 32 (Term.C32 0),
    .mapWrite (Term.C32 0) [Term.V64 1] 0 32 (Term.C32 0),
    .mapWrite (Term.C32 0) [] 0 24 (Term.C32 0),
    .packetWrite 0 0 (Term.C32 0),
    .packetWrite 0 24 (Term.C32 0),
    .packetWrite 0 64 (Term.C32 0)]
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
    "{\"kind\":\"mapWrite\",\"mapWidth\":32,\"map\":\"v64:1\",\"key\":[],\"offset\":0,\"sourceWidth\":32,\"source\":\"0\"}",
    "{\"kind\":\"mapWrite\",\"mapWidth\":32,\"map\":\"0\",\"key\":[0],\"offset\":0,\"sourceWidth\":32,\"source\":\"0\"}",
    "{\"kind\":\"packetWrite\",\"packet\":0,\"offset\":0,\"width\":32,\"source\":\"0\"}",
    "{\"kind\":\"packetWrite\",\"offset\":0,\"width\":24,\"source\":\"0\"}",
    "{\"kind\":\"packetWrite\",\"packet\":0,\"offset\":0,\"width\":64,\"source\":\"v32:1\"}",
    "{\"kind\":\"packetWrite\",\"offset\":0,\"width\":32,\"source\":\"add32(1,)\"}",
    "{\"kind\":\"escape\"}"
  ].all rejected

private def fiveClassStateCheck : Bool :=
  let ps := [Observation.helper 0 .clock [],
    .branch 1 .notTaken ⟨Term.V32 1, .ne, Term.C32 0⟩,
    .ret (Term.C64 18446744073709551615),
    .mapWrite (Term.C64 1) [Term.C32 255] 0 32 (Term.C32 3),
    .packetWrite 0 64 (Term.C64 4)]
  match parseStateJson "[]" ("[" ++ renderPredicatesJson ps ++ "]") with
  | some state => state.predicates == ps
  | none => false

#guard fiveClassStateCheck
#guard fiveClassRoundTripCheck
#guard branchComplementCheck
#guard malformedPredicateCheck
#guard renderPredicateJson (.helper 0 .lookup [Term.C32 1, Term.V32 2]) ==
  "{\"kind\":\"helper\",\"helperId\":1,\"event\":0,\"args\":[\"1\",\"v32:2\"]}"
#guard !predicateWellFormed (.helper 0 (.unsupported 1) [])
#guard
  let p := Observation.helper 0 .lookup
    [Term.C64 1077412584, Term.app .w64 (.add .w64) [Term.V64 0, Term.C64 4]]
  predicateWellFormed p &&
    ((Lean.Json.parse (renderPredicateJson p)).toOption >>= parsePredicateJson) == some p
#guard
  let p := Observation.ret
    (Term.app .w64 (.externalResult 0 0) [Term.C64 1, Term.V64 2, Term.V64 3])
  predicateWellFormed p &&
    ((Lean.Json.parse (renderPredicateJson p)).toOption >>= parsePredicateJson) == some p
#guard !predicateWellFormed (.helper 0 .lookup [Term.C64 1, Term.V32 2])
#guard !predicateWellFormed (.ret
  (Term.app .w64 (.externalResult 0 0) [Term.C64 1, Term.V32 2]))
#guard constraintRoundTripCheck
#guard (parseStateJson "[]" "[{\"kind\":\"cmp\",\"width\":32,\"rel\":\"eq\",\"lhs\":\"0\",\"rhs\":\"0\"}]").isNone
#guard (parseStateJson "[]" "[{\"kind\":\"ret\",\"term\":\"2\"}]").isNone
#guard parseRoundTripCheck
#guard parseOpsRoundTripCheck
#guard Id.run do
  let key := [Term.C32 1, Term.C32 2]
  let some E := ((«seal» ((Reg.real64 1)).bits (Term.V64 1) >>= fun stored => some (update ⟨((update ⟨Expr.nil, []⟩ { exprs := [Expr.mkEq (Reg.real64 1) stored], predicates := [] }).exprs), []⟩ { exprs := [Expr.mkEq (.stack 0 32) (solve (Term.V32 7))], predicates := [] }).exprs)) | return false
  let byte (n : Nat) : Term := .app .w32 (.low 8 32) [.C32 n]
  let some E := ((«seal» (Reg.stack 32 40).bits (byte 0x11) >>= fun stored => some (update ⟨E, []⟩ { exprs := [Expr.mkEq (.stack 32 40) stored], predicates := [] }).exprs)) | return false
  let some E := ((«seal» (Reg.map 3 key 0 8).bits (byte 9) >>= fun stored => some (update ⟨E, []⟩ { exprs := [Expr.mkEq (.map 3 key 0 8) stored], predicates := [] }).exprs)) | return false
  let σ : State := ⟨E, []⟩
  let (exprs, preds) := renderStateJson σ
  match parseStateJson s!"[{exprs}]" s!"[{preds}]" with
  | some σ' =>
      σ'.exprs == E &&
        σ'.exprs.lookupEq (Reg.real64 1) == some (Term.V64 1) &&
        σ'.exprs.lookupEq (.stack 0 32) == E.lookupEq (.stack 0 32) &&
        σ'.exprs.lookupEq (.stack 32 40) == E.lookupEq (.stack 32 40) &&
        σ'.exprs.lookupEq (.map 3 key 0 8) == E.lookupEq (.map 3 key 0 8)
  | none => false
#guard (parseStateJson
  "[{\"role\":\"mem\",\"slot\":\"stack\",\"pieces\":[{\"start\":0,\"slice\":{\"k\":\"c\",\"w\":7,\"v\":1}}]}]"
  "[]").isNone
#guard (parseStateJson "{}" "[]").isNone
#guard (parseTerm "add32(v32:1,)").isNone
#guard (parseReg "packet64:0").isNone

end Wire
