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
    ("map", .map), ("packet", .packet) ].findSome? fun (stem, kind) => do
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
  private partial def parseTermChars (w : Width) (chars : List Char) :
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
      if let some event := suffixNat "regVar" name then
        let (reg, tail) := tail.span (· != ')')
        let ')' :: tail := tail | none
        return (.regVar event (← parseReg (String.ofList reg)), tail)
      let op ← parseOp name w
      let width := opWidth w op
      let (args, tail) ← parseTermArgs width tail
      if let some arity := opArity op then
        if args.length != arity then none else pure ()
      return (.app width op args, tail)
    | _ =>
      if let some n := name.toNat? then
        if n ≥ 2 ^ w.bits then none else pure (.const w n, rest)
      else
        let [width, id] := name.splitOn ":" | none
        let width ← if width == "v32" then some Width.w32
          else if width == "v64" then some Width.w64 else none
        return (.var width (← id.toNat?), rest)

  private partial def parseTermArgs (w : Width) (chars : List Char) :
      Option (List Term × List Char) := do
    if let ')' :: tail := chars then return ([], tail)
    let (term, rest) ← parseTermChars w chars
    match rest with
    | ')' :: tail => pure ([term], tail)
    | ',' :: tail =>
      if let ')' :: _ := tail then none else do
        let (terms, tail) ← parseTermArgs w tail
        pure (term :: terms, tail)
    | _ => none
end

/-- Rendered constants omit width; the containing register supplies it (helper arguments use 32). -/
def parseTerm (text : String) (w : Width := .w32) : Option Term := do
  let (term, []) ← parseTermChars w text.toList | none
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

def parsePredicateJson (value : Lean.Json) : Option Predicate := do
  match ← jsonString value "kind" with
  | "helper" =>
    let event ← (value.getObjVal? "event" >>= Lean.Json.getNat?).toOption
    let id ← (value.getObjVal? "helperId" >>= Lean.Json.getNat?).toOption
    let args ← (value.getObjVal? "args" >>= Lean.Json.getArr?).toOption
    let args ← args.toList.mapM fun a => do parseTerm (← a.getStr?.toOption)
    return .helper event (helperKind id) args
  | _ => none

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
  let regs := [Reg.real32 10, Reg.sw 8, Reg.mapWord 7 4, Reg.packet 3 2, Reg.real64 1]
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

private def constraintRoundTripCheck : Bool :=
  let E := ExprSet.empty.insertEq (Reg.real64 1) (Term.V64 1)
    |>.insertConstraint (Expr.mkRel (Reg.real64 1) .eq (Term.C64 10))
    |>.insertConstraint (Expr.mkRel (Reg.real64 1) (.ltuN 32) (Term.C64 20))
  match parseSemStateJson ("[" ++ renderExprSetJson E ++ "]") "[]" with
  | some state => state.exprs == E && state.exprs.lookupEq (Reg.real64 1) == some (Term.V64 1)
  | none => false

#guard constraintRoundTripCheck
#guard (parseSemStateJson "[]" "[{\"kind\":\"cmp\",\"width\":32,\"rel\":\"eq\",\"lhs\":\"0\",\"rhs\":\"0\"}]").isNone
#guard (parseSemStateJson "[]" "[{\"kind\":\"ret\",\"term\":\"2\"}]").isNone
#guard parseRoundTripCheck
#guard parseOpsRoundTripCheck
#guard (parseSemStateJson "{}" "[]").isNone
#guard (parseTerm "add32(v32:1,)").isNone
#guard (parseReg "packet64:0").isNone

end ClassifierExpr
