import ClassifierExpr.Bits
import ClassifierExpr.Reg
import ClassifierExpr.Op
import ClassifierExpr.Term
import ClassifierExpr.Expr
import ClassifierExpr.Insn

namespace ClassifierExpr

/-! ## Compact string renderers for SemState JSON (`doc/NodeInference/step.md#语义状态与节点状态`) -/

def renderWidth : Width → String
  | .w32 => "32"
  | .w64 => "64"

def renderRegKind : RegKind → String
  | .real => "real"
  | .stack => "stack"
  | .map => "map"
  | .packet => "packet"

def renderReg (r : Reg) : String :=
  s!"{renderRegKind r.kind}{renderWidth r.width}:{r.alpha}"

def renderRel : Rel → String
  | .eq => "eq" | .ne => "ne"
  | .ltu => "ltu" | .leu => "leu" | .gtu => "gtu" | .geu => "geu"
  | .lts => "lts" | .les => "les" | .gts => "gts" | .ges => "ges"
  | .eqN q => s!"eqN{q}" | .neN q => s!"neN{q}"
  | .ltuN q => s!"ltuN{q}" | .leuN q => s!"leuN{q}"
  | .gtuN q => s!"gtuN{q}" | .geuN q => s!"geuN{q}"
  | .ltsN q => s!"ltsN{q}" | .lesN q => s!"lesN{q}"
  | .gtsN q => s!"gtsN{q}" | .gesN q => s!"gesN{q}"
  | .bitsnz q => s!"bitsnz{q}" | .bitsz q => s!"bitsz{q}"

def renderOp : Op → String
  | .add w => s!"add{renderWidth w}"
  | .sub w => s!"sub{renderWidth w}"
  | .mullo w => s!"mullo{renderWidth w}"
  | .neg w => s!"neg{renderWidth w}"
  | .id w => s!"id{renderWidth w}"
  | .and q => s!"and{q}"
  | .or q => s!"or{q}"
  | .xor q => s!"xor{q}"
  | .shl w => s!"shl{renderWidth w}"
  | .lshr w => s!"lshr{renderWidth w}"
  | .ashr w => s!"ashr{renderWidth w}"
  | .ltu w => s!"ltu{renderWidth w}"
  | .lts w => s!"lts{renderWidth w}"
  | .low q _ => s!"low{q}"
  | .extract o ℓ _ => s!"extract{o},{ℓ}"
  | .zext q w _ => s!"zext{q}/{renderWidth w}"
  | .sext q w _ => s!"sext{q}/{renderWidth w}"
  | .bswap q _ => s!"bswap{q}"
  | .externalResult event lane => s!"externalResult{event}_{lane}"
  | .inputByte resource => s!"inputByte{resource}"
  | .mergeLow q wbits => s!"mergeLow{q},{wbits}"

partial def renderTerm : Term → String
  | .const _ c => toString c
  | .var w ξ => s!"v{renderWidth w}:{ξ}"
  | .regVar event reg => s!"regVar{event}({renderReg reg})"
  | .app _ op args =>
      let body := String.intercalate "," (args.map renderTerm)
      s!"{renderOp op}({body})"


/-- Predicate terms preserve mixed-width constants and operator input widths.
The existing Expr and Helper term encoding remains unchanged. -/
private partial def renderPredicateTerm (context : Width) : Term → String
  | .const w c =>
    if w == context then toString c else s!"c{renderWidth w}:{c}"
  | .var w ξ => s!"v{renderWidth w}:{ξ}"
  | .regVar event reg => s!"regVar{event}({renderReg reg})"
  | .app w op args =>
    let name := match op with
      | .low q v => if v == w.bits then renderOp op else s!"low{q}/{v}"
      | .extract o len v => if v == w.bits then renderOp op else s!"extract{o},{len}/{v}"
      | .zext q out v => if v == out.bits then renderOp op else s!"zext{q}/{renderWidth out}/{v}"
      | .sext q out v => if v == out.bits then renderOp op else s!"sext{q}/{renderWidth out}/{v}"
      | .bswap q v => if v == w.bits then renderOp op else s!"bswap{q}/{v}"
      | _ => renderOp op
    let input := match op with
      | .low _ v | .extract _ _ v | .zext _ _ v | .sext _ _ v | .bswap _ v =>
        if v == 64 then Width.w64 else .w32
      | _ => w
    let body := String.intercalate "," (args.map (renderPredicateTerm input))
    let body := s!"{name}({body})"
    if w == context then body else s!"t{renderWidth w}({body})"
def renderExprJson (e : Expr) : String :=
  s!"\{\"reg\":\"{renderReg e.reg}\",\"rel\":\"{renderRel e.rel}\",\"term\":\"{renderTerm e.term}\"}"

def renderPredicateJson : Predicate → String
  | .helper event kind args =>
    let args := String.intercalate "," (args.map fun t => s!"\"{renderTerm t}\"")
    s!"\{\"kind\":\"helper\",\"event\":{event},\"helperId\":{kind.id},\"args\":[{args}]}"
  | .branch position dir cond =>
    let direction := match dir with | .taken => "taken" | .notTaken => "notTaken"
    let w := cond.lhs.width
    s!"\{\"kind\":\"branch\",\"position\":{position},\"dir\":\"{direction}\",\"width\":{w.bits},\"cond\":\{\"lhs\":\"{renderPredicateTerm w cond.lhs}\",\"rel\":\"{renderRel cond.rel}\",\"rhs\":\"{renderPredicateTerm w cond.rhs}\"}}"
  | .ret term =>
    s!"\{\"kind\":\"ret\",\"width\":{term.width.bits},\"term\":\"{renderPredicateTerm term.width term}\"}"
  | .mapWrite event map key offset source =>
    let keys := String.intercalate "," (key.map fun t => s!"\"{renderPredicateTerm .w32 t}\"")
    s!"\{\"kind\":\"mapWrite\",\"event\":{event},\"mapWidth\":{map.width.bits},\"map\":\"{renderPredicateTerm map.width map}\",\"key\":[{keys}],\"offset\":{offset},\"sourceWidth\":{source.width.bits},\"source\":\"{renderPredicateTerm source.width source}\"}"
  | .packetWrite event packet offset source =>
    s!"\{\"kind\":\"packetWrite\",\"event\":{event},\"packet\":{packet},\"offset\":{offset},\"width\":{source.width.bits},\"source\":\"{renderPredicateTerm source.width source}\"}"
def renderExprSetJson (E : ExprSet) : String :=
  String.intercalate "," (E.entries.map renderExprJson ++ E.constraints.map fun e =>
    s!"\{\"reg\":\"{renderReg e.reg}\",\"rel\":\"{renderRel e.rel}\",\"term\":\"{renderTerm e.term}\",\"role\":\"constraint\"}")

def renderPredicatesJson (ps : List Predicate) : String :=
  String.intercalate "," (ps.map renderPredicateJson)

def renderSemStateJson (σ : SemState) : String × String :=
  (renderExprSetJson σ.exprs, renderPredicatesJson σ.predicates)

end ClassifierExpr
