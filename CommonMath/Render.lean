import CommonMath.Bits
import CommonMath.Reg
import CommonMath.Op
import CommonMath.Term
import CommonMath.Expr
import CommonMath.Insn
import CommonMath.Path

namespace CommonMath

/-! ## Compact string renderers for SemState JSON (`doc/common-math.md` §12) -/

def renderWidth : Width → String
  | .w32 => "32"
  | .w64 => "64"

def renderRegKind : RegKind → String
  | .real => "real"
  | .stack => "stack"
  | .map => "map"

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
  | .inputByte => "inputByte"
  | .mergeLow q wbits => s!"mergeLow{q},{wbits}"

partial def renderTerm : Term → String
  | .const _ c => toString c
  | .var w ξ => s!"v{renderWidth w}:{ξ}"
  | .app _ op args =>
      let body := String.intercalate "," (args.map renderTerm)
      s!"{renderOp op}({body})"

def renderExprJson (e : Expr) : String :=
  s!"\{\"reg\":\"{renderReg e.reg}\",\"rel\":\"{renderRel e.rel}\",\"term\":\"{renderTerm e.term}\"}"

def renderPredicateJson : Predicate → String
  | .ret value =>
    s!"\{\"kind\":\"ret\",\"term\":\"{renderTerm value}\"}"
  | .cmp rel lhs rhs =>
    -- rel is the complete effective relation; no redundant atom/polarity fields.
    s!"\{\"kind\":\"cmp\",\"rel\":\"{renderRel rel}\",\"width\":32,\"lhs\":\"{renderTerm lhs}\",\"rhs\":\"{renderTerm rhs}\"}"

def renderExprSetJson (E : ExprSet) : String :=
  String.intercalate "," (E.entries.map renderExprJson)

def renderPredicatesJson (ps : List Predicate) : String :=
  String.intercalate "," (ps.map renderPredicateJson)

def renderSemStateJson (σ : SemState) : String × String :=
  (renderExprSetJson σ.exprs, renderPredicatesJson σ.predicates)

end CommonMath
