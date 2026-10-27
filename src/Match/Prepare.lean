import Observation.Insn
import Term.Basic
import Expression.Basic
import Wire.Parse
import Wire.Render

namespace Match
open Term Term.Value Expression Observation Wire

/-! Prepare one observation for comparison.

`solve` folds closed terms and sorts an addition. A branch whose rendered
left term is greater than its right term swaps the operands and applies
`Rel.swap`. Helper arguments, including a flags word, stay in the argument
list. -/

def orderCond (c : Cond) : Cond :=
  let lhs := solve c.lhs
  let rhs := solve c.rhs
  if compare (renderTerm lhs) (renderTerm rhs) == .gt then
    { lhs := rhs, rel := c.rel.swap, rhs := lhs }
  else
    { lhs, rel := c.rel, rhs }

def prepare : Observation → Observation
  | .helper event kind args => .helper event kind (args.map solve)
  | .branch position dir cond => .branch position dir (orderCond cond)
  | .ret term => .ret (solve term)
  | .mapWrite map key offset bits source =>
    .mapWrite (solve map) (key.map solve) offset bits (solve source)
  | .packetWrite offset bits source => .packetWrite offset bits (solve source)

/-- Hat of one observation. Failure is `{"status":"fail","reason":"LocalReject"}`. -/
@[export lean_match_prepare]
def exportMatchPrepare (predJson : String) : String :=
  match Lean.Json.parse predJson with
  | .ok pred =>
    match parsePredicateJson pred with
    | some p =>
      s!"\{\"status\":\"ok\",\"observation\":{renderPredicateJson (prepare p)}}"
    | none => "{\"status\":\"fail\",\"reason\":\"LocalReject\"}"
  | .error _ => "{\"status\":\"fail\",\"reason\":\"LocalReject\"}"

end Match
