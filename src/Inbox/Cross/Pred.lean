import Observation.Insn
import Term.Basic
import Expression.Basic
import Inbox.Wire.Parse
import Inbox.Wire.Render

namespace Inbox.Cross
open Term Term.Value Expression Observation Inbox.Wire

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
  | .helper kind args => .helper kind (args.map solve)
  | .branch position dir cond => .branch position dir (orderCond cond)
  | .ret term => .ret (solve term)
  | .mapWrite map key offset bits source =>
    .mapWrite (solve map) (key.map solve) offset bits (solve source)
  | .packetWrite offset bits source => .packetWrite offset bits (solve source)

/-- Boxed Lean String ABI. `envJson` must be a JSON object and is not part of
the observation. A predicate that is not one of the five classes returns `null`. -/
@[export lean_cross_pred_normalize]
def exportCrossPredNormalize (envJson predJson : String) : String :=
  match Lean.Json.parse envJson, Lean.Json.parse predJson with
  | .ok env, .ok pred =>
    match env.getObj? with
    | .ok _ =>
      match parsePredicateJson pred with
      | some p => renderPredicateJson (prepare p)
      | none => "null"
    | .error _ => "null"
  | _, _ => "null"

end Inbox.Cross
