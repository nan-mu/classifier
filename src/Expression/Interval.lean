import Expression.Basic
import Interface.Update

namespace Expression
open Term Term.Value Interface

def «seal» (n : Nat) (t : Term) : Option Term := do
  let solved := solve t
  if solved.semanticBits == n then return solved
  if n == 0 || solved.width.bits < n then failure
  pure <| .app (Width.ofBits n) (.low n solved.width.bits) [solved]

/-- Project `len` bits at `offset` in the carrier. A term that already has that length is unchanged. -/
private def sliceTerm (t : Term) (offset len : Nat) : Term :=
  if offset == 0 && len == t.semanticBits then t
  else
    let carrier := t.width.bits
    let out := Width.ofBits len
    .app out (.extract offset len carrier) [t]

private def placeLow (t : Term) (shift total : Nat) : Term :=
  let w := Width.ofBits total
  let base := zStar t.semanticBits w t.width.bits t
  if shift == 0 then base else star w (.shl w) [base, Term.C w shift]

private def mergeBits (a b : Term) (total : Nat) : Term :=
  let w := Width.ofBits total
  star w (.or total) [zStar a.semanticBits w a.width.bits a,
    zStar b.semanticBits w b.width.bits b]

private def appendPiece (acc : Option Term) (part : Term) (shift total : Nat) : Term :=
  match acc with
  | none => part
  | some prev => mergeBits (placeLow prev 0 total) (placeLow part shift total) total

/-- Read `[r.lo, r.hi)`. Exact equalities are reused. Fragments are concatenated.
A hole or an overlap leaves the read undefined. -/
partial def readInterval (E : List Expr) (r : Reg) : Option Term := do
  if !r.valid || !E.wellTyped then failure
  if let some t := E.lookupEq r then
    if t.semanticBits == r.bits then return t
  let pieces := (E.bindings.filter fun e =>
    e.reg.sameResource r && e.reg.lo < r.hi && r.lo < e.reg.hi).mergeSort
    fun a b => a.reg.lo ≤ b.reg.lo
  let rec go (rest : List Expr) (cursor : Nat) (acc : Option Term) : Option Term :=
    match rest with
    | [] => if cursor == r.hi then acc else none
    | e :: rest =>
      if e.reg.lo > cursor then none
      else if cursor < e.reg.hi then
        let take := min e.reg.hi r.hi - cursor
        if take == 0 then go rest cursor acc
        else
          let part := sliceTerm e.term (cursor - e.reg.lo) take
          go rest (cursor + take) (some (appendPiece acc part (cursor - r.lo) (r.bits)))
      else go rest cursor acc
  «seal» r.bits (← go pieces r.lo none)

def putContext (E : List Expr) (j : ContextField) (t : Term) : Option (List Expr) := do
  let n := t.semanticBits
  if n == 0 || j.cap < n then failure
  let stored ← «seal» n t
  some (update ⟨E, []⟩ { exprs := [Expr.mkEq (.context j 0 n) stored], predicates := [] }).exprs

/-- The field's interval that starts at bit 0. Absence means create did not install it. -/
def contextValue (E : List Expr) (j : ContextField) : Option Term :=
  E.bindings.findSome? fun e =>
    match e.reg with
    | .context i 0 _ => if i == j then some e.term else none
    | _ => none

def contextNat (E : List Expr) (j : ContextField) : Option Nat := do
  eval (solve (← contextValue E j))

def ContextField.ofXdp : Nat → Option ContextField
  | 0 => some .data
  | 1 => some .dataEnd
  | 2 => some .dataMeta
  | 3 => some .ingressIfindex
  | 4 => some .rxQueueIndex
  | 5 => some .egressIfindex
  | _ => none

def xdpFields : List ContextField :=
  [.data, .dataEnd, .dataMeta, .ingressIfindex, .rxQueueIndex, .egressIfindex]

/-- The six `xdp_md` words are present as `[0,32)` context equalities. -/
def contextReady (E : List Expr) : Bool :=
  xdpFields.all fun j => (E.lookupEq (.context j 0 32)).isSome

end Expression
