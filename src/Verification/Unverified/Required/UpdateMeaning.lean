import Expression.Interval
import Verification.Verified.StateUpdate

namespace Verification.Unverified.Required.UpdateMeaning

open Term Term.Value Expression Observation Interface Interface.Step

/-!
`assign_lookup` / `kept_lookup` identify exact intervals that are already
bindings. `low_byte_split` is the single shape `[0,8)` / `[8,32)` of one real
register.

A general probe has its own bit length. The write covers it, misses it, or
meets it partially. `readInterval` is partial and returns `none` on a hole.
Those three readings are not theorems yet. `sliceTerm` is private, so the
expected extract is written with the public `Op.extract` constructor.
-/

def Covered (w probe : Reg) : Prop :=
  w.sameResource probe = true ∧ w.lo ≤ probe.lo ∧ probe.hi ≤ w.hi ∧ probe.lo < probe.hi

def Misses (w probe : Reg) : Prop :=
  w.overlaps probe = false ∧ probe.lo < probe.hi

/-- Bits of `t` that sit at `probe` inside a covering write `w`. -/
def extractWritten (w probe : Reg) (t : Term) : Term :=
  if probe.lo = w.lo ∧ probe.hi = w.hi then t
  else
    .app (Width.ofBits probe.bits)
      (.extract (probe.lo - w.lo) probe.bits t.width.bits) [t]

/-- A covered probe reads as that extract, and the extract denotes the same
value as the corresponding bits of `t`. -/
def CoveredRead (parent : State) (w : Reg) (t : Term) : Prop :=
  ∀ probe, Covered w probe →
    readInterval
      (update parent { exprs := [Expr.mkEq w t], predicates := [] }).exprs probe =
      some (extractWritten w probe t)

/-- A probe that misses the write reads exactly as it did before, when the
old read was defined. -/
def MissRead (parent : State) (w : Reg) (t : Term) : Prop :=
  ∀ probe old, Misses w probe →
    readInterval parent.exprs probe = some old →
    readInterval
      (update parent { exprs := [Expr.mkEq w t], predicates := [] }).exprs probe =
      some old

/-- sorry: required obligation, not a proof. -/
theorem covered_probe_reads_extract
    (parent : State) (w : Reg) (t : Term)
    (hw : w.lo < w.hi) (hp : valueSeparated parent.exprs)
    (ht : t.semanticBits = w.bits) :
    CoveredRead parent w t := by
  sorry

/-- sorry: required obligation, not a proof.
`kept_lookup` is the special case where `probe` is already a binding and
`lookupEq` is used instead of `readInterval`. -/
theorem missed_probe_keeps_old_read
    (parent : State) (w : Reg) (t : Term)
    (hw : w.lo < w.hi) (hp : valueSeparated parent.exprs) :
    MissRead parent w t := by
  sorry

end Verification.Unverified.Required.UpdateMeaning
