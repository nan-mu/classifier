import Verification.Obligation
import Verification.Verified.HelperProjection
import Verification.Verified.UnifyMatch

namespace Verification.Verified.Acceptance

open Core Verification.Obligation Verification.Verified.UnifyMatch

/-!
What acceptance currently supports is the structural alignment of projected
observations.

`MeaningsAgree` does not follow. `update_flag_denotation_lost` is a pair of
original observations whose projections coincide and whose argument
denotations differ. RV32 safety is not derived from eBPF safety here.
-/

theorem accept_is_structural (a : Accepts) :
    CrossSubst.Injective
      (unifyLists (a.left.map (toCross a.envL)) (a.right.map (toCross a.envR))).subst ∧
    MaximumAlignment
      (a.left.map (toCross a.envL)) (a.right.map (toCross a.envR))
      (matched a) ∧
    (∀ i j, (i, j) ∈ matched a →
      ∃ u v,
        (a.left.map (toCross a.envL))[i]? = some u ∧
        (a.right.map (toCross a.envR))[j]? = some v ∧
        CrossSubst.rename
          (unifyLists (a.left.map (toCross a.envL)) (a.right.map (toCross a.envR))).subst u = v) ∧
    (unifyLists (a.left.map (toCross a.envL)) (a.right.map (toCross a.envR))).pairs.length =
      a.left.length ∧
    a.left.length = a.right.length := by
  have h := unify_structural
    (a.left.map (toCross a.envL)) (a.right.map (toCross a.envR))
  have hlen := h.2.2.2.1.mp a.pass
  refine ⟨h.1, h.2.1, h.2.2.1, ?_, ?_⟩
  · simpa [List.length_map] using hlen.1
  · simpa [List.length_map] using hlen.2

/-- Structural acceptance of a projection does not imply `MeaningsAgree`. -/
theorem projection_acceptance_misses_flag_meaning :
    ∃ (p q : Predicate) (env : CrossEnv) (c : SharedCondition),
      toCross env p = toCross env q ∧
      denotePred c.νL c.θL p ≠ denotePred c.νR c.θR q := by
  let map : Term := .var .w64 0
  let args (f : Term) : List Term :=
    Verification.Verified.HelperProjection.flagArgs map (.C64 0) (.C64 0) f [.C64 1, .C64 2]
  let p : Predicate := .helper 0 .update (args (.C64 0))
  let q : Predicate := .helper 0 .update (args (.C64 1))
  let layout : CrossMapLayout := { map := toCrossTerm map, keyBytes := 1, valueBytes := 1 }
  let env : CrossEnv := { maps := [layout] }
  let c : SharedCondition := {
    νL := fun _ => 0
    νR := fun _ => 0
    θL := { externalResult := fun _ _ _ _ => none, inputByte := fun _ _ _ => none }
    θR := { externalResult := fun _ _ _ _ => none, inputByte := fun _ _ _ => none }
    resource := fun _ => True
    external := True
  }
  refine ⟨p, q, env, c, ?_, ?_⟩
  · have h := Verification.Verified.HelperProjection.update_flags_erased env layout map
      (.C64 0) (.C64 0) (.C64 0) (.C64 1) [.C64 1] [.C64 2]
      (by simp [env, layout, map]) (by decide) (by decide) (by decide)
    have h' :
        toCrossHelper env .update (args (.C64 0)) =
          toCrossHelper env .update (args (.C64 1)) := by
      unfold args Verification.Verified.HelperProjection.flagArgs
      rw [show ([.C64 1, .C64 2] : List Term) = [.C64 1] ++ [.C64 2] from rfl]
      exact h
    unfold toCross
    simp only [p, q]
    rw [h']
  · have hden := (Verification.Verified.HelperProjection.update_flag_denotation_lost).2
    simp only [denotePred, predArgs, p, q, c]
    unfold Verification.Verified.HelperProjection.denoteArgs
      Verification.Verified.HelperProjection.flagList
      Verification.Verified.HelperProjection.flagArgs
      Verification.Verified.HelperProjection.θ0
      Verification.Verified.HelperProjection.flagMap at hden
    exact hden

/-- Conditional last step. `ValuationFollows`, `ArgsFaithful` and
`RenamePreservesArguments` are not proved. `ArgsFaithful` fails for the flag
pair above, so this does not apply to every passing projection. Entry, step,
history and path coverage are further premises of those three, not inputs of
this function. -/
theorem meanings_if_arguments_survive
    (c : SharedCondition) (a : Accepts)
    (hval : ValuationFollows c a) (hren : RenamePreservesArguments c a)
    (hfaith : ArgsFaithful a) :
    MeaningsAgree c a := by
  exact ⟨hren hval hfaith, hval.2.2, hval.2.1⟩

end Verification.Verified.Acceptance
