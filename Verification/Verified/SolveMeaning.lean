import Core.SolvePreservation

namespace Verification.Verified.SolveMeaning

open Core

/-!
`solve` is the simplifier used when expressions are built. Preservation of
`interpretTerm` is not instruction correctness and is not a statement about
`update`.
-/

/-- R1–R6, closed folds, shifts, and disjoint ors preserve a well-formed term
under a total external interpretation. -/
theorem solve_preserves_interpretation
    (ν : Var → Nat) (θ : ExternalInterpretation) (hθ : θ.Total)
    (t : Term) (ht : t.wellFormed = true) :
    interpretTerm ν θ (solve t) = interpretTerm ν θ t :=
  solve_interpret ν θ hθ t ht

theorem normalize_preserves_interpretation
    (ν : Var → Nat) (θ : ExternalInterpretation) (hθ : θ.Total)
    (t : Term) (ht : t.wellFormed = true) :
    interpretTerm ν θ (normalizeAlgebra t) = interpretTerm ν θ t :=
  normalizeAlgebra_interpret ν θ hθ t ht

theorem liftInteger_preserves_interpretation
    (ν : Var → Nat) (θ : ExternalInterpretation) (hθ : θ.Total)
    (t : Term) (ht : t.wellFormed = true) :
    interpretTerm ν θ (liftInteger t) = interpretTerm ν θ t :=
  liftInteger_interpret ν θ hθ t ht

/-- A missing external result stays missing. Simplification is not allowed to
invent it. -/
theorem external_result_stays_missing
    (ν : Var → Nat) (θ : ExternalInterpretation)
    (w : Width) (event lane : Nat) (args : List Term) (values : List Nat)
    (hs : (Op.externalResult event lane).validSignature w (args.map Term.width) = true)
    (ha : interpretTerms ν θ args = some values)
    (hm : θ.externalResult w event lane values = none) :
    interpretTerm ν θ (.app w (.externalResult event lane) args) = none :=
  interpretTerm_external_missing ν θ w event lane args values hs ha hm

end Verification.Verified.SolveMeaning
