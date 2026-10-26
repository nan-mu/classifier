import Node.Drive

namespace Verification.Verified.HistoryAndPath

open Term Term.Value Expression Observation Interface Interface.Step Wire Node

/-!
`observation_dep_not_ignorable` says a register already in `observationDeps`
is absent from `history`. It does not say that `observationDeps` contains
every semantic dependency, and it does not say that a difference on a
`history` register leaves later observations unchanged.

Equal states do have equal successors, because `step` and `driveStandard` are
functions. That fact is not applied to the ignorable-difference induction.
-/

theorem history_iff_written_and_not_dependent
    (steps : List (List Expr × List Observation)) (entry : List Expr) (r : Reg) :
    r ∈ history steps entry ↔
      r ∈ (steps.flatMap fun (exprs, _) => exprs.bindings.map (·.reg)).eraseDups ∧
      r ∉ observationDeps entry steps := by
  unfold history
  constructor
  · intro hr
    obtain ⟨hm, hc⟩ := List.mem_filter.mp hr
    refine ⟨hm, ?_⟩
    intro hd
    rw [show (observationDeps entry steps).contains r = true from
      List.contains_iff_mem.mpr hd] at hc
    simp at hc
  · intro ⟨hm, hd⟩
    refine List.mem_filter.mpr ⟨hm, ?_⟩
    simp [hd]

theorem dependency_blocks_ignoring
    (steps : List (List Expr × List Observation)) (entry : List Expr) (r : Reg)
    (h : r ∈ observationDeps entry steps) : r ∉ history steps entry :=
  observation_dep_not_ignorable steps entry r h

theorem drive_equal_states
    (step : Nat → State → StepResult) (progLen j : Nat) {σ τ : State}
    (h : σ = τ) :
    driveStandard step progLen j σ = driveStandard step progLen j τ := by
  subst h
  rfl

theorem step_equal_states
    (step : Nat → State → StepResult) (j : Nat) {σ τ : State} (h : σ = τ) :
    step j σ = step j τ := by
  subst h
  rfl

/-- Accumulated predicate lists drop a repeated observation. Repetition counts
have to come from the per-step record, not from `State.predicates`. -/
theorem duplicate_observation_is_dropped
    (parent : State) (p : Observation) (h : parent.predicates.contains p = true) :
    (update parent { exprs := [], predicates := [p] }).predicates = parent.predicates := by
  rw [update_predicates]
  simp [h]

/-- Value rows may differ only on `covered`. This is the history side condition,
not state equality. -/
def ExprIgnorable (covered : List Reg) (σ τ : State) : Prop :=
  diffCovered σ.exprs τ.exprs covered = true

/-- One linear step, or a common rejection / empty result, preserves the
ignorable relation. Branching steps are outside this hypothesis: two candidate
lists make it false. -/
def StepPreserves (step : Nat → State → StepResult) (covered : List Reg) : Prop :=
  ∀ j σ τ, ExprIgnorable covered σ τ →
    match step j σ, step j τ with
    | .reject a, .reject b => a = b
    | .candidates [], .candidates [] => True
    | .candidates [cσ], .candidates [cτ] =>
        cσ.dir = cτ.dir ∧ cσ.loc = cτ.loc ∧ cσ.P_k = cτ.P_k ∧
          match cσ.loc with
          | .exit => True
          | .pos _ =>
              ExprIgnorable covered
                (update σ { exprs := cσ.E_k, predicates := cσ.P_k })
                (update τ { exprs := cτ.E_k, predicates := cτ.P_k })
    | _, _ => False

/-- Observations of a single linear walk, one `P_k` per step, duplicates kept. -/
def linearTrace (step : Nat → State → StepResult) :
    Nat → Nat → State → List (List Observation)
  | 0, _, _ => []
  | fuel + 1, j, σ =>
      match step j σ with
      | .candidates [c] =>
          match c.loc with
          | .exit => [c.P_k]
          | .pos k =>
              c.P_k :: linearTrace step fuel k
                (update σ { exprs := c.E_k, predicates := c.P_k })
      | _ => []

theorem linearTrace_equal_states
    (step : Nat → State → StepResult) (fuel j : Nat) {σ τ : State}
    (h : σ = τ) :
    linearTrace step fuel j σ = linearTrace step fuel j τ := by
  subst h
  rfl

/-- Finite linear observations agree if every ignorable pair has the same
linear step and the successors stay ignorable. Equal-state agreement above is
not the argument. -/
theorem linearTrace_of_step_preservation
    (step : Nat → State → StepResult) (covered : List Reg)
    (h : StepPreserves step covered) :
    ∀ fuel j σ τ, ExprIgnorable covered σ τ →
      linearTrace step fuel j σ = linearTrace step fuel j τ := by
  intro fuel
  induction fuel with
  | zero =>
    intro j σ τ _
    rfl
  | succ fuel ih =>
    intro j σ τ hign
    have hpres := h j σ τ hign
    cases hσ : step j σ with
    | reject _ =>
      cases hτ : step j τ with
      | reject _ => simp [linearTrace, hσ, hτ]
      | candidates cs =>
        rw [hσ, hτ] at hpres
        cases cs with
        | nil => exact False.elim hpres
        | cons _ rest =>
          cases rest with
          | nil => exact False.elim hpres
          | cons _ _ => exact False.elim hpres
    | candidates cs =>
      cases hτ : step j τ with
      | reject _ =>
        rw [hσ, hτ] at hpres
        cases cs with
        | nil => exact False.elim hpres
        | cons _ rest =>
          cases rest with
          | nil => exact False.elim hpres
          | cons _ _ => exact False.elim hpres
      | candidates ct =>
        rw [hσ, hτ] at hpres
        simp only [linearTrace, hσ, hτ]
        cases cs with
        | nil =>
          cases ct with
          | nil => rfl
          | cons _ _ => exact False.elim hpres
        | cons cσ rest =>
          cases rest with
          | cons _ _ => exact False.elim hpres
          | nil =>
            cases ct with
            | nil => exact False.elim hpres
            | cons cτ rest' =>
              cases rest' with
              | cons _ _ => exact False.elim hpres
              | nil =>
                obtain ⟨_, hloc, hobs, hnext⟩ := hpres
                cases hlocσ : cσ.loc with
                | exit =>
                  rw [hlocσ] at hloc
                  have hτloc : cτ.loc = .exit := hloc.symm
                  simp [hlocσ, hτloc, hobs]
                | pos k =>
                  rw [hlocσ] at hloc hnext
                  have hτloc : cτ.loc = .pos k := hloc.symm
                  simp only [hlocσ, hτloc]
                  rw [hobs] at hnext ⊢
                  apply congrArg (List.cons cτ.P_k)
                  exact ih k
                    (update σ { exprs := cσ.E_k, predicates := cτ.P_k })
                    (update τ { exprs := cτ.E_k, predicates := cτ.P_k })
                    hnext

/-- At the parent, a step that still offers both directions is rejected.
This is the driver's reaction. It is not `live_constraint_excludes_both`. -/
theorem both_directions_rejected
    (step : Nat → State → StepResult) (progLen parent : Nat)
    (parentState hereState old : State)
    (interval : List (List Expr × List Observation)) (loopsLeft : Nat)
    (cs : List Candidate)
    (hstep : step parent hereState = .candidates cs)
    (hnt : (cs.find? (·.dir == .notTaken)).isSome = true)
    (htk : (cs.find? (·.dir == .taken)).isSome = true) :
    driveTaken step progLen parent parentState hereState old parent interval loopsLeft =
      .stop (.reject .localReject) := by
  obtain ⟨cN, hN⟩ := Option.isSome_iff_exists.mp hnt
  obtain ⟨cT, hT⟩ := Option.isSome_iff_exists.mp htk
  have hdN := List.find?_some hN
  have hdT := List.find?_some hT
  have hmemN := List.mem_of_find?_eq_some hN
  have hmemT := List.mem_of_find?_eq_some hT
  have hne : cN ≠ cT := by
    intro h
    subst h
    cases hdir : cN.dir with
    | ok =>
      rw [hdir] at hdN
      rw [show (Direction.ok == Direction.notTaken) = false by rfl] at hdN
      cases hdN
    | taken =>
      rw [hdir] at hdN
      rw [show (Direction.taken == Direction.notTaken) = false by rfl] at hdN
      cases hdN
    | notTaken =>
      rw [hdir] at hdT
      rw [show (Direction.notTaken == Direction.taken) = false by rfl] at hdT
      cases hdT
  have hlong : ∃ a b rest, cs = a :: b :: rest := by
    cases cs with
    | nil => cases hmemN
    | cons a rest =>
      cases rest with
      | nil =>
        simp at hmemN hmemT
        exact False.elim (hne (hmemN.trans hmemT.symm))
      | cons b rest => exact ⟨a, b, rest, rfl⟩
  obtain ⟨a, b, rest, hcs⟩ := hlong
  rw [hcs] at hN hT
  unfold driveTaken
  have hparent : (parent != parent) = false := by
    show (!(parent == parent)) = false
    rw [beq_self_eq_true]
    rfl
  simp only [hparent, hstep, hcs, hN, hT]
  rfl

end Verification.Verified.HistoryAndPath
