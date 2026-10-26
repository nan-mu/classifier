import Interface.Update

namespace Verification.Verified.StateUpdate

open Term Term.Value Expression Observation Interface Interface.Step

/-!
Exact-interval consequences of `update`.

Three separate claims:

1. The resulting value rows are pairwise non-overlapping, a non-overlapping
   row is kept, and the written row is installed.
2. The exact written interval reads back as the term that was supplied, and
   an exact non-overlapping interval reads back as the same term.
3. A machine instruction generated that term.

(1) and the exact-interval half of (2) are proved here from `Interface.Update`.
Proper sub-intervals and holes are not. (3) is not a theorem about `update`.
-/

private theorem ContextField.beq_self (j : ContextField) : (j == j) = true := by
  cases j with
  | lddw _ | mapKeyBytes _ | mapValueBytes _ =>
    delta BEq.beq instBEqContextField instBEqContextField.beq instBEqOfDecidableEq
    simp [ContextField.ctorIdx]
  | _ => rfl

theorem Reg.overlaps_refl (r : Reg) (h : r.lo < r.hi) : r.overlaps r = true := by
  cases r <;> simp [Reg.overlaps, Reg.sameResource, h, ContextField.beq_self]

private theorem pairwise_mem_or {α : Type} {R : α → α → Prop} {l : List α}
    (h : l.Pairwise R) {a b : α} (ha : a ∈ l) (hb : b ∈ l) (hne : a ≠ b) :
    R a b ∨ R b a := by
  induction l with
  | nil => cases ha
  | cons x xs ih =>
    cases h with
    | cons hx hxs =>
      cases ha with
      | head =>
        cases hb with
        | head => exact absurd rfl hne
        | tail _ hb => exact Or.inl (hx b hb)
      | tail _ ha =>
        cases hb with
        | head => exact Or.inr (hx a ha)
        | tail _ hb => exact ih hxs ha hb

private theorem fold_rel_beq (E acc : List Expr)
    (hacc : ∀ x ∈ acc, (x.rel == .eq) = true) {e : Expr}
    (he : e ∈ E.foldl (fun acc e =>
      if e.rel == .eq && !(acc.any (fun v => v.reg == e.reg)) then acc ++ [e] else acc) acc) :
    (e.rel == .eq) = true := by
  induction E generalizing acc with
  | nil =>
    simp at he
    exact hacc e he
  | cons x xs ih =>
    rw [List.foldl_cons] at he
    split at he
    · next hcond =>
      apply ih (acc ++ [x]) ?_ he
      intro y hy
      cases List.mem_append.mp hy with
      | inl hy => exact hacc y hy
      | inr hy =>
        simp at hy
        subst y
        simp only [Bool.and_eq_true] at hcond
        exact hcond.1
    · exact ih acc hacc he

theorem bindings_rel_beq (E : List Expr) {e : Expr} (he : e ∈ E.bindings) :
    (e.rel == .eq) = true := by
  have hfold : E.bindings = E.foldl (fun acc e =>
      if e.rel == .eq && !(acc.any (fun v => v.reg == e.reg)) then acc ++ [e] else acc) [] := rfl
  rw [hfold] at he
  exact fold_rel_beq E [] (by intro x hx; cases hx) he

theorem separated_reg_unique (E : List Expr) (h : valueSeparated E)
    {a b : Expr} (ha : a ∈ E.bindings) (hb : b ∈ E.bindings)
    (hr : a.reg = b.reg) (hw : a.reg.lo < a.reg.hi) : a = b := by
  classical
  by_cases hne : a = b
  · exact hne
  · have hover : a.reg.overlaps b.reg = true := by
      rw [hr]
      exact Reg.overlaps_refl b.reg (by simpa [hr] using hw)
    cases pairwise_mem_or h ha hb hne with
    | inl hfalse =>
      rw [hover] at hfalse
      cases hfalse
    | inr hfalse =>
      have hover' : b.reg.overlaps a.reg = true := by simpa [hr] using hover
      rw [hover'] at hfalse
      cases hfalse

private theorem lookupEq_of_unique (E : List Expr) (e : Expr)
    (he : e ∈ E.bindings)
    (huniq : ∀ x ∈ E.bindings, x.reg = e.reg → x = e) :
    E.lookupEq e.reg = some e.term := by
  have hrel := bindings_rel_beq E he
  have heq : ((.eq : Rel) == .eq) = true := by rfl
  have hp : (e.reg == e.reg && e.rel == .eq) = true := by
    rw [beq_self_eq_true, hrel]
    rfl
  unfold List.lookupEq List.lookupRel
  rw [show (if (.eq : Rel) == .eq then E.bindings else E.constraints) = E.bindings by
    simp [heq]]
  have hfind : E.bindings.find? (fun x => x.reg == e.reg && x.rel == .eq) = some e := by
    have hsome : (E.bindings.find? (fun x => x.reg == e.reg && x.rel == .eq)).isSome := by
      rw [List.find?_isSome]
      exact ⟨e, he, hp⟩
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp hsome
    have hxmem := List.mem_of_find?_eq_some hx
    have hpx := List.find?_some hx
    have hreg : x.reg = e.reg := by
      simp only [Bool.and_eq_true, beq_iff_eq] at hpx
      exact hpx.1
    have hxeq : x = e := huniq x hxmem hreg
    simpa [hxeq] using hx
  simp [hfind]

/-- After assigning `w = t`, that exact interval's value row is `t`. -/
theorem assign_lookup (parent : State) (w : Reg) (t : Term)
    (hw : w.lo < w.hi) (hp : valueSeparated parent.exprs) :
    (update parent { exprs := [Expr.mkEq w t], predicates := [] }).exprs.lookupEq w = some t := by
  let σ := update parent { exprs := [Expr.mkEq w t], predicates := [] }
  have hsep : valueSeparated σ.exprs := update_disjoint parent w t hw hp
  have hmem : Expr.mkEq w t ∈ σ.exprs.bindings := update_installs parent w t
  have huniq : ∀ x ∈ σ.exprs.bindings, x.reg = w → x = Expr.mkEq w t := by
    intro x hx hr
    exact separated_reg_unique σ.exprs hsep hx hmem hr (by simpa [hr] using hw)
  simpa [σ] using lookupEq_of_unique σ.exprs (Expr.mkEq w t) hmem huniq

/-- An exact interval that does not meet the write keeps its term. -/
theorem kept_lookup (parent : State) (w : Reg) (t : Term) (v : Expr)
    (hv : v ∈ parent.exprs.bindings) (hmiss : v.reg.overlaps w = false)
    (hw : w.lo < w.hi) (hvW : v.reg.lo < v.reg.hi) (hp : valueSeparated parent.exprs) :
    (update parent { exprs := [Expr.mkEq w t], predicates := [] }).exprs.lookupEq v.reg =
      parent.exprs.lookupEq v.reg := by
  let σ := update parent { exprs := [Expr.mkEq w t], predicates := [] }
  have hsepσ : valueSeparated σ.exprs := update_disjoint parent w t hw hp
  have hmemσ : v ∈ σ.exprs.bindings := update_keeps parent w t v hv hmiss hw hp
  have huniqσ : ∀ x ∈ σ.exprs.bindings, x.reg = v.reg → x = v := by
    intro x hx hr
    exact separated_reg_unique σ.exprs hsepσ hx hmemσ hr (by simpa [hr] using hvW)
  have huniq : ∀ x ∈ parent.exprs.bindings, x.reg = v.reg → x = v := by
    intro x hx hr
    exact separated_reg_unique parent.exprs hp hx hv hr (by simpa [hr] using hvW)
  have hnew := lookupEq_of_unique σ.exprs v hmemσ huniqσ
  have hold := lookupEq_of_unique parent.exprs v hv huniq
  simp [σ, hnew, hold]

/-- One 32-bit register split into bits `[0, 8)` and `[8, 32)`.
This is that shape only. It is not a general fragment theorem.
-/
theorem low_byte_split (idx : Nat) (t s : Term) :
    update
      { exprs := [Expr.mkEq (.real idx 0 32) t], predicates := [] }
      { exprs := [Expr.mkEq (.real idx 0 8) s], predicates := [] }
    = { exprs :=
          [Expr.mkEq (.real idx 0 8) s,
           Expr.mkEq (.real idx 8 32)
             (.app .w32 (.extract 8 24 t.width.bits) [t])],
        predicates := [] } :=
  update_low_byte idx t s

end Verification.Verified.StateUpdate
