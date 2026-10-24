import Core.Insn

namespace Core

/-- One live equality. The register's half-open bit interval is the binding. -/
private structure Live where
  reg : Reg
  term : Term
  deriving DecidableEq, Repr

/-- `a` and `b` share no bit. -/
private def Separated (a b : Live) : Prop := a.reg.overlaps b.reg = false

/-- Project `len` bits at `offset`. A term that already has that length is unchanged. -/
private def sliceTerm (t : Term) (offset len : Nat) : Term :=
  if offset == 0 && len == t.semanticBits then t
  else .app (Width.ofBits len) (.extract offset len t.width.bits) [t]

/-- Uncovered sides of `v` after writing `w`.
A side is absent when that side of `v` has no bits left. -/
private def Live.sides (v : Live) (w : Reg) : List Live :=
  (if v.reg.lo < w.lo then
    [⟨v.reg.withInterval v.reg.lo (min v.reg.hi w.lo),
      sliceTerm v.term 0 (min v.reg.hi w.lo - v.reg.lo)⟩]
   else []) ++
  (if w.hi < v.reg.hi then
    [⟨v.reg.withInterval (max v.reg.lo w.hi) v.reg.hi,
      sliceTerm v.term (max v.reg.lo w.hi - v.reg.lo)
        (v.reg.hi - max v.reg.lo w.hi)⟩]
   else [])

/-- Install `[w.lo, w.hi) = t`. Every overlapping live binding is replaced by `sides`. -/
private def degenerate (xs : List Live) (w : Reg) (t : Term) : List Live :=
  (⟨w, t⟩ :: (xs.filter fun v => v.reg.overlaps w).flatMap fun v => v.sides w) ++
    (xs.filter fun v => !v.reg.overlaps w)

private theorem Reg.withInterval_lo (r : Reg) (b e : Nat) : (r.withInterval b e).lo = b := by
  cases r <;> rfl

private theorem Reg.withInterval_hi (r : Reg) (b e : Nat) : (r.withInterval b e).hi = e := by
  cases r <;> rfl

private theorem ContextField.beq_rfl (a : ContextField) : (a == a) = true := by
  cases a with
  | lddw _ | mapKeyBytes _ | mapValueBytes _ =>
    delta BEq.beq instBEqContextField instBEqContextField.beq instBEqOfDecidableEq
    simp [ContextField.ctorIdx]
  | _ => rfl

private theorem ContextField.eq_of_beq {a b : ContextField} (h : (a == b) = true) : a = b := by
  cases a <;> cases b
  case lddw.lddw n m =>
    delta BEq.beq instBEqContextField instBEqContextField.beq instBEqOfDecidableEq at h
    simp [ContextField.ctorIdx] at h
    subst h
    rfl
  case mapKeyBytes.mapKeyBytes n m =>
    delta BEq.beq instBEqContextField instBEqContextField.beq instBEqOfDecidableEq at h
    simp [ContextField.ctorIdx] at h
    subst h
    rfl
  case mapValueBytes.mapValueBytes n m =>
    delta BEq.beq instBEqContextField instBEqContextField.beq instBEqOfDecidableEq at h
    simp [ContextField.ctorIdx] at h
    subst h
    rfl
  all_goals first
    | rfl
    | (delta BEq.beq instBEqContextField instBEqContextField.beq at h; cases h)

private theorem Reg.withInterval_sameResource (r : Reg) (b e : Nat) :
    (r.withInterval b e).sameResource r = true := by
  cases r with
  | real _ _ _ => simp [Reg.withInterval, Reg.sameResource]
  | stack _ _ => simp [Reg.withInterval, Reg.sameResource]
  | packet _ _ => simp [Reg.withInterval, Reg.sameResource]
  | map _ _ _ _ => simp [Reg.withInterval, Reg.sameResource]
  | context j _ _ => simp [Reg.withInterval, Reg.sameResource, ContextField.beq_rfl j]

private theorem listTerm_beq_comm (a b : List Term) : (a == b) = (b == a) := by
  cases h : a == b <;> cases h2 : b == a
  · rfl
  · exact absurd (beq_iff_eq.mp h2).symm (beq_eq_false_iff_ne.mp h)
  · exact absurd (beq_iff_eq.mp h).symm (beq_eq_false_iff_ne.mp h2)
  · rfl

private theorem Reg.sameResource_comm (a b : Reg) : a.sameResource b = b.sameResource a := by
  cases a <;> cases b <;> try rfl
  case real.real n _ _ m _ _ =>
    simpa [Reg.sameResource] using Nat.beq_comm n m
  case map.map m1 k1 _ _ m2 k2 _ _ =>
    simp only [Reg.sameResource]
    rw [Nat.beq_comm m1 m2, listTerm_beq_comm k1 k2]
  case context.context j _ _ i _ _ =>
    simpa [Reg.sameResource] using ContextField.beq_comm j i

private theorem Reg.overlaps_comm (a b : Reg) : a.overlaps b = b.overlaps a := by
  rw [Reg.overlaps, Reg.overlaps, sameResource_comm a b]
  apply congrArg (fun x => b.sameResource a && x)
  generalize hl : decide (a.lo < b.hi) = l
  generalize hr : decide (b.lo < a.hi) = r
  cases l <;> cases r <;> simp

private theorem Reg.overlaps_eq_true (a b : Reg) :
    a.overlaps b = true ↔ a.sameResource b = true ∧ a.lo < b.hi ∧ b.lo < a.hi := by
  simp [Reg.overlaps, Bool.and_eq_true, decide_eq_true_eq]

private theorem Reg.sameResource_trans (a b c : Reg)
    (hab : a.sameResource b = true) (hbc : b.sameResource c = true) :
    a.sameResource c = true := by
  cases a <;> cases b <;> simp [Reg.sameResource] at hab <;> cases c <;>
    simp_all [Reg.sameResource, beq_iff_eq]
  case context.context.context j1 _ _ j2 _ _ j3 _ _ =>
    have h12 : j1 = j2 := ContextField.eq_of_beq hab
    have h23 : j2 = j3 := ContextField.eq_of_beq hbc
    simp [h12, h23, ContextField.beq_rfl]

private theorem Reg.overlaps_within (p a b : Reg)
    (hsame : p.sameResource a = true) (hlo : a.lo ≤ p.lo) (hhi : p.hi ≤ a.hi)
    (h : a.overlaps b = false) : p.overlaps b = false := by
  cases hpb : p.sameResource b with
  | false => simp [Reg.overlaps, hpb]
  | true =>
    have hab : a.sameResource b = true :=
      sameResource_trans a p b ((sameResource_comm p a).symm ▸ hsame) hpb
    have hnot : ¬ (a.lo < b.hi ∧ b.lo < a.hi) := by
      intro hlt
      have : a.overlaps b = true := (overlaps_eq_true a b).mpr ⟨hab, hlt.1, hlt.2⟩
      rw [h] at this
      cases this
    rw [Reg.overlaps, hpb, Bool.true_and]
    by_cases h1 : a.lo < b.hi
    · have hq : decide (b.lo < p.hi) = false :=
        decide_eq_false fun hlt => hnot ⟨h1, Nat.lt_of_lt_of_le hlt hhi⟩
      simp [hq]
    · have hpLt : decide (p.lo < b.hi) = false :=
        decide_eq_false fun hlt => h1 (Nat.lt_of_le_of_lt hlo hlt)
      simp [hpLt]

private theorem Live.mem_sides (v : Live) (w : Reg) (s : Live) :
    s ∈ v.sides w ↔
      (v.reg.lo < w.lo ∧
        s = ⟨v.reg.withInterval v.reg.lo (min v.reg.hi w.lo),
          sliceTerm v.term 0 (min v.reg.hi w.lo - v.reg.lo)⟩) ∨
      (w.hi < v.reg.hi ∧
        s = ⟨v.reg.withInterval (max v.reg.lo w.hi) v.reg.hi,
          sliceTerm v.term (max v.reg.lo w.hi - v.reg.lo)
            (v.reg.hi - max v.reg.lo w.hi)⟩) := by
  unfold Live.sides
  constructor
  · intro hs
    by_cases hL : v.reg.lo < w.lo <;> by_cases hR : w.hi < v.reg.hi
    · simp only [hL, hR, ↓reduceIte, List.mem_append, List.mem_singleton] at hs
      rcases hs with hs | hs
      · exact Or.inl ⟨hL, hs⟩
      · exact Or.inr ⟨hR, hs⟩
    · simp only [hL, hR, ↓reduceIte, List.mem_append, List.mem_singleton,
        List.not_mem_nil, or_false] at hs
      exact Or.inl ⟨hL, hs⟩
    · simp only [hL, hR, ↓reduceIte, List.mem_append, List.mem_singleton,
        List.not_mem_nil, false_or] at hs
      exact Or.inr ⟨hR, hs⟩
    · simp [hL, hR] at hs
  · intro hs
    rcases hs with ⟨hL, rfl⟩ | ⟨hR, rfl⟩
    · simp [hL]
    · simp [hR]

private theorem Live.side_misses (v : Live) (w : Reg) (s : Live)
    (hov : v.reg.overlaps w = true) (hs : s ∈ v.sides w) :
    s.reg.sameResource v.reg = true ∧ v.reg.lo ≤ s.reg.lo ∧ s.reg.hi ≤ v.reg.hi ∧
      s.reg.overlaps w = false ∧ s.reg.lo < s.reg.hi := by
  have hov' := (Reg.overlaps_eq_true v.reg w).mp hov
  rcases (mem_sides v w s).mp hs with hs | hs
  · rcases hs with ⟨hlo, rfl⟩
    have hwlo : w.lo < v.reg.hi := hov'.2.2
    have hstop : min v.reg.hi w.lo = w.lo := Nat.min_eq_right (Nat.le_of_lt hwlo)
    simp only [hstop, Reg.withInterval_lo, Reg.withInterval_hi]
    refine ⟨Reg.withInterval_sameResource _ _ _, Nat.le_refl _, Nat.le_of_lt hwlo, ?_, ?_⟩
    · have hq : decide (w.lo < w.lo) = false := decide_eq_false (Nat.lt_irrefl _)
      simp [Reg.overlaps, Reg.withInterval_lo, Reg.withInterval_hi]
    · simpa [hstop, Reg.withInterval_lo, Reg.withInterval_hi] using hlo
  · rcases hs with ⟨hhi, rfl⟩
    have hlo : v.reg.lo < w.hi := hov'.2.1
    have hstart : max v.reg.lo w.hi = w.hi := Nat.max_eq_right (Nat.le_of_lt hlo)
    simp only [hstart, Reg.withInterval_lo, Reg.withInterval_hi]
    refine ⟨Reg.withInterval_sameResource _ _ _, Nat.le_of_lt hlo, Nat.le_refl _, ?_, ?_⟩
    · have hpLt : decide (w.hi < w.hi) = false := decide_eq_false (Nat.lt_irrefl _)
      simp [Reg.overlaps, Reg.withInterval_lo, Reg.withInterval_hi]
    · simpa [hstart, Reg.withInterval_lo, Reg.withInterval_hi] using hhi

private theorem Live.sides_cross (v₁ v₂ : Live) (w : Reg) (s₁ s₂ : Live)
    (hov₁ : v₁.reg.overlaps w = true) (hov₂ : v₂.reg.overlaps w = true)
    (hsep : v₁.reg.overlaps v₂.reg = false)
    (hs₁ : s₁ ∈ v₁.sides w) (hs₂ : s₂ ∈ v₂.sides w) :
    s₁.reg.overlaps s₂.reg = false := by
  have h₁ := side_misses v₁ w s₁ hov₁ hs₁
  have h₂ := side_misses v₂ w s₂ hov₂ hs₂
  have hmiss : v₁.reg.overlaps s₂.reg = false := by
    simpa [Reg.overlaps_comm] using
      Reg.overlaps_within s₂.reg v₂.reg v₁.reg h₂.1 h₂.2.1 h₂.2.2.1
        (by simpa [Reg.overlaps_comm] using hsep)
  exact Reg.overlaps_within s₁.reg v₁.reg s₂.reg h₁.1 h₁.2.1 h₁.2.2.1 hmiss

private theorem pairwise_mem {xs : List Live}
    (hp : xs.Pairwise Separated) {a b : Live} (ha : a ∈ xs) (hb : b ∈ xs) (hne : a ≠ b) :
    a.reg.overlaps b.reg = false := by
  induction xs generalizing a b with
  | nil => cases ha
  | cons x xs ih =>
    cases hp with
    | cons hrel hp =>
      simp only [List.mem_cons] at ha hb
      cases ha with
      | inl ha =>
        cases hb with
        | inl hb => exact absurd (ha.trans hb.symm) hne
        | inr hb => simpa [ha] using hrel b hb
      | inr ha =>
        cases hb with
        | inl hb => simpa [hb, Reg.overlaps_comm] using hrel a ha
        | inr hb => exact ih hp ha hb hne

private theorem pairwise_filter {p : Live → Bool} {xs : List Live}
    (hp : xs.Pairwise Separated) : (xs.filter p).Pairwise Separated := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    cases hp with
    | cons hrel hp =>
      rw [List.filter_cons]
      split
      · rw [List.pairwise_cons]
        exact ⟨fun a ha => hrel a (List.mem_filter.mp ha).1, ih hp⟩
      · exact ih hp

private theorem Live.sides_pairwise (v : Live) (w : Reg) (hw : w.lo < w.hi)
    (hov : v.reg.overlaps w = true) : (v.sides w).Pairwise Separated := by
  by_cases hL : v.reg.lo < w.lo
  · by_cases hR : w.hi < v.reg.hi
    · have hs : v.sides w =
          [⟨v.reg.withInterval v.reg.lo (min v.reg.hi w.lo),
            sliceTerm v.term 0 (min v.reg.hi w.lo - v.reg.lo)⟩] ++
          [⟨v.reg.withInterval (max v.reg.lo w.hi) v.reg.hi,
            sliceTerm v.term (max v.reg.lo w.hi - v.reg.lo)
              (v.reg.hi - max v.reg.lo w.hi)⟩] := by
        simp [Live.sides, hL, hR]
      rw [hs, List.pairwise_append]
      refine ⟨by simp, by simp, ?_⟩
      intro a ha b hb
      simp only [List.mem_singleton] at ha hb
      subst ha
      subst hb
      have hov' := (Reg.overlaps_eq_true v.reg w).mp hov
      have hstop : min v.reg.hi w.lo = w.lo :=
        Nat.min_eq_right (Nat.le_of_lt hov'.2.2)
      have hstart : max v.reg.lo w.hi = w.hi :=
        Nat.max_eq_right (Nat.le_of_lt hov'.2.1)
      have hq : decide (w.hi < w.lo) = false := decide_eq_false (Nat.not_lt.mpr (Nat.le_of_lt hw))
      simp [Separated, Reg.overlaps, Reg.withInterval_lo, Reg.withInterval_hi, hstop, hstart, hq]
    · simp [Live.sides, hL, hR]
  · by_cases hR : w.hi < v.reg.hi
    · simp [Live.sides, hL, hR]
    · simp [Live.sides, hL, hR]

private theorem pairwise_sides (vs : List Live) (w : Reg) (hw : w.lo < w.hi)
    (hov : ∀ v ∈ vs, v.reg.overlaps w = true)
    (hp : vs.Pairwise Separated) :
    (vs.flatMap fun v => v.sides w).Pairwise Separated := by
  induction vs with
  | nil => simp
  | cons v vs ih =>
    cases hp with
    | cons hrel hp =>
      simp only [List.flatMap_cons, List.pairwise_append]
      refine ⟨Live.sides_pairwise v w hw (hov v (by simp)),
        ih (fun u hu => hov u (List.mem_cons_of_mem _ hu)) hp, ?_⟩
      intro s₁ hs₁ s₂ hs₂
      obtain ⟨u, hu, hs₂⟩ := List.mem_flatMap.mp hs₂
      exact Live.sides_cross v u w s₁ s₂ (hov v (by simp))
        (hov u (List.mem_cons_of_mem _ hu)) (hrel u hu) hs₁ hs₂

private theorem not_overlaps_of_not {b : Bool} (h : (!b) = true) : b = false := by
  cases b <;> simp_all

private theorem degenerate_installs (xs : List Live) (w : Reg) (t : Term) :
    (degenerate xs w t).head? = some ⟨w, t⟩ := by
  simp [degenerate]

private theorem mem_degenerate (xs : List Live) (w : Reg) (t : Term) (u : Live) :
    u ∈ degenerate xs w t ↔
      u = ⟨w, t⟩ ∨ u ∈ (xs.filter fun v => v.reg.overlaps w).flatMap (fun v => v.sides w) ∨
        u ∈ xs.filter fun v => !v.reg.overlaps w := by
  simp [degenerate, List.mem_append, List.mem_cons]

private theorem degenerate_degenerates (xs : List Live) (w : Reg) (t : Term) (v s : Live)
    (hv : v ∈ xs) (hov : v.reg.overlaps w = true) (hs : s ∈ v.sides w) :
    s ∈ degenerate xs w t := by
  refine (mem_degenerate xs w t s).mpr (Or.inr (Or.inl ?_))
  exact List.mem_flatMap.mpr ⟨v, by simpa [List.mem_filter] using ⟨hv, hov⟩, hs⟩

private theorem degenerate_keeps (xs : List Live) (w : Reg) (t : Term) (v : Live)
    (hv : v ∈ xs) (hmiss : v.reg.overlaps w = false) : v ∈ degenerate xs w t := by
  refine (mem_degenerate xs w t v).mpr (Or.inr (Or.inr ?_))
  simpa [List.mem_filter, hmiss] using hv

private theorem degenerate_drops (xs : List Live) (w : Reg) (t : Term) (v u : Live)
    (_hv : v ∈ xs) (hov : v.reg.overlaps w = true) (hu : u ∈ degenerate xs w t)
    (heq : u.reg = v.reg) : u.reg = w := by
  rcases (mem_degenerate xs w t u).mp hu with rfl | hu | hu
  · rfl
  · obtain ⟨v₂, hv₂, hs⟩ := List.mem_flatMap.mp hu
    have hmiss := (Live.side_misses v₂ w u (List.mem_filter.mp hv₂).2 hs).2.2.2.1
    rw [heq] at hmiss
    simp [hov] at hmiss
  · have hmiss := not_overlaps_of_not (List.mem_filter.mp hu).2
    rw [heq] at hmiss
    simp [hov] at hmiss

private theorem degenerate_disjoint (xs : List Live) (w : Reg) (t : Term)
    (hw : w.lo < w.hi) (hp : xs.Pairwise Separated) :
    (degenerate xs w t).Pairwise Separated := by
  rw [degenerate, List.pairwise_append]
  refine ⟨?_, ?_, ?_⟩
  · rw [List.pairwise_cons]
    refine ⟨?_, pairwise_sides _ _ hw ?_ (pairwise_filter hp)⟩
    · intro u hu
      obtain ⟨v, hv, hs⟩ := List.mem_flatMap.mp hu
      simpa [Separated, Reg.overlaps_comm] using
        (Live.side_misses v w u (List.mem_filter.mp hv).2 hs).2.2.2.1
    · intro v hv
      exact (List.mem_filter.mp hv).2
  · exact pairwise_filter hp
  · intro a ha b hb
    rw [List.mem_cons] at ha
    have hmiss := not_overlaps_of_not (List.mem_filter.mp hb).2
    rcases ha with rfl | ha
    · simpa [Separated, Reg.overlaps_comm] using hmiss
    · obtain ⟨v, hv, hs⟩ := List.mem_flatMap.mp ha
      have hvxs := (List.mem_filter.mp hv).1
      have hbxs := (List.mem_filter.mp hb).1
      have hov := (List.mem_filter.mp hv).2
      have hne : v ≠ b := by
        intro h
        rw [h] at hov
        simp [hov] at hmiss
      have hsep := pairwise_mem hp hvxs hbxs hne
      have hsub := Live.side_misses v w a hov hs
      simpa [Separated] using
        Reg.overlaps_within a.reg v.reg b.reg hsub.1 hsub.2.1 hsub.2.2.1 hsep

private theorem sliceTerm_pos (t : Term) {offset len : Nat} (h : offset ≠ 0) :
    sliceTerm t offset len =
      .app (Width.ofBits len) (.extract offset len t.width.bits) [t] := by
  have : (offset == 0) = false := beq_eq_false_iff_ne.mpr h
  simp [sliceTerm, this]

/-- Writing `[0,8) = s` into `[0,32) = t` drops the wide binding.
The high 24 bits remain as `extract` of `t`. -/
private theorem degenerate_low_byte (idx : Nat) (t s : Term) :
    degenerate [⟨.real idx 0 32, t⟩] (.real idx 0 8) s =
      [⟨.real idx 0 8, s⟩,
       ⟨.real idx 8 32, .app .w32 (.extract 8 24 t.width.bits) [t]⟩] := by
  simp [degenerate, Live.sides, sliceTerm, Reg.overlaps, Reg.sameResource, Reg.lo, Reg.hi,
    Reg.withInterval, Width.ofBits]

private def toLive (e : Expr) : Live := ⟨e.reg, e.term⟩

private def ofLive (v : Live) : Expr := Expr.mkEq v.reg v.term

private def sides (v : Expr) (w : Reg) : List Expr :=
  (Live.sides (toLive v) w).map ofLive

private def branchFact (E : List Expr) (Pi : List Predicate) (e : Expr) : Bool :=
  Pi.any fun
    | .branch _ _ cond =>
      e.rel == cond.rel && solve e.term == solve cond.rhs &&
        match E.lookupEq e.reg with
        | some lhs => solve lhs == solve cond.lhs
        | none => false
    | _ => false

private def bind (acc : List Expr) (e : Expr) : List Expr :=
  if e.rel == .eq && !(acc.any fun v => v.reg == e.reg) then acc ++ [e] else acc

private theorem bindings_eq_foldl (E : List Expr) : E.bindings = E.foldl bind [] := by
  unfold List.bindings
  rfl

private theorem Rel.eq_beq_self : ((.eq : Rel) == .eq) = true := by
  native_decide

private theorem rel_eq_beq {r : Rel} (h : r = .eq) : (r == .eq) = true := by
  rw [h]
  exact Rel.eq_beq_self

private theorem rel_eq_of_beq {r : Rel} (h : (r == .eq) = true) : r = .eq := by
  cases r with
  | eq => rfl
  | ne | ltu | leu | gtu | geu | lts | les | gts | ges =>
    delta BEq.beq instBEqRel at h
    cases h
  | eqN _ | neN _ | ltuN _ | leuN _ | gtuN _ | geuN _ | ltsN _ | lesN _ | gtsN _ | gesN _ | bitsnz _ | bitsz _ =>
    delta BEq.beq instBEqRel at h
    cases h

private theorem bind_false {acc : List Expr} {x : Expr}
    (h : (x.rel == .eq && !(acc.any fun v => v.reg == x.reg)) = false) :
    bind acc x = acc := by
  unfold bind
  rw [h]
  simp

private theorem bind_true {acc : List Expr} {x : Expr}
    (h : (x.rel == .eq && !(acc.any fun v => v.reg == x.reg)) = true) :
    bind acc x = acc ++ [x] := by
  unfold bind
  rw [h]
  simp

private def appendSolved (acc : List Expr) (e : Expr) : List Expr :=
  let e := solveExpr e
  if acc.contains e then acc else acc ++ [e]

private def updateExprs (parent stepExprs : List Expr) (stepPreds : List Predicate) : List Expr :=
  match stepExprs with
  | [] => parent
  | rows =>
    let facts := rows.filter (branchFact parent stepPreds)
    let rest := rows.filter fun e => !facts.contains e
    let writes := rest.bindings
    let lives := writes.foldl (fun live w => degenerate live w.reg w.term)
      (parent.bindings.map toLive)
    let kept := parent.constraints.filter fun e =>
      !(writes.any fun w => w.reg.overlaps e.reg)
    let base := lives.map ofLive ++ kept
    facts.foldl appendSolved (rest.constraints.foldl appendSolved base)

/-- Value rows whose registers share no bits. -/
def valueSeparated (E : List Expr) : Prop :=
  E.bindings.Pairwise fun a b => a.reg.overlaps b.reg = false

/-- `step` is one increment. An empty increment leaves `parent` unchanged. -/
def update (parent step : State) : State where
  exprs := updateExprs parent.exprs step.exprs step.predicates
  predicates := step.predicates.foldl
    (fun acc p => if acc.contains p then acc else acc ++ [p])
    parent.predicates

private theorem mem_foldl_bind (rest acc : List Expr) (e : Expr) (he : e ∈ acc) :
    e ∈ rest.foldl bind acc := by
  induction rest generalizing acc with
  | nil => simpa using he
  | cons x xs ih =>
    rw [List.foldl_cons]
    cases hcond : x.rel == .eq && !(acc.any fun v => v.reg == x.reg) with
    | false =>
      rw [bind_false hcond]
      exact ih acc he
    | true =>
      rw [bind_true hcond]
      exact ih (acc ++ [x]) (List.mem_append_left _ he)

private theorem mem_foldl_bind_origin (rest acc : List Expr) (x : Expr)
    (hx : x ∈ rest.foldl bind acc) : x ∈ acc ∨ x ∈ rest := by
  induction rest generalizing acc with
  | nil =>
    simp at hx
    exact Or.inl hx
  | cons e es ih =>
    rw [List.foldl_cons] at hx
    have h := ih _ hx
    cases h with
    | inl hx =>
      cases hcond : e.rel == .eq && !(acc.any fun v => v.reg == e.reg) with
      | false =>
        rw [bind_false hcond] at hx
        exact Or.inl hx
      | true =>
        rw [bind_true hcond] at hx
        cases List.mem_append.mp hx with
        | inl hx => exact Or.inl hx
        | inr hx =>
          simp at hx
          exact Or.inr (by simp [hx])
    | inr hx => exact Or.inr (List.mem_cons_of_mem _ hx)

private theorem foldl_bind_rel (rest acc : List Expr)
    (hacc : ∀ x ∈ acc, x.rel = .eq) {e : Expr} (he : e ∈ rest.foldl bind acc) :
    e.rel = .eq := by
  induction rest generalizing acc with
  | nil =>
    simp at he
    exact hacc e he
  | cons x xs ih =>
    rw [List.foldl_cons] at he
    refine ih (bind acc x) ?_ he
    intro y hy
    cases hcond : x.rel == .eq && !(acc.any fun v => v.reg == x.reg) with
    | false =>
      rw [bind_false hcond] at hy
      exact hacc y hy
    | true =>
      rw [bind_true hcond] at hy
      cases List.mem_append.mp hy with
      | inl hy => exact hacc y hy
      | inr hy =>
        simp at hy
        subst y
        cases hrel : x.rel == .eq with
        | false => simp [hrel] at hcond
        | true => exact rel_eq_of_beq hrel

private theorem mem_bindings_imp_mem {E : List Expr} {e : Expr} (he : e ∈ E.bindings) : e ∈ E := by
  rw [bindings_eq_foldl] at he
  have h := mem_foldl_bind_origin E [] e he
  cases h with
  | inl h => cases h
  | inr h => exact h

private theorem rel_of_bindings {E : List Expr} {e : Expr} (he : e ∈ E.bindings) : e.rel = .eq := by
  rw [bindings_eq_foldl] at he
  exact foldl_bind_rel E [] (by intro x hx; cases hx) he

private theorem ofLive_toLive_binding {E : List Expr} {e : Expr} (he : e ∈ E.bindings) :
    ofLive (toLive e) = e := by
  have hr := rel_of_bindings he
  cases e with
  | mk reg rel term =>
    cases hr
    rfl

private theorem mem_bindings_head (e : Expr) (rest : List Expr) (hr : e.rel = .eq) :
    e ∈ (e :: rest).bindings := by
  rw [bindings_eq_foldl, List.foldl_cons]
  have hcond : (e.rel == .eq && !(([] : List Expr).any fun v => v.reg == e.reg)) = true := by
    rw [rel_eq_beq hr, List.any_nil]
    rfl
  rw [bind_true hcond]
  exact mem_foldl_bind rest [e] e (by simp)

private theorem bindings_mkEq (w : Reg) (t : Term) :
    [Expr.mkEq w t].bindings = [Expr.mkEq w t] := by
  rw [bindings_eq_foldl, List.foldl_cons, List.foldl_nil]
  have hcond :
      ((Expr.mkEq w t).rel == .eq &&
        !(([] : List Expr).any fun v => v.reg == (Expr.mkEq w t).reg)) = true := by
    change ((.eq : Rel) == .eq && !(([] : List Expr).any fun v => v.reg == w)) = true
    rw [Rel.eq_beq_self, List.any_nil]
    rfl
  rw [bind_true hcond]
  simp

private theorem expr_beq_mkEq (w : Reg) (t : Term) :
    (Expr.mkEq w t == Expr.mkEq w t) = true := by
  delta BEq.beq instBEqExpr instBEqExpr.beq
  simp [Expr.mkEq]
  exact ⟨beq_self_eq_true w, Rel.eq_beq_self, beq_self_eq_true t⟩

private theorem constraints_mkEq (w : Reg) (t : Term) :
    [Expr.mkEq w t].constraints = [] := by
  unfold List.constraints
  rw [bindings_mkEq]
  have hb := expr_beq_mkEq w t
  have hele : List.elem (Expr.mkEq w t) [Expr.mkEq w t] = true := by
    rw [List.elem_cons, hb]
  rw [List.filter]
  dsimp only [List.contains]
  rw [hele]
  rfl

private theorem updateExprs_assign (parent : List Expr) (w : Reg) (t : Term) :
    updateExprs parent [Expr.mkEq w t] [] =
      (degenerate (parent.bindings.map toLive) w t).map ofLive ++
        (parent.constraints.filter fun e => !(w.overlaps e.reg)) := by
  unfold updateExprs
  have hfact : branchFact parent [] (Expr.mkEq w t) = false := by
    simp [branchFact]
  have hfilter : ([Expr.mkEq w t].filter (branchFact parent [])) = [] := by
    simp [List.filter, hfact]
  simp only [hfilter, List.contains_nil, Bool.not_false]
  have hrest : ([Expr.mkEq w t].filter fun _ => true) = [Expr.mkEq w t] := by
    simp [List.filter]
  simp only [hrest, bindings_mkEq, List.foldl_cons, List.foldl_nil, constraints_mkEq]
  simp [Expr.mkEq, List.any_cons, List.any_nil, Reg.overlaps_comm]

theorem update_id (parent : State) :
    update parent { exprs := [], predicates := [] } = parent := by
  cases parent
  simp [update, updateExprs, List.foldl_nil]

theorem update_predicates (parent step : State) :
    (update parent step).predicates =
      step.predicates.foldl
        (fun acc p => if acc.contains p then acc else acc ++ [p])
        parent.predicates := rfl

theorem update_installs (parent : State) (w : Reg) (t : Term) :
    Expr.mkEq w t ∈
      (update parent { exprs := [Expr.mkEq w t], predicates := [] }).exprs.bindings := by
  rw [update, updateExprs_assign]
  have hhead := degenerate_installs (parent.exprs.bindings.map toLive) w t
  cases hL : degenerate (parent.exprs.bindings.map toLive) w t with
  | nil => simp [hL] at hhead
  | cons v vs =>
    simp [hL] at hhead
    subst hhead
    rw [List.map_cons, ofLive]
    exact mem_bindings_head (Expr.mkEq w t)
      (vs.map ofLive ++ parent.exprs.constraints.filter fun e => !(w.overlaps e.reg)) rfl

theorem update_low_byte (idx : Nat) (t s : Term) :
    update
      { exprs := [Expr.mkEq (.real idx 0 32) t], predicates := [] }
      { exprs := [Expr.mkEq (.real idx 0 8) s], predicates := [] }
    = { exprs :=
          [Expr.mkEq (.real idx 0 8) s,
           Expr.mkEq (.real idx 8 32)
             (.app .w32 (.extract 8 24 t.width.bits) [t])],
        predicates := [] } := by
  have h := degenerate_low_byte idx t s
  rw [update]
  simp only [List.foldl_nil]
  rw [updateExprs_assign, bindings_mkEq, constraints_mkEq, List.filter_nil]
  simp only [toLive, Expr.mkEq, List.map_cons, List.map_nil]
  rw [h]
  simp [ofLive, Expr.mkEq, List.map_cons, List.map_nil]

theorem update_drops (parent : State) (w : Reg) (t : Term) (v u : Expr)
    (hv : v ∈ parent.exprs.bindings)
    (hov : v.reg.overlaps w = true)
    (hu : u ∈ (update parent { exprs := [Expr.mkEq w t], predicates := [] }).exprs.bindings)
    (heq : u.reg = v.reg) : u.reg = w := by
  rw [update, updateExprs_assign] at hu
  have huE := mem_bindings_imp_mem hu
  cases List.mem_append.mp huE with
  | inl huE =>
    obtain ⟨lv, hlv, rfl⟩ := List.mem_map.mp huE
    have hvL : toLive v ∈ parent.exprs.bindings.map toLive := List.mem_map_of_mem hv
    have hdrop := degenerate_drops (parent.exprs.bindings.map toLive) w t (toLive v) lv hvL
      (by simpa [toLive] using hov) hlv (by simpa [ofLive] using heq)
    simpa [ofLive] using hdrop
  | inr huE =>
    have hf := (List.mem_filter.mp huE).2
    have hover : w.overlaps u.reg = true := by
      rw [heq]
      simpa [Reg.overlaps_comm] using hov
    simp [hover] at hf

private theorem sameResource_rfl (r : Reg) : r.sameResource r = true := by
  cases r <;> simp [Reg.sameResource, ContextField.beq_rfl]

private theorem overlaps_self_of_width (r : Reg) (h : r.lo < r.hi) : r.overlaps r = true := by
  simp [Reg.overlaps, sameResource_rfl, h]

private theorem bindings_reg_unique (E : List Expr) :
    E.bindings.Pairwise (fun a b => a.reg ≠ b.reg) := by
  rw [bindings_eq_foldl]
  suffices ∀ (rest acc : List Expr), acc.Pairwise (fun a b => a.reg ≠ b.reg) →
      (rest.foldl bind acc).Pairwise (fun a b => a.reg ≠ b.reg) from
    this E [] (by simp)
  intro rest acc hacc
  induction rest generalizing acc with
  | nil => simpa using hacc
  | cons e es ih =>
    rw [List.foldl_cons]
    cases hcond : e.rel == .eq && !(acc.any fun v => v.reg == e.reg) with
    | false =>
      rw [bind_false hcond]
      exact ih acc hacc
    | true =>
      rw [bind_true hcond]
      apply ih
      rw [List.pairwise_append]
      refine ⟨hacc, by simp, ?_⟩
      intro a ha b hb
      simp at hb
      subst b
      intro hreg
      cases hany : acc.any fun v => v.reg == e.reg with
      | true =>
        cases hrel : e.rel == .eq with
        | false => simp [hrel] at hcond
        | true => simp [hrel, hany] at hcond
      | false =>
        have := (List.any_eq_false.mp hany) a ha
        exact this ((beq_iff_eq).mpr hreg)

private theorem exists_binding_reg (E : List Expr) (e : Expr)
    (he : e ∈ E) (hr : e.rel = .eq) :
    ∃ b ∈ E.bindings, b.reg = e.reg := by
  rw [bindings_eq_foldl]
  suffices ∀ (rest acc : List Expr), e ∈ rest → (∀ x ∈ acc, x.rel = .eq) →
      ∃ b ∈ rest.foldl bind acc, b.reg = e.reg from
    this E [] he (by intro x hx; cases hx)
  intro rest acc heMem hacc
  induction rest generalizing acc with
  | nil => cases heMem
  | cons x xs ih =>
    rw [List.foldl_cons]
    cases heMem with
    | head =>
      have hbeq := rel_eq_beq hr
      cases hcond : e.rel == .eq && !(acc.any fun v => v.reg == e.reg) with
      | false =>
        cases hany : acc.any fun v => v.reg == e.reg with
        | false => simp [hbeq, hany] at hcond
        | true =>
          rw [bind_false hcond]
          obtain ⟨v, hv, hreg⟩ := (List.any_eq_true).1 hany
          exact ⟨v, mem_foldl_bind xs acc v hv, (beq_iff_eq).mp hreg⟩
      | true =>
        rw [bind_true hcond]
        exact ⟨e, mem_foldl_bind xs (acc ++ [e]) e (by simp), rfl⟩
    | tail _ htail =>
      cases hcond : x.rel == .eq && !(acc.any fun v => v.reg == x.reg) with
      | false =>
        rw [bind_false hcond]
        exact ih acc htail hacc
      | true =>
        rw [bind_true hcond]
        have hacc' : ∀ y ∈ acc ++ [x], y.rel = .eq := by
          intro y hy
          cases List.mem_append.mp hy with
          | inl hy => exact hacc y hy
          | inr hy =>
            simp at hy
            subst y
            cases hrel : x.rel == .eq with
            | false => simp [hrel] at hcond
            | true => exact rel_eq_of_beq hrel
        exact ih (acc ++ [x]) htail hacc'

private theorem covered_binding (parent : List Expr) (w : Reg) (t : Term) (u : Expr)
    (hu : u ∈ ((degenerate (parent.bindings.map toLive) w t).map ofLive ++
      parent.constraints.filter fun e => !(w.overlaps e.reg)).bindings) :
    ∃ v ∈ degenerate (parent.bindings.map toLive) w t, v.reg = u.reg := by
  have huE := mem_bindings_imp_mem hu
  cases List.mem_append.mp huE with
  | inl huE =>
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp huE
    exact ⟨v, hv, by simp [ofLive, Expr.mkEq]⟩
  | inr huE =>
    have hmem := List.mem_filter.mp huE
    have hr := rel_of_bindings hu
    have hparent : u ∈ parent := by
      unfold List.constraints at hmem
      exact (List.mem_filter.mp hmem.1).1
    have hb := exists_binding_reg parent u hparent hr
    obtain ⟨b, hbMem, hreg⟩ := hb
    have hmiss : b.reg.overlaps w = false := by
      have hover : w.overlaps u.reg = false := by
        have hnot := hmem.2
        simpa [Bool.not_eq_true] using hnot
      rw [← hreg, Reg.overlaps_comm] at hover
      exact hover
    have hbL : toLive b ∈ (parent.bindings.map toLive).filter fun v => !v.reg.overlaps w := by
      refine List.mem_filter.mpr ⟨List.mem_map_of_mem hbMem, ?_⟩
      simpa [toLive, hreg] using hmiss
    refine ⟨toLive b, ?_, by simp [toLive, hreg]⟩
    exact (mem_degenerate (parent.bindings.map toLive) w t (toLive b)).2
      (Or.inr (Or.inr hbL))

theorem update_disjoint (parent : State) (w : Reg) (t : Term)
    (hw : w.lo < w.hi) (hp : valueSeparated parent.exprs) :
    valueSeparated
      (update parent { exprs := [Expr.mkEq w t], predicates := [] }).exprs := by
  rw [valueSeparated, update, updateExprs_assign]
  have hpL : (parent.exprs.bindings.map toLive).Pairwise Separated := by
    rw [List.pairwise_map]
    simpa [Separated, toLive] using hp
  have hdeg := degenerate_disjoint (parent.exprs.bindings.map toLive) w t hw hpL
  have huniq := bindings_reg_unique
    ((degenerate (parent.exprs.bindings.map toLive) w t).map ofLive ++
      parent.exprs.constraints.filter fun e => !(w.overlaps e.reg))
  refine List.Pairwise.imp_of_mem ?_ huniq
  intro a b ha hb hne
  obtain ⟨va, hva, hra⟩ := covered_binding parent.exprs w t a ha
  obtain ⟨vb, hvb, hrb⟩ := covered_binding parent.exprs w t b hb
  have hneq : va ≠ vb := by
    intro h
    apply hne
    rw [← hra, ← hrb, h]
  have hsep := pairwise_mem hdeg hva hvb hneq
  simpa [Separated, hra, hrb] using hsep

private theorem kept_reg_ne_write {v : Expr} {w : Reg}
    (hmiss : v.reg.overlaps w = false) (hw : w.lo < w.hi) : v.reg ≠ w := by
  intro h
  rw [h] at hmiss
  simp [overlaps_self_of_width w hw] at hmiss

private theorem side_reg_ne_write (v : Live) (w : Reg) (s : Live) (hs : s ∈ v.sides w) :
    s.reg ≠ w := by
  intro hreg
  rcases (Live.mem_sides v w s).1 hs with ⟨hL, rfl⟩ | ⟨hR, rfl⟩
  · have hlo := congrArg Reg.lo hreg
    simp [Reg.withInterval_lo] at hlo
    exact Nat.lt_irrefl _ (hlo ▸ hL)
  · have hhi := congrArg Reg.hi hreg
    simp [Reg.withInterval_hi] at hhi
    exact Nat.lt_irrefl _ (hhi ▸ hR)

private theorem sep_reg_ne {a b : Live} (h : Separated a b) (ha : a.reg.lo < a.reg.hi) :
    a.reg ≠ b.reg := by
  intro hreg
  have hover : a.reg.overlaps b.reg = true := by
    rw [hreg]
    exact overlaps_self_of_width _ (by simpa [hreg] using ha)
  simp [Separated, hover] at h

private theorem side_reg_ne_kept (xs : List Live) (w : Reg) (victim side kept : Live)
    (hp : xs.Pairwise Separated) (hvictim : victim ∈ xs) (hov : victim.reg.overlaps w = true)
    (hs : side ∈ victim.sides w) (hkept : kept ∈ xs) (hmiss : kept.reg.overlaps w = false) :
    side.reg ≠ kept.reg := by
  intro hreg
  have hsub := Live.side_misses victim w side hov hs
  have hne : victim ≠ kept := by
    intro h
    rw [h] at hov
    simp [hov] at hmiss
  have hsep := pairwise_mem hp hvictim hkept hne
  have hover : victim.reg.overlaps side.reg = true := by
    have hsame : victim.reg.sameResource side.reg = true := by
      simpa [Reg.sameResource_comm] using hsub.1
    refine (Reg.overlaps_eq_true _ _).2 ⟨hsame, ?_, ?_⟩
    · exact Nat.lt_of_le_of_lt hsub.2.1 hsub.2.2.2.2
    · exact Nat.lt_of_lt_of_le hsub.2.2.2.2 hsub.2.2.1
  rw [hreg] at hover
  simp [hover] at hsep

private theorem pairwise_filter_ne {p : Live → Bool} {xs : List Live}
    (hp : xs.Pairwise (fun a b => a.reg ≠ b.reg)) :
    (xs.filter p).Pairwise (fun a b => a.reg ≠ b.reg) := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    cases hp with
    | cons hrel hp =>
      rw [List.filter_cons]
      split
      · rw [List.pairwise_cons]
        exact ⟨fun a ha => hrel a (List.mem_filter.mp ha).1, ih hp⟩
      · exact ih hp

private theorem mem_bindings_of_first (p s : List Expr) (e : Expr) (he : e.rel = .eq)
    (hpre : ∀ x ∈ p, x.rel = .eq → x.reg ≠ e.reg) :
    e ∈ (p ++ e :: s).bindings := by
  rw [bindings_eq_foldl, List.foldl_append, List.foldl_cons]
  have hany : ((p.foldl bind []).any fun v => v.reg == e.reg) = false := by
    rw [List.any_eq_false]
    intro v hv htrue
    have hvP : v ∈ p := by
      cases mem_foldl_bind_origin p [] v hv with
      | inl h => cases h
      | inr h => exact h
    have hrel := foldl_bind_rel p [] (by intro x hx; cases hx) hv
    exact hpre v hvP hrel ((beq_iff_eq).mp htrue)
  have hcond :
      (e.rel == .eq && !((p.foldl bind []).any fun v => v.reg == e.reg)) = true := by
    rw [rel_eq_beq he, hany]
    rfl
  rw [bind_true hcond]
  exact mem_foldl_bind s _ e (by simp)

/-- `w.lo < w.hi` and `valueSeparated` rule out a zero-width write and a side that
copies an existing register. Without them the kept row and the write can share one register. -/
theorem update_keeps (parent : State) (w : Reg) (t : Term) (v : Expr)
    (hv : v ∈ parent.exprs.bindings) (hmiss : v.reg.overlaps w = false)
    (hw : w.lo < w.hi) (hp : valueSeparated parent.exprs) :
    v ∈ (update parent { exprs := [Expr.mkEq w t], predicates := [] }).exprs.bindings := by
  let xs := parent.exprs.bindings.map toLive
  have huniq : xs.Pairwise (fun a b => a.reg ≠ b.reg) :=
    (bindings_reg_unique parent.exprs).map toLive fun _ _ hne => by simpa [toLive] using hne
  have hvF : toLive v ∈ xs.filter fun u => !u.reg.overlaps w := by
    refine List.mem_filter.mpr ⟨List.mem_map_of_mem hv, ?_⟩
    simpa [toLive] using hmiss
  obtain ⟨p1, s1, hsplit, _⟩ := List.eq_append_cons_of_mem hvF
  have hfil := pairwise_filter_ne (p := fun u => !u.reg.overlaps w) huniq
  rw [hsplit] at hfil
  have hround := ofLive_toLive_binding hv
  have hpL : xs.Pairwise Separated := by
    rw [List.pairwise_map]
    simpa [Separated, toLive] using hp
  rw [update, updateExprs_assign]
  have hshape :
      degenerate xs w t =
        ((⟨w, t⟩ :: (xs.filter fun u => u.reg.overlaps w).flatMap fun u => u.sides w) ++ p1) ++
          toLive v :: s1 := by
    simp [degenerate, hsplit, List.append_assoc]
  rw [hshape, List.map_append, List.map_cons, hround, List.append_assoc, List.cons_append]
  refine mem_bindings_of_first _ _ v (rel_of_bindings hv) ?_
  intro x hx _
  obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hx
  simp only [ofLive, Expr.mkEq]
  cases List.mem_cons.mp hu with
  | inl hu =>
    subst hu
    exact (kept_reg_ne_write hmiss hw).symm
  | inr hu =>
    cases List.mem_append.mp hu with
    | inl hu =>
      obtain ⟨victim, hvictim, hs⟩ := List.mem_flatMap.mp hu
      have hmem := List.mem_filter.mp hvictim
      exact side_reg_ne_kept xs w victim u (toLive v) hpL hmem.1 hmem.2 hs
        (List.mem_map_of_mem hv) (by simpa [toLive] using hmiss)
    | inr hu =>
      have hcross := (List.pairwise_append.mp hfil).2.2
      simpa [toLive] using hcross u hu (toLive v) (by simp)

private theorem update_degenerates (parent : State) (w : Reg) (t : Term) (v s : Expr)
    (hv : v ∈ parent.exprs.bindings) (hov : v.reg.overlaps w = true)
    (hp : valueSeparated parent.exprs) (hw : w.lo < w.hi) (hs : s ∈ sides v w) :
    s ∈ (update parent { exprs := [Expr.mkEq w t], predicates := [] }).exprs.bindings := by
  obtain ⟨sLive, hsLive, rfl⟩ := List.mem_map.mp hs
  let xs := parent.exprs.bindings.map toLive
  have hpL : xs.Pairwise Separated := by
    rw [List.pairwise_map]
    simpa [Separated, toLive] using hp
  let victims := xs.filter fun u => u.reg.overlaps w
  have hflat : (victims.flatMap fun u => u.sides w).Pairwise Separated :=
    pairwise_sides victims w hw (fun u hu => (List.mem_filter.mp hu).2)
      (pairwise_filter (p := fun u => u.reg.overlaps w) hpL)
  have hsDeg : sLive ∈ victims.flatMap fun u => u.sides w := by
    refine List.mem_flatMap.mpr ⟨toLive v, ?_, hsLive⟩
    exact List.mem_filter.mpr ⟨List.mem_map_of_mem hv, by simpa [toLive] using hov⟩
  obtain ⟨pSide, sSide, hsplit, hnot⟩ := List.eq_append_cons_of_mem hsDeg
  rw [update, updateExprs_assign]
  have hshape :
      degenerate xs w t =
        (⟨w, t⟩ :: pSide) ++ sLive :: (sSide ++ xs.filter fun u => !u.reg.overlaps w) := by
    rw [degenerate, hsplit, List.cons_append, List.append_assoc, List.cons_append, ← List.cons_append]
  rw [hshape, List.map_append, List.map_cons, List.append_assoc, List.cons_append,
    List.map_cons, List.cons_append, ← List.cons_append]
  refine mem_bindings_of_first _ _ (ofLive sLive) rfl ?_
  intro x hx _
  cases List.mem_cons.mp hx with
  | inl hx =>
    subst hx
    simpa [ofLive, Expr.mkEq] using (side_reg_ne_write (toLive v) w sLive hsLive).symm
  | inr hx =>
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hx
    simp only [ofLive, Expr.mkEq]
    have huFlat : u ∈ victims.flatMap fun z => z.sides w := by
      rw [hsplit]
      exact List.mem_append_left _ hu
    have hsFlat : sLive ∈ victims.flatMap fun z => z.sides w := by
      rw [hsplit]
      exact List.mem_append_right _ List.mem_cons_self
    have hne : u ≠ sLive := by
      intro h
      exact hnot (h ▸ hu)
    have hsep := pairwise_mem hflat hsFlat huFlat (Ne.symm hne)
    have hwidth := (Live.side_misses (toLive v) w sLive (by simpa [toLive] using hov) hsLive).2.2.2.2
    simpa [ofLive, Expr.mkEq] using (sep_reg_ne hsep hwidth).symm

end Core
