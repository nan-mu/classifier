import ClassifierExpr.CrossPred

namespace ClassifierExpr

/-! Injective symbol renaming and ordered alignment of canonical observations.
The specification is owned by `doc/Predicate/跨架构谓词.md`. -/
deriving instance ReflBEq, LawfulBEq for RegKind


structure CrossSubst where
  vars : List (Nat × Nat) := []
  regs : List (RegKind × Nat × Nat) := []
  deriving DecidableEq, BEq, ReflBEq, LawfulBEq, Repr

namespace CrossSubst

def empty : CrossSubst := ⟨[], []⟩

def varImage? (σ : CrossSubst) (x : Nat) : Option Nat :=
  (σ.vars.find? (·.1 == x)).map (·.2)

def regImage? (σ : CrossSubst) (k : RegKind) (a : Nat) : Option Nat :=
  (σ.regs.find? (fun e => e.1 == k && e.2.1 == a)).map (·.2.2)

def varLookup (σ : CrossSubst) (x : Nat) : Nat := (σ.varImage? x).getD x

def regLookup (σ : CrossSubst) (k : RegKind) (a : Nat) : Nat :=
  (σ.regImage? k a).getD a

def addVar? (σ : CrossSubst) (x y : Nat) : Option CrossSubst :=
  match σ.varImage? x with
  | some y₀ => if y₀ == y then some σ else none
  | none => if σ.vars.any (·.2 == y) then none
            else some ⟨(x, y) :: σ.vars, σ.regs⟩

def addReg? (σ : CrossSubst) (k : RegKind) (a b : Nat) : Option CrossSubst :=
  match σ.regImage? k a with
  | some b₀ => if b₀ == b then some σ else none
  | none => if σ.regs.any (fun e => e.1 == k && e.2.2 == b) then none
            else some ⟨σ.vars, (k, a, b) :: σ.regs⟩

def strip (σ : CrossSubst) : CrossSubst :=
  ⟨σ.vars.filter (fun e => e.1 != e.2),
   σ.regs.filter (fun e => e.2.1 != e.2.2)⟩

def swap (σ : CrossSubst) : CrossSubst :=
  ⟨σ.vars.map (fun (a, b) => (b, a)),
   σ.regs.map (fun (k, a, b) => (k, b, a))⟩

/-- Both domain and codomain are duplicate-free in each symbol namespace. -/
def Injective (σ : CrossSubst) : Prop :=
  (σ.vars.map (·.1)).Nodup ∧ (σ.vars.map (·.2)).Nodup ∧
  (σ.regs.map (fun e => (e.1, e.2.1))).Nodup ∧
  (σ.regs.map (fun e => (e.1, e.2.2))).Nodup

def Extends (σ σ' : CrossSubst) : Prop :=
  (∀ e ∈ σ.vars, e ∈ σ'.vars) ∧ (∀ e ∈ σ.regs, e ∈ σ'.regs)

mutual
  def applyTerm (σ : CrossSubst) : CrossTerm → CrossTerm
    | .c z => .c z
    | .var n => .var (σ.varLookup n)
    | .reg k a => .reg k (σ.regLookup k a)
    | .app f ts => .app f (applyTerms σ ts)
    | .external l ts => .external l (applyTerms σ ts)
  termination_by t => sizeOf t

  def applyTerms (σ : CrossSubst) : List CrossTerm → List CrossTerm
    | [] => []
    | t :: ts => applyTerm σ t :: applyTerms σ ts
  termination_by ts => sizeOf ts
end

def applyValue (σ : CrossSubst) : CrossValue → CrossValue
  | .bytes ts => .bytes (applyTerms σ ts)
  | .source t => .source (applyTerm σ t)

def applyMutation (σ : CrossSubst) (m : CrossMutation) : CrossMutation :=
  { m with map := applyTerm σ m.map, key := applyTerms σ m.key,
           value := applyValue σ m.value }

def applyHelper (σ : CrossSubst) : CrossHelper → CrossHelper
  | .lookup m key => .lookup (applyTerm σ m) (applyTerms σ key)
  | .mutation m => .mutation (applyMutation σ m)
  | .other id args => .other id (applyTerms σ args)

def applyCond (σ : CrossSubst) : CrossCond → CrossCond
  | .plain r a b => .plain r (applyTerm σ a) (applyTerm σ b)
  | .packetBound b r o => .packetBound (applyTerm σ b) r (applyTerm σ o)
  | .packetField f r z => .packetField (applyTerm σ f) r z

def rename (σ : CrossSubst) : CrossPred → CrossPred
  | .helper h => .helper (applyHelper σ h)
  | .branch b => .branch { b with cond := applyCond σ b.cond }
  | .ret r => .ret ⟨applyTerm σ r.payload⟩
  | .mapWrite m => .mapWrite (applyMutation σ m)
  | .packetWrite p => .packetWrite
      { p with offset := applyTerm σ p.offset, value := applyValue σ p.value }

mutual
  def mergeList (σ : CrossSubst) : List CrossTerm → List CrossTerm → Option CrossSubst
    | [], [] => some σ
    | a :: as, b :: bs => do
      let σ' ← mergeTerm σ a b
      mergeList σ' as bs
    | _, _ => none
  termination_by as bs => sizeOf as + sizeOf bs

  def mergeTerm (σ : CrossSubst) : CrossTerm → CrossTerm → Option CrossSubst
    | .c a, .c b => if a == b then some σ else none
    | .var a, .var b => addVar? σ a b
    | .reg k a, .reg l b => if k == l then addReg? σ k a b else none
    | .app f as, .app g bs => if f == g then mergeList σ as bs else none
    | .external l as, .external m bs => if l == m then mergeList σ as bs else none
    | _, _ => none
  termination_by a b => sizeOf a + sizeOf b
end

def mergeValue (σ : CrossSubst) : CrossValue → CrossValue → Option CrossSubst
  | .bytes as, .bytes bs => mergeList σ as bs
  | .source a, .source b => mergeTerm σ a b
  | _, _ => none

def mergeMutation (σ : CrossSubst) (a b : CrossMutation) : Option CrossSubst := do
  if a.kind != b.kind then none
  let σ ← mergeTerm σ a.map b.map
  let σ ← mergeList σ a.key b.key
  if a.offset != b.offset then none
  mergeValue σ a.value b.value

def mergeHelper (σ : CrossSubst) : CrossHelper → CrossHelper → Option CrossSubst
  | .lookup a as, .lookup b bs => do
    let σ ← mergeTerm σ a b
    mergeList σ as bs
  | .mutation a, .mutation b => mergeMutation σ a b
  | .other a as, .other b bs => if a == b then mergeList σ as bs else none
  | _, _ => none

def mergeCond (σ : CrossSubst) : CrossCond → CrossCond → Option CrossSubst
  | .plain r a b, .plain s c d => do
    if r != s then none
    let σ ← mergeTerm σ a c
    mergeTerm σ b d
  | .packetBound a r b, .packetBound c s d => do
    if r != s then none
    let σ ← mergeTerm σ a c
    mergeTerm σ b d
  | .packetField a r z, .packetField b s w =>
    if r == s && z == w then mergeTerm σ a b else none
  | _, _ => none

def mergePred (σ : CrossSubst) : CrossPred → CrossPred → Option CrossSubst
  | .helper a, .helper b => mergeHelper σ a b
  | .branch a, .branch b => if a.dir == b.dir then mergeCond σ a.cond b.cond else none
  | .ret a, .ret b => mergeTerm σ a.payload b.payload
  | .mapWrite a, .mapWrite b => mergeMutation σ a b
  | .packetWrite a, .packetWrite b => do
    if a.packet != b.packet then none else
      let σ ← mergeTerm σ a.offset b.offset
      mergeValue σ a.value b.value
  | _, _ => none

mutual
  theorem applyTerm_empty (t : CrossTerm) : applyTerm .empty t = t := by
    cases t with
    | c z => simp only [applyTerm]
    | var n => simp [applyTerm, varLookup, varImage?, empty]
    | reg k a => simp [applyTerm, regLookup, regImage?, empty]
    | app f ts => simp only [applyTerm, applyTerms_empty ts]
    | external l ts => simp only [applyTerm, applyTerms_empty ts]
  termination_by sizeOf t

  theorem applyTerms_empty (ts : List CrossTerm) : applyTerms .empty ts = ts := by
    cases ts with
    | nil => simp only [applyTerms]
    | cons t ts => simp only [applyTerms, applyTerm_empty t, applyTerms_empty ts]
  termination_by sizeOf ts
end

private theorem applyValue_empty (v : CrossValue) : applyValue .empty v = v := by
  cases v <;> simp only [applyValue, applyTerm_empty, applyTerms_empty]

private theorem applyMutation_empty (m : CrossMutation) :
    applyMutation .empty m = m := by
  simp only [applyMutation, applyTerm_empty, applyTerms_empty, applyValue_empty]

private theorem applyHelper_empty (h : CrossHelper) : applyHelper .empty h = h := by
  cases h <;> simp only [applyHelper, applyTerm_empty, applyTerms_empty, applyMutation_empty]

private theorem applyCond_empty (c : CrossCond) : applyCond .empty c = c := by
  cases c <;> simp only [applyCond, applyTerm_empty]

theorem rename_empty (p : CrossPred) : rename .empty p = p := by
  cases p <;> simp only [rename, applyHelper_empty, applyCond_empty,
    applyTerm_empty, applyMutation_empty, applyValue_empty]

mutual
  private theorem applyTerm_inverse (σ τ : CrossSubst)
      (hv : ∀ n, τ.varLookup (σ.varLookup n) = n)
      (hr : ∀ k a, τ.regLookup k (σ.regLookup k a) = a) (t : CrossTerm) :
      applyTerm τ (applyTerm σ t) = t := by
    cases t with
    | c z => simp only [applyTerm]
    | var n => simp only [applyTerm, hv]
    | reg k a => simp only [applyTerm, hr]
    | app f ts => simp only [applyTerm, applyTerms_inverse σ τ hv hr ts]
    | external l ts => simp only [applyTerm, applyTerms_inverse σ τ hv hr ts]
  termination_by sizeOf t

  private theorem applyTerms_inverse (σ τ : CrossSubst)
      (hv : ∀ n, τ.varLookup (σ.varLookup n) = n)
      (hr : ∀ k a, τ.regLookup k (σ.regLookup k a) = a) (ts : List CrossTerm) :
      applyTerms τ (applyTerms σ ts) = ts := by
    cases ts with
    | nil => simp only [applyTerms]
    | cons t ts => simp only [applyTerms, applyTerm_inverse σ τ hv hr t,
        applyTerms_inverse σ τ hv hr ts]
  termination_by sizeOf ts
end

theorem rename_swap (σ : CrossSubst)
    (hv : ∀ n, σ.swap.varLookup (σ.varLookup n) = n)
    (hr : ∀ k a, σ.swap.regLookup k (σ.regLookup k a) = a) (p : CrossPred) :
    rename σ.swap (rename σ p) = p := by
  have ht := applyTerm_inverse σ σ.swap hv hr
  have hts := applyTerms_inverse σ σ.swap hv hr
  have hvv : ∀ v, applyValue σ.swap (applyValue σ v) = v := by
    intro v; cases v <;> simp only [applyValue, ht, hts]
  have hmm : ∀ m, applyMutation σ.swap (applyMutation σ m) = m := by
    intro m; simp only [applyMutation, ht, hts, hvv]
  have hhh : ∀ h, applyHelper σ.swap (applyHelper σ h) = h := by
    intro h; cases h <;> simp only [applyHelper, ht, hts, hmm]
  have hcc : ∀ c, applyCond σ.swap (applyCond σ c) = c := by
    intro c; cases c <;> simp only [applyCond, ht]
  cases p <;> simp only [rename, hhh, hcc, ht, hmm, hvv]

/- All renameable occurrences, including identity bindings, have been pinned. -/
mutual
  def Determined (σ : CrossSubst) : CrossTerm → Prop
    | .c _ => True
    | .var n => ∃ y, σ.varImage? n = some y
    | .reg k a => ∃ b, σ.regImage? k a = some b
    | .app _ ts | .external _ ts => DeterminedTerms σ ts
  termination_by t => sizeOf t

  def DeterminedTerms (σ : CrossSubst) : List CrossTerm → Prop
    | [] => True
    | t :: ts => Determined σ t ∧ DeterminedTerms σ ts
  termination_by ts => sizeOf ts
end

private theorem find_key_of_mem {α κ : Type} [BEq κ] [LawfulBEq κ]
    (key : α → κ) {xs : List α} (hn : (xs.map key).Nodup)
    {e : α} (he : e ∈ xs) :
    xs.find? (fun d => key d == key e) = some e := by
  induction xs with
  | nil => simp at he
  | cons d ds ih =>
    simp only [List.map_cons, List.nodup_cons] at hn
    rcases List.mem_cons.mp he with rfl | he
    · simp
    · have hne : key d ≠ key e := by
        intro h
        exact hn.1 (h ▸ List.mem_map.mpr ⟨e, he, rfl⟩)
      simp only [List.find?_cons, beq_eq_false_iff_ne.mpr hne]
      exact ih hn.2 he

private theorem image_some_iff {α κ δ : Type} [BEq κ] [LawfulBEq κ]
    (key : α → κ) (value : α → δ) {xs : List α}
    (hn : (xs.map key).Nodup) (x : κ) (y : δ) :
    (xs.find? (fun e => key e == x)).map value = some y ↔
      ∃ e ∈ xs, key e = x ∧ value e = y := by
  constructor
  · intro h
    cases hf : xs.find? (fun e => key e == x) with
    | none => simp [hf] at h
    | some e =>
      exact ⟨e, List.mem_of_find?_eq_some hf,
        eq_of_beq (List.find?_some (p := fun d => key d == x) hf), by simpa [hf] using h⟩
  · rintro ⟨e, he, hk, hv⟩
    rw [← hk, find_key_of_mem key hn he]
    simp [hv]

theorem extends_refl (σ : CrossSubst) : Extends σ σ :=
  ⟨fun _ h => h, fun _ h => h⟩

theorem extends_trans {σ τ υ : CrossSubst} (h : Extends σ τ) (g : Extends τ υ) :
    Extends σ υ :=
  ⟨fun e he => g.1 e (h.1 e he), fun e he => g.2 e (h.2 e he)⟩

theorem varImage_some_iff {σ : CrossSubst} (h : Injective σ) (x y : Nat) :
    σ.varImage? x = some y ↔ (x, y) ∈ σ.vars := by
  rw [varImage?, image_some_iff (fun e : Nat × Nat => e.1) (fun e => e.2) h.1]
  constructor
  · rintro ⟨⟨a, b⟩, he, rfl, rfl⟩; exact he
  · intro he; exact ⟨(x, y), he, rfl, rfl⟩

theorem regImage_some_iff {σ : CrossSubst} (h : Injective σ) (k : RegKind) (a b : Nat) :
    σ.regImage? k a = some b ↔ (k, a, b) ∈ σ.regs := by
  have hp : (fun e : RegKind × Nat × Nat => e.1 == k && e.2.1 == a) =
      (fun e => (e.1, e.2.1) == (k, a)) := by
    funext e; rfl
  rw [regImage?, hp, image_some_iff
    (fun e : RegKind × Nat × Nat => (e.1, e.2.1)) (fun e => e.2.2) h.2.2.1]
  constructor
  · rintro ⟨⟨l, c, d⟩, he, hk, rfl⟩
    cases hk; exact he
  · intro he; exact ⟨(k, a, b), he, rfl, rfl⟩

theorem varImage_extends {σ τ : CrossSubst} (he : Extends σ τ)
    (hi : Injective σ) (hj : Injective τ) {x y : Nat}
    (h : σ.varImage? x = some y) : τ.varImage? x = some y :=
  (varImage_some_iff hj x y).mpr (he.1 _ ((varImage_some_iff hi x y).mp h))

theorem regImage_extends {σ τ : CrossSubst} (he : Extends σ τ)
    (hi : Injective σ) (hj : Injective τ) {k : RegKind} {a b : Nat}
    (h : σ.regImage? k a = some b) : τ.regImage? k a = some b :=
  (regImage_some_iff hj k a b).mpr (he.2 _ ((regImage_some_iff hi k a b).mp h))

theorem addVar_sound {σ τ : CrossSubst} {x y : Nat} (hi : Injective σ)
    (h : addVar? σ x y = some τ) :
    Extends σ τ ∧ Injective τ ∧ τ.varImage? x = some y := by
  unfold addVar? at h
  split at h
  · split at h
    · have hτ : σ = τ := Option.some.inj h
      subst τ
      exact ⟨extends_refl σ, hi, by simp_all⟩
    · contradiction
  · rename_i hn
    split at h
    · contradiction
    · have hτ : ⟨(x, y) :: σ.vars, σ.regs⟩ = τ := Option.some.inj h
      subst τ
      have hx : x ∉ σ.vars.map (·.1) := by
        intro hm
        obtain ⟨e, he, hk⟩ := List.mem_map.mp hm
        have hf := find_key_of_mem (fun e : Nat × Nat => e.1) hi.1 he
        have : σ.varImage? x = some e.2 := by
          simp only [varImage?, ← hk, hf, Option.map_some]
        rw [hn] at this
        contradiction
      have hy : y ∉ σ.vars.map (·.2) := by
        simpa using ‹¬ σ.vars.any (fun e => e.2 == y) = true›
      refine ⟨⟨fun e he => List.mem_cons_of_mem _ he, fun _ he => he⟩, ?_, ?_⟩
      · simpa [Injective, List.map_cons, List.nodup_cons] using
          And.intro (And.intro hx hi.1) (And.intro (And.intro hy hi.2.1) hi.2.2)
      · simp [varImage?]

theorem addReg_sound {σ τ : CrossSubst} {k : RegKind} {a b : Nat}
    (hi : Injective σ) (h : addReg? σ k a b = some τ) :
    Extends σ τ ∧ Injective τ ∧ τ.regImage? k a = some b := by
  unfold addReg? at h
  split at h
  · split at h
    · have hτ : σ = τ := Option.some.inj h
      subst τ
      exact ⟨extends_refl σ, hi, by simp_all⟩
    · contradiction
  · rename_i hn
    split at h
    · contradiction
    · have hτ : ⟨σ.vars, (k, a, b) :: σ.regs⟩ = τ := Option.some.inj h
      subst τ
      have ha : (k, a) ∉ σ.regs.map (fun e => (e.1, e.2.1)) := by
        intro hm
        obtain ⟨⟨l, c, d⟩, he, hk⟩ := List.mem_map.mp hm
        cases hk
        have hf := (regImage_some_iff hi l c d).mpr he
        rw [hn] at hf
        contradiction
      have hb : (k, b) ∉ σ.regs.map (fun e => (e.1, e.2.2)) := by
        simpa [List.mem_map, Prod.ext_iff] using
          ‹¬ σ.regs.any (fun e => e.1 == k && e.2.2 == b) = true›
      refine ⟨⟨fun _ he => he, fun e he => List.mem_cons_of_mem _ he⟩, ?_, ?_⟩
      · simpa [Injective, List.map_cons, List.nodup_cons] using
          And.intro hi.1 (And.intro hi.2.1
            (And.intro (And.intro ha hi.2.2.1) (And.intro hb hi.2.2.2)))
      · simp [regImage?]

mutual
  theorem determined_extends {σ τ : CrossSubst} (he : Extends σ τ)
      (hi : Injective σ) (hj : Injective τ) (a : CrossTerm) (hd : Determined σ a) :
      Determined τ a ∧ applyTerm τ a = applyTerm σ a := by
    cases a <;> simp only [Determined] at hd ⊢
    case c z => exact ⟨True.intro, by simp only [applyTerm]⟩
    case var x =>
      obtain ⟨y, hy⟩ := hd
      have ht := varImage_extends he hi hj hy
      exact ⟨⟨y, ht⟩, by simp [applyTerm, varLookup, ht, hy]⟩
    case reg k a =>
      obtain ⟨b, hb⟩ := hd
      have ht := regImage_extends he hi hj hb
      exact ⟨⟨b, ht⟩, by simp [applyTerm, regLookup, ht, hb]⟩
    case app f ts =>
      obtain ⟨hd, ht⟩ := determinedTerms_extends he hi hj ts hd
      exact ⟨hd, by simp only [applyTerm, ht]⟩
    case external l ts =>
      obtain ⟨hd, ht⟩ := determinedTerms_extends he hi hj ts hd
      exact ⟨hd, by simp only [applyTerm, ht]⟩
  termination_by sizeOf a

  theorem determinedTerms_extends {σ τ : CrossSubst} (he : Extends σ τ)
      (hi : Injective σ) (hj : Injective τ) (as : List CrossTerm)
      (hd : DeterminedTerms σ as) :
      DeterminedTerms τ as ∧ applyTerms τ as = applyTerms σ as := by
    cases as <;> simp only [DeterminedTerms] at hd ⊢
    case nil => exact ⟨True.intro, by simp only [applyTerms]⟩
    case cons a as =>
      obtain ⟨ha, hta⟩ := determined_extends he hi hj a hd.1
      obtain ⟨has, htas⟩ := determinedTerms_extends he hi hj as hd.2
      exact ⟨⟨ha, has⟩, by simp only [applyTerms, hta, htas]⟩
  termination_by sizeOf as
end

mutual
  theorem mergeTerm_spec (σ τ : CrossSubst) (a b : CrossTerm)
      (hi : Injective σ) (h : mergeTerm σ a b = some τ) :
      Extends σ τ ∧ Injective τ ∧ Determined τ a ∧ applyTerm τ a = b := by
    cases a <;> cases b <;> simp only [mergeTerm, Determined] at h ⊢
    all_goals try split at h
    all_goals try contradiction
    case c.c.isTrue z w hc =>
      have : z = w := eq_of_beq hc
      subst w; cases h
      exact ⟨extends_refl _, hi, True.intro, by simp only [applyTerm]⟩
    case var.var x y =>
      obtain ⟨he, hj, hv⟩ := addVar_sound hi h
      exact ⟨he, hj, ⟨y, hv⟩, by simp [applyTerm, varLookup, hv]⟩
    case reg.reg.isTrue k a l b hk =>
      have : k = l := eq_of_beq hk
      subst l
      obtain ⟨he, hj, hr⟩ := addReg_sound hi h
      exact ⟨he, hj, ⟨b, hr⟩, by simp [applyTerm, regLookup, hr]⟩
    case app.app.isTrue f as g bs hf =>
      have : f = g := eq_of_beq hf
      subst g
      obtain ⟨he, hj, hd, ht⟩ := mergeList_spec σ τ as bs hi h
      exact ⟨he, hj, hd, by simp only [applyTerm, ht]⟩
    case external.external.isTrue l as m bs hl =>
      have : l = m := eq_of_beq hl
      subst m
      obtain ⟨he, hj, hd, ht⟩ := mergeList_spec σ τ as bs hi h
      exact ⟨he, hj, hd, by simp only [applyTerm, ht]⟩
  termination_by sizeOf a + sizeOf b

  theorem mergeList_spec (σ τ : CrossSubst) (as bs : List CrossTerm)
      (hi : Injective σ) (h : mergeList σ as bs = some τ) :
      Extends σ τ ∧ Injective τ ∧ DeterminedTerms τ as ∧ applyTerms τ as = bs := by
    cases as with
    | nil =>
      cases bs <;> simp only [mergeList, DeterminedTerms] at h ⊢
      · cases h; exact ⟨extends_refl _, hi, True.intro, by simp only [applyTerms]⟩
      · contradiction
    | cons a as =>
      cases bs with
      | nil => simp [mergeList] at h
      | cons b bs =>
        simp only [mergeList, Option.bind_eq_bind] at h
        cases hm : mergeTerm σ a b with
        | none => simp [hm] at h
        | some υ =>
          simp only [hm, Option.bind_some] at h
          obtain ⟨he, hj, hd, ht⟩ := mergeTerm_spec σ υ a b hi hm
          obtain ⟨he', hj', hd', ht'⟩ := mergeList_spec υ τ as bs hj h
          obtain ⟨hda, hta⟩ := determined_extends he' hj hj' a hd
          simp only [DeterminedTerms]
          exact ⟨extends_trans he he', hj', ⟨hda, hd'⟩,
            by simp only [applyTerms, hta, ht, ht']⟩
  termination_by sizeOf as + sizeOf bs
end

theorem mergeList_already_determined (σ τ υ : CrossSubst) (as bs : List CrossTerm)
    (hi : Injective σ) (h : mergeList σ as bs = some τ)
    (he : Extends τ υ) (hj : Injective υ) : applyTerms υ as = bs := by
  obtain ⟨_, ht, hd, ha⟩ := mergeList_spec σ τ as bs hi h
  exact (determinedTerms_extends he ht hj as hd).2.trans ha

theorem mergeValue_spec (σ τ : CrossSubst) (a b : CrossValue)
    (hi : Injective σ) (h : mergeValue σ a b = some τ) :
    Extends σ τ ∧ Injective τ ∧
      ∀ υ, Extends τ υ → Injective υ → applyValue υ a = b := by
  cases a <;> cases b <;> simp only [mergeValue] at h
  all_goals try contradiction
  case bytes.bytes as bs =>
    obtain ⟨he, hj, hd, ht⟩ := mergeList_spec σ τ as bs hi h
    refine ⟨he, hj, fun υ he' hj' => ?_⟩
    simp only [applyValue, mergeList_already_determined σ τ υ as bs hi h he' hj']
  case source.source a b =>
    obtain ⟨he, hj, hd, ht⟩ := mergeTerm_spec σ τ a b hi h
    refine ⟨he, hj, fun υ he' hj' => ?_⟩
    simp only [applyValue, (determined_extends he' hj hj' a hd).2, ht]

theorem mergeMutation_spec (σ τ : CrossSubst) (a b : CrossMutation)
    (hi : Injective σ) (h : mergeMutation σ a b = some τ) :
    Extends σ τ ∧ Injective τ ∧
      ∀ υ, Extends τ υ → Injective υ → applyMutation υ a = b := by
  simp only [mergeMutation, Option.bind_eq_bind] at h
  split at h
  · simp at h
  · rename_i hk
    have hk : a.kind = b.kind := by simpa using hk
    cases hm : mergeTerm σ a.map b.map with
    | none => simp [hm] at h
    | some σ₁ =>
      simp only [hm, Option.bind_some] at h
      obtain ⟨he₁, hi₁, hd₁, ht₁⟩ := mergeTerm_spec σ σ₁ a.map b.map hi hm
      cases hl : mergeList σ₁ a.key b.key with
      | none => simp [hl] at h
      | some σ₂ =>
        simp only [hl, Option.bind_some] at h
        obtain ⟨he₂, hi₂, _, _⟩ := mergeList_spec σ₁ σ₂ a.key b.key hi₁ hl
        split at h
        · simp at h
        · rename_i ho
          have ho : a.offset = b.offset := by simpa using ho
          obtain ⟨he₃, hi₃, hv⟩ := mergeValue_spec σ₂ τ a.value b.value hi₂ h
          refine ⟨extends_trans (extends_trans he₁ he₂) he₃, hi₃, ?_⟩
          intro υ he₄ hi₄
          have hm' := (determined_extends
            (extends_trans he₂ (extends_trans he₃ he₄)) hi₁ hi₄ a.map hd₁).2.trans ht₁
          have hl' := mergeList_already_determined σ₁ σ₂ υ a.key b.key hi₁ hl
            (extends_trans he₃ he₄) hi₄
          have hv' := hv υ he₄ hi₄
          cases a; cases b
          simp_all only [applyMutation]

theorem mergeHelper_spec (σ τ : CrossSubst) (a b : CrossHelper)
    (hi : Injective σ) (h : mergeHelper σ a b = some τ) :
    Extends σ τ ∧ Injective τ ∧
      ∀ υ, Extends τ υ → Injective υ → applyHelper υ a = b := by
  cases a <;> cases b <;> simp only [mergeHelper, Option.bind_eq_bind] at h
  all_goals try contradiction
  case lookup.lookup a as b bs =>
    cases hm : mergeTerm σ a b with
    | none => simp [hm] at h
    | some σ₁ =>
      simp only [hm, Option.bind_some] at h
      obtain ⟨he₁, hi₁, hd₁, ht₁⟩ := mergeTerm_spec σ σ₁ a b hi hm
      obtain ⟨he₂, hi₂, _, _⟩ := mergeList_spec σ₁ τ as bs hi₁ h
      refine ⟨extends_trans he₁ he₂, hi₂, ?_⟩
      intro υ he₃ hi₃
      have ht := (determined_extends (extends_trans he₂ he₃) hi₁ hi₃ a hd₁).2.trans ht₁
      have hts := mergeList_already_determined σ₁ τ υ as bs hi₁ h he₃ hi₃
      simp only [applyHelper, ht, hts]
  case mutation.mutation a b =>
    obtain ⟨he, hj, ht⟩ := mergeMutation_spec σ τ a b hi h
    exact ⟨he, hj, fun υ he' hj' => by simp only [applyHelper, ht υ he' hj']⟩
  case other.other a as b bs =>
    split at h
    · rename_i hab
      have : a = b := eq_of_beq hab
      subst b
      obtain ⟨he, hj, _, _⟩ := mergeList_spec σ τ as bs hi h
      exact ⟨he, hj, fun υ he' hj' => by
        simp only [applyHelper, mergeList_already_determined σ τ υ as bs hi h he' hj']⟩
    · contradiction

theorem mergeCond_spec (σ τ : CrossSubst) (a b : CrossCond)
    (hi : Injective σ) (h : mergeCond σ a b = some τ) :
    Extends σ τ ∧ Injective τ ∧
      ∀ υ, Extends τ υ → Injective υ → applyCond υ a = b := by
  cases a <;> cases b <;> simp only [mergeCond, Option.bind_eq_bind] at h
  all_goals try contradiction
  case plain.plain r a b s c d =>
    split at h
    · simp at h
    · rename_i hrs
      have : r = s := by simpa using hrs
      subst s
      cases hm : mergeTerm σ a c with
      | none => simp [hm] at h
      | some σ₁ =>
        simp only [hm, Option.bind_some] at h
        obtain ⟨he₁, hi₁, hd₁, ht₁⟩ := mergeTerm_spec σ σ₁ a c hi hm
        obtain ⟨he₂, hi₂, hd₂, ht₂⟩ := mergeTerm_spec σ₁ τ b d hi₁ h
        refine ⟨extends_trans he₁ he₂, hi₂, ?_⟩
        intro υ he₃ hi₃
        have ht := (determined_extends (extends_trans he₂ he₃) hi₁ hi₃ a hd₁).2.trans ht₁
        have ht' := (determined_extends he₃ hi₂ hi₃ b hd₂).2.trans ht₂
        simp only [applyCond, ht, ht']
  case packetBound.packetBound a r b c s d =>
    split at h
    · simp at h
    · rename_i hrs
      have : r = s := by simpa using hrs
      subst s
      cases hm : mergeTerm σ a c with
      | none => simp [hm] at h
      | some σ₁ =>
        simp only [hm, Option.bind_some] at h
        obtain ⟨he₁, hi₁, hd₁, ht₁⟩ := mergeTerm_spec σ σ₁ a c hi hm
        obtain ⟨he₂, hi₂, hd₂, ht₂⟩ := mergeTerm_spec σ₁ τ b d hi₁ h
        refine ⟨extends_trans he₁ he₂, hi₂, ?_⟩
        intro υ he₃ hi₃
        have ht := (determined_extends (extends_trans he₂ he₃) hi₁ hi₃ a hd₁).2.trans ht₁
        have ht' := (determined_extends he₃ hi₂ hi₃ b hd₂).2.trans ht₂
        simp only [applyCond, ht, ht']
  case packetField.packetField a r z b s w =>
    split at h
    · rename_i hrz
      obtain ⟨hrs, hzw⟩ : r = s ∧ z = w := by simpa using hrz
      subst s; subst w
      obtain ⟨he, hj, hd, ht⟩ := mergeTerm_spec σ τ a b hi h
      exact ⟨he, hj, fun υ he' hj' => by
        simp only [applyCond, (determined_extends he' hj hj' a hd).2, ht]⟩
    · contradiction

theorem mergePred_spec (σ τ : CrossSubst) (a b : CrossPred)
    (hi : Injective σ) (h : mergePred σ a b = some τ) :
    Extends σ τ ∧ Injective τ ∧
      ∀ υ, Extends τ υ → Injective υ → rename υ a = b := by
  cases a <;> cases b <;> simp only [mergePred] at h
  all_goals try contradiction
  case helper.helper a b =>
    obtain ⟨he, hj, ht⟩ := mergeHelper_spec σ τ a b hi h
    exact ⟨he, hj, fun υ he' hj' => by simp only [rename, ht υ he' hj']⟩
  case branch.branch a b =>
    split at h
    · rename_i hdir
      have hdir : a.dir = b.dir := eq_of_beq hdir
      obtain ⟨he, hj, ht⟩ := mergeCond_spec σ τ a.cond b.cond hi h
      refine ⟨he, hj, fun υ he' hj' => ?_⟩
      have ht := ht υ he' hj'
      cases a; cases b; simp_all only [rename]
    · contradiction
  case ret.ret a b =>
    obtain ⟨he, hj, hd, ht⟩ := mergeTerm_spec σ τ a.payload b.payload hi h
    refine ⟨he, hj, fun υ he' hj' => ?_⟩
    have ht := (determined_extends he' hj hj' a.payload hd).2.trans ht
    cases a; cases b; simp_all only [rename]
  case mapWrite.mapWrite a b =>
    obtain ⟨he, hj, ht⟩ := mergeMutation_spec σ τ a b hi h
    exact ⟨he, hj, fun υ he' hj' => by simp only [rename, ht υ he' hj']⟩
  case packetWrite.packetWrite a b =>
    simp only [Option.bind_eq_bind] at h
    split at h
    · simp at h
    · rename_i hp
      have hp : a.packet = b.packet := by simpa using hp
      cases ho : mergeTerm σ a.offset b.offset with
      | none => simp [ho] at h
      | some σ₁ =>
        simp only [ho, Option.bind_some] at h
        obtain ⟨he₁, hi₁, hd₁, ht₁⟩ := mergeTerm_spec σ σ₁ a.offset b.offset hi ho
        obtain ⟨he₂, hi₂, ht₂⟩ := mergeValue_spec σ₁ τ a.value b.value hi₁ h
        refine ⟨extends_trans he₁ he₂, hi₂, fun υ he₃ hi₃ => ?_⟩
        have ho' := (determined_extends (extends_trans he₂ he₃)
          hi₁ hi₃ a.offset hd₁).2.trans ht₁
        have hv' := ht₂ υ he₃ hi₃
        cases a; cases b; simp_all only [rename]

private theorem filtered_lookup_getD {α κ δ : Type}
    [BEq κ] [LawfulBEq κ] [BEq δ] [LawfulBEq δ]
    (key : α → κ) (value : α → δ) (default : κ → δ)
    (xs : List α) (hn : (xs.map key).Nodup) (x : κ) :
    (((xs.filter (fun e => default (key e) != value e)).find?
      (fun e => key e == x)).map value).getD (default x) =
    ((xs.find? (fun e => key e == x)).map value).getD (default x) := by
  induction xs with
  | nil => simp
  | cons e es ih =>
    simp only [List.map_cons, List.nodup_cons] at hn
    by_cases hk : key e = x
    · have hf : es.find? (fun d => key d == x) = none := by
        apply List.find?_eq_none.mpr
        intro d hd heq
        have hdx : key d = x := eq_of_beq heq
        exact hn.1 (List.mem_map.mpr ⟨d, hd, hdx.trans hk.symm⟩)
      have hg : (es.filter (fun d => default (key d) != value d)).find?
          (fun d => key d == x) = none := by
        apply List.find?_eq_none.mpr
        intro d hd
        exact List.find?_eq_none.mp hf d (List.mem_filter.mp hd).1
      by_cases hv : default x = value e
      · simp [hk, hv, hg]
      · simp [hk, hv]
    · have hk' : (key e == x) = false := beq_eq_false_iff_ne.mpr hk
      by_cases hv : (default (key e) != value e) = true
      · simpa [List.filter_cons, List.find?_cons, hk', hv] using ih hn.2
      · simpa [List.filter_cons, List.find?_cons, hk', hv] using ih hn.2

theorem strip_varLookup {σ : CrossSubst} (hi : Injective σ) (x : Nat) :
    σ.strip.varLookup x = σ.varLookup x := by
  exact filtered_lookup_getD (fun e : Nat × Nat => e.1) (·.2) id σ.vars hi.1 x

theorem strip_regLookup {σ : CrossSubst} (hi : Injective σ) (k : RegKind) (a : Nat) :
    σ.strip.regLookup k a = σ.regLookup k a := by
  exact filtered_lookup_getD (fun e : RegKind × Nat × Nat => (e.1, e.2.1))
    (·.2.2) (·.2) σ.regs hi.2.2.1 (k, a)

theorem strip_injective {σ : CrossSubst} (hi : Injective σ) : Injective σ.strip := by
  exact ⟨(List.filter_sublist.map _).nodup hi.1,
    (List.filter_sublist.map _).nodup hi.2.1,
    (List.filter_sublist.map _).nodup hi.2.2.1,
    (List.filter_sublist.map _).nodup hi.2.2.2⟩

mutual
  theorem strip_applyTerm {σ : CrossSubst} (hi : Injective σ) (t : CrossTerm) :
      applyTerm σ.strip t = applyTerm σ t := by
    cases t with
    | c z => simp only [applyTerm]
    | var x => simp only [applyTerm, strip_varLookup hi]
    | reg k a => simp only [applyTerm, strip_regLookup hi]
    | app f ts => simp only [applyTerm, strip_applyTerms hi ts]
    | external l ts => simp only [applyTerm, strip_applyTerms hi ts]
  termination_by sizeOf t

  theorem strip_applyTerms {σ : CrossSubst} (hi : Injective σ) (ts : List CrossTerm) :
      applyTerms σ.strip ts = applyTerms σ ts := by
    cases ts with
    | nil => simp only [applyTerms]
    | cons t ts => simp only [applyTerms, strip_applyTerm hi t, strip_applyTerms hi ts]
  termination_by sizeOf ts
end

def DeterminedValue (σ : CrossSubst) : CrossValue → Prop
  | .bytes ts => DeterminedTerms σ ts
  | .source t => Determined σ t

def DeterminedMutation (σ : CrossSubst) (m : CrossMutation) : Prop :=
  Determined σ m.map ∧ DeterminedTerms σ m.key ∧ DeterminedValue σ m.value

def DeterminedHelper (σ : CrossSubst) : CrossHelper → Prop
  | .lookup m key => Determined σ m ∧ DeterminedTerms σ key
  | .mutation m => DeterminedMutation σ m
  | .other _ args => DeterminedTerms σ args

def DeterminedCond (σ : CrossSubst) : CrossCond → Prop
  | .plain _ a b | .packetBound a _ b => Determined σ a ∧ Determined σ b
  | .packetField a _ _ => Determined σ a

/-- Every renameable occurrence has an explicit binding, including identities. -/
def DeterminedPred (σ : CrossSubst) : CrossPred → Prop
  | .helper h => DeterminedHelper σ h
  | .branch b => DeterminedCond σ b.cond
  | .ret r => Determined σ r.payload
  | .mapWrite m => DeterminedMutation σ m
  | .packetWrite p => Determined σ p.offset ∧ DeterminedValue σ p.value

theorem determinedPred_extends {σ τ : CrossSubst} (he : Extends σ τ)
    (hi : Injective σ) (hj : Injective τ) (p : CrossPred)
    (hd : DeterminedPred σ p) : DeterminedPred τ p := by
  have ht := fun t h => (determined_extends he hi hj t h).1
  have hts := fun ts h => (determinedTerms_extends he hi hj ts h).1
  have hv : ∀ v, DeterminedValue σ v → DeterminedValue τ v := by
    intro v; cases v <;> simp only [DeterminedValue] <;> first | exact hts _ | exact ht _
  have hm : ∀ m, DeterminedMutation σ m → DeterminedMutation τ m := by
    intro m h
    exact ⟨ht _ h.1, hts _ h.2.1, hv _ h.2.2⟩
  have hh : ∀ h, DeterminedHelper σ h → DeterminedHelper τ h := by
    intro h; cases h with
    | lookup m key => exact fun h => ⟨ht _ h.1, hts _ h.2⟩
    | mutation m => exact hm m
    | other _ args => exact hts args
  have hc : ∀ c, DeterminedCond σ c → DeterminedCond τ c := by
    intro c; cases c with
    | plain _ a b | packetBound a _ b => exact fun h => ⟨ht _ h.1, ht _ h.2⟩
    | packetField a _ _ => exact ht a
  cases p with
  | helper h => exact hh h hd
  | branch b => exact hc b.cond hd
  | ret r => exact ht r.payload hd
  | mapWrite m => exact hm m hd
  | packetWrite p => exact ⟨ht p.offset hd.1, hv p.value hd.2⟩

private theorem mergeValue_determined (σ τ : CrossSubst) (a b : CrossValue)
    (hi : Injective σ) (h : mergeValue σ a b = some τ) :
    DeterminedValue τ a := by
  cases a <;> cases b <;> simp only [mergeValue] at h
  all_goals try contradiction
  case bytes.bytes as bs => exact (mergeList_spec σ τ as bs hi h).2.2.1
  case source.source a b => exact (mergeTerm_spec σ τ a b hi h).2.2.1

private theorem mergeMutation_determined (σ τ : CrossSubst) (a b : CrossMutation)
    (hi : Injective σ) (h : mergeMutation σ a b = some τ) :
    DeterminedMutation τ a := by
  simp only [mergeMutation, Option.bind_eq_bind] at h
  split at h
  · simp at h
  · cases hm : mergeTerm σ a.map b.map with
    | none => simp [hm] at h
    | some σ₁ =>
      simp only [hm, Option.bind_some] at h
      obtain ⟨_, hi₁, hd₁, _⟩ := mergeTerm_spec σ σ₁ a.map b.map hi hm
      cases hl : mergeList σ₁ a.key b.key with
      | none => simp [hl] at h
      | some σ₂ =>
        simp only [hl, Option.bind_some] at h
        obtain ⟨he₂, hi₂, hd₂, _⟩ := mergeList_spec σ₁ σ₂ a.key b.key hi₁ hl
        split at h
        · simp at h
        · obtain ⟨he₃, hi₃, _⟩ := mergeValue_spec σ₂ τ a.value b.value hi₂ h
          exact ⟨(determined_extends (extends_trans he₂ he₃) hi₁ hi₃ a.map hd₁).1,
            (determinedTerms_extends he₃ hi₂ hi₃ a.key hd₂).1,
            mergeValue_determined σ₂ τ a.value b.value hi₂ h⟩

private theorem mergeHelper_determined (σ τ : CrossSubst) (a b : CrossHelper)
    (hi : Injective σ) (h : mergeHelper σ a b = some τ) :
    DeterminedHelper τ a := by
  cases a <;> cases b <;> simp only [mergeHelper, Option.bind_eq_bind] at h
  all_goals try contradiction
  case lookup.lookup a as b bs =>
    cases hm : mergeTerm σ a b with
    | none => simp [hm] at h
    | some σ₁ =>
      simp only [hm, Option.bind_some] at h
      obtain ⟨_, hi₁, hd₁, _⟩ := mergeTerm_spec σ σ₁ a b hi hm
      obtain ⟨he₂, hi₂, hd₂, _⟩ := mergeList_spec σ₁ τ as bs hi₁ h
      exact ⟨(determined_extends he₂ hi₁ hi₂ a hd₁).1, hd₂⟩
  case mutation.mutation a b => exact mergeMutation_determined σ τ a b hi h
  case other.other a as b bs =>
    split at h
    · exact (mergeList_spec σ τ as bs hi h).2.2.1
    · contradiction

private theorem mergeCond_determined (σ τ : CrossSubst) (a b : CrossCond)
    (hi : Injective σ) (h : mergeCond σ a b = some τ) :
    DeterminedCond τ a := by
  cases a <;> cases b <;> simp only [mergeCond, Option.bind_eq_bind] at h
  all_goals try contradiction
  case plain.plain r a b s c d =>
    split at h
    · simp at h
    · cases hm : mergeTerm σ a c with
      | none => simp [hm] at h
      | some σ₁ =>
        simp only [hm, Option.bind_some] at h
        obtain ⟨_, hi₁, hd₁, _⟩ := mergeTerm_spec σ σ₁ a c hi hm
        obtain ⟨he₂, hi₂, hd₂, _⟩ := mergeTerm_spec σ₁ τ b d hi₁ h
        exact ⟨(determined_extends he₂ hi₁ hi₂ a hd₁).1, hd₂⟩
  case packetBound.packetBound a r b c s d =>
    split at h
    · simp at h
    · cases hm : mergeTerm σ a c with
      | none => simp [hm] at h
      | some σ₁ =>
        simp only [hm, Option.bind_some] at h
        obtain ⟨_, hi₁, hd₁, _⟩ := mergeTerm_spec σ σ₁ a c hi hm
        obtain ⟨he₂, hi₂, hd₂, _⟩ := mergeTerm_spec σ₁ τ b d hi₁ h
        exact ⟨(determined_extends he₂ hi₁ hi₂ a hd₁).1, hd₂⟩
  case packetField.packetField a r z b s w =>
    split at h
    · exact (mergeTerm_spec σ τ a b hi h).2.2.1
    · contradiction

theorem mergePred_determined (σ τ : CrossSubst) (a b : CrossPred)
    (hi : Injective σ) (h : mergePred σ a b = some τ) : DeterminedPred τ a := by
  cases a <;> cases b <;> simp only [mergePred] at h
  all_goals try contradiction
  case helper.helper a b => exact mergeHelper_determined σ τ a b hi h
  case branch.branch a b =>
    split at h
    · exact mergeCond_determined σ τ a.cond b.cond hi h
    · contradiction
  case ret.ret a b => exact (mergeTerm_spec σ τ a.payload b.payload hi h).2.2.1
  case mapWrite.mapWrite a b => exact mergeMutation_determined σ τ a b hi h
  case packetWrite.packetWrite a b =>
    simp only [Option.bind_eq_bind] at h
    split at h
    · simp at h
    · cases ho : mergeTerm σ a.offset b.offset with
      | none => simp [ho] at h
      | some σ₁ =>
        simp only [ho, Option.bind_some] at h
        obtain ⟨_, hi₁, hd₁, _⟩ := mergeTerm_spec σ σ₁ a.offset b.offset hi ho
        obtain ⟨he₂, hi₂, _⟩ := mergeValue_spec σ₁ τ a.value b.value hi₁ h
        exact ⟨(determined_extends he₂ hi₁ hi₂ a.offset hd₁).1,
          mergeValue_determined σ₁ τ a.value b.value hi₁ h⟩

/-! Theorems discharge the local merge and identity-stripping obligations.
Malformed input substitutions still invalidate unconditional injectivity
preservation and unconditional identity stripping. -/
namespace ProofObligations

theorem mergeTerm_sound :
  ∀ σ σ' a b, Injective σ → mergeTerm σ a b = some σ' →
    Extends σ σ' ∧ Injective σ' ∧ applyTerm σ' a = b := by
  intro σ τ a b hi h
  obtain ⟨he, hj, _, ht⟩ := mergeTerm_spec σ τ a b hi h
  exact ⟨he, hj, ht⟩

theorem mergeTerm_determined :
  ∀ σ σ' a b, Injective σ → mergeTerm σ a b = some σ' → Determined σ' a := by
  intro σ τ a b hi h
  exact (mergeTerm_spec σ τ a b hi h).2.2.1

/-- The already-determined pair cannot be changed by later consistent merges. -/
theorem mergeTerm_already_determined :
  ∀ σ σ' σ'' a b, Injective σ → mergeTerm σ a b = some σ' →
    Extends σ' σ'' → Injective σ'' → applyTerm σ'' a = b := by
  intro σ τ υ a b hi h he hj
  obtain ⟨_, ht, hd, ha⟩ := mergeTerm_spec σ τ a b hi h
  exact (determined_extends he ht hj a hd).2.trans ha

theorem mergePred_sound :
  ∀ σ σ' a b, Injective σ → mergePred σ a b = some σ' →
    Extends σ σ' ∧ Injective σ' ∧ rename σ' a = b := by
  intro σ τ a b hi h
  obtain ⟨he, hj, ht⟩ := mergePred_spec σ τ a b hi h
  exact ⟨he, hj, ht τ (extends_refl τ) hj⟩

theorem strip_rename :
  ∀ σ p, Injective σ → rename σ.strip p = rename σ p := by
  intro σ p hi
  have ht := strip_applyTerm hi
  have hts := strip_applyTerms hi
  have hv : ∀ v, applyValue σ.strip v = applyValue σ v := by
    intro v; cases v <;> simp only [applyValue, ht, hts]
  have hm : ∀ m, applyMutation σ.strip m = applyMutation σ m := by
    intro m; simp only [applyMutation, ht, hts, hv]
  have hh : ∀ h, applyHelper σ.strip h = applyHelper σ h := by
    intro h; cases h <;> simp only [applyHelper, ht, hts, hm]
  have hc : ∀ c, applyCond σ.strip c = applyCond σ c := by
    intro c; cases c <;> simp only [applyCond, ht]
  cases p <;> simp only [rename, hh, hc, ht, hm, hv]

end ProofObligations

end CrossSubst

structure Match where
  size : Nat
  subst : CrossSubst
  pairs : List (Nat × Nat)
  ambiguous : Bool
  deriving Repr

/-- Select the first maximizer, but never erase multiplicity of maximizers. -/
private def chooseMatch (candidates : List Match) (fallback : Match) : Match :=
  let best := candidates.foldl (fun n m => max n m.size) 0
  let achievers := candidates.filter (·.size == best)
  let winner := achievers.headD fallback
  { winner with ambiguous := achievers.length > 1 || achievers.any (·.ambiguous) }

private theorem maxFold_bounds (xs : List Match) (n : Nat) :
    n ≤ xs.foldl (fun n m => max n m.size) n ∧
      ∀ m ∈ xs, m.size ≤ xs.foldl (fun n m => max n m.size) n := by
  induction xs generalizing n with
  | nil => simp
  | cons a xs ih =>
    obtain ⟨hn, hm⟩ := ih (max n a.size)
    constructor
    · exact Nat.le_trans (Nat.le_max_left n a.size) hn
    · intro m h
      rcases List.mem_cons.mp h with h | h
      · subst m; exact Nat.le_trans (Nat.le_max_right n a.size) hn
      · exact hm m h

private theorem maxFold_choice (xs : List Match) (n : Nat) :
    xs.foldl (fun n m => max n m.size) n = n ∨
      ∃ m ∈ xs, m.size = xs.foldl (fun n m => max n m.size) n := by
  induction xs generalizing n with
  | nil => exact Or.inl rfl
  | cons a xs ih =>
    obtain h | ⟨m, hm, he⟩ := ih (max n a.size)
    · by_cases hn : a.size ≤ n
      · exact Or.inl (by simpa [List.foldl, Nat.max_eq_left hn] using h)
      · have hna : n ≤ a.size := by omega
        exact Or.inr ⟨a, by simp, by
          simpa [List.foldl, Nat.max_eq_right hna] using h.symm⟩
    · exact Or.inr ⟨m, List.mem_cons_of_mem _ hm, he⟩

private theorem maxFold_attained (xs : List Match) (hne : xs ≠ []) :
    ∃ m ∈ xs, m.size = xs.foldl (fun n m => max n m.size) 0 := by
  obtain hz | hm := maxFold_choice xs 0
  · cases xs with
    | nil => contradiction
    | cons m ms =>
      refine ⟨m, by simp, ?_⟩
      have hb := (maxFold_bounds (m :: ms) 0).2 m (by simp)
      omega
  · exact hm

theorem chooseMatch_size_max (candidates : List Match) (fallback : Match)
    (hne : candidates ≠ []) :
    (chooseMatch candidates fallback).size =
      candidates.foldl (fun n m => max n m.size) 0 ∧
      ∀ m ∈ candidates, m.size ≤ (chooseMatch candidates fallback).size := by
  obtain ⟨m, hm, he⟩ := maxFold_attained candidates hne
  have ha : m ∈ candidates.filter
      (fun m => m.size == candidates.foldl (fun n m => max n m.size) 0) := by
    exact List.mem_filter.mpr ⟨hm, by simp [he]⟩
  unfold chooseMatch
  dsimp only
  generalize hx : candidates.filter
    (fun m => m.size == candidates.foldl (fun n m => max n m.size) 0) = achievers at *
  cases achievers with
  | nil => simp at ha
  | cons winner rest =>
    have hw : winner ∈ candidates.filter
        (fun m => m.size == candidates.foldl (fun n m => max n m.size) 0) := by
      rw [hx]; exact List.mem_cons_self
    have hs := eq_of_beq (List.mem_filter.mp hw).2
    exact ⟨hs, fun c hc => by simpa [hs] using (maxFold_bounds candidates 0).2 c hc⟩


/-- A maximizer is unique exactly when its branch is unique and has no child tie.
The certificate predicate is supplied independently of candidate generation. -/
theorem chooseMatch_ambiguity_certificate
    (candidates : List Match) (fallback : Match)
    (P : List (Nat × Nat) → Prop)
    (hne : candidates ≠ [])
    (hnd : (candidates.map Match.pairs).Nodup)
    (hlen : ∀ m ∈ candidates, m.pairs.length = m.size)
    (hself : ∀ m ∈ candidates, P m.pairs)
    (hchild : ∀ m ∈ candidates, m.ambiguous = true →
      ∃ p, P p ∧ p.length = m.size ∧ p ≠ m.pairs)
    (hcover : ∀ p, P p →
      p.length = (chooseMatch candidates fallback).size →
      ∃ m ∈ candidates, m.size = (chooseMatch candidates fallback).size ∧
        (p = m.pairs ∨ m.ambiguous = true)) :
    (chooseMatch candidates fallback).ambiguous = true ↔
      ∃ p, P p ∧ p.length = (chooseMatch candidates fallback).size ∧
        p ≠ (chooseMatch candidates fallback).pairs := by
  obtain ⟨m, hm, he⟩ := maxFold_attained candidates hne
  have hnonempty : candidates.filter
      (fun m => m.size == candidates.foldl (fun n m => max n m.size) 0) ≠ [] := by
    intro hz
    have hh : m ∈ candidates.filter
        (fun m => m.size == candidates.foldl (fun n m => max n m.size) 0) :=
      List.mem_filter.mpr ⟨hm, by simp [he]⟩
    simp only [hz, List.not_mem_nil] at hh
  unfold chooseMatch at *
  dsimp only at *
  generalize ha : candidates.filter
    (fun m => m.size == candidates.foldl (fun n m => max n m.size) 0) = achievers at *
  have hmem : ∀ a ∈ achievers, a ∈ candidates := by
    intro a hm
    rw [← ha] at hm
    exact (List.mem_filter.mp hm).1
  have hbest : ∀ a ∈ achievers,
      a.size = candidates.foldl (fun n m => max n m.size) 0 := by
    intro a hm
    rw [← ha] at hm
    exact eq_of_beq (List.mem_filter.mp hm).2
  have hand : (achievers.map Match.pairs).Nodup := by
    apply List.Nodup.sublist ?_ hnd
    rw [← ha]
    exact (List.filter_sublist).map Match.pairs
  cases achievers with
  | nil => exact False.elim (hnonempty rfl)
  | cons winner rest =>
    have hw := hmem winner List.mem_cons_self
    have hws := hbest winner List.mem_cons_self
    cases rest with
    | nil =>
      simp only [List.length_cons, List.length_nil, List.any_cons, List.any_nil,
        List.headD_cons, Nat.lt_irrefl, decide_false, Bool.false_or, Bool.or_false]
      change winner.ambiguous = true ↔
        ∃ p, P p ∧ p.length = winner.size ∧ p ≠ winner.pairs
      constructor
      · intro hamb
        obtain ⟨p, hp, hl, hn⟩ := hchild winner hw hamb
        exact ⟨p, hp, hl, hn⟩
      · rintro ⟨p, hp, hl, hn⟩
        obtain ⟨a, hac, has, hcase⟩ := hcover p hp hl
        have ham : a ∈ [winner] := by
          rw [← ha]
          exact List.mem_filter.mpr ⟨hac, by simp [has, hws]⟩
        have haw : a = winner := by simpa using ham
        subst a
        rcases hcase with hsame | hamb
        · exact False.elim (hn hsame)
        · exact hamb
    | cons second rest =>
      have hs := hmem second (by simp)
      have hss := hbest second (by simp)
      have hnepair : second.pairs ≠ winner.pairs := by
        have hh := (List.nodup_cons.mp hand).1
        intro heq
        apply hh
        simp only [List.map_cons, List.mem_cons]
        exact Or.inl heq.symm
      constructor
      · intro _
        refine ⟨second.pairs, hself second hs, ?_, hnepair⟩
        exact (hlen second hs).trans (hss.trans hws.symm)
      · intro _
        simp

/-- Each left position is either skipped or paired with one later right position.
This enumerates each increasing partial matching once, including the empty one. -/
def search (L R : List (Nat × CrossPred)) (σ : CrossSubst) : Match :=
  match L with
  | [] => ⟨0, σ, [], false⟩
  | l :: ls =>
    let skip := search ls R σ
    let branches := (List.range R.length).filterMap fun k => do
      let r ← R[k]?
      let σ' ← σ.mergePred l.2 r.2
      let s := search ls (R.drop (k + 1)) σ'
      pure ⟨s.size + 1, s.subst, (l.1, r.1) :: s.pairs, s.ambiguous⟩
    chooseMatch (skip :: branches) skip
termination_by L.length

theorem search_ge_skip (l : Nat × CrossPred) (ls R : List (Nat × CrossPred))
    (σ : CrossSubst) : (search ls R σ).size ≤ (search (l :: ls) R σ).size := by
  rw [search]
  exact (chooseMatch_size_max _ _ (by simp)).2 _ List.mem_cons_self

theorem search_ge_branch (l : Nat × CrossPred) (ls R : List (Nat × CrossPred))
    (σ τ : CrossSubst) (k : Nat) (r : Nat × CrossPred)
    (hg : R[k]? = some r) (hm : σ.mergePred l.2 r.2 = some τ) :
    (search ls (R.drop (k + 1)) τ).size + 1 ≤ (search (l :: ls) R σ).size := by
  rw [search]
  let s := search ls (R.drop (k + 1)) τ
  let m : Match := ⟨s.size + 1, s.subst, (l.1, r.1) :: s.pairs, s.ambiguous⟩
  apply (chooseMatch_size_max _ _ (by simp)).2 m
  apply List.mem_cons_of_mem
  apply List.mem_filterMap.mpr
  exact ⟨k, List.mem_range.mpr (List.getElem?_eq_some_iff.mp hg).1,
    by simp [hg, hm, m, s]⟩


private theorem chooseMatch_preserves (P : CrossSubst → List (Nat × Nat) → Prop)
    (candidates : List Match) (fallback : Match)
    (hf : P fallback.subst fallback.pairs)
    (hc : ∀ m ∈ candidates, P m.subst m.pairs) :
    P (chooseMatch candidates fallback).subst (chooseMatch candidates fallback).pairs := by
  unfold chooseMatch
  dsimp only
  generalize hb : candidates.foldl (fun n m => max n m.size) 0 = best
  generalize ha : candidates.filter (fun m => m.size == best) = achievers
  cases achievers with
  | nil => simpa using hf
  | cons m ms =>
    have hm : m ∈ candidates.filter (fun m => m.size == best) := by
      rw [ha]; exact List.mem_cons_self
    simpa using hc m (List.mem_filter.mp hm).1

theorem search_sound (L R : List (Nat × CrossPred)) (σ : CrossSubst)
    (hi : CrossSubst.Injective σ) :
    CrossSubst.Extends σ (search L R σ).subst ∧
    CrossSubst.Injective (search L R σ).subst ∧
    ∀ i j, (i, j) ∈ (search L R σ).pairs →
      ∃ a b, (i, a) ∈ L ∧ (j, b) ∈ R ∧
        CrossSubst.rename (search L R σ).subst a = b := by
  induction L generalizing R σ with
  | nil => simpa only [search, List.not_mem_nil, false_implies, implies_true, and_true]
      using And.intro (CrossSubst.extends_refl σ) hi
  | cons l ls ih =>
    rw [search]
    apply chooseMatch_preserves
      (fun τ pairs => CrossSubst.Extends σ τ ∧ CrossSubst.Injective τ ∧
        ∀ i j, (i, j) ∈ pairs →
          ∃ a b, (i, a) ∈ l :: ls ∧ (j, b) ∈ R ∧ CrossSubst.rename τ a = b)
    · obtain ⟨he, hj, hp⟩ := ih R σ hi
      refine ⟨he, hj, ?_⟩
      intro i j hij
      obtain ⟨a, b, ha, hb, ht⟩ := hp i j hij
      exact ⟨a, b, List.mem_cons_of_mem _ ha, hb, ht⟩
    · intro m hm
      rcases List.mem_cons.mp hm with hm | hm
      · subst m
        obtain ⟨he, hj, hp⟩ := ih R σ hi
        refine ⟨he, hj, ?_⟩
        intro i j hij
        obtain ⟨a, b, ha, hb, ht⟩ := hp i j hij
        exact ⟨a, b, List.mem_cons_of_mem _ ha, hb, ht⟩
      · obtain ⟨k, _, hm⟩ := List.mem_filterMap.mp hm
        simp only [Option.bind_eq_bind] at hm
        cases hr : R[k]? with
        | none => simp [hr] at hm
        | some r =>
          simp only [hr, Option.bind_some] at hm
          cases hmerge : CrossSubst.mergePred σ l.2 r.2 with
          | none => simp [hmerge] at hm
          | some τ =>
            simp only [hmerge, Option.bind_some, Option.pure_def, Option.some.injEq] at hm
            subst m
            obtain ⟨he, hj, ht⟩ := CrossSubst.mergePred_spec σ τ l.2 r.2 hi hmerge
            obtain ⟨he', hj', hp⟩ := ih (R.drop (k + 1)) τ hj
            refine ⟨CrossSubst.extends_trans he he', hj', ?_⟩
            intro i j hij
            rcases List.mem_cons.mp hij with hij | hij
            · have hij := Prod.mk.inj hij
              obtain ⟨rfl, rfl⟩ := hij
              exact ⟨l.2, r.2, by simp,
                List.mem_of_getElem? hr, ht _ he' hj'⟩
            · obtain ⟨a, b, ha, hb, ht⟩ := hp i j hij
              exact ⟨a, b, List.mem_cons_of_mem _ ha, List.mem_of_mem_drop hb, ht⟩

private theorem chooseMatch_preserves_match (P : Match → Prop)
    (candidates : List Match) (fallback : Match)
    (hu : ∀ m b, P m → P { m with ambiguous := b })
    (hf : P fallback) (hc : ∀ m ∈ candidates, P m) :
    P (chooseMatch candidates fallback) := by
  unfold chooseMatch
  dsimp only
  generalize hb : candidates.foldl (fun n m => max n m.size) 0 = best
  generalize ha : candidates.filter (fun m => m.size == best) = achievers
  cases achievers with
  | nil => exact hu fallback _ hf
  | cons m ms =>
    have hm : m ∈ candidates.filter (fun m => m.size == best) := by
      rw [ha]; exact List.mem_cons_self
    exact hu m _ (hc m (List.mem_filter.mp hm).1)

/-- Search preserves both input orders, independently of symbol consistency. -/
theorem search_structure (L R : List (Nat × CrossPred)) (σ : CrossSubst) :
    (search L R σ).size = (search L R σ).pairs.length ∧
    ((search L R σ).pairs.map Prod.fst).Sublist (L.map Prod.fst) ∧
    ((search L R σ).pairs.map Prod.snd).Sublist (R.map Prod.fst) := by
  induction L generalizing R σ with
  | nil => simp [search]
  | cons l ls ih =>
    rw [search]
    apply chooseMatch_preserves_match
      (fun m => m.size = m.pairs.length ∧
        (m.pairs.map Prod.fst).Sublist ((l :: ls).map Prod.fst) ∧
        (m.pairs.map Prod.snd).Sublist (R.map Prod.fst))
    · intro m b hm
      exact hm
    · obtain ⟨hn, hl, hr⟩ := ih R σ
      exact ⟨hn, hl.cons l.1, hr⟩
    · intro m hm
      rcases List.mem_cons.mp hm with hm | hm
      · subst m
        obtain ⟨hn, hl, hr⟩ := ih R σ
        exact ⟨hn, hl.cons l.1, hr⟩
      · obtain ⟨k, _, hm⟩ := List.mem_filterMap.mp hm
        simp only [Option.bind_eq_bind] at hm
        cases hget : R[k]? with
        | none => simp [hget] at hm
        | some r =>
          simp only [hget, Option.bind_some] at hm
          cases hmerge : CrossSubst.mergePred σ l.2 r.2 with
          | none => simp [hmerge] at hm
          | some τ =>
            simp only [hmerge, Option.bind_some, Option.pure_def, Option.some.injEq] at hm
            subst m
            obtain ⟨hn, hl, hr⟩ := ih (R.drop (k + 1)) τ
            refine ⟨by simpa using hn, hl.cons₂ l.1, ?_⟩
            have htail : (r :: R.drop (k + 1)).Sublist R := by
              obtain ⟨hk, heq⟩ := List.getElem?_eq_some_iff.mp hget
              have hd : R.drop k = r :: R.drop (k + 1) := by
                simpa only [heq] using List.drop_eq_getElem_cons hk
              rw [← hd]
              exact List.drop_sublist k R
            exact (hr.cons₂ r.1).trans (htail.map Prod.fst)

theorem search_pairs_determined (L R : List (Nat × CrossPred)) (σ : CrossSubst)
    (hi : CrossSubst.Injective σ) :
    ∀ i j, (i, j) ∈ (search L R σ).pairs →
      ∃ a b, (i, a) ∈ L ∧ (j, b) ∈ R ∧
        CrossSubst.DeterminedPred (search L R σ).subst a ∧
        CrossSubst.rename (search L R σ).subst a = b := by
  induction L generalizing R σ with
  | nil => simp [search]
  | cons l ls ih =>
    rw [search]
    apply chooseMatch_preserves
      (fun τ pairs => ∀ i j, (i, j) ∈ pairs →
        ∃ a b, (i, a) ∈ l :: ls ∧ (j, b) ∈ R ∧
          CrossSubst.DeterminedPred τ a ∧ CrossSubst.rename τ a = b)
    · intro i j hij
      obtain ⟨a, b, ha, hb, hd, ht⟩ := ih R σ hi i j hij
      exact ⟨a, b, List.mem_cons_of_mem _ ha, hb, hd, ht⟩
    · intro m hm
      rcases List.mem_cons.mp hm with hm | hm
      · subst m
        intro i j hij
        obtain ⟨a, b, ha, hb, hd, ht⟩ := ih R σ hi i j hij
        exact ⟨a, b, List.mem_cons_of_mem _ ha, hb, hd, ht⟩
      · obtain ⟨k, _, hm⟩ := List.mem_filterMap.mp hm
        simp only [Option.bind_eq_bind] at hm
        cases hr : R[k]? with
        | none => simp [hr] at hm
        | some r =>
          simp only [hr, Option.bind_some] at hm
          cases hmerge : CrossSubst.mergePred σ l.2 r.2 with
          | none => simp [hmerge] at hm
          | some τ =>
            simp only [hmerge, Option.bind_some, Option.pure_def, Option.some.injEq] at hm
            subst m
            obtain ⟨_, hj, ht⟩ := CrossSubst.mergePred_spec σ τ l.2 r.2 hi hmerge
            obtain ⟨he', hj', _⟩ := search_sound ls (R.drop (k + 1)) τ hj
            intro i j hij
            rcases List.mem_cons.mp hij with hij | hij
            · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hij
              exact ⟨l.2, r.2, by simp, List.mem_of_getElem? hr,
                CrossSubst.determinedPred_extends he' hj hj' l.2
                  (CrossSubst.mergePred_determined σ τ l.2 r.2 hi hmerge),
                ht _ he' hj'⟩
            · obtain ⟨a, b, ha, hb, hd, ht⟩ := ih (R.drop (k + 1)) τ hj i j hij
              exact ⟨a, b, List.mem_cons_of_mem _ ha, List.mem_of_mem_drop hb, hd, ht⟩

private theorem indexed_mem_iff {α : Type} (L : List α) (i : Nat) (a : α) :
    (i, a) ∈ (List.range L.length).zip L ↔ L[i]? = some a := by
  constructor
  · intro h
    obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp h
    obtain ⟨hi, ha⟩ := List.getElem?_zip_eq_some.mp hk
    have hlt : k < L.length := by
      simpa using (List.getElem?_eq_some_iff.mp hi).1
    have heq : k = i := by
      simpa [List.getElem?_range hlt] using hi
    simpa [heq] using ha
  · intro h
    apply List.mem_iff_getElem?.mpr
    refine ⟨i, List.getElem?_zip_eq_some.mpr ⟨?_, h⟩⟩
    exact List.getElem?_range (List.getElem?_eq_some_iff.mp h).1

structure UnifyOut where
  ambiguous : Bool
  subst : CrossSubst
  pairs : List (Nat × Nat)
  onlyLeft : List Nat
  onlyRight : List Nat
  deriving DecidableEq, BEq, ReflBEq, LawfulBEq, Repr

def UnifyOut.pass (out : UnifyOut) : Bool := out.onlyLeft.isEmpty && out.onlyRight.isEmpty

def unifyLists (L R : List CrossPred) : UnifyOut :=
  let m := search ((List.range L.length).zip L) ((List.range R.length).zip R) .empty
  ⟨m.ambiguous, m.subst.strip, m.pairs,
   (List.range L.length).filter (fun i => !m.pairs.any (·.1 == i)),
   (List.range R.length).filter (fun j => !m.pairs.any (·.2 == j))⟩

namespace ObservationEqProofObligations

theorem unify_pairs_sound :
  ∀ L R i j, (i, j) ∈ (unifyLists L R).pairs →
    ∃ a b, L[i]? = some a ∧ R[j]? = some b ∧
      CrossSubst.rename (unifyLists L R).subst a = b := by
  intro L R i j hij
  have hempty : CrossSubst.Injective .empty := by simp [CrossSubst.Injective, CrossSubst.empty]
  obtain ⟨_, hi, hp⟩ := search_sound
    ((List.range L.length).zip L) ((List.range R.length).zip R) .empty hempty
  obtain ⟨a, b, ha, hb, ht⟩ := hp i j hij
  exact ⟨a, b, (indexed_mem_iff L i a).mp ha, (indexed_mem_iff R j b).mp hb,
    (CrossSubst.ProofObligations.strip_rename _ a hi).trans ht⟩

theorem unify_subst_injective :
  ∀ L R, CrossSubst.Injective (unifyLists L R).subst := by
  intro L R
  apply CrossSubst.strip_injective
  exact (search_sound ((List.range L.length).zip L) ((List.range R.length).zip R)
    .empty (by simp [CrossSubst.Injective, CrossSubst.empty])).2.1

/-- The pre-strip witness covers every symbol occurring in any matched input. -/
theorem unify_alignment_witness (L R : List CrossPred) :
    ∃ σ, CrossSubst.Injective σ ∧ σ.strip = (unifyLists L R).subst ∧
      ∀ i j, (i, j) ∈ (unifyLists L R).pairs →
        ∃ a b, L[i]? = some a ∧ R[j]? = some b ∧
          CrossSubst.DeterminedPred σ a ∧ CrossSubst.rename σ a = b := by
  let σ := (search ((List.range L.length).zip L)
    ((List.range R.length).zip R) .empty).subst
  have hi : CrossSubst.Injective .empty := by
    simp [CrossSubst.Injective, CrossSubst.empty]
  refine ⟨σ, (search_sound _ _ .empty hi).2.1, rfl, ?_⟩
  intro i j hij
  obtain ⟨a, b, ha, hb, hd, ht⟩ := search_pairs_determined
    ((List.range L.length).zip L) ((List.range R.length).zip R) .empty hi i j hij
  exact ⟨a, b, (indexed_mem_iff L i a).mp ha, (indexed_mem_iff R j b).mp hb, hd, ht⟩

end ObservationEqProofObligations

/-- Identity collisions prevent a two-pair alignment with explicit input coverage. -/
theorem unify_identity_collision_ambiguous :
    let L : List CrossPred := [.ret ⟨.var 0⟩, .ret ⟨.var 1⟩]
    let R : List CrossPred := [.ret ⟨.var 1⟩, .ret ⟨.var 1⟩]
    (unifyLists L R).ambiguous = true ∧
    (unifyLists L R).pairs = [(1, 0)] ∧
    (unifyLists L R).onlyLeft = [0] ∧ (unifyLists L R).onlyRight = [1] := by
  decide +kernel

/-- Explicit-entry injectivity alone does not imply injectivity of defaulted lookup. -/
theorem unify_identity_collision_two_pair_witness :
    let σ : CrossSubst := ⟨[(0, 1)], []⟩
    CrossSubst.Injective σ ∧
    CrossSubst.rename σ (.ret ⟨.var 0⟩) = .ret ⟨.var 1⟩ ∧
    CrossSubst.rename σ (.ret ⟨.var 1⟩) = .ret ⟨.var 1⟩ := by
  simp [CrossSubst.Injective, CrossSubst.rename, CrossSubst.applyTerm,
    CrossSubst.varLookup, CrossSubst.varImage?]

/-! Strict canonical JSON parser. Every object has exactly its constructor keys;
integer strings use the decimal spelling emitted by `renderCrossPredJson`. -/

private def exactFields (j : Lean.Json) (keys : List String) : Bool :=
  match j.getObj? with
  | .error _ => false
  | .ok obj => obj.keys.all keys.contains && keys.all obj.contains

private def field (j : Lean.Json) (key : String) : Option Lean.Json :=
  (j.getObjVal? key).toOption

private def strField (j : Lean.Json) (key : String) : Option String :=
  field j key >>= fun v => v.getStr?.toOption

private def natField (j : Lean.Json) (key : String) : Option Nat :=
  field j key >>= fun v => v.getNat?.toOption

private def intField (j : Lean.Json) (key : String) : Option Int := do
  let text ← strField j key
  let z ← text.toInt?
  if toString z == text then some z else none

private def parseRegClass : Nat → Option RegKind
  | 0 => some .real | 1 => some .stack | 2 => some .map
  | 3 => some .packet | 4 => some .context | _ => none

private def parseCrossOp (name : String) (params : List Nat) : Option CrossOp :=
  match name, params with
  | "add", [] => some .add | "sub", [] => some .sub | "mullo", [] => some .mullo
  | "linear", [] => some .linear
  | "packetReg", [bytes] => if [1, 2, 4, 8].contains bytes then some (.packetReg bytes) else none
  | "packetRead", [bytes, ending] => some (.packetRead bytes ending)
  | "neg", [] => some .neg | "id", [] => some .id | "shl", [] => some .shl
  | "lshr", [] => some .lshr | "ashr", [] => some .ashr
  | "ltu", [] => some .ltu | "lts", [] => some .lts
  | "and", [] => some .and | "or", [] => some .or
  | "xor", [] => some .xor | "low", [q] => some (.low q)
  | "extract", [a,b] => some (.extract a b) | "zext", [a,b] => some (.zext a b)
  | "sext", [a,b] => some (.sext a b) | "bswap", [a,b] => some (.bswap a b)
  | "inputByte", [r] => some (.inputByte r) | "mergeLow", [a,b] => some (.mergeLow a b)
  | "udiv", [bits, zeroResult] => some (.udiv bits zeroResult)
  | "sdiv", [bits, zeroResult] => some (.sdiv bits zeroResult)
  | "urem", [bits] => some (.urem bits) | "srem", [bits] => some (.srem bits)
  | "mulh", [bits] => some (.mulh bits) | "mulhu", [bits] => some (.mulhu bits)
  | "mulhsu", [bits] => some (.mulhsu bits) | "selectEq", [bits] => some (.selectEq bits)
  | _, _ => none

/-- The Option least fixpoint follows only proper nested argument JSON.
No arbitrary depth cap or fuel bound is imposed on canonical terms. -/
private def parseCrossTermJson (j : Lean.Json) : Option CrossTerm := do
    match ← strField j "kind" with
    | "c" =>
      if !exactFields j ["kind", "value"] then none
      pure (.c (← intField j "value"))
    | "var" =>
      if !exactFields j ["kind", "name"] then none
      pure (.var (← natField j "name"))
    | "reg" =>
      if !exactFields j ["kind", "class", "alpha"] then none
      pure (.reg (← parseRegClass (← natField j "class")) (← natField j "alpha"))
    | "app" =>
      if !exactFields j ["kind", "op", "params", "args"] then none
      let params ← ((← field j "params").getArr?).toOption
      let params ← params.toList.mapM (fun v => v.getNat?.toOption)
      let op ← parseCrossOp (← strField j "op") params
      let args ← field j "args"
      match args with
      | .arr xs => pure (.app op (← xs.toList.mapM parseCrossTermJson))
      | _ => none
    | "external" =>
      if !exactFields j ["kind", "lane", "args"] then none
      let lane ← natField j "lane"
      let args ← field j "args"
      match args with
      | .arr xs => pure (.external lane (← xs.toList.mapM parseCrossTermJson))
      | _ => none
    | _ => none

partial_fixpoint

private def parseCrossTermsJson (js : List Lean.Json) : Option (List CrossTerm) :=
  js.mapM parseCrossTermJson

private def termField (j : Lean.Json) (key : String) : Option CrossTerm :=
  field j key >>= parseCrossTermJson

private def termsField (j : Lean.Json) (key : String) : Option (List CrossTerm) := do
  let xs ← ((← field j key).getArr?).toOption
  parseCrossTermsJson xs.toList

private def parseCrossRelJson (j : Lean.Json) : Option CrossRel := do
  if !exactFields j ["kind", "q"] then none
  let kind ← match ← strField j "kind" with
    | "eq" => some CrossRelKind.eq | "ne" => some .ne
    | "ltu" => some .ltu | "leu" => some .leu | "gtu" => some .gtu | "geu" => some .geu
    | "lts" => some .lts | "les" => some .les | "gts" => some .gts | "ges" => some .ges
    | "bitsnz" => some .bitsnz | "bitsz" => some .bitsz | _ => none
  pure ⟨kind, ← natField j "q"⟩

private def parseCrossCondJson (j : Lean.Json) : Option CrossCond := do
  match ← strField j "kind" with
  | "plain" =>
    if !exactFields j ["kind", "rel", "lhs", "rhs"] then none
    pure (.plain (← field j "rel" >>= parseCrossRelJson)
      (← termField j "lhs") (← termField j "rhs"))
  | "packetBound" =>
    if !exactFields j ["kind", "base", "rel", "offset"] then none
    pure (.packetBound (← termField j "base")
      (← field j "rel" >>= parseCrossRelJson) (← termField j "offset"))
  | "packetField" =>
    if !exactFields j ["kind", "field", "rel", "value"] then none
    pure (.packetField (← termField j "field")
      (← field j "rel" >>= parseCrossRelJson) (← intField j "value"))
  | _ => none

private def parseCrossValueJson (j : Lean.Json) : Option CrossValue := do
  match ← strField j "kind" with
  | "bytes" =>
    if !exactFields j ["kind", "values"] then none
    pure (.bytes (← termsField j "values"))
  | "source" =>
    if !exactFields j ["kind", "term"] then none
    pure (.source (← termField j "term"))
  | _ => none

private def parseCrossMutationJson (j : Lean.Json) : Option CrossMutation := do
  if !exactFields j ["action", "map", "key", "offset", "value"] then none
  let kind ← match ← strField j "action" with
    | "write" => some CrossMutationKind.write | "delete" => some .delete | _ => none
  pure ⟨kind, ← termField j "map", ← termsField j "key", ← natField j "offset",
    ← field j "value" >>= parseCrossValueJson⟩

private def parseCrossHelperJson (j : Lean.Json) : Option CrossHelper := do
  match ← strField j "kind" with
  | "lookup" =>
    if !exactFields j ["kind", "map", "key"] then none
    pure (.lookup (← termField j "map") (← termsField j "key"))
  | "mutation" =>
    if !exactFields j ["kind", "mutation"] then none
    pure (.mutation (← field j "mutation" >>= parseCrossMutationJson))
  | "other" =>
    if !exactFields j ["kind", "helperId", "args"] then none
    pure (.other (← natField j "helperId") (← termsField j "args"))
  | _ => none

def parseCrossPredJson (j : Lean.Json) : Option CrossPred := do
  match ← strField j "kind" with
  | "helper" =>
    if !exactFields j ["kind", "observation"] then none
    pure (.helper (← field j "observation" >>= parseCrossHelperJson))
  | "branch" =>
    if !exactFields j ["kind", "dir", "cond"] then none
    let dir ← match ← strField j "dir" with
      | "taken" => some BranchDirection.taken | "notTaken" => some .notTaken | _ => none
    pure (.branch ⟨dir, ← field j "cond" >>= parseCrossCondJson⟩)
  | "ret" =>
    if !exactFields j ["kind", "payload"] then none
    pure (.ret ⟨← termField j "payload"⟩)
  | "mapWrite" =>
    if !exactFields j ["kind", "mutation"] then none
    pure (.mapWrite (← field j "mutation" >>= parseCrossMutationJson))
  | "packetWrite" =>
    let symbolic := (field j "offsetTerm").isSome
    let fields := ["kind", "packet", if symbolic then "offsetTerm" else "offset", "value"]
    if !exactFields j fields then none
    let offset ← if symbolic then termField j "offsetTerm"
      else do pure (.c (← natField j "offset"))
    pure (.packetWrite ⟨← natField j "packet", offset,
      ← field j "value" >>= parseCrossValueJson⟩)
  | _ => none

private def regClass : RegKind → Nat
  | .real => 0 | .stack => 1 | .map => 2 | .packet => 3 | .context => 4

private def renderNats (ns : List Nat) : String :=
  "[" ++ String.intercalate "," (ns.map toString) ++ "]"

private def renderCrossSubst (σ : CrossSubst) : String :=
  let vars := σ.vars.mergeSort (fun a b =>
    a.1 < b.1 || (a.1 == b.1 && a.2 ≤ b.2))
  let regs := (σ.regs.map (fun (k,a,b) => (regClass k,a,b))).mergeSort
    (fun a b => a.1 < b.1 || (a.1 == b.1 &&
      (a.2.1 < b.2.1 || (a.2.1 == b.2.1 && a.2.2 ≤ b.2.2))))
  let vs := String.intercalate "," (vars.map fun (a,b) => renderNats [a,b])
  let rs := String.intercalate "," (regs.map fun (k,a,b) => renderNats [k,a,b])
  s!"\{\"vars\":[{vs}],\"regs\":[{rs}]}"

private def renderUnifyOut (out : UnifyOut) : String :=
  if out.ambiguous then "{\"ok\":false}" else
  let pairs := String.intercalate "," (out.pairs.map fun (i,j) =>
    s!"\{\"left\":{i},\"right\":{j}}")
  s!"\{\"ok\":true,\"pass\":{out.pass},\"pairs\":[{pairs}],\"onlyLeft\":{renderNats out.onlyLeft},\"onlyRight\":{renderNats out.onlyRight},\"subst\":{renderCrossSubst out.subst}}"

/-- Boxed Lean String ABI. Bad canonical JSON and lists longer than 32 return
`null`; multiple maximum matchings return exactly `{"ok":false}`. -/
@[export lean_cross_pred_unify]
def exportCrossPredUnify (requestJson : String) : String :=
  let result : Option String := do
    let j ← (Lean.Json.parse requestJson).toOption
    if !exactFields j ["left", "right"] then none
    let left ← ((← field j "left").getArr?).toOption
    let right ← ((← field j "right").getArr?).toOption
    if left.size > 32 || right.size > 32 then none
    let L ← left.toList.mapM parseCrossPredJson
    let R ← right.toList.mapM parseCrossPredJson
    pure (renderUnifyOut (unifyLists L R))
  result.getD "null"

/-! Canonical JSON fixtures. These checks exercise the ABI and all nested tags;
they are finite regression evidence, not proofs of search completeness. -/

private def fixture (wire : String) : Option CrossPred :=
  (Lean.Json.parse wire).toOption >>= parseCrossPredJson

private def request (L R : List String) : String :=
  s!"\{\"left\":[{String.intercalate "," L}],\"right\":[{String.intercalate "," R}]}"

private def var4 : String := "{\"kind\":\"ret\",\"payload\":{\"kind\":\"var\",\"name\":4}}"
private def var9 : String := "{\"kind\":\"ret\",\"payload\":{\"kind\":\"var\",\"name\":9}}"
private def real2 : String := "{\"kind\":\"ret\",\"payload\":{\"kind\":\"reg\",\"class\":0,\"alpha\":2}}"
private def real5 : String := "{\"kind\":\"ret\",\"payload\":{\"kind\":\"reg\",\"class\":0,\"alpha\":5}}"
private def stack2 : String := "{\"kind\":\"ret\",\"payload\":{\"kind\":\"reg\",\"class\":1,\"alpha\":2}}"
private def const1 : String := "{\"kind\":\"ret\",\"payload\":{\"kind\":\"c\",\"value\":\"1\"}}"
private def const2 : String := "{\"kind\":\"ret\",\"payload\":{\"kind\":\"c\",\"value\":\"2\"}}"
private def appAdd : String := "{\"kind\":\"ret\",\"payload\":{\"kind\":\"app\",\"op\":\"add\",\"params\":[],\"args\":[]}}"
private def appSub : String := "{\"kind\":\"ret\",\"payload\":{\"kind\":\"app\",\"op\":\"sub\",\"params\":[],\"args\":[]}}"

private def helperFixture : String :=
  "{\"kind\":\"helper\",\"observation\":{\"kind\":\"lookup\",\"map\":{\"kind\":\"reg\",\"class\":2,\"alpha\":7},\"key\":[{\"kind\":\"var\",\"name\":4}]}}"
private def branchFixture : String :=
  "{\"kind\":\"branch\",\"dir\":\"taken\",\"cond\":{\"kind\":\"packetBound\",\"base\":{\"kind\":\"reg\",\"class\":3,\"alpha\":0},\"rel\":{\"kind\":\"ltu\",\"q\":32},\"offset\":{\"kind\":\"external\",\"lane\":2,\"args\":[{\"kind\":\"var\",\"name\":4}]}}}"
private def mapFixture : String :=
  "{\"kind\":\"mapWrite\",\"mutation\":{\"action\":\"write\",\"map\":{\"kind\":\"reg\",\"class\":2,\"alpha\":7},\"key\":[{\"kind\":\"c\",\"value\":\"-1\"}],\"offset\":2,\"value\":{\"kind\":\"bytes\",\"values\":[{\"kind\":\"var\",\"name\":4}]}}}"
private def packetFixture : String :=
  "{\"kind\":\"packetWrite\",\"packet\":3,\"offset\":8,\"value\":{\"kind\":\"source\",\"term\":{\"kind\":\"app\",\"op\":\"extract\",\"params\":[8,8],\"args\":[{\"kind\":\"var\",\"name\":4}]}}}"
private def allKinds : List String :=
  [helperFixture, branchFixture, var4, mapFixture, packetFixture]

-- 1. Identical non-trivial lists, with all five observation kinds.
#guard exportCrossPredUnify (request allKinds allKinds) ==
  "{\"ok\":true,\"pass\":true,\"pairs\":[{\"left\":0,\"right\":0},{\"left\":1,\"right\":1},{\"left\":2,\"right\":2},{\"left\":3,\"right\":3},{\"left\":4,\"right\":4}],\"onlyLeft\":[],\"onlyRight\":[],\"subst\":{\"vars\":[],\"regs\":[]}}"

-- 2. Both renameable namespaces; response bytes and key order are frozen.
#guard exportCrossPredUnify (request [var4, real2] [var9, real5]) ==
  "{\"ok\":true,\"pass\":true,\"pairs\":[{\"left\":0,\"right\":0},{\"left\":1,\"right\":1}],\"onlyLeft\":[],\"onlyRight\":[],\"subst\":{\"vars\":[[4,9]],\"regs\":[[0,2,5]]}}"

-- 3. Register kinds are rigid.
#guard exportCrossPredUnify (request [real2] [stack2]) ==
  "{\"ok\":true,\"pass\":false,\"pairs\":[],\"onlyLeft\":[0],\"onlyRight\":[0],\"subst\":{\"vars\":[],\"regs\":[]}}"

-- 4. Operators and their Nat parameters are rigid.
#guard exportCrossPredUnify (request [appAdd] [appSub]) ==
  "{\"ok\":true,\"pass\":false,\"pairs\":[],\"onlyLeft\":[0],\"onlyRight\":[0],\"subst\":{\"vars\":[],\"regs\":[]}}"
#guard fixture packetFixture >>= (fun p => match p with
    | .packetWrite w => some (CrossSubst.empty.mergePred p
        (.packetWrite { w with value := .source (.app (.extract 0 8) [.var 4]) }))
    | _ => none) == some none

-- 5. The two increasing size-one maxima are distinct alignments.
#guard exportCrossPredUnify (request [const1, const2] [const2, const1]) == "{\"ok\":false}"

-- 6. The cap is checked before search; 32 is allowed and 33 is rejected.
#guard exportCrossPredUnify (request (List.replicate 33 const1) []) == "null"
#guard exportCrossPredUnify (request (List.replicate 32 const1) []) != "null"
#guard exportCrossPredUnify (request [] (List.replicate 33 const1)) == "null"

-- 7. Missing keys, noncanonical values, extra keys and wrong containers reject.
#guard exportCrossPredUnify "{\"left\":[]}" == "null"
#guard exportCrossPredUnify (request ["{\"kind\":\"ret\",\"payload\":{\"kind\":\"var\",\"name\":4,\"extra\":0}}"] []) == "null"
#guard exportCrossPredUnify (request ["{\"kind\":\"ret\",\"payload\":{\"kind\":\"c\",\"value\":\"01\"}}"] []) == "null"
#guard exportCrossPredUnify "{\"left\":[],\"right\":[],\"extra\":0}" == "null"
#guard exportCrossPredUnify "{\"left\":{},\"right\":[]}" == "null"
#guard exportCrossPredUnify "[]" == "null"
#guard exportCrossPredUnify (request ["{\"kind\":\"ret\",\"payload\":{\"kind\":\"app\",\"op\":\"add\",\"params\":[32],\"args\":[]}}"] []) == "null"

-- 8. Repeated predicates have one full increasing alignment, not two paths.
#guard exportCrossPredUnify (request [var4, var4] [var4, var4]) ==
  "{\"ok\":true,\"pass\":true,\"pairs\":[{\"left\":0,\"right\":0},{\"left\":1,\"right\":1}],\"onlyLeft\":[],\"onlyRight\":[],\"subst\":{\"vars\":[],\"regs\":[]}}"

-- 9. Mirror substitution and unequal leftovers.
#guard exportCrossPredUnify (request [const1, var4, real2] [var9, real5]) ==
  "{\"ok\":true,\"pass\":false,\"pairs\":[{\"left\":1,\"right\":0},{\"left\":2,\"right\":1}],\"onlyLeft\":[0],\"onlyRight\":[],\"subst\":{\"vars\":[[4,9]],\"regs\":[[0,2,5]]}}"
#guard exportCrossPredUnify (request [var9, real5] [const1, var4, real2]) ==
  "{\"ok\":true,\"pass\":false,\"pairs\":[{\"left\":0,\"right\":1},{\"left\":1,\"right\":2}],\"onlyLeft\":[],\"onlyRight\":[0],\"subst\":{\"vars\":[[9,4]],\"regs\":[[0,5,2]]}}"

-- 10. Round-trip each of the five outer kinds through its canonical renderer.
#guard allKinds.all fun wire => match fixture wire with
  | none => false
  | some p => fixture (renderCrossPredJson p) == some p

-- Every nested helper/condition/value tag also accepts its canonical shape.
private def nestedFixtures : List String :=
  ["{\"kind\":\"helper\",\"observation\":{\"kind\":\"mutation\",\"mutation\":{\"action\":\"delete\",\"map\":{\"kind\":\"reg\",\"class\":2,\"alpha\":7},\"key\":[],\"offset\":0,\"value\":{\"kind\":\"bytes\",\"values\":[]}}}}",
   "{\"kind\":\"helper\",\"observation\":{\"kind\":\"other\",\"helperId\":99,\"args\":[{\"kind\":\"reg\",\"class\":4,\"alpha\":0}]}}",
   "{\"kind\":\"branch\",\"dir\":\"notTaken\",\"cond\":{\"kind\":\"plain\",\"rel\":{\"kind\":\"bitsnz\",\"q\":64},\"lhs\":{\"kind\":\"var\",\"name\":4},\"rhs\":{\"kind\":\"c\",\"value\":\"-2\"}}}",
   "{\"kind\":\"branch\",\"dir\":\"taken\",\"cond\":{\"kind\":\"packetField\",\"field\":{\"kind\":\"reg\",\"class\":1,\"alpha\":2},\"rel\":{\"kind\":\"eq\",\"q\":8},\"value\":\"0\"}}"]

#guard nestedFixtures.all fun wire => match fixture wire with
  | none => false
  | some p => fixture (renderCrossPredJson p) == some p

private def opFixtures : List CrossOp :=
  [.add, .sub, .mullo, .neg, .id, .shl, .lshr, .ashr, .ltu, .lts,
   .and, .or, .xor, .low 16, .extract 8 16, .zext 64 32,
   .sext 64 32, .bswap 32 32, .inputByte 3, .mergeLow 32 8,
   .udiv 32 0, .udiv 32 4294967295, .sdiv 64 18446744073709551615,
   .urem 32, .srem 64, .mulh 32, .mulhu 64, .mulhsu 32, .selectEq 64]
#guard opFixtures.all fun op =>
  let p := CrossPred.ret ⟨.app op [.var 4]⟩
  fixture (renderCrossPredJson p) == some p

-- Direct top-level self check, on parsed canonical observations.
#guard (do
    let ps ← allKinds.mapM fixture
    let out := unifyLists ps ps
    pure (out.pass && !out.ambiguous && out.subst == CrossSubst.empty &&
      out.onlyLeft.isEmpty && out.onlyRight.isEmpty)) == some true

#guard (do
    let p ← fixture var4
    let out := unifyLists [p,p] [p,p]
    pure (out.pass && !out.ambiguous)) == some true

-- Identity bindings stay pinned internally and are removed only for reporting.
#guard CrossSubst.empty.addVar? 4 4 == some ⟨[(4,4)], []⟩
#guard (CrossSubst.empty.addVar? 4 4 >>= fun σ => σ.addVar? 4 9) == none
#guard (CrossSubst.empty.addVar? 4 4 >>= fun σ => σ.addVar? 9 4) == none
#guard CrossSubst.empty.addReg? .real 2 2 == some ⟨[], [(.real,2,2)]⟩
#guard (CrossSubst.empty.addReg? .real 2 2 >>= fun σ => σ.addReg? .real 2 5) == none
#guard (CrossSubst.empty.addReg? .real 2 2 >>= fun σ => σ.addReg? .stack 3 2) ==
  some ⟨[], [(.stack,3,2),(.real,2,2)]⟩
#guard renderCrossSubst (CrossSubst.strip
    ⟨[(9,3),(4,8),(2,2)], [(.map,8,3),(.real,9,4),(.real,2,5)]⟩) ==
  "{\"vars\":[[4,8],[9,3]],\"regs\":[[0,2,5],[0,9,4],[2,8,3]]}"

-- The measured source wires exercise normalization and the canonical parser together.
private def liveEnvR : String :=
  "{\"packetBase\":\"v32:4\",\"packetEnd\":\"add32(v32:4,v32:5)\"}"
private def liveEnvE : String :=
  "{\"packetBase\":\"v32:4\",\"packetEnd\":\"add32(v32:4,128)\"}"
private def liveEthertypeR : String :=
  "{\"kind\":\"branch\",\"position\":25,\"dir\":\"taken\",\"width\":32,\"cond\":{\"lhs\":\"or32(or32(0,shl32(zext8/32(low8(inputByte0(v32:4,add32(v32:4,16)))),0)),shl32(zext8/32(low8(inputByte0(v32:4,add32(v32:4,17)))),8))\",\"rel\":\"eq\",\"rhs\":\"56710\"}}"
private def liveEthertypeE : String :=
  "{\"kind\":\"branch\",\"position\":17,\"dir\":\"taken\",\"width\":64,\"cond\":{\"lhs\":\"or64(or64(0,shl64(zext8/64/32(low8(inputByte0(v32:4,add32(v32:4,16)))),0)),shl64(zext8/64/32(low8(inputByte0(v32:4,add32(v32:4,17)))),8))\",\"rel\":\"eqN32\",\"rhs\":\"56710\"}}"
private def liveLookupNullR : String :=
  "{\"kind\":\"branch\",\"position\":48,\"dir\":\"taken\",\"width\":32,\"cond\":{\"lhs\":\"id32(externalResult489_0(1,1077412584,id32(add32(v32:0,4294967280))))\",\"rel\":\"eq\",\"rhs\":\"0\"}}"
private def liveLookupNullE : String :=
  "{\"kind\":\"branch\",\"position\":38,\"dir\":\"taken\",\"width\":64,\"cond\":{\"lhs\":\"externalResult85_0(1,1077412584,id64(add64(id64(v64:0),18446744073709551612)))\",\"rel\":\"eq\",\"rhs\":\"0\"}}"

private def liveUnifyPass (r e : String) : Bool :=
  exportCrossPredUnify (request
    [exportCrossPredNormalize liveEnvR r] [exportCrossPredNormalize liveEnvE e]) ==
    "{\"ok\":true,\"pass\":true,\"pairs\":[{\"left\":0,\"right\":0}],\"onlyLeft\":[],\"onlyRight\":[],\"subst\":{\"vars\":[],\"regs\":[]}}"
private def liveEthertypeUnify : Bool := liveUnifyPass liveEthertypeR liveEthertypeE
private def liveLookupNullUnify : Bool := liveUnifyPass liveLookupNullR liveLookupNullE
#guard liveEthertypeUnify
#guard liveLookupNullUnify

private def bitwiseParamsReject : Bool :=
  ["and", "or", "xor"].all fun name =>
    exportCrossPredUnify (request
      [s!"\{\"kind\":\"ret\",\"payload\":\{\"kind\":\"app\",\"op\":\"{name}\",\"params\":[32],\"args\":[]}}"] []) == "null"
#guard bitwiseParamsReject

namespace MapWriteCarryFixtures

private def sameNormalized (r e : String) : Bool :=
  let result : Option Bool := do
    let left ← fixture (exportCrossPredNormalize envR r)
    let right ← fixture (exportCrossPredNormalize envE e)
    let r := renderCrossPredJson (CrossSubst.rename ⟨[], [(.real,10,0)]⟩ left)
    let e := renderCrossPredJson right
    pure (r != "null" && e != "null" && r == e)
  result.getD false

private def liveNode26MapWritesNormalize : Bool :=
  sameNormalized node26LowR node26LowE && sameNormalized node26HighR node26HighE
private def liveNode34MapWritesNormalize : Bool :=
  sameNormalized node34LowR node34LowE && sameNormalized node34HighR node34HighE
#guard liveNode26MapWritesNormalize
#guard liveNode34MapWritesNormalize

private def liveMapWriteUnify (rs es : List String) : Bool :=
  let r := rs.map (exportCrossPredNormalize envR)
  let e := es.map (exportCrossPredNormalize envE)
  let result : Option Bool := do
    let left ← r.mapM fixture
    let right ← e.mapM fixture
    let out := unifyLists left right
    let renamed := left.map (fun p =>
      renderCrossPredJson (CrossSubst.rename out.subst p))
    pure (out.pass && !out.ambiguous && out.onlyLeft.isEmpty && out.onlyRight.isEmpty &&
      out.pairs == [(0,0),(1,1),(2,2)] &&
      out.subst.strip == ⟨[], [(.real,10,0)]⟩ && renamed == e)
  r.all (· != "null") && e.all (· != "null") && result.getD false &&
    exportCrossPredUnify (request r e) ==
      "{\"ok\":true,\"pass\":true,\"pairs\":[{\"left\":0,\"right\":0},{\"left\":1,\"right\":1},{\"left\":2,\"right\":2}],\"onlyLeft\":[],\"onlyRight\":[],\"subst\":{\"vars\":[],\"regs\":[[0,10,0]]}}"

private def liveNode26MapWriteUnify : Bool := liveMapWriteUnify node26PredsR node26PredsE
private def liveNode34MapWriteUnify : Bool := liveMapWriteUnify node34PredsR node34PredsE
#guard liveNode26MapWriteUnify
#guard liveNode34MapWriteUnify

end MapWriteCarryFixtures

end ClassifierExpr
