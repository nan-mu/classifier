import Core.Semantics

namespace Core

namespace SolvePreservation

private def value (ν : Var → Nat) (θ : ExternalInterpretation) (t : Term) : Nat :=
  (interpretTerm ν θ t).getD 0

private theorem meaning (ν : Var → Nat) (θ : ExternalInterpretation)
    (hθ : θ.Total) (t : Term) (ht : t.wellFormed = true) :
    interpretTerm ν θ t = some (value ν θ t) := by
  obtain ⟨v, hv⟩ := interpretTerm_total ν θ hθ t ht
  simp [value, hv]

private theorem value_lt (ν : Var → Nat) (θ : ExternalInterpretation)
    (t : Term) : value ν θ t < 2 ^ t.width.bits := by
  cases t with
  | const w c =>
    by_cases hc : c < 2 ^ w.bits
    · simp [value, interpretTerm, hc, Term.width]
    · simpa [value, interpretTerm, hc, Term.width] using Nat.two_pow_pos w.bits
  | var w n => simpa [value, interpretTerm, Term.width] using MNat_lt w.bits _
  | regVar event r =>
    by_cases hr : (r.valid && r.kind == .real) = true
    · simpa [value, interpretTerm, hr, Term.width] using MNat_lt r.width.bits _
    · simpa [value, interpretTerm, hr, Term.width] using Nat.two_pow_pos r.width.bits
  | app w op args =>
    cases hs : op.validSignature w (args.map Term.width) with
    | false =>
      simpa [value, interpretTerm, hs, Term.width] using Nat.two_pow_pos w.bits
    | true =>
      cases hv : interpretTerms ν θ args with
      | none =>
        simpa [value, interpretTerm, hs, hv, Term.width] using Nat.two_pow_pos w.bits
      | some vs =>
        cases ho : interpretWith θ w op vs with
        | none =>
          simpa [value, interpretTerm, hs, hv, ho, Term.width] using Nat.two_pow_pos w.bits
        | some v =>
          simpa [value, interpretTerm, hs, hv, ho, Term.width] using MNat_lt w.bits v

@[simp] private theorem value_mod (ν : Var → Nat) (θ : ExternalInterpretation)
    (w : Width) (t : Term) (hw : t.width = w) :
    MNat w.bits (value ν θ t) = value ν θ t := by
  apply MNat_of_lt
  simpa [hw] using value_lt ν θ t

@[simp] private theorem value_mod_pow (ν : Var → Nat) (θ : ExternalInterpretation)
    (w : Width) (t : Term) (hw : t.width = w) :
    value ν θ t % 2 ^ w.bits = value ν θ t := by
  apply Nat.mod_eq_of_lt
  simpa [hw] using value_lt ν θ t

@[simp] private theorem value_const (ν : Var → Nat) (θ : ExternalInterpretation)
    (w : Width) (c : Nat) (hc : c < 2 ^ w.bits) :
    value ν θ (.const w c) = c := by
  simp [value, interpretTerm, hc]

private theorem value_zero (ν : Var → Nat) (θ : ExternalInterpretation) (t : Term)
    (h : (match t with | .const _ 0 => true | _ => false) = true) :
    value ν θ t = 0 := by
  cases t with
  | const w c =>
    cases c <;> simp_all [value, interpretTerm, Nat.two_pow_pos]
  | var => contradiction
  | regVar => contradiction
  | app => contradiction

private theorem value_one (ν : Var → Nat) (θ : ExternalInterpretation) (t : Term)
    (h : (match t with | .const _ 1 => true | _ => false) = true) :
    value ν θ t = 1 := by
  cases t with
  | const w c =>
    cases c with
    | zero => contradiction
    | succ c =>
      cases c with
      | zero => exact value_const ν θ w 1 (by cases w <;> decide)
      | succ c => contradiction
  | var => contradiction
  | regVar => contradiction
  | app => contradiction

private theorem value_binary (ν : Var → Nat) (θ : ExternalInterpretation)
    (hθ : θ.Total) (w : Width) (op : Op) (a b : Term)
    (ht : (Term.app w op [a, b]).wellFormed = true) :
    value ν θ (.app w op [a, b]) =
      ((interpretWith θ w op [value ν θ a, value ν θ b]).map (MNat w.bits)).getD 0 := by
  have hvalid : op.validSignature w ([a, b].map Term.width) = true ∧
      termsWellFormed [a, b] = true := by
    simpa only [Term.wellFormed, Bool.and_eq_true] using ht
  obtain ⟨hs, ha⟩ := hvalid
  have ha' : a.wellFormed = true ∧ b.wellFormed = true := by
    simpa [termsWellFormed] using ha
  change (interpretTerm ν θ (.app w op [a, b])).getD 0 = _
  rw [interpretTerm]
  simp only [hs, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
    interpretTerms, meaning ν θ hθ a ha'.1, meaning ν θ hθ b ha'.2,
    Option.bind_eq_bind, Option.bind_some, Option.pure_def]
  cases ho : interpretWith θ w op [value ν θ a, value ν θ b] <;> simp_all

/-- Every retained atom has the original carrier and remains structurally valid. -/
theorem additiveSpine_atoms_valid (w : Width) (t : Term)
    (ht : t.wellFormed = true) (hw : t.width = w) :
    ∀ a ∈ (additiveSpine w t).1, a.wellFormed = true ∧ a.width = w := by
  revert ht hw
  fun_induction additiveSpine w t <;>
    simp_all +zetaDelta [Term.wellFormed, termsWellFormed,
      Op.validSignature, Term.width, List.mem_append]
  case case2 wo wi lhs rhs x y ihl ihr =>
    intro hwi hl hr hfl hfr hw atom hm
    rcases hm with hm | hm
    · exact ihl hfl (hl.trans hw) atom hm
    · exact ihr hfr (hr.trans hw) atom hm
  all_goals
    intros
    simp_all

/-- The spine denotes its atom sum plus its constant, reduced at the original width. -/
private theorem additiveSpine_value (ν : Var → Nat) (θ : ExternalInterpretation)
    (hθ : θ.Total) (w : Width) (t : Term)
    (ht : t.wellFormed = true) (hw : t.width = w) :
    value ν θ t = MNat w.bits
      (((additiveSpine w t).1.map (value ν θ)).sum + (additiveSpine w t).2) := by
  revert ht hw
  fun_induction additiveSpine w t
  all_goals intro ht hw
  case case1 wc c =>
    have hc : c < 2 ^ wc.bits := by
      simpa only [Term.wellFormed, decide_eq_true_eq] using ht
    have hw' : wc = w := hw
    rw [hw'] at hc ⊢
    simp only [List.map_nil, List.sum_nil, Nat.zero_add]
    rw [value_const ν θ w c hc, MNat_of_lt hc]
  case case2 wo wi a b x y iha ihb =>
    have hbinary := value_binary ν θ hθ wo (.add wi) a b ht
    have hf : wo = wi ∧ a.width = wo ∧ b.width = wo ∧
        a.wellFormed = true ∧ b.wellFormed = true := by
      simpa [Term.wellFormed, termsWellFormed, Op.validSignature, and_assoc] using ht
    obtain ⟨hwi, hwa, hwb, ha, hb⟩ := hf
    have hw' : wo = w := hw
    rw [hw'] at hwi hwa hwb hbinary ⊢
    rw [← hwi] at hbinary ⊢
    rw [hbinary]
    simp only [interpretWith, interpretOp, Option.map_some, Option.getD_some,
      ADD, MNat_idempotent]
    rw [iha ha hwa, ihb hb hwb]
    dsimp [x, y]
    simp only [MNat, Nat.mod_add_mod, Nat.add_mod_mod]
    simp [List.sum_append, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  case case3 wo wi a b heq =>
    have hbinary := value_binary ν θ hθ wo (.sub wi) a b ht
    have hab : a = b := eq_of_beq heq
    subst b
    simpa [interpretWith, interpretOp, MNat] using hbinary
  case case4 wo wi a wc c x hne ih =>
    have hbinary := value_binary ν θ hθ wo (.sub wi) a (.const wc c) ht
    have hf : wo = wi ∧ a.width = wo ∧ wc = wo ∧
        a.wellFormed = true ∧ c < 2 ^ wc.bits := by
      simpa [Term.wellFormed, termsWellFormed, Op.validSignature,
        Term.width, and_assoc] using ht
    obtain ⟨hwi, hwa, hwc, ha, hc⟩ := hf
    have hw' : wo = w := hw
    rw [hw'] at hwi hwa hwc hbinary ⊢
    rw [← hwi, hwc] at hbinary ⊢
    rw [hwc] at hc
    rw [hbinary]
    simp only [interpretWith, interpretOp, Option.map_some, Option.getD_some,
      value_const ν θ w c hc, SUB_eq_ADD_NEG, ADD, MNat_idempotent]
    rw [ih ha hwa]
    simp [x, MNat, Nat.add_assoc]
  case case6 wo q a b heq =>
    have hbinary := value_binary ν θ hθ wo (.xor q) a b ht
    have hab : a = b := eq_of_beq heq
    subst b
    simpa [interpretWith, interpretOp, MNat] using hbinary
  case case7 wo q a b hne hguard ih =>
    have hbinary := value_binary ν θ hθ wo (.xor q) a b ht
    have hf : 0 < q ∧ q ≤ wo.bits ∧ a.width = wo ∧ b.width = wo ∧
        a.wellFormed = true ∧ b.wellFormed = true := by
      simpa [Term.wellFormed, termsWellFormed, Op.validSignature, and_assoc] using ht
    obtain ⟨_, _, hwa, _, ha, _⟩ := hf
    have hw' : wo = w := hw
    rw [hw'] at hwa hbinary ⊢
    simp only [Bool.and_eq_true, beq_iff_eq] at hguard
    have hz := value_zero ν θ b hguard.2
    rw [hbinary]
    simp only [interpretWith, interpretOp, Option.map_some, Option.getD_some]
    rw [hz, hguard.1, XOR_zero, MNat_idempotent, value_mod ν θ w a hwa]
    exact ih ha hwa
  case case9 wo q a b hguard ih =>
    have hbinary := value_binary ν θ hθ wo (.or q) a b ht
    have hf : 0 < q ∧ q ≤ wo.bits ∧ a.width = wo ∧ b.width = wo ∧
        a.wellFormed = true ∧ b.wellFormed = true := by
      simpa [Term.wellFormed, termsWellFormed, Op.validSignature, and_assoc] using ht
    obtain ⟨_, _, hwa, _, ha, _⟩ := hf
    have hw' : wo = w := hw
    rw [hw'] at hwa hbinary ⊢
    simp only [Bool.and_eq_true, beq_iff_eq] at hguard
    have hz := value_zero ν θ b hguard.2
    rw [hbinary]
    simp only [interpretWith, interpretOp, Option.map_some, Option.getD_some]
    rw [hz, hguard.1, OR_zero, MNat_idempotent, value_mod ν θ w a hwa]
    exact ih ha hwa
  case case11 wo q a wc c hguard ih =>
    have hbinary := value_binary ν θ hθ wo (.and q) a (.const wc c) ht
    have hf : 0 < q ∧ q ≤ wo.bits ∧ a.width = wo ∧ wc = wo ∧
        a.wellFormed = true ∧ c < 2 ^ wc.bits := by
      simpa [Term.wellFormed, termsWellFormed, Op.validSignature,
        Term.width, and_assoc] using ht
    obtain ⟨_, _, hwa, _, ha, hc⟩ := hf
    have hw' : wo = w := hw
    rw [hw'] at hwa hbinary ⊢
    simp only [Bool.and_eq_true, beq_iff_eq] at hguard
    rw [hbinary]
    simp only [interpretWith, interpretOp, Option.map_some, Option.getD_some]
    rw [value_const ν θ wc c hc, hguard.1, hguard.2, AND_mask,
      MNat_idempotent, value_mod ν θ w a hwa]
    exact ih ha hwa
  case case13 wo wi a b hguard ih =>
    have hbinary := value_binary ν θ hθ wo (.mullo wi) a b ht
    have hf : wo = wi ∧ a.width = wo ∧ b.width = wo ∧
        a.wellFormed = true ∧ b.wellFormed = true := by
      simpa [Term.wellFormed, termsWellFormed, Op.validSignature, and_assoc] using ht
    obtain ⟨hwi, hwa, _, ha, _⟩ := hf
    have hw' : wo = w := hw
    rw [hw'] at hwi hwa hbinary ⊢
    rw [← hwi] at hbinary ⊢
    have ho := value_one ν θ b hguard
    rw [hbinary]
    simp only [interpretWith, interpretOp, Option.map_some, Option.getD_some]
    rw [ho, MULLO_one, MNat_idempotent, value_mod ν θ w a hwa]
    exact ih ha hwa
  case case15 wo wi a b hguard ih =>
    have hbinary := value_binary ν θ hθ wo (.shl wi) a b ht
    have hf : wo = wi ∧ a.width = wo ∧ b.width = wo ∧
        a.wellFormed = true ∧ b.wellFormed = true := by
      simpa [Term.wellFormed, termsWellFormed, Op.validSignature, and_assoc] using ht
    obtain ⟨hwi, hwa, _, ha, _⟩ := hf
    have hw' : wo = w := hw
    rw [hw'] at hwi hwa hbinary ⊢
    rw [← hwi] at hbinary ⊢
    have hz := value_zero ν θ b hguard
    rw [hbinary]
    simp only [interpretWith, interpretOp, Option.map_some, Option.getD_some]
    rw [hz, SHL_zero_shift, MNat_idempotent, value_mod ν θ w a hwa]
    exact ih ha hwa
  case case17 wo wi a b hguard ih =>
    have hbinary := value_binary ν θ hθ wo (.lshr wi) a b ht
    have hf : wo = wi ∧ a.width = wo ∧ b.width = wo ∧
        a.wellFormed = true ∧ b.wellFormed = true := by
      simpa [Term.wellFormed, termsWellFormed, Op.validSignature, and_assoc] using ht
    obtain ⟨hwi, hwa, _, ha, _⟩ := hf
    have hw' : wo = w := hw
    rw [hw'] at hwi hwa hbinary ⊢
    rw [← hwi] at hbinary ⊢
    have hz := value_zero ν θ b hguard
    rw [hbinary]
    simp only [interpretWith, interpretOp, Option.map_some, Option.getD_some]
    rw [hz, LSHR_zero_shift, MNat_idempotent, value_mod ν θ w a hwa]
    exact ih ha hwa
  case case19 wo wi a b hguard ih =>
    have hbinary := value_binary ν θ hθ wo (.ashr wi) a b ht
    have hf : wo = wi ∧ a.width = wo ∧ b.width = wo ∧
        a.wellFormed = true ∧ b.wellFormed = true := by
      simpa [Term.wellFormed, termsWellFormed, Op.validSignature, and_assoc] using ht
    obtain ⟨hwi, hwa, _, ha, _⟩ := hf
    have hw' : wo = w := hw
    rw [hw'] at hwi hwa hbinary ⊢
    rw [← hwi] at hbinary ⊢
    have hz := value_zero ν θ b hguard
    rw [hbinary]
    simp only [interpretWith, interpretOp, Option.map_some, Option.getD_some]
    rw [hz, ASHR_zero_shift, MNat_idempotent, value_mod ν θ w a hwa]
    exact ih ha hwa
  all_goals
    simpa only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Nat.add_zero] using (value_mod ν θ w _ hw).symm

private theorem add_valid (w : Width) (a b : Term)
    (ha : a.wellFormed = true) (hb : b.wellFormed = true)
    (hwa : a.width = w) (hwb : b.width = w) :
    (Term.app w (.add w) [a, b]).wellFormed = true := by
  simp [Term.wellFormed, termsWellFormed, Op.validSignature, ha, hb, hwa, hwb]

private theorem foldl_value (ν : Var → Nat) (θ : ExternalInterpretation)
    (hθ : θ.Total) (w : Width) (atoms : List Term) (acc : Term)
    (hc : acc.wellFormed = true) (hw : acc.width = w)
    (ha : ∀ a ∈ atoms, a.wellFormed = true ∧ a.width = w) :
    let result := atoms.foldl (fun lhs rhs => Term.app w (.add w) [lhs, rhs]) acc
    result.wellFormed = true ∧ result.width = w ∧
      value ν θ result = MNat w.bits (value ν θ acc + (atoms.map (value ν θ)).sum) := by
  induction atoms generalizing acc with
  | nil => simp [hc, hw]
  | cons a atoms ih =>
    have hh := ha a (by simp)
    have ht := fun (x : Term) (hx : x ∈ atoms) => ha x (by simp [hx])
    have hv := add_valid w acc a hc hh.1 hw hh.2
    obtain ⟨hf, hfwidth, hvalue⟩ := ih (.app w (.add w) [acc, a]) hv rfl ht
    refine ⟨hf, hfwidth, ?_⟩
    simpa [value_binary ν θ hθ w (.add w) acc a hv, interpretWith, interpretOp,
      ADD, MNat, Nat.add_assoc] using hvalue

private theorem rebuildSpine_value (ν : Var → Nat) (θ : ExternalInterpretation)
    (hθ : θ.Total) (w : Width) (atoms : List Term) (constant : Nat)
    (ha : ∀ a ∈ atoms, a.wellFormed = true ∧ a.width = w) :
    value ν θ (rebuildSpine w atoms constant) =
      MNat w.bits ((atoms.map (value ν θ)).sum + constant) := by
  cases atoms with
  | nil => simp [rebuildSpine, MNat_lt]
  | cons a atoms =>
    have hh := ha a (by simp)
    have ht := fun (x : Term) (hx : x ∈ atoms) => ha x (by simp [hx])
    obtain ⟨hf, hw, hv⟩ := foldl_value ν θ hθ w atoms a hh.1 hh.2 ht
    let sum := atoms.foldl (fun lhs rhs => Term.app w (.add w) [lhs, rhs]) a
    have hs : sum.wellFormed = true := hf
    have hsw : sum.width = w := hw
    have hconst : (Term.const w (MNat w.bits constant)).wellFormed = true := by
      simp [Term.wellFormed, MNat_lt]
    have hadd := add_valid w sum (.const w (MNat w.bits constant)) hs hconst hsw rfl
    unfold rebuildSpine
    dsimp only
    split
    · rename_i hz
      have hz' : MNat w.bits constant = 0 := eq_of_beq hz
      have hz'' : constant % 2 ^ w.bits = 0 := by
        simpa [MNat, Nat.shiftLeft_eq] using hz'
      simpa [MNat, Nat.shiftLeft_eq, Nat.add_mod, hz''] using hv
    · change value ν θ (.app w (.add w) [sum, .const w (MNat w.bits constant)]) =
        MNat w.bits (value ν θ a + (atoms.map (value ν θ)).sum + constant)
      rw [value_binary ν θ hθ w (.add w) sum (.const w (MNat w.bits constant)) hadd]
      simp only [interpretWith, interpretOp, Option.map_some, Option.getD_some,
        value_const ν θ w (MNat w.bits constant) (MNat_lt w.bits constant),
        ADD, MNat_idempotent]
      rw [show value ν θ sum =
        MNat w.bits (value ν θ a + (atoms.map (value ν θ)).sum) from hv]
      simp [MNat]

/-- Sorting atoms changes neither their multiplicity nor their numeric sum. -/
private theorem sorted_atom_sum (ν : Var → Nat) (θ : ExternalInterpretation)
    (atoms : List Term) :
    ((atoms.mergeSort Term.rawLE).map (value ν θ)).sum =
      (atoms.map (value ν θ)).sum := by
  exact ((List.mergeSort_perm atoms Term.rawLE).map (value ν θ)).sum_nat

theorem ctz_mod (n : Nat) : n % 2 ^ ctz n = 0 := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    cases n with
    | zero => simp [ctz]
    | succ n =>
      by_cases h : (n + 1) % 2 = 0
      · have hd : 2 ∣ n + 1 := Nat.dvd_of_mod_eq_zero h
        have hlt : (n + 1) / 2 < n + 1 := Nat.div_lt_self (Nat.succ_pos n) (by decide)
        generalize hhalf : (n + 1) / 2 = half
        have ih' := ih half (hhalf ▸ hlt)
        have heq : n + 1 = 2 * half := by
          rw [← hhalf, Nat.mul_comm]
          exact (Nat.div_mul_cancel hd).symm
        simp only [ctz, h, hhalf, ↓reduceIte]
        have hpow : 2 ^ (ctz half + 1) = 2 * 2 ^ ctz half := by
          rw [Nat.pow_succ, Nat.mul_comm]
        have hd2 : 2 * 2 ^ ctz half ∣ 2 * half :=
          Nat.mul_dvd_mul_left 2 (Nat.dvd_of_mod_eq_zero ih')
        rw [hpow]
        exact Nat.mod_eq_zero_of_dvd (heq ▸ hd2)
      · simp [ctz, h, Nat.mod_one]

theorem bitLen_spec (n : Nat) (hn : n ≠ 0) : n < 2 ^ bitLen n := by
  have hz : (n == 0) = false := beq_eq_false_iff_ne.mpr hn
  simp [bitLen, hz, Nat.lt_log2_self]

private theorem span_forces_zero (v lo hi : Nat) (hlt : v < 2 ^ hi)
    (hmod : v % 2 ^ lo = 0) (he : hi ≤ lo) : v = 0 := by
  have hle : 2 ^ hi ≤ 2 ^ lo := Nat.pow_le_pow_right (by decide) he
  have hlt' : v < 2 ^ lo := Nat.lt_of_lt_of_le hlt hle
  exact (Nat.mod_eq_of_lt hlt').symm.trans hmod

private theorem value_missing_span (ν : Var → Nat) (θ : ExternalInterpretation)
    (t : Term) (s : BitSpan) (h : interpretTerm ν θ t = none) :
    value ν θ t < 2 ^ s.hi ∧ value ν θ t % 2 ^ s.lo = 0 := by
  simp [value, h, Nat.two_pow_pos, Nat.zero_mod]

private theorem eq_two_pow_log (c : Nat) (hne : c ≠ 0) (h : c &&& (c - 1) = 0) :
    c = 2 ^ c.log2 := by
  revert hne h
  refine Nat.strongRecOn
    (motive := fun c => c ≠ 0 → c &&& (c - 1) = 0 → c = 2 ^ c.log2) c ?_
  intro c ih hne h
  obtain _ | c := c
  · exact absurd rfl hne
  · obtain _ | c := c
    · rw [Nat.log2_def]
      simp
    ·
        have hdiv : (((c + 2) &&& (c + 1)) / 2) =
            ((c + 2) / 2) &&& ((c + 1) / 2) := Nat.and_div_two
        have hdiv0 : ((c + 2) &&& (c + 1)) / 2 = 0 := by
          have h' : (c + 2) &&& (c + 1) = 0 := by simpa using h
          simp [h']
        by_cases hodd : (c + 2) % 2 = 1
        · have heq : (c + 1) / 2 = (c + 2) / 2 := by omega
          have hhalf0 : (c + 2) / 2 = 0 := by
            have : ((c + 2) / 2) &&& ((c + 2) / 2) = 0 := by
              simpa [heq, hdiv0] using hdiv.symm
            simpa [Nat.and_self] using this
          omega
        · have hmod : (c + 2) % 2 = 0 := by omega
          have hstep : (c + 1) / 2 = (c + 2) / 2 - 1 := by omega
          have hzero : ((c + 2) / 2) &&& ((c + 2) / 2 - 1) = 0 := by
            simpa [hstep, hdiv0] using hdiv.symm
          have hhalf : (c + 2) / 2 ≠ 0 := by omega
          have hhalf_lt : (c + 2) / 2 < c + 2 := by omega
          have heq := ih ((c + 2) / 2) hhalf_lt hhalf hzero
          have hlog : (c + 2).log2 = ((c + 2) / 2).log2 + 1 := by
            rw [Nat.log2_def]
            simp [show 2 ≤ c + 2 by omega]
          have htwo : c + 2 = 2 * ((c + 2) / 2) := by omega
          let k := ((c + 2) / 2).log2
          have hk : (c + 2) / 2 = 2 ^ k := heq
          calc
            c + 2 = 2 * ((c + 2) / 2) := htwo
            _ = 2 * 2 ^ k := by rw [hk]
            _ = 2 ^ (k + 1) := by rw [Nat.pow_succ, Nat.mul_comm]
            _ = 2 ^ (c + 2).log2 := by rw [← hlog]

private theorem pow2_shift_eq (c k : Nat) (h : natPow2Shift? c = some k) : c = 2 ^ k := by
  simp only [natPow2Shift?] at h
  split at h
  · rename_i hpow
    cases h
    simp only [Bool.and_eq_true, bne_iff_ne, beq_iff_eq] at hpow
    exact eq_two_pow_log c hpow.1 hpow.2
  · cases h

private theorem and_low_cleared (x m : Nat) :
    (x &&& m) % 2 ^ ctz m = 0 := by
  rw [Nat.and_mod_two_pow, ctz_mod, Nat.and_zero]

private theorem land_span (m r : Nat) (hr : r ≤ m) (hdiv : r % 2 ^ ctz m = 0) :
    r < 2 ^ (if (m == 0) = true then BitSpan.empty else ⟨ctz m, bitLen m⟩).hi ∧
      r % 2 ^ (if (m == 0) = true then BitSpan.empty else ⟨ctz m, bitLen m⟩).lo = 0 := by
  by_cases hz : (m == 0) = true
  · have hm : m = 0 := by simpa using hz
    subst hm
    have hr0 : r = 0 := Nat.le_zero.mp hr
    simp [hr0, hz, BitSpan.empty, BitSpan.hi, BitSpan.lo, Nat.two_pow_pos, Nat.mod_one]
  · have hne : m ≠ 0 := by simpa using hz
    simp only [if_neg hz, BitSpan.hi, BitSpan.lo]
    exact ⟨Nat.lt_of_le_of_lt hr (bitLen_spec m hne), hdiv⟩

private theorem bitRange_value (ν : Var → Nat) (θ : ExternalInterpretation)
    (w : Width) (t : Term) (s : BitSpan) (hs : bitRange w t = some s) :
    value ν θ t < 2 ^ s.hi ∧ value ν θ t % 2 ^ s.lo = 0 := by
  revert s hs
  fun_induction bitRange w t
  case case1 wc c =>
    intro s hs
    cases hs
    cases hc : (c == 0)
    · have hne : c ≠ 0 := by simpa [beq_eq_false_iff_ne] using hc
      simp only [hc, if_neg Bool.false_ne_true, BitSpan.lo, BitSpan.hi]
      by_cases hlt : c < 2 ^ wc.bits
      · simp [value, interpretTerm, hlt]
        exact ⟨bitLen_spec c hne, ctz_mod c⟩
      · simp [value, interpretTerm, hlt, Nat.two_pow_pos, Nat.zero_mod]
    · have hc0 : c = 0 := by simpa using hc
      subst hc0
      simp [BitSpan.empty, value, interpretTerm, Nat.two_pow_pos, Nat.mod_one]
  case case13 tw htw ow a ih =>
    intro s hs
    have hchild := ih s hs
    cases h : interpretTerm ν θ (.app tw (.id ow) [a])
    · exact value_missing_span ν θ _ s h
    · have happ := h
      simp only [value, happ]
      rw [interpretTerm] at h
      cases ha : interpretTerm ν θ a
      · simp [interpretTerms, ha, interpretWith, interpretOp, ID] at h
      · simp [interpretTerms, ha, interpretWith, interpretOp, ID] at h
        rcases h with ⟨hsig, hval⟩
        simp only [Op.validSignature, List.all_cons, List.all_nil, beq_iff_eq,
          Bool.and_eq_true, Bool.decide_eq_true] at hsig
        rcases hsig with ⟨rfl, -, ha_w⟩
        rcases ha_w with ⟨ha_w, -⟩
        have htw' : tw = w := by simpa using htw
        subst htw'
        have hlt := value_lt ν θ a
        simp only [value, ha, Option.getD_some] at hchild hlt
        rw [ha_w] at hlt
        rw [MNat_of_lt hlt] at hval
        simpa [hval] using hchild
  case case24 tw htw ow a b sa sb hb ha iha ihb =>
    intro s hs
    have ha' := iha sa ha
    have hb' := ihb sb hb
    cases h : interpretTerm ν θ (.app tw (.add ow) [a, b])
    · exact value_missing_span ν θ _ s h
    · have happ := h
      simp only [value, happ]
      rw [interpretTerm] at h
      cases haa : interpretTerm ν θ a
      · simp [interpretTerms, haa] at h
      · cases hbb : interpretTerm ν θ b
        · simp [interpretTerms, haa, hbb] at h
        · simp [interpretTerms, haa, hbb, interpretWith, interpretOp, ADD] at h
          rcases h with ⟨hsig, hval⟩
          simp only [Op.validSignature, List.all_cons, List.all_nil, beq_iff_eq,
            Bool.and_eq_true] at hsig
          rcases hsig with ⟨rfl, -, ha_w, hb_w, -⟩
          have htw' : tw = w := by simpa using htw
          subst htw'
          simp only [value, haa, hbb, Option.getD_some] at ha' hb' hval
          -- The carried sum stays inside the joined span.
          unfold BitSpan.join at hs
          split at hs
          · rename_i hempty
            cases hs
            have he : sa.hi ≤ sa.lo := by
              simpa [BitSpan.isEmpty, decide_eq_true_eq] using hempty
            have hz := span_forces_zero _ sa.lo sa.hi ha'.1 ha'.2 he
            simp only [hz, Nat.zero_add] at hval
            have hlt := value_lt ν θ b
            simp only [value, hbb, Option.getD_some] at hlt
            rw [hb_w] at hlt
            rw [MNat_of_lt hlt, MNat_of_lt hlt] at hval
            simp only [Option.getD_some]
            rw [← hval]
            exact hb'
          · rename_i hnota
            split at hs
            · rename_i _ hempty
              cases hs
              have he : sb.hi ≤ sb.lo := by
                simpa [BitSpan.isEmpty, decide_eq_true_eq] using hempty
              have hz := span_forces_zero _ sb.lo sb.hi hb'.1 hb'.2 he
              simp only [hz, Nat.add_zero] at hval
              have hlt := value_lt ν θ a
              simp only [value, haa, Option.getD_some] at hlt
              rw [ha_w] at hlt
              rw [MNat_of_lt hlt, MNat_of_lt hlt] at hval
              simp only [Option.getD_some]
              rw [← hval]
              exact ha'
            · rename_i _ hnotb
              split at hs
              · rename_i hsplit
                cases hs
                have hltA := value_lt ν θ a
                have hltB := value_lt ν θ b
                simp only [value, haa, hbb, Option.getD_some] at hltA hltB
                rw [ha_w] at hltA
                rw [hb_w] at hltB
                have hva_n :=
                  Nat.lt_of_lt_of_le ha'.1 (Nat.pow_le_pow_right (by decide) hsplit)
                have hsum_eq := add_eq_lor_of_split _ _ sb.lo hva_n hb'.2
                have hsum_lt := Nat.or_lt_two_pow hltA hltB
                rw [← hsum_eq] at hsum_lt
                rw [MNat_of_lt hsum_lt, MNat_of_lt hsum_lt] at hval
                simp only [Option.getD_some]
                rw [← hval]
                refine ⟨?_, ?_⟩
                · have hlo : sb.lo < sb.hi := by
                    have : ¬sb.lo ≥ sb.hi := by
                      simpa [BitSpan.isEmpty, decide_eq_true_eq] using hnotb
                    omega
                  have hva_hi :=
                    Nat.lt_of_lt_of_le hva_n
                      (Nat.pow_le_pow_right (by decide) (Nat.le_of_lt hlo))
                  rw [hsum_eq]
                  exact Nat.or_lt_two_pow hva_hi hb'.1
                · have horder : sa.lo ≤ sa.hi := by
                    have : ¬sa.hi ≤ sa.lo := by
                      simpa [BitSpan.isEmpty, decide_eq_true_eq] using hnota
                    omega
                  exact Nat.mod_eq_zero_of_dvd (Nat.dvd_add
                    (Nat.dvd_of_mod_eq_zero ha'.2)
                    (Nat.dvd_trans (Nat.pow_dvd_pow 2 (Nat.le_trans horder hsplit))
                      (Nat.dvd_of_mod_eq_zero hb'.2)))
              · split at hs
                · rename_i _ _ _ hsplit
                  cases hs
                  have hltA := value_lt ν θ a
                  have hltB := value_lt ν θ b
                  simp only [value, haa, hbb, Option.getD_some] at hltA hltB
                  rw [ha_w] at hltA
                  rw [hb_w] at hltB
                  have hvb_n :=
                    Nat.lt_of_lt_of_le hb'.1 (Nat.pow_le_pow_right (by decide) hsplit)
                  have hsum_eq := add_eq_lor_of_split _ _ sa.lo hvb_n ha'.2
                  have hsum_lt := Nat.or_lt_two_pow hltB hltA
                  rw [← hsum_eq, Nat.add_comm] at hsum_lt
                  rw [MNat_of_lt hsum_lt, MNat_of_lt hsum_lt] at hval
                  simp only [Option.getD_some]
                  rw [← hval]
                  refine ⟨?_, ?_⟩
                  · have hlo : sa.lo < sa.hi := by
                      have : ¬sa.hi ≤ sa.lo := by
                        simpa [BitSpan.isEmpty, decide_eq_true_eq] using hnota
                      omega
                    have hvb_hi :=
                      Nat.lt_of_lt_of_le hvb_n
                        (Nat.pow_le_pow_right (by decide) (Nat.le_of_lt hlo))
                    rw [Nat.add_comm, hsum_eq]
                    exact Nat.or_lt_two_pow hvb_hi ha'.1
                  · have horder : sb.lo ≤ sb.hi := by
                      have : ¬sb.hi ≤ sb.lo := by
                        simpa [BitSpan.isEmpty, decide_eq_true_eq] using hnotb
                      omega
                    exact Nat.mod_eq_zero_of_dvd (Nat.dvd_add
                      (Nat.dvd_trans (Nat.pow_dvd_pow 2 (Nat.le_trans horder hsplit))
                        (Nat.dvd_of_mod_eq_zero ha'.2))
                      (Nat.dvd_of_mod_eq_zero hb'.2))
                · cases hs
  case case7 tw htw q ow v a hq =>
    intro s hs
    cases hs
    simp only [BitSpan.hi, BitSpan.lo, Nat.pow_zero]
    refine ⟨?_, Nat.mod_one _⟩
    cases h : interpretTerm ν θ (.app tw (.zext q ow v) [a])
    · simpa [value, h] using Nat.two_pow_pos q
    · have happ := h
      simp only [value, happ, Option.getD_some]
      rw [interpretTerm] at h
      cases ha : interpretTerm ν θ a
      · simp [interpretTerms, ha, interpretWith, interpretOp] at h
      · rename_i val
        simp [interpretTerms, ha, interpretWith, interpretOp, Z] at h
        rcases h with ⟨hsig, hval⟩
        simp only [Op.validSignature, List.all_cons, List.all_nil, beq_iff_eq,
          Bool.and_eq_true, decide_eq_true_eq] at hsig
        rcases hsig with ⟨h1, h2, h3, h4⟩
        rcases h1 with ⟨⟨rfl, -, hle⟩, -⟩
        have hlt := MNat_lt q val
        have hmid : MNat q val < 2 ^ tw.bits :=
          Nat.lt_of_lt_of_le hlt (Nat.pow_le_pow_right (by decide) hle)
        rw [MNat_of_lt hmid, MNat_of_lt hmid] at hval
        simpa [hval] using hlt
  case case9 tw htw q v a hq =>
    intro s hs
    cases hs
    simp only [BitSpan.hi, BitSpan.lo, Nat.pow_zero]
    refine ⟨?_, Nat.mod_one _⟩
    cases h : interpretTerm ν θ (.app tw (.low q v) [a])
    · simpa [value, h] using Nat.two_pow_pos q
    · have happ := h
      simp only [value, happ, Option.getD_some]
      rw [interpretTerm] at h
      cases ha : interpretTerm ν θ a
      · simp [interpretTerms, ha, interpretWith, interpretOp] at h
      · rename_i val
        simp [interpretTerms, ha, interpretWith, interpretOp, LOW] at h
        rcases h with ⟨-, hval⟩
        have htw' : tw = w := by simpa using htw
        subst htw'
        have hq' : 0 < q ∧ q ≤ tw.bits := by
          simpa [Bool.and_eq_true, decide_eq_true_eq] using hq
        have hle : q ≤ tw.bits := hq'.2
        have hlt := MNat_lt q (MNat v val)
        rw [MNat_of_lt (Nat.lt_of_lt_of_le hlt
          (Nat.pow_le_pow_right (by decide) hle))] at hval
        simpa [hval] using hlt
  case case11 tw htw ℓ v a hq =>
    intro s hs
    cases hs
    simp only [BitSpan.hi, BitSpan.lo, Nat.pow_zero]
    refine ⟨?_, Nat.mod_one _⟩
    cases h : interpretTerm ν θ (.app tw (.extract 0 ℓ v) [a])
    · simpa [value, h] using Nat.two_pow_pos ℓ
    · have happ := h
      simp only [value, happ, Option.getD_some]
      rw [interpretTerm] at h
      cases ha : interpretTerm ν θ a
      · simp [interpretTerms, ha, interpretWith, interpretOp] at h
      · rename_i val
        simp [interpretTerms, ha, interpretWith, interpretOp, EXTRACT] at h
        rcases h with ⟨-, hval⟩
        have htw' : tw = w := by simpa using htw
        subst htw'
        have hq' : 0 < ℓ ∧ ℓ ≤ tw.bits := by
          simpa [Bool.and_eq_true, decide_eq_true_eq] using hq
        have hle : ℓ ≤ tw.bits := hq'.2
        have hlt := MNat_lt ℓ (MNat v val)
        rw [MNat_of_lt (Nat.lt_of_lt_of_le hlt
          (Nat.pow_le_pow_right (by decide) hle))] at hval
        simpa [hval] using hlt
  case case4 hneq q head wc mraw hguard msk =>
    rename_i tw
    intro s hs
    cases hs
    cases h : interpretTerm ν θ (.app tw (.and q) [head, .const wc mraw])
    · simp only [value, h]
      exact land_span _ 0 (Nat.zero_le _) (Nat.zero_mod _)
    · rename_i val1
      simp only [value, h, Option.getD_some]
      rw [interpretTerm] at h
      cases hhead : interpretTerm ν θ head
      · simp [interpretTerms, hhead] at h
      · rename_i va
        cases hm : interpretTerm ν θ (.const wc mraw)
        · simp [interpretTerms, hhead, hm] at h
        · rename_i vm
          simp [interpretTerms, hhead, hm, interpretWith, interpretOp, AND] at h
          rcases h with ⟨-, hval⟩
          simp only [interpretTerm] at hm
          split at hm
          · cases hm
            have htw' : tw = w := by simpa using hneq
            subst htw'
            have hqle : q ≤ tw.bits := by
              by_cases h0 : q = 0
              · simp [h0] at hguard
              · by_cases hlt : tw.bits < q
                · simp [hlt, decide_eq_true_eq] at hguard
                · omega
            have hinner := MNat_lt q (va &&& mraw)
            have hres : MNat q (va &&& mraw) < 2 ^ tw.bits :=
              Nat.lt_of_lt_of_le hinner (Nat.pow_le_pow_right (by decide) hqle)
            rw [MNat_of_lt hres] at hval
            have hmod : MNat q (va &&& mraw) = (va &&& mraw) % 2 ^ q := by
              simp [MNat, Nat.shiftLeft_eq, Nat.one_mul]
            have hm' : mraw &&& ((1 <<< q) - 1) = mraw % 2 ^ q := by
              rw [Nat.shiftLeft_eq, Nat.one_mul, Nat.and_two_pow_sub_one_eq_mod]
            rw [hmod] at hval
            have hr : val1 = (va % 2 ^ q) &&& msk := by
              rw [← hval, Nat.and_mod_two_pow, ← hm']
            have hle_r : val1 ≤ msk := by
              rw [hr]
              exact Nat.and_le_right
            have hdiv : val1 % 2 ^ ctz msk = 0 := by
              rw [hr]
              exact and_low_cleared _ _
            exact land_span msk val1 hle_r hdiv
          · cases hm
  case case6 hneq q wc mraw head hnot hguard msk =>
    rename_i tw
    intro s hs
    cases hs
    cases h : interpretTerm ν θ (.app tw (.and q) [.const wc mraw, head])
    · simp only [value, h]
      exact land_span _ 0 (Nat.zero_le _) (Nat.zero_mod _)
    · rename_i val1
      simp only [value, h, Option.getD_some]
      rw [interpretTerm] at h
      cases hm : interpretTerm ν θ (.const wc mraw)
      · simp [interpretTerms, hm] at h
      · rename_i vm
        cases hhead : interpretTerm ν θ head
        · simp [interpretTerms, hm, hhead] at h
        · rename_i va
          simp [interpretTerms, hm, hhead, interpretWith, interpretOp, AND] at h
          rcases h with ⟨-, hval⟩
          simp only [interpretTerm] at hm
          split at hm
          · cases hm
            rw [Nat.and_comm] at hval
            have htw' : tw = w := by simpa using hneq
            subst htw'
            have hqle : q ≤ tw.bits := by
              by_cases h0 : q = 0
              · simp [h0] at hguard
              · by_cases hlt : tw.bits < q
                · simp [hlt, decide_eq_true_eq] at hguard
                · omega
            have hinner := MNat_lt q (va &&& mraw)
            have hres : MNat q (va &&& mraw) < 2 ^ tw.bits :=
              Nat.lt_of_lt_of_le hinner (Nat.pow_le_pow_right (by decide) hqle)
            rw [MNat_of_lt hres] at hval
            have hmod : MNat q (va &&& mraw) = (va &&& mraw) % 2 ^ q := by
              simp [MNat, Nat.shiftLeft_eq, Nat.one_mul]
            have hm' : mraw &&& ((1 <<< q) - 1) = mraw % 2 ^ q := by
              rw [Nat.shiftLeft_eq, Nat.one_mul, Nat.and_two_pow_sub_one_eq_mod]
            rw [hmod] at hval
            have hr : val1 = (va % 2 ^ q) &&& msk := by
              rw [← hval, Nat.and_mod_two_pow, ← hm']
            have hle_r : val1 ≤ msk := by
              rw [hr]
              exact Nat.and_le_right
            have hdiv : val1 % 2 ^ ctz msk = 0 := by
              rw [hr]
              exact and_low_cleared _ _
            exact land_span msk val1 hle_r hdiv
          · cases hm
  case case14 hneq ow a wc craw k hk span hs hempty ih =>
    rename_i tw
    intro s hs'
    cases hs'
    have hv := ih span hs
    have he : span.hi ≤ span.lo := by
      simpa [BitSpan.isEmpty, decide_eq_true_eq] using hempty
    have hz := span_forces_zero (value ν θ a) span.lo span.hi hv.1 hv.2 he
    simp only [BitSpan.empty, BitSpan.hi, BitSpan.lo, Nat.pow_zero]
    cases h : interpretTerm ν θ (.app tw (.mullo ow) [a, .const wc craw])
    · simp [value, h, Nat.mod_one, Nat.two_pow_pos]
    · rename_i val1
      simp only [value, h, Option.getD_some]
      rw [interpretTerm] at h
      cases ha : interpretTerm ν θ a
      · simp [interpretTerms, ha] at h
      · rename_i va
        simp only [value, ha, Option.getD_some] at hz
        subst hz
        cases hc : interpretTerm ν θ (.const wc craw)
        · simp [interpretTerms, ha, hc] at h
        · simp [interpretTerms, ha, hc, interpretWith, interpretOp, MULLO,
            Nat.zero_mul, MNat] at h
          rcases h with ⟨-, hval⟩
          simp [hval, Nat.mod_one, Nat.two_pow_pos]
  case case15 hneq ow a wc craw k hk span hs hnot hfit ih =>
    rename_i tw
    intro s hs'
    cases hs'
    simp only [BitSpan.hi, BitSpan.lo]
    have hc := pow2_shift_eq craw k hk
    have hv := ih span hs
    cases h : interpretTerm ν θ (.app tw (.mullo ow) [a, .const wc craw])
    · simp only [value, h]
      exact ⟨Nat.two_pow_pos _, Nat.zero_mod _⟩
    · rename_i val1
      simp only [value, h, Option.getD_some]
      rw [interpretTerm] at h
      cases ha : interpretTerm ν θ a
      · simp [interpretTerms, ha] at h
      · rename_i va
        cases hm : interpretTerm ν θ (.const wc craw)
        · simp [interpretTerms, ha, hm] at h
        · rename_i vm
          simp [interpretTerms, ha, hm, interpretWith, interpretOp, MULLO] at h
          rcases h with ⟨hsig, hval⟩
          simp only [interpretTerm] at hm
          split at hm
          · cases hm
            simp only [Op.validSignature, List.all_cons, List.all_nil, beq_iff_eq,
              Bool.and_eq_true] at hsig
            rcases hsig with ⟨rfl, -, ha_w, hc_w, -⟩
            have htw' : tw = w := by simpa using hneq
            subst htw'
            subst hc
            simp only [value, ha, Option.getD_some] at hv
            have hmul : va * 2 ^ k < 2 ^ (span.hi + k) := by
              have hlt := (Nat.mul_lt_mul_left (Nat.two_pow_pos k)).mpr hv.1
              simpa [Nat.mul_comm, Nat.pow_add] using hlt
            have hwide : va * 2 ^ k < 2 ^ tw.bits :=
              Nat.lt_of_lt_of_le hmul (Nat.pow_le_pow_right (by decide)
                (by simpa using hfit))
            have hprod : MNat tw.bits (va * 2 ^ k) = va * 2 ^ k := MNat_of_lt hwide
            rw [hprod, hprod] at hval
            rw [← hval]
            refine ⟨hmul, ?_⟩
            have hd : 2 ^ span.lo ∣ va := Nat.dvd_of_mod_eq_zero hv.2
            rw [Nat.pow_add]
            exact Nat.mod_eq_zero_of_dvd (Nat.mul_dvd_mul_right hd (2 ^ k))
          · cases hm
  case case19 hneq ow wc craw a hnot k hk span hs hempty ih =>
    rename_i tw
    intro s hs'
    cases hs'
    have hv := ih span hs
    have he : span.hi ≤ span.lo := by
      simpa [BitSpan.isEmpty, decide_eq_true_eq] using hempty
    have hz := span_forces_zero (value ν θ a) span.lo span.hi hv.1 hv.2 he
    simp only [BitSpan.empty, BitSpan.hi, BitSpan.lo, Nat.pow_zero]
    cases h : interpretTerm ν θ (.app tw (.mullo ow) [.const wc craw, a])
    · simp [value, h, Nat.mod_one, Nat.two_pow_pos]
    · rename_i val1
      simp only [value, h, Option.getD_some]
      rw [interpretTerm] at h
      cases hc : interpretTerm ν θ (.const wc craw)
      · simp [interpretTerms, hc] at h
      · cases ha : interpretTerm ν θ a
        · simp [interpretTerms, hc, ha] at h
        · rename_i va
          simp only [value, ha, Option.getD_some] at hz
          subst hz
          simp [interpretTerms, hc, ha, interpretWith, interpretOp, MULLO,
            Nat.mul_zero, MNat] at h
          rcases h with ⟨-, hval⟩
          simp [hval, Nat.mod_one, Nat.two_pow_pos]
  case case20 hneq ow wc craw a hnot k hk span hs hnotE hfit ih =>
    rename_i tw
    intro s hs'
    cases hs'
    simp only [BitSpan.hi, BitSpan.lo]
    have hc := pow2_shift_eq craw k hk
    have hv := ih span hs
    cases h : interpretTerm ν θ (.app tw (.mullo ow) [.const wc craw, a])
    · simp only [value, h]
      exact ⟨Nat.two_pow_pos _, Nat.zero_mod _⟩
    · rename_i val1
      simp only [value, h, Option.getD_some]
      rw [interpretTerm] at h
      cases hm : interpretTerm ν θ (.const wc craw)
      · simp [interpretTerms, hm] at h
      · rename_i vm
        cases ha : interpretTerm ν θ a
        · simp [interpretTerms, hm, ha] at h
        · rename_i va
          simp [interpretTerms, hm, ha, interpretWith, interpretOp, MULLO] at h
          rcases h with ⟨hsig, hval⟩
          simp only [interpretTerm] at hm
          split at hm
          · cases hm
            rw [Nat.mul_comm] at hval
            simp only [Op.validSignature, List.all_cons, List.all_nil, beq_iff_eq,
              Bool.and_eq_true] at hsig
            rcases hsig with ⟨rfl, -, hc_w, ha_w, -⟩
            have htw' : tw = w := by simpa using hneq
            subst htw'
            subst hc
            simp only [value, ha, Option.getD_some] at hv
            have hmul : va * 2 ^ k < 2 ^ (span.hi + k) := by
              have hlt := (Nat.mul_lt_mul_left (Nat.two_pow_pos k)).mpr hv.1
              simpa [Nat.mul_comm, Nat.pow_add] using hlt
            have hwide : va * 2 ^ k < 2 ^ tw.bits :=
              Nat.lt_of_lt_of_le hmul (Nat.pow_le_pow_right (by decide)
                (by simpa using hfit))
            have hprod : MNat tw.bits (va * 2 ^ k) = va * 2 ^ k := MNat_of_lt hwide
            rw [hprod, hprod] at hval
            rw [← hval]
            refine ⟨hmul, ?_⟩
            have hd : 2 ^ span.lo ∣ va := Nat.dvd_of_mod_eq_zero hv.2
            rw [Nat.pow_add]
            exact Nat.mod_eq_zero_of_dvd (Nat.mul_dvd_mul_right hd (2 ^ k))
          · cases hm
  case case28 hneq ow z a wc craw hz k hk hw span hs ih =>
    rename_i tw
    intro s hs'
    cases hs'
    have hc := pow2_shift_eq craw k hk
    have hv := ih span hs
    have htw' : tw = w := by simpa using hneq
    subst htw'
    subst hc
    by_cases hempty : (span.isEmpty || decide (span.hi ≤ k)) = true
    · simp only [hempty, if_true, BitSpan.empty, BitSpan.hi, BitSpan.lo, Nat.pow_zero]
      -- The quotient is zero, so it occupies the empty span.
      cases h : interpretTerm ν θ (.app tw (.udiv ow z) [a, .const wc (2 ^ k)])
      · simp [value, h, Nat.mod_one, Nat.two_pow_pos]
      · rename_i val1
        simp only [value, h, Option.getD_some]
        rw [interpretTerm] at h
        cases ha : interpretTerm ν θ a
        · simp [interpretTerms, ha] at h
        · rename_i va
          cases hm : interpretTerm ν θ (.const wc (2 ^ k))
          · simp [interpretTerms, ha, hm] at h
          · rename_i vm
            simp [interpretTerms, ha, hm, interpretWith, interpretOp, UDIV] at h
            rcases h with ⟨hsig, hval⟩
            simp only [interpretTerm] at hm
            split at hm
            · cases hm
              simp only [Op.validSignature, List.all_cons, List.all_nil, beq_iff_eq,
                Bool.and_eq_true] at hsig
              rcases hsig with ⟨rfl, -, ha_w, -, -⟩
              simp only [value, ha, Option.getD_some] at hv
              have hva : va < 2 ^ tw.bits := by
                have hlt := value_lt ν θ a
                simp only [value, ha, Option.getD_some] at hlt
                simpa [ha_w] using hlt
              have hzero : va / 2 ^ k = 0 := by
                simp only [Bool.or_eq_true, decide_eq_true_eq] at hempty
                rcases hempty with hempty | hhi
                · have he : span.hi ≤ span.lo := by
                    simpa [BitSpan.isEmpty, decide_eq_true_eq] using hempty
                  have hzv := span_forces_zero va span.lo span.hi hv.1 hv.2 he
                  simp [hzv]
                · have hlt : va < 2 ^ k :=
                    Nat.lt_of_lt_of_le hv.1 (Nat.pow_le_pow_right (by decide) hhi)
                  exact Nat.div_eq_of_lt hlt
              have hklt : k < tw.bits := by omega
              have hpow : 2 ^ k < 2 ^ tw.bits := Nat.pow_lt_pow_of_lt (by decide) hklt
              have hne : ((2 ^ k) == 0) = false := by
                simp [beq_eq_false_iff_ne, Nat.ne_of_gt (Nat.two_pow_pos k)]
              simp only [MNat, Nat.shiftLeft_eq, Nat.one_mul] at hval
              rw [Nat.mod_eq_of_lt hpow, Nat.mod_eq_of_lt hva] at hval
              simp [hne, hzero, Nat.zero_mod] at hval
              rw [hval.symm]
              exact ⟨Nat.one_pos, Nat.mod_one _⟩
            · cases hm
    · simp only [if_neg hempty, BitSpan.hi, BitSpan.lo]
      cases h : interpretTerm ν θ (.app tw (.udiv ow z) [a, .const wc (2 ^ k)])
      · simp only [value, h]
        refine ⟨Nat.two_pow_pos _, Nat.zero_mod _⟩
      · rename_i val1
        simp only [value, h, Option.getD_some]
        rw [interpretTerm] at h
        cases ha : interpretTerm ν θ a
        · simp [interpretTerms, ha] at h
        · rename_i va
          cases hm : interpretTerm ν θ (.const wc (2 ^ k))
          · simp [interpretTerms, ha, hm] at h
          · rename_i vm
            simp [interpretTerms, ha, hm, interpretWith, interpretOp, UDIV] at h
            rcases h with ⟨hsig, hval⟩
            simp only [interpretTerm] at hm
            split at hm
            · cases hm
              simp only [Op.validSignature, List.all_cons, List.all_nil, beq_iff_eq,
                Bool.and_eq_true] at hsig
              rcases hsig with ⟨rfl, -, ha_w, -, -⟩
              simp only [value, ha, Option.getD_some] at hv
              have hva : va < 2 ^ tw.bits := by
                have hlt := value_lt ν θ a
                simp only [value, ha, Option.getD_some] at hlt
                simpa [ha_w] using hlt
              have hklt : k < tw.bits := by omega
              have hpow : 2 ^ k < 2 ^ tw.bits := Nat.pow_lt_pow_of_lt (by decide) hklt
              have hne : ((2 ^ k) == 0) = false := by
                simp [beq_eq_false_iff_ne, Nat.ne_of_gt (Nat.two_pow_pos k)]
              simp only [MNat, Nat.shiftLeft_eq, Nat.one_mul] at hval
              rw [Nat.mod_eq_of_lt hpow, Nat.mod_eq_of_lt hva] at hval
              simp only [show 2 ^ k ≠ 0 from Nat.ne_of_gt (Nat.two_pow_pos k), if_false] at hval
              have hquot : va / 2 ^ k < 2 ^ tw.bits :=
                Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hva
              rw [Nat.mod_eq_of_lt hquot] at hval
              rw [← hval]
              have hhi : k < span.hi := by
                simp only [Bool.or_eq_true, Bool.not_eq_true, decide_eq_true_eq] at hempty
                omega
              refine ⟨?_, ?_⟩
              · have hbase : 2 ^ span.hi = 2 ^ (span.hi - k) * 2 ^ k := by
                  rw [← Nat.pow_add]
                  exact congrArg (fun n => 2 ^ n) (by omega)
                exact (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos k)).mpr (hbase ▸ hv.1)
              · by_cases hlo : span.lo ≤ k
                · simp [hlo, Nat.pow_zero, Nat.mod_one]
                · simp [hlo]
                  have hd : 2 ^ span.lo ∣ va := Nat.dvd_of_mod_eq_zero hv.2
                  have hstep : span.lo = (span.lo - k) + k := by omega
                  rw [hstep, Nat.pow_add, Nat.mul_comm] at hd
                  have hdivd : 2 ^ (span.lo - k) ∣ va / 2 ^ k :=
                    Nat.dvd_div_of_mul_dvd hd
                  exact Nat.mod_eq_zero_of_dvd hdivd
            · cases hm
  case case29 hneq ow z a wc craw hz k hk hw hnone ih =>
    rename_i tw
    intro s hs'
    cases hs'
    simp only [BitSpan.hi, BitSpan.lo, Nat.pow_zero]
    refine ⟨?_, Nat.mod_one _⟩
    have hc := pow2_shift_eq craw k hk
    have htw' : tw = w := by simpa using hneq
    subst htw'
    subst hc
    have hklt : k < tw.bits := by omega
    cases h : interpretTerm ν θ (.app tw (.udiv ow z) [a, .const wc (2 ^ k)])
    · simp [value, h]
      exact Nat.two_pow_pos _
    · rename_i val1
      simp only [value, h, Option.getD_some]
      rw [interpretTerm] at h
      cases ha : interpretTerm ν θ a
      · simp [interpretTerms, ha] at h
      · rename_i va
        cases hm : interpretTerm ν θ (.const wc (2 ^ k))
        · simp [interpretTerms, ha, hm] at h
        · rename_i vm
          simp [interpretTerms, ha, hm, interpretWith, interpretOp, UDIV] at h
          rcases h with ⟨hsig, hval⟩
          simp only [interpretTerm] at hm
          split at hm
          · cases hm
            simp only [Op.validSignature, List.all_cons, List.all_nil, beq_iff_eq,
              Bool.and_eq_true] at hsig
            rcases hsig with ⟨rfl, -, ha_w, -, -⟩
            have hva : va < 2 ^ tw.bits := by
              have hlt := value_lt ν θ a
              simp only [value, ha, Option.getD_some] at hlt
              simpa [ha_w] using hlt
            have hpow : 2 ^ k < 2 ^ tw.bits := Nat.pow_lt_pow_of_lt (by decide) hklt
            have hne : ((2 ^ k) == 0) = false := by
              simp [beq_eq_false_iff_ne, Nat.ne_of_gt (Nat.two_pow_pos k)]
            simp only [MNat, Nat.shiftLeft_eq, Nat.one_mul] at hval
            rw [Nat.mod_eq_of_lt hpow, Nat.mod_eq_of_lt hva] at hval
            simp only [show 2 ^ k ≠ 0 from Nat.ne_of_gt (Nat.two_pow_pos k), if_false] at hval
            have hquot : va / 2 ^ k < 2 ^ tw.bits :=
              Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hva
            rw [Nat.mod_eq_of_lt hquot] at hval
            rw [← hval]
            have hbase : 2 ^ tw.bits = 2 ^ (tw.bits - k) * 2 ^ k := by
              rw [← Nat.pow_add]
              exact congrArg (fun n => 2 ^ n) (by omega)
            exact (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos k)).mpr (hbase ▸ hva)
          · cases hm
  all_goals
    intro s hs
    first
    | cases hs
    | fail "OPEN"

private theorem terms_members (args : List Term) (h : termsWellFormed args = true) :
    ∀ x ∈ args, x.wellFormed = true := by
  induction args with
  | nil => intro x hx; cases hx
  | cons a args ih =>
    simp only [termsWellFormed, Bool.and_eq_true] at h
    intro x hx
    simp only [List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact h.1
    · exact ih h.2 x hx

private theorem interpretTerms_lift (ν : Var → Nat) (θ : ExternalInterpretation)
    (hθ : θ.Total) (args : List Term)
    (hall : ∀ x ∈ args, x.wellFormed = true)
    (ih : ∀ x ∈ args, x.wellFormed = true → value ν θ (liftInteger x) = value ν θ x) :
    interpretTerms ν θ (args.map liftInteger) = interpretTerms ν θ args := by
  induction args with
  | nil => rfl
  | cons a args iha =>
    have ha : a.wellFormed = true := hall a (by simp)
    have htail : ∀ x ∈ args, x.wellFormed = true := by
      intro x hx
      exact hall x (by simp [hx])
    have hterms := iha htail fun x hx hwf => ih x (List.mem_cons_of_mem _ hx) hwf
    simp only [List.map_cons, interpretTerms, meaning ν θ hθ a ha,
      meaning ν θ hθ (liftInteger a) (liftInteger_wellFormed a ha),
      ih a (by simp) ha, hterms, Option.bind_eq_bind, Option.bind_some]

private theorem value_app_lifted (ν : Var → Nat) (θ : ExternalInterpretation)
    (w : Width) (op : Op) (args : List Term)
    (ht : (Term.app w op args).wellFormed = true)
    (hterms : interpretTerms ν θ (args.map liftInteger) = interpretTerms ν θ args) :
    value ν θ (.app w op (args.map liftInteger)) = value ν θ (.app w op args) := by
  have hw : (args.map liftInteger).map Term.width = args.map Term.width := by
    induction args with
    | nil => rfl
    | cons a args iha => simp [liftInteger_width, iha]
  simp only [value, interpretTerm, hw, hterms]

private theorem liftInteger_value (ν : Var → Nat) (θ : ExternalInterpretation)
    (hθ : θ.Total) (t : Term) (ht : t.wellFormed = true) :
    value ν θ (liftInteger t) = value ν θ t := by
  fun_induction liftInteger t
  case case1 | case2 | case3 => rfl
  case case4 w op args ih =>
    have hall : ∀ x ∈ args, x.wellFormed = true := by
      have h := ht
      simp only [Term.wellFormed, Bool.and_eq_true] at h
      exact terms_members args h.2
    have hterms := interpretTerms_lift ν θ hθ args hall ih
    simp only [rewriteHead]
    split
    · rename_i ow wa av wc k heq
      split
      · rename_i hwidth
        have hww : wa = w ∧ wc = w := by simpa [Bool.and_eq_true, beq_iff_eq] using hwidth
        generalize hmap : List.map liftInteger args = lifted at heq
        rw [hww.1, hww.2] at heq
        cases args with
        | nil => simp [heq] at hmap
        | cons a rest =>
          cases rest with
          | nil => simp [heq] at hmap
          | cons b rest =>
            cases rest with
            | cons c rest => simp [heq] at hmap
            | nil =>
              have hpair : liftInteger a = Term.const w av ∧ liftInteger b = Term.const w k := by
                simp only [heq, List.map_cons, List.map_nil, List.cons.injEq, and_true] at hmap
                exact hmap
              have hva := ih a (by simp) (hall a (by simp))
              have hvb := ih b (by simp) (hall b (by simp))
              have hav : av < 2 ^ w.bits := by
                have := liftInteger_wellFormed a (hall a (by simp))
                rw [hpair.1] at this
                simpa [Term.wellFormed] using this
              have hkv : k < 2 ^ w.bits := by
                have := liftInteger_wellFormed b (hall b (by simp))
                rw [hpair.2] at this
                simpa [Term.wellFormed] using this
              have ha_val : value ν θ a = av := by
                have hconst : value ν θ (.const w av) = av := value_const ν θ w av hav
                rw [hpair.1] at hva
                exact Eq.trans (Eq.symm hva) hconst
              have hb_val : value ν θ b = k := by
                have hconst : value ν θ (.const w k) = k := value_const ν θ w k hkv
                rw [hpair.2] at hvb
                exact Eq.trans (Eq.symm hvb) hconst
              have how : ow = w := by
                simp only [Term.wellFormed, Op.validSignature, Bool.and_eq_true, beq_iff_eq,
                  List.map_cons, List.map_nil] at ht
                exact ht.1.1.symm
              subst how
              have hlt : SHL ow av k < 2 ^ ow.bits := SHL_lt ow av k
              rw [value_binary ν θ hθ ow (.shl ow) a b ht, ha_val, hb_val]
              simp [interpretWith, interpretOp, MNat_of_lt hlt, value, interpretTerm, hlt]
      · exact value_app_lifted ν θ w (Op.shl _) args ht hterms
    · rename_i ow base wc k _ heq
      split
      · rename_i hfit
        split
        · rename_i hzero
          generalize hmap : List.map liftInteger args = lifted at heq
          cases args with
          | nil => simp [heq] at hmap
          | cons a rest =>
            cases rest with
            | nil => simp [heq] at hmap
            | cons b rest =>
              cases rest with
              | cons c rest => simp [heq] at hmap
              | nil =>
                have hpair : liftInteger a = base ∧ liftInteger b = Term.const wc k := by
                  simp only [heq, List.map_cons, List.map_nil, List.cons.injEq, and_true] at hmap
                  exact hmap
                have ha : value ν θ base = value ν θ a := by
                  have hih := ih a (by simp) (hall a (by simp))
                  rw [hpair.1] at hih
                  exact hih
                have hb : value ν θ b = k := by
                  have hih := ih b (by simp) (hall b (by simp))
                  rw [hpair.2] at hih
                  have hfit' : wc = w ∧ base.width = w := by
                    simpa [Bool.and_eq_true, beq_iff_eq] using hfit
                  have hwc : wc = w := hfit'.1
                  have hklt : k < 2 ^ w.bits := by
                    have := liftInteger_wellFormed b (hall b (by simp))
                    rw [hpair.2, hwc] at this
                    simpa [Term.wellFormed] using this
                  exact Eq.trans (Eq.symm hih) (value_const ν θ wc k (by simpa [hwc] using hklt))
                have how : ow = w := by
                  have h := ht
                  simp only [Term.wellFormed, Op.validSignature, Bool.and_eq_true, beq_iff_eq,
                    List.map_cons, List.map_nil] at h
                  exact h.1.1.symm
                subst how
                have hk0 : k % ow.bits = 0 := by simpa [beq_iff_eq] using hzero
                have haw : a.width = ow := by
                  have hfit' : wc = ow ∧ base.width = ow := by
                    simpa [Bool.and_eq_true, beq_iff_eq] using hfit
                  have hw := liftInteger_width a
                  rw [hpair.1] at hw
                  exact Eq.trans (Eq.symm hw) hfit'.2
                rw [ha, value_binary ν θ hθ ow (.shl ow) a b ht, hb]
                simp [interpretWith, interpretOp, SHL, kShift, hk0, value_mod ν θ ow a haw]
        · rename_i hzero
          generalize hmap : List.map liftInteger args = lifted at heq
          cases args with
          | nil => simp [heq] at hmap
          | cons a rest =>
            cases rest with
            | nil => simp [heq] at hmap
            | cons b rest =>
              cases rest with
              | cons c rest => simp [heq] at hmap
              | nil =>
                have hpair : liftInteger a = base ∧ liftInteger b = Term.const wc k := by
                  simp only [heq, List.map_cons, List.map_nil, List.cons.injEq, and_true] at hmap
                  exact hmap
                have ha : value ν θ base = value ν θ a := by
                  have hih := ih a (by simp) (hall a (by simp))
                  rw [hpair.1] at hih
                  exact hih
                have hb : value ν θ b = k := by
                  have hih := ih b (by simp) (hall b (by simp))
                  rw [hpair.2] at hih
                  have hwc : wc = w := by
                    have hfit' : wc = w ∧ base.width = w := by
                      simpa [Bool.and_eq_true, beq_iff_eq] using hfit
                    exact hfit'.1
                  have hklt : k < 2 ^ w.bits := by
                    have := liftInteger_wellFormed b (hall b (by simp))
                    rw [hpair.2, hwc] at this
                    simpa [Term.wellFormed] using this
                  exact Eq.trans (Eq.symm hih) (value_const ν θ wc k (by simpa [hwc] using hklt))
                have how : ow = w := by
                  have h := ht
                  simp only [Term.wellFormed, Op.validSignature, Bool.and_eq_true, beq_iff_eq,
                    List.map_cons, List.map_nil] at h
                  exact h.1.1.symm
                subst how
                have haw : a.width = ow := by
                  have hfit' : wc = ow ∧ base.width = ow := by
                    simpa [Bool.and_eq_true, beq_iff_eq] using hfit
                  have hw := liftInteger_width a
                  rw [hpair.1] at hw
                  exact Eq.trans (Eq.symm hw) hfit'.2
                have hpow : 1 <<< (k % ow.bits) < 2 ^ ow.bits := by
                  simpa [kShift] using shift_pow_lt ow k
                have hbase_wf : base.wellFormed = true := by
                  rw [← hpair.1]
                  exact liftInteger_wellFormed a (hall a (by simp))
                have hbw : base.width = ow := by
                  have hfit' : wc = ow ∧ base.width = ow := by
                    simpa [Bool.and_eq_true, beq_iff_eq] using hfit
                  exact hfit'.2
                have hmul_wf :
                    (Term.app ow (.mullo ow) [base, .const ow (1 <<< (k % ow.bits))]).wellFormed = true := by
                  simp [Term.wellFormed, Term.width, termsWellFormed, Op.validSignature, hpow, hbase_wf]
                  exact hbw
                rw [value_binary ν θ hθ ow (.mullo ow) base (.const ow (1 <<< (k % ow.bits))) hmul_wf,
                  value_binary ν θ hθ ow (.shl ow) a b ht, ha, hb]
                simp [interpretWith, interpretOp, value_const ν θ ow _ hpow,
                  SHL_eq_MULLO ow (value ν θ a) k (by simpa [haw] using value_lt ν θ a),
                  kShift, value_mod ν θ ow a haw]
      · exact value_app_lifted ν θ w (.shl ow) args ht hterms
    · rename_i ow wa av wc k heq
      split
      · rename_i hwidth
        have hww : wa = w ∧ wc = w := by simpa [Bool.and_eq_true, beq_iff_eq] using hwidth
        generalize hmap : List.map liftInteger args = lifted at heq
        rw [hww.1, hww.2] at heq
        cases args with
        | nil => simp [heq] at hmap
        | cons a rest =>
          cases rest with
          | nil => simp [heq] at hmap
          | cons b rest =>
            cases rest with
            | cons c rest => simp [heq] at hmap
            | nil =>
              have hpair : liftInteger a = Term.const w av ∧ liftInteger b = Term.const w k := by
                simp only [heq, List.map_cons, List.map_nil, List.cons.injEq, and_true] at hmap
                exact hmap
              have hva := ih a (by simp) (hall a (by simp))
              have hvb := ih b (by simp) (hall b (by simp))
              have hav : av < 2 ^ w.bits := by
                have := liftInteger_wellFormed a (hall a (by simp))
                rw [hpair.1] at this
                simpa [Term.wellFormed] using this
              have hkv : k < 2 ^ w.bits := by
                have := liftInteger_wellFormed b (hall b (by simp))
                rw [hpair.2] at this
                simpa [Term.wellFormed] using this
              have ha_val : value ν θ a = av := by
                have hconst : value ν θ (.const w av) = av := value_const ν θ w av hav
                rw [hpair.1] at hva
                exact Eq.trans (Eq.symm hva) hconst
              have hb_val : value ν θ b = k := by
                have hconst : value ν θ (.const w k) = k := value_const ν θ w k hkv
                rw [hpair.2] at hvb
                exact Eq.trans (Eq.symm hvb) hconst
              have how : ow = w := by
                simp only [Term.wellFormed, Op.validSignature, Bool.and_eq_true, beq_iff_eq,
                  List.map_cons, List.map_nil] at ht
                exact ht.1.1.symm
              subst how
              have hlt : LSHR ow av k < 2 ^ ow.bits := LSHR_lt ow av k
              rw [value_binary ν θ hθ ow (.lshr ow) a b ht, ha_val, hb_val]
              simp [interpretWith, interpretOp, MNat_of_lt hlt, value, interpretTerm, hlt]
      · exact value_app_lifted ν θ w (.lshr _) args ht hterms
    · rename_i ow base wc k _ heq
      split
      · rename_i hfit
        split
        · rename_i hzero
          generalize hmap : List.map liftInteger args = lifted at heq
          cases args with
          | nil => simp [heq] at hmap
          | cons a rest =>
            cases rest with
            | nil => simp [heq] at hmap
            | cons b rest =>
              cases rest with
              | cons c rest => simp [heq] at hmap
              | nil =>
                have hpair : liftInteger a = base ∧ liftInteger b = Term.const wc k := by
                  simp only [heq, List.map_cons, List.map_nil, List.cons.injEq, and_true] at hmap
                  exact hmap
                have ha : value ν θ base = value ν θ a := by
                  have hih := ih a (by simp) (hall a (by simp))
                  rw [hpair.1] at hih
                  exact hih
                have hb : value ν θ b = k := by
                  have hih := ih b (by simp) (hall b (by simp))
                  rw [hpair.2] at hih
                  have hfit' : wc = w ∧ base.width = w := by
                    simpa [Bool.and_eq_true, beq_iff_eq] using hfit
                  have hwc : wc = w := hfit'.1
                  have hklt : k < 2 ^ w.bits := by
                    have := liftInteger_wellFormed b (hall b (by simp))
                    rw [hpair.2, hwc] at this
                    simpa [Term.wellFormed] using this
                  exact Eq.trans (Eq.symm hih) (value_const ν θ wc k (by simpa [hwc] using hklt))
                have how : ow = w := by
                  have h := ht
                  simp only [Term.wellFormed, Op.validSignature, Bool.and_eq_true, beq_iff_eq,
                    List.map_cons, List.map_nil] at h
                  exact h.1.1.symm
                subst how
                have hk0 : k % ow.bits = 0 := by simpa [beq_iff_eq] using hzero
                have haw : a.width = ow := by
                  have hfit' : wc = ow ∧ base.width = ow := by
                    simpa [Bool.and_eq_true, beq_iff_eq] using hfit
                  have hw := liftInteger_width a
                  rw [hpair.1] at hw
                  exact Eq.trans (Eq.symm hw) hfit'.2
                rw [ha, value_binary ν θ hθ ow (.lshr ow) a b ht, hb]
                simp [interpretWith, interpretOp, LSHR, kShift, hk0, value_mod ν θ ow a haw]
        · rename_i hzero
          generalize hmap : List.map liftInteger args = lifted at heq
          cases args with
          | nil => simp [heq] at hmap
          | cons a rest =>
            cases rest with
            | nil => simp [heq] at hmap
            | cons b rest =>
              cases rest with
              | cons c rest => simp [heq] at hmap
              | nil =>
                have hpair : liftInteger a = base ∧ liftInteger b = Term.const wc k := by
                  simp only [heq, List.map_cons, List.map_nil, List.cons.injEq, and_true] at hmap
                  exact hmap
                have ha : value ν θ base = value ν θ a := by
                  have hih := ih a (by simp) (hall a (by simp))
                  rw [hpair.1] at hih
                  exact hih
                have hb : value ν θ b = k := by
                  have hih := ih b (by simp) (hall b (by simp))
                  rw [hpair.2] at hih
                  have hwc : wc = w := by
                    have hfit' : wc = w ∧ base.width = w := by
                      simpa [Bool.and_eq_true, beq_iff_eq] using hfit
                    exact hfit'.1
                  have hklt : k < 2 ^ w.bits := by
                    have := liftInteger_wellFormed b (hall b (by simp))
                    rw [hpair.2, hwc] at this
                    simpa [Term.wellFormed] using this
                  exact Eq.trans (Eq.symm hih) (value_const ν θ wc k (by simpa [hwc] using hklt))
                have how : ow = w := by
                  have h := ht
                  simp only [Term.wellFormed, Op.validSignature, Bool.and_eq_true, beq_iff_eq,
                    List.map_cons, List.map_nil] at h
                  exact h.1.1.symm
                subst how
                have haw : a.width = ow := by
                  have hfit' : wc = ow ∧ base.width = ow := by
                    simpa [Bool.and_eq_true, beq_iff_eq] using hfit
                  have hw := liftInteger_width a
                  rw [hpair.1] at hw
                  exact Eq.trans (Eq.symm hw) hfit'.2
                have hpow : 1 <<< (k % ow.bits) < 2 ^ ow.bits := by
                  simpa [kShift] using shift_pow_lt ow k
                have hbase_wf : base.wellFormed = true := by
                  rw [← hpair.1]
                  exact liftInteger_wellFormed a (hall a (by simp))
                have hbw : base.width = ow := by
                  have hfit' : wc = ow ∧ base.width = ow := by
                    simpa [Bool.and_eq_true, beq_iff_eq] using hfit
                  exact hfit'.2
                have hmul_wf :
                    (Term.app ow (.udiv ow 0) [base, .const ow (1 <<< (k % ow.bits))]).wellFormed = true := by
                  simp [Term.wellFormed, Term.width, termsWellFormed, Op.validSignature, hpow, hbase_wf]
                  exact hbw
                rw [value_binary ν θ hθ ow (.udiv ow 0) base (.const ow (1 <<< (k % ow.bits))) hmul_wf,
                  value_binary ν θ hθ ow (.lshr ow) a b ht, ha, hb]
                simp [interpretWith, interpretOp, value_const ν θ ow _ hpow,
                  LSHR_eq_UDIV ow (value ν θ a) k (by simpa [haw] using value_lt ν θ a),
                  kShift, value_mod ν θ ow a haw]
      · exact value_app_lifted ν θ w (.lshr ow) args ht hterms
    · rename_i q lhs rhs heq
      generalize hmap : List.map liftInteger args = lifted at heq
      cases args with
      | nil => simp [heq] at hmap
      | cons a rest =>
        cases rest with
        | nil => simp [heq] at hmap
        | cons b rest =>
          cases rest with
          | cons c rest => simp [heq] at hmap
          | nil =>
            have hpair : liftInteger a = lhs ∧ liftInteger b = rhs := by
              simp only [heq, List.map_cons, List.map_nil, List.cons.injEq, and_true] at hmap
              exact hmap
            split
            · rename_i hz
              have hz' := by simpa [Bool.and_eq_true, beq_iff_eq] using hz
              rcases hz' with ⟨⟨⟨hq, hzero⟩, _⟩, hrw⟩
              have hv0 : value ν θ a = 0 := by
                have hzl : value ν θ lhs = 0 :=
                  value_zero ν θ lhs (by simpa [termZero] using hzero)
                have hva := ih a (by simp) (hall a (by simp))
                rw [hpair.1] at hva
                exact Eq.trans hva.symm hzl
              have hbw : b.width = w := by
                have hw := liftInteger_width b
                rw [hpair.2] at hw
                exact Eq.trans hw.symm hrw
              have hvr : value ν θ rhs = value ν θ b := by
                have hvb := ih b (by simp) (hall b (by simp))
                rw [hpair.2] at hvb
                exact hvb
              subst hq
              rw [hvr, value_binary ν θ hθ w (.or w.bits) a b ht, hv0]
              simp [interpretWith, interpretOp, OR, Nat.zero_or, MNat_idempotent,
                value_mod ν θ w b hbw]
            · split
              · rename_i hz
                have hz' := by simpa [Bool.and_eq_true, beq_iff_eq] using hz
                rcases hz' with ⟨⟨⟨hq, hzero⟩, hlw⟩, _⟩
                have hv0 : value ν θ b = 0 := by
                  have hzl : value ν θ rhs = 0 :=
                    value_zero ν θ rhs (by simpa [termZero] using hzero)
                  have hvb := ih b (by simp) (hall b (by simp))
                  rw [hpair.2] at hvb
                  exact Eq.trans hvb.symm hzl
                have haw : a.width = w := by
                  have hw := liftInteger_width a
                  rw [hpair.1] at hw
                  exact Eq.trans hw.symm hlw
                have hvl : value ν θ lhs = value ν θ a := by
                  have hva := ih a (by simp) (hall a (by simp))
                  rw [hpair.1] at hva
                  exact hva
                subst hq
                rw [hvl, value_binary ν θ hθ w (.or w.bits) a b ht, hv0]
                simp [interpretWith, interpretOp, OR, Nat.or_zero, MNat_idempotent,
                  value_mod ν θ w a haw]
              · split
                case h_1 _ _ wa av wb bv _ _ =>
                  split
                  · rename_i hfold
                    have hf := by
                      simpa [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] using hfold
                    rcases hf with ⟨⟨⟨hwa, hwb⟩, _⟩, hqle⟩
                    have hav : av < 2 ^ w.bits := by
                      have h := liftInteger_wellFormed a (hall a (by simp))
                      rw [hpair.1, hwa] at h
                      simpa [Term.wellFormed] using h
                    have hbv : bv < 2 ^ w.bits := by
                      have h := liftInteger_wellFormed b (hall b (by simp))
                      rw [hpair.2, hwb] at h
                      simpa [Term.wellFormed] using h
                    have ha_val : value ν θ a = av := by
                      have hconst : value ν θ (.const w av) = av := value_const ν θ w av hav
                      have hva := ih a (by simp) (hall a (by simp))
                      rw [hpair.1, hwa] at hva
                      exact Eq.trans hva.symm hconst
                    have hb_val : value ν θ b = bv := by
                      have hconst : value ν θ (.const w bv) = bv := value_const ν θ w bv hbv
                      have hvb := ih b (by simp) (hall b (by simp))
                      rw [hpair.2, hwb] at hvb
                      exact Eq.trans hvb.symm hconst
                    have hlt : OR q av bv < 2 ^ w.bits :=
                      Nat.lt_of_lt_of_le (OR_lt q av bv) (Nat.pow_le_pow_right (by decide) hqle)
                    rw [show value ν θ (.const w (MNat w.bits (OR q av bv))) = OR q av bv from ?_]
                    · rw [value_binary ν θ hθ w (.or q) a b ht, ha_val, hb_val]
                      simp [interpretWith, interpretOp, MNat_of_lt hlt]
                    · rw [MNat_of_lt hlt]
                      exact value_const ν θ w (OR q av bv) hlt
                  · rw [← hmap]
                    exact value_app_lifted ν θ w (.or q) [a, b] ht hterms
                · split
                  case h_1 _ _ _ _ sa sb hsa hsb =>
                    split
                    · rename_i hdis
                      have hd := by
                        simpa [Bool.and_eq_true, decide_eq_true_eq] using hdis
                      rcases hd with ⟨⟨⟨⟨_, hqle⟩, hahi⟩, hbhi⟩, hdjb⟩
                      have hsig : a.width = w ∧ b.width = w := by
                        have h := ht
                        simp only [Term.wellFormed, Bool.and_eq_true] at h
                        have hs := h.1
                        simp only [Op.validSignature, List.map_cons, List.map_nil, List.all_cons,
                          List.all_nil, Bool.and_eq_true, beq_iff_eq] at hs
                        rcases hs with ⟨-, ⟨-, haw, hbw, -⟩⟩
                        exact ⟨haw, hbw⟩
                      have ha_wf : lhs.wellFormed = true := by
                        rw [← hpair.1]
                        exact liftInteger_wellFormed a (hall a (by simp))
                      have hb_wf : rhs.wellFormed = true := by
                        rw [← hpair.2]
                        exact liftInteger_wellFormed b (hall b (by simp))
                      have hlw : lhs.width = w := by
                        have hw := liftInteger_width a
                        rw [hpair.1] at hw
                        exact Eq.trans hw hsig.1
                      have hrw : rhs.width = w := by
                        have hw := liftInteger_width b
                        rw [hpair.2] at hw
                        exact Eq.trans hw hsig.2
                      have hadd_wf :
                          (Term.app w (.add w) [lhs, rhs]).wellFormed = true := by
                        simp [Term.wellFormed, termsWellFormed, Op.validSignature,
                          ha_wf, hb_wf, hlw, hrw]
                      have hspan_a := bitRange_value ν θ w lhs sa hsa
                      have hspan_b := bitRange_value ν θ w rhs sb hsb
                      have hqa : value ν θ lhs < 2 ^ q :=
                        Nat.lt_of_lt_of_le hspan_a.1 (Nat.pow_le_pow_right (by decide) hahi)
                      have hqb : value ν θ rhs < 2 ^ q :=
                        Nat.lt_of_lt_of_le hspan_b.1 (Nat.pow_le_pow_right (by decide) hbhi)
                      have hdj := by
                        simpa [BitSpan.disjoint, Bool.or_eq_true, decide_eq_true_eq] using hdjb
                      have hor_eq : OR q (value ν θ lhs) (value ν θ rhs) =
                          ADD w (value ν θ lhs) (value ν θ rhs) := by
                        rcases hdj with ((hempty | hempty) | hord) | hord
                        · have hge : sa.hi ≤ sa.lo := by
                            simpa [BitSpan.isEmpty, decide_eq_true_eq] using hempty
                          have hv0 := span_forces_zero (value ν θ lhs) sa.lo sa.hi
                            hspan_a.1 hspan_a.2 hge
                          exact OR_eq_ADD_of_split w q (value ν θ lhs) (value ν θ rhs) 0
                            hqle hqa hqb ⟨by simp [hv0], Nat.mod_one _⟩
                        · have hge : sb.hi ≤ sb.lo := by
                            simpa [BitSpan.isEmpty, decide_eq_true_eq] using hempty
                          have hv0 := span_forces_zero (value ν θ rhs) sb.lo sb.hi
                            hspan_b.1 hspan_b.2 hge
                          have hswap := OR_eq_ADD_of_split w q (value ν θ rhs) (value ν θ lhs) 0
                            hqle hqb hqa ⟨by simp [hv0], Nat.mod_one _⟩
                          have horc : OR q (value ν θ lhs) (value ν θ rhs) =
                              OR q (value ν θ rhs) (value ν θ lhs) := by
                            simp [OR, Nat.or_comm]
                          have haddc : ADD w (value ν θ lhs) (value ν θ rhs) =
                              ADD w (value ν θ rhs) (value ν θ lhs) := by
                            simp [ADD, Nat.add_comm]
                          rw [horc, haddc, hswap]
                        · have hlow : value ν θ lhs < 2 ^ sb.lo :=
                            Nat.lt_of_lt_of_le hspan_a.1 (Nat.pow_le_pow_right (by decide) hord)
                          exact OR_eq_ADD_of_split w q (value ν θ lhs) (value ν θ rhs) sb.lo
                            hqle hqa hqb ⟨hlow, hspan_b.2⟩
                        · have hlow : value ν θ rhs < 2 ^ sa.lo :=
                            Nat.lt_of_lt_of_le hspan_b.1 (Nat.pow_le_pow_right (by decide) hord)
                          have hswap := OR_eq_ADD_of_split w q (value ν θ rhs) (value ν θ lhs) sa.lo
                            hqle hqb hqa ⟨hlow, hspan_a.2⟩
                          have horc : OR q (value ν θ lhs) (value ν θ rhs) =
                              OR q (value ν θ rhs) (value ν θ lhs) := by
                            simp [OR, Nat.or_comm]
                          have haddc : ADD w (value ν θ lhs) (value ν θ rhs) =
                              ADD w (value ν θ rhs) (value ν θ lhs) := by
                            simp [ADD, Nat.add_comm]
                          rw [horc, haddc, hswap]
                      have ha_eq : value ν θ a = value ν θ lhs := by
                        have hva := ih a (by simp) (hall a (by simp))
                        rw [hpair.1] at hva
                        exact hva.symm
                      have hb_eq : value ν θ b = value ν θ rhs := by
                        have hvb := ih b (by simp) (hall b (by simp))
                        rw [hpair.2] at hvb
                        exact hvb.symm
                      have hA : ADD w (value ν θ lhs) (value ν θ rhs) < 2 ^ w.bits := by
                        unfold ADD
                        exact MNat_lt _ _
                      have hO : OR q (value ν θ lhs) (value ν θ rhs) < 2 ^ w.bits :=
                        Nat.lt_of_lt_of_le (OR_lt q _ _) (Nat.pow_le_pow_right (by decide) hqle)
                      rw [value_binary ν θ hθ w (.add w) lhs rhs hadd_wf,
                        value_binary ν θ hθ w (.or q) a b ht]
                      simp [interpretWith, interpretOp, ha_eq, hb_eq, MNat_of_lt hA, MNat_of_lt hO,
                        hor_eq]
                    · rw [← hmap]
                      exact value_app_lifted ν θ w (.or q) [a, b] ht hterms
                  case h_2 =>
                    rw [← hmap]
                    exact value_app_lifted ν θ w (.or q) [a, b] ht hterms
    · exact value_app_lifted ν θ w _ args ht hterms

end SolvePreservation

/-- R2 through R6 preserve interpretation under a complete external environment. -/
theorem normalizeAlgebra_interpret (ν : Var → Nat) (θ : ExternalInterpretation)
    (hθ : θ.Total) (t : Term) (ht : t.wellFormed = true) :
    interpretTerm ν θ (normalizeAlgebra t) = interpretTerm ν θ t := by
  have hn := (normalizeAlgebra_wellFormed t ht).1
  rw [SolvePreservation.meaning ν θ hθ _ hn, SolvePreservation.meaning ν θ hθ t ht]
  apply congrArg some
  unfold normalizeAlgebra
  rw [SolvePreservation.rebuildSpine_value ν θ hθ]
  · rw [SolvePreservation.sorted_atom_sum]
    exact (SolvePreservation.additiveSpine_value ν θ hθ t.width t ht rfl).symm
  · intro a ha
    exact SolvePreservation.additiveSpine_atoms_valid t.width t ht rfl a
      (List.mem_mergeSort.mp ha)

/-- Concrete shifts and disjoint ors preserve interpretation. -/
theorem liftInteger_interpret (ν : Var → Nat) (θ : ExternalInterpretation)
    (hθ : θ.Total) (t : Term) (ht : t.wellFormed = true) :
    interpretTerm ν θ (liftInteger t) = interpretTerm ν θ t := by
  rw [SolvePreservation.meaning ν θ hθ (liftInteger t) (liftInteger_wellFormed t ht),
    SolvePreservation.meaning ν θ hθ t ht]
  exact congrArg some (SolvePreservation.liftInteger_value ν θ hθ t ht)

/-- R1 through R6, together with the integer-domain shift and disjoint-or
rewrites, preserve every well-formed term. -/
theorem solve_interpret (ν : Var → Nat) (θ : ExternalInterpretation)
    (hθ : θ.Total) (t : Term) (ht : t.wellFormed = true) :
    interpretTerm ν θ (solve t) = interpretTerm ν θ t := by
  simp only [solve, ht, ↓reduceIte]
  rw [foldClosed_interpret,
    normalizeAlgebra_interpret ν θ hθ _
      (liftInteger_wellFormed _ (foldClosed_wellFormed t ht)),
    liftInteger_interpret ν θ hθ _ (foldClosed_wellFormed t ht),
    foldClosed_interpret]

end Core
