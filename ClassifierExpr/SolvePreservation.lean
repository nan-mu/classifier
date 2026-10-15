import ClassifierExpr.Semantics

namespace ClassifierExpr

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

/-- R1 through R6 preserve every well-formed term, not just closed inputs. -/
theorem solve_interpret (ν : Var → Nat) (θ : ExternalInterpretation)
    (hθ : θ.Total) (t : Term) (ht : t.wellFormed = true) :
    interpretTerm ν θ (solve t) = interpretTerm ν θ t := by
  simp only [solve, ht, ↓reduceIte]
  rw [foldClosed_interpret,
    normalizeAlgebra_interpret ν θ hθ _ (foldClosed_wellFormed t ht),
    foldClosed_interpret]

end ClassifierExpr
