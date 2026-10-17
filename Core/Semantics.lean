import Core.Expr

namespace Core

private theorem interpretWith_total (θ : ExternalInterpretation) (hθ : θ.Total)
    (w : Width) (op : Op) (widths : List Width) (values : List Nat)
    (hs : op.validSignature w widths = true) (hl : values.length = widths.length) :
    ∃ v, interpretWith θ w op values = some v := by
  cases op
  case externalResult event lane =>
    exact hθ.1 w event lane values
  case inputByte resource =>
    have hw : widths.length = 2 := by
      cases widths with
      | nil => simp [Op.validSignature] at hs
      | cons base widths =>
        cases widths with
        | nil => simp [Op.validSignature] at hs
        | cons address widths =>
          cases widths with
          | nil => rfl
          | cons extra widths => simp [Op.validSignature] at hs
    have hv : values.length = 2 := hl.trans hw
    cases values with
    | nil => simp at hv
    | cons base values =>
      cases values with
      | nil => simp at hv
      | cons address values =>
        cases values with
        | nil => simpa [interpretWith] using hθ.2 resource base address
        | cons extra values => simp at hv
  case packetRead bytes ending =>
    cases values with
    | nil =>
      cases widths with
      | nil => simp [Op.validSignature] at hs
      | cons width rest => simp at hl
    | cons value rest => exact ⟨value, rfl⟩
  all_goals
    cases values with
    | nil => simp_all [Op.validSignature]
    | cons a values =>
      cases values with
      | nil => simp_all [Op.validSignature, interpretWith, interpretOp]
      | cons b values =>
        cases values with
        | nil => simp_all [Op.validSignature, interpretWith, interpretOp]
        | cons c values =>
          cases values with
          | nil => simp_all [Op.validSignature]
          | cons d values =>
            cases values <;> simp_all [Op.validSignature, interpretWith, interpretOp]

mutual
  /-- A complete external interpretation is defined on every structurally valid term. -/
  theorem interpretTerm_total (ν : Var → Nat) (θ : ExternalInterpretation)
      (hθ : θ.Total) (t : Term) (ht : t.wellFormed = true) :
      ∃ v, interpretTerm ν θ t = some v := by
    cases t with
    | const w c =>
      have hc : c < 2 ^ w.bits := by simpa only [Term.wellFormed, decide_eq_true_eq] using ht
      exact ⟨c, by simp [interpretTerm, hc]⟩
    | var w n => exact ⟨MNat w.bits (ν ⟨w, n, none⟩), by simp [interpretTerm]⟩
    | regVar event r =>
      have hr : (r.valid && r.kind == .real) = true := by
        simpa only [Term.wellFormed] using ht
      exact ⟨MNat r.width.bits (ν ⟨r.width, r.alpha, some (event, r)⟩),
        by simp [interpretTerm, hr]⟩
    | app w op args =>
      have hvalid : op.validSignature w (args.map Term.width) = true ∧
          termsWellFormed args = true := by
        simpa only [Term.wellFormed, Bool.and_eq_true] using ht
      obtain ⟨hs, ha⟩ := hvalid
      obtain ⟨values, hv, hl⟩ := interpretTerms_total ν θ hθ args ha
      obtain ⟨v, hop⟩ := interpretWith_total θ hθ w op (args.map Term.width) values hs
        (by simpa using hl)
      exact ⟨MNat w.bits v, by simp [interpretTerm, hs, hv, hop]⟩
  termination_by sizeOf t

  theorem interpretTerms_total (ν : Var → Nat) (θ : ExternalInterpretation)
      (hθ : θ.Total) (ts : List Term) (ht : termsWellFormed ts = true) :
      ∃ values, interpretTerms ν θ ts = some values ∧ values.length = ts.length := by
    cases ts with
    | nil => exact ⟨[], by simp [interpretTerms], rfl⟩
    | cons t ts =>
      have hvalid : t.wellFormed = true ∧ termsWellFormed ts = true := by
        simpa only [termsWellFormed, Bool.and_eq_true] using ht
      obtain ⟨hh, ht⟩ := hvalid
      obtain ⟨v, hv⟩ := interpretTerm_total ν θ hθ t hh
      obtain ⟨values, hvalues, hl⟩ := interpretTerms_total ν θ hθ ts ht
      exact ⟨v :: values, by simp [interpretTerms, hv, hvalues], by simp [hl]⟩
  termination_by sizeOf ts
end

/-- Undefined partial environments are not implicitly promoted to complete meanings. -/
theorem interpretTerm_external_missing (ν : Var → Nat) (θ : ExternalInterpretation)
    (w : Width) (event lane : Nat) (args : List Term) (values : List Nat)
    (hs : (Op.externalResult event lane).validSignature w (args.map Term.width) = true)
    (ha : interpretTerms ν θ args = some values)
    (hm : θ.externalResult w event lane values = none) :
    interpretTerm ν θ (.app w (.externalResult event lane) args) = none := by
  simp [interpretTerm, hs, ha, interpretWith, hm]

end Core
