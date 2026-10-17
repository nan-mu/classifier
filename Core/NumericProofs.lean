import Std.Tactic
import Core.Numeric

namespace Core

@[simp] theorem MNat_idempotent (q a : Nat) : MNat q (MNat q a) = MNat q a := by
  simp [MNat]

theorem MNat_lt (q a : Nat) : MNat q a < 2 ^ q := by
  simpa [MNat, Nat.shiftLeft_eq] using Nat.mod_lt a (Nat.two_pow_pos q)

@[simp] theorem MNat_of_lt {q a : Nat} (h : a < 2 ^ q) : MNat q a = a := by
  exact Nat.mod_eq_of_lt (by simpa [Nat.shiftLeft_eq] using h)

theorem M_lt (q : Nat) (z : Int) : M q z < 2 ^ q := by
  have hp : (0 : Int) < (1 : Int) <<< q := by
    simp only [Int.shiftLeft_eq, Int.one_mul]
    exact Int.pow_pos (by decide)
  have hn := Int.emod_nonneg z (Int.ne_of_gt hp)
  have hl := Int.emod_lt_of_pos z hp
  simp only [M, show ¬z % ((1 : Int) <<< q) < 0 by omega, ↓reduceIte]
  apply (Int.toNat_lt hn).mpr
  simpa [Int.shiftLeft_eq] using hl

@[simp] theorem M_cast (q : Nat) (z : Int) :
    (M q z : Int) = z % (2 : Int) ^ q := by
  have hp : (0 : Int) < (1 : Int) <<< q := by
    simp only [Int.shiftLeft_eq, Int.one_mul]
    exact Int.pow_pos (by decide)
  have hn := Int.emod_nonneg z (Int.ne_of_gt hp)
  simp only [M, show ¬z % ((1 : Int) <<< q) < 0 by omega, ↓reduceIte]
  simpa [Int.shiftLeft_eq] using Int.toNat_of_nonneg hn
@[simp] theorem M_natCast (q a : Nat) : M q (a : Int) = MNat q a := by
  apply Int.ofNat_inj.mp
  simp only [M_cast, MNat, Nat.shiftLeft_eq, Nat.one_mul, Int.natCast_emod,
    Int.natCast_pow, Int.cast_ofNat_Int]

@[simp] theorem M_s (q a : Nat) : M q (s q a) = MNat q a := by
  apply Int.ofNat_inj.mp
  rw [M_cast]
  have hmod : (MNat q a : Int) % (2 : Int) ^ q = (MNat q a : Int) := by
    rw [← M_cast, M_natCast, MNat_idempotent]
  dsimp only [s]
  by_cases h : MNat q a < (1 : Nat) <<< (q - 1)
  · rw [if_pos h]
    exact hmod
  · rw [if_neg h]
    simp only [Nat.shiftLeft_eq, Nat.one_mul, Int.ofNat_eq_natCast,
      Int.natCast_pow, Int.cast_ofNat_Int]
    rw [Int.sub_emod, Int.emod_self, Int.sub_zero, Int.emod_emod]
    exact hmod

/-- Floor division lies between its two adjacent multiples. -/
theorem floor_quotient_interval (x d : Int) (hd : 0 < d) :
    (x / d) * d ≤ x ∧ x < (x / d + 1) * d := by
  exact ⟨Int.ediv_mul_le _ (Int.ne_of_gt hd), Int.lt_ediv_add_one_mul_self _ hd⟩

/-- Floor division is the unique quotient whose adjacent multiples enclose the input. -/
theorem floor_quotient_unique (x d quotient : Int) (hd : 0 < d)
    (lower : quotient * d ≤ x) (upper : x < (quotient + 1) * d) :
    x / d = quotient := by
  have hl : quotient ≤ x / d := (Int.le_ediv_iff_mul_le hd).mpr lower
  have hu : x / d < quotient + 1 := (Int.ediv_lt_iff_lt_mul hd).mpr upper
  omega

theorem shift_divisor_positive (k : Nat) : (0 : Int) < Int.ofNat (1 <<< k) := by
  have hp : 0 < (1 : Nat) <<< k := by
    simpa [Nat.shiftLeft_eq] using Nat.two_pow_pos k
  exact Int.natCast_pos.mpr hp

/-- This is the signed quotient before re-encoding as a machine word. -/
theorem ASHR_quotient_interval (w : Width) (a b : Nat) :
    let x := s w.bits a
    let d := Int.ofNat (1 <<< kShift w b)
    (x / d) * d ≤ x ∧ x < (x / d + 1) * d := by
  dsimp
  exact floor_quotient_interval _ _ (shift_divisor_positive (kShift w b))

theorem ASHR_quotient_unique (w : Width) (a b : Nat) (quotient : Int)
    (lower : quotient * Int.ofNat (1 <<< kShift w b) ≤ s w.bits a)
    (upper : s w.bits a < (quotient + 1) * Int.ofNat (1 <<< kShift w b)) :
    ASHR w a b = M w.bits quotient := by
  unfold ASHR
  rw [floor_quotient_unique _ _ _ (shift_divisor_positive _) lower upper]

@[simp] theorem UDIV_zero (w : Width) (z a : Nat) :
    UDIV w z a 0 = MNat w.bits z := by simp [UDIV, MNat]

@[simp] theorem UREM_zero (w : Width) (a : Nat) :
    UREM w a 0 = MNat w.bits a := by simp [UREM, MNat]

@[simp] theorem SDIV_zero (w : Width) (z a : Nat) :
    SDIV w z a 0 = MNat w.bits z := by
  cases w <;> simp [SDIV, s, MNat, Width.bits]

@[simp] theorem SREM_zero (w : Width) (a : Nat) :
    SREM w a 0 = MNat w.bits a := by
  cases w <;> simp [SREM, s, MNat, Width.bits]

@[simp] theorem signed_mask (w : Width) : s w.bits w.mask = -1 := by
  cases w <;> decide

@[simp] theorem ASHR_mask (w : Width) (b : Nat) :
    ASHR w w.mask b = w.mask := by
  have hp := shift_divisor_positive (kShift w b)
  have hs := Int.sign_eq_one_of_pos hp
  rw [ASHR, signed_mask, Int.neg_one_ediv, hs]
  cases w <;> decide

@[simp] theorem ASHR_zero_shift (w : Width) (a : Nat) :
    ASHR w a 0 = MNat w.bits a := by
  simp [ASHR, kShift]

@[simp] theorem SELECTEQ_equal (w : Width) (a yes no : Nat) :
    SELECTEQ w a a yes no = MNat w.bits yes := by simp [SELECTEQ]

@[simp] theorem SELECTEQ_different (w : Width) (a b yes no : Nat)
    (h : MNat w.bits a ≠ MNat w.bits b) :
    SELECTEQ w a b yes no = MNat w.bits no := by simp [SELECTEQ, h]


theorem M_add (q : Nat) (a b : Int) :
    M q (a + b) = MNat q (M q a + M q b) := by
  apply Int.ofNat_inj.mp
  simp only [M_cast, MNat, Nat.shiftLeft_eq, Nat.one_mul, Int.natCast_emod,
    Int.natCast_add, Int.natCast_pow]
  exact Int.add_emod a b _

@[simp] theorem ADD_zero (w : Width) (a : Nat) : ADD w a 0 = MNat w.bits a := by
  simp [ADD]

theorem ADD_assoc (w : Width) (a b c : Nat) :
    ADD w (ADD w a b) c = ADD w a (ADD w b c) := by
  simp [ADD, MNat, Nat.add_assoc]

theorem ADD_comm (w : Width) (a b : Nat) : ADD w a b = ADD w b a := by
  simp [ADD, Nat.add_comm]

@[simp] theorem SUB_self (w : Width) (a : Nat) : SUB w a a = 0 := by
  simp [SUB, M]

theorem SUB_eq_ADD_NEG (w : Width) (a b : Nat) :
    SUB w a b = ADD w a (NEG w b) := by
  unfold SUB
  rw [Int.sub_eq_add_neg, M_add]
  change MNat w.bits (M w.bits (MNat w.bits a : Int) + NEG w b) =
    MNat w.bits (a + NEG w b)
  rw [M_natCast, MNat_idempotent]
  simp only [MNat, Nat.mod_add_mod]

@[simp] theorem XOR_self (q a : Nat) : XOR q a a = 0 := by
  simp [XOR, MNat]

@[simp] theorem OR_zero (q a : Nat) : OR q a 0 = MNat q a := by simp [OR]
@[simp] theorem XOR_zero (q a : Nat) : XOR q a 0 = MNat q a := by simp [XOR]

@[simp] theorem AND_mask (w : Width) (a : Nat) :
    AND w.bits a w.mask = MNat w.bits a := by
  simp [AND, Width.mask, MNat, Nat.shiftLeft_eq]

@[simp] theorem MULLO_one (w : Width) (a : Nat) : MULLO w a 1 = MNat w.bits a := by
  simp [MULLO]

@[simp] theorem SHL_zero_shift (w : Width) (a : Nat) :
    SHL w a 0 = MNat w.bits a := by simp [SHL, kShift]

@[simp] theorem LSHR_zero_shift (w : Width) (a : Nat) :
    LSHR w a 0 = MNat w.bits a := by simp [LSHR, kShift]

@[simp] theorem SDIV_overflow (w : Width) (zeroResult : Nat) :
    SDIV w zeroResult (1 <<< (w.bits - 1)) w.mask = 1 <<< (w.bits - 1) := by
  unfold SDIV
  rw [signed_mask]
  change M w.bits (TQ (s w.bits (1 <<< (w.bits - 1))) (-1)) =
    1 <<< (w.bits - 1)
  cases w <;> decide

@[simp] theorem SREM_overflow (w : Width) :
    SREM w (1 <<< (w.bits - 1)) w.mask = 0 := by
  cases w <;> decide

end Core
