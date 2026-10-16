import ClassifierExpr.Insn
import ClassifierExpr.Term
import ClassifierExpr.Op
import ClassifierExpr.Expr
import ClassifierExpr.Parse
import ClassifierExpr.Virtual

namespace ClassifierExpr

/-! Carrier-erased observation keys; semantic scope and premises are owned by
`doc/Predicate/跨架构谓词.md`. Equality is deliberately not injective. -/

inductive CrossOp where
  | add | sub | mullo | neg | id | shl | lshr | ashr | ltu | lts
  | udiv (bits zeroResult : Nat) | urem (bits : Nat)
  | sdiv (bits zeroResult : Nat) | srem (bits : Nat)
  | mulh (bits : Nat) | mulhu (bits : Nat) | mulhsu (bits : Nat)
  | selectEq (bits : Nat)
  | and | or | xor
  | low (q : Nat) | extract (offset length : Nat)
  | zext (q input : Nat) | sext (q input : Nat) | bswap (q input : Nat)
  | inputByte (resource : Nat) | mergeLow (q bits : Nat)
  | linear
  /-- Checked compound byte cell; args carry packet, offset, end-cell, strictness,
  and byte index. packetRead is the non-erased malformed annotation case. -/
  | packetReg (bytes : Nat)
  | packetRead (bytes endCtx : Nat)
  deriving DecidableEq, BEq, ReflBEq, LawfulBEq, Repr, Ord

inductive CrossTerm where
  | c (z : Int)
  | var (name : Nat)
  | reg (kind : RegKind) (alpha : Nat)
  | app (op : CrossOp) (args : List CrossTerm)
  | external (lane : Nat) (args : List CrossTerm)
  deriving Repr

mutual
  private def crossTermDecEq : (a b : CrossTerm) → Decidable (a = b)
    | .c x, .c y => decidable_of_iff (x = y) (by simp)
    | .var x, .var y => decidable_of_iff (x = y) (by simp)
    | .reg k x, .reg l y => decidable_of_iff (k = l ∧ x = y) (by simp)
    | .app f xs, .app g ys =>
      letI := crossListDecEq xs ys
      decidable_of_iff (f = g ∧ xs = ys) (by simp)
    | .external x xs, .external y ys =>
      letI := crossListDecEq xs ys
      decidable_of_iff (x = y ∧ xs = ys) (by simp)
    | .c _, .var _ | .c _, .reg _ _ | .c _, .app _ _ | .c _, .external _ _
    | .var _, .c _ | .var _, .reg _ _ | .var _, .app _ _ | .var _, .external _ _
    | .reg _ _, .c _ | .reg _ _, .var _ | .reg _ _, .app _ _ | .reg _ _, .external _ _
    | .app _ _, .c _ | .app _ _, .var _ | .app _ _, .reg _ _ | .app _ _, .external _ _
    | .external _ _, .c _ | .external _ _, .var _
    | .external _ _, .reg _ _ | .external _ _, .app _ _ => .isFalse (by intro h; cases h)
  termination_by a b => sizeOf a + sizeOf b

  private def crossListDecEq : (xs ys : List CrossTerm) → Decidable (xs = ys)
    | [], [] => .isTrue rfl
    | [], _ :: _ | _ :: _, [] => .isFalse (by intro h; cases h)
    | x :: xs, y :: ys =>
      letI := crossTermDecEq x y
      letI := crossListDecEq xs ys
      decidable_of_iff (x = y ∧ xs = ys) (by simp)
  termination_by xs ys => sizeOf xs + sizeOf ys
end

instance : DecidableEq CrossTerm := crossTermDecEq
instance : BEq CrossTerm := ⟨fun a b => decide (a = b)⟩
instance : LawfulBEq CrossTerm where
  eq_of_beq := of_decide_eq_true
  rfl := of_decide_eq_self_eq_true _

private def crossOp : Op → CrossOp
  | .add _ => .add | .sub _ => .sub | .mullo _ => .mullo
  | .udiv w z => .udiv w.bits z | .urem w => .urem w.bits
  | .sdiv w z => .sdiv w.bits z | .srem w => .srem w.bits
  | .mulh w => .mulh w.bits | .mulhu w => .mulhu w.bits
  | .mulhsu w => .mulhsu w.bits | .selectEq w => .selectEq w.bits
  | .neg _ => .neg | .id _ => .id | .shl _ => .shl
  | .lshr _ => .lshr | .ashr _ => .ashr | .ltu _ => .ltu | .lts _ => .lts
  | .and _ => .and | .or _ => .or | .xor _ => .xor
  | .low q _ => .low q | .extract o n _ => .extract o n
  | .zext q _ v => .zext q v | .sext q _ v => .sext q v
  | .bswap q v => .bswap q v | .inputByte r => .inputByte r
  | .mergeLow q v => .mergeLow q v
  | .packetRead bytes ending => .packetRead bytes ending
  | .externalResult _ _ => .id -- handled separately, never emitted

private def identityCast : Op → Bool
  | .id _ => true
  | .extract o n v => o == 0 && n == v
  | .zext q _ v => q ≤ v
  | .low q v => q == v
  | .sext q w v => q == v && v == w.bits
  | .bswap q v => q == 8 && v == 8
  | _ => false

private def triangle (n : Nat) : Nat := n * (n + 1) / 2

/-- Largest pairing diagonal below n, by bounded binary search. -/
private def pairDiagonal (n lo hi : Nat) : Nat :=
  if h : lo < hi then
    let mid := (lo + hi + 1) / 2
    if triangle mid ≤ n then pairDiagonal n mid hi
    else pairDiagonal n lo (mid - 1)
  else lo
termination_by hi - lo
decreasing_by all_goals omega

/-- Map alpha pairs a dynamic lookup namespace with a byte offset.
Retain the offset, not the namespace; other kinds keep their static alpha. -/
private def crossRegAlpha (r : Reg) : Nat :=
  if r.kind == .map then r.alpha - triangle (pairDiagonal r.alpha 0 r.alpha)
  else r.alpha

private theorem triangle_mono {a b : Nat} (h : a ≤ b) :
    triangle a ≤ triangle b :=
  Nat.div_le_div_right (Nat.mul_le_mul h (Nat.add_le_add_right h 1))

private theorem triangle_succ (n : Nat) :
    triangle (n + 1) = triangle n + (n + 1) := by
  have h : (n + 1) * (n + 1 + 1) = n * (n + 1) + 2 * (n + 1) := by
    simp only [Nat.add_mul, Nat.mul_add, Nat.one_mul, Nat.mul_one]
    omega
  unfold triangle
  rw [h, Nat.add_mul_div_left _ _ (by decide)]

private theorem triangle_ge (n : Nat) : n ≤ triangle n := by
  induction n with
  | zero => simp [triangle]
  | succ n ih => rw [triangle_succ]; omega

private theorem pairDiagonal_eq_of_interval (n lo hi d : Nat)
    (hlo : lo ≤ d) (hhi : d ≤ hi)
    (hbelow : triangle d ≤ n) (habove : n < triangle (d + 1)) :
    pairDiagonal n lo hi = d := by
  unfold pairDiagonal
  split
  · rename_i h
    dsimp only
    split
    · rename_i hm
      have hd : (lo + hi + 1) / 2 ≤ d := by
        by_cases hn : (lo + hi + 1) / 2 ≤ d
        · exact hn
        · have ht := triangle_mono (a := d + 1) (b := (lo + hi + 1) / 2)
            (by omega)
          omega
      exact pairDiagonal_eq_of_interval n _ hi d hd hhi hbelow habove
    · rename_i hm
      have hd : d ≤ (lo + hi + 1) / 2 - 1 := by
        by_cases hn : d ≤ (lo + hi + 1) / 2 - 1
        · exact hn
        · have ht := triangle_mono (a := (lo + hi + 1) / 2) (b := d)
            (by omega)
          omega
      exact pairDiagonal_eq_of_interval n lo _ d hlo hd hbelow habove
  · omega
termination_by hi - lo
decreasing_by all_goals omega

private theorem pairDiagonal_pair (resource offset : Nat) :
    pairDiagonal (triangle (resource + offset) + offset) 0
      (triangle (resource + offset) + offset) = resource + offset := by
  apply pairDiagonal_eq_of_interval
  · omega
  · have h := triangle_ge (resource + offset); omega
  · omega
  · rw [triangle_succ]; omega

/-- Arithmetic offset recovery only: no Map identity or frozen-key correspondence
is inferred from erasing the lookup namespace. -/
theorem crossRegAlpha_mapWord (resource offset : Nat) :
    crossRegAlpha (Reg.mapWord resource offset) = offset := by
  change triangle (resource + offset) + offset -
    triangle (pairDiagonal (triangle (resource + offset) + offset) 0
      (triangle (resource + offset) + offset)) = offset
  rw [pairDiagonal_pair]
  omega

theorem crossRegAlpha_mapDword (resource offset : Nat) :
    crossRegAlpha (Reg.mapDword resource offset) = offset := by
  change triangle (resource + offset) + offset -
    triangle (pairDiagonal (triangle (resource + offset) + offset) 0
      (triangle (resource + offset) + offset)) = offset
  rw [pairDiagonal_pair]
  omega

/-- Generation-side lookup witness, before query namespaces are erased. -/
def MapRegisterTie (Pg : List Predicate) (r : Reg) (map : Term)
    (key : List Term) (offset : Nat) : Prop :=
  ∃ event, (r = Reg.mapWord event offset ∨ r = Reg.mapDword event offset) ∧
    LookupTie Pg event map key

theorem mapRegisterTie_offset (Pg : List Predicate) (r : Reg) (map : Term)
    (key : List Term) (offset : Nat) (h : MapRegisterTie Pg r map key offset) :
    crossRegAlpha r = offset := by
  rcases h with ⟨event, hw | hd, _⟩
  · rw [hw, crossRegAlpha_mapWord]
  · rw [hd, crossRegAlpha_mapDword]

theorem mapRegisterTie_same_slot (Pg₁ Pg₂ : List Predicate) (r₁ r₂ : Reg)
    (map : Term) (key : List Term) (offset₁ offset₂ : Nat)
    (h₁ : MapRegisterTie Pg₁ r₁ map key offset₁)
    (h₂ : MapRegisterTie Pg₂ r₂ map key offset₂)
    (he : crossRegAlpha r₁ = crossRegAlpha r₂) :
    (map, key, offset₁) = (map, key, offset₂) := by
  have ho : offset₁ = offset₂ :=
    (mapRegisterTie_offset Pg₁ r₁ map key offset₁ h₁).symm.trans
      (he.trans (mapRegisterTie_offset Pg₂ r₂ map key offset₂ h₂))
  rw [ho]

theorem mapRegisterTie_distinct_slots (Pg₁ Pg₂ : List Predicate) (r₁ r₂ : Reg)
    (map : Term) (key : List Term) (offset₁ offset₂ : Nat)
    (h₁ : MapRegisterTie Pg₁ r₁ map key offset₁)
    (h₂ : MapRegisterTie Pg₂ r₂ map key offset₂)
    (he : crossRegAlpha r₁ ≠ crossRegAlpha r₂) :
    (map, key, offset₁) ≠ (map, key, offset₂) := by
  intro hs
  have ho : offset₁ = offset₂ := congrArg (fun s : Term × List Term × Nat => s.2.2) hs
  exact he ((mapRegisterTie_offset Pg₁ r₁ map key offset₁ h₁).trans
    (ho.trans (mapRegisterTie_offset Pg₂ r₂ map key offset₂ h₂).symm))

theorem crossRegAlpha_static (r : Reg)
    (h : r.kind = .real ∨ r.kind = .stack ∨ r.kind = .context) :
    crossRegAlpha r = r.alpha := by
  rcases h with h | h | h <;> simp [crossRegAlpha, h]

theorem crossRegAlpha_static_injective (r₁ r₂ : Reg)
    (h₁ : r₁.kind = .real ∨ r₁.kind = .stack ∨ r₁.kind = .context)
    (h₂ : r₂.kind = r₁.kind) (he : crossRegAlpha r₁ = crossRegAlpha r₂) :
    r₁.alpha = r₂.alpha := by
  have hk₂ : r₂.kind = .real ∨ r₂.kind = .stack ∨ r₂.kind = .context := by
    rw [h₂]
    exact h₁
  rw [crossRegAlpha_static r₁ h₁, crossRegAlpha_static r₂ hk₂] at he
  exact he

/-- Lane zero keeps at most the first two ABI arguments; for Map helpers these
are the helper id and Map term. Other helper kinds need not share that meaning. -/
private def abiPrefix (lane : Nat) (args : List Term) : List Term :=
  if lane == 0 then args.take 2 else args

private theorem abiPrefix_sizeOf_le (lane : Nat) (args : List Term) :
    sizeOf (abiPrefix lane args) ≤ sizeOf args := by
  unfold abiPrefix
  split
  · cases args with
    | nil => simp
    | cons a args =>
      cases args with
      | nil => simp
      | cons b args => cases args <;> simp +arith [List.take]
  · exact Nat.le_refl _

theorem abiPrefix_zero_take (args : List Term) : abiPrefix 0 args = args.take 2 := rfl

theorem abiPrefix_zero_three (a b c : Term) : abiPrefix 0 [a,b,c] = [a,b] := rfl

theorem abiPrefix_zero_cons_cons (a b : Term) (tail : List Term) :
    abiPrefix 0 (a :: b :: tail) = [a, b] := rfl

theorem abiPrefix_zero_append (ret key : List Term) (h : 2 ≤ ret.length) :
    abiPrefix 0 (ret ++ key) = abiPrefix 0 ret := by
  simp only [abiPrefix_zero_take, List.take_append, Nat.sub_eq_zero_of_le h,
    List.take_zero, List.append_nil]

theorem abiPrefix_zero_singleton (a : Term) : abiPrefix 0 [a] = [a] := rfl

theorem abiPrefix_zero_length_le (args : List Term) : (abiPrefix 0 args).length ≤ 2 := by
  cases args with
  | nil => simp [abiPrefix]
  | cons a args =>
    cases args with
    | nil => simp [abiPrefix]
    | cons b args => simp [abiPrefix, List.take]

theorem abiPrefix_idempotent (lane : Nat) (args : List Term) :
    abiPrefix lane (abiPrefix lane args) = abiPrefix lane args := by
  by_cases h : lane = 0
  · subst lane
    cases args with
    | nil => rfl
    | cons a args =>
      cases args with
      | nil => rfl
      | cons b args => simp [abiPrefix, List.take]
  · simp [abiPrefix, h]

/-- Total structural order: constructor rank, then constructor fields in order. -/
private def crossRank : CrossTerm → Nat
  | .c _ => 0 | .var _ => 1 | .reg _ _ => 2 | .app _ _ => 3 | .external _ _ => 4

mutual
  private def crossCompare (a b : CrossTerm) : Ordering :=
    match a, b with
    | .c x, .c y => compare x y
    | .var x, .var y => compare x y
    | .reg k x, .reg l y =>
      match compare (regRank k) (regRank l) with
      | .eq => compare x y | o => o
    | .app f xs, .app g ys =>
      match compare f g with
      | .eq => crossCompareList xs ys | o => o
    | .external x xs, .external y ys =>
      match compare x y with
      | .eq => crossCompareList xs ys | o => o
    | _, _ => compare (crossRank a) (crossRank b)
  termination_by sizeOf a + sizeOf b

  private def crossCompareList (xs ys : List CrossTerm) : Ordering :=
    match xs, ys with
    | [], [] => .eq | [], _ => .lt | _, [] => .gt
    | x :: xs, y :: ys =>
      match crossCompare x y with
      | .eq => crossCompareList xs ys | o => o
  termination_by sizeOf xs + sizeOf ys

  private def regRank : RegKind → Nat
    | .real => 0 | .stack => 1 | .map => 2 | .packet => 3 | .context => 4
end

/- Width of the represented observation, not of its original carrier.
Variables require the generation-side common 32-bit value premise (CP-Q). -/
mutual
  def CrossTerm.compareBits : CrossTerm → Nat
    | .c z => if -(2^31 : Int) ≤ z && z < 2^31 then 32 else 64
    | .var _ | .reg _ _ => 32
    | .app op args =>
      match op with
      | .low q | .extract _ q | .zext q _ | .sext q _ | .bswap q _ => q
      | .mergeLow _ q => q
      | .udiv bits _ | .urem bits | .sdiv bits _ | .srem bits
      | .mulh bits | .mulhu bits | .mulhsu bits | .selectEq bits => bits
      | .inputByte _ | .packetReg _ => 8
      | .ltu | .lts => 1
      | _ => max 32 (crossBits args)
    | .external _ args => max 32 (crossBits args)
  termination_by t => sizeOf t

  private def crossBits : List CrossTerm → Nat
    | [] => 0
    | t :: ts => max t.compareBits (crossBits ts)
  termination_by ts => sizeOf ts
end
private def crossUnary (op : Op) (x : CrossTerm) : CrossTerm :=
  if identityCast op then x
  else match op with
    | .extract o n _ =>
      if o == 0 && x.compareBits == 32 && x.compareBits ≤ n then x
      else match x with
        | .app (.sext q _) [v] =>
          if o + n ≤ q then .app (.extract o n) [v]
          else .app (.extract o n) [x]
        | _ => .app (.extract o n) [x]
    | _ => .app (crossOp op) [x]

/-- Signed representative for the modulus of the *operator's* carrier. -/
def addResidue (w : Nat) (z : Int) : Int :=
  let m := (2 : Int) ^ w
  let r := z % m
  if r < (2 : Int) ^ (w - 1) then r else r - m

/-- The payload tag is reserved for coefficient/atom pairs inside a sum.
It is never the image of an original machine operator. -/
abbrev AddCombo := List (Int × CrossTerm) × Int

private def comboPlus (a b : AddCombo) : AddCombo := (a.1 ++ b.1, a.2 + b.2)

private def comboScale (k : Int) (a : AddCombo) : AddCombo :=
  (a.1.map fun p => (k * p.1, p.2), k * a.2)

mutual
  /-- Flatten adds of every arity, including previously printed combinations.
  Non-add operators are opaque atoms. -/
  private def addParts : CrossTerm → AddCombo
    | .c k => ([], k)
    | .app .add [.app .linear ps, .app .linear []] => addPayload ps
    | .app .add args => args.foldl (fun a t => comboPlus a (addParts t)) ([], 0)
    | t => ([(1,t)], 0)
  termination_by t => sizeOf t

  private def addPayload : List CrossTerm → AddCombo
    | [] => ([], 0)
    | .app .linear [.c k, a] :: ps =>
      comboPlus (comboScale k (addParts a)) (addPayload ps)
    | a :: ps => comboPlus (addParts a) (addPayload ps)
  termination_by ps => sizeOf ps
end

private def insertAdd (p : Int × CrossTerm) : List (Int × CrossTerm) →
    List (Int × CrossTerm)
  | [] => [p]
  | q :: qs =>
    if p.2 == q.2 then (p.1 + q.1, q.2) :: qs
    else if crossCompare p.2 q.2 == .lt then p :: q :: qs
    else q :: insertAdd p qs

private def sortAdd : List (Int × CrossTerm) → List (Int × CrossTerm)
  | [] => []
  | p :: ps => insertAdd p (sortAdd ps)

private def reduceAdd (w : Nat) : List (Int × CrossTerm) →
    List (Int × CrossTerm)
  | [] => []
  | (k,a) :: ps =>
    let r := addResidue w k
    if r == 0 then reduceAdd w ps else (r,a) :: reduceAdd w ps

private def printAddPayload (ps : List (Int × CrossTerm)) (k : Int) : List CrossTerm :=
  match ps with
  | [] => if k == 0 then [] else [.c k]
  | (c,a) :: ps => .app .linear [.c c, a] :: printAddPayload ps k

/-- Simple offsets retain their existing wire form. All other sums use a binary
root with a `linear` list of coefficient/atom entries and an optional nonzero
constant, followed by an empty `linear` delimiter. The delimiter is not a
constant RHS, so this cannot collide with a simple offset. Every nontrivial
encoding has a binary-add root, which no atom has. -/
def printAdd (a : AddCombo) : CrossTerm :=
  match a with
  | ([], k) => .c k
  | ([(1,t)], k) => if k == 0 then t else .app .add [t, .c k]
  | (ps, k) => .app .add [.app .linear (printAddPayload ps k), .app .linear []]

/-- Total, width-indexed linear-combination normal form. -/
def normalizeCrossAdd (w : Nat) (t : CrossTerm) : CrossTerm :=
  let a := addParts t
  printAdd (reduceAdd w (sortAdd a.1), addResidue w a.2)

mutual
  /-- Valuation-indexed *add-fragment* denotation, not machine evaluation.
  Non-add atoms are assigned arbitrary integers by `ρ`; addition of every arity,
  constants and the reserved coefficient payload have an interpretation here. -/
  def CrossTerm.addValue (ρ : CrossTerm → Int) : CrossTerm → Int
    | .c k => k
    | .app .add [.app .linear ps, .app .linear []] => addPayloadValue ρ ps
    | .app .add args => args.foldl (fun z t => z + t.addValue ρ) 0
    | t => ρ t
  termination_by t => sizeOf t

  private def addPayloadValue (ρ : CrossTerm → Int) : List CrossTerm → Int
    | [] => 0
    | .app .linear [.c k, a] :: ps =>
      k * a.addValue ρ + addPayloadValue ρ ps
    | a :: ps => a.addValue ρ + addPayloadValue ρ ps
  termination_by ps => sizeOf ps
end

def CrossTerm.addDenote (w : Nat) (ρ : CrossTerm → Int) (t : CrossTerm) : Int :=
  t.addValue ρ % (2 : Int) ^ w

private def comboValue (ρ : CrossTerm → Int) (ps : List (Int × CrossTerm)) : Int :=
  match ps with
  | [] => 0
  | (k,a) :: ps => k * a.addValue ρ + comboValue ρ ps

private theorem comboValue_append (ρ : CrossTerm → Int) (ps qs) :
    comboValue ρ (ps ++ qs) = comboValue ρ ps + comboValue ρ qs := by
  induction ps with
  | nil => simp [comboValue]
  | cons p ps ih => simp [comboValue, ih, Int.add_assoc]

private theorem comboValue_scale (ρ : CrossTerm → Int) (k : Int) (ps) :
    comboValue ρ (ps.map fun p => (k * p.1, p.2)) = k * comboValue ρ ps := by
  induction ps with
  | nil => simp [comboValue]
  | cons p ps ih => simp [comboValue, ih, Int.mul_add, Int.mul_assoc]

private theorem partsValue (ρ : CrossTerm → Int) (t : CrossTerm) :
    comboValue ρ (addParts t).1 + (addParts t).2 = t.addValue ρ := by
  unfold addParts
  split
  · simp [CrossTerm.addValue, comboValue]
  · simpa only [CrossTerm.addValue] using payloadValue ρ _
  · rename_i args h
    simpa only [CrossTerm.addValue, h, ↓reduceDIte, ↓reduceIte, comboValue,
      Int.zero_add] using foldValue ρ args ([], 0)
  · simp_all [CrossTerm.addValue, comboValue]
termination_by sizeOf t
where
  foldValue (ρ : CrossTerm → Int) (ts : List CrossTerm) (a : AddCombo) :
      comboValue ρ (ts.foldl (fun a t => comboPlus a (addParts t)) a).1 +
          (ts.foldl (fun a t => comboPlus a (addParts t)) a).2 =
        ts.foldl (fun z t => z + t.addValue ρ) (comboValue ρ a.1 + a.2) := by
    cases ts with
    | nil => rfl
    | cons t ts =>
      simp only [List.foldl_cons]
      rw [foldValue ρ ts]
      simp only [comboPlus, comboValue_append]
      rw [← partsValue ρ t]
      congr 1
      ac_rfl
  termination_by sizeOf ts
  payloadValue (ρ : CrossTerm → Int) (ps : List CrossTerm) :
      comboValue ρ (addPayload ps).1 + (addPayload ps).2 =
        addPayloadValue ρ ps := by
    unfold addPayload
    split
    · simp [addPayloadValue, comboValue]
    · rename_i k a ps
      have ha := partsValue ρ a
      have hp := payloadValue ρ ps
      simp only [addPayloadValue, comboPlus, comboScale,
        comboValue_append, comboValue_scale]
      rw [← ha, ← hp, Int.mul_add]
      ac_rfl
    · rename_i a ps h
      have ha := partsValue ρ a
      have hp := payloadValue ρ ps
      simp_all only [addPayloadValue, comboPlus, comboValue_append]
      rw [← ha, ← hp]
      ac_rfl
  termination_by sizeOf ps

private theorem insertAdd_value (ρ : CrossTerm → Int) (p) (ps) :
    comboValue ρ (insertAdd p ps) = p.1 * p.2.addValue ρ + comboValue ρ ps := by
  induction ps with
  | nil => rfl
  | cons q qs ih =>
    unfold insertAdd
    split
    · rename_i h
      have he : p.2 = q.2 := by simpa using h
      simp [comboValue, he, Int.add_mul, Int.add_assoc]
    · split
      · rfl
      · simp only [comboValue, ih]
        ac_rfl

private theorem sortAdd_value (ρ : CrossTerm → Int) (ps) :
    comboValue ρ (sortAdd ps) = comboValue ρ ps := by
  induction ps with
  | nil => rfl
  | cons p ps ih => simp [sortAdd, insertAdd_value, comboValue, ih]

theorem addResidue_mod (w : Nat) (z : Int) :
    addResidue w z % (2 : Int)^w = z % (2 : Int)^w := by
  dsimp only [addResidue]
  split <;> simp

private theorem reduceAdd_value (w : Nat) (ρ : CrossTerm → Int) (ps) :
    comboValue ρ (reduceAdd w ps) % (2 : Int)^w =
      comboValue ρ ps % (2 : Int)^w := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    rcases p with ⟨k,a⟩
    simp only [reduceAdd]
    split
    · rename_i h
      have hz : addResidue w k = 0 := by simpa using h
      have hk : k % (2 : Int)^w = 0 := by
        rw [← addResidue_mod w k, hz]; simp
      simpa [comboValue, Int.add_emod, Int.mul_emod, hk] using ih
    · simp only [comboValue]
      calc
        _ = ((addResidue w k * a.addValue ρ) % (2 : Int)^w +
            comboValue ρ (reduceAdd w ps) % (2 : Int)^w) % (2 : Int)^w :=
          Int.add_emod _ _ _
        _ = ((k * a.addValue ρ) % (2 : Int)^w +
            comboValue ρ ps % (2 : Int)^w) % (2 : Int)^w := by
          rw [ih]
          congr 2
          exact (Int.mul_emod _ _ _).trans
            (by rw [addResidue_mod]; exact (Int.mul_emod _ _ _).symm)
        _ = _ := (Int.add_emod _ _ _).symm

private theorem payload_print_value (ρ : CrossTerm → Int) (ps) (k : Int) :
    addPayloadValue ρ (printAddPayload ps k) = comboValue ρ ps + k := by
  induction ps with
  | nil =>
    by_cases hk : k = 0 <;>
      simp [printAddPayload, hk, addPayloadValue, CrossTerm.addValue, comboValue]
  | cons p ps ih => simp [printAddPayload, addPayloadValue, comboValue, ih, Int.add_assoc]

private theorem printAdd_value (ρ : CrossTerm → Int) (a : AddCombo) :
    (printAdd a).addValue ρ = comboValue ρ a.1 + a.2 := by
  unfold printAdd
  split
  · simp [CrossTerm.addValue, comboValue]
  · rename_i t k
    by_cases hk : k = 0 <;>
      simp [hk, CrossTerm.addValue, comboValue]
  · simp only [CrossTerm.addValue, payload_print_value]

/-- CP-Add: every CrossTerm add tree, at a common positive modulus width,
preserves its valuation-indexed modular denotation. This excludes R6 and makes
no assertion connecting arbitrary atom valuations to original machine values. -/
theorem normalizeCrossAdd_denote (w : Nat) (_hw : 0 < w)
    (ρ : CrossTerm → Int) (t : CrossTerm) :
    (normalizeCrossAdd w t).addDenote w ρ = t.addDenote w ρ := by
  unfold normalizeCrossAdd CrossTerm.addDenote
  rw [printAdd_value, Int.add_emod, reduceAdd_value, addResidue_mod,
    sortAdd_value, ← Int.add_emod, partsValue]

/-- R6 is a structural pre-rewrite. Its same-element word-content and carry
premises remain CP-Bytes/Q. The one-atom nonzero offset encoding is unchanged. -/
private def crossAdd (w : Nat) (x y : CrossTerm) : CrossTerm :=
  match x, y with
  | .external lane [.c _], .app .ltu [.app .add [l, .c k], .c k'] =>
    if 1 ≤ lane && k == k' then .app (.extract 32 32) [.app .add [l, .c k]]
    else normalizeCrossAdd w (.app .add [x,y])
  | _, _ => normalizeCrossAdd w (.app .add [x,y])

private def crossBinary (op : Op) (x y : CrossTerm) : CrossTerm :=
  match op with
  | .add w => if crossCompare x y == .gt then crossAdd w.bits x y else crossAdd w.bits y x
  | .or _ | .xor _ =>
    if x == .c 0 then y else if y == .c 0 then x else .app (crossOp op) [x,y]
  | .shl _ | .lshr _ | .ashr _ =>
    if y == .c 0 then x else .app (crossOp op) [x,y]
  | _ => .app (crossOp op) [x,y]

def PacketOffset.toCross : PacketOffset → CrossTerm
  | .c n => .c n
  | .packet alpha => .reg .packet alpha
  | .add a b => normalizeCrossAdd 32 (.app .add [a.toCross, b.toCross])
  | .low q a => .app (.low q) [a.toCross]
  | .shl a b => .app .shl [a.toCross, b.toCross]
  | .sub a n => normalizeCrossAdd 32 (.app .add [a.toCross, .c (-(Int.ofNat n))])
  | .id a => a.toCross
  | .zext q v a => .app (.zext q v) [a.toCross]
  | .sext q v a => .app (.sext q v) [a.toCross]

def CompoundPacketReg.toCross (p : CompoundPacketReg) : CrossTerm :=
  .app (.packetReg p.bytes) [.c p.κ, p.offset.toCross, .reg .context p.endCtx,
    .c (if p.strict then 1 else 0), .c p.byteIndex, p.checkedEnd.toCross]

/-- Mathematical natural-number valuation: address sums do not wrap. -/
def PacketOffset.value (leaf : Nat → Nat) : PacketOffset → Nat
  | .c n => n
  | .packet alpha => leaf alpha
  | .add a b => a.value leaf + b.value leaf
  | .low q a => a.value leaf % (2 ^ q)
  | .shl a b => a.value leaf * 2 ^ b.value leaf
  | .sub a n => M 32 (Int.ofNat (a.value leaf) - Int.ofNat n)
  | .id a => a.value leaf
  | .zext q _ a => MNat 32 (MNat q (a.value leaf))
  | .sext q _ a => M 32 (s q (a.value leaf))

theorem CompoundPacketReg.bounds (p : CompoundPacketReg) (leaf : Nat → Nat)
    (base ending : Nat)
    (passed : base + p.checkedEnd.value leaf ≤ ending)
    (covered : p.offset.value leaf + p.bytes ≤ p.checkedEnd.value leaf) :
    base + p.offset.value leaf + p.bytes ≤ ending := by omega

theorem CompoundPacketReg.bounds_strict (p : CompoundPacketReg) (leaf : Nat → Nat)
    (base ending : Nat)
    (passed : base + p.checkedEnd.value leaf < ending)
    (covered : p.offset.value leaf + p.bytes ≤ p.checkedEnd.value leaf) :
    base + p.offset.value leaf + p.bytes < ending := by omega

theorem CompoundPacketReg.bounds_passed (p : CompoundPacketReg) (leaf : Nat → Nat)
    (base ending : Nat)
    (passed : if p.strict then base + p.checkedEnd.value leaf < ending
      else base + p.checkedEnd.value leaf ≤ ending)
    (covered : p.offset.value leaf + p.bytes ≤ p.checkedEnd.value leaf) :
    if p.strict then base + p.offset.value leaf + p.bytes < ending
      else base + p.offset.value leaf + p.bytes ≤ ending := by
  cases hs : p.strict <;> simp only [hs, Bool.false_eq_true, ↓reduceIte] at passed ⊢
  · exact p.bounds leaf base ending passed covered
  · exact p.bounds_strict leaf base ending passed covered

def Reg.toCross (r : Reg) : CrossTerm :=
  match r.compound with
  | none => .reg r.kind (crossRegAlpha r)
  | some p => p.toCross

mutual
  def toCrossTerm : Term → CrossTerm
    | .const w c => .c (s w.bits c)
    | .var _ name => .var name
    | .regVar _ r => r.toCross
    | .app _ (.externalResult _ lane) args => .external lane (crossTerms (abiPrefix lane args))
    | .app _ (.packetRead bytes ending) (value :: metadata) =>
      match compoundPacketFromMetadata bytes ending metadata with
      | some p => p.toCross
      | none => .app (.packetRead bytes ending) (crossTerms (value :: metadata))
    | .app _ (.add w) [t] => normalizeCrossAdd w.bits (.app .add [toCrossTerm t])
    | .app _ op [t] => crossUnary op (toCrossTerm t)
    | .app _ op [a,b] => crossBinary op (toCrossTerm a) (toCrossTerm b)
    | .app _ (.add w) args => normalizeCrossAdd w.bits (.app .add (crossTerms args))
    | .app _ op args => .app (crossOp op) (crossTerms args)
  termination_by t => sizeOf t
  decreasing_by
    all_goals simp_wf
    all_goals first
      | omega
      | have := abiPrefix_sizeOf_le lane args
        omega

  private def crossTerms : List Term → List CrossTerm
    | [] => []
    | t :: ts => toCrossTerm t :: crossTerms ts
  termination_by ts => sizeOf ts
end
/-- Genuine additive atoms exclude constants, sums, and the reserved payload tag. -/
def CrossTerm.IsAddAtom : CrossTerm → Prop
  | .c _ | .app .add _ | .app .linear _ => False
  | _ => True

/-- The add-fragment map uses R1 at every add and never invokes R6.
Other source nodes are leaves, translated by `toCrossTerm`. -/
def toCrossAddTree : Term → CrossTerm
  | .app _ (.add w) [a,b] =>
    let x := toCrossAddTree a
    let y := toCrossAddTree b
    if crossCompare x y == .gt then normalizeCrossAdd w.bits (.app .add [x,y])
    else normalizeCrossAdd w.bits (.app .add [y,x])
  | .app _ (.add w) args =>
    normalizeCrossAdd w.bits (.app .add (args.map toCrossAddTree))
  | t => toCrossTerm t
termination_by t => sizeOf t

/-- Common-width source add fragment. Constants have the common carrier;
other leaves have genuine atomic images, so their valuation is independent
of the add interpretation. Non-add source applications are not traversed. -/
def Term.AllAddWidth (w : Nat) : Term → Prop
  | .app output (.add carrier) args =>
    output.bits = w ∧ carrier.bits = w ∧ ∀ u ∈ args, u.AllAddWidth w
  | .const carrier _ => carrier.bits = w
  | t => t.width.bits = w ∧ (toCrossTerm t).IsAddAtom
termination_by t => sizeOf t

/-- The nonconstant source leaves of the add fragment, with multiplicity. -/
def Term.addAtoms : Term → List Term
  | .app _ (.add _) args => args.flatMap Term.addAtoms
  | .const _ _ => []
  | t => [t]
termination_by t => sizeOf t

/-- Structural exclusion of the R6 pre-rewrite for one ordered pair. -/
def CrossTerm.NoAddCarry (x y : CrossTerm) : Prop :=
  match x, y with
  | .external lane [.c _], .app .ltu [.app .add [_, .c k], .c k'] =>
    ¬ (1 ≤ lane ∧ k = k')
  | _, _ => True

/-- R6 is excluded in both orientations of every binary source add.
The test uses the recursively normalized, R6-free children. -/
def Term.AddR6Free : Term → Prop
  | .app _ (.add _) args =>
    (∀ a b, args = [a,b] →
      (toCrossAddTree a).NoAddCarry (toCrossAddTree b) ∧
      (toCrossAddTree b).NoAddCarry (toCrossAddTree a)) ∧
    ∀ u ∈ args, u.AddR6Free
  | _ => True
termination_by t => sizeOf t

private theorem addValue_pair (ρ : CrossTerm → Int) (x y : CrossTerm)
    (hx : ∀ ps, x ≠ .app .linear ps) :
    (CrossTerm.app .add [x,y]).addValue ρ = x.addValue ρ + y.addValue ρ := by
  conv => lhs; unfold CrossTerm.addValue
  split <;> simp_all
  rename_i args hn he
  cases he
  simp

private theorem atom_parts (t : CrossTerm) (ht : t.IsAddAtom) :
    addParts t = ([(1,t)], 0) := by
  cases t <;> simp_all [CrossTerm.IsAddAtom, addParts]
  rename_i op args
  cases op <;> simp_all [addParts]

private theorem atom_value (ρ : CrossTerm → Int) (t : CrossTerm) (ht : t.IsAddAtom) :
    t.addValue ρ = ρ t := by
  cases t <;> simp_all [CrossTerm.IsAddAtom, CrossTerm.addValue]
  rename_i op args
  cases op <;> simp_all [CrossTerm.addValue]

private def RegularAdd (t : CrossTerm) : Prop :=
  ∀ p ∈ (addParts t).1, p.2.IsAddAtom

private theorem insertAdd_atoms (p : Int × CrossTerm) (ps : List (Int × CrossTerm))
    (hp : p.2.IsAddAtom) (hs : ∀ q ∈ ps, q.2.IsAddAtom) :
    ∀ q ∈ insertAdd p ps, q.2.IsAddAtom := by
  induction ps with
  | nil => simpa [insertAdd] using hp
  | cons a as ih =>
    simp only [insertAdd]
    split
    · simpa using hs
    · split
      · intro q h
        simp only [List.mem_cons] at h
        rcases h with rfl | rfl | h
        · exact hp
        · exact hs q (by simp)
        · exact hs q (by simp [h])
      · intro q h
        rcases List.mem_cons.mp h with he | h
        · subst q
          exact hs a (by simp)
        · exact ih (fun q h => hs q (by simp [h])) q h

private theorem sortAdd_atoms (ps : List (Int × CrossTerm))
    (hs : ∀ q ∈ ps, q.2.IsAddAtom) :
    ∀ q ∈ sortAdd ps, q.2.IsAddAtom := by
  induction ps with
  | nil => simp [sortAdd]
  | cons p ps ih =>
    exact insertAdd_atoms p _ (hs p (by simp))
      (ih (fun q h => hs q (by simp [h])))

private theorem reduceAdd_atoms (w : Nat) (ps : List (Int × CrossTerm))
    (hs : ∀ q ∈ ps, q.2.IsAddAtom) :
    ∀ q ∈ reduceAdd w ps, q.2.IsAddAtom := by
  induction ps with
  | nil => simp [reduceAdd]
  | cons p ps ih =>
    simp only [reduceAdd]
    split
    · exact ih (fun q h => hs q (by simp [h]))
    · simp only [List.mem_cons]
      intro q h
      rcases h with rfl | h
      · exact hs p (by simp)
      · exact ih (fun q h => hs q (by simp [h])) q h

private theorem payload_atoms (ps : List (Int × CrossTerm)) (k : Int)
    (hs : ∀ q ∈ ps, q.2.IsAddAtom) :
    ∀ q ∈ (addPayload (printAddPayload ps k)).1, q.2.IsAddAtom := by
  induction ps with
  | nil => by_cases hk : k = 0 <;> simp [printAddPayload, hk, addPayload, addParts, comboPlus]
  | cons p ps ih =>
    have hp := atom_parts p.2 (hs p (by simp))
    simpa [printAddPayload, addPayload, comboPlus, comboScale, hp] using
      And.intro (hs p (by simp)) (ih (fun q h => hs q (by simp [h])))

private theorem printAdd_regular (a : AddCombo)
    (hs : ∀ q ∈ a.1, q.2.IsAddAtom) : RegularAdd (printAdd a) := by
  unfold printAdd
  split
  · simp [RegularAdd, addParts]
  · rename_i t k
    have ht : t.IsAddAtom := hs (1,t) (by simp)
    have hp := atom_parts t ht
    by_cases hk : k = 0
    · simpa [RegularAdd, hk, hp] using ht
    · simpa [RegularAdd, hk, addParts, comboPlus, hp] using ht
  · simpa only [RegularAdd, addParts] using payload_atoms _ _ hs

private theorem normalizeAdd_regular (w : Nat) (t : CrossTerm) (ht : RegularAdd t) :
    RegularAdd (normalizeCrossAdd w t) :=
  printAdd_regular _ (reduceAdd_atoms w _ (sortAdd_atoms _ ht))

private theorem parts_pair (x y : CrossTerm) (hl : ∀ ps, x ≠ .app .linear ps) :
    addParts (.app .add [x,y]) = comboPlus (addParts x) (addParts y) := by
  conv => lhs; unfold addParts
  split <;> simp_all
  rename_i args hn he
  cases he
  simp [comboPlus]

private theorem pair_regular (x y : CrossTerm) (hx : RegularAdd x) (hy : RegularAdd y)
    (hl : ∀ ps, x ≠ .app .linear ps) : RegularAdd (.app .add [x,y]) := by
  simp only [RegularAdd, parts_pair x y hl, comboPlus, List.mem_append]
  intro p h
  exact h.elim (hx p) (hy p)

private theorem regular_not_linear (t : CrossTerm) (ht : RegularAdd t)
    (ps : List CrossTerm) : t ≠ .app .linear ps := by
  intro he
  subst t
  simp [RegularAdd, addParts, CrossTerm.IsAddAtom] at ht

private theorem addTree_regular (w : Nat) (t : Term) (ht : t.AllAddWidth w)
    (ν : Var → Nat) (θ : ExternalInterpretation) (v : Nat)
    (hv : interpretTerm ν θ t = some v) : RegularAdd (toCrossAddTree t) := by
  cases t with
  | const carrier c => simp [toCrossAddTree, toCrossTerm, RegularAdd, addParts]
  | var carrier name => simp [toCrossAddTree, toCrossTerm, RegularAdd, addParts, CrossTerm.IsAddAtom]
  | regVar event r =>
    simp only [Term.AllAddWidth] at ht
    have ha := ht.2
    simpa [toCrossAddTree, RegularAdd, atom_parts _ ha] using ha
  | app output op args =>
    by_cases hadd : ∃ carrier, op = .add carrier
    · obtain ⟨carrier, rfl⟩ := hadd
      simp only [Term.AllAddWidth] at ht
      have hargs := ht.2.2
      cases hs : (Op.add carrier).validSignature output (args.map Term.width) with
      | false => simp [interpretTerm, hs] at hv
      | true =>
        have hlen : args.length = 2 := by
          have hh := hs
          simp only [Op.validSignature, Bool.and_eq_true, beq_iff_eq] at hh
          simpa only [List.length_map] using hh.2.1
        cases args with
        | nil => simp at hlen
        | cons a args =>
          cases args with
          | nil => simp at hlen
          | cons b args =>
            cases args with
            | cons c cs => simp at hlen
            | nil =>
              cases ha : interpretTerm ν θ a with
              | none => simp [interpretTerm, interpretTerms, ha] at hv
              | some va =>
                cases hb : interpretTerm ν θ b with
                | none => simp [interpretTerm, interpretTerms, ha, hb] at hv
                | some vb =>
                  have ia := addTree_regular w a (hargs a (by simp)) ν θ va ha
                  have ib := addTree_regular w b (hargs b (by simp)) ν θ vb hb
                  simp only [toCrossAddTree]
                  split
                  · exact normalizeAdd_regular _ _ (pair_regular _ _ ia ib (regular_not_linear _ ia))
                  · exact normalizeAdd_regular _ _ (pair_regular _ _ ib ia (regular_not_linear _ ib))
    · have hop : ∀ carrier, op ≠ .add carrier := fun carrier h => hadd ⟨carrier,h⟩
      have ht' : (Term.app output op args).width.bits = w ∧
          (toCrossTerm (.app output op args)).IsAddAtom := by
        cases op <;> simp_all [Term.AllAddWidth, Term.width]
      have he : toCrossAddTree (.app output op args) = toCrossTerm (.app output op args) := by
        cases op <;> simp_all [toCrossAddTree]
      simpa [he, RegularAdd, atom_parts _ ht'.2] using ht'.2
termination_by sizeOf t

private theorem interpretTerm_bound (ν : Var → Nat) (θ : ExternalInterpretation)
    (t : Term) (v : Nat) (h : interpretTerm ν θ t = some v) :
    v < 2 ^ t.width.bits := by
  cases t with
  | const w c =>
    simp only [interpretTerm] at h
    split at h <;> simp_all [Term.width]
  | var w name =>
    simp only [interpretTerm, Option.some.injEq] at h
    exact h ▸ MNat_lt w.bits _
  | regVar event r =>
    simp only [interpretTerm] at h
    split at h
    · simp only [Option.some.injEq] at h
      exact h ▸ MNat_lt r.width.bits _
    · contradiction
  | app output op args =>
    simp only [interpretTerm] at h
    split at h
    · contradiction
    · cases hv : interpretTerms ν θ args with
      | none => simp [hv] at h
      | some vs =>
        cases ho : interpretWith θ output op vs with
        | none => simp [hv, ho] at h
        | some value =>
          simp [hv, ho] at h
          exact h ▸ MNat_lt output.bits value

private theorem ofNat_add_mod (w a : Nat) :
    Int.ofNat a % (2 : Int)^w = Int.ofNat (MNat w a) := by
  simp [MNat, Nat.shiftLeft_eq, Int.natCast_emod, Int.natCast_pow]

private theorem addTree_interpret (w : Nat) (hw : 0 < w)
    (ν : Var → Nat) (θ : ExternalInterpretation) (ρ : CrossTerm → Int)
    (t : Term) (ht : t.AllAddWidth w)
    (hρ : ∀ u ∈ t.addAtoms,
      ρ (toCrossTerm u) = Int.ofNat ((interpretTerm ν θ u).getD 0))
    (v : Nat) (hv : interpretTerm ν θ t = some v) :
    (toCrossAddTree t).addDenote w ρ = Int.ofNat v := by
  cases t with
  | const carrier c =>
    simp only [Term.AllAddWidth] at ht
    simp only [interpretTerm] at hv
    split at hv
    · rename_i hc
      cases hv
      simp only [toCrossAddTree, toCrossTerm, CrossTerm.addDenote, CrossTerm.addValue]
      rw [← ht, ← M_cast, M_s, MNat_of_lt hc]
      rfl
    · contradiction
  | var carrier name =>
    simp only [Term.AllAddWidth, Term.width] at ht
    have ht' := ht
    have hr := hρ (.var carrier name) (by simp [Term.addAtoms])
    simp only [hv, Option.getD_some] at hr
    simp only [toCrossAddTree, CrossTerm.addDenote, atom_value ρ _ ht'.2, hr]
    rw [← ht'.1]
    rw [ofNat_add_mod]
    simpa only [Term.width] using
      congrArg Int.ofNat (MNat_of_lt (interpretTerm_bound ν θ _ _ hv))
  | regVar event r =>
    have hr := hρ (.regVar event r) (by simp [Term.addAtoms])
    simp only [hv, Option.getD_some] at hr
    simp only [Term.AllAddWidth, Term.width] at ht
    have ht' := ht
    simp only [toCrossAddTree, CrossTerm.addDenote, atom_value ρ _ ht'.2, hr]
    rw [← ht'.1]
    rw [ofNat_add_mod]
    simpa only [Term.width] using
      congrArg Int.ofNat (MNat_of_lt (interpretTerm_bound ν θ _ _ hv))
  | app output op args =>
    by_cases hadd : ∃ carrier, op = .add carrier
    · obtain ⟨carrier, rfl⟩ := hadd
      simp only [Term.AllAddWidth] at ht
      obtain ⟨hout, hcarrier, hargs⟩ := ht
      cases hs : (Op.add carrier).validSignature output (args.map Term.width) with
      | false => simp [interpretTerm, hs] at hv
      | true =>
        cases args with
        | nil => simp [Op.validSignature] at hs
        | cons a args =>
          cases args with
          | nil => simp [Op.validSignature] at hs
          | cons b args =>
            cases args with
            | cons c cs =>
              simp [Op.validSignature] at hs
            | nil =>
              cases ha : interpretTerm ν θ a with
              | none => simp [interpretTerm, interpretTerms, ha] at hv
              | some va =>
                cases hb : interpretTerm ν θ b with
                | none => simp [interpretTerm, interpretTerms, ha, hb] at hv
                | some vb =>
                  have ia := addTree_interpret w hw ν θ ρ a (hargs a (by simp))
                    (fun u hu => hρ u (by simp [Term.addAtoms, hu])) va ha
                  have ib := addTree_interpret w hw ν θ ρ b (hargs b (by simp))
                    (fun u hu => hρ u (by simp [Term.addAtoms, hu])) vb hb
                  have hva := regular_not_linear _ (addTree_regular w a (hargs a (by simp)) ν θ va ha)
                  have hvb := regular_not_linear _ (addTree_regular w b (hargs b (by simp)) ν θ vb hb)
                  simp [interpretTerm, interpretTerms, ha, hb,
                    interpretWith, interpretOp] at hv
                  simp only [toCrossAddTree, hcarrier]
                  split <;> rw [normalizeCrossAdd_denote w hw]
                  all_goals
                    simp only [CrossTerm.addDenote]
                    rw [addValue_pair ρ _ _ (by assumption)]
                    rw [Int.add_emod]
                    change ((toCrossAddTree _).addDenote w ρ + (toCrossAddTree _).addDenote w ρ) %
                      (2 : Int)^w = _
                    simp only [ia, ib]
                    have castAdd (a b : Nat) :
                        Int.ofNat a + Int.ofNat b = Int.ofNat (a + b) := rfl
                    rw [castAdd, ofNat_add_mod]
                    have he : MNat w (va + vb) = v := by
                      simpa [ADD, hout, hcarrier] using hv.2
                    simpa [Nat.add_comm] using congrArg Int.ofNat he
    · have hop : ∀ carrier, op ≠ .add carrier := fun carrier h => hadd ⟨carrier,h⟩
      have ht' : output.bits = w ∧ (toCrossTerm (.app output op args)).IsAddAtom := by
        cases op <;> simp_all [Term.AllAddWidth, Term.width]
      have hatoms : (Term.app output op args).addAtoms = [.app output op args] := by
        cases op <;> simp_all [Term.addAtoms]
      have he : toCrossAddTree (.app output op args) = toCrossTerm (.app output op args) := by
        cases op <;> simp_all [toCrossAddTree]
      have hr := hρ (.app output op args) (by simp [hatoms])
      simp only [hv, Option.getD_some] at hr
      simp only [he, CrossTerm.addDenote, atom_value ρ _ ht'.2, hr]
      rw [← ht'.1]
      rw [ofNat_add_mod]
      simpa only [Term.width] using
        congrArg Int.ofNat (MNat_of_lt (interpretTerm_bound ν θ _ _ hv))
termination_by sizeOf t

/-- CP-Add for the R1-only normal-form map. The atom correspondence ranges
only over the genuine nonconstant source leaves of this add fragment. -/
theorem toCrossAddTree_add_interpret (w : Nat) (hw : 0 < w)
    (ν : Var → Nat) (θ : ExternalInterpretation) (ρ : CrossTerm → Int)
    (output carrier : Width) (args : List Term)
    (ht : (Term.app output (.add carrier) args).AllAddWidth w)
    (hρ : ∀ u ∈ (Term.app output (.add carrier) args).addAtoms,
      ρ (toCrossTerm u) = Int.ofNat ((interpretTerm ν θ u).getD 0))
    (v : Nat) (hv : interpretTerm ν θ (.app output (.add carrier) args) = some v) :
    (toCrossAddTree (.app output (.add carrier) args)).addDenote w ρ = Int.ofNat v :=
  addTree_interpret w hw ν θ ρ _ ht hρ v hv

/-- Applying the width-indexed normalizer again preserves the source value. -/
theorem normalizeCrossAddTree_interpret (w : Nat) (hw : 0 < w)
    (ν : Var → Nat) (θ : ExternalInterpretation) (ρ : CrossTerm → Int)
    (output carrier : Width) (args : List Term)
    (ht : (Term.app output (.add carrier) args).AllAddWidth w)
    (hρ : ∀ u ∈ (Term.app output (.add carrier) args).addAtoms,
      ρ (toCrossTerm u) = Int.ofNat ((interpretTerm ν θ u).getD 0))
    (v : Nat) (hv : interpretTerm ν θ (.app output (.add carrier) args) = some v) :
    (normalizeCrossAdd w (toCrossAddTree (.app output (.add carrier) args))).addDenote w ρ =
      Int.ofNat v := by
  rw [normalizeCrossAdd_denote w hw]
  exact toCrossAddTree_add_interpret w hw ν θ ρ output carrier args ht hρ v hv

private theorem crossAdd_noCarry (w : Nat) (x y : CrossTerm)
    (h : x.NoAddCarry y) :
    crossAdd w x y = normalizeCrossAdd w (.app .add [x,y]) := by
  unfold crossAdd
  split
  · rename_i lane i l k k'
    simp only [CrossTerm.NoAddCarry] at h
    have hh : ¬ (1 ≤ lane && k == k') = true := by
      simpa only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] using h
    simp [hh]
  · rfl

private theorem crossTerms_eq_map (args : List Term) :
    crossTerms args = args.map toCrossTerm := by
  induction args with
  | nil => simp only [crossTerms, List.map_nil]
  | cons a args ih => simp only [crossTerms, List.map_cons, ih]

/-- On the R6-free source add fragment, `toCrossTerm` is exactly the R1 map.
This structural statement is independent of machine evaluation and valuation. -/
theorem toCrossTerm_add_normalForm (t : Term) (hfree : t.AddR6Free) :
    toCrossTerm t = toCrossAddTree t := by
  cases t with
  | const carrier c => simp only [toCrossAddTree]
  | var carrier name => simp only [toCrossAddTree]
  | regVar event r => simp only [toCrossAddTree]
  | app output op args =>
    by_cases hadd : ∃ carrier, op = .add carrier
    · obtain ⟨carrier, rfl⟩ := hadd
      simp only [Term.AddR6Free] at hfree
      have ih (u : Term) (hu : u ∈ args) :
          toCrossTerm u = toCrossAddTree u :=
        toCrossTerm_add_normalForm u (hfree.2 u hu)
      have hm : crossTerms args = args.map toCrossAddTree := by
        rw [crossTerms_eq_map]
        exact List.map_congr_left ih
      cases args with
      | nil => simp only [toCrossTerm, toCrossAddTree, crossTerms, List.map_nil]
      | cons a args =>
        cases args with
        | nil => simp only [toCrossTerm, toCrossAddTree, List.map_cons,
            List.map_nil, ih a (by simp)]
        | cons b args =>
          cases args with
          | nil =>
            have hab := hfree.1 a b rfl
            simp only [toCrossTerm, crossBinary, toCrossAddTree,
              ih a (by simp), ih b (by simp)]
            split
            · exact crossAdd_noCarry _ _ _ hab.1
            · exact crossAdd_noCarry _ _ _ hab.2
          | cons c cs => simp only [toCrossTerm, toCrossAddTree, hm]
    · have hop : ∀ carrier, op ≠ .add carrier := fun carrier h => hadd ⟨carrier,h⟩
      have he : toCrossAddTree (.app output op args) = toCrossTerm (.app output op args) := by
        cases op <;> simp_all [toCrossAddTree]
      exact he.symm
termination_by sizeOf t
decreasing_by
  all_goals
    have hs := List.sizeOf_lt_of_mem hu
    simp_all
    omega

/-- CP-Add source bridge for `toCrossTerm`, with R6 excluded structurally.
The other erase rules are confined to leaves with explicit atom correspondence. -/
theorem toCrossTerm_add_interpret (w : Nat) (hw : 0 < w)
    (ν : Var → Nat) (θ : ExternalInterpretation) (ρ : CrossTerm → Int)
    (output carrier : Width) (args : List Term)
    (ht : (Term.app output (.add carrier) args).AllAddWidth w)
    (hρ : ∀ u ∈ (Term.app output (.add carrier) args).addAtoms,
      ρ (toCrossTerm u) = Int.ofNat ((interpretTerm ν θ u).getD 0))
    (hfree : (Term.app output (.add carrier) args).AddR6Free)
    (v : Nat) (hv : interpretTerm ν θ (.app output (.add carrier) args) = some v) :
    (toCrossTerm (.app output (.add carrier) args)).addDenote w ρ = Int.ofNat v := by
  rw [toCrossTerm_add_normalForm _ hfree]
  exact toCrossAddTree_add_interpret w hw ν θ ρ output carrier args ht hρ v hv



/-! Interpretation-level premises for the implemented erasures. -/

theorem cross_MNat_mono {q r a : Nat} (hqr : q ≤ r) (ha : a < 2^q) :
    MNat r a = a := by
  apply MNat_of_lt
  exact Nat.lt_of_lt_of_le ha (Nat.pow_le_pow_right (by decide) hqr)

theorem cross_MNat_nested {q r : Nat} (hqr : q ≤ r) (a : Nat) :
    MNat q (MNat r a) = MNat q a := by
  simp only [MNat, Nat.shiftLeft_eq, Nat.one_mul]
  exact Nat.mod_mod_of_dvd a (Nat.pow_dvd_pow 2 hqr)

private theorem cross_unary_value (ν : Var → Nat) (θ : ExternalInterpretation)
    (out : Width) (op : Op) (a : Term) (va result : Nat)
    (hs : op.validSignature out [a.width] = true)
    (ha : interpretTerm ν θ a = some va)
    (hop : interpretOp op [va] = some result) :
    interpretTerm ν θ (.app out op [a]) = some (MNat out.bits result) := by
  cases op <;> simp_all [interpretTerm, interpretTerms, interpretWith, interpretOp]

private theorem cross_binary_value (ν : Var → Nat) (θ : ExternalInterpretation)
    (out : Width) (op : Op) (a b : Term) (va vb result : Nat)
    (hs : op.validSignature out [a.width,b.width] = true)
    (ha : interpretTerm ν θ a = some va) (hb : interpretTerm ν θ b = some vb)
    (hop : interpretOp op [va,vb] = some result) :
    interpretTerm ν θ (.app out op [a,b]) = some (MNat out.bits result) := by
  cases op <;> simp_all [interpretTerm, interpretTerms, interpretWith, interpretOp]

theorem cross_zext_interpret (ν : Var → Nat) (θ : ExternalInterpretation)
    (out : Width) (q v : Nat) (a : Term) (va : Nat)
    (hs : (Op.zext q out v).validSignature out [a.width] = true)
    (_hqv : q ≤ v) (hqo : q ≤ out.bits)
    (ha : interpretTerm ν θ a = some va) (hva : va < 2^q) :
    interpretTerm ν θ (.app out (.zext q out v) [a]) = some va := by
  rw [cross_unary_value ν θ out (.zext q out v) a va (Z q out v va) hs ha rfl]
  simp [Z, MNat_of_lt hva, cross_MNat_mono hqo hva]

theorem cross_and_interpret (ν : Var → Nat) (θ : ExternalInterpretation)
    (w w' : Width) (q : Nat) (a b a' b' : Term) (va vb : Nat)
    (hs : (Op.and q).validSignature w [a.width,b.width] = true)
    (hs' : (Op.and q).validSignature w' [a'.width,b'.width] = true)
    (hq : q ≤ w.bits) (hq' : q ≤ w'.bits)
    (ha : interpretTerm ν θ a = some va) (hb : interpretTerm ν θ b = some vb)
    (ha' : interpretTerm ν θ a' = some va) (hb' : interpretTerm ν θ b' = some vb)
    (_hva : va < 2^q) (_hvb : vb < 2^q) :
    interpretTerm ν θ (.app w (.and q) [a,b]) = some (MNat q (va &&& vb)) ∧
    interpretTerm ν θ (.app w' (.and q) [a',b']) = some (MNat q (va &&& vb)) := by
  constructor
  · rw [cross_binary_value ν θ w (.and q) a b va vb (AND q va vb) hs ha hb rfl]
    exact congrArg some (cross_MNat_mono hq (MNat_lt q _))
  · rw [cross_binary_value ν θ w' (.and q) a' b' va vb (AND q va vb) hs' ha' hb' rfl]
    exact congrArg some (cross_MNat_mono hq' (MNat_lt q _))

theorem cross_or_interpret (ν : Var → Nat) (θ : ExternalInterpretation)
    (w w' : Width) (q : Nat) (a b a' b' : Term) (va vb : Nat)
    (hs : (Op.or q).validSignature w [a.width,b.width] = true)
    (hs' : (Op.or q).validSignature w' [a'.width,b'.width] = true)
    (hq : q ≤ w.bits) (hq' : q ≤ w'.bits)
    (ha : interpretTerm ν θ a = some va) (hb : interpretTerm ν θ b = some vb)
    (ha' : interpretTerm ν θ a' = some va) (hb' : interpretTerm ν θ b' = some vb)
    (_hva : va < 2^q) (_hvb : vb < 2^q) :
    interpretTerm ν θ (.app w (.or q) [a,b]) = some (MNat q (va ||| vb)) ∧
    interpretTerm ν θ (.app w' (.or q) [a',b']) = some (MNat q (va ||| vb)) := by
  constructor
  · rw [cross_binary_value ν θ w (.or q) a b va vb (OR q va vb) hs ha hb rfl]
    exact congrArg some (cross_MNat_mono hq (MNat_lt q _))
  · rw [cross_binary_value ν θ w' (.or q) a' b' va vb (OR q va vb) hs' ha' hb' rfl]
    exact congrArg some (cross_MNat_mono hq' (MNat_lt q _))

theorem cross_xor_interpret (ν : Var → Nat) (θ : ExternalInterpretation)
    (w w' : Width) (q : Nat) (a b a' b' : Term) (va vb : Nat)
    (hs : (Op.xor q).validSignature w [a.width,b.width] = true)
    (hs' : (Op.xor q).validSignature w' [a'.width,b'.width] = true)
    (hq : q ≤ w.bits) (hq' : q ≤ w'.bits)
    (ha : interpretTerm ν θ a = some va) (hb : interpretTerm ν θ b = some vb)
    (ha' : interpretTerm ν θ a' = some va) (hb' : interpretTerm ν θ b' = some vb)
    (_hva : va < 2^q) (_hvb : vb < 2^q) :
    interpretTerm ν θ (.app w (.xor q) [a,b]) = some (MNat q (va ^^^ vb)) ∧
    interpretTerm ν θ (.app w' (.xor q) [a',b']) = some (MNat q (va ^^^ vb)) := by
  constructor
  · rw [cross_binary_value ν θ w (.xor q) a b va vb (XOR q va vb) hs ha hb rfl]
    exact congrArg some (cross_MNat_mono hq (MNat_lt q _))
  · rw [cross_binary_value ν θ w' (.xor q) a' b' va vb (XOR q va vb) hs' ha' hb' rfl]
    exact congrArg some (cross_MNat_mono hq' (MNat_lt q _))

theorem cross_extract_represented_interpret (ν : Var → Nat) (θ : ExternalInterpretation)
    (out : Width) (n v : Nat) (a : Term) (va : Nat)
    (hs : (Op.extract 0 n v).validSignature out [a.width] = true)
    (hn : 32 ≤ n) (hnv : n ≤ v) (hout : 32 ≤ out.bits)
    (ha : interpretTerm ν θ a = some va) (hva : va < 2^32) :
    interpretTerm ν θ (.app out (.extract 0 n v) [a]) = some va := by
  rw [cross_unary_value ν θ out (.extract 0 n v) a va (EXTRACT 0 n v va) hs ha rfl]
  simp [EXTRACT, cross_MNat_mono (Nat.le_trans hn hnv) hva,
    cross_MNat_mono hn hva, cross_MNat_mono hout hva]

theorem cross_ltu_carry (l k : Nat) (hl : l < 2^32) (hk : k < 2^32) :
    LTU .w32 (ADD .w32 l k) k = (l + k) / 2^32 := by
  have hm : MNat 32 k = k := MNat_of_lt hk
  have hr := Nat.mod_add_div (l+k) (2^32)
  have hmod := Nat.mod_lt (l+k) (by decide : 0 < 2^32)
  change indicator (MNat 32 (MNat 32 (l+k)) < MNat 32 k) = _
  rw [MNat_idempotent, hm]
  simp only [indicator, decide_eq_true_eq, MNat, Nat.shiftLeft_eq, Nat.one_mul]
  split <;> omega

/-- Numeric content of R6, modulo the high word. -/
theorem cross_carry_value (h l k : Nat) (hl : l < 2^32) (hk : k < 2^32) :
    MNat 32 (LTU .w32 (ADD .w32 l k) k + h) =
      EXTRACT 32 32 64 (ADD .w64 (h * 2^32 + l) k) := by
  rw [cross_ltu_carry l k hl hk]
  change ((l+k) / 4294967296 + h) % 4294967296 =
    ((h * 4294967296 + l + k) % 18446744073709551616 %
      18446744073709551616 / 4294967296) % 4294967296
  have hdiv : (h * 4294967296 + l + k) / 4294967296 =
      h + (l+k) / 4294967296 := by
    rw [Nat.add_assoc, Nat.mul_comm h, Nat.mul_add_div (by decide : 0 < 4294967296)]
  rw [Nat.mod_mod, show (18446744073709551616 : Nat) =
    4294967296 * 4294967296 by decide, Nat.mod_mul_right_div_self, hdiv]
  simp [Nat.add_comm]

/-- One lookup event, words 0/1 at offsets 0/4, and that element's double word.
The source equation is a word-content premise, not a program/sltu premise. -/
theorem cross_carry_interpret (values : Nat × Reg → Nat) (event element k : Nat)
    (hl : values (event, Reg.mapWord element 0) < 2^32) (hk : k < 2^32)
    (sameElement : values (event, Reg.mapDword element 0) =
      values (event, Reg.mapWord element 4) * 2^32 + values (event, Reg.mapWord element 0)) :
    MNat 32 (LTU .w32 (ADD .w32 (values (event, Reg.mapWord element 0)) k) k +
      values (event, Reg.mapWord element 4)) =
    EXTRACT 32 32 64 (ADD .w64 (values (event, Reg.mapDword element 0)) k) := by
  rw [sameElement]
  exact cross_carry_value _ _ k hl hk

theorem cross_M_low {q r : Nat} (hqr : q ≤ r) (z : Int) :
    MNat q (M r z) = M q z := by
  apply Int.ofNat_inj.mp
  simp only [MNat, Nat.shiftLeft_eq, Nat.one_mul, Int.natCast_emod,
    Int.natCast_pow, Int.cast_ofNat_Int, M_cast]
  exact Int.emod_emod_of_dvd z (by
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hqr
    rw [hd, Int.pow_add]
    exact ⟨(2 : Int)^d, rfl⟩)

theorem cross_S_low (q : Nat) (out : Width) (v a : Nat) (hq : q ≤ out.bits) :
    MNat q (S q out v a) = MNat q a := by
  rw [S, cross_M_low hq, M_s, MNat_idempotent]

theorem cross_extract_low (o n v a : Nat) (h : o+n ≤ v) :
    EXTRACT o n v a = MNat n (a / 2^o) := by
  simp only [EXTRACT, MNat, Nat.shiftLeft_eq, Nat.one_mul]
  rw [show v = o + (v-o) by omega, Nat.pow_add, Nat.mod_mul_right_div_self]
  exact Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by omega))

theorem cross_extract_sext_value (o n q input : Nat) (out : Width) (a : Nat)
    (hon : o+n ≤ q) (hqi : q ≤ input) (hqo : q ≤ out.bits) :
    EXTRACT o n out.bits (S q out input a) = EXTRACT o n input a := by
  have heq := congrArg (EXTRACT o n q) (cross_S_low q out input a hqo)
  simp only [EXTRACT, MNat_idempotent] at heq
  calc
    EXTRACT o n out.bits (S q out input a) =
        EXTRACT o n q (S q out input a) := by
      rw [cross_extract_low _ _ _ _ (Nat.le_trans hon hqo),
        cross_extract_low _ _ _ _ hon]
    _ = EXTRACT o n q a := heq
    _ = EXTRACT o n input a := by
      rw [cross_extract_low _ _ _ _ hon,
        cross_extract_low _ _ _ _ (Nat.le_trans hon hqi)]

theorem cross_extract_sext_interpret (ν : Var → Nat) (θ : ExternalInterpretation)
    (out carrier : Width) (o n q input : Nat) (a : Term) (va : Nat)
    (hs : (Op.sext q carrier input).validSignature carrier [a.width] = true)
    (he : (Op.extract o n carrier.bits).validSignature out [carrier] = true)
    (hi : (Op.extract o n input).validSignature out [a.width] = true)
    (hon : o+n ≤ q) (hqi : q ≤ input) (hqo : q ≤ carrier.bits)
    (ha : interpretTerm ν θ a = some va) :
    interpretTerm ν θ (.app out (.extract o n carrier.bits)
      [.app carrier (.sext q carrier input) [a]]) =
    interpretTerm ν θ (.app out (.extract o n input) [a]) := by
  have hv : MNat carrier.bits (S q carrier input va) = S q carrier input va :=
    MNat_of_lt (M_lt _ _)
  have hv' := cross_unary_value ν θ carrier (.sext q carrier input) a va
    (S q carrier input va) hs ha rfl
  rw [hv] at hv'
  rw [cross_unary_value ν θ out (.extract o n carrier.bits)
    (.app carrier (.sext q carrier input) [a]) (S q carrier input va) _ he hv' rfl,
    cross_unary_value ν θ out (.extract o n input) a va _ hi ha rfl,
    cross_extract_sext_value o n q input carrier va hon hqi hqo]

theorem cross_or_zero_interpret (ν : Var → Nat) (θ : ExternalInterpretation)
    (w : Width) (q : Nat) (a z : Term) (va : Nat)
    (hs : (Op.or q).validSignature w [a.width,z.width] = true)
    (hs' : (Op.or q).validSignature w [z.width,a.width] = true)
    (ha : interpretTerm ν θ a = some va) (hz : interpretTerm ν θ z = some 0)
    (hva : va < 2^q) (hq : q ≤ w.bits) :
    interpretTerm ν θ (.app w (.or q) [a,z]) = interpretTerm ν θ a ∧
    interpretTerm ν θ (.app w (.or q) [z,a]) = interpretTerm ν θ a := by
  rw [cross_binary_value ν θ w (.or q) a z va 0 _ hs ha hz rfl,
    cross_binary_value ν θ w (.or q) z a 0 va _ hs' hz ha rfl, ha]
  simp [OR, MNat_of_lt hva, cross_MNat_mono hq hva]

theorem cross_xor_zero_interpret (ν : Var → Nat) (θ : ExternalInterpretation)
    (w : Width) (q : Nat) (a z : Term) (va : Nat)
    (hs : (Op.xor q).validSignature w [a.width,z.width] = true)
    (hs' : (Op.xor q).validSignature w [z.width,a.width] = true)
    (ha : interpretTerm ν θ a = some va) (hz : interpretTerm ν θ z = some 0)
    (hva : va < 2^q) (hq : q ≤ w.bits) :
    interpretTerm ν θ (.app w (.xor q) [a,z]) = interpretTerm ν θ a ∧
    interpretTerm ν θ (.app w (.xor q) [z,a]) = interpretTerm ν θ a := by
  rw [cross_binary_value ν θ w (.xor q) a z va 0 _ hs ha hz rfl,
    cross_binary_value ν θ w (.xor q) z a 0 va _ hs' hz ha rfl, ha]
  simp [XOR, MNat_of_lt hva, cross_MNat_mono hq hva]

theorem cross_shift_zero_interpret (ν : Var → Nat) (θ : ExternalInterpretation)
    (w : Width) (op : Op) (a z : Term) (va : Nat)
    (hop : op = .shl w ∨ op = .lshr w ∨ op = .ashr w)
    (hs : op.validSignature w [a.width,z.width] = true)
    (ha : interpretTerm ν θ a = some va) (hz : interpretTerm ν θ z = some 0)
    (hva : va < 2^w.bits) :
    interpretTerm ν θ (.app w op [a,z]) = interpretTerm ν θ a := by
  rcases hop with rfl | rfl | rfl
  all_goals
    rw [cross_binary_value ν θ w _ a z va 0 _ hs ha hz rfl, ha]
    simp [MNat_of_lt hva]

theorem cross_id_interpret (ν : Var → Nat) (θ : ExternalInterpretation)
    (w : Width) (a : Term) (va : Nat)
    (hs : (Op.id w).validSignature w [a.width] = true)
    (ha : interpretTerm ν θ a = some va) (hva : va < 2^w.bits) :
    interpretTerm ν θ (.app w (.id w) [a]) = interpretTerm ν θ a := by
  rw [cross_unary_value ν θ w (.id w) a va va hs ha rfl, ha, MNat_of_lt hva]

theorem cross_extract_identity_interpret (ν : Var → Nat) (θ : ExternalInterpretation)
    (out : Width) (v : Nat) (a : Term) (va : Nat)
    (hs : (Op.extract 0 v v).validSignature out [a.width] = true)
    (hvo : v ≤ out.bits) (ha : interpretTerm ν θ a = some va) (hva : va < 2^v) :
    interpretTerm ν θ (.app out (.extract 0 v v) [a]) = interpretTerm ν θ a := by
  rw [cross_unary_value ν θ out (.extract 0 v v) a va _ hs ha rfl, ha]
  simp [EXTRACT, MNat_of_lt hva, cross_MNat_mono hvo hva]

theorem cross_low_identity_interpret (ν : Var → Nat) (θ : ExternalInterpretation)
    (out : Width) (v : Nat) (a : Term) (va : Nat)
    (hs : (Op.low v v).validSignature out [a.width] = true)
    (hvo : v ≤ out.bits) (ha : interpretTerm ν θ a = some va) (hva : va < 2^v) :
    interpretTerm ν θ (.app out (.low v v) [a]) = interpretTerm ν θ a := by
  rw [cross_unary_value ν θ out (.low v v) a va _ hs ha rfl, ha]
  simp [LOW, MNat_of_lt hva, cross_MNat_mono hvo hva]

theorem cross_sext_identity_interpret (ν : Var → Nat) (θ : ExternalInterpretation)
    (out : Width) (a : Term) (va : Nat)
    (hs : (Op.sext out.bits out out.bits).validSignature out [a.width] = true)
    (ha : interpretTerm ν θ a = some va) (hva : va < 2^out.bits) :
    interpretTerm ν θ (.app out (.sext out.bits out out.bits) [a]) =
      interpretTerm ν θ a := by
  rw [cross_unary_value ν θ out _ a va _ hs ha rfl, ha]
  simp [S, M_s, MNat_of_lt hva]

theorem cross_bswap_identity_interpret (ν : Var → Nat) (θ : ExternalInterpretation)
    (out : Width) (a : Term)
    (hs : (Op.bswap 8 8).validSignature out [a.width] = true) :
    interpretTerm ν θ (.app out (.bswap 8 8) [a]) = interpretTerm ν θ a := by
  simp [Op.validSignature] at hs

theorem cross_interpretTerms_take (ν : Var → Nat) (θ : ExternalInterpretation)
    (args : List Term) (vs : List Nat) (h : interpretTerms ν θ args = some vs)
    (n : Nat) :
    interpretTerms ν θ (args.take n) = some (vs.take n) := by
  induction args generalizing vs n with
  | nil => simp [interpretTerms] at h; subst vs; simp [interpretTerms]
  | cons a args ih =>
    cases hv : interpretTerm ν θ a <;> simp [interpretTerms, hv] at h
    rename_i va
    cases ht : interpretTerms ν θ args <;> simp [ht] at h
    rename_i tail
    subst vs
    cases n with
    | zero => simp [interpretTerms]
    | succ n => simp [List.take, interpretTerms, hv, ih tail ht n]

/-- Successful evaluation of the full list is essential for strict partial
interpretation: discarded undefined arguments cannot be silently recovered. -/
theorem cross_abiPrefix_interpret (ν : Var → Nat) (θ : ExternalInterpretation)
    (w : Width) (event : Nat) (args : List Term) (vs : List Nat)
    (hs : (Op.externalResult event 0).validSignature w (args.map Term.width) = true)
    (hp : (Op.externalResult event 0).validSignature w
      ((abiPrefix 0 args).map Term.width) = true)
    (hv : interpretTerms ν θ args = some vs)
    (depends : ∀ vs ws, vs.take 2 = ws.take 2 →
      θ.externalResult w event 0 vs = θ.externalResult w event 0 ws) :
    interpretTerm ν θ (.app w (.externalResult event 0) args) =
      interpretTerm ν θ (.app w (.externalResult event 0) (abiPrefix 0 args)) := by
  have ht : interpretTerms ν θ (abiPrefix 0 args) = some (vs.take 2) := by
    rw [abiPrefix_zero_take]
    exact cross_interpretTerms_take ν θ args vs hv 2
  have hd := depends vs (vs.take 2) (by rw [List.take_take]; rfl)
  simp [interpretTerm, hs, hp, hv, ht, interpretWith, hd]

/-- The interpretation quotient, relative to the explicit value environments. -/
def crossInterpretSetoid (ν : Var → Nat) (θ : ExternalInterpretation) : Setoid Term where
  r a b := interpretTerm ν θ a = interpretTerm ν θ b
  iseqv := ⟨fun _ => rfl, fun h => h.symm, fun h k => h.trans k⟩

theorem cross_quotient_eq_iff (ν : Var → Nat) (θ : ExternalInterpretation) (a b : Term) :
    Quotient.mk (crossInterpretSetoid ν θ) a = Quotient.mk (crossInterpretSetoid ν θ) b ↔
      interpretTerm ν θ a = interpretTerm ν θ b :=
  ⟨Quotient.exact, fun h => Quotient.sound (s := crossInterpretSetoid ν θ) h⟩

inductive CrossRelKind where
  | eq | ne | ltu | leu | gtu | geu | lts | les | gts | ges | bitsnz | bitsz
  deriving DecidableEq, BEq, ReflBEq, LawfulBEq, Repr

structure CrossRel where
  kind : CrossRelKind
  q : Nat
  deriving DecidableEq, BEq, ReflBEq, LawfulBEq, Repr

private def relKind : Rel → CrossRelKind
  | .eq | .eqN _ => .eq | .ne | .neN _ => .ne
  | .ltu | .ltuN _ => .ltu | .leu | .leuN _ => .leu
  | .gtu | .gtuN _ => .gtu | .geu | .geuN _ => .geu
  | .lts | .ltsN _ => .lts | .les | .lesN _ => .les
  | .gts | .gtsN _ => .gts | .ges | .gesN _ => .ges
  | .bitsnz _ => .bitsnz | .bitsz _ => .bitsz

private def relBits (represented : Nat) : Rel → Nat
  | .eqN q | .neN q | .ltuN q | .leuN q | .gtuN q | .geuN q
  | .ltsN q | .lesN q | .gtsN q | .gesN q | .bitsnz q | .bitsz q => q
  | _ => represented

def CrossRelKind.dual : CrossRelKind → CrossRelKind
  | .ltu => .gtu | .gtu => .ltu | .leu => .geu | .geu => .leu
  | .lts => .gts | .gts => .lts | .les => .ges | .ges => .les
  | k => k

/-- `swapped` says that the fixed operand was originally on the right. -/
def toCrossRel (represented : Nat) (rel : Rel) (swapped : Bool := false) : CrossRel :=
  ⟨if swapped then (relKind rel).dual else relKind rel, relBits represented rel⟩

def Rel.crossDual : Rel → Rel
  | .ltu => .gtu | .gtu => .ltu | .leu => .geu | .geu => .leu
  | .lts => .gts | .gts => .lts | .les => .ges | .ges => .les
  | .ltuN q => .gtuN q | .gtuN q => .ltuN q
  | .leuN q => .geuN q | .geuN q => .leuN q
  | .ltsN q => .gtsN q | .gtsN q => .ltsN q
  | .lesN q => .gesN q | .gesN q => .lesN q
  | r => r

inductive CrossCond where
  | plain (rel : CrossRel) (lhs rhs : CrossTerm)
  | packetBound (base : CrossTerm) (rel : CrossRel) (offset : CrossTerm)
  | packetField (field : CrossTerm) (rel : CrossRel) (value : Int)
  deriving DecidableEq, BEq, ReflBEq, LawfulBEq, Repr

def CrossCond.rel : CrossCond → CrossRel
  | .plain r _ _ | .packetBound _ r _ | .packetField _ r _ => r

/-- Meta map layouts; the map term is normalized from the static resource binding. -/
structure CrossMapLayout where
  map : CrossTerm
  keyBytes : Nat
  valueBytes : Nat
  deriving DecidableEq, BEq, ReflBEq, LawfulBEq, Repr

mutual
  private def termDecEq : (a b : Term) → Decidable (a = b)
    | .const w x, .const v y => decidable_of_iff (w = v ∧ x = y) (by simp)
    | .var w x, .var v y => decidable_of_iff (w = v ∧ x = y) (by simp)
    | .regVar e r, .regVar f s => decidable_of_iff (e = f ∧ r = s) (by simp)
    | .app w f xs, .app v g ys =>
      letI := termListDecEq xs ys
      decidable_of_iff (w = v ∧ f = g ∧ xs = ys) (by simp)
    | .const _ _, .var _ _ | .const _ _, .regVar _ _ | .const _ _, .app _ _ _
    | .var _ _, .const _ _ | .var _ _, .regVar _ _ | .var _ _, .app _ _ _
    | .regVar _ _, .const _ _ | .regVar _ _, .var _ _ | .regVar _ _, .app _ _ _
    | .app _ _ _, .const _ _ | .app _ _ _, .var _ _ | .app _ _ _, .regVar _ _ =>
      .isFalse (by intro h; cases h)
  termination_by a b => sizeOf a + sizeOf b

  private def termListDecEq : (xs ys : List Term) → Decidable (xs = ys)
    | [], [] => .isTrue rfl
    | [], _ :: _ | _ :: _, [] => .isFalse (by intro h; cases h)
    | x :: xs, y :: ys =>
      letI := termDecEq x y
      letI := termListDecEq xs ys
      decidable_of_iff (x = y ∧ xs = ys) (by simp)
  termination_by xs ys => sizeOf xs + sizeOf ys
end

instance : DecidableEq Term := termDecEq

/-- Each side supplies its own entry XDP cells and Meta layouts.
Store width is only a fallback for observations without predicate metadata. -/
structure CrossEnv where
  packetBase : Option Term := none
  packetEnd : Option Term := none
  maps : List CrossMapLayout := []
  storeBytes : Option Nat := none
  deriving DecidableEq, Repr

instance : BEq CrossEnv := ⟨fun a b => decide (a = b)⟩
instance : LawfulBEq CrossEnv where
  eq_of_beq := of_decide_eq_true
  rfl := of_decide_eq_self_eq_true _

mutual
  private def packetFieldTerm (base : CrossTerm) : CrossTerm → Bool
    | .app (.inputByte _) [b, _] => b == base
    | .app _ args => packetFieldArgs base args
    | _ => false
  termination_by t => sizeOf t

  private def packetFieldArgs (base : CrossTerm) : List CrossTerm → Bool
    | [] => false
    | t :: ts => packetFieldTerm base t || packetFieldArgs base ts
  termination_by ts => sizeOf ts
end

def toCrossCond (env : CrossEnv) (cond : Cond) : CrossCond :=
  let lhs := toCrossTerm cond.lhs
  let rhs := toCrossTerm cond.rhs
  let q := max lhs.compareBits rhs.compareBits
  match env.packetBase, env.packetEnd with
  | some b, some e =>
    let base := toCrossTerm b
    let endTerm := toCrossTerm e
    if lhs == endTerm then
      .packetBound base (toCrossRel q cond.rel) rhs
    else if rhs == endTerm then
      .packetBound base (toCrossRel q cond.rel true) lhs
    else fieldOrPlain base lhs rhs q
  | some b, none => fieldOrPlain (toCrossTerm b) lhs rhs q
  | _, _ => plain lhs rhs q
where
  plain (lhs rhs : CrossTerm) (q : Nat) : CrossCond :=
    if crossCompare lhs rhs == .gt then
      .plain (toCrossRel q cond.rel) lhs rhs
    else .plain (toCrossRel q cond.rel true) rhs lhs
  fieldOrPlain (base lhs rhs : CrossTerm) (q : Nat) : CrossCond :=
    match lhs, rhs with
    | field, .c z => if packetFieldTerm base field then
        .packetField field (toCrossRel q cond.rel) z else plain lhs rhs q
    | .c z, field => if packetFieldTerm base field then
        .packetField field (toCrossRel q cond.rel true) z else plain lhs rhs q
    | _, _ => plain lhs rhs q

/-- Every classification writes the same source relation and inferred width;
the witness is the swap flag of the branch selected by the classifier. -/
theorem toCrossCond_rel (env : CrossEnv) (cond : Cond) :
    ∃ swapped : Bool, (toCrossCond env cond).rel =
      toCrossRel (max (toCrossTerm cond.lhs).compareBits
        (toCrossTerm cond.rhs).compareBits) cond.rel swapped := by
  unfold toCrossCond toCrossCond.fieldOrPlain toCrossCond.plain
  dsimp only
  repeat' first
    | exact ⟨false, rfl⟩
    | exact ⟨true, rfl⟩
    | split

theorem toCrossCond_rel_q (env : CrossEnv) (cond : Cond) :
    (toCrossCond env cond).rel.q =
      relBits (max (toCrossTerm cond.lhs).compareBits
        (toCrossTerm cond.rhs).compareBits) cond.rel := by
  obtain ⟨swapped, h⟩ := toCrossCond_rel env cond
  rw [h]
  rfl

/-- Byte lists for writes, or an unsized source for callers without access metadata. -/
inductive CrossValue where
  | bytes (values : List CrossTerm)
  | source (term : CrossTerm)
  deriving DecidableEq, BEq, ReflBEq, LawfulBEq, Repr

inductive CrossMutationKind where
  | write | delete
  deriving DecidableEq, BEq, ReflBEq, LawfulBEq, Repr

structure CrossMutation where
  kind : CrossMutationKind
  map : CrossTerm
  key : List CrossTerm
  offset : Nat
  value : CrossValue
  deriving DecidableEq, BEq, ReflBEq, LawfulBEq, Repr

inductive CrossHelper where
  | lookup (map : CrossTerm) (key : List CrossTerm)
  | mutation (observation : CrossMutation)
  | other (helperId : Nat) (args : List CrossTerm)
  deriving DecidableEq, BEq, ReflBEq, LawfulBEq, Repr

structure CrossReturn where
  payload : CrossTerm
  deriving DecidableEq, BEq, ReflBEq, LawfulBEq, Repr

deriving instance ReflBEq, LawfulBEq for BranchDirection

structure CrossBranch where
  dir : BranchDirection
  cond : CrossCond
  deriving DecidableEq, BEq, ReflBEq, LawfulBEq, Repr

abbrev CrossMapWrite := CrossMutation

structure CrossPacketWrite where
  packet : Nat
  offset : CrossTerm
  value : CrossValue
  deriving DecidableEq, BEq, ReflBEq, LawfulBEq, Repr

inductive CrossPred where
  | helper (observation : CrossHelper)
  | branch (observation : CrossBranch)
  | ret (observation : CrossReturn)
  | mapWrite (observation : CrossMapWrite)
  | packetWrite (observation : CrossPacketWrite)
  deriving DecidableEq, BEq, ReflBEq, LawfulBEq, Repr

/-- Access byte count comes from the predicate, including compound destinations. -/
def Predicate.storeBytes? : Predicate → Option Nat
  | .packetWrite _ _ _ bits _ compound =>
    some (match compound with | some p => p.bytes | none => bits / 8)
  | .mapWrite _ _ _ _ bits _ => some (bits / 8)
  | _ => none

/-- Frozen-source bytes in increasing memory offset, by the fixed LE definition. -/
def storeByteTerms (bytes : Nat) (source : Term) : List CrossTerm :=
  (List.range bytes).map fun j =>
    toCrossTerm (star source.width (.extract (8 * j) 8 source.width.bits) [source])

/-- Little-endian store bytes, each evaluated from the frozen source.
Only constants fold; open sources retain their byte extraction structure. -/
private def storeValue (bytes : Option Nat) (source : Term) : CrossValue :=
  match bytes with
  | none => .source (toCrossTerm source)
  | some n => .bytes (storeByteTerms n source)

/-- Frozen tails require the static map layout. ABI pointers never stand for keys.
Update tails: ABI map/keyPtr/valuePtr/flags, then key bytes, then value bytes. -/
def toCrossHelper (env : CrossEnv) (kind : HelperKind) (args : List Term) : CrossHelper :=
  let fallback := fun () => CrossHelper.other kind.id (crossTerms args)
  match args with
  | map :: _ =>
    let normalizedMap := toCrossTerm map
    match env.maps.find? (fun m => m.map == normalizedMap) with
    | none => fallback ()
    | some layout =>
      let tail := args.drop (helperArity kind)
      match kind with
      | .lookup => if args.length == 2 + layout.keyBytes && layout.keyBytes > 0 then
          .lookup normalizedMap (crossTerms tail) else fallback ()
      | .delete => if args.length == 2 + layout.keyBytes && layout.keyBytes > 0 then
          .mutation ⟨.delete, normalizedMap, crossTerms tail, 0, .bytes []⟩
          else fallback ()
      | .update =>
        if args.length == 4 + layout.keyBytes + layout.valueBytes && layout.keyBytes > 0 then
          .mutation ⟨.write, normalizedMap, crossTerms (tail.take layout.keyBytes), 0,
            .bytes (crossTerms (tail.drop layout.keyBytes))⟩
        else fallback ()
      | _ => fallback ()
  | [] => fallback ()

/-- Total and pure. Helper mutations and direct writes use the same outer tag. -/
def toCross (env : CrossEnv) (predicate : Predicate) : CrossPred :=
  let bytes := match predicate.storeBytes? with
    | some n => some n
    | none => env.storeBytes
  match predicate with
  | .helper _ kind args => match toCrossHelper env kind args with
    | .mutation m => .mapWrite m
    | h => .helper h
  | .branch _ dir cond => .branch ⟨dir, toCrossCond env cond⟩
  | .ret term => .ret ⟨toCrossTerm term⟩
  | .mapWrite _ map key offset _ source =>
    .mapWrite ⟨.write, toCrossTerm map, crossTerms key, offset, storeValue bytes source⟩
  | .packetWrite _ packet offset _ source compound =>
    .packetWrite ⟨packet, (match compound with | none => .c offset | some p => p.toCross),
      storeValue bytes source⟩

/-- The value component of a write observation. -/
def CrossPred.writeValue? : CrossPred → Option CrossValue
  | .mapWrite m => some m.value
  | .packetWrite p => some p.value
  | _ => none

theorem storeByteTerms_length (bytes : Nat) (source : Term) :
    (storeByteTerms bytes source).length = bytes := by
  simp [storeByteTerms]

theorem storeByteTerms_getElem (bytes : Nat) (source : Term) (j : Nat) (h : j < bytes) :
    (storeByteTerms bytes source)[j]'(by simpa [storeByteTerms] using h) =
      toCrossTerm (star source.width (.extract (8 * j) 8 source.width.bits) [source]) := by
  simp [storeByteTerms]

theorem toCross_mapWrite_bytes (env : CrossEnv) (event : Nat) (map : Term)
    (key : List Term) (offset bits : Nat) (source : Term) :
    (toCross env (.mapWrite event map key offset bits source)).writeValue? =
      some (.bytes (storeByteTerms (bits / 8) source)) := by
  rfl

theorem toCross_packetWrite_bytes (env : CrossEnv) (event packet offset bits : Nat)
    (source : Term) :
    (toCross env (.packetWrite event packet offset bits source none)).writeValue? =
      some (.bytes (storeByteTerms (bits / 8) source)) := by
  rfl

theorem toCross_compoundPacketWrite_bytes (env : CrossEnv)
    (event packet offset bits : Nat) (source : Term) (p : CompoundPacketReg) :
    (toCross env (.packetWrite event packet offset bits source (some p))).writeValue? =
      some (.bytes (storeByteTerms p.bytes source)) := by
  rfl

/-- Every sized write constructs exactly the byte count saved in that predicate. -/
theorem toCross_write_width (env : CrossEnv) (predicate : Predicate) (bytes : Nat)
    (h : predicate.storeBytes? = some bytes) :
    ∃ values, (toCross env predicate).writeValue? = some (.bytes values) ∧
      values.length = bytes := by
  cases predicate with
  | helper => simp [Predicate.storeBytes?] at h
  | branch => simp [Predicate.storeBytes?] at h
  | ret => simp [Predicate.storeBytes?] at h
  | mapWrite event map key offset bits source =>
    cases h
    exact ⟨_, toCross_mapWrite_bytes .., storeByteTerms_length ..⟩
  | packetWrite event packet offset bits source compound =>
    cases compound with
    | none =>
      cases h
      exact ⟨_, toCross_packetWrite_bytes .., storeByteTerms_length ..⟩
    | some p =>
      cases h
      exact ⟨_, toCross_compoundPacketWrite_bytes .., storeByteTerms_length ..⟩

/-- The fallback cannot affect any write with a predicate-owned width. -/
theorem toCross_write_storeBytes_irrelevant (env : CrossEnv) (predicate : Predicate)
    (bytes : Nat) (fallback : Option Nat) (h : predicate.storeBytes? = some bytes) :
    toCross { env with storeBytes := fallback } predicate = toCross env predicate := by
  cases predicate <;> simp_all [Predicate.storeBytes?, toCross]

private theorem crossTerms_length (terms : List Term) :
    (crossTerms terms).length = terms.length := by
  induction terms with
  | nil => simp [crossTerms]
  | cons t ts ih => simp [crossTerms, ih]

/-- A successful full lookup's key is the layout-sized frozen tail. -/
theorem toCrossHelper_lookup_full (env : CrossEnv) (args : List Term)
    (map : Term) (rest : List Term) (layout : CrossMapLayout)
    (ha : args = map :: rest)
    (hl : env.maps.find? (fun m => m.map == toCrossTerm map) = some layout)
    (hn : args.length = 2 + layout.keyBytes) (hk : 0 < layout.keyBytes) :
    toCrossHelper env .lookup args = .lookup (toCrossTerm map) (crossTerms (args.drop 2)) ∧
      (crossTerms (args.drop 2)).length = layout.keyBytes := by
  constructor
  · subst args
    simp [toCrossHelper, hl, helperArity, hn, hk]
  · rw [crossTerms_length, List.length_drop, hn]
    omega

theorem toCrossHelper_delete_full (env : CrossEnv) (args : List Term)
    (map : Term) (rest : List Term) (layout : CrossMapLayout)
    (ha : args = map :: rest)
    (hl : env.maps.find? (fun m => m.map == toCrossTerm map) = some layout)
    (hn : args.length = 2 + layout.keyBytes) (hk : 0 < layout.keyBytes) :
    toCrossHelper env .delete args =
      .mutation ⟨.delete, toCrossTerm map, crossTerms (args.drop 2), 0, .bytes []⟩ ∧
      (crossTerms (args.drop 2)).length = layout.keyBytes := by
  constructor
  · subst args
    simp [toCrossHelper, hl, helperArity, hn, hk]
  · rw [crossTerms_length, List.length_drop, hn]
    omega

/-- The update tail splits at the layout key size, leaving exactly its value size. -/
theorem toCrossHelper_update_full (env : CrossEnv) (args : List Term)
    (map : Term) (rest : List Term) (layout : CrossMapLayout)
    (ha : args = map :: rest)
    (hl : env.maps.find? (fun m => m.map == toCrossTerm map) = some layout)
    (hn : args.length = 4 + layout.keyBytes + layout.valueBytes)
    (hk : 0 < layout.keyBytes) :
    toCrossHelper env .update args =
      .mutation ⟨.write, toCrossTerm map,
        crossTerms ((args.drop 4).take layout.keyBytes), 0,
        .bytes (crossTerms ((args.drop 4).drop layout.keyBytes))⟩ ∧
      (args.drop 4).length = layout.keyBytes + layout.valueBytes ∧
      (crossTerms ((args.drop 4).take layout.keyBytes)).length = layout.keyBytes ∧
      (crossTerms ((args.drop 4).drop layout.keyBytes)).length = layout.valueBytes := by
  constructor
  · subst args
    simp [toCrossHelper, hl, helperArity, hn, hk]
  · have ht : (args.drop 4).length = layout.keyBytes + layout.valueBytes := by
      rw [List.length_drop, hn]
      omega
    refine ⟨ht, ?_, ?_⟩
    · rw [crossTerms_length, List.length_take, ht]
      omega
    · rw [crossTerms_length, List.length_drop, ht]
      omega

/-- Full-form classification itself supplies the lookup's layout and tail length. -/
theorem toCrossHelper_lookup_length (env : CrossEnv) (args : List Term)
    (map : CrossTerm) (key : List CrossTerm)
    (h : toCrossHelper env .lookup args = .lookup map key) :
    ∃ source rest layout, args = source :: rest ∧
      env.maps.find? (fun m => m.map == toCrossTerm source) = some layout ∧
      key = crossTerms (args.drop 2) ∧ key.length = layout.keyBytes := by
  cases args with
  | nil => simp [toCrossHelper] at h
  | cons source rest =>
    unfold toCrossHelper at h
    dsimp only at h
    split at h
    · simp at h
    · rename_i layout hl
      split at h
      · rename_i hn
        simp only [CrossHelper.lookup.injEq] at h
        obtain ⟨_, rfl⟩ := h
        refine ⟨source, rest, layout, rfl, hl, rfl, ?_⟩
        simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hn
        rw [crossTerms_length, List.length_drop]
        simp only [helperArity] at *
        omega
      · simp at h

theorem toCrossHelper_delete_length (env : CrossEnv) (args : List Term)
    (mutation : CrossMutation)
    (h : toCrossHelper env .delete args = .mutation mutation) :
    ∃ source rest layout, args = source :: rest ∧
      env.maps.find? (fun m => m.map == toCrossTerm source) = some layout ∧
      mutation.key = crossTerms (args.drop 2) ∧
      mutation.key.length = layout.keyBytes := by
  cases args with
  | nil => simp [toCrossHelper] at h
  | cons source rest =>
    unfold toCrossHelper at h
    dsimp only at h
    split at h
    · simp at h
    · rename_i layout hl
      split at h
      · rename_i hn
        cases h
        refine ⟨source, rest, layout, rfl, hl, rfl, ?_⟩
        simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hn
        simp only [helperArity, crossTerms_length, List.length_drop]
        omega
      · simp at h

theorem toCrossHelper_update_lengths (env : CrossEnv) (args : List Term)
    (mutation : CrossMutation)
    (h : toCrossHelper env .update args = .mutation mutation) :
    ∃ source rest layout values, args = source :: rest ∧
      env.maps.find? (fun m => m.map == toCrossTerm source) = some layout ∧
      mutation.key = crossTerms ((args.drop 4).take layout.keyBytes) ∧
      mutation.value = .bytes values ∧
      values = crossTerms ((args.drop 4).drop layout.keyBytes) ∧
      (args.drop 4).length = layout.keyBytes + layout.valueBytes ∧
      mutation.key.length = layout.keyBytes ∧ values.length = layout.valueBytes := by
  cases args with
  | nil => simp [toCrossHelper] at h
  | cons source rest =>
    unfold toCrossHelper at h
    dsimp only at h
    split at h
    · simp at h
    · rename_i layout hl
      split at h
      · rename_i hn
        cases h
        simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hn
        refine ⟨source, rest, layout, _, rfl, hl, rfl, rfl, rfl, ?_, ?_, ?_⟩
        all_goals
          simp only [helperArity, crossTerms_length, List.length_take, List.length_drop]
          omega
      · simp at h

/-- Only the three map helpers have this compare-level return contract. -/
inductive MapHelperId where
  | lookup | update | delete
  deriving DecidableEq, BEq, ReflBEq, LawfulBEq, Repr

def MapHelperId.id : MapHelperId → Nat
  | .lookup => 1
  | .update => 2
  | .delete => 3

/-- Semantic return identity uses frozen bytes, not a key/value pointer tail. -/
structure MapHelperReturn where
  helper : MapHelperId
  map : CrossTerm
  key : List CrossTerm
  isNull : Bool
  deriving DecidableEq, BEq, ReflBEq, LawfulBEq, Repr

def MapHelperReturn.lane0Prefix (r : MapHelperReturn) : List CrossTerm :=
  [.c r.helper.id, r.map]

def MapHelperReturn.toCrossReturn (r : MapHelperReturn) : CrossReturn :=
  ⟨.external 0 (r.lane0Prefix ++ r.key)⟩

def MapHelperReturn.nullComparison (r : MapHelperReturn) : CrossCond :=
  .plain ⟨.eq, 32⟩ (.c (if r.isNull then 0 else 1)) (.c 0)

theorem mapHelperReturn_deterministic (a b : MapHelperReturn)
    (hh : a.helper = b.helper) (hm : a.map = b.map) (hk : a.key = b.key)
    (hn : a.isNull = b.isNull) :
    a.lane0Prefix = b.lane0Prefix ∧ a.toCrossReturn = b.toCrossReturn ∧
      a.nullComparison = b.nullComparison := by
  cases a
  cases b
  simp_all

theorem mapHelperReturn_prefix_deterministic (a b : MapHelperReturn)
    (hh : a.helper = b.helper) (hm : a.map = b.map) :
    a.lane0Prefix = b.lane0Prefix := by
  simp [MapHelperReturn.lane0Prefix, hh, hm]

theorem mapHelperReturn_key_relevant (helper : MapHelperId) (map : CrossTerm)
    (a b : List CrossTerm) (isNull : Bool) (h : a ≠ b) :
    (MapHelperReturn.mk helper map a isNull).toCrossReturn ≠
      (MapHelperReturn.mk helper map b isNull).toCrossReturn := by
  simpa [MapHelperReturn.toCrossReturn, MapHelperReturn.lane0Prefix] using h

theorem mapHelperReturn_null_relevant (helper : MapHelperId) (map : CrossTerm)
    (key : List CrossTerm) :
    (MapHelperReturn.mk helper map key true).nullComparison ≠
      (MapHelperReturn.mk helper map key false).nullComparison := by
  simp [MapHelperReturn.nullComparison]

private def crossOpName : CrossOp → String
  | .add => "add" | .sub => "sub" | .mullo => "mullo" | .neg => "neg"
  | .udiv _ _ => "udiv" | .urem _ => "urem"
  | .sdiv _ _ => "sdiv" | .srem _ => "srem"
  | .mulh _ => "mulh" | .mulhu _ => "mulhu" | .mulhsu _ => "mulhsu"
  | .selectEq _ => "selectEq"
  | .id => "id" | .shl => "shl" | .lshr => "lshr" | .ashr => "ashr"
  | .ltu => "ltu" | .lts => "lts" | .and => "and" | .or => "or"
  | .xor => "xor" | .low _ => "low" | .extract _ _ => "extract"
  | .zext _ _ => "zext" | .sext _ _ => "sext" | .bswap _ _ => "bswap"
  | .inputByte _ => "inputByte" | .mergeLow _ _ => "mergeLow"
  | .linear => "linear"
  | .packetReg _ => "packetReg" | .packetRead _ _ => "packetRead"

private def crossOpParams : CrossOp → List Nat
  | .udiv bits z | .sdiv bits z => [bits, z]
  | .urem bits | .srem bits | .mulh bits | .mulhu bits
  | .mulhsu bits | .selectEq bits => [bits]
  | .low q | .inputByte q => [q]
  | .packetReg bytes => [bytes]
  | .packetRead bytes ending => [bytes, ending]
  | .extract a b | .zext a b | .sext a b | .bswap a b | .mergeLow a b => [a,b]
  | _ => []

mutual
  def renderCrossTermJson : CrossTerm → String
    | .c z => s!"\{\"kind\":\"c\",\"value\":\"{z}\"}"
    | .var name => s!"\{\"kind\":\"var\",\"name\":{name}}"
    | .reg kind alpha => s!"\{\"kind\":\"reg\",\"class\":{regRank kind},\"alpha\":{alpha}}"
    | .app op args =>
      let params := String.intercalate "," ((crossOpParams op).map toString)
      s!"\{\"kind\":\"app\",\"op\":\"{crossOpName op}\",\"params\":[{params}],\"args\":[{renderCrossTerms args}]}"
    | .external lane args =>
      s!"\{\"kind\":\"external\",\"lane\":{lane},\"args\":[{renderCrossTerms args}]}"
  termination_by t => sizeOf t

  private def renderCrossTerms : List CrossTerm → String
    | [] => ""
    | [t] => renderCrossTermJson t
    | t :: ts => renderCrossTermJson t ++ "," ++ renderCrossTerms ts
  termination_by ts => sizeOf ts
end

private def crossRelName : CrossRelKind → String
  | .eq => "eq" | .ne => "ne" | .ltu => "ltu" | .leu => "leu"
  | .gtu => "gtu" | .geu => "geu" | .lts => "lts" | .les => "les"
  | .gts => "gts" | .ges => "ges" | .bitsnz => "bitsnz" | .bitsz => "bitsz"

def renderCrossRelJson (rel : CrossRel) : String :=
  s!"\{\"kind\":\"{crossRelName rel.kind}\",\"q\":{rel.q}}"

private def renderCrossCondJson : CrossCond → String
  | .plain r a b => s!"\{\"kind\":\"plain\",\"rel\":{renderCrossRelJson r},\"lhs\":{renderCrossTermJson a},\"rhs\":{renderCrossTermJson b}}"
  | .packetBound b r o => s!"\{\"kind\":\"packetBound\",\"base\":{renderCrossTermJson b},\"rel\":{renderCrossRelJson r},\"offset\":{renderCrossTermJson o}}"
  | .packetField f r z => s!"\{\"kind\":\"packetField\",\"field\":{renderCrossTermJson f},\"rel\":{renderCrossRelJson r},\"value\":\"{z}\"}"

private def renderCrossValueJson : CrossValue → String
  | .bytes bs => s!"\{\"kind\":\"bytes\",\"values\":[{renderCrossTerms bs}]}"
  | .source t => s!"\{\"kind\":\"source\",\"term\":{renderCrossTermJson t}}"

private def renderCrossMutationJson (m : CrossMutation) : String :=
  let action := match m.kind with | .write => "write" | .delete => "delete"
  s!"\{\"action\":\"{action}\",\"map\":{renderCrossTermJson m.map},\"key\":[{renderCrossTerms m.key}],\"offset\":{m.offset},\"value\":{renderCrossValueJson m.value}}"

private def renderCrossHelperJson : CrossHelper → String
  | .lookup map key => s!"\{\"kind\":\"lookup\",\"map\":{renderCrossTermJson map},\"key\":[{renderCrossTerms key}]}"
  | .mutation m => s!"\{\"kind\":\"mutation\",\"mutation\":{renderCrossMutationJson m}}"
  | .other id args => s!"\{\"kind\":\"other\",\"helperId\":{id},\"args\":[{renderCrossTerms args}]}"

/-- Stable field order, compact ASCII labels; arbitrary integers are decimal strings. -/
def renderCrossPredJson : CrossPred → String
  | .helper h => s!"\{\"kind\":\"helper\",\"observation\":{renderCrossHelperJson h}}"
  | .branch b =>
    let dir := match b.dir with | .taken => "taken" | .notTaken => "notTaken"
    s!"\{\"kind\":\"branch\",\"dir\":\"{dir}\",\"cond\":{renderCrossCondJson b.cond}}"
  | .ret r => s!"\{\"kind\":\"ret\",\"payload\":{renderCrossTermJson r.payload}}"
  | .mapWrite m => s!"\{\"kind\":\"mapWrite\",\"mutation\":{renderCrossMutationJson m}}"
  | .packetWrite p =>
    let offset := match p.offset with
      | .c n => s!"\"offset\":{n}"
      | t => s!"\"offsetTerm\":{renderCrossTermJson t}"
    s!"\{\"kind\":\"packetWrite\",\"packet\":{p.packet},{offset},\"value\":{renderCrossValueJson p.value}}"

/-! General proofs. Finite fixture checks below are not semantic equivalence proofs. -/

private theorem signed_small32 (n : Nat) (h : n < 2^31) : s 32 n = Int.ofNat n := by
  have hn : n < (1 <<< 32 : Nat) := by
    change n < 4294967296
    have : n < 2147483648 := h
    omega
  have hh : n < (1 <<< (32 - 1) : Nat) := h
  unfold s MNat
  rw [Nat.mod_eq_of_lt hn, if_pos hh]

private theorem signed_small64 (n : Nat) (h : n < 2^31) : s 64 n = Int.ofNat n := by
  have hn : n < (1 <<< 64 : Nat) := by
    change n < 18446744073709551616
    have : n < 2147483648 := h
    omega
  have hh : n < (1 <<< (64 - 1) : Nat) := by
    change n < 9223372036854775808
    have : n < 2147483648 := h
    omega
  unfold s MNat
  rw [Nat.mod_eq_of_lt hn, if_pos hh]

theorem cross_return_small (env : CrossEnv) (n : Nat) (h : n < 2^31) :
    toCross env (.ret (.C32 n)) = toCross env (.ret (.C64 n)) := by
  have h32 : n < (1 <<< 32 : Nat) := by
    change n < 4294967296
    have : n < 2147483648 := h
    omega
  have h64 : n < (1 <<< 64 : Nat) := by
    change n < 18446744073709551616
    have : n < 2147483648 := h
    omega
  simp only [toCross, Term.C32, Term.C64, Term.C, Width.bits,
    MNat, Nat.mod_eq_of_lt h32, Nat.mod_eq_of_lt h64, toCrossTerm,
    signed_small32 n h, signed_small64 n h]

theorem cross_rel_dual (q : Nat) (r : Rel) (swap : Bool) :
    toCrossRel q r.crossDual (!swap) = toCrossRel q r swap := by
  cases r <;> cases swap <;> rfl

theorem cross_rel_plain_eqN (q : Nat) (swap : Bool) :
    toCrossRel q .eq swap = toCrossRel q (.eqN q) swap := by rfl

theorem rel_gtu_swap (a b : Nat) :
    interpretRel 64 .gtu a b = interpretRel 64 .ltu b a := by rfl

theorem rel_leu_swap (a b : Nat) :
    interpretRel 64 .leu a b = interpretRel 64 .geu b a := by rfl

theorem rel_geu_swap (a b : Nat) :
    interpretRel 64 .geu a b = interpretRel 64 .leu b a := by rfl

theorem rel_gts_swap (a b : Nat) :
    interpretRel 64 .gts a b = interpretRel 64 .lts b a := by rfl

theorem rel_les_swap (a b : Nat) :
    interpretRel 64 .les a b = interpretRel 64 .ges b a := by rfl

theorem rel_ges_swap (a b : Nat) :
    interpretRel 64 .ges a b = interpretRel 64 .les b a := by rfl

theorem rel_explicit_dual_swap (w q a b : Nat) :
    interpretRel w (.gtuN q) a b = interpretRel w (.ltuN q) b a ∧
    interpretRel w (.leuN q) a b = interpretRel w (.geuN q) b a ∧
    interpretRel w (.gtsN q) a b = interpretRel w (.ltsN q) b a ∧
    interpretRel w (.lesN q) a b = interpretRel w (.gesN q) b a := by
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- Carrier inputs must already represent the values, as well as fitting low q. -/
theorem rel_eqN_small (w q a b : Nat)
    (ha : a < (1 <<< q)) (hb : b < (1 <<< q))
    (hwa : a < (1 <<< w)) (hwb : b < (1 <<< w)) :
    interpretRel w (.eqN q) a b = (a == b) := by
  simp [interpretRel, MNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb,
    Nat.mod_eq_of_lt hwa, Nat.mod_eq_of_lt hwb]

theorem cross_branch_position (env : CrossEnv) (p₁ p₂ : Nat) (d : BranchDirection) (c : Cond) :
    toCross env (.branch p₁ d c) = toCross env (.branch p₂ d c) := by rfl

theorem cross_helper_event (env : CrossEnv) (ε ε' : Nat) (h : HelperKind) (args : List Term) :
    toCross env (.helper ε h args) = toCross env (.helper ε' h args) := by rfl

theorem cross_mutation_eq (x y : CrossMutation) :
    x = y ↔ x.kind = y.kind ∧ x.map = y.map ∧ x.key = y.key ∧
      x.offset = y.offset ∧ x.value = y.value := by
  cases x; cases y; simp only [CrossMutation.mk.injEq]

theorem cross_mutation_decide (x y : CrossMutation) :
    decide (x = y) = true ↔ x = y := by simp

theorem cross_pred_beq (x y : CrossPred) : (x == y) = true ↔ x = y := by
  exact beq_iff_eq

private theorem ordering_swap_then (a b : Ordering) :
    (a.then b).swap = a.swap.then b.swap := by cases a <;> rfl

private theorem ordering_then_eq (a b : Ordering) :
    a.then b = .eq ↔ a = .eq ∧ b = .eq := by cases a <;> simp [Ordering.then]

private theorem nat_one_swap (a b : Nat) :
    ((compare a b).then .eq).swap = (compare b a).then .eq := by
  rw [ordering_swap_then, Nat.compare_swap]; rfl

private theorem nat_two_swap (a b c d : Nat) :
    ((compare a b).then ((compare c d).then .eq)).swap =
      (compare b a).then ((compare d c).then .eq) := by
  rw [ordering_swap_then, ordering_swap_then, Nat.compare_swap, Nat.compare_swap]; rfl

private theorem nat_one_eq (a b : Nat) (h : (compare a b).then .eq = .eq) : a = b :=
  Nat.compare_eq_eq.mp ((ordering_then_eq _ _).mp h).1

private theorem nat_two_eq (a b c d : Nat)
    (h : (compare a b).then ((compare c d).then .eq) = .eq) : a = b ∧ c = d :=
  ⟨Nat.compare_eq_eq.mp ((ordering_then_eq _ _).mp h).1,
    nat_one_eq _ _ ((ordering_then_eq _ _).mp h).2⟩

private theorem crossOp_compare_swap (a b : CrossOp) :
    (compare a b).swap = compare b a := by
  cases a <;> cases b <;> first | rfl | exact nat_one_swap _ _ | exact nat_two_swap _ _ _ _

private theorem crossOp_compare_eq (a b : CrossOp) (h : compare a b = .eq) : a = b := by
  cases a <;> cases b <;> first
    | rfl
    | contradiction
    | (congr 1; exact nat_one_eq _ _ h)
    | (obtain ⟨rfl, rfl⟩ := nat_two_eq _ _ _ _ h; rfl)

mutual
  private theorem crossCompare_swap (a b : CrossTerm) :
      (crossCompare a b).swap = crossCompare b a := by
    cases a <;> cases b <;> simp only [crossCompare, crossRank] <;>
      try first | rfl | exact Int.compare_swap _ _ | exact Nat.compare_swap _ _
    case reg.reg k x l y =>
      change ((compare (regRank k) (regRank l)).then (compare x y)).swap = _
      rw [ordering_swap_then, Nat.compare_swap, Nat.compare_swap]
      rfl
    case app.app f xs g ys =>
      change ((compare f g).then (crossCompareList xs ys)).swap = _
      rw [ordering_swap_then, crossOp_compare_swap, crossCompareList_swap]
      rfl
    case external.external x xs y ys =>
      change ((compare x y).then (crossCompareList xs ys)).swap = _
      rw [ordering_swap_then, Nat.compare_swap, crossCompareList_swap]
      rfl
  termination_by sizeOf a + sizeOf b

  private theorem crossCompareList_swap (xs ys : List CrossTerm) :
      (crossCompareList xs ys).swap = crossCompareList ys xs := by
    cases xs with
    | nil => cases ys <;> simp [crossCompareList]
    | cons x xs =>
      cases ys with
      | nil => simp [crossCompareList]
      | cons y ys =>
        simp only [crossCompareList]
        change ((crossCompare x y).then (crossCompareList xs ys)).swap = _
        rw [ordering_swap_then, crossCompare_swap, crossCompareList_swap]
        rfl
  termination_by sizeOf xs + sizeOf ys
end

private theorem regRank_compare_eq (k l : RegKind)
    (h : compare (regRank k) (regRank l) = .eq) : k = l := by
  have heq := Nat.compare_eq_eq.mp h
  cases k <;> cases l <;> simp_all [regRank]

mutual
  private theorem crossCompare_eq (a b : CrossTerm) (h : crossCompare a b = .eq) :
      a = b := by
    cases a <;> cases b <;> simp only [crossCompare, crossRank] at h <;> try contradiction
    case c.c x y => exact congrArg CrossTerm.c (Int.compare_eq_eq.mp h)
    case var.var x y => exact congrArg CrossTerm.var (Nat.compare_eq_eq.mp h)
    case reg.reg k x l y =>
      have hh := (ordering_then_eq _ _).mp h
      have hk := regRank_compare_eq _ _ hh.1
      have hx := Nat.compare_eq_eq.mp hh.2
      subst l; subst y; rfl
    case app.app f xs g ys =>
      have hh := (ordering_then_eq _ _).mp h
      have hf := crossOp_compare_eq _ _ hh.1
      have hxs := crossCompareList_eq _ _ hh.2
      subst g; subst ys; rfl
    case external.external x xs y ys =>
      have hh := (ordering_then_eq _ _).mp h
      have hx := Nat.compare_eq_eq.mp hh.1
      have hxs := crossCompareList_eq _ _ hh.2
      subst y; subst ys; rfl
  termination_by sizeOf a + sizeOf b

  private theorem crossCompareList_eq (xs ys : List CrossTerm)
      (h : crossCompareList xs ys = .eq) : xs = ys := by
    cases xs with
    | nil => cases ys <;> simp_all [crossCompareList]
    | cons x xs =>
      cases ys with
      | nil => simp [crossCompareList] at h
      | cons y ys =>
        simp only [crossCompareList] at h
        have hh := (ordering_then_eq _ _).mp h
        have hx := crossCompare_eq _ _ hh.1
        have hxs := crossCompareList_eq _ _ hh.2
        subst y; subst ys; rfl
  termination_by sizeOf xs + sizeOf ys
end

private theorem crossCompare_gt_iff (a b : CrossTerm) :
    crossCompare a b = .gt ↔ crossCompare b a = .lt := by
  have hs := crossCompare_swap b a
  rw [← hs]
  cases crossCompare b a <;> simp

/-- The same-width modular-addition premise of R1; not interpretation preservation. -/
theorem cross_add_mod_comm (w : Nat) (a b : Int) :
    (a + b) % (2 ^ w : Int) = (b + a) % (2 ^ w : Int) := by
  rw [Int.add_comm a b]

theorem cross_term_add_comm (w₁ w₂ q : Width) (a b : Term) :
    toCrossTerm (.app w₁ (.add q) [a,b]) =
      toCrossTerm (.app w₂ (.add q) [b,a]) := by
  cases h : crossCompare (toCrossTerm a) (toCrossTerm b) with
  | lt =>
    have hb := (crossCompare_gt_iff (toCrossTerm b) (toCrossTerm a)).mpr h
    simp [toCrossTerm, crossBinary, h, hb]
  | gt =>
    have hb := (crossCompare_gt_iff (toCrossTerm a) (toCrossTerm b)).mp h
    simp [toCrossTerm, crossBinary, h, hb]
  | eq =>
    have heq := crossCompare_eq _ _ h
    simp [toCrossTerm, crossBinary, heq]

theorem cross_term_id (w : Width) (t : Term) :
    toCrossTerm (.app w (.id w) [t]) = toCrossTerm t := by
  simp [toCrossTerm, crossUnary, identityCast]

theorem cross_term_extract (w : Width) (v : Nat) (t : Term) :
    toCrossTerm (.app w (.extract 0 v v) [t]) = toCrossTerm t := by
  simp [toCrossTerm, crossUnary, identityCast]

/-- Structural R5 recognition; its value-domain bridge is
`cross_extract_represented_interpret`. -/
theorem cross_term_extract_represented (w : Width) (n v : Nat) (t : Term)
    (hwidth : (toCrossTerm t).compareBits = 32) (h : (toCrossTerm t).compareBits ≤ n) :
    toCrossTerm (.app w (.extract 0 n v) [t]) = toCrossTerm t := by
  have hn : 32 ≤ n := by simpa [hwidth] using h
  by_cases hv : n = v <;> simp [toCrossTerm, crossUnary, identityCast, hn, hv, hwidth]

/-- Structural recognition of R6. `cross_carry_interpret` proves the numeric
bridge under explicit same-element word-content and residue premises. -/
theorem cross_term_add_carry (w q : Width) (h c : Term)
    (lane : Nat) (i k : Int) (l : CrossTerm)
    (hh : toCrossTerm h = .external lane [.c i])
    (hc : toCrossTerm c = .app .ltu [.app .add [l, .c k], .c k])
    (hlane : 1 ≤ lane) :
    toCrossTerm (.app w (.add q) [h,c]) =
      .app (.extract 32 32) [.app .add [l, .c k]] := by
  have hcmp : compare (4 : Nat) 3 = .gt := by decide
  simp [toCrossTerm, crossBinary, crossCompare, crossRank, hh, hc, crossAdd, hlane, hcmp]

theorem cross_term_zext (w : Width) (v : Nat) (t : Term) :
    toCrossTerm (.app w (.zext v w v) [t]) = toCrossTerm t := by
  simp [toCrossTerm, crossUnary, identityCast]

theorem cross_term_zext_carrier (w out : Width) (q v : Nat) (t : Term) (h : q ≤ v) :
    toCrossTerm (.app w (.zext q out v) [t]) = toCrossTerm t := by
  simp [toCrossTerm, crossUnary, identityCast, h]

theorem cross_term_and_carrier (w₁ w₂ : Width) (q₁ q₂ : Nat) (a b : Term) :
    toCrossTerm (.app w₁ (.and q₁) [a,b]) =
      toCrossTerm (.app w₂ (.and q₂) [a,b]) := by
  simp [toCrossTerm, crossBinary, crossOp]

theorem cross_term_or_carrier (w₁ w₂ : Width) (q₁ q₂ : Nat) (a b : Term) :
    toCrossTerm (.app w₁ (.or q₁) [a,b]) =
      toCrossTerm (.app w₂ (.or q₂) [a,b]) := by
  simp [toCrossTerm, crossBinary, crossOp]

theorem cross_term_xor_carrier (w₁ w₂ : Width) (q₁ q₂ : Nat) (a b : Term) :
    toCrossTerm (.app w₁ (.xor q₁) [a,b]) =
      toCrossTerm (.app w₂ (.xor q₂) [a,b]) := by
  simp [toCrossTerm, crossBinary, crossOp]

theorem cross_term_low (w : Width) (v : Nat) (t : Term) :
    toCrossTerm (.app w (.low v v) [t]) = toCrossTerm t := by
  simp [toCrossTerm, crossUnary, identityCast]

theorem cross_term_or_zero (w : Width) (q : Nat) (t z : Term)
    (hz : toCrossTerm z = .c 0) :
    toCrossTerm (.app w (.or q) [z,t]) = toCrossTerm t ∧
      toCrossTerm (.app w (.or q) [t,z]) = toCrossTerm t := by
  by_cases ht : toCrossTerm t = .c 0 <;> simp [toCrossTerm, crossBinary, hz, ht]

theorem cross_term_xor_zero (w : Width) (q : Nat) (t z : Term)
    (hz : toCrossTerm z = .c 0) :
    toCrossTerm (.app w (.xor q) [z,t]) = toCrossTerm t ∧
      toCrossTerm (.app w (.xor q) [t,z]) = toCrossTerm t := by
  by_cases ht : toCrossTerm t = .c 0 <;> simp [toCrossTerm, crossBinary, hz, ht]

theorem cross_term_shift_zero (w q : Width) (t z : Term)
    (hz : toCrossTerm z = .c 0) :
    toCrossTerm (.app w (.shl q) [t,z]) = toCrossTerm t ∧
      toCrossTerm (.app w (.lshr q) [t,z]) = toCrossTerm t ∧
      toCrossTerm (.app w (.ashr q) [t,z]) = toCrossTerm t := by
  simp [toCrossTerm, crossBinary, hz]

/-- Full-input identity and R5 represented-value erasure take priority over R4. -/
theorem cross_term_extract_sext (w : Width) (o n v q input : Nat)
    (t : Term) (x : CrossTerm)
    (hview : toCrossTerm t = .app (.sext q input) [x])
    (hcast : ¬ (o = 0 ∧ n = v)) (hrepresented : ¬ (o = 0 ∧ q = 32 ∧ q ≤ n))
    (h : o + n ≤ q) :
    toCrossTerm (.app w (.extract o n v) [t]) = .app (.extract o n) [x] := by
  simp [toCrossTerm, crossUnary, identityCast, hview, hcast,
    CrossTerm.compareBits, h] <;> omega

private def envR : CrossEnv :=
  { packetBase := some (Term.V32 4), packetEnd := parseTerm "add32(v32:4,v32:5)" }
private def envE : CrossEnv :=
  { packetBase := some (Term.V32 4), packetEnd := parseTerm "add32(v32:4,128)" }

private def parsedCross (env : CrossEnv) (wire : String) : Option CrossPred := do
  let json ← (Lean.Json.parse wire).toOption
  let p ← parsePredicateJson json
  pure (toCross env p)

private def boundRT : String := "{\"kind\":\"branch\",\"position\":10,\"dir\":\"taken\",\"width\":32,\"cond\":{\"lhs\":\"add32(v32:4,v32:5)\",\"rel\":\"ltu\",\"rhs\":\"add32(v32:4,14)\"}}"
private def boundET : String := "{\"kind\":\"branch\",\"position\":6,\"dir\":\"taken\",\"width\":64,\"cond\":{\"lhs\":\"id64(add64(id64(zext32/64/32(extract0,32(v32:4))),14))\",\"rel\":\"gtu\",\"rhs\":\"zext32/64/32(extract0,32(add32(v32:4,128)))\"}}"
private def boundRF : String := "{\"kind\":\"branch\",\"position\":10,\"dir\":\"notTaken\",\"width\":32,\"cond\":{\"lhs\":\"add32(v32:4,v32:5)\",\"rel\":\"geu\",\"rhs\":\"add32(v32:4,14)\"}}"
private def boundEF : String := "{\"kind\":\"branch\",\"position\":6,\"dir\":\"notTaken\",\"width\":64,\"cond\":{\"lhs\":\"id64(add64(id64(zext32/64/32(extract0,32(v32:4))),14))\",\"rel\":\"leu\",\"rhs\":\"zext32/64/32(extract0,32(add32(v32:4,128)))\"}}"
private def lookupA : String := "{\"kind\":\"branch\",\"position\":48,\"dir\":\"taken\",\"width\":32,\"cond\":{\"lhs\":\"id32(externalResult747_0(1,1077412584,id32(add32(v32:0,4294967280))))\",\"rel\":\"eq\",\"rhs\":\"0\"}}"
private def lookupB : String := "{\"kind\":\"branch\",\"position\":48,\"dir\":\"taken\",\"width\":32,\"cond\":{\"lhs\":\"id32(externalResult517_0(1,1077412584,id32(add32(v32:0,4294967280))))\",\"rel\":\"eq\",\"rhs\":\"0\"}}"

private def sameParsed (a b : Option CrossPred) : Bool :=
  match a, b with
  | some x, some y => x == y
  | _, _ => false

#guard sameParsed (parsedCross envR boundRT) (parsedCross envE boundET)
#guard sameParsed (parsedCross envR boundRF) (parsedCross envE boundEF)
#guard match parsedCross envR boundRT, parsedCross envE boundET with
  | some a, some b => renderCrossPredJson a == renderCrossPredJson b
  | _, _ => false
#guard toCross envR (.ret (.C32 1)) == toCross envR (.ret (.C64 1))
#guard sameParsed (parsedCross envR "{\"kind\":\"ret\",\"width\":32,\"term\":\"1\"}")
  (parsedCross envE "{\"kind\":\"ret\",\"width\":64,\"term\":\"1\"}")
#guard sameParsed (parsedCross envR lookupA) (parsedCross envR lookupB)
#guard parsedCross envR boundRT == some (.branch ⟨.taken,
  .packetBound (.var 4) ⟨.ltu, 32⟩ (.app .add [.var 4, .c 14])⟩)
#guard parsedCross envR boundRF == some (.branch ⟨.notTaken,
  .packetBound (.var 4) ⟨.geu, 32⟩ (.app .add [.var 4, .c 14])⟩)
#guard toCrossTerm (.C32 4294967280) == toCrossTerm (.C64 18446744073709551600)

private def mutationEnv : CrossEnv :=
  { maps := [⟨.c 42, 1, 4⟩] }
#guard toCross mutationEnv (.mapWrite 7 (.C32 42) [.C32 9] 0 32 (.C32 0x04030201)) ==
  toCross mutationEnv (.helper 8 .update
    [.C64 42, .V64 100, .V64 101, .C64 0, .C64 9, .C64 1, .C64 2, .C64 3, .C64 4])
#guard toCross mutationEnv (.helper 7 .lookup [.C32 42, .V32 100, .C32 9]) ==
  toCross mutationEnv (.helper 8 .lookup [.C64 42, .V64 200, .C64 9])
#guard toCrossTerm (.regVar 7 (Reg.mapWord 7 4)) ==
  toCrossTerm (.regVar 8 (Reg.mapDword 8 4))

/-! ## Normalization ABI -/

/-- Env wire keys. Unknown keys reject; every key is optional. Terms use the shared
Meta term grammar (`parseTerm`) and are normalized through `toCrossTerm`. -/
private def crossEnvKeys : List String :=
  ["packetBase", "packetEnd", "maps", "storeBytes", "storeBigEndian"]

/-- Object whose keys are drawn from `allowed` and which contains every `required` key. -/
private def envFields (value : Lean.Json) (allowed required : List String) : Bool :=
  match value.getObj? with
  | .error _ => false
  | .ok obj => obj.keys.all (fun k => allowed.contains k) && required.all obj.contains

private def envStr (value : Lean.Json) (key : String) : Option String :=
  (value.getObjVal? key >>= Lean.Json.getStr?).toOption
private def envNat (value : Lean.Json) (key : String) : Option Nat :=
  (value.getObjVal? key >>= Lean.Json.getNat?).toOption
private def optTerm (value : Lean.Json) (key : String) : Option (Option Term) :=
  match value.getObjVal? key with
  | .error _ => some none
  | .ok field => do
    let text ← field.getStr?.toOption
    pure (some (← parseTerm text))
private def optNat (value : Lean.Json) (key : String) : Option (Option Nat) :=
  match value.getObjVal? key with
  | .error _ => some none
  | .ok field => do
    pure (some (← field.getNat?.toOption))
private def optBool (value : Lean.Json) (key : String) : Option (Option Bool) :=
  match value.getObjVal? key with
  | .error _ => some none
  | .ok field => do
    pure (some (← field.getBool?.toOption))

private def parseCrossMapLayout (value : Lean.Json) : Option CrossMapLayout := do
  if !envFields value ["map", "keyBytes", "valueBytes"] ["map", "keyBytes", "valueBytes"] then
    none
  pure ⟨toCrossTerm (← parseTerm (← envStr value "map")),
    ← envNat value "keyBytes", ← envNat value "valueBytes"⟩

/-- Env wire object → `CrossEnv`. Unknown keys and malformed terms reject. Every field
is optional; `storeBigEndian` is accepted as a legacy Bool and ignored. Terms are
normalized by `toCrossTerm`, so a map key is a static resource binding. -/
def parseCrossEnvJson (value : Lean.Json) : Option CrossEnv := do
  if !envFields value crossEnvKeys [] then none
  let packetBase ← optTerm value "packetBase"
  let packetEnd ← optTerm value "packetEnd"
  let maps ← match value.getObjVal? "maps" with
    | .error _ => some []
    | .ok field => (← field.getArr?.toOption).toList.mapM parseCrossMapLayout
  let storeBytes ← optNat value "storeBytes"
  let _ ← optBool value "storeBigEndian"
  pure { packetBase, packetEnd, maps, storeBytes }

private def parseCrossEnvText (text : String) : Option CrossEnv :=
  (Lean.Json.parse text).toOption >>= parseCrossEnvJson

/-- Boxed Lean String ABI: `envJson` (env wire object) and `predJson` (one Predicate
object) → `renderCrossPredJson (toCross env p)` bytes, or the four characters `null`
on any parse or environment failure. -/
@[export lean_cross_pred_normalize]
def exportCrossPredNormalize (envJson predJson : String) : String :=
  let result : Option String := do
    let env ← parseCrossEnvText envJson
    let pred ← (Lean.Json.parse predJson).toOption >>= parsePredicateJson
    pure (renderCrossPredJson (toCross env pred))
  result.getD "null"

private def envRJson : String := "{\"packetBase\":\"v32:4\",\"packetEnd\":\"add32(v32:4,v32:5)\"}"
private def envEJson : String := "{\"packetBase\":\"v32:4\",\"packetEnd\":\"add32(v32:4,128)\"}"
private def mutationEnvJson : String :=
  "{\"maps\":[{\"map\":\"42\",\"keyBytes\":1,\"valueBytes\":4}]}"
private def ret32 : String := "{\"kind\":\"ret\",\"width\":32,\"term\":\"1\"}"
private def ret64 : String := "{\"kind\":\"ret\",\"width\":64,\"term\":\"1\"}"

#guard parseCrossEnvText envRJson == some envR
#guard parseCrossEnvText envEJson == some envE
#guard parseCrossEnvText mutationEnvJson == some mutationEnv
#guard exportCrossPredNormalize envRJson boundRT == exportCrossPredNormalize envEJson boundET
#guard exportCrossPredNormalize envRJson boundRF == exportCrossPredNormalize envEJson boundEF
#guard exportCrossPredNormalize envRJson boundRT ==
  ((parsedCross envR boundRT).map renderCrossPredJson).getD "null"
#guard exportCrossPredNormalize envRJson ret32 == exportCrossPredNormalize envEJson ret64
#guard exportCrossPredNormalize envRJson ret32 ==
  "{\"kind\":\"ret\",\"payload\":{\"kind\":\"c\",\"value\":\"1\"}}"
#guard exportCrossPredNormalize envRJson boundRT ==
  "{\"kind\":\"branch\",\"dir\":\"taken\",\"cond\":{\"kind\":\"packetBound\",\"base\":{\"kind\":\"var\",\"name\":4},\"rel\":{\"kind\":\"ltu\",\"q\":32},\"offset\":{\"kind\":\"app\",\"op\":\"add\",\"params\":[],\"args\":[{\"kind\":\"var\",\"name\":4},{\"kind\":\"c\",\"value\":\"14\"}]}}}"
#guard exportCrossPredNormalize envRJson "{" == "null"
#guard exportCrossPredNormalize "{" boundRT == "null"
#guard exportCrossPredNormalize "{\"bogus\":1}" boundRT == "null"
#guard exportCrossPredNormalize envRJson "{\"kind\":\"ret\",\"width\":16,\"term\":\"0\"}" == "null"
#guard exportCrossPredNormalize "{\"maps\":[{\"map\":\"42\",\"keyBytes\":1}]}" ret32 == "null"

-- Measured dual just_tx nodes 9, 77 and 29; normalization checks must not accept null.
private def liveEthertypeR : String :=
  "{\"kind\":\"branch\",\"position\":25,\"dir\":\"taken\",\"width\":32,\"cond\":{\"lhs\":\"or32(or32(0,shl32(zext8/32(low8(inputByte0(v32:4,add32(v32:4,16)))),0)),shl32(zext8/32(low8(inputByte0(v32:4,add32(v32:4,17)))),8))\",\"rel\":\"eq\",\"rhs\":\"56710\"}}"
private def liveEthertypeE : String :=
  "{\"kind\":\"branch\",\"position\":17,\"dir\":\"taken\",\"width\":64,\"cond\":{\"lhs\":\"or64(or64(0,shl64(zext8/64/32(low8(inputByte0(v32:4,add32(v32:4,16)))),0)),shl64(zext8/64/32(low8(inputByte0(v32:4,add32(v32:4,17)))),8))\",\"rel\":\"eqN32\",\"rhs\":\"56710\"}}"
private def liveByteFieldR : String :=
  "{\"kind\":\"branch\",\"position\":58,\"dir\":\"taken\",\"width\":32,\"cond\":{\"lhs\":\"or32(0,shl32(zext8/32(low8(inputByte0(v32:4,add32(v32:4,27)))),0))\",\"rel\":\"ne\",\"rhs\":\"17\"}}"
private def liveByteFieldE : String :=
  "{\"kind\":\"branch\",\"position\":44,\"dir\":\"taken\",\"width\":64,\"cond\":{\"lhs\":\"zext32/64/32(extract0,32(zext32/32/64(or64(0,shl64(zext8/64/32(low8(inputByte0(v32:4,add32(v32:4,27)))),0)))))\",\"rel\":\"neN32\",\"rhs\":\"17\"}}"
private def liveLookupNullR : String :=
  "{\"kind\":\"branch\",\"position\":48,\"dir\":\"taken\",\"width\":32,\"cond\":{\"lhs\":\"id32(externalResult489_0(1,1077412584,id32(add32(v32:0,4294967280))))\",\"rel\":\"eq\",\"rhs\":\"0\"}}"
private def liveLookupNullE : String :=
  "{\"kind\":\"branch\",\"position\":38,\"dir\":\"taken\",\"width\":64,\"cond\":{\"lhs\":\"externalResult85_0(1,1077412584,id64(add64(id64(v64:0),18446744073709551612)))\",\"rel\":\"eq\",\"rhs\":\"0\"}}"

private def sameNormalized (r e : String) : Bool :=
  let normalized := exportCrossPredNormalize envRJson r
  normalized != "null" && normalized == exportCrossPredNormalize envEJson e
private def liveEthertypeNormalize : Bool := sameNormalized liveEthertypeR liveEthertypeE
private def liveByteFieldNormalize : Bool := sameNormalized liveByteFieldR liveByteFieldE
private def liveLookupNullNormalize : Bool := sameNormalized liveLookupNullR liveLookupNullE
#guard liveEthertypeNormalize
#guard liveByteFieldNormalize
#guard liveLookupNullNormalize

private def opFixtures : List CrossOp :=
  [.add, .sub, .mullo, .neg, .id, .shl, .lshr, .ashr, .ltu, .lts,
   .and, .or, .xor, .low 16, .extract 8 16, .zext 64 32,
   .sext 64 32, .bswap 32 32, .inputByte 3, .mergeLow 32 8]
#guard opFixtures.map crossOpParams ==
  [[], [], [], [], [], [], [], [], [], [], [], [], [],
   [16], [8,16], [64,32], [64,32], [32,32], [3], [32,8]]

#guard toCrossTerm (.app .w32 (.externalResult 1 0) [.C32 1]) == .external 0 [.c 1]
#guard toCrossTerm (.app .w32 (.externalResult 1 2) [.C32 1, .C32 2, .C32 3]) ==
  .external 2 [.c 1, .c 2, .c 3]

namespace ABIPrefixFixtures

-- One lookup's return term and observation share the ABI prefix. Frozen bytes
-- belong only to the observation, exactly as in the helper generators.
private def lookupFixture (pointer : Term) (bytes : List Term) : Term × Predicate :=
  (.app .w32 (.externalResult 7 0) [.C32 1, .C32 42, pointer],
    .helper 7 .lookup ([.C32 42, pointer] ++ bytes))

private def normalizedLookup (pointer : Term) (bytes : List Term) : CrossTerm × CrossPred :=
  let (result, observation) := lookupFixture pointer bytes
  (toCrossTerm result, toCross mutationEnv observation)

private def returnAndFrozenKey : Bool :=
  normalizedLookup (.V32 100) [.C32 9] ==
    (.external 0 [.c 1, .c 42], .helper (.lookup (.c 42) [.c 9]))
#guard returnAndFrozenKey

private def droppedPointerEqual : Bool :=
  normalizedLookup (.V32 100) [.C32 9] == normalizedLookup (.V32 200) [.C32 9]
#guard droppedPointerEqual

private def differentFrozenKeyDistinct : Bool :=
  let a := normalizedLookup (.V32 100) [.C32 9]
  let b := normalizedLookup (.V32 200) [.C32 10]
  a.1 == b.1 && a.2 != b.2
#guard differentFrozenKeyDistinct

private def compareReturnFrozenKeyDistinct : Bool :=
  let a : MapHelperReturn := ⟨.lookup, .c 42, [.c 9], true⟩
  let b : MapHelperReturn := ⟨.lookup, .c 42, [.c 10], true⟩
  a.lane0Prefix == b.lane0Prefix && a.toCrossReturn != b.toCrossReturn &&
    a.nullComparison == b.nullComparison
#guard compareReturnFrozenKeyDistinct

private def complexEnv : CrossEnv :=
  { maps := [⟨.c 42, 4, 4⟩] }

private def complexPointer : Term :=
  .app .w32 (.add .w32) [.V32 4, .app .w32 (.add .w32) [.C32 18, .C32 40]]

private def differentComplexPointer : Term :=
  .app .w32 (.add .w32) [.V32 6, .app .w32 (.add .w32) [.C32 20, .C32 41]]

-- Node 15's four byte trees, with a nested constant offset inside inputByte.
private def complexKeyBytes (offset : String) : Option (List Term) :=
  ([0, 8, 16, 24] : List Nat).mapM fun bit =>
    parseTerm s!"extract{bit},8(or32(0,shl32(zext8/32(low8(inputByte0(v32:4,add32(v32:4,{offset})))),0)))"

private def normalizedComplexLookup (pointer : Term) (offset : String) :
    Option (CrossTerm × CrossPred) := do
  let bytes ← complexKeyBytes offset
  let (result, observation) := lookupFixture pointer bytes
  pure (toCrossTerm result, toCross complexEnv observation)

private def complexReturnPointerIndependent : Bool :=
  match normalizedComplexLookup complexPointer "add32(18,6)",
      normalizedComplexLookup differentComplexPointer "add32(18,6)" with
  | some a, some b =>
    a.1 == .external 0 [.c 1, .c 42] && b.1 == .external 0 [.c 1, .c 42]
  | _, _ => false
#guard complexReturnPointerIndependent

private def complexKeyNormalizes : Bool :=
  match normalizedComplexLookup complexPointer "add32(18,6)" with
  | some (_, .helper (.lookup (.c 42) key)) =>
    let byte : CrossTerm :=
      .app (.low 8) [.app (.inputByte 0) [.var 4, .app .add [.var 4, .c 24]]]
    key == [.app (.extract 0 8) [byte], .app (.extract 8 8) [byte],
      .app (.extract 16 8) [byte], .app (.extract 24 8) [byte]]
  | _ => false
#guard complexKeyNormalizes

private def complexDeepKeyDistinct : Bool :=
  match normalizedComplexLookup complexPointer "add32(18,6)",
      normalizedComplexLookup complexPointer "add32(18,7)" with
  | some a, some b => a.1 == b.1 && a.2 != b.2
  | _, _ => false
#guard complexDeepKeyDistinct

end ABIPrefixFixtures

-- Live 2026-10-14 20:20 pairs: loc is the host atom location, not position.
-- Branch directions below are forced from the compare-tree edge, as on the host.
private def liveEnvRJson : String :=
  "{\"packetBase\":\"v32:4\",\"packetEnd\":\"add32(v32:4,v32:5)\",\"maps\":[{\"map\":\"1077412584\",\"keyBytes\":4,\"valueBytes\":8}]}"
private def liveEnvEJson : String :=
  "{\"packetBase\":\"v32:4\",\"packetEnd\":\"add32(v32:4,128)\",\"maps\":[{\"map\":\"1077412584\",\"keyBytes\":4,\"valueBytes\":8}]}"
-- Node 15: RV loc76 / eBPF loc30 (raw eBPF notTaken becomes edge taken).
private def liveNode15BranchR : String :=
  "{\"kind\":\"branch\",\"cond\":{\"lhs\":\"add32(v32:4,v32:5)\",\"rel\":\"geu\",\"rhs\":\"add32(add32(18,v32:4),40)\"},\"dir\":\"taken\",\"position\":35,\"width\":32}"
private def liveNode15BranchE : String :=
  "{\"kind\":\"branch\",\"cond\":{\"lhs\":\"id64(add64(id64(id64(add64(id64(zext32/64/32(extract0,32(v32:4))),18))),40))\",\"rel\":\"leu\",\"rhs\":\"zext32/64/32(extract0,32(add32(v32:4,128)))\"},\"dir\":\"taken\",\"position\":30,\"width\":64}"
-- Node 31: RV loc35 / eBPF loc31, the ltu/gtu relation family.
private def liveNode31BranchR : String :=
  "{\"kind\":\"branch\",\"cond\":{\"lhs\":\"add32(v32:4,v32:5)\",\"rel\":\"ltu\",\"rhs\":\"add32(add32(18,v32:4),20)\"},\"dir\":\"taken\",\"position\":30,\"width\":32}"
private def liveNode31BranchE : String :=
  "{\"kind\":\"branch\",\"cond\":{\"lhs\":\"id64(add64(id64(id64(add64(id64(zext32/64/32(extract0,32(v32:4))),18))),20))\",\"rel\":\"gtu\",\"rhs\":\"zext32/64/32(extract0,32(add32(v32:4,128)))\"},\"dir\":\"taken\",\"position\":23,\"width\":64}"
-- Node 15 lookup: RV loc45 / eBPF loc37, four frozen key bytes.
private def liveNode15HelperR : String :=
  "{\"kind\":\"helper\",\"args\":[\"1077412584\",\"id32(add32(v32:0,4294967280))\",\"extract0,8(or32(0,shl32(zext8/32(low8(inputByte0(v32:4,add32(v32:4,24)))),0)))\",\"extract8,8(or32(0,shl32(zext8/32(low8(inputByte0(v32:4,add32(v32:4,24)))),0)))\",\"extract16,8(or32(0,shl32(zext8/32(low8(inputByte0(v32:4,add32(v32:4,24)))),0)))\",\"extract24,8(or32(0,shl32(zext8/32(low8(inputByte0(v32:4,add32(v32:4,24)))),0)))\"],\"event\":747,\"helperId\":1}"
private def liveNode15HelperE : String :=
  "{\"kind\":\"helper\",\"args\":[\"c64:1077412584\",\"t64(id64(add64(id64(v64:0),18446744073709551612)))\",\"t64(zext8/64/32(extract0,8(zext32/32/64(or64(0,shl64(zext8/64/32(low8(inputByte0(v32:4,add32(v32:4,24)))),0))))))\",\"t64(or64(0,shl64(zext8/64/32(extract8,8(zext32/32/64(or64(0,shl64(zext8/64/32(low8(inputByte0(v32:4,add32(v32:4,24)))),0))))),0)))\",\"t64(or64(0,shl64(zext8/64/32(extract16,8(zext32/32/64(or64(0,shl64(zext8/64/32(low8(inputByte0(v32:4,add32(v32:4,24)))),0))))),0)))\",\"t64(or64(0,shl64(zext8/64/32(extract24,8(zext32/32/64(or64(0,shl64(zext8/64/32(low8(inputByte0(v32:4,add32(v32:4,24)))),0))))),0)))\"],\"event\":386,\"helperId\":1}"
-- Node 46 write at offset 0: RV loc65 / eBPF loc47.
private def liveNode46WriteR : String :=
  "{\"kind\":\"packetWrite\",\"event\":849,\"offset\":0,\"packet\":0,\"source\":\"sext16/32(or32(or32(0,shl32(zext8/32(low8(inputByte0(v32:4,add32(v32:4,6)))),0)),shl32(zext8/32(low8(inputByte0(v32:4,add32(v32:4,7)))),8)))\",\"width\":16}"
private def liveNode46WriteE : String :=
  "{\"kind\":\"packetWrite\",\"event\":495,\"offset\":0,\"packet\":0,\"source\":\"t64(or64(or64(0,shl64(zext8/64/32(low8(inputByte0(v32:4,add32(v32:4,6)))),0)),shl64(zext8/64/32(low8(inputByte0(v32:4,add32(v32:4,7)))),8)))\",\"width\":16}"
-- Node 3 ethertype: RV loc16 / eBPF loc10, different VLAN disjuncts.
private def liveNode3EthertypeR : String :=
  "{\"kind\":\"branch\",\"cond\":{\"lhs\":\"or32(or32(0,shl32(zext8/32(low8(inputByte0(v32:4,add32(v32:4,12)))),0)),shl32(zext8/32(low8(inputByte0(v32:4,add32(v32:4,13)))),8))\",\"rel\":\"eq\",\"rhs\":\"43144\"},\"dir\":\"taken\",\"position\":14,\"width\":32}"
private def liveNode3EthertypeE : String :=
  "{\"kind\":\"branch\",\"cond\":{\"lhs\":\"or64(or64(0,shl64(zext8/64/32(low8(inputByte0(v32:4,add32(v32:4,12)))),0)),shl64(zext8/64/32(low8(inputByte0(v32:4,add32(v32:4,13)))),8))\",\"rel\":\"eqN32\",\"rhs\":\"129\"},\"dir\":\"taken\",\"position\":8,\"width\":64}"
private def liveNode15BranchNormalize : Bool :=
  let r := exportCrossPredNormalize liveEnvRJson liveNode15BranchR
  let e := exportCrossPredNormalize liveEnvEJson liveNode15BranchE
  r != "null" && e != "null" && r == e &&
    r == "{\"kind\":\"branch\",\"dir\":\"taken\",\"cond\":{\"kind\":\"packetBound\",\"base\":{\"kind\":\"var\",\"name\":4},\"rel\":{\"kind\":\"geu\",\"q\":32},\"offset\":{\"kind\":\"app\",\"op\":\"add\",\"params\":[],\"args\":[{\"kind\":\"var\",\"name\":4},{\"kind\":\"c\",\"value\":\"58\"}]}}}"
#guard liveNode15BranchNormalize

private def liveNode15FlatR : String :=
  "{\"kind\":\"branch\",\"cond\":{\"lhs\":\"add32(v32:4,v32:5)\",\"rel\":\"geu\",\"rhs\":\"add32(v32:4,58)\"},\"dir\":\"taken\",\"position\":35,\"width\":32}"
private def liveNode31FlatR : String :=
  "{\"kind\":\"branch\",\"cond\":{\"lhs\":\"add32(v32:4,v32:5)\",\"rel\":\"ltu\",\"rhs\":\"add32(v32:4,38)\"},\"dir\":\"taken\",\"position\":30,\"width\":32}"

#guard toCrossTerm (.app .w32 (.add .w32) [.app .w32 (.add .w32) [.V32 4, .C32 18], .C32 40]) ==
  .app .add [.var 4, .c 58]
#guard toCrossTerm (.app .w32 (.add .w32) [.app .w32 (.add .w32) [.C32 18, .V32 4], .C32 40]) ==
  .app .add [.var 4, .c 58]
#guard toCrossTerm (.app .w64 (.add .w64) [.app .w64 (.add .w64) [.V32 4, .C64 18], .C64 40]) ==
  .app .add [.var 4, .c 58]
#guard toCrossTerm (.app .w32 (.add .w32)
    [.app .w32 (.add .w32) [.app .w32 (.add .w32) [.V32 4, .C32 18], .C32 20], .C32 21]) ==
  .app .add [.var 4, .c 59]
#guard toCrossTerm (.app .w32 (.add .w32) [.app .w32 (.add .w32) [.V32 4, .C32 18], .C32 40]) ==
  toCrossTerm (.app .w64 (.add .w64) [.app .w64 (.add .w64) [.V64 4, .C64 18], .C64 40])
#guard toCrossTerm (.app .w32 (.add .w32) [.app .w32 (.add .w32) [.V32 4, .C32 18], .C32 20]) ==
  .app .add [.var 4, .c 38]
#guard toCrossTerm (.app .w32 (.add .w32) [.app .w32 (.add .w32) [.C32 18, .V32 4], .C32 20]) ==
  .app .add [.var 4, .c 38]
#guard toCrossTerm (.app .w32 (.add .w32) [.app .w32 (.add .w32) [.V32 4, .V32 5], .C32 10]) ==
  .app .add [.app .linear
    [.app .linear [.c 1, .var 4], .app .linear [.c 1, .var 5], .c 10], .app .linear []]

#guard toCrossTerm (.app .w32 (.add .w32) [.C32 40, .app .w32 (.add .w32) [.C32 18, .V32 4]]) ==
  .app .add [.var 4, .c 58]
#guard toCrossTerm (.app .w32 (.add .w32) [.app .w32 (.add .w32) [.V32 4, .C32 4294967280], .C32 15]) ==
  .app .add [.var 4, .c (-1)]
#guard toCrossTerm (.app .w32 (.add .w32) [.app .w32 (.add .w32) [.V32 4, .C32 4294967280], .C32 16]) ==
  .var 4
#guard toCrossTerm (.app .w32 (.add .w32) [.app .w32 (.add .w32) [.V32 4, .C32 2147483647], .C32 1]) ==
  .app .add [.var 4, .c (-2147483648)]
#guard (CrossTerm.compareBits (.app .add [.var 4, .c (-2147483648)])) == 32
#guard toCrossCond envR ⟨.app .w32 (.add .w32) [.V32 4, .V32 5], .geu,
    .app .w32 (.add .w32) [.app .w32 (.add .w32) [.V32 4, .C32 2147483647], .C32 1]⟩ ==
  .packetBound (.var 4) ⟨.geu, 32⟩ (.app .add [.var 4, .c (-2147483648)])
#guard toCrossTerm (.app .w32 (.add .w32) [.V32 4, .C32 0]) ==
  .var 4
#guard toCrossTerm (.app .w32 (.add .w32) [.V32 4, .C32 18, .C32 40]) ==
  .app .add [.var 4, .c 58]
#guard toCrossTerm (.app .w32 (.add .w32)
    [.app .w32 (.add .w32) [.V32 4, .C32 18, .C32 40], .C32 1]) ==
  .app .add [.var 4, .c 59]
#guard toCrossTerm (.app .w32 (.add .w32) [.V32 4]) == .var 4
#guard toCrossTerm (.app .w32 (.add .w32) []) == .c 0

#guard toCrossTerm (.app .w32 (.add .w32) [.C32 2147483647, .C32 1]) ==
  .c (-2147483648)
#guard (toCrossTerm (.app .w32 (.add .w32) [.C32 2147483647, .C32 1])).compareBits == 32
#guard normalizeCrossAdd 32 (.app .add [.var 4, .var 5]) !=
  normalizeCrossAdd 32 (.app .add [.var 4, .var 4])
#guard normalizeCrossAdd 32 (.app .add [.app .add [.var 6, .var 4], .var 5]) ==
  normalizeCrossAdd 32 (.app .add [.var 4, .app .add [.var 5, .var 6]])
#guard normalizeCrossAdd 32 (.app .add [.var 4, .var 4]) ==
  printAdd ([(2, .var 4)], 0)
#guard normalizeCrossAdd 32 (.app .add [.var 4, .var 4]) !=
  .app .mullo [.c 2, .var 4]
#guard normalizeCrossAdd 1 (.app .add [.var 4, .var 4]) == .c 0
#guard normalizeCrossAdd 32 (printAdd ([(2, .var 4), (1, .var 5)], 0)) ==
  printAdd ([(2, .var 4), (1, .var 5)], 0)
#guard exportCrossPredNormalize liveEnvRJson liveNode15BranchR ==
  exportCrossPredNormalize liveEnvRJson liveNode15FlatR
#guard exportCrossPredNormalize liveEnvRJson liveNode31BranchR ==
  exportCrossPredNormalize liveEnvRJson liveNode31FlatR

private def liveNode31BranchNormalize : Bool :=
  let r := exportCrossPredNormalize liveEnvRJson liveNode31BranchR
  let e := exportCrossPredNormalize liveEnvEJson liveNode31BranchE
  r != "null" && e != "null" && r == e
#guard liveNode31BranchNormalize

private def liveNode15HelperNormalize : Bool :=
  let r := exportCrossPredNormalize liveEnvRJson liveNode15HelperR
  let e := exportCrossPredNormalize liveEnvEJson liveNode15HelperE
  r != "null" && e != "null" && r == e &&
    r == "{\"kind\":\"helper\",\"observation\":{\"kind\":\"lookup\",\"map\":{\"kind\":\"c\",\"value\":\"1077412584\"},\"key\":[{\"kind\":\"app\",\"op\":\"extract\",\"params\":[0,8],\"args\":[{\"kind\":\"app\",\"op\":\"low\",\"params\":[8],\"args\":[{\"kind\":\"app\",\"op\":\"inputByte\",\"params\":[0],\"args\":[{\"kind\":\"var\",\"name\":4},{\"kind\":\"app\",\"op\":\"add\",\"params\":[],\"args\":[{\"kind\":\"var\",\"name\":4},{\"kind\":\"c\",\"value\":\"24\"}]}]}]}]},{\"kind\":\"app\",\"op\":\"extract\",\"params\":[8,8],\"args\":[{\"kind\":\"app\",\"op\":\"low\",\"params\":[8],\"args\":[{\"kind\":\"app\",\"op\":\"inputByte\",\"params\":[0],\"args\":[{\"kind\":\"var\",\"name\":4},{\"kind\":\"app\",\"op\":\"add\",\"params\":[],\"args\":[{\"kind\":\"var\",\"name\":4},{\"kind\":\"c\",\"value\":\"24\"}]}]}]}]},{\"kind\":\"app\",\"op\":\"extract\",\"params\":[16,8],\"args\":[{\"kind\":\"app\",\"op\":\"low\",\"params\":[8],\"args\":[{\"kind\":\"app\",\"op\":\"inputByte\",\"params\":[0],\"args\":[{\"kind\":\"var\",\"name\":4},{\"kind\":\"app\",\"op\":\"add\",\"params\":[],\"args\":[{\"kind\":\"var\",\"name\":4},{\"kind\":\"c\",\"value\":\"24\"}]}]}]}]},{\"kind\":\"app\",\"op\":\"extract\",\"params\":[24,8],\"args\":[{\"kind\":\"app\",\"op\":\"low\",\"params\":[8],\"args\":[{\"kind\":\"app\",\"op\":\"inputByte\",\"params\":[0],\"args\":[{\"kind\":\"var\",\"name\":4},{\"kind\":\"app\",\"op\":\"add\",\"params\":[],\"args\":[{\"kind\":\"var\",\"name\":4},{\"kind\":\"c\",\"value\":\"24\"}]}]}]}]}]}}"
#guard liveNode15HelperNormalize

private def liveNode46WriteBytesNormalize : Bool :=
  let r := exportCrossPredNormalize liveEnvRJson liveNode46WriteR
  let e := exportCrossPredNormalize liveEnvEJson liveNode46WriteE
  r != "null" && e != "null" && r == e &&
    r == "{\"kind\":\"packetWrite\",\"packet\":0,\"offset\":0,\"value\":{\"kind\":\"bytes\",\"values\":[{\"kind\":\"app\",\"op\":\"extract\",\"params\":[0,8],\"args\":[{\"kind\":\"app\",\"op\":\"or\",\"params\":[],\"args\":[{\"kind\":\"app\",\"op\":\"low\",\"params\":[8],\"args\":[{\"kind\":\"app\",\"op\":\"inputByte\",\"params\":[0],\"args\":[{\"kind\":\"var\",\"name\":4},{\"kind\":\"app\",\"op\":\"add\",\"params\":[],\"args\":[{\"kind\":\"var\",\"name\":4},{\"kind\":\"c\",\"value\":\"6\"}]}]}]},{\"kind\":\"app\",\"op\":\"shl\",\"params\":[],\"args\":[{\"kind\":\"app\",\"op\":\"low\",\"params\":[8],\"args\":[{\"kind\":\"app\",\"op\":\"inputByte\",\"params\":[0],\"args\":[{\"kind\":\"var\",\"name\":4},{\"kind\":\"app\",\"op\":\"add\",\"params\":[],\"args\":[{\"kind\":\"var\",\"name\":4},{\"kind\":\"c\",\"value\":\"7\"}]}]}]},{\"kind\":\"c\",\"value\":\"8\"}]}]}]},{\"kind\":\"app\",\"op\":\"extract\",\"params\":[8,8],\"args\":[{\"kind\":\"app\",\"op\":\"or\",\"params\":[],\"args\":[{\"kind\":\"app\",\"op\":\"low\",\"params\":[8],\"args\":[{\"kind\":\"app\",\"op\":\"inputByte\",\"params\":[0],\"args\":[{\"kind\":\"var\",\"name\":4},{\"kind\":\"app\",\"op\":\"add\",\"params\":[],\"args\":[{\"kind\":\"var\",\"name\":4},{\"kind\":\"c\",\"value\":\"6\"}]}]}]},{\"kind\":\"app\",\"op\":\"shl\",\"params\":[],\"args\":[{\"kind\":\"app\",\"op\":\"low\",\"params\":[8],\"args\":[{\"kind\":\"app\",\"op\":\"inputByte\",\"params\":[0],\"args\":[{\"kind\":\"var\",\"name\":4},{\"kind\":\"app\",\"op\":\"add\",\"params\":[],\"args\":[{\"kind\":\"var\",\"name\":4},{\"kind\":\"c\",\"value\":\"7\"}]}]}]},{\"kind\":\"c\",\"value\":\"8\"}]}]}]}]}}"
#guard liveNode46WriteBytesNormalize

-- A predicate's access width controls the byte count even without an env override.
private def predicateStoreWidthCheck : Bool :=
  let source := Term.C32 0x44332211
  let narrow := toCross {} (.packetWrite 0 0 0 16 source)
  let wide := toCross {} (.packetWrite 0 0 0 32 source)
  narrow == .packetWrite ⟨0, .c 0, .bytes [.c 0x11, .c 0x22]⟩ &&
    wide == .packetWrite ⟨0, .c 0, .bytes [.c 0x11, .c 0x22, .c 0x33, .c 0x44]⟩ &&
    narrow != wide &&
    toCross { storeBytes := some 8 } (.packetWrite 0 0 0 16 source) == narrow &&
    toCross { storeBytes := some 1 } (.mapWrite 0 (.C32 42) [] 0 32 source) ==
      .mapWrite ⟨.write, .c 42, [], 0, .bytes [.c 0x11, .c 0x22, .c 0x33, .c 0x44]⟩
#guard predicateStoreWidthCheck

#guard toCross {} (.packetWrite 0 0 0 16 (.C64 0x8877665544332211)) ==
  .packetWrite ⟨0, .c 0, .bytes [.c 0x11, .c 0x22]⟩
#guard (Predicate.ret (.C32 0)).storeBytes? == none

#guard exportCrossPredNormalize "{\"storeBigEndian\":true}"
    (renderPredicateJson (.packetWrite 0 0 0 16 (.C64 0x44332211))) ==
  exportCrossPredNormalize "{}"
    (renderPredicateJson (.packetWrite 0 0 0 16 (.C64 0x44332211)))

-- just_tx.c: ETH_P_8021Q=0x8100 and ETH_P_8021AD=0x88A8 occur in one ||.
-- Both trees read byte12 into bits 0..7 and byte13 into bits 8..15.
-- bpf_htons gives Q=129 and AD=43144. Compilers reverse the disjunct order;
-- the host pairs eq with eq (AD with Q). Merging these constants is unsound.
private def liveNode3EthertypeDistinct : Bool :=
  let r := exportCrossPredNormalize liveEnvRJson liveNode3EthertypeR
  let e := exportCrossPredNormalize liveEnvEJson liveNode3EthertypeE
  r != "null" && e != "null" && r != e &&
    r == "{\"kind\":\"branch\",\"dir\":\"taken\",\"cond\":{\"kind\":\"packetField\",\"field\":{\"kind\":\"app\",\"op\":\"or\",\"params\":[],\"args\":[{\"kind\":\"app\",\"op\":\"low\",\"params\":[8],\"args\":[{\"kind\":\"app\",\"op\":\"inputByte\",\"params\":[0],\"args\":[{\"kind\":\"var\",\"name\":4},{\"kind\":\"app\",\"op\":\"add\",\"params\":[],\"args\":[{\"kind\":\"var\",\"name\":4},{\"kind\":\"c\",\"value\":\"12\"}]}]}]},{\"kind\":\"app\",\"op\":\"shl\",\"params\":[],\"args\":[{\"kind\":\"app\",\"op\":\"low\",\"params\":[8],\"args\":[{\"kind\":\"app\",\"op\":\"inputByte\",\"params\":[0],\"args\":[{\"kind\":\"var\",\"name\":4},{\"kind\":\"app\",\"op\":\"add\",\"params\":[],\"args\":[{\"kind\":\"var\",\"name\":4},{\"kind\":\"c\",\"value\":\"13\"}]}]}]},{\"kind\":\"c\",\"value\":\"8\"}]}]},\"rel\":{\"kind\":\"eq\",\"q\":32},\"value\":\"43144\"}}" &&
    e == "{\"kind\":\"branch\",\"dir\":\"taken\",\"cond\":{\"kind\":\"packetField\",\"field\":{\"kind\":\"app\",\"op\":\"or\",\"params\":[],\"args\":[{\"kind\":\"app\",\"op\":\"low\",\"params\":[8],\"args\":[{\"kind\":\"app\",\"op\":\"inputByte\",\"params\":[0],\"args\":[{\"kind\":\"var\",\"name\":4},{\"kind\":\"app\",\"op\":\"add\",\"params\":[],\"args\":[{\"kind\":\"var\",\"name\":4},{\"kind\":\"c\",\"value\":\"12\"}]}]}]},{\"kind\":\"app\",\"op\":\"shl\",\"params\":[],\"args\":[{\"kind\":\"app\",\"op\":\"low\",\"params\":[8],\"args\":[{\"kind\":\"app\",\"op\":\"inputByte\",\"params\":[0],\"args\":[{\"kind\":\"var\",\"name\":4},{\"kind\":\"app\",\"op\":\"add\",\"params\":[],\"args\":[{\"kind\":\"var\",\"name\":4},{\"kind\":\"c\",\"value\":\"13\"}]}]}]},{\"kind\":\"c\",\"value\":\"8\"}]}]},\"rel\":{\"kind\":\"eq\",\"q\":32},\"value\":\"129\"}}"
#guard liveNode3EthertypeDistinct


namespace MapWriteCarryFixtures

-- Exact fresh node increments: lookup-null branch, low write, high write.
def envR : String :=
  "{\"packetBase\":\"v32:4\",\"packetEnd\":\"add32(v32:4,v32:5)\",\"maps\":[{\"map\":\"1077412584\",\"keyBytes\":4,\"valueBytes\":8}]}"

def envE : String :=
  "{\"packetBase\":\"v32:4\",\"packetEnd\":\"add32(v32:4,128)\",\"maps\":[{\"map\":\"1077412584\",\"keyBytes\":4,\"valueBytes\":8}]}"

def node26BranchR : String :=
  "{\"kind\":\"branch\",\"cond\":{\"lhs\":\"id32(externalResult747_0(1,1077412584,id32(add32(v32:0,4294967280))))\",\"rel\":\"ne\",\"rhs\":\"0\"},\"dir\":\"notTaken\",\"position\":48,\"width\":32}"
def node26LowR : String :=
  "{\"kind\":\"mapWrite\",\"event\":771,\"key\":[\"extract0,8(or32(0,shl32(zext8/32(low8(inputByte0(v32:4,add32(v32:4,24)))),0)))\",\"extract8,8(or32(0,shl32(zext8/32(low8(inputByte0(v32:4,add32(v32:4,24)))),0)))\",\"extract16,8(or32(0,shl32(zext8/32(low8(inputByte0(v32:4,add32(v32:4,24)))),0)))\",\"extract24,8(or32(0,shl32(zext8/32(low8(inputByte0(v32:4,add32(v32:4,24)))),0)))\"],\"map\":\"1077412584\",\"mapWidth\":32,\"offset\":0,\"source\":\"add32(regVar747(real32:10),1)\",\"sourceWidth\":32}"
def node26HighR : String :=
  "{\"kind\":\"mapWrite\",\"event\":773,\"key\":[\"extract0,8(or32(0,shl32(zext8/32(low8(inputByte0(v32:4,add32(v32:4,24)))),0)))\",\"extract8,8(or32(0,shl32(zext8/32(low8(inputByte0(v32:4,add32(v32:4,24)))),0)))\",\"extract16,8(or32(0,shl32(zext8/32(low8(inputByte0(v32:4,add32(v32:4,24)))),0)))\",\"extract24,8(or32(0,shl32(zext8/32(low8(inputByte0(v32:4,add32(v32:4,24)))),0)))\"],\"map\":\"1077412584\",\"mapWidth\":32,\"offset\":4,\"source\":\"add32(externalResult747_2(1),ltu32(add32(regVar747(real32:10),1),1))\",\"sourceWidth\":32}"
def node26PredsR : List String :=
  [node26BranchR, node26LowR, node26HighR]

def node26BranchE : String :=
  "{\"kind\":\"branch\",\"cond\":{\"lhs\":\"externalResult386_0(1,1077412584,id64(add64(id64(v64:0),18446744073709551612)))\",\"rel\":\"ne\",\"rhs\":\"0\"},\"dir\":\"notTaken\",\"position\":38,\"width\":64}"
def node26LowE : String :=
  "{\"kind\":\"mapWrite\",\"event\":418,\"key\":[\"extract0,8(zext32/32/64(or64(0,shl64(zext8/64/32(low8(inputByte0(v32:4,add32(v32:4,24)))),0))))\",\"extract8,8(zext32/32/64(or64(0,shl64(zext8/64/32(low8(inputByte0(v32:4,add32(v32:4,24)))),0))))\",\"extract16,8(zext32/32/64(or64(0,shl64(zext8/64/32(low8(inputByte0(v32:4,add32(v32:4,24)))),0))))\",\"extract24,8(zext32/32/64(or64(0,shl64(zext8/64/32(low8(inputByte0(v32:4,add32(v32:4,24)))),0))))\"],\"map\":\"1077412584\",\"mapWidth\":64,\"offset\":0,\"source\":\"extract0,32/64(id64(add64(regVar386(real64:0),1)))\",\"sourceWidth\":32}"
def node26HighE : String :=
  "{\"kind\":\"mapWrite\",\"event\":418,\"key\":[\"extract0,8(zext32/32/64(or64(0,shl64(zext8/64/32(low8(inputByte0(v32:4,add32(v32:4,24)))),0))))\",\"extract8,8(zext32/32/64(or64(0,shl64(zext8/64/32(low8(inputByte0(v32:4,add32(v32:4,24)))),0))))\",\"extract16,8(zext32/32/64(or64(0,shl64(zext8/64/32(low8(inputByte0(v32:4,add32(v32:4,24)))),0))))\",\"extract24,8(zext32/32/64(or64(0,shl64(zext8/64/32(low8(inputByte0(v32:4,add32(v32:4,24)))),0))))\"],\"map\":\"1077412584\",\"mapWidth\":64,\"offset\":4,\"source\":\"extract32,32/64(id64(add64(regVar386(real64:0),1)))\",\"sourceWidth\":32}"
def node26PredsE : List String :=
  [node26BranchE, node26LowE, node26HighE]

def node34BranchR : String :=
  "{\"kind\":\"branch\",\"cond\":{\"lhs\":\"id32(externalResult737_0(1,1077412584,id32(add32(v32:0,4294967280))))\",\"rel\":\"ne\",\"rhs\":\"0\"},\"dir\":\"notTaken\",\"position\":48,\"width\":32}"
def node34LowR : String :=
  "{\"kind\":\"mapWrite\",\"event\":766,\"key\":[\"extract0,8(or32(0,shl32(zext8/32(low8(inputByte0(v32:4,add32(v32:4,20)))),0)))\",\"extract8,8(or32(0,shl32(zext8/32(low8(inputByte0(v32:4,add32(v32:4,20)))),0)))\",\"extract16,8(or32(0,shl32(zext8/32(low8(inputByte0(v32:4,add32(v32:4,20)))),0)))\",\"extract24,8(or32(0,shl32(zext8/32(low8(inputByte0(v32:4,add32(v32:4,20)))),0)))\"],\"map\":\"1077412584\",\"mapWidth\":32,\"offset\":0,\"source\":\"add32(regVar737(real32:10),1)\",\"sourceWidth\":32}"
def node34HighR : String :=
  "{\"kind\":\"mapWrite\",\"event\":768,\"key\":[\"extract0,8(or32(0,shl32(zext8/32(low8(inputByte0(v32:4,add32(v32:4,20)))),0)))\",\"extract8,8(or32(0,shl32(zext8/32(low8(inputByte0(v32:4,add32(v32:4,20)))),0)))\",\"extract16,8(or32(0,shl32(zext8/32(low8(inputByte0(v32:4,add32(v32:4,20)))),0)))\",\"extract24,8(or32(0,shl32(zext8/32(low8(inputByte0(v32:4,add32(v32:4,20)))),0)))\"],\"map\":\"1077412584\",\"mapWidth\":32,\"offset\":4,\"source\":\"add32(externalResult737_2(1),ltu32(add32(regVar737(real32:10),1),1))\",\"sourceWidth\":32}"
def node34PredsR : List String :=
  [node34BranchR, node34LowR, node34HighR]

def node34BranchE : String :=
  "{\"kind\":\"branch\",\"cond\":{\"lhs\":\"externalResult336_0(1,1077412584,id64(add64(id64(v64:0),18446744073709551612)))\",\"rel\":\"ne\",\"rhs\":\"0\"},\"dir\":\"notTaken\",\"position\":38,\"width\":64}"
def node34LowE : String :=
  "{\"kind\":\"mapWrite\",\"event\":381,\"key\":[\"extract0,8(zext32/32/64(or64(0,shl64(zext8/64/32(low8(inputByte0(v32:4,add32(v32:4,20)))),0))))\",\"extract8,8(zext32/32/64(or64(0,shl64(zext8/64/32(low8(inputByte0(v32:4,add32(v32:4,20)))),0))))\",\"extract16,8(zext32/32/64(or64(0,shl64(zext8/64/32(low8(inputByte0(v32:4,add32(v32:4,20)))),0))))\",\"extract24,8(zext32/32/64(or64(0,shl64(zext8/64/32(low8(inputByte0(v32:4,add32(v32:4,20)))),0))))\"],\"map\":\"1077412584\",\"mapWidth\":64,\"offset\":0,\"source\":\"extract0,32/64(id64(add64(regVar336(real64:0),1)))\",\"sourceWidth\":32}"
def node34HighE : String :=
  "{\"kind\":\"mapWrite\",\"event\":381,\"key\":[\"extract0,8(zext32/32/64(or64(0,shl64(zext8/64/32(low8(inputByte0(v32:4,add32(v32:4,20)))),0))))\",\"extract8,8(zext32/32/64(or64(0,shl64(zext8/64/32(low8(inputByte0(v32:4,add32(v32:4,20)))),0))))\",\"extract16,8(zext32/32/64(or64(0,shl64(zext8/64/32(low8(inputByte0(v32:4,add32(v32:4,20)))),0))))\",\"extract24,8(zext32/32/64(or64(0,shl64(zext8/64/32(low8(inputByte0(v32:4,add32(v32:4,20)))),0))))\"],\"map\":\"1077412584\",\"mapWidth\":64,\"offset\":4,\"source\":\"extract32,32/64(id64(add64(regVar336(real64:0),1)))\",\"sourceWidth\":32}"
def node34PredsE : List String :=
  [node34BranchE, node34LowE, node34HighE]

private def liveNode26HighCanonical : Bool :=
  let r := exportCrossPredNormalize envR node26HighR
  r != "null" && r == "{\"kind\":\"mapWrite\",\"mutation\":{\"action\":\"write\",\"map\":{\"kind\":\"c\",\"value\":\"1077412584\"},\"key\":[{\"kind\":\"app\",\"op\":\"extract\",\"params\":[0,8],\"args\":[{\"kind\":\"app\",\"op\":\"low\",\"params\":[8],\"args\":[{\"kind\":\"app\",\"op\":\"inputByte\",\"params\":[0],\"args\":[{\"kind\":\"var\",\"name\":4},{\"kind\":\"app\",\"op\":\"add\",\"params\":[],\"args\":[{\"kind\":\"var\",\"name\":4},{\"kind\":\"c\",\"value\":\"24\"}]}]}]}]},{\"kind\":\"app\",\"op\":\"extract\",\"params\":[8,8],\"args\":[{\"kind\":\"app\",\"op\":\"low\",\"params\":[8],\"args\":[{\"kind\":\"app\",\"op\":\"inputByte\",\"params\":[0],\"args\":[{\"kind\":\"var\",\"name\":4},{\"kind\":\"app\",\"op\":\"add\",\"params\":[],\"args\":[{\"kind\":\"var\",\"name\":4},{\"kind\":\"c\",\"value\":\"24\"}]}]}]}]},{\"kind\":\"app\",\"op\":\"extract\",\"params\":[16,8],\"args\":[{\"kind\":\"app\",\"op\":\"low\",\"params\":[8],\"args\":[{\"kind\":\"app\",\"op\":\"inputByte\",\"params\":[0],\"args\":[{\"kind\":\"var\",\"name\":4},{\"kind\":\"app\",\"op\":\"add\",\"params\":[],\"args\":[{\"kind\":\"var\",\"name\":4},{\"kind\":\"c\",\"value\":\"24\"}]}]}]}]},{\"kind\":\"app\",\"op\":\"extract\",\"params\":[24,8],\"args\":[{\"kind\":\"app\",\"op\":\"low\",\"params\":[8],\"args\":[{\"kind\":\"app\",\"op\":\"inputByte\",\"params\":[0],\"args\":[{\"kind\":\"var\",\"name\":4},{\"kind\":\"app\",\"op\":\"add\",\"params\":[],\"args\":[{\"kind\":\"var\",\"name\":4},{\"kind\":\"c\",\"value\":\"24\"}]}]}]}]}],\"offset\":4,\"value\":{\"kind\":\"bytes\",\"values\":[{\"kind\":\"app\",\"op\":\"extract\",\"params\":[0,8],\"args\":[{\"kind\":\"app\",\"op\":\"extract\",\"params\":[32,32],\"args\":[{\"kind\":\"app\",\"op\":\"add\",\"params\":[],\"args\":[{\"kind\":\"reg\",\"class\":0,\"alpha\":10},{\"kind\":\"c\",\"value\":\"1\"}]}]}]},{\"kind\":\"app\",\"op\":\"extract\",\"params\":[8,8],\"args\":[{\"kind\":\"app\",\"op\":\"extract\",\"params\":[32,32],\"args\":[{\"kind\":\"app\",\"op\":\"add\",\"params\":[],\"args\":[{\"kind\":\"reg\",\"class\":0,\"alpha\":10},{\"kind\":\"c\",\"value\":\"1\"}]}]}]},{\"kind\":\"app\",\"op\":\"extract\",\"params\":[16,8],\"args\":[{\"kind\":\"app\",\"op\":\"extract\",\"params\":[32,32],\"args\":[{\"kind\":\"app\",\"op\":\"add\",\"params\":[],\"args\":[{\"kind\":\"reg\",\"class\":0,\"alpha\":10},{\"kind\":\"c\",\"value\":\"1\"}]}]}]},{\"kind\":\"app\",\"op\":\"extract\",\"params\":[24,8],\"args\":[{\"kind\":\"app\",\"op\":\"extract\",\"params\":[32,32],\"args\":[{\"kind\":\"app\",\"op\":\"add\",\"params\":[],\"args\":[{\"kind\":\"reg\",\"class\":0,\"alpha\":10},{\"kind\":\"c\",\"value\":\"1\"}]}]}]}]}}}"
#guard liveNode26HighCanonical

end MapWriteCarryFixtures

end ClassifierExpr
