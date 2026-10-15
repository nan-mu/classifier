import ClassifierExpr.Insn
import ClassifierExpr.Term
import ClassifierExpr.Op
import ClassifierExpr.Expr
import ClassifierExpr.Parse

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

/-- Lane zero is the ABI return value: keep helper id and resource, not frame pointers. -/
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
      | .inputByte _ => 8
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

/-- One non-constant base plus a sum of `.c` leaves. Two bases are not a value. -/
private inductive AffineAdd where
  | pure (k : Int)
  | base (t : CrossTerm) (k : Int)

private def combineAffine : AffineAdd → AffineAdd → Option AffineAdd
  | .pure x, .pure y => some (.pure (x + y))
  | .base t x, .pure y | .pure y, .base t x => some (.base t (x + y))
  | .base _ _, .base _ _ => none

/-- Same refusal as host `fold_add_const`: an `add` with two non-constant bases
does not fold, and a non-binary `add` does not fold. Sums are exact `Int` sums. -/
private def affineAdd : CrossTerm → Option AffineAdd
  | .c k => some (.pure k)
  | .app .add [a, b] =>
    match affineAdd a, affineAdd b with
    | some xa, some xb => combineAffine xa xb
    | _, _ => none
  | .app .add _ => none
  | t => some (.base t 0)

private def fromAffine : AffineAdd → CrossTerm
  | .pure k => .c k
  | .base t k => .app .add [t, .c k]

private def foldAddConst (x y : CrossTerm) : CrossTerm :=
  match affineAdd x, affineAdd y with
  | some xa, some ya =>
    match combineAffine xa ya with
    | some z => fromAffine z
    | none => .app .add [x, y]
  | _, _ => .app .add [x, y]

/-- R6 recognizes only the closed word-content carry idiom. Its interpretation
requires H and L to name word 1 and word 0 of the same Map element (CP-Bytes/Q);
this is a non-injective observation key, not an identity for arbitrary H.
The fallback folds a single base plus `.c` leaves after R1 ordering. -/
private def crossAdd (x y : CrossTerm) : CrossTerm :=
  match x, y with
  | .external lane [.c _], .app .ltu [.app .add [l, .c k], .c k'] =>
    if 1 ≤ lane && k == k' then .app (.extract 32 32) [.app .add [l, .c k]]
    else foldAddConst x y
  | _, _ => foldAddConst x y

private def crossBinary (op : Op) (x y : CrossTerm) : CrossTerm :=
  match op with
  | .add _ => if crossCompare x y == .gt then crossAdd x y else crossAdd y x
  | .or _ | .xor _ =>
    if x == .c 0 then y else if y == .c 0 then x else .app (crossOp op) [x,y]
  | .shl _ | .lshr _ | .ashr _ =>
    if y == .c 0 then x else .app (crossOp op) [x,y]
  | _ => .app (crossOp op) [x,y]

mutual
  def toCrossTerm : Term → CrossTerm
    | .const w c => .c (s w.bits c)
    | .var _ name => .var name
    | .regVar _ r => .reg r.kind (crossRegAlpha r)
    | .app _ (.externalResult _ lane) args => .external lane (crossTerms (abiPrefix lane args))
    | .app _ op [t] => crossUnary op (toCrossTerm t)
    | .app _ op [a,b] => crossBinary op (toCrossTerm a) (toCrossTerm b)
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

/-- Each side supplies its own entry XDP cells, Meta layouts, and (when available)
decoded current store width/endian. No Expr or SemState is retained. -/
structure CrossEnv where
  packetBase : Option Term := none
  packetEnd : Option Term := none
  maps : List CrossMapLayout := []
  storeBytes : Option Nat := none
  storeBigEndian : Bool := false
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

/-- Missing decoded store metadata remains explicit; a source is not fabricated bytes. -/
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
  offset : Nat
  value : CrossValue
  deriving DecidableEq, BEq, ReflBEq, LawfulBEq, Repr

inductive CrossPred where
  | helper (observation : CrossHelper)
  | branch (observation : CrossBranch)
  | ret (observation : CrossReturn)
  | mapWrite (observation : CrossMapWrite)
  | packetWrite (observation : CrossPacketWrite)
  deriving DecidableEq, BEq, ReflBEq, LawfulBEq, Repr

/-- Known little/big-endian store bytes, each evaluated from the frozen source.
Only constants fold; open sources retain their byte extraction structure. -/
private def storeValue (env : CrossEnv) (source : Term) : CrossValue :=
  match env.storeBytes with
  | none => .source (toCrossTerm source)
  | some n => .bytes ((List.range n).map fun j =>
      let k := if env.storeBigEndian then n - 1 - j else j
      toCrossTerm (star source.width (.extract (8*k) 8 source.width.bits) [source]))

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
def toCross (env : CrossEnv) : Predicate → CrossPred
  | .helper _ kind args => match toCrossHelper env kind args with
    | .mutation m => .mapWrite m
    | h => .helper h
  | .branch _ dir cond => .branch ⟨dir, toCrossCond env cond⟩
  | .ret term => .ret ⟨toCrossTerm term⟩
  | .mapWrite _ map key offset source =>
    .mapWrite ⟨.write, toCrossTerm map, crossTerms key, offset, storeValue env source⟩
  | .packetWrite _ packet offset source => .packetWrite ⟨packet, offset, storeValue env source⟩

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

private def crossOpParams : CrossOp → List Nat
  | .udiv bits z | .sdiv bits z => [bits, z]
  | .urem bits | .srem bits | .mulh bits | .mulhu bits
  | .mulhsu bits | .selectEq bits => [bits]
  | .low q | .inputByte q => [q]
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
  | .packetWrite p => s!"\{\"kind\":\"packetWrite\",\"packet\":{p.packet},\"offset\":{p.offset},\"value\":{renderCrossValueJson p.value}}"

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

theorem cross_term_add_comm (w₁ w₂ q₁ q₂ : Width) (a b : Term) :
    toCrossTerm (.app w₁ (.add q₁) [a,b]) =
      toCrossTerm (.app w₂ (.add q₂) [b,a]) := by
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

/-- R5 is structural; represented-value bounds are the generation-side CP-Q premise. -/
theorem cross_term_extract_represented (w : Width) (n v : Nat) (t : Term)
    (hwidth : (toCrossTerm t).compareBits = 32) (h : (toCrossTerm t).compareBits ≤ n) :
    toCrossTerm (.app w (.extract 0 n v) [t]) = toCrossTerm t := by
  have hn : 32 ≤ n := by simpa [hwidth] using h
  by_cases hv : n = v <;> simp [toCrossTerm, crossUnary, identityCast, hn, hv, hwidth]

/-- Structural recognition of R6. The same-element word-content and machine carry
premises needed for interpretation are owned by CP-Bytes/Q, not proved here. -/
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
  { maps := [⟨.c 42, 1, 4⟩], storeBytes := some 4 }
#guard toCross mutationEnv (.mapWrite 7 (.C32 42) [.C32 9] 0 (.C32 0x04030201)) ==
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
is optional; an absent field keeps its `CrossEnv` default. Terms are normalized by
`toCrossTerm`, so a map key is compared as a static resource binding. -/
def parseCrossEnvJson (value : Lean.Json) : Option CrossEnv := do
  if !envFields value crossEnvKeys [] then none
  let packetBase ← optTerm value "packetBase"
  let packetEnd ← optTerm value "packetEnd"
  let maps ← match value.getObjVal? "maps" with
    | .error _ => some []
    | .ok field => (← field.getArr?.toOption).toList.mapM parseCrossMapLayout
  let storeBytes ← optNat value "storeBytes"
  let storeBigEndian ← optBool value "storeBigEndian"
  pure { packetBase, packetEnd, maps, storeBytes, storeBigEndian := storeBigEndian.getD false }

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
  "{\"maps\":[{\"map\":\"42\",\"keyBytes\":1,\"valueBytes\":4}],\"storeBytes\":4}"
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

-- Live 2026-10-14 20:20 pairs: loc is the host atom location, not position.
-- Branch directions below are forced from the compare-tree edge, as on the host.
private def liveEnvRJson : String :=
  "{\"packetBase\":\"v32:4\",\"packetEnd\":\"add32(v32:4,v32:5)\",\"maps\":[{\"map\":\"1077412584\",\"keyBytes\":4,\"valueBytes\":8}]}"
private def liveEnvEJson : String :=
  "{\"packetBase\":\"v32:4\",\"packetEnd\":\"add32(v32:4,128)\",\"maps\":[{\"map\":\"1077412584\",\"keyBytes\":4,\"valueBytes\":8}]}"
private def liveStoreEnvRJson : String :=
  "{\"packetBase\":\"v32:4\",\"packetEnd\":\"add32(v32:4,v32:5)\",\"maps\":[{\"map\":\"1077412584\",\"keyBytes\":4,\"valueBytes\":8}],\"storeBytes\":2}"
private def liveStoreEnvEJson : String :=
  "{\"packetBase\":\"v32:4\",\"packetEnd\":\"add32(v32:4,128)\",\"maps\":[{\"map\":\"1077412584\",\"keyBytes\":4,\"valueBytes\":8}],\"storeBytes\":2}"
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
  "{\"kind\":\"packetWrite\",\"event\":849,\"offset\":0,\"packet\":0,\"source\":\"sext16/32(or32(or32(0,shl32(zext8/32(low8(inputByte0(v32:4,add32(v32:4,6)))),0)),shl32(zext8/32(low8(inputByte0(v32:4,add32(v32:4,7)))),8)))\",\"width\":32}"
private def liveNode46WriteE : String :=
  "{\"kind\":\"packetWrite\",\"event\":495,\"offset\":0,\"packet\":0,\"source\":\"or64(or64(0,shl64(zext8/64/32(low8(inputByte0(v32:4,add32(v32:4,6)))),0)),shl64(zext8/64/32(low8(inputByte0(v32:4,add32(v32:4,7)))),8))\",\"width\":64}"
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
#guard toCrossTerm (.app .w32 (.add .w32) [.app .w32 (.add .w32) [.V32 4, .C32 18], .C32 20]) ==
  .app .add [.var 4, .c 38]
#guard toCrossTerm (.app .w32 (.add .w32) [.app .w32 (.add .w32) [.C32 18, .V32 4], .C32 20]) ==
  .app .add [.var 4, .c 38]
#guard toCrossTerm (.app .w32 (.add .w32) [.app .w32 (.add .w32) [.V32 4, .V32 5], .C32 10]) ==
  .app .add [.app .add [.var 5, .var 4], .c 10]
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
  let r := exportCrossPredNormalize liveStoreEnvRJson liveNode46WriteR
  let e := exportCrossPredNormalize liveStoreEnvEJson liveNode46WriteE
  r != "null" && e != "null" && r == e &&
    r == "{\"kind\":\"packetWrite\",\"packet\":0,\"offset\":0,\"value\":{\"kind\":\"bytes\",\"values\":[{\"kind\":\"app\",\"op\":\"extract\",\"params\":[0,8],\"args\":[{\"kind\":\"app\",\"op\":\"or\",\"params\":[],\"args\":[{\"kind\":\"app\",\"op\":\"low\",\"params\":[8],\"args\":[{\"kind\":\"app\",\"op\":\"inputByte\",\"params\":[0],\"args\":[{\"kind\":\"var\",\"name\":4},{\"kind\":\"app\",\"op\":\"add\",\"params\":[],\"args\":[{\"kind\":\"var\",\"name\":4},{\"kind\":\"c\",\"value\":\"6\"}]}]}]},{\"kind\":\"app\",\"op\":\"shl\",\"params\":[],\"args\":[{\"kind\":\"app\",\"op\":\"low\",\"params\":[8],\"args\":[{\"kind\":\"app\",\"op\":\"inputByte\",\"params\":[0],\"args\":[{\"kind\":\"var\",\"name\":4},{\"kind\":\"app\",\"op\":\"add\",\"params\":[],\"args\":[{\"kind\":\"var\",\"name\":4},{\"kind\":\"c\",\"value\":\"7\"}]}]}]},{\"kind\":\"c\",\"value\":\"8\"}]}]}]},{\"kind\":\"app\",\"op\":\"extract\",\"params\":[8,8],\"args\":[{\"kind\":\"app\",\"op\":\"or\",\"params\":[],\"args\":[{\"kind\":\"app\",\"op\":\"low\",\"params\":[8],\"args\":[{\"kind\":\"app\",\"op\":\"inputByte\",\"params\":[0],\"args\":[{\"kind\":\"var\",\"name\":4},{\"kind\":\"app\",\"op\":\"add\",\"params\":[],\"args\":[{\"kind\":\"var\",\"name\":4},{\"kind\":\"c\",\"value\":\"6\"}]}]}]},{\"kind\":\"app\",\"op\":\"shl\",\"params\":[],\"args\":[{\"kind\":\"app\",\"op\":\"low\",\"params\":[8],\"args\":[{\"kind\":\"app\",\"op\":\"inputByte\",\"params\":[0],\"args\":[{\"kind\":\"var\",\"name\":4},{\"kind\":\"app\",\"op\":\"add\",\"params\":[],\"args\":[{\"kind\":\"var\",\"name\":4},{\"kind\":\"c\",\"value\":\"7\"}]}]}]},{\"kind\":\"c\",\"value\":\"8\"}]}]}]}]}}"
#guard liveNode46WriteBytesNormalize

-- Current host envs omit storeBytes: source sext16/32 must remain different.
private def liveNode46WriteNeedsStoreBytes : Bool :=
  let r := exportCrossPredNormalize liveEnvRJson liveNode46WriteR
  let e := exportCrossPredNormalize liveEnvEJson liveNode46WriteE
  r != "null" && e != "null" && r != e
#guard liveNode46WriteNeedsStoreBytes

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
  "{\"packetBase\":\"v32:4\",\"packetEnd\":\"add32(v32:4,v32:5)\",\"maps\":[{\"map\":\"1077412584\",\"keyBytes\":4,\"valueBytes\":8}],\"storeBytes\":4}"

def envE : String :=
  "{\"packetBase\":\"v32:4\",\"packetEnd\":\"add32(v32:4,128)\",\"maps\":[{\"map\":\"1077412584\",\"keyBytes\":4,\"valueBytes\":8}],\"storeBytes\":4}"

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
