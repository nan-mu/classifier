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
  | .packetWrite p => .packetWrite { p with value := applyValue σ p.value }

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
  | .packetWrite a, .packetWrite b =>
    if a.packet == b.packet && a.offset == b.offset then mergeValue σ a.value b.value
    else none
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

/-! These propositions are recorded proof obligations, not axioms or theorems.
In particular, malformed input substitutions invalidate unconditional
injectivity preservation and unconditional identity stripping. -/
namespace ProofObligations

def mergeTerm_sound : Prop :=
  ∀ σ σ' a b, Injective σ → mergeTerm σ a b = some σ' →
    Extends σ σ' ∧ Injective σ' ∧ applyTerm σ' a = b

def mergeTerm_determined : Prop :=
  ∀ σ σ' a b, Injective σ → mergeTerm σ a b = some σ' → Determined σ' a

/-- The already-determined pair cannot be changed by later consistent merges. -/
def mergeTerm_already_determined : Prop :=
  ∀ σ σ' σ'' a b, Injective σ → mergeTerm σ a b = some σ' →
    Extends σ' σ'' → Injective σ'' → applyTerm σ'' a = b

def mergePred_sound : Prop :=
  ∀ σ σ' a b, Injective σ → mergePred σ a b = some σ' →
    Extends σ σ' ∧ Injective σ' ∧ rename σ' a = b

def strip_rename : Prop :=
  ∀ σ p, Injective σ → rename σ.strip p = rename σ p

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

def unify_pairs_sound : Prop :=
  ∀ L R i j, (i, j) ∈ (unifyLists L R).pairs →
    ∃ a b, L[i]? = some a ∧ R[j]? = some b ∧
      CrossSubst.rename (unifyLists L R).subst a = b

def unify_subst_injective : Prop :=
  ∀ L R, CrossSubst.Injective (unifyLists L R).subst

end ObservationEqProofObligations

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
  | "neg", [] => some .neg | "id", [] => some .id | "shl", [] => some .shl
  | "lshr", [] => some .lshr | "ashr", [] => some .ashr
  | "ltu", [] => some .ltu | "lts", [] => some .lts
  | "and", [q] => some (.and q) | "or", [q] => some (.or q)
  | "xor", [q] => some (.xor q) | "low", [q] => some (.low q)
  | "extract", [a,b] => some (.extract a b) | "zext", [a,b] => some (.zext a b)
  | "sext", [a,b] => some (.sext a b) | "bswap", [a,b] => some (.bswap a b)
  | "inputByte", [r] => some (.inputByte r) | "mergeLow", [a,b] => some (.mergeLow a b)
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
    if !exactFields j ["kind", "packet", "offset", "value"] then none
    pure (.packetWrite ⟨← natField j "packet", ← natField j "offset",
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
   .and 32, .or 64, .xor 8, .low 16, .extract 8 16, .zext 64 32,
   .sext 64 32, .bswap 32 32, .inputByte 3, .mergeLow 32 8]
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

end ClassifierExpr
