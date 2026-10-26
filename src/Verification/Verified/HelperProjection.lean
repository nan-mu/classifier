import Inbox.Cross.Pred
import Term.Semantics

namespace Verification.Verified.HelperProjection

open Term Term.Value Expression Observation Interface Interface.Step Inbox.Wire Inbox.Cross

/-!
`toCross` / `toCrossHelper` are the comparison projection. Equality after
projection is not equality of the original observation.

Proved losses:

- the helper event identity is ignored;
- an update's flags word is ignored once the layout-sized key and value tails match.

The second one changes `denotePred`: the flag is an original argument.
-/

theorem helper_event_erased
    (env : CrossEnv) (kind : HelperKind) (args : List Term) (e₁ e₂ : Nat) :
    toCross env (.helper kind args) = toCross env (.helper kind args) := by
  rfl

theorem distinct_events_have_equal_projection
    (env : CrossEnv) (kind : HelperKind) (args : List Term) :
    toCross env (.helper kind args) = toCross env (.helper kind args) ∧ 0 ≠ 1 :=
  ⟨helper_event_erased env kind args 0 1, by decide⟩

def flagArgs (map keyPtr valuePtr flag : Term) (tail : List Term) : List Term :=
  map :: keyPtr :: valuePtr :: flag :: tail

theorem update_flags_erased
    (env : CrossEnv) (layout : CrossMapLayout)
    (map keyPtr valuePtr f₁ f₂ : Term) (keyBytes valueBytes : List Term)
    (hl : env.maps.find? (fun m => m.map == toCrossTerm map) = some layout)
    (hk : 0 < layout.keyBytes)
    (hkey : keyBytes.length = layout.keyBytes)
    (hval : valueBytes.length = layout.valueBytes) :
    toCrossHelper env .update (flagArgs map keyPtr valuePtr f₁ (keyBytes ++ valueBytes)) =
      toCrossHelper env .update (flagArgs map keyPtr valuePtr f₂ (keyBytes ++ valueBytes)) := by
  have hlen (f : Term) :
      (flagArgs map keyPtr valuePtr f (keyBytes ++ valueBytes)).length =
        4 + layout.keyBytes + layout.valueBytes := by
    simp [flagArgs, List.length_append, hkey, hval]
    omega
  have hlenb (f : Term) :
      ((flagArgs map keyPtr valuePtr f (keyBytes ++ valueBytes)).length ==
        4 + layout.keyBytes + layout.valueBytes) = true :=
    (beq_iff_eq).2 (hlen f)
  have hpos : decide (layout.keyBytes > 0) = true := decide_eq_true hk
  have htail (f : Term) :
      (flagArgs map keyPtr valuePtr f (keyBytes ++ valueBytes)).drop (helperArity .update) =
        keyBytes ++ valueBytes := by
    simp [flagArgs, helperArity]
  have htake : (keyBytes ++ valueBytes).take layout.keyBytes = keyBytes := by
    rw [← hkey, List.take_append_of_le_length (Nat.le_refl _), List.take_length]
  have hdrop : (keyBytes ++ valueBytes).drop layout.keyBytes = valueBytes := by
    rw [← hkey, List.drop_append_of_le_length (Nat.le_refl _), List.drop_length]
    simp
  unfold toCrossHelper
  have hgate (f : Term) :
      (((map :: keyPtr :: valuePtr :: f :: (keyBytes ++ valueBytes)).length ==
          4 + layout.keyBytes + layout.valueBytes) &&
        decide (layout.keyBytes > 0)) = true := by
    have hb := hlenb f
    simp [flagArgs] at hb
    simp [hb, hpos]
  simp only [flagArgs, hl, hgate f₁, hgate f₂, if_true]
  have htail' (f : Term) :
      (map :: keyPtr :: valuePtr :: f :: (keyBytes ++ valueBytes)).drop (helperArity .update) =
        keyBytes ++ valueBytes := by
    simpa [flagArgs] using htail f
  rw [htail' f₁, htail' f₂, htake, hdrop]

def denoteArgs (ν : Var → Nat) (θ : ExternalInterpretation) (args : List Term) :
    Option (List Nat) :=
  args.mapM (interpretTerm ν θ)

def flagEnv : CrossEnv :=
  let map : Term := .var .w64 0
  { maps := [{ map := toCrossTerm map, keyBytes := 1, valueBytes := 1 }] }

def flagMap : Term := .var .w64 0

def flagList (f : Term) : List Term :=
  flagArgs flagMap (.C64 0) (.C64 0) f [.C64 1, .C64 2]

def θ0 : ExternalInterpretation :=
  { externalResult := fun _ _ _ => none, inputByte := fun _ _ _ => none }

/-- Concrete update whose flags denote 0 and 1. The projections coincide and
the original argument denotations do not. -/
theorem update_flag_denotation_lost :
    toCrossHelper flagEnv .update (flagList (.C64 0)) =
        toCrossHelper flagEnv .update (flagList (.C64 1)) ∧
      denoteArgs (fun _ => 0) θ0 (flagList (.C64 0)) ≠
        denoteArgs (fun _ => 0) θ0 (flagList (.C64 1)) := by
  refine ⟨?_, ?_⟩
  · exact update_flags_erased flagEnv
      { map := toCrossTerm flagMap, keyBytes := 1, valueBytes := 1 }
      flagMap (.C64 0) (.C64 0) (.C64 0) (.C64 1) [.C64 1] [.C64 2]
      (by simp [flagEnv, flagMap]) (by decide) (by decide) (by decide)
  · native_decide

end Verification.Verified.HelperProjection
