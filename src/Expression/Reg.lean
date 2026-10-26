import Term.Value.Bits

namespace Expression
open Term.Value

/-- Field named by `Context`. The register itself stores only this name and a bit interval. -/
inductive ContextField where
  | data
  | dataEnd
  | dataMeta
  | ingressIfindex
  | rxQueueIndex
  | egressIfindex
  | ctx
  | sp
  | packetBytes
  | imageBase
  | helper
  | wrapperReturn
  | lddw (slot : Nat)
  | mapKeyBytes (mapId : Nat)
  | mapValueBytes (mapId : Nat)
  deriving DecidableEq, BEq, Repr, Inhabited

theorem Nat.beq_comm (n m : Nat) : (n == m) = (m == n) := by
  by_cases h : n = m
  · subst m; rfl
  · rw [beq_eq_false_iff_ne.mpr h, beq_eq_false_iff_ne.mpr (Ne.symm h)]

theorem ContextField.beq_comm (a b : ContextField) : (a == b) = (b == a) := by
  cases a <;> cases b
  case lddw.lddw n m =>
    exact Nat.beq_comm n m
  case mapKeyBytes.mapKeyBytes n m =>
    exact Nat.beq_comm n m
  case mapValueBytes.mapValueBytes n m =>
    exact Nat.beq_comm n m
  all_goals rfl

/-- Upper bound of a field interval. Not stored on the register. -/
def ContextField.cap : ContextField → Nat
  | .ctx | .sp | .lddw _ => 64
  | _ => 32

/-- Carrier used by the existing 32/64 numeric operators. The register interval is the semantic width. -/
def Width.ofBits (n : Nat) : Width :=
  if n ≤ 32 then .w32 else .w64

end Expression
