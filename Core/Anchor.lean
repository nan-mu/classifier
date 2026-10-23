import Core.Interval
import Core.MapLayout

namespace Core

/-- Create-time values are context equalities. A missing equality is unbound.
Zero is a real bound value when create chooses to write it. The host's unbound
signal stays outside the expression. -/
def bindField (E : List Expr) (j : ContextField) (t : Term) : Option (List Expr) :=
  putContext E j t

def fieldNat (E : List Expr) (j : ContextField) : Option Nat :=
  contextNat E j

namespace Anchor

/-- Key and value sizes live on `mapKeyBytes` / `mapValueBytes`. A zero key size
or a repeated id is not a layout. -/
def installMaps (E : List Expr) (maps : List MapLayout) : Option (List Expr) := do
  let mut out := E
  let mut seen : List Nat := []
  for m in maps do
    if seen.contains m.mapId || m.keySize == 0 || m.keySize ≥ 2 ^ 32 ||
        m.valueSize ≥ 2 ^ 32 then
      failure
    seen := m.mapId :: seen
    out ← bindField out (.mapKeyBytes m.mapId) (Term.C32 m.keySize)
    out ← bindField out (.mapValueBytes m.mapId) (Term.C32 m.valueSize)
  pure out

def layout? (E : List Expr) (map : Term) : Option MapLayout := do
  let id ← eval (solve map)
  let keySize ← fieldNat E (.mapKeyBytes id)
  let valueSize ← fieldNat E (.mapValueBytes id)
  if keySize == 0 then failure
  pure ⟨id, keySize, valueSize⟩

/-- A nonzero host immediate becomes `Context(lddw slot)`. Zero is not written:
absence of that equality is unbound. -/
def bindLddw (E : List Expr) (slot value : Nat) : Option (List Expr) :=
  if value == 0 then some E else bindField E (.lddw slot) (Term.C64 value)

end Anchor

inductive LddwBind where
  | unbound
  | bound (t : Term)
  deriving Repr, BEq

def lddwBind (E : List Expr) (slot : Nat) : LddwBind :=
  match contextValue E (.lddw slot) with
  | some t => .bound t
  | none => .unbound

end Core
