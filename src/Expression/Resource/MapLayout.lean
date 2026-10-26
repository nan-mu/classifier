namespace Expression

/-- Static Map object layout, keyed by its concrete parameter id. -/
structure MapLayout where
  mapId : Nat
  keySize : Nat
  valueSize : Nat
  deriving Repr, Inhabited, BEq

end Expression
