import ClassifierExpr.Term
import Lean

namespace ClassifierExpr

/-- Static Map object layout, keyed by its concrete parameter id. -/
structure MapLayout where
  mapId : Nat
  keySize : Nat
  valueSize : Nat
  deriving Repr, Inhabited, BEq

def parseMapLayout (value : Lean.Json) : Option MapLayout := do
  let mapId ← (value.getObjVal? "mapId" >>= Lean.Json.getNat?).toOption
  let keySize ← (value.getObjVal? "keySize" >>= Lean.Json.getNat?).toOption
  let valueSize ← (value.getObjVal? "valueSize" >>= Lean.Json.getNat?).toOption
  if keySize > 64 || valueSize == 0 || valueSize > 4096 then none
  else some { mapId, keySize, valueSize }

def findMapLayout (maps : List MapLayout) (mapTerm : Term) : Option MapLayout :=
  match eval (solve mapTerm) with
  | some id => maps.find? (fun m => m.mapId == id)
  | none => none

end ClassifierExpr
