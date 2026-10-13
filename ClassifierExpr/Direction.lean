namespace ClassifierExpr

/-! ## Successor direction (`doc/NodeInference/路径.md`) -/

inductive Direction where
  | ok
  | taken
  | notTaken
  deriving DecidableEq, BEq, Repr, Inhabited

/-- Continuous node references within one run. -/
abbrev NodeId := Nat

end ClassifierExpr
