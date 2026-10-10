namespace CommonMath

/-! ## Successor direction (`doc/NodeInference/展开图与执行路径.md`) -/

inductive Direction where
  | only
  | taken
  | notTaken
  deriving DecidableEq, BEq, Repr, Inhabited

/-- Continuous node references within one run. -/
abbrev NodeId := Nat

end CommonMath
