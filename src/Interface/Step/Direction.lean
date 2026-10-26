namespace Interface.Step

/-! ## Successor direction (`doc/NodeInference/路径.md`) -/

inductive Direction where
  | ok
  | taken
  | notTaken
  deriving DecidableEq, BEq, Repr, Inhabited

end Interface.Step
