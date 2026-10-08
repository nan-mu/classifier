namespace CommonMath

/-! ## Successor direction (`doc/common-math.md` §13.3) -/

inductive Direction where
  | only
  | taken
  | notTaken
  deriving DecidableEq, BEq, Repr, Inhabited

/-- Continuous node references within one run. -/
abbrev NodeId := Nat

end CommonMath
