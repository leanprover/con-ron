/-!
Theorem 1 for `instantiate1Go`: the dispatcher's `_spec` and one ARM's own
`_spec`, both closed.  The arm theorem is what makes the "an arm's theorems
count toward its dispatcher" rule observable.
-/

namespace ConRon.Bridge

theorem instantiate1ArmApp_spec (v : EIdx) (ve : Expr) (fuel : Nat) :
    True := by
  trivial

theorem instantiate1Go_spec (v : EIdx) (ve : Expr) :
    True := by
  trivial

/-- The `instantiateList` walk is stated and NOT closed: the word `sorry`
below is the proof, and the one in this sentence is inside a comment and
must not count. -/
theorem instantiateList_spec (vs : Array EIdx) :
    True := by
  sorry

theorem wscopedBFast_spec (fuel : Nat) : True := by trivial

end ConRon.Bridge
