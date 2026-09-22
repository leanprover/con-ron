/-!
# `ConRon.Arena.ExprOps` — the fixture's substitution walks

Six twins of the real module, at their real names: an arm-split walk whose
arms fold into it, the copy helper whose only bridge theorem carries an
unrecognised suffix, the pointer test with an `_exact`, the fast wrapper
that is closed on both sides, and a walk that is stated but not closed.
-/

namespace ConRon.Arena

/-- con-leche: none — arena infrastructure. -/
def eidxCopyUpto (xs : Array EIdx) (k i : Nat) (out : Array EIdx) : Array EIdx :=
  out

/-- The `bvar` arm, outside the mutual block because it does not recurse. -/
def instantiate1ArmBVar (v : EIdx) (h : EIdx) (d : Nat) : AM EIdx := do
  pure v

mutual

/-- The dispatcher: it is the one non-arm definition that names both arms,
which is how the census finds that they belong to it. -/
def instantiate1Go (v : EIdx) (fuel : Nat) (h : EIdx) (d : Nat) : AM EIdx :=
  if d == 0 then instantiate1ArmBVar v h d else instantiate1ArmApp v fuel h d

/-- The `app` arm. -/
def instantiate1ArmApp (v : EIdx) (fuel : Nat) (h : EIdx) (d : Nat) : AM EIdx :=
  instantiate1Go v fuel h d

end

/-- The `instantiateList` walk: stated, not closed. -/
def instantiateList (vs : Array EIdx) (fuel : Nat) (h : EIdx) (d : Nat) : AM EIdx :=
  pure h

/-- The pointer test. -/
def exprPtrBEq (a b : EIdx) : Bool := a == b

/-- The memoised entry point. -/
def wscopedBFast (fuel : Nat) (e : EIdx) : AM Bool := pure true

end ConRon.Arena
