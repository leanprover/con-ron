/-
# `arena_peel` — twenty lines of meta code instead of a Mathlib dependency

`mvcgen` threads its plumbing through the postconditions of the `@[spec]`
theorems, so every verification condition arrives with a stack of hypotheses
of the form `s' = s ∧ <what the step did>`.  Splitting those and substituting
the state equalities is what lets `grind` see one state where the goal shows
seven, and it is the difference between "`grind` closes every verification
condition" and "`grind` closes most of them".

Mathlib spells this `casesm* _ ∧ _`; the arena libraries do not depend on
Mathlib (task #97a: it multiplies this library's build time by two orders of
magnitude), and the obvious substitute

```lean
repeat (obtain ⟨rfl, _⟩ := ‹(_ : AState) = _ ∧ _›)
```

is a **trap** the P2s spike measured: the `‹_›` anonymous-hypothesis notation
elaborates to `assumption` with metavariables in the type, and on a goal
where no such hypothesis is left that search `whnf`s the whole verification
condition — six minutes and a heartbeat timeout, per goal.  So the peel looks
at the local context instead of searching it.

This is the spike's `Spike/Peel.lean` moved into the checker's own library
(the spike stays throw-away and unimported); the code is unchanged but for
the tactic's name.
-/
import Lean
import ConRon.Arena.ExprOps

namespace ConRon.Arena

open Lean Elab Tactic Meta

/-- con-leche: none — destruct every conjunctive hypothesis, repeatedly.
Mathlib's `casesm* _ ∧ _`, without Mathlib. -/
elab "arena_peel" : tactic => do
  liftMetaTactic fun g => do
    let mut goal := g
    let mut progress := true
    while progress do
      progress := false
      let lctx ← goal.withContext getLCtx
      for d in lctx do
        if d.isImplementationDetail then continue
        let t ← goal.withContext (instantiateMVars d.type)
        if t.isAppOfArity ``And 2 then
          let subs ← goal.cases d.fvarId
          match subs[0]? with
          | some s0 =>
            if subs.size == 1 then
              goal := s0.mvarId
              progress := true
              break
          | none => pure ()
    return [goal]

end ConRon.Arena
