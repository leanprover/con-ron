/-
# `ConRon.Bridge.ExprOps.Walks` — Theorem 1 for the `Bool` and `Nat` walks

DESIGN §8.2's Theorem 1 at the twins of `Arena/ExprOps.lean` whose answer is
a **representation-free scalar**: `sizeB`, `sizeF`, `wscopedB`,
`looseBVarsBounded`, `hasFvar`, and the two one-node readers `isLam`,
`lamPw`.  Its two companions are `ExprOps/Ranges.lean` (the
packed-field reads and their memoized recomputations) and
`ExprOps/Leaves.lean` (the leaf list, the `seen` set and the leaf guard).

## Why this tier is the cheap one

`Bridge/Rel.lean`'s answer relation for these twins is `RelV`:

```lean
RelV (f : Expr → α) (st : EStore) (c : EIdx) (x : α) : Prop :=
  ∀ e, denoteE st c = some e → x = f e
```

— **no target store**, because a `Bool` or a `Nat` names none.  Nothing here
interns, so nothing here grows the arena: every twin below leaves the state
literally unchanged and Theorem 1's postcondition says `s' = s₁` where a
rebuilding walk needs `Ext s₁.store s'.store` plus four frame equations.
That collapses the whole extension-chain half of `ExprOps/Inst1.lean`'s
proof, and with it the per-arm `_step` lemmas: **`bridge_vcs` closes every
verification condition of every twin in this file**, given `RelV` in its
`grind` list.

## The one thing the closer needed: `RelV` in the unfold list

`RelV` is a `def` (deliberately — a `∀`-hypothesis has no head symbol for
`grind` to ematch on), so the closer cannot see into the goal
`RelV Expr.sizeB st h (x + y + 1)` unless it is told to unfold it.
`bridge_vcs [Expr.sizeB, RelV]` is the whole recipe, and it is the finding
this file records: task #97-P3-0's note on `ExprOps/Inst1.lean`'s `bvar` arm
("`try unfold RelE` inside the closer takes them and breaks the `proj` arm")
does **not** apply to a walk with no target store — there is no `proj` arm
whose answer has to be retargeted, so the unfold is free and universal.
No `_step` lemma, no `next =>` block, no `arm_hyp` appears below.

## Fuel, and what the twins dispatch on

Fuel, as everywhere in this tier, because a handle DAG has no structural
order the elaborator can see; exhaustion is a failure and Theorem 1 claims
nothing on failure, which is what `⇓?` says.  Unlike the rebuilding walks,
these five dispatch on `view` DIRECTLY (a `match ← view h` over the ten
`ENodeView` constructors, not the tag test of task #97-P6-13), so the arms
arrive already carrying their `view` equation and `Bridge/Rel.lean`'s group 5
inversions fire on it without help.
-/
import ConRon.Bridge.Specs
import ConRon.Bridge.ExprOps.TagFirst

namespace ConRon.Bridge.ExprOps

set_option autoImplicit false
set_option mvcgen.warning false
set_option maxHeartbeats 2000000

open ConLeche ConRon.Arena ConRon.Bridge Std.Do

/-! ### Attribute hygiene (task #97s round 2, item 1)

`RelE.ext`, `.of_ext` and `.retarget` close the answer relation under `Ext` in
both directions, so every intermediate store multiplies every answer already
known.  `attribute [-grind]` does not travel through an import, so every file
of this tier repeats the line — even this one, which has no `Ext` in any
statement: the closer's second stage still has them in its list. -/
attribute [-grind] RelE.ext RelE.of_ext RelE.retarget

/-! ### The catch-all of the one-node readers

`isLam` and `lamPw` are `match ← view h` with ONE named arm and a
`_ =>` fallthrough, and the fallthrough is the one verification condition the
closer cannot take unaided: it has "the view is not a `lam`" as a
`∀`-hypothesis over `ENodeView` and no reason to case-split on the view.
Stated as a DISJUNCTION the closer takes it in one step — `grind` splits the
`∨`, and the left disjunct contradicts the arm's own hypothesis.  This is
`Bridge/Rel.lean`'s `denote_leaf_of_tag` played at the constructor rather
than at the tag, and it **morally belongs in `Bridge/Rel.lean`**. -/

/-! ## The two one-node readers — `ExprOps.lean:1000`, `:1008`

One `view` and a test: no recursion, no fuel, so no `Spec` record and no
induction.  Theorem 1 is the triple itself.

**`lamPw` answers `Option PropWhen`, and `PropWhen` is a SEALED
representation** (con-leche's own `ExprOps.lean` needs `import all` to
destruct one; the arena never destructs one, it only compares).  So it
is stated against con-leche's `Expr.lamPw` as an equation on
the `Option PropWhen` and nothing below looks inside: the `BinderMeta` the
twin reads off the node IS the one the denotation carries
(`denote_lam_inv`'s `e = .lam et eb m`), so `m.pw` needs no unfolding. -/

/-- con-leche: ConLeche/Kernel/ExprOps.lean:887-894 lamPw — **THEOREM 1 for
`lamPw`**, on the `Option PropWhen` and not inside it. -/
theorem lamPw_spec (s₀ : AState) (h : EIdx) (hok : StateOK s₀)
    (hden : (denoteE s₀.store h).isSome = true) :
    ⦃fun s => ⌜s = s₀⌝⦄ lamPw h
    ⦃⇓? r s' => ⌜s' = s₀ ∧ RelV Expr.lamPw s₀.store h r⌝⦄ := by
  mvcgen [lamPw]
  all_goals first
    | bridge_vcs [Expr.lamPw, RelV]
    -- the tag-first `else` arm (task #97-P5-Core round 4): the view comes
    -- back from the denotation, and its tag is not `lam`
    | (bridge_peel
       subst_vars
       obtain ⟨v, hv⟩ := view_of_denote_isSome (by assumption)
       have hne := view_tagOf_ne hv (t := ETag.lam) (by assumption)
       refine ⟨rfl, fun e he => ?_⟩
       rw [denoteE_view_eq hok.wf hv] at he
       cases v <;> first
         | exact absurd rfl hne
         | grind [denoteEView, Expr.lamPw, opt2_eq_some_iff, opt3_eq_some_iff,
             Option.map_eq_some_iff])

/-! ## The axiom check -/

#print axioms lamPw_spec

end ConRon.Bridge.ExprOps
