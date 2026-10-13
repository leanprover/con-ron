/-
# `ConRon.Bridge.ExprOps.Walks` — Theorem 1 for the `Bool` and `Nat` walks

DESIGN §8.2's Theorem 1 at the twins of `Arena/ExprOps.lean` whose answer is
a **representation-free scalar**: `sizeB`, `sizeF`, `wscopedB`,
`looseBVarsBounded`, `hasFvar`, and the two one-node readers `isForallE`,
`lamPair?`.  Its two companions are `ExprOps/Ranges.lean` (the
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
nothing on failure, which is what the `⊤` exception postcondition says.  Unlike the rebuilding walks,
these five dispatch on `view` DIRECTLY (a `match ← view h` over the ten
`ENodeView` constructors, not the tag test of task #97-P6-13), so the arms
arrive already carrying their `view` equation and `Bridge/Rel.lean`'s group 5
inversions fire on it without help.
-/
import ConRon.Bridge.Frame
import ConRon.Bridge.Specs
import ConRon.Bridge.ExprOps.TagFirst

namespace ConRon.Bridge.ExprOps

set_option autoImplicit false
set_option experimental.vcgen true
set_option maxHeartbeats 2000000

open ConLeche ConRon.Arena ConRon.Bridge Std.WP
open scoped Lean.Order

/-! ### Attribute hygiene (task #97s round 2, item 1)

`RelE.ext`, `.of_ext` and `.retarget` close the answer relation under `Ext` in
both directions, so every intermediate store multiplies every answer already
known.  `attribute [-grind]` does not travel through an import, so every file
of this tier repeats the line — even this one, which has no `Ext` in any
statement: the closer's second stage still has them in its list. -/
attribute [-grind] RelE.ext RelE.of_ext RelE.retarget

/-! ## The two one-node readers — `ExprOps.lean:771`, `:776`

`isForallE` is a tag read off the handle word; `lamPair?` tests both tags and
then takes the two binder projections (task #119: con-leche's λ-telescope
comparison `defeqLams` descends with it).  No recursion, no fuel. -/

/-- con-leche: ConLeche/Kernel/ExprOps.lean:771-774 isForallE — **THEOREM 1
for `isForallE`**: the tag of a denoting handle is `forallE` exactly when its
denotation is a ∀. -/
theorem isForallE_rel {st : EStore} (hwf : StoreWF st) {h : EIdx} {e : Expr}
    (he : denoteE st h = some e) : isForallE h = Expr.isForallE e := by
  obtain ⟨v, hv⟩ := denoteE_view he
  have htag := EStore.tagOf_of_view hv
  rw [denoteE_view_eq hwf hv] at he
  simp only [isForallE, htag]
  cases v <;>
    simp_all [ENodeView.tagOf, denoteEView, Expr.isForallE, opt2_eq_some_iff,
      opt3_eq_some_iff, Option.map_eq_some_iff, ETag.bvar, ETag.fvar, ETag.sort,
      ETag.const, ETag.app, ETag.lam, ETag.forallE, ETag.letE, ETag.lit,
      ETag.proj] <;> grind

/-- con-leche: none — a handle that denotes a λ carries the `lam` tag. -/
theorem tag_lam_of_denote {st : EStore} (hwf : StoreWF st) {h : EIdx} {t b : Expr}
    (he : denoteE st h = some (.lam t b)) : h.tag = ETag.lam := by
  obtain ⟨v, hv⟩ := denoteE_view he
  have htag := EStore.tagOf_of_view hv
  rw [denoteE_view_eq hwf hv] at he
  cases v <;>
    simp_all [ENodeView.tagOf, denoteEView, opt2_eq_some_iff, opt3_eq_some_iff,
      Option.map_eq_some_iff]

/-- con-leche: ConLeche/Kernel/ExprOps.lean:776-780 lamPair? — the declining
arm: a handle pair whose tags are not both `lam` denotes no λ pair (task
#120: the arm's content as a lemma `bridge_auto` instantiates). -/
theorem lamPair?_none_of_tag {st : EStore} (hwf : StoreWF st) {a b : EIdx}
    {ea eb : Expr} (hea : denoteE st a = some ea) (heb : denoteE st b = some eb)
    (htg : ¬ (a.tag == ETag.lam && b.tag == ETag.lam) = true) :
    Expr.lamPair? ea eb = none := by
  cases ea <;> cases eb <;> try rfl
  exact absurd (by simp [tag_lam_of_denote hwf hea, tag_lam_of_denote hwf heb]) htg

/-- con-leche: ConLeche/Kernel/ExprOps.lean:776-780 lamPair? — **THEOREM 1
for `lamPair?`**: the state does not move; `none` exactly when the two
denotations are not both λs, and otherwise the four handles denote the four
components. -/
theorem lamPair?_spec (s₀ : AState) (a b : EIdx) (hok : StateOK s₀)
    (ha : (denoteE s₀.store a).isSome = true)
    (hb : (denoteE s₀.store b).isSome = true) :
    ⦃fun s => s = s₀⦄ lamPair? a b
    ⦃fun r s' => s' = s₀ ∧ ∀ ea eb, denoteE s₀.store a = some ea →
        denoteE s₀.store b = some eb →
        match r with
        | none => Expr.lamPair? ea eb = none
        | some (t₁, b₁, t₂, b₂) => ∃ et₁ eb₁ et₂ eb₂,
            Expr.lamPair? ea eb = some (et₁, eb₁, et₂, eb₂) ∧
            denoteE s₀.store t₁ = some et₁ ∧ denoteE s₀.store b₁ = some eb₁ ∧
            denoteE s₀.store t₂ = some et₂ ∧ denoteE s₀.store b₂ = some eb₂; ⊤⦄ := by
  vcgen [lamPair?]
  all_goals (bridge_peel; subst_vars)
  bridge_auto [lamPair?_none_of_tag]

/-! ## The axiom check -/

#print axioms isForallE_rel
#print axioms tag_lam_of_denote
#print axioms lamPair?_spec

end ConRon.Bridge.ExprOps
