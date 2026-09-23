/-
# `ConRon.Bridge.ExprOps.Walks` — Theorem 1 for the `Bool` and `Nat` walks

DESIGN §8.2's Theorem 1 at the twins of `Arena/ExprOps.lean` whose answer is
a **representation-free scalar**: `sizeB`, `sizeF`, `wscopedB`,
`looseBVarsBounded`, `hasFvar`, and the three one-node readers `isLam`,
`lamPw`, `forallPw`.  Its two companions are `ExprOps/Ranges.lean` (the
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

/-! ## The generic `RelV` step lemmas

Not used by any proof below — `bridge_vcs [f, RelV]` closes every arm — but
stated because they are what a walk whose arms `grind` cannot take would need,
and because they are the `RelV` half of `Bridge/Rel.lean` group 7's step
lemmas, which that file has only for `RelE`.  **They morally belong in
`Bridge/Rel.lean`**; they are here because this task owns one file.

Each is `RelE.app`'s shape with the rebuilt view replaced by a pure
combining function `g`: the subject's children's answers, combined, are the
answer at the subject. -/

/-- con-leche: ConLeche/Verify/SimI.lean:252 RelV — the `app` step at a
representation-free answer. -/
theorem RelV.app {α β γ : Type} {F : Expr → γ} {Ff : Expr → α} {Fa : Expr → β}
    {g : α → β → γ} {st : EStore} {h f a : EIdx} {x : α} {y : β}
    (hwf : StoreWF st) (hview : st.view h = some (.app f a))
    (hdec : ∀ u v, F (.app u v) = g (Ff u) (Fa v))
    (hf : RelV Ff st f x) (ha : RelV Fa st a y) : RelV F st h (g x y) := by
  intro e he
  obtain ⟨ef, ea, rfl, hdf, hda⟩ := denote_app_inv hwf hview he
  rw [hdec, hf ef hdf, ha ea hda]

/-- con-leche: ConLeche/Verify/SimI.lean:252 RelV — the `lam` step. -/
theorem RelV.lam {α β γ : Type} {F : Expr → γ} {Ft : Expr → α} {Fb : Expr → β}
    {g : α → β → γ} {st : EStore} {h ty b : EIdx} {m : BinderMeta} {x : α}
    {y : β} (hwf : StoreWF st) (hview : st.view h = some (.lam ty b m))
    (hdec : ∀ u v, F (.lam u v m) = g (Ft u) (Fb v))
    (ht : RelV Ft st ty x) (hb : RelV Fb st b y) : RelV F st h (g x y) := by
  intro e he
  obtain ⟨et, eb, rfl, hdt, hdb⟩ := denote_lam_inv hwf hview he
  rw [hdec, ht et hdt, hb eb hdb]

/-- con-leche: ConLeche/Verify/SimI.lean:252 RelV — the `forallE` step. -/
theorem RelV.forallE {α β γ : Type} {F : Expr → γ} {Ft : Expr → α}
    {Fb : Expr → β} {g : α → β → γ} {st : EStore} {h ty b : EIdx}
    {m : BinderMeta} {x : α} {y : β} (hwf : StoreWF st)
    (hview : st.view h = some (.forallE ty b m))
    (hdec : ∀ u v, F (.forallE u v m) = g (Ft u) (Fb v))
    (ht : RelV Ft st ty x) (hb : RelV Fb st b y) : RelV F st h (g x y) := by
  intro e he
  obtain ⟨et, eb, rfl, hdt, hdb⟩ := denote_forallE_inv hwf hview he
  rw [hdec, ht et hdt, hb eb hdb]

/-- con-leche: ConLeche/Verify/SimI.lean:252 RelV — the `letE` step. -/
theorem RelV.letE {α β γ δ : Type} {F : Expr → δ} {Ft : Expr → α}
    {Fv : Expr → β} {Fb : Expr → γ} {g : α → β → γ → δ} {st : EStore}
    {h ty v b : EIdx} {x : α} {y : β} {z : γ} (hwf : StoreWF st)
    (hview : st.view h = some (.letE ty v b))
    (hdec : ∀ u w t, F (.letE u w t) = g (Ft u) (Fv w) (Fb t))
    (ht : RelV Ft st ty x) (hv : RelV Fv st v y) (hb : RelV Fb st b z) :
    RelV F st h (g x y z) := by
  intro e he
  obtain ⟨et, ev, eb, rfl, hdt, hdv, hdb⟩ := denote_letE_inv hwf hview he
  rw [hdec, ht et hdt, hv ev hdv, hb eb hdb]

/-- con-leche: ConLeche/Verify/SimI.lean:252 RelV — the `proj` step.  The
structure name is not read, so unlike `RelE.proj` this needs no name fact. -/
theorem RelV.proj {α β : Type} {F : Expr → β} {Fs : Expr → α} {g : α → β}
    {st : EStore} {h sub : EIdx} {n : NIdx} {i : Nat} {x : α}
    (hwf : StoreWF st) (hview : st.view h = some (.proj n i sub))
    (hdec : ∀ nm u, F (.proj nm i u) = g (Fs u)) (hs : RelV Fs st sub x) :
    RelV F st h (g x) := by
  intro e he
  obtain ⟨nm, es, rfl, _, hds⟩ := denote_proj_inv hwf hview he
  rw [hdec, hs es hds]

/-- con-leche: ConLeche/Verify/SimI.lean:252 RelV — the `fvar` step, which is
the one arm where `sizeF`, `wscopedB` and `fvarLeaves` differ from the
abstraction walks: the annotation is descended. -/
theorem RelV.fvar {α β : Type} {F : Expr → β} {Ft : Expr → α} {g : Nat → α → β}
    {st : EStore} {h ty : EIdx} {k : Nat} {x : α} (hwf : StoreWF st)
    (hview : st.view h = some (.fvar k ty))
    (hdec : ∀ u, F (.fvar k u) = g k (Ft u)) (ht : RelV Ft st ty x) :
    RelV F st h (g k x) := by
  intro e he
  obtain ⟨t, rfl, hdt⟩ := denote_fvar_inv hwf hview he
  rw [hdec, ht t hdt]

/-! ### The catch-all of the one-node readers

`isLam`, `lamPw` and `forallPw` are `match ← view h` with ONE named arm and a
`_ =>` fallthrough, and the fallthrough is the one verification condition the
closer cannot take unaided: it has "the view is not a `lam`" as a
`∀`-hypothesis over `ENodeView` and no reason to case-split on the view.
Stated as a DISJUNCTION the closer takes it in one step — `grind` splits the
`∨`, and the left disjunct contradicts the arm's own hypothesis.  This is
`Bridge/Rel.lean`'s `denote_leaf_of_tag` played at the constructor rather
than at the tag, and it **morally belongs in `Bridge/Rel.lean`**. -/

/-- con-leche: none — a handle whose view is not a `lam` denotes a term that
is not a `lam`, in the form `grind` can split. -/
@[grind →] theorem denote_lam_or {st : EStore} (hwf : StoreWF st) {h : EIdx}
    {v : ENodeView} {e : Expr} (hview : st.view h = some v)
    (he : denoteE st h = some e) :
    (∃ ty b m, v = .lam ty b m) ∨ (e.isLam = false ∧ Expr.lamPw e = none) := by
  cases v with
  | bvar i => rw [denote_bvar_inv hwf hview he]; exact Or.inr ⟨rfl, rfl⟩
  | fvar k t =>
    obtain ⟨_, rfl, _⟩ := denote_fvar_inv hwf hview he; exact Or.inr ⟨rfl, rfl⟩
  | sort u =>
    obtain ⟨_, rfl, _⟩ := denote_sort_inv hwf hview he; exact Or.inr ⟨rfl, rfl⟩
  | const n us =>
    obtain ⟨_, _, rfl, _, _⟩ := denote_const_inv hwf hview he
    exact Or.inr ⟨rfl, rfl⟩
  | app f a =>
    obtain ⟨_, _, rfl, _, _⟩ := denote_app_inv hwf hview he
    exact Or.inr ⟨rfl, rfl⟩
  | lam ty b m => exact Or.inl ⟨ty, b, m, rfl⟩
  | forallE ty b m =>
    obtain ⟨_, _, rfl, _, _⟩ := denote_forallE_inv hwf hview he
    exact Or.inr ⟨rfl, rfl⟩
  | letE ty w b =>
    obtain ⟨_, _, _, rfl, _, _, _⟩ := denote_letE_inv hwf hview he
    exact Or.inr ⟨rfl, rfl⟩
  | lit l => rw [denote_lit_inv hwf hview he]; exact Or.inr ⟨rfl, rfl⟩
  | proj n i sub =>
    obtain ⟨_, _, rfl, _, _⟩ := denote_proj_inv hwf hview he
    exact Or.inr ⟨rfl, rfl⟩

/-- con-leche: none — the same at the `forallE` constructor, for
`forallPw`'s fallthrough. -/
@[grind →] theorem denote_forallE_or {st : EStore} (hwf : StoreWF st)
    {h : EIdx} {v : ENodeView} {e : Expr} (hview : st.view h = some v)
    (he : denoteE st h = some e) :
    (∃ ty b m, v = .forallE ty b m) ∨ Expr.forallPw e = none := by
  cases v with
  | bvar i => rw [denote_bvar_inv hwf hview he]; exact Or.inr rfl
  | fvar k t =>
    obtain ⟨_, rfl, _⟩ := denote_fvar_inv hwf hview he; exact Or.inr rfl
  | sort u =>
    obtain ⟨_, rfl, _⟩ := denote_sort_inv hwf hview he; exact Or.inr rfl
  | const n us =>
    obtain ⟨_, _, rfl, _, _⟩ := denote_const_inv hwf hview he
    exact Or.inr rfl
  | app f a =>
    obtain ⟨_, _, rfl, _, _⟩ := denote_app_inv hwf hview he; exact Or.inr rfl
  | lam ty b m =>
    obtain ⟨_, _, rfl, _, _⟩ := denote_lam_inv hwf hview he; exact Or.inr rfl
  | forallE ty b m => exact Or.inl ⟨ty, b, m, rfl⟩
  | letE ty w b =>
    obtain ⟨_, _, _, rfl, _, _, _⟩ := denote_letE_inv hwf hview he
    exact Or.inr rfl
  | lit l => rw [denote_lit_inv hwf hview he]; exact Or.inr rfl
  | proj n i sub =>
    obtain ⟨_, _, rfl, _, _⟩ := denote_proj_inv hwf hview he; exact Or.inr rfl

/-! ## `sizeB` — `ExprOps.lean:644`

The `Spec` record of `ExprOps/Inst1.lean` at its simplest: one level of the
recursion, with the state frozen.  `StateOK` is a hypothesis and not a
conjunct of the postcondition because the store does not move; the fuel
induction hands the arms `ih.run` exactly as `Inst1Spec` does. -/

/-- con-leche: ConLeche/Verify/SimI.lean:244 SimAt — Theorem 1's statement for
one level of `sizeB`'s recursion. -/
structure SizeBSpec (rec : EIdx → AM Nat) : Prop where
  run : ∀ (s₁ : AState) (c : EIdx), StateOK s₁ →
      (denoteE s₁.store c).isSome = true →
    ⦃fun s => ⌜s = s₁⌝⦄ rec c
    ⦃⇓? r s' => ⌜s' = s₁ ∧ RelV Expr.sizeB s₁.store c r⌝⦄

/-- con-leche: ConLeche/Kernel/ExprOps.lean:741-748 sizeB — **THEOREM 1 for
`sizeB`**, at one level of the recursion, by induction on the fuel. -/
theorem sizeB_spec : ∀ fuel, SizeBSpec (sizeB fuel) := by
  intro fuel
  induction fuel with
  | zero =>
    constructor
    intro s₀ h _ _
    mvcgen [sizeB_zero]
    all_goals bridge_vcs [Expr.sizeB, RelV]
  | succ fuel ih =>
    constructor
    intro s₀ h hok hden
    have hrec := ih.run
    mvcgen [sizeB_succ, sizeBArmApp, sizeBArmBind, sizeBArmLet, sizeBArmProj, hrec]
    all_goals bridge_vcs [Expr.sizeB, RelV]

/-- con-leche: ConLeche/Kernel/ExprOps.lean:741-748 sizeB — the same statement
about a RUN, which is the form the tier above consumes. -/
theorem sizeB_run {fuel : Nat} {s₀ s' : AState} {h : EIdx} {r : Nat}
    (hok : StateOK s₀) (hden : (denoteE s₀.store h).isSome = true)
    (hrun : (sizeB fuel h).run s₀ = Except.ok (r, s')) :
    s' = s₀ ∧ RelV Expr.sizeB s₀.store h r :=
  AM.of_run (P := fun s => s = s₀) rfl hrun
    ((sizeB_spec fuel).run s₀ h hok hden)

/-! ## `sizeF` — `ExprOps.lean:703`

`sizeB` with the `fvar` annotation counted: the one arm that differs, and it
differs by descending into a child the other walk treats as a leaf. -/

/-- con-leche: ConLeche/Verify/SimI.lean:244 SimAt — Theorem 1's statement for
one level of `sizeF`'s recursion. -/
structure SizeFSpec (rec : EIdx → AM Nat) : Prop where
  run : ∀ (s₁ : AState) (c : EIdx), StateOK s₁ →
      (denoteE s₁.store c).isSome = true →
    ⦃fun s => ⌜s = s₁⌝⦄ rec c
    ⦃⇓? r s' => ⌜s' = s₁ ∧ RelV Expr.sizeF s₁.store c r⌝⦄

/-- con-leche: ConLeche/Kernel/ExprOps.lean:810-819 sizeF — **THEOREM 1 for
`sizeF`**. -/
theorem sizeF_spec : ∀ fuel, SizeFSpec (sizeF fuel) := by
  intro fuel
  induction fuel with
  | zero =>
    constructor
    intro s₀ h _ _
    mvcgen [sizeF_zero]
    all_goals bridge_vcs [Expr.sizeF, RelV]
  | succ fuel ih =>
    constructor
    intro s₀ h hok hden
    have hrec := ih.run
    mvcgen [sizeF_succ, sizeFArmFVar, sizeFArmApp, sizeFArmBind, sizeFArmLet, sizeFArmProj, hrec]
    all_goals bridge_vcs [Expr.sizeF, RelV]

/-- con-leche: ConLeche/Kernel/ExprOps.lean:810-819 sizeF — the run form. -/
theorem sizeF_run {fuel : Nat} {s₀ s' : AState} {h : EIdx} {r : Nat}
    (hok : StateOK s₀) (hden : (denoteE s₀.store h).isSome = true)
    (hrun : (sizeF fuel h).run s₀ = Except.ok (r, s')) :
    s' = s₀ ∧ RelV Expr.sizeF s₀.store h r :=
  AM.of_run (P := fun s => s = s₀) rfl hrun
    ((sizeF_spec fuel).run s₀ h hok hden)

/-! ## `wscopedB` — `ExprOps.lean:757`

The unmemoized scope check, which is `Kernel/ExprOps.lean`'s and is the
SPECIFICATION of `wscopedBFast` (`ExprOps/Leaves.lean`).  The cursor is part
of the relation, and the `fvar` arm descends at the annotation's OWN index —
so the `Spec` record quantifies over `d` and the recursive hypothesis is used
at a different `d` than the one it was given, which is why `d` is universally
quantified inside `run` rather than being a parameter of the record. -/

/-- con-leche: ConLeche/Verify/SimI.lean:244 SimAt — Theorem 1's statement for
one level of `wscopedB`'s recursion. -/
structure WScopedBSpec (rec : Nat → EIdx → AM Bool) : Prop where
  run : ∀ (s₁ : AState) (d : Nat) (c : EIdx), StateOK s₁ →
      (denoteE s₁.store c).isSome = true →
    ⦃fun s => ⌜s = s₁⌝⦄ rec d c
    ⦃⇓? r s' => ⌜s' = s₁ ∧ RelV (Expr.wscopedB d) s₁.store c r⌝⦄

/-- con-leche: ConLeche/Kernel/ExprOps.lean:835-861 wscopedB — **THEOREM 1 for
`wscopedB`**.  con-leche's `&&` is short-circuiting and so is the twin's
explicit `if` chain, so the two agree arm for arm without a `Bool` lemma. -/
theorem wscopedB_spec : ∀ fuel, WScopedBSpec (wscopedB fuel) := by
  intro fuel
  induction fuel with
  | zero =>
    constructor
    intro s₀ d h _ _
    mvcgen [wscopedB_zero]
    all_goals bridge_vcs [Expr.wscopedB, RelV]
  | succ fuel ih =>
    constructor
    intro s₀ d h hok hden
    have hrec := ih.run
    mvcgen [wscopedB_succ, wscopedBArmApp, wscopedBArmBind, wscopedBArmLet, hrec]
    all_goals bridge_vcs [Expr.wscopedB, RelV]

/-- con-leche: ConLeche/Kernel/ExprOps.lean:835-861 wscopedB — the run form. -/
theorem wscopedB_run {fuel d : Nat} {s₀ s' : AState} {h : EIdx} {r : Bool}
    (hok : StateOK s₀) (hden : (denoteE s₀.store h).isSome = true)
    (hrun : (wscopedB fuel d h).run s₀ = Except.ok (r, s')) :
    s' = s₀ ∧ RelV (Expr.wscopedB d) s₀.store h r :=
  AM.of_run (P := fun s => s = s₀) rfl hrun
    ((wscopedB_spec fuel).run s₀ d h hok hden)

/-! ## `looseBVarsBounded` — `ExprOps.lean:973`

The pure walk, which con-leche's `@[csimp]` pair makes the specification of
the `O(1)` field read `looseBVarsBoundedFast` (`ExprOps/Ranges.lean`).  The
cursor is bumped under binders, so it is quantified inside `run` for
`wscopedB`'s reason. -/

/-- con-leche: ConLeche/Verify/SimI.lean:244 SimAt — Theorem 1's statement for
one level of `looseBVarsBounded`'s recursion. -/
structure LooseBVarsBoundedSpec (rec : Nat → EIdx → AM Bool) : Prop where
  run : ∀ (s₁ : AState) (k : Nat) (c : EIdx), StateOK s₁ →
      (denoteE s₁.store c).isSome = true →
    ⦃fun s => ⌜s = s₁⌝⦄ rec k c
    ⦃⇓? r s' => ⌜s' = s₁ ∧ RelV (Expr.looseBVarsBounded k) s₁.store c r⌝⦄

/-- con-leche: ConLeche/Kernel/ExprOps.lean:863-877 looseBVarsBounded —
**THEOREM 1 for `looseBVarsBounded`**. -/
theorem looseBVarsBounded_spec :
    ∀ fuel, LooseBVarsBoundedSpec (looseBVarsBounded fuel) := by
  intro fuel
  induction fuel with
  | zero =>
    constructor
    intro s₀ k h _ _
    mvcgen [looseBVarsBounded_zero]
    all_goals bridge_vcs [Expr.looseBVarsBounded, RelV]
  | succ fuel ih =>
    constructor
    intro s₀ k h hok hden
    have hrec := ih.run
    mvcgen [looseBVarsBounded_succ, looseBArmApp, looseBArmBind, looseBArmLet, hrec]
    all_goals bridge_vcs [Expr.looseBVarsBounded, RelV]

/-- con-leche: ConLeche/Kernel/ExprOps.lean:863-877 looseBVarsBounded — the
run form. -/
theorem looseBVarsBounded_run {fuel k : Nat} {s₀ s' : AState} {h : EIdx}
    {r : Bool} (hok : StateOK s₀)
    (hden : (denoteE s₀.store h).isSome = true)
    (hrun : (looseBVarsBounded fuel k h).run s₀ = Except.ok (r, s')) :
    s' = s₀ ∧ RelV (Expr.looseBVarsBounded k) s₀.store h r :=
  AM.of_run (P := fun s => s = s₀) rfl hrun
    ((looseBVarsBounded_spec fuel).run s₀ k h hok hden)

/-! ## `hasFvar` — `ExprOps.lean:1022`

The pure walk, `@[csimp]`-replaced by the field read `hasFvarFast`
(`ExprOps/Ranges.lean`).  Note the arms are `||`-shaped where `wscopedB`'s
are `&&`-shaped, and the twin's `if x then pure true else …` chain is the
short-circuit spelled out. -/

/-- con-leche: ConLeche/Verify/SimI.lean:244 SimAt — Theorem 1's statement for
one level of `hasFvar`'s recursion. -/
structure HasFvarSpec (rec : EIdx → AM Bool) : Prop where
  run : ∀ (s₁ : AState) (c : EIdx), StateOK s₁ →
      (denoteE s₁.store c).isSome = true →
    ⦃fun s => ⌜s = s₁⌝⦄ rec c
    ⦃⇓? r s' => ⌜s' = s₁ ∧ RelV Expr.hasFvar s₁.store c r⌝⦄

/-- con-leche: ConLeche/Kernel/ExprOps.lean:904-913 hasFvar — **THEOREM 1 for
`hasFvar`**. -/
theorem hasFvar_spec : ∀ fuel, HasFvarSpec (hasFvar fuel) := by
  intro fuel
  induction fuel with
  | zero =>
    constructor
    intro s₀ h _ _
    mvcgen [hasFvar_zero]
    all_goals bridge_vcs [Expr.hasFvar, RelV]
  | succ fuel ih =>
    constructor
    intro s₀ h hok hden
    have hrec := ih.run
    mvcgen [hasFvar_succ, hasFvarArmApp, hasFvarArmBind, hasFvarArmLet, hrec]
    all_goals bridge_vcs [Expr.hasFvar, RelV]

/-- con-leche: ConLeche/Kernel/ExprOps.lean:904-913 hasFvar — the run
form. -/
theorem hasFvar_run {fuel : Nat} {s₀ s' : AState} {h : EIdx} {r : Bool}
    (hok : StateOK s₀) (hden : (denoteE s₀.store h).isSome = true)
    (hrun : (hasFvar fuel h).run s₀ = Except.ok (r, s')) :
    s' = s₀ ∧ RelV Expr.hasFvar s₀.store h r :=
  AM.of_run (P := fun s => s = s₀) rfl hrun
    ((hasFvar_spec fuel).run s₀ h hok hden)

/-! ## The three one-node readers — `ExprOps.lean:1000`, `:1008`, `:1015`

One `view` and a test: no recursion, no fuel, so no `Spec` record and no
induction.  Theorem 1 is the triple itself.

**`lamPw` and `forallPw` answer `Option PropWhen`, and `PropWhen` is a SEALED
representation** (con-leche's own `ExprOps.lean` needs `import all` to
destruct one; the arena never destructs one, it only compares).  So the two
are stated against con-leche's `Expr.lamPw` / `Expr.forallPw` as equations on
the `Option PropWhen` and nothing below looks inside: the `BinderMeta` the
twin reads off the node IS the one the denotation carries
(`denote_lam_inv`'s `e = .lam et eb m`), so `m.pw` needs no unfolding. -/

/-- con-leche: none — `isLam`'s tag-first `then` arm (task #97-T2-LOCKSTEP): a
λ-tagged handle whose binder projection reads is a λ. -/
theorem relV_isLam_true {st : EStore} (hwf : StoreWF st) {h : EIdx}
    (htg : (h.tag == ETag.lam) = true) {p : EIdx × EIdx × BMIdx}
    (hp : some p = st.viewBindI h) : RelV Expr.isLam st h true := by
  obtain ⟨ty, b, mi⟩ := p
  have ht : h.tag = ETag.lam := by simpa using htg
  obtain ⟨m, -, -, hv⟩ := view_of_viewBindI_wf hwf (by rw [ht]; rfl) hp.symm
  rw [eBindView, ht] at hv
  simp only [beq_self_eq_true, if_true] at hv
  intro e he
  obtain ⟨_, _, rfl, -⟩ := denote_lam_inv hwf hv he
  rfl

/-- con-leche: none — `isLam`'s tag-first `else` arm: a handle that denotes
and is not λ-tagged denotes a non-λ. -/
theorem relV_isLam_false {st : EStore} (hwf : StoreWF st) {h : EIdx}
    (hd : (denoteE st h).isSome = true) (ht : ¬ (h.tag == ETag.lam) = true) :
    RelV Expr.isLam st h false := by
  obtain ⟨v, hv⟩ := view_of_denote_isSome hd
  have hne := view_tagOf_ne hv ht
  intro e he
  rcases denote_lam_or hwf hv he with ⟨ty, b, m, rfl⟩ | ⟨h1, -⟩
  · exact absurd rfl hne
  · exact h1.symm

/-- con-leche: ConLeche/Kernel/ExprOps.lean:879-885 isLam — **THEOREM 1 for
`isLam`**. -/
theorem isLam_spec (s₀ : AState) (h : EIdx) (hok : StateOK s₀)
    (hden : (denoteE s₀.store h).isSome = true) :
    ⦃fun s => ⌜s = s₀⌝⦄ isLam h
    ⦃⇓? r s' => ⌜s' = s₀ ∧ RelV Expr.isLam s₀.store h r⌝⦄ := by
  mvcgen [isLam]
  all_goals try bridge_vcs [Expr.isLam, RelV]
  all_goals
    (bridge_peel
     subst_vars
     first
     | exact ⟨rfl, relV_isLam_true hok.wf (by assumption) (by assumption)⟩
     | exact ⟨rfl, relV_isLam_false hok.wf hden (by assumption)⟩)

/-- con-leche: ConLeche/Kernel/ExprOps.lean:879-885 isLam — the run form. -/
theorem isLam_run {s₀ s' : AState} {h : EIdx} {r : Bool} (hok : StateOK s₀)
    (hden : (denoteE s₀.store h).isSome = true)
    (hrun : (isLam h).run s₀ = Except.ok (r, s')) :
    s' = s₀ ∧ RelV Expr.isLam s₀.store h r :=
  AM.of_run (P := fun s => s = s₀) rfl hrun (isLam_spec s₀ h hok hden)

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

/-- con-leche: ConLeche/Kernel/ExprOps.lean:887-894 lamPw — the run form. -/
theorem lamPw_run {s₀ s' : AState} {h : EIdx} {r : Option PropWhen}
    (hok : StateOK s₀) (hden : (denoteE s₀.store h).isSome = true)
    (hrun : (lamPw h).run s₀ = Except.ok (r, s')) :
    s' = s₀ ∧ RelV Expr.lamPw s₀.store h r :=
  AM.of_run (P := fun s => s = s₀) rfl hrun (lamPw_spec s₀ h hok hden)

/-- con-leche: ConLeche/Kernel/ExprOps.lean:896-902 forallPw — **THEOREM 1 for
`forallPw`**. -/
theorem forallPw_spec (s₀ : AState) (h : EIdx) (hok : StateOK s₀)
    (hden : (denoteE s₀.store h).isSome = true) :
    ⦃fun s => ⌜s = s₀⌝⦄ forallPw h
    ⦃⇓? r s' => ⌜s' = s₀ ∧ RelV Expr.forallPw s₀.store h r⌝⦄ := by
  mvcgen [forallPw]
  all_goals first
    | bridge_vcs [Expr.forallPw, RelV, denote_forallE_inv]
    -- the tag-first `else` arm (task #97-T2-LOCKSTEP)
    | (bridge_peel
       subst_vars
       obtain ⟨v, hv⟩ := view_of_denote_isSome (by assumption)
       have hne := view_tagOf_ne hv (t := ETag.forallE) (by assumption)
       refine ⟨rfl, fun e he => ?_⟩
       rw [denoteE_view_eq hok.wf hv] at he
       cases v <;> first
         | exact absurd rfl hne
         | grind [denoteEView, Expr.forallPw, opt2_eq_some_iff, opt3_eq_some_iff,
             Option.map_eq_some_iff])

/-- con-leche: ConLeche/Kernel/ExprOps.lean:896-902 forallPw — the run
form. -/
theorem forallPw_run {s₀ s' : AState} {h : EIdx} {r : Option PropWhen}
    (hok : StateOK s₀) (hden : (denoteE s₀.store h).isSome = true)
    (hrun : (forallPw h).run s₀ = Except.ok (r, s')) :
    s' = s₀ ∧ RelV Expr.forallPw s₀.store h r :=
  AM.of_run (P := fun s => s = s₀) rfl hrun (forallPw_spec s₀ h hok hden)

/-! ## The axiom check -/

#print axioms sizeB_spec
#print axioms sizeF_spec
#print axioms wscopedB_spec
#print axioms looseBVarsBounded_spec
#print axioms hasFvar_spec
#print axioms isLam_spec
#print axioms lamPw_spec
#print axioms forallPw_spec

end ConRon.Bridge.ExprOps
