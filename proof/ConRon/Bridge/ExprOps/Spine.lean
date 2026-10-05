/-
# `ConRon.Bridge.ExprOps.Spine` — Theorem 1 for the spine and telescope twins

DESIGN §8.2's Theorem 1 at the twins of `Arena/ExprOps.lean` that
walk an APPLICATION SPINE or a BINDER TELESCOPE rather than the handle DAG:
`getAppFn` … `instLamsAt` (`ExprOps.lean:1045`–`:1387`).

## What makes this group different from `ExprOps/Inst1`

1. **Almost none of them takes a memo, and half take no fuel.**  The
   recursion is structural on a binder count (`stripPis`), on an
   argument list (`mkAppN`, `instSpine`, `instPisAt`) or on a `Nat` cursor
   (`mkAppNFrom`, `bvarRange`), so the theorems are plain inductions over
   that argument and not fuel inductions, and the postcondition frames no
   memo table at all.  The six READ-ONLY twins (`getAppFn`, `getAppArgs`,
   `stripLams`, `stripPis`, `piResult`, `fvarTypeD`) intern nothing, so their postcondition is `s' = s₀` and the
   answer relation's two stores coincide.
2. **Two of them are arena-only.**  `bvarRange` interns `recRulePlain`'s
   comparand list (con-leche writes it as a literal `List.map`) and
   `mkAppNFrom` applies a PUSH-ORDER `Array` from a cursor (task #97-P6-15's
   clause change).  Their doc comments say `con-leche: none` and their
   theorems are exactly the list facts their callers consume: `bvarRange`'s
   answer denotes `(List.range n).map …`, and `mkAppNFrom`'s pure function is
   `mkAppN`'s at the dropped prefix, so `mkAppN_spec` composes with it.
3. **The `…F` accumulators are REVERSED.**  `instPisAtFGo` / `instLamsAtFGo`
   hold their pending substitutions in an `Array` built with `Array.push`,
   where con-leche's `instPisAtFGo` builds a `List` with `a :: acc` — task
   #97-P6-15's "thirteen accumulator sites moved".  So an accumulator that
   denotes `L` in array order is con-leche's `L.reverse`, and every `…F`
   statement below says `L.reverse` explicitly.  `ExprOpsTest.lean`'s
   `instantiateList` guards are the same reversal's own test (`con-leche's
   [cf, s1] is the twin's #[s1, cf]`).

## The answer relations

`Bridge/Rel.lean` has the four shapes the DAG walks need; this group needs
two more, and they are declared here because they are this group's result
types:

* `RelEP` — an `Option (List EIdx × EIdx)` answer (`instPisAt`,
  `instLamsAt`, and the four `…F`s);
* `RelBP` — an `Option (List (EIdx × BinderMeta) × EIdx)` answer
  (`stripLams`, `stripPis`): the binder metadata is a VALUE and crosses the
  denotation unchanged.

Everything else reuses `Rel.lean`: `RelE` for `getAppFn`, `piResult`,
`fvarTypeD`, `instSpine`, `mkAppN` and `mkAppNFrom` (the last two at the
partially applied pure function `fun x => Expr.mkAppN x eargs`, which is how
a multi-subject twin fits a one-subject relation — the argument list's
denotation is an ordinary hypothesis), `RelV` for `recRulePlain`, and
`RelEL` for `getAppArgs` and `bvarRange`.

## The axiom check, and what it inherits

**Nothing in this file is unproved.**  `#print axioms` at the end reports
`[propext, Classical.choice, Quot.sound]` for every twin.  Three of
them — `instPisAt`, `instLamsAt`, `instSpine` — CONSUME
`ExprOps/Inst1`'s `instantiate1Fast_spec` and inherited its open goals until
task #97-P3-1's arm split closed them; as that section predicted, they closed
with it and no statement changed.

## What this module does not claim

`instPisAtFGo` / `instPisAtF` / `instLamsAtFGo` / `instLamsAtF` call
`instantiateListFast`, whose Theorem 1 belongs to this tier's `Subst` group
and does not exist yet.  Their statements below take it as an explicit
hypothesis — the record `InstListSpec` — exactly as `instantiate1Go_spec`'s
fuel induction takes its own recursive call.  When `Subst.lean` lands the
record is discharged at its `instantiateListFast_spec` and the four theorems
become unconditional; nothing in their statements changes.
-/
import ConRon.Bridge.ExprOps.Inst1
import ConRon.Bridge.ExprOps.TagFirst

namespace ConRon.Bridge.ExprOps

set_option autoImplicit false
set_option experimental.vcgen true
set_option maxHeartbeats 2000000

open ConLeche ConRon.Arena ConRon.Bridge Std.WP
open scoped Lean.Order

/-! ### Attribute hygiene (task #97s round 2, item 1)

`attribute [-grind]` does not travel through an import, so every file of the
tier repeats `ExprOps/Inst1`'s line. -/
attribute [-grind] RelE.ext RelE.of_ext RelE.retarget

/-! ## 1. The answer relations this group adds

Modelled on `Bridge/Rel.lean`'s `RelEO`: an `Option`-valued answer gets a
`denote…` function that turns the handle side into `Option (Option …)`, so
that the relation has `RelE`'s shape exactly and `grind` still sees a head
symbol. -/

/-- con-leche: none — the denotation of a BINDER list: the domain is a
handle, the `BinderMeta` is a value and crosses unchanged (task #97-P6-16's
datum store is read by `view`, so nothing here decodes one). -/
def denoteBL (st : EStore) : List (EIdx × BinderMeta) →
    Option (List (Expr × BinderMeta))
  | [] => some []
  | (t, m) :: bs =>
    match denoteE st t, denoteBL st bs with
    | some x, some xs => some ((x, m) :: xs)
    | _, _ => none

/-- con-leche: none — the denotation of `stripLams`' result shape. -/
def denoteBP (st : EStore) : Option (List (EIdx × BinderMeta) × EIdx) →
    Option (Option (List (Expr × BinderMeta) × Expr))
  | none => some none
  | some (bs, e) =>
    match denoteBL st bs, denoteE st e with
    | some xs, some x => some (some (xs, x))
    | _, _ => none

/-- con-leche: ConLeche/Verify/SimI.lean:250 RelE — the answer relation at
`stripLams`/`stripPis`' result shape. -/
def RelBP (f : Expr → Option (List (Expr × BinderMeta) × Expr))
    (st : EStore) (c : EIdx) (st' : EStore)
    (r : Option (List (EIdx × BinderMeta) × EIdx)) : Prop :=
  ∀ e, denoteE st c = some e → denoteBP st' r = some (f e)

/-! ### The TWO-SUBJECT relations

Half of this group takes a second subject — an argument LIST (`mkAppN`,
`instPisAt`, `instSpine`) — and the answer depends on both.  Template rule 4 says
why the second subject may not be a named `Expr` in the statement: the
recursion carries it forward, so a `∀ eargs` in the PRECONDITION leaves the
recursive call's side goal with a metavariable `grind` cannot invent.  So the
relation quantifies it, exactly as `RelE` quantifies the first.

**All of them belong in `Bridge/Rel.lean` group 7.** -/

/-- con-leche: ConLeche/Verify/SimI.lean:250 RelE — the answer relation with
an argument LIST as a second subject (`mkAppN`, `mkAppNFrom`, `instSpine`). -/
def RelEA (F : Expr → List Expr → Expr) (st : EStore) (c : EIdx)
    (args : List EIdx) (st' : EStore) (r : EIdx) : Prop :=
  ∀ e es, denoteE st c = some e → Frontend.denoteEList st args = some es →
    denoteE st' r = some (F e es)

/-! ### Their eliminators

`.apply` and the two transports, exactly `RelEO`'s set.  **These
`denote…`s and their lemmas morally belong in `Bridge/Rel.lean`** beside
`denoteEO`/`RelEO`; they are here because `Rel.lean` is another agent's file
this round. -/

/-! ## 2. The step lemmas the whole group is written against

All of them morally belong in `Bridge/Rel.lean` group 7 beside
`RelE.of_view`: none mentions a walk.  `RelE.head_step` is `RelE.app` for a
walk that DESCENDS into the head and answers the head's answer (rather than
rebuilding the node), which is `getAppFn`'s and every spine peel's shape;
`RelE.self_of_view` is `RelE.self` with the licence read off the view, which
is what every "not a `∀`" fallthrough arm needs. -/

/-- con-leche: none — a walk that descends into the HEAD of an application
and answers the head's answer, at a known view.  The pure function's own
clause is the decomposition hypothesis, as in `RelE.app`. -/
theorem RelE.head_step {F Ff : Expr → Expr} {st st' : EStore}
    {h f a r : EIdx} (hwf : StoreWF st) (hview : st.view h = some (.app f a))
    (hdec : ∀ x y, F (.app x y) = Ff x) (hf : RelE Ff st f st' r) :
    RelE F st h st' r := by
  intro e he
  obtain ⟨ef, ea, rfl, hdf, _⟩ := denote_app_inv hwf hview he
  rw [hdec]; exact hf ef hdf

/-- con-leche: none — the same at a `∀` node: descend into the BODY.  The
shape of `piResult` and the telescope peels. -/
theorem RelE.body_step {F Fb : Expr → Expr} {st st' : EStore}
    {h ty b r : EIdx} {m : BinderMeta} (hwf : StoreWF st)
    (hview : st.view h = some (.forallE ty b m))
    (hdec : ∀ x y, F (.forallE x y m) = Fb y) (hb : RelE Fb st b st' r) :
    RelE F st h st' r := by
  intro e he
  obtain ⟨et, eb, rfl, _, hdb⟩ := denote_forallE_inv hwf hview he
  rw [hdec]; exact hb eb hdb

/-- con-leche: none — a leaf/fallthrough arm that answers its own subject,
with the licence read off the VIEW rather than off the denoted term.  This is
`RelE.self` in the form `vcgen` produces: the arm has the view as a branch
condition, and `denoteEView` is what the remaining obligation speaks of. -/
theorem RelE.self_of_view {f : Expr → Expr} {st : EStore} {h : EIdx}
    {v : ENodeView} (hwf : StoreWF st) (hview : st.view h = some v)
    (hf : ∀ e, denoteEView st v = some e → f e = e) : RelE f st h st h :=
  RelE.self (fun e he => hf e (by rw [← denoteE_view_eq hwf hview]; exact he))

/-- con-leche: none — `RelBP` at a fallthrough arm that answers `none`. -/
theorem RelBP.none_of_view
    {f : Expr → Option (List (Expr × BinderMeta) × Expr)} {st : EStore}
    {h : EIdx} {v : ENodeView} (hwf : StoreWF st)
    (hview : st.view h = some v)
    (hf : ∀ e, denoteEView st v = some e → f e = none) :
    RelBP f st h st none := by
  intro e he
  rw [denoteE_view_eq hwf hview] at he
  rw [denoteBP, hf e he]

/-- con-leche: ConLeche/Kernel/ExprOps.lean:1212-1217 fvarTypeD — the one
walk of this group that answers a node's CHILD without recursing. -/
theorem RelE.fvar_ty_step {F : Expr → Expr} {st st' : EStore} {h ty : EIdx}
    {k : Nat} (hwf : StoreWF st) (hview : st.view h = some (.fvar k ty))
    (hdec : ∀ x y, F (.fvar x y) = y) (hx : Ext st st') :
    RelE F st h st' ty := by
  intro e he
  obtain ⟨t, rfl, hdt⟩ := denote_fvar_inv hwf hview he
  rw [hdec]; exact denote_ext hdt hx

/-- con-leche: ConLeche/Kernel/ExprOps.lean:925-928 mkAppN — the CONS clause
of an argument fold: intern the application and continue with the tail.  The
one step lemma `mkAppN` and `mkAppNFrom` share; it belongs in
`Bridge/Rel.lean` group 7. -/
theorem RelEA.cons_step {F : Expr → List Expr → Expr} {st s1 st' : EStore}
    {f a g r : EIdx} {as : List EIdx}
    (hdec : ∀ x y ys, F x (y :: ys) = F (.app x y) ys) (hx1 : Ext st s1)
    (hg : denoteE s1 g = denoteEView s1 (.app f a))
    (hrec : RelEA F s1 g as st' r) : RelEA F st f (a :: as) st' r := by
  intro e es he hes
  simp only [Frontend.denoteEList] at hes
  cases ha : denoteE st a with
  | none => rw [ha] at hes; simp at hes
  | some ea =>
    cases has : Frontend.denoteEList st as with
    | none => rw [ha, has] at hes; simp at hes
    | some eas =>
      rw [ha, has] at hes
      obtain rfl := Option.some.inj hes
      rw [hdec]
      refine hrec (.app e ea) eas ?_ (denoteEList_ext hx1 as eas has)
      rw [hg, denoteEView, denote_ext he hx1, denote_ext ha hx1]
      rfl

/-- con-leche: none — an interned `app` node denotes as soon as its children
do: the `isSome` side goal of the argument folds' recursive call.  Belongs in
`Bridge/Rel.lean` group 4. -/
theorem denote_isSome_of_intern_app {st : EStore} {r f a : EIdx}
    (hr : denoteE st r = denoteEView st (.app f a))
    (hf : (denoteE st f).isSome = true) (ha : (denoteE st a).isSome = true) :
    (denoteE st r).isSome = true := by
  obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp hf
  obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp ha
  rw [hr, denoteEView, hx, hy]; rfl

/-- con-leche: ConLeche/Kernel/ExprOps.lean:925-928 mkAppN — the NIL clause:
the fold's answer is its own subject. -/
theorem RelEA.nil {F : Expr → List Expr → Expr} {st st' : EStore} {f : EIdx}
    (hdec : ∀ x, F x [] = x) (hx : Ext st st') : RelEA F st f [] st' f := by
  intro e es he hes
  simp only [Frontend.denoteEList, Option.some.injEq] at hes
  subst hes
  rw [hdec]
  exact denote_ext he hx

/-! ### The `Option`-pair answers' inversions and their two step lemmas

The telescope peels (`stripLams`, `stripPis`, `instPisAt`, `instLamsAt`,
and the four `…F`s) all have the SAME two arms
— "the recursive call answered `some p`, so cons this binder onto it" and
"the recursive call answered `none`, so answer `none`" — and the pure
function's own clause is an `Option.map`.  Two step lemmas per answer shape
cover all eight.  They belong in `Bridge/Rel.lean` group 7. -/

/-- con-leche: none — what `denoteBP` at `some p` says. -/
theorem denoteBP_some_inv {st : EStore} {p : List (EIdx × BinderMeta) × EIdx}
    {x : Option (List (Expr × BinderMeta) × Expr)}
    (h : denoteBP st (some p) = some x) :
    ∃ xs e, x = some (xs, e) ∧ denoteBL st p.1 = some xs ∧
      denoteE st p.2 = some e := by
  simp only [denoteBP] at h
  cases hbl : denoteBL st p.1 with
  | none => rw [hbl] at h; simp at h
  | some xs =>
    cases he : denoteE st p.2 with
    | none => rw [hbl, he] at h; simp at h
    | some e => rw [hbl, he] at h; exact ⟨xs, e, (Option.some.inj h).symm, rfl, rfl⟩

/-- con-leche: ConLeche/Kernel/ExprOps.lean:1128-1134 stripPis — the CONS arm
of a binder peel that keeps the binder metadata. -/
theorem RelBP.cons_step {F Fb : Expr → Option (List (Expr × BinderMeta) × Expr)}
    {st : EStore} {h ty b : EIdx} {m : BinderMeta}
    {p : List (EIdx × BinderMeta) × EIdx} (hwf : StoreWF st)
    (hview : st.view h = some (.forallE ty b m))
    (hdec : ∀ x y bs e, Fb y = some (bs, e) →
      F (.forallE x y m) = some ((x, m) :: bs, e))
    (hb : RelBP Fb st b st (some p)) :
    RelBP F st h st (some ((ty, m) :: p.1, p.2)) := by
  intro e he
  obtain ⟨et, eb, rfl, hdt, hdb⟩ := denote_forallE_inv hwf hview he
  obtain ⟨xs, x, hx, hbl, hde⟩ := denoteBP_some_inv (hb eb hdb)
  rw [hdec et eb xs x hx]
  simp only [denoteBP, denoteBL, hdt, hbl, hde]

/-- con-leche: ConLeche/Kernel/ExprOps.lean:1120-1126 stripLams — the same at
a λ binder. -/
theorem RelBP.consLam_step
    {F Fb : Expr → Option (List (Expr × BinderMeta) × Expr)}
    {st : EStore} {h ty b : EIdx} {m : BinderMeta}
    {p : List (EIdx × BinderMeta) × EIdx} (hwf : StoreWF st)
    (hview : st.view h = some (.lam ty b m))
    (hdec : ∀ x y bs e, Fb y = some (bs, e) →
      F (.lam x y m) = some ((x, m) :: bs, e))
    (hb : RelBP Fb st b st (some p)) :
    RelBP F st h st (some ((ty, m) :: p.1, p.2)) := by
  intro e he
  obtain ⟨et, eb, rfl, hdt, hdb⟩ := denote_lam_inv hwf hview he
  obtain ⟨xs, x, hx, hbl, hde⟩ := denoteBP_some_inv (hb eb hdb)
  rw [hdec et eb xs x hx]
  simp only [denoteBP, denoteBL, hdt, hbl, hde]

/-- con-leche: ConLeche/Kernel/ExprOps.lean:1128-1134 stripPis — the `none`
arm: the peel failed one level down, so it fails here. -/
theorem RelBP.none_step {F Fb : Expr → Option (List (Expr × BinderMeta) × Expr)}
    {st : EStore} {h ty b : EIdx} {m : BinderMeta} (hwf : StoreWF st)
    (hview : st.view h = some (.forallE ty b m))
    (hdec : ∀ x y, Fb y = none → F (.forallE x y m) = none)
    (hb : RelBP Fb st b st none) : RelBP F st h st none := by
  intro e he
  obtain ⟨et, eb, rfl, _, hdb⟩ := denote_forallE_inv hwf hview he
  have hh := hb eb hdb
  simp only [denoteBP, Option.some.injEq] at hh
  rw [hdec et eb hh.symm, denoteBP]

/-- con-leche: ConLeche/Kernel/ExprOps.lean:1120-1126 stripLams — the same at
a λ binder. -/
theorem RelBP.noneLam_step
    {F Fb : Expr → Option (List (Expr × BinderMeta) × Expr)} {st : EStore}
    {h ty b : EIdx} {m : BinderMeta} (hwf : StoreWF st)
    (hview : st.view h = some (.lam ty b m))
    (hdec : ∀ x y, Fb y = none → F (.lam x y m) = none)
    (hb : RelBP Fb st b st none) : RelBP F st h st none := by
  intro e he
  obtain ⟨et, eb, rfl, _, hdb⟩ := denote_lam_inv hwf hview he
  have hh := hb eb hdb
  simp only [denoteBP, Option.some.injEq] at hh
  rw [hdec et eb hh.symm, denoteBP]

/-! ### The `isSome` calculus at a handle LIST

Two facts; after them no proof below unfolds `denoteEList`.  Both belong in
`Bridge/Rel.lean` group 4. -/

/-- con-leche: none — a denoting handle list denotes head and tail. -/
@[grind →] theorem denoteEList_cons_isSome {st : EStore} {a : EIdx}
    {as : List EIdx}
    (h : (Frontend.denoteEList st (a :: as)).isSome = true) :
    (denoteE st a).isSome = true ∧
      (Frontend.denoteEList st as).isSome = true := by
  simp only [Frontend.denoteEList] at h
  cases ha : denoteE st a with
  | none => rw [ha] at h; simp at h
  | some x =>
    cases has : Frontend.denoteEList st as with
    | none => rw [ha, has] at h; simp at h
    | some xs => exact ⟨rfl, rfl⟩

/-- con-leche: none — `isSome` survives an arena extension, at a LIST. -/
@[grind →] theorem denoteEList_isSome_ext {st st' : EStore} {rs : List EIdx}
    (h : (Frontend.denoteEList st rs).isSome = true) (hx : Ext st st') :
    (Frontend.denoteEList st' rs).isSome = true := by
  obtain ⟨xs, hxs⟩ := Option.isSome_iff_exists.mp h
  rw [denoteEList_ext hx rs xs hxs]; rfl

/-! ### `denoteEView` preserves the head constructor

The fallthrough arm of a telescope walk is handed the view as an ABSTRACT
`ENodeView` with a negative constraint (`∀ ty b m, x ≠ .forallE ty b m`) — it
is one arm and not nine, because `vcgen` does not split a `match` whose
default case is a wildcard.  So what the arm needs is that the CONSTRAINT
travels to the denoted term, and that is one ten-case analysis, done once
here.  It belongs in `Bridge/Rel.lean` beside `denoteEView_ext`. -/

/-- con-leche: none — a node view's denotation has the view's own head
constructor, as the four negative facts this group's fallthrough arms need. -/
theorem denoteEView_shape {st : EStore} {v : ENodeView} {e : Expr}
    (h : denoteEView st v = some e) :
    ((∀ ty b m, v ≠ .forallE ty b m) → ∀ ty b m, e ≠ .forallE ty b m) ∧
      ((∀ ty b m, v ≠ .lam ty b m) → ∀ ty b m, e ≠ .lam ty b m) ∧
      ((∀ k t, v ≠ .fvar k t) → ∀ k t, e ≠ .fvar k t) ∧
      ((∀ u, v ≠ .sort u) → ∀ l, e ≠ .sort l) := by
  cases v <;>
    grind [denoteEView, opt2_eq_some_iff, opt3_eq_some_iff,
      Option.map_eq_some_iff]

/-- con-leche: none — `denoteEView_shape`'s `∀` projection. -/
theorem denoteEView_not_forallE {st : EStore} {v : ENodeView} {e : Expr}
    (h : denoteEView st v = some e) (hv : ∀ ty b m, v ≠ .forallE ty b m) :
    ∀ ty b m, e ≠ .forallE ty b m := (denoteEView_shape h).1 hv

/-- con-leche: none — its λ projection. -/
theorem denoteEView_not_lam {st : EStore} {v : ENodeView} {e : Expr}
    (h : denoteEView st v = some e) (hv : ∀ ty b m, v ≠ .lam ty b m) :
    ∀ ty b m, e ≠ .lam ty b m := (denoteEView_shape h).2.1 hv

/-- con-leche: none — its `fvar` projection. -/
theorem denoteEView_not_fvar {st : EStore} {v : ENodeView} {e : Expr}
    (h : denoteEView st v = some e) (hv : ∀ k t, v ≠ .fvar k t) :
    ∀ k t, e ≠ .fvar k t := (denoteEView_shape h).2.2.1 hv

/-- con-leche: none — its `sort` projection. -/
theorem denoteEView_not_sort {st : EStore} {v : ENodeView} {e : Expr}
    (h : denoteEView st v = some e) (hv : ∀ u, v ≠ .sort u) :
    ∀ l, e ≠ .sort l := (denoteEView_shape h).2.2.2 hv

/-! ### The pure functions' fallthrough clauses

One lemma per twin, each a `cases e` over the ten constructors.  They are the
`instantiate1_leaf` of this group (`ExprOps/Inst1`'s own catch-all licence). -/

/-- con-leche: ConLeche/Kernel/ExprOps.lean:1136-1140 piResult — the
fallthrough clause. -/
theorem piResult_of_not_forallE {e : Expr}
    (h : ∀ ty b m, e ≠ Expr.forallE ty b m) : Expr.piResult e = e := by
  cases e with
  | forallE ty b m => exact absurd rfl (h ty b m)
  | _ => simp [Expr.piResult]

/-- con-leche: ConLeche/Kernel/ExprOps.lean:1212-1217 fvarTypeD — the
fallthrough clause. -/
theorem fvarTypeD_of_not_fvar {e : Expr} (h : ∀ k t, e ≠ Expr.fvar k t) :
    Expr.fvarTypeD e = e := by
  cases e with
  | fvar k t => exact absurd rfl (h k t)
  | _ => simp [Expr.fvarTypeD]

/-- con-leche: ConLeche/Kernel/ExprOps.lean:1128-1134 stripPis — the
fallthrough clause at a nonzero count. -/
theorem stripPis_of_not_forallE {e : Expr} {k : Nat}
    (h : ∀ ty b m, e ≠ Expr.forallE ty b m) :
    Expr.stripPis (k + 1) e = none := by
  cases e with
  | forallE ty b m => exact absurd rfl (h ty b m)
  | _ => simp [Expr.stripPis]

/-- con-leche: ConLeche/Kernel/ExprOps.lean:1120-1126 stripLams — the
fallthrough clause at a nonzero count. -/
theorem stripLams_of_not_lam {e : Expr} {k : Nat}
    (h : ∀ ty b m, e ≠ Expr.lam ty b m) :
    Expr.stripLams (k + 1) e = none := by
  cases e with
  | lam ty b m => exact absurd rfl (h ty b m)
  | _ => simp [Expr.stripLams]

/-! ### The tag dispatch's licence at `app`

`getAppFn` and `getAppArgs` test `h.tag == ETag.app` before reading the store
(task #97-P6-13), so their fallthrough arm knows only the NEGATIVE tag fact.
This is `Rel.lean`'s `denote_leaf_of_tag` at one constructor instead of four,
and it belongs there. -/

/-- con-leche: none — a handle whose tag is not `app` denotes a term that is
not an application. -/
theorem not_app_of_tag {st : EStore} (hwf : StoreWF st) {h : EIdx} {e : Expr}
    (htg : ¬ (h.tag = ETag.app)) (he : denoteE st h = some e) :
    ∀ x y, e ≠ .app x y := by
  obtain ⟨v, hvw⟩ := denoteE_view he
  have htag := EStore.tagOf_of_view hvw
  cases v with
  | bvar i => rw [denote_bvar_inv hwf hvw he]; intro x y; simp
  | fvar k t =>
    obtain ⟨t', rfl, _⟩ := denote_fvar_inv hwf hvw he; intro x y; simp
  | sort u => obtain ⟨l, rfl, _⟩ := denote_sort_inv hwf hvw he; intro x y; simp
  | const n us =>
    obtain ⟨nm, ls, rfl, _, _⟩ := denote_const_inv hwf hvw he; intro x y; simp
  | app f a => exact absurd (htag.trans rfl) htg
  | lam ty b m =>
    obtain ⟨et, eb, rfl, _, _⟩ := denote_lam_inv hwf hvw he; intro x y; simp
  | forallE ty b m =>
    obtain ⟨et, eb, rfl, _, _⟩ := denote_forallE_inv hwf hvw he; intro x y; simp
  | letE ty w b =>
    obtain ⟨et, ew, eb, rfl, _, _, _⟩ := denote_letE_inv hwf hvw he
    intro x y; simp
  | lit l => rw [denote_lit_inv hwf hvw he]; intro x y; simp
  | proj n i sub =>
    obtain ⟨nm, es, rfl, _, _⟩ := denote_proj_inv hwf hvw he; intro x y; simp

/-- con-leche: ConLeche/Kernel/ExprOps.lean:915-918 getAppFn — the pure
function's fallthrough clause, as a lemma. -/
theorem getAppFn_of_not_app {e : Expr} (h : ∀ x y, e ≠ Expr.app x y) :
    Expr.getAppFn e = e := by
  cases e with
  | app f a => exact absurd rfl (h f a)
  | _ => simp [Expr.getAppFn]

/-- con-leche: ConLeche/Kernel/ExprOps.lean:920-923 getAppArgs — the same for
`getAppArgs`. -/
theorem getAppArgs_of_not_app {e : Expr} (h : ∀ x y, e ≠ Expr.app x y) :
    Expr.getAppArgs e = [] := by
  cases e with
  | app f a => exact absurd rfl (h f a)
  | _ => simp [Expr.getAppArgs]

/-- con-leche: none — a handle list's denotation, extended by one at the END.
`getAppArgs` answers `as ++ [a]` (outermost last), so this is the shape its
step lemma needs; it belongs in `Bridge/Rel.lean` beside
`denoteEList_ext`. -/
theorem denoteEList_snoc {st : EStore} {a : EIdx} {ea : Expr}
    (ha : denoteE st a = some ea) :
    ∀ (rs : List EIdx) (xs : List Expr),
      Frontend.denoteEList st rs = some xs →
        Frontend.denoteEList st (rs ++ [a]) = some (xs ++ [ea]) := by
  intro rs
  induction rs with
  | nil =>
    intro xs h
    simp only [Frontend.denoteEList, Option.some.injEq] at h
    subst h
    simp only [List.nil_append, Frontend.denoteEList, ha]
  | cons j js ih =>
    intro xs h
    simp only [Frontend.denoteEList] at h
    cases hj : denoteE st j with
    | none => rw [hj] at h; simp at h
    | some y =>
      cases hjs : Frontend.denoteEList st js with
      | none => rw [hj, hjs] at h; simp at h
      | some ys =>
        rw [hj, hjs] at h
        simp only [Option.some.injEq] at h
        subst h
        simp only [List.cons_append, Frontend.denoteEList, hj, ih ys hjs]

/-- con-leche: none — `RelEL` at a walk that peels an application and appends
the argument: `getAppArgs`' one clause.  Belongs in `Bridge/Rel.lean` group
7. -/
theorem RelEL.snoc_step {F Ff : Expr → List Expr} {st st' : EStore}
    {h f a : EIdx} {rs : List EIdx} (hwf : StoreWF st)
    (hview : st.view h = some (.app f a))
    (hdec : ∀ x y, F (.app x y) = Ff x ++ [y])
    (hf : RelEL Ff st f st' rs) (hx : Ext st st') :
    RelEL F st h st' (rs ++ [a]) := by
  intro e he
  obtain ⟨ef, ea, rfl, hdf, hda⟩ := denote_app_inv hwf hview he
  rw [hdec]
  exact denoteEList_snoc (denote_ext hda hx) rs (Ff ef) (hf ef hdf)

/-! ## 3. The application spine -/

/-- con-leche: ConLeche/Kernel/ExprOps.lean:915-918 getAppFn — **THEOREM 1**
for `getAppFn`.  Read-only: the walk peels `app` nodes and answers a handle
it was already holding, so the store is unchanged and the answer relation's
two stores coincide. -/
theorem getAppFn_spec : ∀ (fuel : Nat) (s₀ : AState) (h : EIdx),
    StateOK s₀ → (denoteE s₀.store h).isSome = true →
    ⦃fun s => s = s₀⦄ getAppFn fuel h
    ⦃fun r s' => s' = s₀ ∧ RelE Expr.getAppFn s₀.store h s₀.store r; ⊤⦄ := by
  intro fuel
  induction fuel with
  | zero =>
    intro s₀ h _ _
    vcgen [getAppFn]
    all_goals bridge_vcs [Expr.getAppFn]
  | succ fuel ih =>
    intro s₀ h hok hden
    vcgen [getAppFn, ih]
    all_goals try bridge_vcs [Expr.getAppFn]
    -- Two verification conditions remain, in goal order: the `app` arm's
    -- postcondition and the fallthrough.  The closer does not take either,
    -- because the answer relation is a `def` and `grind` will not unfold one
    -- (the finding `ExprOps/Inst1` records at its `bvar` arm), so both are
    -- one application of the matching step lemma.
    next =>
      bridge_peel
      subst_vars
      exact ⟨rfl, RelE.head_step hok.wf
        (view_of_viewApp_tag (by arm_hyp) (by arm_hyp)) (fun _ _ => rfl)
        (by arm_hyp)⟩
    next =>
      bridge_peel
      subst_vars
      exact ⟨rfl, RelE.self (fun e he =>
        getAppFn_of_not_app (not_app_of_tag hok.wf (by grind) he))⟩

/-- con-leche: ConLeche/Kernel/ExprOps.lean:920-923 getAppArgs — **THEOREM 1**
for `getAppArgs`.  Read-only, and the one twin of this group whose answer is
a LIST of handles, so `RelEL` is the relation. -/
theorem getAppArgs_spec : ∀ (fuel : Nat) (s₀ : AState) (h : EIdx),
    StateOK s₀ → (denoteE s₀.store h).isSome = true →
    ⦃fun s => s = s₀⦄ getAppArgs fuel h
    ⦃fun rs s' => s' = s₀ ∧ RelEL Expr.getAppArgs s₀.store h s₀.store rs; ⊤⦄ := by
  intro fuel
  induction fuel with
  | zero =>
    intro s₀ h _ _
    vcgen [getAppArgs]
    all_goals bridge_vcs [Expr.getAppArgs]
  | succ fuel ih =>
    intro s₀ h hok hden
    vcgen [getAppArgs, ih]
    all_goals try bridge_vcs [Expr.getAppArgs]
    next =>
      bridge_peel
      subst_vars
      exact ⟨rfl, RelEL.snoc_step hok.wf
        (view_of_viewApp_tag (by arm_hyp) (by arm_hyp)) (fun _ _ => rfl)
        (by arm_hyp) (Ext.refl _)⟩
    next =>
      bridge_peel
      subst_vars
      refine ⟨rfl, fun e he => ?_⟩
      rw [getAppArgs_of_not_app (not_app_of_tag hok.wf (by grind) he)]
      rfl

/-! ## 4. The read-only telescope walks

`vcgen` hands every arm its hypotheses already introduced, each spec's
postcondition as one conjunction.  `arm_pre` peels and substitutes them and
recovers the tag-first views in one line, so that the arm proofs below are
the `exact` and nothing else.  (Under `mvcgen` it also had to introduce the
hypotheses some arms got as arrows; `vcgen` leaves none.) -/

/-- con-leche: none — the arm preamble: `ExprOps/Inst1`'s peel and
substitution, then the tag-first arms' `view` facts. -/
macro "arm_pre" : tactic =>
  `(tactic| (bridge_peel
             subst_vars
             tf_views))

/-- con-leche: ConLeche/Kernel/ExprOps.lean:1136-1140 piResult — **THEOREM 1**
for `piResult`: the body of a syntactic `∀`-telescope.  Read-only. -/
theorem piResult_spec : ∀ (fuel : Nat) (s₀ : AState) (h : EIdx),
    StateOK s₀ → (denoteE s₀.store h).isSome = true →
    ⦃fun s => s = s₀⦄ piResult fuel h
    ⦃fun r s' => s' = s₀ ∧ RelE Expr.piResult s₀.store h s₀.store r; ⊤⦄ := by
  intro fuel
  induction fuel with
  | zero =>
    intro s₀ h _ _
    vcgen [piResult]
    all_goals bridge_vcs [Expr.piResult]
  | succ fuel ih =>
    intro s₀ h hok hden
    vcgen [piResult, ih]
    all_goals try bridge_vcs [Expr.piResult]
    -- Ten verification conditions remain: the `forallE` arm's postcondition
    -- and the nine fallthrough constructors.  `RelE` is a `def`, so the
    -- closer cannot unfold it; both shapes are one step lemma.
    -- The twin tests the tag and reads `viewBindI` since task #97-P5-Core
    -- round 4, as the Rust does: the `forallE` arm recovers the view from the
    -- binder projection, the `else` arm from the denotation and the tag.
    all_goals
      (arm_pre
       first
       | (obtain ⟨_, hv⟩ := view_forallE_of_viewBindI hok.wf (by arm_hyp)
            (by arm_hyp)
          exact ⟨rfl, RelE.body_step hok.wf hv (fun _ _ => rfl) (by arm_hyp)⟩)
       | (obtain ⟨v, hv⟩ := view_of_denote_isSome (by arm_hyp)
          exact ⟨rfl, RelE.self_of_view hok.wf hv (fun e he =>
            piResult_of_not_forallE (denoteEView_not_forallE he
              (fun ty b m hh => view_tagOf_ne hv (t := ETag.forallE) (by arm_hyp)
                (by rw [hh]; rfl))))⟩)
       | exact isSome_body_of_viewBindI hok.wf (by arm_hyp) (by arm_hyp) (by arm_hyp))

/-- con-leche: ConLeche/Kernel/ExprOps.lean:1212-1217 fvarTypeD — **THEOREM 1**
for `fvarTypeD`: the type annotation of a free-variable leaf, the expression
itself otherwise.  No fuel and no recursion at all. -/
theorem fvarTypeD_spec (s₀ : AState) (h : EIdx) (hok : StateOK s₀)
    (hden : (denoteE s₀.store h).isSome = true) :
    ⦃fun s => s = s₀⦄ fvarTypeD h
    ⦃fun r s' => s' = s₀ ∧ RelE Expr.fvarTypeD s₀.store h s₀.store r; ⊤⦄ := by
  vcgen [fvarTypeD]
  all_goals try bridge_vcs [Expr.fvarTypeD]
  all_goals
    (arm_pre
     first
     | exact ⟨rfl, RelE.fvar_ty_step hok.wf (by arm_hyp) (fun _ _ => rfl)
         (Ext.refl _)⟩
     | exact ⟨rfl, RelE.self_of_view hok.wf (by arm_hyp) (fun e he =>
         fvarTypeD_of_not_fvar (denoteEView_not_fvar he (by grind)))⟩)

/-- con-leche: ConLeche/Kernel/ExprOps.lean:1128-1134 stripPis — **THEOREM 1**
for `stripPis`: strip `k` leading `∀`s.  Structural on `k`, so the induction
is on `k` and there is no fuel; read-only, so the answer relation's two
stores coincide. -/
theorem stripPis_spec : ∀ (k : Nat) (s₀ : AState) (h : EIdx),
    StateOK s₀ → (denoteE s₀.store h).isSome = true →
    ⦃fun s => s = s₀⦄ stripPis k h
    ⦃fun r s' => s' = s₀ ∧ RelBP (Expr.stripPis k) s₀.store h s₀.store r; ⊤⦄ := by
  intro k
  induction k with
  | zero =>
    intro s₀ h hok hden
    vcgen [stripPis]
    all_goals try bridge_vcs [Expr.stripPis]
    next =>
      arm_pre
      refine ⟨rfl, fun e he => ?_⟩
      simp [denoteBP, denoteBL, he, Expr.stripPis]
  | succ k ih =>
    intro s₀ h hok hden
    vcgen [stripPis, ih]
    all_goals try bridge_vcs [Expr.stripPis]
    all_goals
      (arm_pre
       first
       | exact ⟨rfl, RelBP.cons_step (Fb := Expr.stripPis k) hok.wf
           (by arm_hyp) (by intro x y bs e hh; simp [Expr.stripPis, hh])
           (by arm_hyp)⟩
       | exact ⟨rfl, RelBP.none_step (Fb := Expr.stripPis k) hok.wf
           (by arm_hyp) (by intro x y hh; simp [Expr.stripPis, hh])
           (by arm_hyp)⟩
       -- the tag-first `else` arm (task #97-P5-Core round 4)
       | (obtain ⟨v, hv⟩ := view_of_denote_isSome (by arm_hyp)
          exact ⟨rfl, RelBP.none_of_view hok.wf hv (fun e he =>
            stripPis_of_not_forallE (denoteEView_not_forallE he
              (fun ty b m hh => view_tagOf_ne hv (t := ETag.forallE) (by arm_hyp)
                (by rw [hh]; rfl))))⟩))

/-- con-leche: ConLeche/Kernel/ExprOps.lean:1120-1126 stripLams —
**THEOREM 1** for `stripLams`, `stripPis`' λ twin. -/
theorem stripLams_spec : ∀ (k : Nat) (s₀ : AState) (h : EIdx),
    StateOK s₀ → (denoteE s₀.store h).isSome = true →
    ⦃fun s => s = s₀⦄ stripLams k h
    ⦃fun r s' => s' = s₀ ∧
        RelBP (Expr.stripLams k) s₀.store h s₀.store r; ⊤⦄ := by
  intro k
  induction k with
  | zero =>
    intro s₀ h hok hden
    vcgen [stripLams]
    all_goals try bridge_vcs [Expr.stripLams]
    next =>
      arm_pre
      refine ⟨rfl, fun e he => ?_⟩
      simp [denoteBP, denoteBL, he, Expr.stripLams]
  | succ k ih =>
    intro s₀ h hok hden
    vcgen [stripLams, ih]
    all_goals try bridge_vcs [Expr.stripLams]
    all_goals
      (arm_pre
       first
       | exact ⟨rfl, RelBP.consLam_step (Fb := Expr.stripLams k) hok.wf
           (by arm_hyp) (by intro x y bs e hh; simp [Expr.stripLams, hh])
           (by arm_hyp)⟩
       | exact ⟨rfl, RelBP.noneLam_step (Fb := Expr.stripLams k) hok.wf
           (by arm_hyp) (by intro x y hh; simp [Expr.stripLams, hh])
           (by arm_hyp)⟩
       | exact ⟨rfl, RelBP.none_of_view hok.wf (by arm_hyp) (fun e he =>
           stripLams_of_not_lam
             (denoteEView_not_lam he (by grind)))⟩)


/-! ## 5. The two argument folds, and `recRulePlain`'s comparand list

These three intern, so their postcondition carries `Ext` and the four frame
equations.  None of them takes a memo: `internE`'s own spec frames
`s'.memos = s₀.memos`, so `MemoOK` never appears. -/

/-- con-leche: ConLeche/Kernel/ExprOps.lean:925-928 mkAppN — **THEOREM 1**
for `mkAppN`: apply to a list of arguments.  Structural on the list, so the
induction is on the list and there is no fuel.  `RelEA` is `RelE` with the
argument LIST as a second subject — quantified INSIDE the relation, because
template rule 4 forbids a named `List Expr` in the precondition (the
recursive call's side goal would carry a metavariable). -/
theorem mkAppN_spec : ∀ (args : List EIdx) (s₀ : AState) (f : EIdx),
    StateOK s₀ → (denoteE s₀.store f).isSome = true →
    (Frontend.denoteEList s₀.store args).isSome = true →
    ⦃fun s => s = s₀⦄ mkAppN f args
    ⦃fun r s' => StateOK s' ∧ Ext s₀.store s'.store ∧
        BMExt s₀.store s'.store ∧ s'.memos = s₀.memos ∧
        s'.caches = s₀.caches ∧ s'.pins = s₀.pins ∧
        RelEA Expr.mkAppN s₀.store f args s'.store r; ⊤⦄ := by
  intro args
  induction args with
  | nil =>
    intro s₀ f hok hf hargs
    vcgen [mkAppN]
    all_goals try bridge_vcs [Expr.mkAppN]
    all_goals
      (arm_pre
       exact ⟨hok, Ext.refl _, BMExt.refl _, rfl, rfl, rfl,
         RelEA.nil (fun _ => rfl) (Ext.refl _)⟩)
  | cons a as ih =>
    intro s₀ f hok hf hargs
    obtain ⟨ha1, ha2⟩ := denoteEList_cons_isSome hargs
    vcgen [mkAppN, ih]
    all_goals try bridge_vcs [Expr.mkAppN]
    all_goals
      (arm_pre
       first
       | exact denote_isSome_of_intern_app (by arm_hyp) (by grind) (by grind)
       | (refine ⟨by arm_hyp, by grind only [Ext.trans],
       by grind only [BMExt.trans, BMExt.refl], by grind, by grind,
            by grind, ?_⟩
          exact RelEA.cons_step (fun _ _ _ => rfl) (by arm_hyp) (by arm_hyp)
            (by arm_hyp)))

/-- con-leche: none — a handle list's denotation, extended by one at the
FRONT.  Belongs in `Bridge/Rel.lean` beside `denoteEList_snoc`. -/
theorem denoteEList_cons_of {st : EStore} {b : EIdx} {rest : List EIdx}
    {x : Expr} {xs : List Expr} (hb : denoteE st b = some x)
    (hrest : Frontend.denoteEList st rest = some xs) :
    Frontend.denoteEList st (b :: rest) = some (x :: xs) := by
  simp only [Frontend.denoteEList, hb, hrest]

/-- con-leche: none — `internE`'s postcondition at a `bvar` node, read as a
denotation.  `denoteEView st (.bvar i)` IS `some (.bvar i)`. -/
theorem denote_bvar_of_intern {st : EStore} {b : EIdx} {i : Nat}
    (h : denoteE st b = denoteEView st (.bvar i)) :
    denoteE st b = some (.bvar i) := h

/-- con-leche: none — `mkAppNFrom`'s two clauses, spelled out.  **Unfolding
the walk by name LOOPS**: its recursion is on a cursor and not on a
structural argument, so `mvcgen [mkAppNFrom]` rewrote the recursive call
again and again until `maxRecDepth` (measured; `vcgen [mkAppNFrom]` does not
loop, measured in task #111, but leaves goals the arm proofs below do not
fit).  These two equations unfold
it exactly once, which is the shape rule this group adds to task #97s's
seven: *a walk whose measure is `termination_by` and not a constructor
pattern needs its clauses as lemmas.* -/
theorem mkAppNFrom_lt {f : EIdx} {args : Array EIdx} {i : Nat}
    (h : i < args.size) :
    mkAppNFrom f args i =
      (do let g ← internAppE f args[i]; mkAppNFrom g args (i + 1)) := by
  rw [mkAppNFrom]
  simp only [h, dite_eq_left]

/-- con-leche: none — and the exhausted clause. -/
theorem mkAppNFrom_ge {f : EIdx} {args : Array EIdx} {i : Nat}
    (h : ¬ i < args.size) : mkAppNFrom f args i = pure f := by
  rw [mkAppNFrom]
  simp only [h, reduceDIte]

/-- con-leche: none — `mkAppNFrom f args i` is `mkAppN` at the arguments from
`i` on: task #97-P6-15's push-order `Array` accumulator read with a cursor
instead of copied.  **Stated so that `mkAppN_spec` composes**: the answer
relation is the SAME `RelEA Expr.mkAppN`, at the DROPPED handle list, so a
caller that has `mkAppN`'s theorem has this one.  The recursion is on
`args.size - i`, so the induction is on that difference. -/
theorem mkAppNFrom_spec : ∀ (n : Nat) (s₀ : AState) (f : EIdx)
    (args : Array EIdx) (i : Nat), args.size - i = n → StateOK s₀ →
    (denoteE s₀.store f).isSome = true →
    (Frontend.denoteEList s₀.store (args.toList.drop i)).isSome = true →
    ⦃fun s => s = s₀⦄ mkAppNFrom f args i
    ⦃fun r s' => StateOK s' ∧ Ext s₀.store s'.store ∧
        BMExt s₀.store s'.store ∧ s'.memos = s₀.memos ∧
        s'.caches = s₀.caches ∧ s'.pins = s₀.pins ∧
        RelEA Expr.mkAppN s₀.store f (args.toList.drop i) s'.store r; ⊤⦄ := by
  intro n
  induction n with
  | zero =>
    intro s₀ f args i hn hok hf hargs
    have hd : args.toList.drop i = [] :=
      List.drop_eq_nil_of_le (by simp; omega)
    rw [hd] at hargs ⊢
    rw [mkAppNFrom_ge (by omega)]
    vcgen
    all_goals try bridge_vcs [Expr.mkAppN]
    all_goals
      (arm_pre
       exact ⟨hok, Ext.refl _, BMExt.refl _, rfl, rfl, rfl,
         RelEA.nil (fun _ => rfl) (Ext.refl _)⟩)
  | succ n ih =>
    intro s₀ f args i hn hok hf hargs
    by_cases hi : i < args.size
    · have hd : args.toList.drop i = args[i] :: args.toList.drop (i + 1) := by
        rw [List.drop_eq_getElem_cons (by simp; omega)]
        simp
      rw [hd] at hargs ⊢
      obtain ⟨ha1, ha2⟩ := denoteEList_cons_isSome hargs
      rw [mkAppNFrom_lt hi]
      vcgen [ih]
      all_goals try bridge_vcs [Expr.mkAppN]
      all_goals
        (arm_pre
         first
         | exact denote_isSome_of_intern_app (by arm_hyp) (by grind) (by grind)
         | (refine ⟨by arm_hyp, by grind only [Ext.trans],
         by grind only [BMExt.trans, BMExt.refl], by grind, by grind,
              by grind, ?_⟩
            exact RelEA.cons_step (fun _ _ _ => rfl) (by arm_hyp) (by arm_hyp)
              (by arm_hyp)))
    · have hd : args.toList.drop i = [] :=
        List.drop_eq_nil_of_le (by simp; omega)
      rw [hd] at hargs ⊢
      rw [mkAppNFrom_ge hi]
      vcgen
      all_goals try bridge_vcs [Expr.mkAppN]
      all_goals
        (arm_pre
         exact ⟨hok, Ext.refl _, BMExt.refl _, rfl, rfl, rfl,
           RelEA.nil (fun _ => rfl) (Ext.refl _)⟩)

/-- con-leche: none — `bvarRange`'s answer, as the recursion the twin itself
performs.  `recRulePlain` compares against con-leche's
`(List.range cnP).map (fun k => Expr.bvar (mI - 1 - k))`, which is this at
cursor `0` (`bvarRangeSpec_eq_range`). -/
def bvarRangeSpec (mI : Nat) : Nat → Nat → List Expr
  | 0, _ => []
  | n + 1, k => Expr.bvar (mI - 1 - k) :: bvarRangeSpec mI n (k + 1)

/-- con-leche: ConLeche/Kernel/ExprOps.lean:1229-1244 recRulePlain — **the
equation the bridge cites**: `bvarRange`'s recursion IS con-leche's literal
comparand list. -/
theorem bvarRangeSpec_eq_range (mI : Nat) :
    ∀ (n k : Nat), bvarRangeSpec mI n k =
      (List.range n).map (fun j => Expr.bvar (mI - 1 - (k + j))) := by
  intro n
  induction n with
  | zero => intro k; simp [bvarRangeSpec]
  | succ n ih =>
    intro k
    have hf : (fun j => Expr.bvar (mI - 1 - (k + 1 + j))) =
        (fun j => Expr.bvar (mI - 1 - (k + (j + 1)))) := by
      funext j; congr 1; omega
    rw [bvarRangeSpec, ih (k + 1), hf, List.range_succ_eq_map]
    simp [Function.comp_def]

/-- con-leche: none — **THEOREM 1** for `bvarRange`, the arena-only helper
that interns `recRulePlain`'s comparand list.  There is no expression SUBJECT
at all (the answer is built from `Nat`s), so no `RelEL`: what the caller
consumes is that the answered handle list DENOTES `bvarRangeSpec`, and
`bvarRangeSpec_eq_range` turns that into con-leche's `List.range` literal. -/
theorem bvarRange_spec : ∀ (n : Nat) (s₀ : AState) (mI k : Nat), StateOK s₀ →
    ⦃fun s => s = s₀⦄ bvarRange mI n k
    ⦃fun rs s' => StateOK s' ∧ Ext s₀.store s'.store ∧
        BMExt s₀.store s'.store ∧ s'.memos = s₀.memos ∧
        s'.caches = s₀.caches ∧ s'.pins = s₀.pins ∧
        Frontend.denoteEList s'.store rs = some (bvarRangeSpec mI n k); ⊤⦄ := by
  intro n
  induction n with
  | zero =>
    intro s₀ mI k hok
    vcgen [bvarRange]
    all_goals try bridge_vcs [bvarRangeSpec]
    all_goals
      (arm_pre
       exact ⟨hok, Ext.refl _, BMExt.refl _, rfl, rfl, rfl, rfl⟩)
  | succ n ih =>
    intro s₀ mI k hok
    vcgen [bvarRange, ih]
    all_goals try bridge_vcs [bvarRangeSpec]
    all_goals
      (arm_pre
       refine ⟨by arm_hyp, by grind only [Ext.trans],
       by grind only [BMExt.trans, BMExt.refl], by grind, by grind,
         by grind, ?_⟩
       rw [bvarRangeSpec]
       exact denoteEList_cons_of
         (denote_ext (denote_bvar_of_intern (by arm_hyp)) (by arm_hyp))
         (by arm_hyp))

/-! ## 7. The three walks that fold `instantiate1`

`instSpine`, `instPisAt` and `instLamsAt` call
`instantiate1Fast`, whose Theorem 1 is `ExprOps/Inst1`'s
`instantiate1Fast_spec`.  Two things about consuming it:

* it takes the substituted term `ve` EXPLICITLY, so the argument's
  denotation has to be named before `vcgen` runs — `obtain` it from the
  argument list's `isSome` and specialise the spec with a `have` (task #97s
  round 2's second trap, "specialise it at the arm's own `ea` with a
  `have`");
* it frames `caches` and `pins` but NOT `memos` (it drops its own per-call
  table, `s'.memos.inst1C = ∅`), so these four twins' postconditions frame
  `caches` and `pins` only.  That is the honest frame: a caller that needs
  `MemoOK` of another table must re-establish it, and `MemoOK.of_empty` is
  what makes that free for the dropped one. -/

/-- con-leche: ConLeche/Kernel/ExprOps.lean:1219-1227 instSpine — the CONS
clause of a fold whose step is a substitution: `instantiate1` the head
argument in, then continue with the tail at the lowered cursor. -/
theorem RelEA.inst_step {F Fr : Expr → List Expr → Expr} {gf : Expr → Expr}
    {st s1 st' : EStore} {e a e' r : EIdx} {as : List EIdx} {ea : Expr}
    (hea : denoteE st a = some ea) (hx1 : Ext st s1)
    (hg : RelE gf st e s1 e') (hrec : RelEA Fr s1 e' as st' r)
    (hdec : ∀ x ys, F x (ea :: ys) = Fr (gf x) ys) :
    RelEA F st e (a :: as) st' r := by
  intro x es hx hes
  simp only [Frontend.denoteEList] at hes
  cases has : Frontend.denoteEList st as with
  | none => rw [hea, has] at hes; simp at hes
  | some eas =>
    rw [hea, has] at hes
    obtain rfl := Option.some.inj hes
    rw [hdec]
    exact hrec (gf x) eas (hg x hx) (denoteEList_ext hx1 as eas has)

/-- con-leche: ConLeche/Kernel/ExprOps.lean:1219-1227 instSpine —
**THEOREM 1** for `instSpine`: instantiate a telescope-context expression at
an argument spine, `bvar t` first and descending.  Structural on the argument
list; the fuel is the one `instantiate1Fast` needs. -/
theorem instSpine_spec (fuel : Nat) : ∀ (as : List EIdx) (s₀ : AState)
    (t : Nat) (e : EIdx), StateOK s₀ → (denoteE s₀.store e).isSome = true →
    (Frontend.denoteEList s₀.store as).isSome = true →
    ⦃fun s => s = s₀⦄ instSpine fuel as t e
    ⦃fun r s' => StateOK s' ∧ Ext s₀.store s'.store ∧
        BMExt s₀.store s'.store ∧
        s'.caches = s₀.caches ∧ s'.pins = s₀.pins ∧
        RelEA (fun x xs => Expr.instSpine xs t x) s₀.store e as s'.store r; ⊤⦄ := by
  intro as
  induction as with
  | nil =>
    intro s₀ t e hok hden hargs
    vcgen [instSpine]
    all_goals try bridge_vcs [Expr.instSpine]
    all_goals
      (arm_pre
       exact ⟨hok, Ext.refl _, BMExt.refl _, rfl, rfl, RelEA.nil (fun _ => rfl) (Ext.refl _)⟩)
  | cons a as ih =>
    intro s₀ t e hok hden hargs
    obtain ⟨ha1, ha2⟩ := denoteEList_cons_isSome hargs
    obtain ⟨ea, hea⟩ := Option.isSome_iff_exists.mp ha1
    have hinst : ∀ (s : AState) (x : EIdx) (d : Nat), StateOK s →
        denoteE s.store a = some ea → (denoteE s.store x).isSome = true →
        ⦃fun u => u = s⦄ instantiate1Fast fuel x a d
        ⦃fun rr s' => StateOK s' ∧ Ext s.store s'.store ∧
            BMExt s.store s'.store ∧
            s'.caches = s.caches ∧ s'.pins = s.pins ∧
            s'.memos.inst1C = ∅ ∧
            Inst1At ea d s.store x s'.store rr; ⊤⦄ :=
      fun s x d hs hv hx => instantiate1Fast_spec fuel s x a d ea hs hv hx
    vcgen [instSpine, ih, hinst]
    all_goals try bridge_vcs [Expr.instSpine]
    all_goals
      (arm_pre
       first
       | (refine ⟨by arm_hyp,
            by grind only [Ext.trans],
            by grind only [BMExt.trans, BMExt.refl], by grind, by grind, ?_⟩
          exact RelEA.inst_step hea (by arm_hyp) (by arm_hyp) (by arm_hyp)
            (fun _ _ => rfl)))

/-! ## 8. `instPisAt` / `instLamsAt` — the sequential telescope peels

The domains come out PROGRESSIVELY INSTANTIATED (con-leche's own words), so
the answer is a (domain list, residual) pair: `RelEPA`.  The two differ only
in the binder they peel. -/

/-! ## The axiom check

DESIGN §8.2 asks for it on every closed theorem of the tier.  The
twins, and the four denotation transports and two exactness lemmas the
statements rest on. -/

#print axioms getAppFn_spec
#print axioms getAppArgs_spec
#print axioms mkAppN_spec
#print axioms mkAppNFrom_spec
#print axioms stripLams_spec
#print axioms stripPis_spec
#print axioms piResult_spec
#print axioms fvarTypeD_spec
#print axioms instSpine_spec
#print axioms bvarRange_spec
#print axioms bvarRangeSpec_eq_range
#print axioms denoteEView_shape
#print axioms not_app_of_tag
#print axioms denoteEList_snoc

end ConRon.Bridge.ExprOps
