/-
# `ConRon.Bridge.Rel` — the answer relations and the denotation calculus

DESIGN.md §8.2, Theorem 1.  This module is the *representation* half of the
bridge's foundation: everything that says "this handle denotes that term",
and nothing that mentions `AState`, a memo table or a Hoare triple.

It is task #97s's eight lemma groups (§"For P2b"), grown from the spike's
three-primitive store to the real `EStore`, with ONE change of shape that
task #97b measured and recommends (§"The spec layer, written and set
aside", finding 1):

> **the answer relation is GENERIC.**  `RelE f st c st' r` — "`r` in `st'`
> denotes `f` of what `c` denotes in `st`" — gives all eleven structural
> walks one set of eliminators and one set of step lemmas, where the spike's
> monomorphic `Inst1At` would need eleven copies of its 822-line layer.  The
> per-walk relations are `abbrev`s that fix `f`, so the generic lemmas still
> match syntactically and `grind` still sees a head symbol.

The exception the same finding names: a generic *step* lemma cannot be
`@[grind →]`, because its decomposition hypothesis
(`∀ x y, f (.app x y) = .app (ff x) (fa y)`) has a variable at its head and
`grind` finds no pattern.  The step lemmas below are therefore applied by
hand, which is what task #97s round 2's recipe (item 3) asks for anyway.

The groups, in order:

1. soundness — `AM.of_run`, the one step from a Hoare triple to a run;
2. transport — a denotation survives `Ext`, at all four handle kinds;
3. the ten denote INVERSIONS — the only place this tier unfolds `denoteE`;
4. the `isSome` calculus — a precondition with no `Expr` in it, so that a
   recursive call's side goal carries no metavariable (template rule 4);
5. the `isSome`-flavoured inversions — the same ten facts with the VIEW as
   the ematch pattern, which is what makes the uniform closer work;
6. the PROJECTIONS' exactness — `viewApp`, `viewBindI`/`viewBM` and their
   eleven siblings against `view`, the lemma `Arena/Store.lean` says "the
   bridge owes for each";
7. the answer relations `RelE` / `RelV` / `RelEO` / `RelEL` / `RelL` with
   their five eliminators and their generic step lemmas;
8. `ViewOK` — `intern`'s precondition, one lemma per node shape.
-/
import ConRon.Bridge.Peel
import ConLeche.Kernel.ExprOps

namespace ConRon.Bridge

set_option autoImplicit false

open ConLeche ConRon.Arena Std.Do

set_option mvcgen.warning false

/-! ## 1. Soundness: from the triple back to a run -/

/-- con-leche: none — the `WP` soundness step for `AM`.  Everything `mvcgen`
proves is a triple; Theorem 1 is stated on a *run*, and this is the four-line
bridge (`Std.Do` ships `StateM.of_wp_run_eq` and `Except.of_wp_eq`, but
nothing for `StateT σ (Except ε)`). -/
theorem AM.of_run {α : Type} {prog : AM α} {s s' : AState} {a : α}
    {P : AState → Prop} {Q : α → AState → Prop}
    (hp : P s) (h : prog.run s = .ok (a, s'))
    (hwp : ⦃fun s => ⌜P s⌝⦄ prog ⦃⇓? r s'' => ⌜Q r s''⌝⦄) : Q a s' := by
  have hs := hwp s
  simp only [WP.wp, PredTrans.apply_pushArg] at hs
  rw [h] at hs
  exact hs hp

/-! ## 2. Transport

Four facts; after them no proof in the bridge ever unfolds `denoteE`'s `Ext`
argument. -/

/-- con-leche: ConLeche/Verify/SimI.lean:244 SimAt (the `Ext` conjunct) — a
denotation survives every arena extension. -/
@[grind →] theorem denote_ext {st st' : EStore} {h : EIdx} {e : Expr}
    (hd : denoteE st h = some e) (hx : Ext st st') : denoteE st' h = some e :=
  hx.expr h e hd

/-- con-leche: ConLeche/Verify/SimI.lean:244 SimAt — the same for a NAME
handle: `Ext` carries the three nested stores too. -/
@[grind →] theorem denoteN_ext {st st' : EStore} {c : NIdx} {x : ConLeche.Name}
    (hd : denoteN st.ns c = some x) (hx : Ext st st') :
    denoteN st'.ns c = some x :=
  hx.lss.ls.ns c x hd

/-- con-leche: ConLeche/Verify/SimI.lean:244 SimAt — the same for a LEVEL
handle. -/
@[grind →] theorem denoteL_ext {st st' : EStore} {c : LIdx} {u : Level}
    (hd : denoteL st.ls c = some u) (hx : Ext st st') :
    denoteL st'.ls c = some u :=
  hx.lss.ls.lvl c u hd

/-- con-leche: ConLeche/Verify/SimI.lean:244 SimAt — the same for an interned
universe-argument LIST handle. -/
@[grind →] theorem denoteLs_ext {st st' : EStore} {c : LsIdx} {us : List Level}
    (hd : denoteLs st.lss c = some us) (hx : Ext st st') :
    denoteLs st'.lss c = some us :=
  hx.lss.lst c us hd

/-- con-leche: none — a denoting handle has a view; this is what discharges
`intern`'s `ViewOK` at a node whose children denote. -/
theorem view_isSome_of_denote {st : EStore} {h : EIdx} {e : Expr}
    (hd : denoteE st h = some e) : (st.view h).isSome = true := by
  obtain ⟨v, hv⟩ := denoteE_view hd
  rw [hv]; rfl

/-- con-leche: none — a name handle that denotes has a view. -/
@[grind →] theorem nview_isSome_of_denote {st : NStore} {c : NIdx}
    {x : ConLeche.Name} (hd : denoteN st c = some x) :
    (st.view c).isSome = true := by
  obtain ⟨w, hw⟩ := denoteN_view hd; rw [hw]; rfl

/-- con-leche: none — a level handle that denotes has a view. -/
@[grind →] theorem lview_isSome_of_denote {st : LStore} {c : LIdx} {u : Level}
    (hd : denoteL st c = some u) : (st.view c).isSome = true := by
  obtain ⟨w, hw⟩ := denoteL_view hd; rw [hw]; rfl

/-! ## 3. The denote-inversion layer

Ten lemmas, one per constructor — the *only* place this tier unfolds
`denoteE`.  Each says: given the handle's view, the denoted term has the
matching shape and the children denote.  `mvcgen` hands the view as a branch
condition, so one `obtain` per branch puts the children's denotations in
context and everything after is pure.  (con-leche's `Verify/Disc.lean` is the
same layer, site by site.) -/

/-- con-leche: none — trade the fuel for the rank once, at the top of each
inversion. -/
theorem denoteE_view_eq {st : EStore} (hwf : StoreWF st) {h : EIdx}
    {w : ENodeView} (hw : st.view h = some w) :
    denoteE st h = denoteEView st w := by
  obtain ⟨rk, hr⟩ := hwf; exact denoteE_unfold hr hw

theorem denote_bvar_inv {st : EStore} (hwf : StoreWF st) {h : EIdx} {i : Nat}
    {e : Expr} (hw : st.view h = some (.bvar i)) (he : denoteE st h = some e) :
    e = .bvar i := by
  rw [denoteE_view_eq hwf hw, denoteEView] at he; exact (Option.some.inj he).symm

theorem denote_fvar_inv {st : EStore} (hwf : StoreWF st) {h : EIdx} {k : Nat}
    {ty : EIdx} {e : Expr} (hw : st.view h = some (.fvar k ty))
    (he : denoteE st h = some e) :
    ∃ t, e = .fvar k t ∧ denoteE st ty = some t := by
  rw [denoteE_view_eq hwf hw, denoteEView, Option.map_eq_some_iff] at he
  obtain ⟨t, ht, rfl⟩ := he; exact ⟨t, rfl, ht⟩

theorem denote_sort_inv {st : EStore} (hwf : StoreWF st) {h : EIdx} {u : LIdx}
    {e : Expr} (hw : st.view h = some (.sort u)) (he : denoteE st h = some e) :
    ∃ l, e = .sort l ∧ denoteL st.ls u = some l := by
  rw [denoteE_view_eq hwf hw, denoteEView, Option.map_eq_some_iff] at he
  obtain ⟨l, hl, rfl⟩ := he; exact ⟨l, rfl, hl⟩

theorem denote_const_inv {st : EStore} (hwf : StoreWF st) {h : EIdx} {n : NIdx}
    {us : LsIdx} {e : Expr} (hw : st.view h = some (.const n us))
    (he : denoteE st h = some e) :
    ∃ nm ls, e = .const nm ls ∧ denoteN st.ns n = some nm ∧
      denoteLs st.lss us = some ls := by
  rw [denoteE_view_eq hwf hw, denoteEView, opt2_eq_some_iff] at he
  obtain ⟨nm, ls, hn, hl, rfl⟩ := he; exact ⟨nm, ls, rfl, hn, hl⟩

theorem denote_lit_inv {st : EStore} (hwf : StoreWF st) {h : EIdx}
    {l : Literal} {e : Expr} (hw : st.view h = some (.lit l))
    (he : denoteE st h = some e) : e = .lit l := by
  rw [denoteE_view_eq hwf hw, denoteEView] at he; exact (Option.some.inj he).symm

theorem denote_app_inv {st : EStore} (hwf : StoreWF st) {h f a : EIdx}
    {e : Expr} (hw : st.view h = some (.app f a))
    (he : denoteE st h = some e) :
    ∃ ef ea, e = .app ef ea ∧ denoteE st f = some ef ∧ denoteE st a = some ea := by
  rw [denoteE_view_eq hwf hw, denoteEView, opt2_eq_some_iff] at he
  obtain ⟨x, y, hx, hy, rfl⟩ := he; exact ⟨x, y, rfl, hx, hy⟩

theorem denote_lam_inv {st : EStore} (hwf : StoreWF st) {h ty b : EIdx}
    {m : BinderMeta} {e : Expr} (hw : st.view h = some (.lam ty b m))
    (he : denoteE st h = some e) :
    ∃ et eb, e = .lam et eb m ∧ denoteE st ty = some et ∧
      denoteE st b = some eb := by
  rw [denoteE_view_eq hwf hw, denoteEView, opt2_eq_some_iff] at he
  obtain ⟨x, y, hx, hy, rfl⟩ := he; exact ⟨x, y, rfl, hx, hy⟩

theorem denote_forallE_inv {st : EStore} (hwf : StoreWF st) {h ty b : EIdx}
    {m : BinderMeta} {e : Expr} (hw : st.view h = some (.forallE ty b m))
    (he : denoteE st h = some e) :
    ∃ et eb, e = .forallE et eb m ∧ denoteE st ty = some et ∧
      denoteE st b = some eb := by
  rw [denoteE_view_eq hwf hw, denoteEView, opt2_eq_some_iff] at he
  obtain ⟨x, y, hx, hy, rfl⟩ := he; exact ⟨x, y, rfl, hx, hy⟩

theorem denote_letE_inv {st : EStore} (hwf : StoreWF st) {h ty w b : EIdx}
    {e : Expr} (hw : st.view h = some (.letE ty w b))
    (he : denoteE st h = some e) :
    ∃ et ew eb, e = .letE et ew eb ∧ denoteE st ty = some et ∧
      denoteE st w = some ew ∧ denoteE st b = some eb := by
  rw [denoteE_view_eq hwf hw, denoteEView, opt3_eq_some_iff] at he
  obtain ⟨x, y, z, hx, hy, hz, rfl⟩ := he; exact ⟨x, y, z, rfl, hx, hy, hz⟩

theorem denote_proj_inv {st : EStore} (hwf : StoreWF st) {h : EIdx} {n : NIdx}
    {i : Nat} {sub : EIdx} {e : Expr} (hw : st.view h = some (.proj n i sub))
    (he : denoteE st h = some e) :
    ∃ nm es, e = .proj nm i es ∧ denoteN st.ns n = some nm ∧
      denoteE st sub = some es := by
  rw [denoteE_view_eq hwf hw, denoteEView, opt2_eq_some_iff] at he
  obtain ⟨x, y, hx, hy, rfl⟩ := he; exact ⟨x, y, rfl, hx, hy⟩

/-! ## 4. The `isSome` calculus

A (B) function's *precondition* is "this handle denotes" — `isSome`, with no
`Expr` in it, so that a recursive call's side goal carries **no
metavariable** (task #97s template rule 4).  These lemmas push `isSome` down
a node and along an extension, which is all the automation needs. -/

/-- con-leche: none — `isSome` survives an arena extension. -/
@[grind →] theorem denote_isSome_ext {st st' : EStore} {c : EIdx}
    (hs : (denoteE st c).isSome = true) (hx : Ext st st') :
    (denoteE st' c).isSome = true := by
  obtain ⟨e, he⟩ := Option.isSome_iff_exists.mp hs
  rw [denote_ext he hx]; rfl

@[grind →] theorem isSome_fvar {st : EStore} (hwf : StoreWF st) {h : EIdx}
    {k : Nat} {ty : EIdx} (hw : st.view h = some (.fvar k ty))
    (hs : (denoteE st h).isSome = true) : (denoteE st ty).isSome = true := by
  obtain ⟨e, he⟩ := Option.isSome_iff_exists.mp hs
  obtain ⟨t, _, ht⟩ := denote_fvar_inv hwf hw he
  rw [ht]; rfl

@[grind →] theorem isSome_app {st : EStore} (hwf : StoreWF st) {h f a : EIdx}
    (hw : st.view h = some (.app f a)) (hs : (denoteE st h).isSome = true) :
    (denoteE st f).isSome = true ∧ (denoteE st a).isSome = true := by
  obtain ⟨e, he⟩ := Option.isSome_iff_exists.mp hs
  obtain ⟨x, y, _, hx, hy⟩ := denote_app_inv hwf hw he
  exact ⟨by rw [hx]; rfl, by rw [hy]; rfl⟩

@[grind →] theorem isSome_lam {st : EStore} (hwf : StoreWF st) {h ty b : EIdx}
    {m : BinderMeta} (hw : st.view h = some (.lam ty b m))
    (hs : (denoteE st h).isSome = true) :
    (denoteE st ty).isSome = true ∧ (denoteE st b).isSome = true := by
  obtain ⟨e, he⟩ := Option.isSome_iff_exists.mp hs
  obtain ⟨x, y, _, hx, hy⟩ := denote_lam_inv hwf hw he
  exact ⟨by rw [hx]; rfl, by rw [hy]; rfl⟩

@[grind →] theorem isSome_forallE {st : EStore} (hwf : StoreWF st)
    {h ty b : EIdx} {m : BinderMeta} (hw : st.view h = some (.forallE ty b m))
    (hs : (denoteE st h).isSome = true) :
    (denoteE st ty).isSome = true ∧ (denoteE st b).isSome = true := by
  obtain ⟨e, he⟩ := Option.isSome_iff_exists.mp hs
  obtain ⟨x, y, _, hx, hy⟩ := denote_forallE_inv hwf hw he
  exact ⟨by rw [hx]; rfl, by rw [hy]; rfl⟩

@[grind →] theorem isSome_letE {st : EStore} (hwf : StoreWF st)
    {h ty w b : EIdx} (hw : st.view h = some (.letE ty w b))
    (hs : (denoteE st h).isSome = true) :
    (denoteE st ty).isSome = true ∧ (denoteE st w).isSome = true ∧
      (denoteE st b).isSome = true := by
  obtain ⟨e, he⟩ := Option.isSome_iff_exists.mp hs
  obtain ⟨x, y, z, _, hx, hy, hz⟩ := denote_letE_inv hwf hw he
  exact ⟨by rw [hx]; rfl, by rw [hy]; rfl, by rw [hz]; rfl⟩

@[grind →] theorem isSome_proj {st : EStore} (hwf : StoreWF st) {h : EIdx}
    {n : NIdx} {i : Nat} {sub : EIdx} (hw : st.view h = some (.proj n i sub))
    (hs : (denoteE st h).isSome = true) :
    (denoteE st sub).isSome = true := by
  obtain ⟨e, he⟩ := Option.isSome_iff_exists.mp hs
  obtain ⟨x, y, _, _, hy⟩ := denote_proj_inv hwf hw he
  rw [hy]; rfl

/-- con-leche: none — the `isSome` calculus at `eBindView`, so that a walk
whose binder clause is shared between `lam` and `forallE` (which is every
rebuilding walk since task #97-P6-16) needs no case split. -/
@[grind →] theorem isSome_eBindView {st : EStore} (hwf : StoreWF st)
    {h ty b : EIdx} {m : BinderMeta} {tg : UInt32}
    (hview : st.view h = some (eBindView tg ty b m))
    (hs : (denoteE st h).isSome = true) :
    (denoteE st ty).isSome = true ∧ (denoteE st b).isSome = true := by
  unfold eBindView at hview
  by_cases hc : (tg == ETag.lam) = true
  · rw [if_pos hc] at hview; exact isSome_lam hwf hview hs
  · simp only [Bool.not_eq_true] at hc
    rw [hc] at hview; simp only [Bool.false_eq_true, if_false] at hview
    exact isSome_forallE hwf hview hs

/-! ## 5. The `isSome`-flavoured inversions — the form `grind` can use

The same ten facts as group 3, but stated so that the *view* is the ematch
pattern and the denotation is a conclusion rather than a hypothesis.  This is
what makes the uniform closer work: `mvcgen` hands each branch its view, and
these fire on it. -/

@[grind →] theorem denote_eq_bvar {st : EStore} (hwf : StoreWF st) {h : EIdx}
    {i : Nat} (hw : st.view h = some (.bvar i))
    (hs : (denoteE st h).isSome = true) : denoteE st h = some (.bvar i) := by
  obtain ⟨e, he⟩ := Option.isSome_iff_exists.mp hs
  rw [he, denote_bvar_inv hwf hw he]

@[grind →] theorem denote_eq_fvar {st : EStore} (hwf : StoreWF st) {h : EIdx}
    {k : Nat} {ty : EIdx} (hw : st.view h = some (.fvar k ty))
    (hs : (denoteE st h).isSome = true) :
    ∃ t, denoteE st h = some (.fvar k t) ∧ denoteE st ty = some t := by
  obtain ⟨e, he⟩ := Option.isSome_iff_exists.mp hs
  obtain ⟨t, rfl, ht⟩ := denote_fvar_inv hwf hw he
  exact ⟨t, he, ht⟩

@[grind →] theorem denote_eq_sort {st : EStore} (hwf : StoreWF st) {h : EIdx}
    {u : LIdx} (hw : st.view h = some (.sort u))
    (hs : (denoteE st h).isSome = true) :
    ∃ l, denoteE st h = some (.sort l) ∧ denoteL st.ls u = some l := by
  obtain ⟨e, he⟩ := Option.isSome_iff_exists.mp hs
  obtain ⟨l, rfl, hl⟩ := denote_sort_inv hwf hw he
  exact ⟨l, he, hl⟩

@[grind →] theorem denote_eq_const {st : EStore} (hwf : StoreWF st) {h : EIdx}
    {n : NIdx} {us : LsIdx} (hw : st.view h = some (.const n us))
    (hs : (denoteE st h).isSome = true) :
    ∃ nm ls, denoteE st h = some (.const nm ls) ∧ denoteN st.ns n = some nm ∧
      denoteLs st.lss us = some ls := by
  obtain ⟨e, he⟩ := Option.isSome_iff_exists.mp hs
  obtain ⟨nm, ls, rfl, hn, hl⟩ := denote_const_inv hwf hw he
  exact ⟨nm, ls, he, hn, hl⟩

@[grind →] theorem denote_eq_lit {st : EStore} (hwf : StoreWF st) {h : EIdx}
    {l : Literal} (hw : st.view h = some (.lit l))
    (hs : (denoteE st h).isSome = true) : denoteE st h = some (.lit l) := by
  obtain ⟨e, he⟩ := Option.isSome_iff_exists.mp hs
  rw [he, denote_lit_inv hwf hw he]

@[grind →] theorem denote_eq_app {st : EStore} (hwf : StoreWF st) {h f a : EIdx}
    (hw : st.view h = some (.app f a)) (hs : (denoteE st h).isSome = true) :
    ∃ ef ea, denoteE st h = some (.app ef ea) ∧
      denoteE st f = some ef ∧ denoteE st a = some ea := by
  obtain ⟨e, he⟩ := Option.isSome_iff_exists.mp hs
  obtain ⟨x, y, rfl, hx, hy⟩ := denote_app_inv hwf hw he
  exact ⟨x, y, he, hx, hy⟩

@[grind →] theorem denote_eq_lam {st : EStore} (hwf : StoreWF st)
    {h ty b : EIdx} {m : BinderMeta} (hw : st.view h = some (.lam ty b m))
    (hs : (denoteE st h).isSome = true) :
    ∃ et eb, denoteE st h = some (.lam et eb m) ∧
      denoteE st ty = some et ∧ denoteE st b = some eb := by
  obtain ⟨e, he⟩ := Option.isSome_iff_exists.mp hs
  obtain ⟨x, y, rfl, hx, hy⟩ := denote_lam_inv hwf hw he
  exact ⟨x, y, he, hx, hy⟩

@[grind →] theorem denote_eq_forallE {st : EStore} (hwf : StoreWF st)
    {h ty b : EIdx} {m : BinderMeta} (hw : st.view h = some (.forallE ty b m))
    (hs : (denoteE st h).isSome = true) :
    ∃ et eb, denoteE st h = some (.forallE et eb m) ∧
      denoteE st ty = some et ∧ denoteE st b = some eb := by
  obtain ⟨e, he⟩ := Option.isSome_iff_exists.mp hs
  obtain ⟨x, y, rfl, hx, hy⟩ := denote_forallE_inv hwf hw he
  exact ⟨x, y, he, hx, hy⟩

@[grind →] theorem denote_eq_letE {st : EStore} (hwf : StoreWF st)
    {h ty w b : EIdx} (hw : st.view h = some (.letE ty w b))
    (hs : (denoteE st h).isSome = true) :
    ∃ et ew eb, denoteE st h = some (.letE et ew eb) ∧
      denoteE st ty = some et ∧ denoteE st w = some ew ∧
      denoteE st b = some eb := by
  obtain ⟨e, he⟩ := Option.isSome_iff_exists.mp hs
  obtain ⟨x, y, z, rfl, hx, hy, hz⟩ := denote_letE_inv hwf hw he
  exact ⟨x, y, z, he, hx, hy, hz⟩

@[grind →] theorem denote_eq_proj {st : EStore} (hwf : StoreWF st) {h : EIdx}
    {n : NIdx} {i : Nat} {sub : EIdx} (hw : st.view h = some (.proj n i sub))
    (hs : (denoteE st h).isSome = true) :
    ∃ nm es, denoteE st h = some (.proj nm i es) ∧
      denoteN st.ns n = some nm ∧ denoteE st sub = some es := by
  obtain ⟨e, he⟩ := Option.isSome_iff_exists.mp hs
  obtain ⟨x, y, rfl, hx, hy⟩ := denote_proj_inv hwf hw he
  exact ⟨x, y, he, hx, hy⟩

/-! ## 6. The projections' exactness

`Arena/Store.lean` states the obligation for each: "the exactness lemma the
bridge owes for each is `getApp t i = (t.get i).bind appParts` and its
siblings".  What the twins actually need is the *forward* direction, and with
the tag the caller has already tested off the handle word: a projection that
answers `some fields` at a handle whose tag is that constructor's fixes
`view`.

The tag hypothesis is not decoration.  `ETables.getApp` reads
`t.apps.node? i.idxNat` **without** testing the tag (that is the whole point
of a projection — the caller tested it already), so without `i.tag = ETag.app`
the conclusion is false: a `lit` handle whose index happens to be in range of
the `apps` array projects an `app`.  The twins always test first (task
#97-P6-13: "a clause that is one constructor plus a fallthrough tests the
handle's own tag word BEFORE reading the store"), so the hypothesis is always
available. -/

/-- con-leche: none — at a non-binder tag `view` IS the tier select over
`ETables.get`; the two binder arms are the ones that go through `viewBind`. -/
theorem EStore.view_eq_tier {st : EStore} {i : EIdx}
    (hb : ETag.isBind i.tag = false) :
    st.view i = (if i.isPersistent then st.pers.get i
      else if st.scratchOn then st.scr.get i else none) := by
  simp only [EStore.view, hb, Bool.false_eq_true, if_false]

/-- con-leche: none — the tier select is the same for `view` and for every
projection, so the transfer is proved ONCE over an abstract pair of tier
readers and each projection below is three lines. -/
theorem EStore.view_of_proj {st : EStore} {i : EIdx} {v : ENodeView}
    {α : Type} {p : ETables → EIdx → Option α} {x : α}
    (hb : ETag.isBind i.tag = false)
    (hstep : ∀ t : ETables, p t i = some x → t.get i = some v)
    (h : (if i.isPersistent then p st.pers i
          else if st.scratchOn then p st.scr i else none) = some x) :
    st.view i = some v := by
  simp only [EStore.view, hb, Bool.false_eq_true, if_false]
  by_cases hp : i.isPersistent = true
  · rw [if_pos hp] at h ⊢; exact hstep _ h
  · simp only [Bool.not_eq_true] at hp
    rw [hp] at h ⊢
    simp only [Bool.false_eq_true, if_false] at h ⊢
    by_cases hon : st.scratchOn = true
    · rw [if_pos hon] at h ⊢; exact hstep _ h
    · simp only [Bool.not_eq_true] at hon
      rw [hon] at h; simp at h

set_option linter.unusedSimpArgs false in
theorem ETables.get_of_getBVar {t : ETables} {i : EIdx} {k : Nat}
    (htg : i.tag = ETag.bvar) (h : t.getBVar i = some k) :
    t.get i = some (.bvar k) := by
  simp only [ETables.getBVar, Option.map_eq_some_iff] at h
  obtain ⟨r, hr, rfl⟩ := h
  simp [ETables.get, htg, hr, ETag.bvar]

set_option linter.unusedSimpArgs false in
theorem ETables.get_of_getFVar {t : ETables} {i : EIdx} {k : Nat} {ty : EIdx}
    (htg : i.tag = ETag.fvar) (hk : t.getFVarIdx i = some k)
    (hty : t.getFVarTy i = some ty) : t.get i = some (.fvar k ty) := by
  simp only [ETables.getFVarIdx, Option.map_eq_some_iff] at hk
  obtain ⟨r, hr, rfl⟩ := hk
  simp only [ETables.getFVarTy, hr, Option.map_some, Option.some.injEq] at hty
  subst hty
  simp [ETables.get, htg, hr, ETag.fvar, ETag.bvar]

set_option linter.unusedSimpArgs false in
theorem ETables.get_of_getSort {t : ETables} {i : EIdx} {u : LIdx}
    (htg : i.tag = ETag.sort) (h : t.getSort i = some u) :
    t.get i = some (.sort u) := by
  simp only [ETables.getSort, Option.map_eq_some_iff] at h
  obtain ⟨r, hr, rfl⟩ := h
  simp [ETables.get, htg, hr, ETag.sort, ETag.bvar, ETag.fvar]

set_option linter.unusedSimpArgs false in
theorem ETables.get_of_getConst {t : ETables} {i : EIdx} {n : NIdx} {us : LsIdx}
    (htg : i.tag = ETag.const) (h : t.getConst i = some (n, us)) :
    t.get i = some (.const n us) := by
  simp only [ETables.getConst, Option.map_eq_some_iff, Prod.mk.injEq] at h
  obtain ⟨r, hr, rfl, rfl⟩ := h
  simp [ETables.get, htg, hr, ETag.const, ETag.bvar, ETag.fvar, ETag.sort]

set_option linter.unusedSimpArgs false in
theorem ETables.get_of_getConstName {t : ETables} {i : EIdx} {n : NIdx}
    (htg : i.tag = ETag.const) (h : t.getConstName i = some n) :
    ∃ us, t.get i = some (.const n us) := by
  simp only [ETables.getConstName, Option.map_eq_some_iff] at h
  obtain ⟨r, hr, rfl⟩ := h
  exact ⟨r.us, by simp [ETables.get, htg, hr, ETag.const, ETag.bvar, ETag.fvar,
    ETag.sort]⟩

set_option linter.unusedSimpArgs false in
theorem ETables.get_of_getApp {t : ETables} {i : EIdx} {f a : EIdx}
    (htg : i.tag = ETag.app) (h : t.getApp i = some (f, a)) :
    t.get i = some (.app f a) := by
  simp only [ETables.getApp, Option.map_eq_some_iff, Prod.mk.injEq] at h
  obtain ⟨r, hr, rfl, rfl⟩ := h
  simp [ETables.get, htg, hr, ETag.app, ETag.bvar, ETag.fvar, ETag.sort,
    ETag.const]

set_option linter.unusedSimpArgs false in
theorem ETables.get_of_getLet {t : ETables} {i : EIdx} {ty val b : EIdx}
    (htg : i.tag = ETag.letE) (h : t.getLet i = some (ty, val, b)) :
    t.get i = some (.letE ty val b) := by
  simp only [ETables.getLet, Option.map_eq_some_iff, Prod.mk.injEq] at h
  obtain ⟨r, hr, rfl, rfl, rfl⟩ := h
  simp [ETables.get, htg, hr, ETag.letE, ETag.bvar, ETag.fvar, ETag.sort,
    ETag.const, ETag.app, ETag.isBind, ETag.lam, ETag.forallE]

set_option linter.unusedSimpArgs false in
theorem ETables.get_of_getLit {t : ETables} {i : EIdx} {l : ConLeche.Literal}
    (htg : i.tag = ETag.lit) (h : t.getLit i = some l) :
    t.get i = some (.lit l) := by
  simp only [ETables.getLit, Option.map_eq_some_iff] at h
  obtain ⟨r, hr, rfl⟩ := h
  simp [ETables.get, htg, hr, ETag.lit, ETag.bvar, ETag.fvar, ETag.sort,
    ETag.const, ETag.app, ETag.isBind, ETag.lam, ETag.forallE, ETag.letE]

set_option linter.unusedSimpArgs false in
theorem ETables.get_of_getProj {t : ETables} {i : EIdx} {n : NIdx} {k : Nat}
    {e : EIdx} (htg : i.tag = ETag.proj) (h : t.getProj i = some (n, k, e)) :
    t.get i = some (.proj n k e) := by
  simp only [ETables.getProj, Option.map_eq_some_iff, Prod.mk.injEq] at h
  obtain ⟨r, hr, rfl, rfl, rfl⟩ := h
  simp [ETables.get, htg, hr, ETag.proj, ETag.bvar, ETag.fvar, ETag.sort,
    ETag.const, ETag.app, ETag.isBind, ETag.lam, ETag.forallE, ETag.letE,
    ETag.lit]

/-! ### The eleven `EStore` projections against `view` -/

theorem view_of_viewBVar {st : EStore} {i : EIdx} {k : Nat}
    (htg : i.tag = ETag.bvar) (h : st.viewBVar i = some k) :
    st.view i = some (.bvar k) :=
  EStore.view_of_proj (by rw [htg]; decide)
    (fun _ hh => ETables.get_of_getBVar htg hh) h

/-- con-leche: none — the `fvar` node is the one whose fields are read by TWO
projections (`viewFVarIdx` and `viewFVarTy`, task #97-P6-10), so the tier
select is taken by hand here instead of through `view_of_proj`. -/
theorem view_of_viewFVar {st : EStore} {i : EIdx} {k : Nat} {ty : EIdx}
    (htg : i.tag = ETag.fvar) (hk : st.viewFVarIdx i = some k)
    (hty : st.viewFVarTy i = some ty) : st.view i = some (.fvar k ty) := by
  rw [EStore.view_eq_tier (by rw [htg]; decide)]
  simp only [EStore.viewFVarIdx, EStore.persGetFVarIdx] at hk
  simp only [EStore.viewFVarTy, EStore.persGetFVarTy] at hty
  by_cases hp : i.isPersistent = true
  · rw [if_pos hp] at hk hty ⊢; exact ETables.get_of_getFVar htg hk hty
  · simp only [Bool.not_eq_true] at hp
    rw [hp] at hk hty ⊢
    simp only [Bool.false_eq_true, if_false] at hk hty ⊢
    by_cases hon : st.scratchOn = true
    · rw [if_pos hon] at hk hty ⊢; exact ETables.get_of_getFVar htg hk hty
    · simp only [Bool.not_eq_true] at hon
      rw [hon] at hk; simp at hk

theorem view_of_viewSort {st : EStore} {i : EIdx} {u : LIdx}
    (htg : i.tag = ETag.sort) (h : st.viewSort i = some u) :
    st.view i = some (.sort u) :=
  EStore.view_of_proj (by rw [htg]; decide)
    (fun _ hh => ETables.get_of_getSort htg hh) h

theorem view_of_viewConst {st : EStore} {i : EIdx} {n : NIdx} {us : LsIdx}
    (htg : i.tag = ETag.const) (h : st.viewConst i = some (n, us)) :
    st.view i = some (.const n us) :=
  EStore.view_of_proj (by rw [htg]; decide)
    (fun _ hh => ETables.get_of_getConst htg hh) h

theorem view_of_viewApp {st : EStore} {i f a : EIdx}
    (htg : i.tag = ETag.app) (h : st.viewApp i = some (f, a)) :
    st.view i = some (.app f a) :=
  EStore.view_of_proj (by rw [htg]; decide)
    (fun _ hh => ETables.get_of_getApp htg hh) h

theorem view_of_viewLet {st : EStore} {i ty val b : EIdx}
    (htg : i.tag = ETag.letE) (h : st.viewLet i = some (ty, val, b)) :
    st.view i = some (.letE ty val b) :=
  EStore.view_of_proj (by rw [htg]; decide)
    (fun _ hh => ETables.get_of_getLet htg hh) h

theorem view_of_viewLit {st : EStore} {i : EIdx} {l : ConLeche.Literal}
    (htg : i.tag = ETag.lit) (h : st.viewLit i = some l) :
    st.view i = some (.lit l) :=
  EStore.view_of_proj (by rw [htg]; decide)
    (fun _ hh => ETables.get_of_getLit htg hh) h

theorem view_of_viewProj {st : EStore} {i : EIdx} {n : NIdx} {k : Nat}
    {e : EIdx} (htg : i.tag = ETag.proj) (h : st.viewProj i = some (n, k, e)) :
    st.view i = some (.proj n k e) :=
  EStore.view_of_proj (by rw [htg]; decide)
    (fun _ hh => ETables.get_of_getProj htg hh) h

/-- con-leche: ConLeche/Kernel/Expr.lean:94-105 BinderMeta — the BINDER
projection pair.  `view`'s two binder arms go through `viewBind`, which is
`viewBindI` and then `viewBM` at the datum handle it answers, so this is one
`simp` and no tier reasoning at all (task #97-LC finding 2: `bms` has one
constructor and `getBM` does not dispatch on the tag). -/
theorem view_of_viewBindI {st : EStore} {i ty b : EIdx} {mi : BMIdx}
    {m : ConLeche.BinderMeta} (htg : ETag.isBind i.tag = true)
    (h1 : st.viewBindI i = some (ty, b, mi)) (h2 : st.viewBM mi = some m) :
    st.view i = some (eBindView i.tag ty b m) := by
  simp only [EStore.view, htg, if_true, EStore.viewBind, h1, h2]

/-- con-leche: none — and the same at the `lam` tag, where `eBindView`
resolves. -/
theorem view_of_viewBindI_lam {st : EStore} {i ty b : EIdx} {mi : BMIdx}
    {m : ConLeche.BinderMeta} (htg : i.tag = ETag.lam)
    (h1 : st.viewBindI i = some (ty, b, mi)) (h2 : st.viewBM mi = some m) :
    st.view i = some (.lam ty b m) := by
  have hb : ETag.isBind i.tag = true := by rw [htg]; decide
  rw [view_of_viewBindI hb h1 h2, eBindView, htg]
  simp

/-- con-leche: none — and at the `forallE` tag. -/
theorem view_of_viewBindI_forallE {st : EStore} {i ty b : EIdx} {mi : BMIdx}
    {m : ConLeche.BinderMeta} (htg : i.tag = ETag.forallE)
    (h1 : st.viewBindI i = some (ty, b, mi)) (h2 : st.viewBM mi = some m) :
    st.view i = some (.forallE ty b m) := by
  have hb : ETag.isBind i.tag = true := by rw [htg]; decide
  rw [view_of_viewBindI hb h1 h2, eBindView, htg]
  simp [ETag.lam, ETag.forallE]

/-! ### The same eight, in the form the twins' tag dispatch produces

A twin tests `h.tag == ETag.C` (a `Bool`) and then takes the projection, so
what `mvcgen` hands each arm is `(i.tag == ETag.C) = true` and an equation on
`st.viewC i`.  These are group 6's lemmas at that spelling, and they are
`@[grind →]` — the projection read is their ematch pattern, so the closer
derives the `view` fact itself and the arm proofs never mention it. -/

@[grind →] theorem view_of_viewApp_tag {st : EStore} {i f a : EIdx}
    (htg : (i.tag == ETag.app) = true) (h : st.viewApp i = some (f, a)) :
    st.view i = some (.app f a) :=
  view_of_viewApp (by simpa using htg) h

@[grind →] theorem view_of_viewBVar_tag {st : EStore} {i : EIdx} {k : Nat}
    (htg : (i.tag == ETag.bvar) = true) (h : st.viewBVar i = some k) :
    st.view i = some (.bvar k) :=
  view_of_viewBVar (by simpa using htg) h

@[grind →] theorem view_of_viewSort_tag {st : EStore} {i : EIdx} {u : LIdx}
    (htg : (i.tag == ETag.sort) = true) (h : st.viewSort i = some u) :
    st.view i = some (.sort u) :=
  view_of_viewSort (by simpa using htg) h

@[grind →] theorem view_of_viewConst_tag {st : EStore} {i : EIdx} {n : NIdx}
    {us : LsIdx} (htg : (i.tag == ETag.const) = true)
    (h : st.viewConst i = some (n, us)) : st.view i = some (.const n us) :=
  view_of_viewConst (by simpa using htg) h

@[grind →] theorem view_of_viewLit_tag {st : EStore} {i : EIdx}
    {l : ConLeche.Literal} (htg : (i.tag == ETag.lit) = true)
    (h : st.viewLit i = some l) : st.view i = some (.lit l) :=
  view_of_viewLit (by simpa using htg) h

@[grind →] theorem view_of_viewLet_tag {st : EStore} {i ty val b : EIdx}
    (htg : (i.tag == ETag.letE) = true) (h : st.viewLet i = some (ty, val, b)) :
    st.view i = some (.letE ty val b) :=
  view_of_viewLet (by simpa using htg) h

@[grind →] theorem view_of_viewProj_tag {st : EStore} {i : EIdx} {n : NIdx}
    {k : Nat} {e : EIdx} (htg : (i.tag == ETag.proj) = true)
    (h : st.viewProj i = some (n, k, e)) : st.view i = some (.proj n k e) :=
  view_of_viewProj (by simpa using htg) h

@[grind →] theorem view_of_viewFVar_tag {st : EStore} {i : EIdx} {k : Nat}
    {ty : EIdx} (htg : (i.tag == ETag.fvar) = true)
    (hk : st.viewFVarIdx i = some k) (hty : st.viewFVarTy i = some ty) :
    st.view i = some (.fvar k ty) :=
  view_of_viewFVar (by simpa using htg) hk hty

/-- con-leche: ConLeche/Kernel/Expr.lean:94-105 BinderMeta — **what a
rebuilding walk gets from `viewBindI`**: the datum decodes, its tag is `0`
(task #97-LC finding 2, which `Bridge/StoreBind.lean`'s spec needs as a
hypothesis) and the handle's view is the binder view the datum spells out.
All three are `EWFAt.bmChildOK`'s own conjuncts. -/
theorem view_of_viewBindI_wf {st : EStore} (hwf : StoreWF st) {i ty b : EIdx}
    {mi : BMIdx} (htg : ETag.isBind i.tag = true)
    (h1 : st.viewBindI i = some (ty, b, mi)) :
    ∃ m, st.viewBM mi = some m ∧ mi.tag = 0 ∧
      st.view i = some (eBindView i.tag ty b m) := by
  obtain ⟨rk, hrk⟩ := hwf
  obtain ⟨hs, _, htag0⟩ := hrk.bmChildOK i ty b mi h1
  obtain ⟨m, hm⟩ := Option.isSome_iff_exists.mp hs
  exact ⟨m, hm, htag0, view_of_viewBindI htg h1 hm⟩

/-- con-leche: ConLeche/Kernel/Expr.lean:94-105 BinderMeta — the two facts
`Bridge/StoreBind.lean`'s spec asks of a datum handle, read off `EWFAt` and
keyed on the `viewBindI` read so that the closer derives them itself.  Stated
with `isSome` rather than with the datum's VALUE (template rule 4): the value
is recovered inside the consumer's postcondition, so nothing has to be
guessed. -/
@[grind →] theorem bmOK_of_viewBindI {st : EStore} (hwf : StoreWF st)
    {i ty b : EIdx} {mi : BMIdx} (h : st.viewBindI i = some (ty, b, mi)) :
    (st.viewBM mi).isSome = true ∧ mi.tag = 0 := by
  obtain ⟨rk, hrk⟩ := hwf
  obtain ⟨hs, _, htag0⟩ := hrk.bmChildOK i ty b mi h
  exact ⟨hs, htag0⟩

/-! ### The handle carries the tag of its own view

Task #97-P6-13's licence for the tag dispatch, as a lemma: "a handle in a
well-formed store carries the tag of its own view (`StoreWF`'s `intern`/`push`
clause), and the two forms differ only on a DANGLING handle, which `StoreWF`
excludes".  It needs no `StoreWF` at all — `ETables.get` dispatches on
`i.tag` FIRST, so a handle that decodes decodes to that tag's constructor —
and it is what lets a walk's catch-all `else` arm know which four
constructors it is looking at. -/

set_option linter.unusedSimpArgs false in
/-- con-leche: none — a tier that decodes a handle decodes it to the
constructor its tag names. -/
theorem ETables.tagOf_of_get {t : ETables} {i : EIdx} {v : ENodeView}
    (h : t.get i = some v) : i.tag = v.tagOf := by
  simp only [ETables.get] at h
  split at h
  · rename_i hc
    obtain ⟨r, _, rfl⟩ := Option.map_eq_some_iff.mp h
    simpa [ENodeView.tagOf] using hc
  · split at h
    · rename_i hc
      obtain ⟨r, _, rfl⟩ := Option.map_eq_some_iff.mp h
      simpa [ENodeView.tagOf] using hc
    · split at h
      · rename_i hc
        obtain ⟨r, _, rfl⟩ := Option.map_eq_some_iff.mp h
        simpa [ENodeView.tagOf] using hc
      · split at h
        · rename_i hc
          obtain ⟨r, _, rfl⟩ := Option.map_eq_some_iff.mp h
          simpa [ENodeView.tagOf] using hc
        · split at h
          · rename_i hc
            obtain ⟨r, _, rfl⟩ := Option.map_eq_some_iff.mp h
            simpa [ENodeView.tagOf] using hc
          · split at h
            · exact absurd h (by simp)
            · split at h
              · rename_i hc
                obtain ⟨r, _, rfl⟩ := Option.map_eq_some_iff.mp h
                simpa [ENodeView.tagOf] using hc
              · split at h
                · rename_i hc
                  obtain ⟨r, _, rfl⟩ := Option.map_eq_some_iff.mp h
                  simpa [ENodeView.tagOf] using hc
                · split at h
                  · rename_i hc
                    obtain ⟨r, _, rfl⟩ := Option.map_eq_some_iff.mp h
                    simpa [ENodeView.tagOf] using hc
                  · exact absurd h (by simp)

/-- con-leche: none — the same at the whole store: the two binder arms go
through `eBindView`, which builds the constructor the tag names by
definition. -/
theorem EStore.tagOf_of_view {st : EStore} {i : EIdx} {v : ENodeView}
    (h : st.view i = some v) : i.tag = v.tagOf := by
  by_cases hb : ETag.isBind i.tag = true
  · simp only [EStore.view, hb, if_true] at h
    split at h
    · exact absurd h (by simp)
    · rename_i ty b m _
      obtain rfl := Option.some.inj h
      rcases (show i.tag = ETag.lam ∨ i.tag = ETag.forallE by
          simp only [ETag.isBind, Bool.or_eq_true, beq_iff_eq] at hb; exact hb)
        with hl | hl
      · rw [eBindView, hl]; simp [ENodeView.tagOf]
      · rw [eBindView, hl]; simp [ENodeView.tagOf, ETag.lam, ETag.forallE]
  · simp only [Bool.not_eq_true] at hb
    rw [EStore.view_eq_tier hb] at h
    by_cases hp : i.isPersistent = true
    · rw [if_pos hp] at h; exact ETables.tagOf_of_get h
    · simp only [Bool.not_eq_true] at hp
      rw [hp] at h; simp only [Bool.false_eq_true, if_false] at h
      by_cases hon : st.scratchOn = true
      · rw [if_pos hon] at h; exact ETables.tagOf_of_get h
      · simp only [Bool.not_eq_true] at hon
        rw [hon] at h; simp at h

/-- con-leche: none — the catch-all arm's content, once: a handle whose tag is
none of the six the substituting walks dispatch on decodes to one of the four
LEAF constructors, and its denotation is that leaf. -/
theorem denote_leaf_of_tag {st : EStore} (hwf : StoreWF st) {h : EIdx}
    {v : ENodeView} (hview : st.view h = some v)
    (happ : ¬ (h.tag = ETag.app)) (hbind : ETag.isBind h.tag = false)
    (hbvar : ¬ (h.tag = ETag.bvar)) (hlet : ¬ (h.tag = ETag.letE))
    (hproj : ¬ (h.tag = ETag.proj)) {e : Expr} (he : denoteE st h = some e) :
    (∃ k t, e = .fvar k t) ∨ (∃ u, e = .sort u) ∨
      (∃ n us, e = .const n us) ∨ (∃ l, e = .lit l) := by
  have htag := EStore.tagOf_of_view hview
  cases v with
  | bvar i => exact absurd (htag.trans rfl) hbvar
  | fvar k t =>
    obtain ⟨t', rfl, _⟩ := denote_fvar_inv hwf hview he
    exact Or.inl ⟨k, t', rfl⟩
  | sort u =>
    obtain ⟨l, rfl, _⟩ := denote_sort_inv hwf hview he
    exact Or.inr (Or.inl ⟨l, rfl⟩)
  | const n us =>
    obtain ⟨nm, ls, rfl, _, _⟩ := denote_const_inv hwf hview he
    exact Or.inr (Or.inr (Or.inl ⟨nm, ls, rfl⟩))
  | app f a => exact absurd (htag.trans rfl) happ
  | lam ty b m =>
    rw [htag] at hbind; simp [ENodeView.tagOf, ETag.isBind] at hbind
  | forallE ty b m =>
    rw [htag] at hbind
    simp [ENodeView.tagOf, ETag.isBind, ETag.lam, ETag.forallE] at hbind
  | letE ty w b => exact absurd (htag.trans rfl) hlet
  | lit l =>
    rw [denote_lit_inv hwf hview he]
    exact Or.inr (Or.inr (Or.inr ⟨l, rfl⟩))
  | proj n i sub => exact absurd (htag.trans rfl) hproj

/-! ## 6b. `denoteEView` transports too

`internRebuilt`'s `same` branch (task #97-P6-5's upward cutoff) answers the
ORIGINAL handle, and what its caller must then show is that the original
handle denotes the rebuilt view — which is `denoteE_view_eq` plus this. -/

/-- con-leche: none — a node view's denotation survives an arena extension.
One `cases` over the ten constructors, each arm a transport of group 2. -/
theorem denoteEView_ext {st st' : EStore} {w : ENodeView} {e : Expr}
    (hd : denoteEView st w = some e) (hx : Ext st st') :
    denoteEView st' w = some e := by
  cases w with
  | bvar _ => exact hd
  | lit _ => exact hd
  | fvar k ty =>
    simp only [denoteEView, Option.map_eq_some_iff] at hd ⊢
    obtain ⟨t, ht, rfl⟩ := hd
    exact ⟨t, denote_ext ht hx, rfl⟩
  | sort u =>
    simp only [denoteEView, Option.map_eq_some_iff] at hd ⊢
    obtain ⟨l, hl, rfl⟩ := hd
    exact ⟨l, denoteL_ext hl hx, rfl⟩
  | const n us =>
    simp only [denoteEView, opt2_eq_some_iff] at hd ⊢
    obtain ⟨nm, ls, hn, hl, rfl⟩ := hd
    exact ⟨nm, ls, denoteN_ext hn hx, denoteLs_ext hl hx, rfl⟩
  | app f a =>
    simp only [denoteEView, opt2_eq_some_iff] at hd ⊢
    obtain ⟨x, y, hxx, hyy, rfl⟩ := hd
    exact ⟨x, y, denote_ext hxx hx, denote_ext hyy hx, rfl⟩
  | lam ty b m =>
    simp only [denoteEView, opt2_eq_some_iff] at hd ⊢
    obtain ⟨x, y, hxx, hyy, rfl⟩ := hd
    exact ⟨x, y, denote_ext hxx hx, denote_ext hyy hx, rfl⟩
  | forallE ty b m =>
    simp only [denoteEView, opt2_eq_some_iff] at hd ⊢
    obtain ⟨x, y, hxx, hyy, rfl⟩ := hd
    exact ⟨x, y, denote_ext hxx hx, denote_ext hyy hx, rfl⟩
  | letE ty v b =>
    simp only [denoteEView, opt3_eq_some_iff] at hd ⊢
    obtain ⟨x, y, z, hxx, hyy, hzz, rfl⟩ := hd
    exact ⟨x, y, z, denote_ext hxx hx, denote_ext hyy hx, denote_ext hzz hx, rfl⟩
  | proj n i sub =>
    simp only [denoteEView, opt2_eq_some_iff] at hd ⊢
    obtain ⟨x, y, hxx, hyy, rfl⟩ := hd
    exact ⟨x, y, denoteN_ext hxx hx, denote_ext hyy hx, rfl⟩

/-! ## 6c. The declaration layer's denotation transports

`Arena/Frontend/Readback.lean` denotes the declaration layer
(`IConstantVal`, `IRecRule`, `IIndCaps`, `IProjTable`, `IConstantInfo`) and
DESIGN §8.2's parser-tier statement is about `denoteDecl`.  Ten mechanical
transports, one per denotation, so that `IFEnvOK` and the `DeclCheck` tier
have the same `Ext` calculus the expression layer has. -/

/-- con-leche: none — a list of handles denotes through an extension. -/
theorem denoteEList_ext {st st' : EStore} (hx : Ext st st') :
    ∀ (rs : List EIdx) (xs : List Expr),
      Frontend.denoteEList st rs = some xs →
        Frontend.denoteEList st' rs = some xs := by
  intro rs
  induction rs with
  | nil => intro _ h; exact h
  | cons j js ih =>
    intro xs h
    simp only [Frontend.denoteEList] at h ⊢
    cases hj : denoteE st j with
    | none => rw [hj] at h; simp at h
    | some y =>
      cases hjs : Frontend.denoteEList st js with
      | none => rw [hj, hjs] at h; simp at h
      | some ys =>
        rw [hj, hjs] at h
        rw [denote_ext hj hx, ih ys hjs]
        exact h

theorem denoteNList_ext {st st' : NStore} (hx : NExt st st') :
    ∀ (hs : List NIdx) (xs : List ConLeche.Name),
      Frontend.denoteNList st hs = some xs →
        Frontend.denoteNList st' hs = some xs := by
  intro hs
  induction hs with
  | nil => intro _ h; exact h
  | cons a as ih =>
    intro xs h
    simp only [Frontend.denoteNList] at h ⊢
    cases ha : denoteN st a with
    | none => rw [ha] at h; simp at h
    | some y =>
      cases has : Frontend.denoteNList st as with
      | none => rw [ha, has] at h; simp at h
      | some ys => rw [ha, has] at h; rw [hx a y ha, ih ys has]; exact h

theorem denoteLList_ext {st st' : LStore} (hx : LExt st st') :
    ∀ (hs : List LIdx) (xs : List Level),
      denoteLList st hs = some xs → denoteLList st' hs = some xs := by
  intro hs
  induction hs with
  | nil => intro _ h; exact h
  | cons a as ih =>
    intro xs h
    simp only [denoteLList] at h ⊢
    cases ha : denoteL st a with
    | none => rw [ha] at h; simp at h
    | some y =>
      cases has : denoteLList st as with
      | none => rw [ha, has] at h; simp at h
      | some ys => rw [ha, has] at h; rw [hx.lvl a y ha, ih ys has]; exact h

/-- con-leche: none — `denoteNList_ext` at the whole arena's `Ext`, so that
`st.ns` and not `st.lss.ls.ns` is what the rewrite sees. -/
theorem denoteNListE_ext {st st' : EStore} (hx : Ext st st')
    (hs : List NIdx) (xs : List ConLeche.Name)
    (h : Frontend.denoteNList st.ns hs = some xs) :
    Frontend.denoteNList st'.ns hs = some xs :=
  denoteNList_ext hx.lss.ls.ns hs xs h

/-- con-leche: none — the same for a level-handle list. -/
theorem denoteLListE_ext {st st' : EStore} (hx : Ext st st')
    (hs : List LIdx) (xs : List Level)
    (h : denoteLList st.ls hs = some xs) : denoteLList st'.ls hs = some xs :=
  denoteLList_ext hx.lss.ls hs xs h

theorem denoteEArray_ext {st st' : EStore} {hs : Array EIdx} {xs : Array Expr}
    (h : Frontend.denoteEArray st hs = some xs) (hx : Ext st st') :
    Frontend.denoteEArray st' hs = some xs := by
  simp only [Frontend.denoteEArray] at h ⊢
  cases hl : Frontend.denoteEList st hs.toList with
  | none => rw [hl] at h; simp at h
  | some ys => rw [hl] at h; rw [denoteEList_ext hx _ ys hl]; exact h

theorem denoteCV_ext {st st' : EStore} {cv : IConstantVal} {c : ConstantVal}
    (h : Frontend.denoteCV st cv = some c) (hx : Ext st st') :
    Frontend.denoteCV st' cv = some c := by
  simp only [Frontend.denoteCV] at h ⊢
  cases hn : denoteN st.ns cv.name with
  | none => rw [hn] at h; simp at h
  | some n =>
    cases hl : Frontend.denoteNList st.ns cv.levelParams with
    | none => rw [hn, hl] at h; simp at h
    | some lps =>
      cases ht : denoteE st cv.type with
      | none => rw [hn, hl, ht] at h; simp at h
      | some ty =>
        rw [hn, hl, ht] at h
        rw [denoteN_ext hn hx, denoteNListE_ext hx _ lps hl,
          denote_ext ht hx]
        exact h

theorem denoteFire_ext {st st' : EStore} {f : IRecRuleFire} {g : RecRuleFire}
    (h : Frontend.denoteFire st f = some g) (hx : Ext st st') :
    Frontend.denoteFire st' f = some g := by
  cases f with
  | inert => exact h
  | plain => exact h
  | nested lvls pins =>
    simp only [Frontend.denoteFire] at h ⊢
    cases hl : denoteLList st.ls lvls with
    | none => rw [hl] at h; simp at h
    | some ls =>
      cases hp : Frontend.denoteEList st pins with
      | none => rw [hl, hp] at h; simp at h
      | some ps =>
        rw [hl, hp] at h
        rw [denoteLListE_ext hx _ ls hl, denoteEList_ext hx _ ps hp]
        exact h

theorem denoteRule_ext {st st' : EStore} {rl : IRecRule} {r : RecRule}
    (h : Frontend.denoteRule st rl = some r) (hx : Ext st st') :
    Frontend.denoteRule st' rl = some r := by
  simp only [Frontend.denoteRule] at h ⊢
  cases hc : denoteN st.ns rl.ctor with
  | none => rw [hc] at h; simp at h
  | some c =>
    cases hf : Frontend.denoteFire st rl.fire with
    | none => rw [hc, hf] at h; simp at h
    | some fr =>
      cases hr : denoteE st rl.rhs with
      | none => rw [hc, hf, hr] at h; simp at h
      | some rh =>
        rw [hc, hf, hr] at h
        rw [denoteN_ext hc hx, denoteFire_ext hf hx, denote_ext hr hx]
        exact h

theorem denoteRules_ext {st st' : EStore} (hx : Ext st st') :
    ∀ (rs : List IRecRule) (xs : List RecRule),
      Frontend.denoteRules st rs = some xs →
        Frontend.denoteRules st' rs = some xs := by
  intro rs
  induction rs with
  | nil => intro _ h; exact h
  | cons a as ih =>
    intro xs h
    simp only [Frontend.denoteRules] at h ⊢
    cases ha : Frontend.denoteRule st a with
    | none => rw [ha] at h; simp at h
    | some y =>
      cases has : Frontend.denoteRules st as with
      | none => rw [ha, has] at h; simp at h
      | some ys =>
        rw [ha, has] at h
        rw [denoteRule_ext ha hx, ih ys has]
        exact h

theorem denoteCaps_ext {st st' : EStore} {c : IIndCaps} {d : IndCaps}
    (h : Frontend.denoteCaps st c = some d) (hx : Ext st st') :
    Frontend.denoteCaps st' c = some d := by
  simp only [Frontend.denoteCaps] at h ⊢
  cases hc : denoteN st.ns c.etaCtor with
  | none => rw [hc] at h; simp at h
  | some ct => rw [hc] at h; rw [denoteN_ext hc hx]; exact h

theorem denoteProjTable_ext {st st' : EStore} {t : IProjTable} {p : ProjTable}
    (h : Frontend.denoteProjTable st t = some p) (hx : Ext st st') :
    Frontend.denoteProjTable st' t = some p := by
  simp only [Frontend.denoteProjTable] at h ⊢
  cases hs : denoteN st.ns t.structName with
  | none => rw [hs] at h; simp at h
  | some sn =>
    cases hl : Frontend.denoteNList st.ns t.levelParams with
    | none => rw [hs, hl] at h; simp at h
    | some lps =>
      cases hc : denoteN st.ns t.ctor with
      | none => rw [hs, hl, hc] at h; simp at h
      | some ct =>
        rw [hs, hl, hc] at h
        rw [denoteN_ext hs hx, denoteNListE_ext hx _ lps hl,
          denoteN_ext hc hx]
        cases hss : denoteL st.ls t.structSort with
        | none => rw [hss] at h; simp at h
        | some ss =>
          cases hb : Frontend.denoteEArray st t.bodies with
          | none => rw [hss, hb] at h; simp at h
          | some bs =>
            cases hg : denoteLList st.ls t.guards with
            | none => rw [hss, hb, hg] at h; simp at h
            | some gs =>
              rw [hss, hb, hg] at h
              rw [denoteL_ext hss hx, denoteEArray_ext hb hx,
                denoteLListE_ext hx _ gs hg]
              exact h

theorem denoteCI_ext {st st' : EStore} {ci : IConstantInfo} {c : ConstantInfo}
    (h : Frontend.denoteCI st ci = some c) (hx : Ext st st') :
    Frontend.denoteCI st' ci = some c := by
  cases ci with
  | axiomInfo v =>
    simp only [Frontend.denoteCI, Option.map_eq_some_iff] at h ⊢
    obtain ⟨cv, hcv, hc⟩ := h
    exact ⟨cv, denoteCV_ext hcv hx, hc⟩
  | ctorInfo v nP nF =>
    simp only [Frontend.denoteCI, Option.map_eq_some_iff] at h ⊢
    obtain ⟨cv, hcv, hc⟩ := h
    exact ⟨cv, denoteCV_ext hcv hx, hc⟩
  | projInfo t =>
    simp only [Frontend.denoteCI, Option.map_eq_some_iff] at h ⊢
    obtain ⟨p, hp, hc⟩ := h
    exact ⟨p, denoteProjTable_ext hp hx, hc⟩
  | defnInfo v e hint =>
    simp only [Frontend.denoteCI] at h ⊢
    cases hcv : Frontend.denoteCV st v with
    | none => rw [hcv] at h; simp at h
    | some cv =>
      cases he : denoteE st e with
      | none => rw [hcv, he] at h; simp at h
      | some x =>
        rw [hcv, he] at h
        rw [denoteCV_ext hcv hx, denote_ext he hx]; exact h
  | thmInfo v e =>
    simp only [Frontend.denoteCI] at h ⊢
    cases hcv : Frontend.denoteCV st v with
    | none => rw [hcv] at h; simp at h
    | some cv =>
      cases he : denoteE st e with
      | none => rw [hcv, he] at h; simp at h
      | some x =>
        rw [hcv, he] at h
        rw [denoteCV_ext hcv hx, denote_ext he hx]; exact h
  | indInfo v cp =>
    simp only [Frontend.denoteCI] at h ⊢
    cases hcv : Frontend.denoteCV st v with
    | none => rw [hcv] at h; simp at h
    | some cv =>
      cases hcp : Frontend.denoteCaps st cp with
      | none => rw [hcv, hcp] at h; simp at h
      | some caps =>
        rw [hcv, hcp] at h
        rw [denoteCV_ext hcv hx, denoteCaps_ext hcp hx]; exact h
  | recInfo v mI rP rs =>
    simp only [Frontend.denoteCI] at h ⊢
    cases hcv : Frontend.denoteCV st v with
    | none => rw [hcv] at h; simp at h
    | some cv =>
      cases hrs : Frontend.denoteRules st rs with
      | none => rw [hcv, hrs] at h; simp at h
      | some rules =>
        rw [hcv, hrs] at h
        rw [denoteCV_ext hcv hx, denoteRules_ext hx _ rules hrs]; exact h

/-! ## 7. The answer relations

**Generic** (task #97b, finding 1): one relation per RESULT SHAPE, not one
per walk.  The per-walk relation is an `abbrev` that fixes the pure function
(`Bridge/ExprOps/*`), so the eliminators below still ematch and `grind` still
sees a head symbol.

Four shapes cover the whole `ExprOps` tier:

* `RelE f st c st' r` — a handle in, a handle out (`instantiate1`,
  `abstract1`, `liftLooseBVars`, …);
* `RelV f st c x` — a handle in, a REPRESENTATION-FREE value out (`Bool`,
  `Nat`: `wscopedB`, `sizeB`, `piArity`, `bvarBound`).  No target store,
  because the answer names none;
* `RelEO f st c st' r` — an `Option` handle out (`instPis`, `pisToLams`);
* `RelEL f st c st' rs` — a LIST of handles out (`getAppArgs`, `bvarRange`).

The level and name shapes (`RelL`, `RelLs`) are the same at `denoteL` /
`denoteLs`. -/

/-- con-leche: ConLeche/Verify/SimI.lean:250 RelE — **the answer relation**:
"`r` in `st'` denotes `f` of what `c` denotes in `st`".

Written as a bare `∀ e, denoteE st c = some e → …` at every call site it would
cost the automation dearly: a `∀`-hypothesis has no head symbol, so `grind`
cannot ematch on it and every use has to be supplied by hand.  Behind a `def`
it has one, and the five eliminators below carry every use. -/
def RelE (f : Expr → Expr) (st : EStore) (c : EIdx) (st' : EStore) (r : EIdx) :
    Prop :=
  ∀ e, denoteE st c = some e → denoteE st' r = some (f e)

/-- con-leche: ConLeche/Verify/SimI.lean:252 RelV — the answer relation at a
representation-free result. -/
def RelV {α : Type} (f : Expr → α) (st : EStore) (c : EIdx) (x : α) : Prop :=
  ∀ e, denoteE st c = some e → x = f e

/-- con-leche: none — the denotation of an OPTIONAL handle, so that `RelEO`
has `RelE`'s shape exactly. -/
def denoteEO (st : EStore) : Option EIdx → Option (Option Expr)
  | none => some none
  | some j => (denoteE st j).map some

/-- con-leche: ConLeche/Verify/SimI.lean:250 RelE — the answer relation at an
`Option` result. -/
def RelEO (f : Expr → Option Expr) (st : EStore) (c : EIdx) (st' : EStore)
    (r : Option EIdx) : Prop :=
  ∀ e, denoteE st c = some e → denoteEO st' r = some (f e)

/-- con-leche: ConLeche/Verify/SimI.lean:250 RelE — the answer relation at a
LIST result. -/
def RelEL (f : Expr → List Expr) (st : EStore) (c : EIdx) (st' : EStore)
    (rs : List EIdx) : Prop :=
  ∀ e, denoteE st c = some e → Frontend.denoteEList st' rs = some (f e)

/-- con-leche: ConLeche/Verify/SimI.lean:254 RelL — the answer relation whose
SUBJECT is a level handle and whose answer is one too (`substLMemoAt`). -/
def RelL (f : Level → Level) (st : EStore) (c : LIdx) (st' : EStore) (r : LIdx) :
    Prop :=
  ∀ u, denoteL st.ls c = some u → denoteL st'.ls r = some (f u)

/-- con-leche: none — the same at an interned universe-argument LIST
(`substLsMemoAt`). -/
def RelLs (f : List Level → List Level) (st : EStore) (c : LsIdx) (st' : EStore)
    (r : LsIdx) : Prop :=
  ∀ us, denoteLs st.lss c = some us → denoteLs st'.lss r = some (f us)

/-! ### The five eliminators

`.apply`, `.isSome`, `.ext`, `.of_ext`, `.retarget` — the set task #97s round
1 found necessary and round 2 found explosive as `@[grind →]` *together with*
the per-site step lemmas.  They are tagged here and the arm proofs erase the
three transports with `attribute [-grind]`, exactly as `ExpAFast.lean` does;
the erasure does not travel through an import, so each arm file repeats the
line. -/

@[grind →] theorem RelE.apply {f : Expr → Expr} {st st' : EStore} {c r : EIdx}
    {e : Expr} (h : RelE f st c st' r) (he : denoteE st c = some e) :
    denoteE st' r = some (f e) := h e he

@[grind →] theorem RelE.isSome {f : Expr → Expr} {st st' : EStore} {c r : EIdx}
    (h : RelE f st c st' r) (hs : (denoteE st c).isSome = true) :
    (denoteE st' r).isSome = true := by
  obtain ⟨e, he⟩ := Option.isSome_iff_exists.mp hs
  rw [h e he]; rfl

/-- con-leche: none — the answer travels forward with the arena. -/
@[grind →] theorem RelE.ext {f : Expr → Expr} {st st' st'' : EStore} {c r : EIdx}
    (h : RelE f st c st' r) (hx : Ext st' st'') : RelE f st c st'' r :=
  fun e he => denote_ext (h e he) hx

/-- con-leche: none — and backward along an extension of the SOURCE. -/
@[grind →] theorem RelE.of_ext {f : Expr → Expr} {st st0 st' : EStore}
    {c r : EIdx} (h : RelE f st c st' r) (hx : Ext st0 st) :
    RelE f st0 c st' r :=
  fun e he => h e (denote_ext he hx)

/-- con-leche: none — **retarget the source store**.  The answer relation was
established against the store the call *started* in; the memo records it
against the store the call *ended* in.  They agree because `denoteE` is a
function and `Ext` transports the input's denotation forward.  This is the one
lemma con-leche's tree-shaped proof never needed. -/
@[grind →] theorem RelE.retarget {f : Expr → Expr} {st st0 st' : EStore}
    {c r : EIdx} (h : RelE f st c st' r) (hx : Ext st st0)
    (hs : (denoteE st c).isSome = true) : RelE f st0 c st' r := by
  intro e he
  obtain ⟨e0, he0⟩ := Option.isSome_iff_exists.mp hs
  have hh := denote_ext he0 hx
  rw [he] at hh
  rw [Option.some.inj hh]
  exact h e0 he0

/-- con-leche: none — two extensions at once.  `grind` chains `Ext.trans` and
`RelE.ext` only when it has the budget for two nested instantiations; the
composite fires in one. -/
theorem RelE.ext2 {f : Expr → Expr} {st a b c : EStore} {x r : EIdx}
    (h : RelE f st x a r) (h1 : Ext a b) (h2 : Ext b c) : RelE f st x c r :=
  (h.ext h1).ext h2

/-- con-leche: none — retarget the source and extend the target in one step:
the shape every SECOND child of a node needs, because its answer was
established against the store the first child's call left behind. -/
theorem RelE.back_ext {f : Expr → Expr} {st st1 a b : EStore} {x r : EIdx}
    (h : RelE f st1 x a r) (h0 : Ext st st1) (h1 : Ext a b) : RelE f st x b r :=
  (h.of_ext h0).ext h1

/-- con-leche: none — and with two extensions after the retarget (the third
child of `letE`). -/
theorem RelE.back_ext2 {f : Expr → Expr} {st st1 a b c : EStore} {x r : EIdx}
    (h : RelE f st1 x a r) (h0 : Ext st st1) (h1 : Ext a b) (h2 : Ext b c) :
    RelE f st x c r := ((h.of_ext h0).ext h1).ext h2

/-- con-leche: none — **the pure function may be replaced by an equal one**.
This is what lets a twin whose clause is not con-leche's clause be stated
against con-leche's function anyway: the equating lemma goes here (DESIGN
§8's "the equation the bridge cites"). -/
theorem RelE.congr {f g : Expr → Expr} {st st' : EStore} {c r : EIdx}
    (h : RelE f st c st' r) (hfg : ∀ e, f e = g e) : RelE g st c st' r :=
  fun e he => by rw [← hfg e]; exact h e he

/-- con-leche: none — a leaf arm that answers the handle it was given: the
CUTOFF shape.  Every derived-word cutoff in `ExprOps.lean` closes through
this, with `hf` supplied by con-leche's own `*_of_*_le` licence. -/
theorem RelE.self {f : Expr → Expr} {st : EStore} {c : EIdx}
    (hf : ∀ e, denoteE st c = some e → f e = e) : RelE f st c st c :=
  fun e he => by rw [hf e he]; exact he

/-- con-leche: none — the same at a store the walk has already grown. -/
theorem RelE.self_ext {f : Expr → Expr} {st st' : EStore} {c : EIdx}
    (hf : ∀ e, denoteE st c = some e → f e = e) (hx : Ext st st') :
    RelE f st c st' c := (RelE.self hf).ext hx

/-! ### The same eliminators, at the other four shapes -/

@[grind →] theorem RelV.apply {α : Type} {f : Expr → α} {st : EStore} {c : EIdx}
    {x : α} {e : Expr} (h : RelV f st c x) (he : denoteE st c = some e) :
    x = f e := h e he

@[grind →] theorem RelV.of_ext {α : Type} {f : Expr → α} {st st0 : EStore}
    {c : EIdx} {x : α} (h : RelV f st c x) (hx : Ext st0 st) :
    RelV f st0 c x :=
  fun e he => h e (denote_ext he hx)

@[grind →] theorem RelV.retarget {α : Type} {f : Expr → α} {st st0 : EStore}
    {c : EIdx} {x : α} (h : RelV f st c x) (hx : Ext st st0)
    (hs : (denoteE st c).isSome = true) : RelV f st0 c x := by
  intro e he
  obtain ⟨e0, he0⟩ := Option.isSome_iff_exists.mp hs
  have hh := denote_ext he0 hx
  rw [he] at hh
  rw [Option.some.inj hh]
  exact h e0 he0

theorem RelV.congr {α : Type} {f g : Expr → α} {st : EStore} {c : EIdx} {x : α}
    (h : RelV f st c x) (hfg : ∀ e, f e = g e) : RelV g st c x :=
  fun e he => by rw [← hfg e]; exact h e he

@[grind →] theorem RelEO.apply {f : Expr → Option Expr} {st st' : EStore}
    {c : EIdx} {r : Option EIdx} {e : Expr} (h : RelEO f st c st' r)
    (he : denoteE st c = some e) : denoteEO st' r = some (f e) := h e he

@[grind →] theorem RelEO.ext {f : Expr → Option Expr} {st st' st'' : EStore}
    {c : EIdx} {r : Option EIdx} (h : RelEO f st c st' r) (hx : Ext st' st'') :
    RelEO f st c st'' r := by
  intro e he
  have hh := h e he
  cases r with
  | none => exact hh
  | some j =>
    simp only [denoteEO, Option.map_eq_some_iff] at hh ⊢
    obtain ⟨x, hx1, hx2⟩ := hh
    exact ⟨x, denote_ext hx1 hx, hx2⟩

@[grind →] theorem RelEO.of_ext {f : Expr → Option Expr} {st st0 st' : EStore}
    {c : EIdx} {r : Option EIdx} (h : RelEO f st c st' r) (hx : Ext st0 st) :
    RelEO f st0 c st' r :=
  fun e he => h e (denote_ext he hx)

@[grind →] theorem RelEO.retarget {f : Expr → Option Expr} {st st0 st' : EStore}
    {c : EIdx} {r : Option EIdx} (h : RelEO f st c st' r) (hx : Ext st st0)
    (hs : (denoteE st c).isSome = true) : RelEO f st0 c st' r := by
  intro e he
  obtain ⟨e0, he0⟩ := Option.isSome_iff_exists.mp hs
  have hh := denote_ext he0 hx
  rw [he] at hh
  rw [Option.some.inj hh]
  exact h e0 he0

theorem RelEO.congr {f g : Expr → Option Expr} {st st' : EStore} {c : EIdx}
    {r : Option EIdx} (h : RelEO f st c st' r) (hfg : ∀ e, f e = g e) :
    RelEO g st c st' r :=
  fun e he => by rw [← hfg e]; exact h e he

@[grind →] theorem RelEL.apply {f : Expr → List Expr} {st st' : EStore}
    {c : EIdx} {rs : List EIdx} {e : Expr} (h : RelEL f st c st' rs)
    (he : denoteE st c = some e) : Frontend.denoteEList st' rs = some (f e) := h e he

@[grind →] theorem RelEL.ext {f : Expr → List Expr} {st st' st'' : EStore}
    {c : EIdx} {rs : List EIdx} (h : RelEL f st c st' rs) (hx : Ext st' st'') :
    RelEL f st c st'' rs :=
  fun e he => denoteEList_ext hx rs (f e) (h e he)

@[grind →] theorem RelEL.of_ext {f : Expr → List Expr} {st st0 st' : EStore}
    {c : EIdx} {rs : List EIdx} (h : RelEL f st c st' rs) (hx : Ext st0 st) :
    RelEL f st0 c st' rs :=
  fun e he => h e (denote_ext he hx)

@[grind →] theorem RelEL.retarget {f : Expr → List Expr} {st st0 st' : EStore}
    {c : EIdx} {rs : List EIdx} (h : RelEL f st c st' rs) (hx : Ext st st0)
    (hs : (denoteE st c).isSome = true) : RelEL f st0 c st' rs := by
  intro e he
  obtain ⟨e0, he0⟩ := Option.isSome_iff_exists.mp hs
  have hh := denote_ext he0 hx
  rw [he] at hh
  rw [Option.some.inj hh]
  exact h e0 he0

theorem RelEL.congr {f g : Expr → List Expr} {st st' : EStore} {c : EIdx}
    {rs : List EIdx} (h : RelEL f st c st' rs) (hfg : ∀ e, f e = g e) :
    RelEL g st c st' rs :=
  fun e he => by rw [← hfg e]; exact h e he

@[grind →] theorem RelL.apply {f : Level → Level} {st st' : EStore} {c r : LIdx}
    {u : Level} (h : RelL f st c st' r) (hu : denoteL st.ls c = some u) :
    denoteL st'.ls r = some (f u) := h u hu

@[grind →] theorem RelL.ext {f : Level → Level} {st st' st'' : EStore}
    {c r : LIdx} (h : RelL f st c st' r) (hx : Ext st' st'') :
    RelL f st c st'' r :=
  fun u hu => denoteL_ext (h u hu) hx

@[grind →] theorem RelL.of_ext {f : Level → Level} {st st0 st' : EStore}
    {c r : LIdx} (h : RelL f st c st' r) (hx : Ext st0 st) :
    RelL f st0 c st' r :=
  fun u hu => h u (denoteL_ext hu hx)

@[grind →] theorem RelLs.apply {f : List Level → List Level} {st st' : EStore}
    {c r : LsIdx} {us : List Level} (h : RelLs f st c st' r)
    (hu : denoteLs st.lss c = some us) : denoteLs st'.lss r = some (f us) :=
  h us hu

@[grind →] theorem RelLs.ext {f : List Level → List Level}
    {st st' st'' : EStore} {c r : LsIdx} (h : RelLs f st c st' r)
    (hx : Ext st' st'') : RelLs f st c st'' r :=
  fun u hu => denoteLs_ext (h u hu) hx

@[grind →] theorem RelLs.of_ext {f : List Level → List Level}
    {st st0 st' : EStore} {c r : LsIdx} (h : RelLs f st c st' r)
    (hx : Ext st0 st) : RelLs f st0 c st' r :=
  fun u hu => h u (denoteLs_ext hu hx)

/-! ### The universal step, and the five per-site instances

`RelE.of_view` is the whole content: the subject's view denotes what the
subject denotes (that is `denoteE_view_eq`), the answer's handle denotes what
the REBUILT view denotes (that is `intern`'s postcondition), and what is left
is a statement about `denoteEView` alone, with no store operation in it.

The five lemmas after it are `of_view` at a concrete constructor, with the
pure function's own clause supplied as a decomposition hypothesis `hdec`.  Per
task #97b finding 1 they are **not** `@[grind →]`: `hdec`'s head is a
variable, so `grind` finds no pattern.  They are applied by hand, which is
what task #97s round 2's recipe item 3 prescribes anyway. -/

theorem RelE.of_view {f : Expr → Expr} {st st' : EStore} {h r : EIdx}
    {w w' : ENodeView} (hwf : StoreWF st) (hview : st.view h = some w)
    (hr : denoteE st' r = denoteEView st' w')
    (hstep : ∀ e, denoteEView st w = some e → denoteEView st' w' = some (f e)) :
    RelE f st h st' r := by
  intro e he
  rw [denoteE_view_eq hwf hview] at he
  rw [hr]; exact hstep e he

theorem RelE.app {F Ff Fa : Expr → Expr} {st st' : EStore}
    {h f a rf ra r : EIdx} (hwf : StoreWF st)
    (hview : st.view h = some (.app f a))
    (hdec : ∀ x y, F (.app x y) = .app (Ff x) (Fa y))
    (hf : RelE Ff st f st' rf) (ha : RelE Fa st a st' ra)
    (hr : denoteE st' r = denoteEView st' (.app rf ra)) : RelE F st h st' r := by
  intro e he
  obtain ⟨ef, ea, rfl, hdf, hda⟩ := denote_app_inv hwf hview he
  rw [hr, denoteEView, hdec, hf ef hdf, ha ea hda]; rfl

theorem RelE.lam {F Ft Fb : Expr → Expr} {st st' : EStore}
    {h ty b rt rb r : EIdx} {m m' : BinderMeta} (hwf : StoreWF st)
    (hview : st.view h = some (.lam ty b m))
    (hdec : ∀ x y, F (.lam x y m) = .lam (Ft x) (Fb y) m')
    (ht : RelE Ft st ty st' rt) (hb : RelE Fb st b st' rb)
    (hr : denoteE st' r = denoteEView st' (.lam rt rb m')) :
    RelE F st h st' r := by
  intro e he
  obtain ⟨et, eb, rfl, hdt, hdb⟩ := denote_lam_inv hwf hview he
  rw [hr, denoteEView, hdec, ht et hdt, hb eb hdb]; rfl

theorem RelE.forallE {F Ft Fb : Expr → Expr} {st st' : EStore}
    {h ty b rt rb r : EIdx} {m m' : BinderMeta} (hwf : StoreWF st)
    (hview : st.view h = some (.forallE ty b m))
    (hdec : ∀ x y, F (.forallE x y m) = .forallE (Ft x) (Fb y) m')
    (ht : RelE Ft st ty st' rt) (hb : RelE Fb st b st' rb)
    (hr : denoteE st' r = denoteEView st' (.forallE rt rb m')) :
    RelE F st h st' r := by
  intro e he
  obtain ⟨et, eb, rfl, hdt, hdb⟩ := denote_forallE_inv hwf hview he
  rw [hr, denoteEView, hdec, ht et hdt, hb eb hdb]; rfl

theorem RelE.letE {F Ft Fv Fb : Expr → Expr} {st st' : EStore}
    {h ty v b rt rv rb r : EIdx} (hwf : StoreWF st)
    (hview : st.view h = some (.letE ty v b))
    (hdec : ∀ x y z, F (.letE x y z) = .letE (Ft x) (Fv y) (Fb z))
    (ht : RelE Ft st ty st' rt) (hv : RelE Fv st v st' rv)
    (hb : RelE Fb st b st' rb)
    (hr : denoteE st' r = denoteEView st' (.letE rt rv rb)) :
    RelE F st h st' r := by
  intro e he
  obtain ⟨et, ev, eb, rfl, hdt, hdv, hdb⟩ := denote_letE_inv hwf hview he
  rw [hr, denoteEView, hdec, ht et hdt, hv ev hdv, hb eb hdb]; rfl

theorem RelE.proj {F Fs : Expr → Expr} {st st' : EStore} {h sub rs r : EIdx}
    {n n' : NIdx} {i : Nat} {nm nm' : ConLeche.Name} (hwf : StoreWF st)
    (hview : st.view h = some (.proj n i sub))
    (hdec : ∀ x, F (.proj nm i x) = .proj nm' i (Fs x))
    (hs : RelE Fs st sub st' rs)
    (hn0 : denoteN st.ns n = some nm) (hn' : denoteN st'.ns n' = some nm')
    (hr : denoteE st' r = denoteEView st' (.proj n' i rs)) :
    RelE F st h st' r := by
  intro e he
  obtain ⟨nm2, es, rfl, hdn, hds⟩ := denote_proj_inv hwf hview he
  rw [hn0] at hdn
  obtain rfl := Option.some.inj hdn
  rw [hr, denoteEView, hdec, hs es hds, hn']; rfl

/-! ## 8. `ViewOK` — `intern`'s precondition

One lemma per node shape the twins build.  Each is "the children denote, hence
they have views". -/

/-- con-leche: none — a handle that denotes has a view (the `isSome`
spelling, so nothing has to be guessed). -/
theorem view_isSome {st : EStore} {c : EIdx}
    (hs : (denoteE st c).isSome = true) : (st.view c).isSome = true := by
  obtain ⟨e, he⟩ := Option.isSome_iff_exists.mp hs
  exact view_isSome_of_denote he

theorem viewOK_bvar {st : EStore} {i : Nat} : st.ViewOK (.bvar i) :=
  ⟨by simp [ENodeView.echildren], by simp [ENodeView.nchildren],
   by simp [ENodeView.lchildren], by simp [ENodeView.lschildren]⟩

theorem viewOK_lit {st : EStore} {l : ConLeche.Literal} : st.ViewOK (.lit l) :=
  ⟨by simp [ENodeView.echildren], by simp [ENodeView.nchildren],
   by simp [ENodeView.lchildren], by simp [ENodeView.lschildren]⟩

theorem viewOK_fvar {st : EStore} {k : Nat} {ty : EIdx}
    (ht : (denoteE st ty).isSome = true) : st.ViewOK (.fvar k ty) :=
  ⟨by intro c hc; simp [ENodeView.echildren] at hc; subst hc
      exact view_isSome ht,
   by simp [ENodeView.nchildren], by simp [ENodeView.lchildren],
   by simp [ENodeView.lschildren]⟩

theorem viewOK_sort {st : EStore} {u : LIdx}
    (hu : (st.ls.view u).isSome = true) : st.ViewOK (.sort u) :=
  ⟨by simp [ENodeView.echildren], by simp [ENodeView.nchildren],
   by intro c hc; simp [ENodeView.lchildren] at hc; subst hc; exact hu,
   by simp [ENodeView.lschildren]⟩

theorem viewOK_const {st : EStore} {n : NIdx} {us : LsIdx}
    (hn : (st.ns.view n).isSome = true) (hu : (st.lss.view us).isSome = true) :
    st.ViewOK (.const n us) :=
  ⟨by simp [ENodeView.echildren],
   by intro c hc; simp [ENodeView.nchildren] at hc; subst hc; exact hn,
   by simp [ENodeView.lchildren],
   by intro c hc; simp [ENodeView.lschildren] at hc; subst hc; exact hu⟩

theorem viewOK_app {st : EStore} {f a : EIdx}
    (hf : (denoteE st f).isSome = true) (ha : (denoteE st a).isSome = true) :
    st.ViewOK (.app f a) :=
  ⟨by intro c hc; simp [ENodeView.echildren] at hc
      rcases hc with rfl | rfl
      · exact view_isSome hf
      · exact view_isSome ha,
   by simp [ENodeView.nchildren], by simp [ENodeView.lchildren],
   by simp [ENodeView.lschildren]⟩

theorem viewOK_lam {st : EStore} {ty b : EIdx} {m : BinderMeta}
    (ht : (denoteE st ty).isSome = true) (hb : (denoteE st b).isSome = true) :
    st.ViewOK (.lam ty b m) :=
  ⟨by intro c hc; simp [ENodeView.echildren] at hc
      rcases hc with rfl | rfl
      · exact view_isSome ht
      · exact view_isSome hb,
   by simp [ENodeView.nchildren], by simp [ENodeView.lchildren],
   by simp [ENodeView.lschildren]⟩

theorem viewOK_forallE {st : EStore} {ty b : EIdx} {m : BinderMeta}
    (ht : (denoteE st ty).isSome = true) (hb : (denoteE st b).isSome = true) :
    st.ViewOK (.forallE ty b m) :=
  ⟨by intro c hc; simp [ENodeView.echildren] at hc
      rcases hc with rfl | rfl
      · exact view_isSome ht
      · exact view_isSome hb,
   by simp [ENodeView.nchildren], by simp [ENodeView.lchildren],
   by simp [ENodeView.lschildren]⟩

theorem viewOK_letE {st : EStore} {ty v b : EIdx}
    (ht : (denoteE st ty).isSome = true) (hv : (denoteE st v).isSome = true)
    (hb : (denoteE st b).isSome = true) : st.ViewOK (.letE ty v b) :=
  ⟨by intro c hc; simp [ENodeView.echildren] at hc
      rcases hc with rfl | rfl | rfl
      · exact view_isSome ht
      · exact view_isSome hv
      · exact view_isSome hb,
   by simp [ENodeView.nchildren], by simp [ENodeView.lchildren],
   by simp [ENodeView.lschildren]⟩

theorem viewOK_proj {st : EStore} {n : NIdx} {i : Nat} {sub : EIdx}
    (hn : (st.ns.view n).isSome = true) (hs : (denoteE st sub).isSome = true) :
    st.ViewOK (.proj n i sub) :=
  ⟨by intro c hc; simp [ENodeView.echildren] at hc; subst hc
      exact view_isSome hs,
   by intro c hc; simp [ENodeView.nchildren] at hc; subst hc; exact hn,
   by simp [ENodeView.lchildren], by simp [ENodeView.lschildren]⟩

/-- con-leche: none — `eBindView`'s `ViewOK`, so that the binder arms of the
rebuilding walks (which carry the tag rather than the constructor) need no
case split. -/
theorem viewOK_eBindView {st : EStore} {tag : UInt32} {ty b : EIdx}
    {m : BinderMeta} (ht : (denoteE st ty).isSome = true)
    (hb : (denoteE st b).isSome = true) : st.ViewOK (eBindView tag ty b m) := by
  unfold eBindView
  by_cases hc : (tag == ETag.lam) = true
  · rw [if_pos hc]; exact viewOK_lam ht hb
  · simp only [Bool.not_eq_true] at hc
    rw [hc]; simp only [Bool.false_eq_true, if_false]
    exact viewOK_forallE ht hb

end ConRon.Bridge
