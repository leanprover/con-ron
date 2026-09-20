/-
# `ConRon.Arena.Specs` — the `@[spec]` / `@[grind]` layer of (B)

Task #97s's deliverable for P2b, grown once for the real `EStore`: "one spec
theorem per store primitive, in one shape, so that `mvcgen` can walk a (B)
body without any store reasoning appearing in the proof text", and the eight
lemma groups the spike's `Spike/Specs.lean` priced at 822 lines for a
three-primitive store with one memo.

## The template (task #97s, rules 1-7)

```lean
@[spec] theorem f_spec (s₀ : AState) (args…) (pre…) :
    ⦃fun s => ⌜s = s₀⌝⦄ f args ⦃⇓? r s' => ⌜Post s₀ r s'⌝⦄
```

1. the precondition is `s = s₀` **and nothing else** — every real
   precondition is an ordinary hypothesis, so `mspec` turns it into a side
   goal instead of an entailment;
2. `⇓?` (partial correctness), never `⇓`: a (B) function may fail and
   Theorem 1 claims nothing then (con-leche's `SimAt`);
3. the postcondition names `s₀`, the only way to state `Ext s₀.store s'.store`
   inside a triple;
4. "the subject denotes" is an `isSome`, never a named `Expr`: with a named
   `Expr` every recursive call leaves `denoteE s.store f = some ?e`, a
   metavariable `grind` cannot invent;
5. the answer is a **named relation** with eliminators, never a bare `∀`: a
   `∀`-hypothesis has no head symbol to ematch on;
6. a memo insert's spec states that the INVARIANT is preserved, not that the
   table grew;
7. one named failure primitive (`fail`), because a bare `throw` leaves
   `mvcgen` with universe metavariables.

## What is new here, against the spike

**The answer relation is generic in the pure function.**  The spike had one
`Inst1At` for one subject; P2b has eleven structural walks, and writing
eleven copies of the relation, its five eliminators and its six step lemmas
would be eleven times 800 lines.  `RelAt f st c st' r` — "`r` in `st'`
denotes `f` of what `c` denotes in `st`" — is that relation once, and every
step lemma takes the pure function's own **decomposition equation**
(`∀ x y, f (.app x y) = .app (ff x) (fa y)`) as a hypothesis.  That equation
is `rfl` for every twin in this module, which is why the per-twin cost drops
to the arm specs.

The same generalisation carries the memo: `MemoOK f tbl st` is the invariant
of any cursor-keyed handle memo, `MemoNOK` of the two `Nat`-valued ones.
-/
import ConRon.Arena.Peel
import ConLeche.Kernel.ExprOps
import Std.Tactic.Do

namespace ConRon.Arena

open ConLeche Std.Do

set_option mvcgen.warning false

/-! ## Group 1 — soundness: from the triple back to a run -/

/-- con-leche: none — the `WP` soundness step for `AM`.  Everything `mvcgen`
proves is a triple; Theorem 1 is stated on a *run*, and this is the bridge
(`Std.Do` ships `StateM.of_wp_run_eq` and `Except.of_wp_eq`, but nothing for
`StateT σ (Except ε)`). -/
theorem AM.of_run {α : Type} {prog : AM α} {s s' : AState} {a : α}
    {P : AState → Prop} {Q : α → AState → Prop}
    (hp : P s) (h : prog.run s = .ok (a, s'))
    (hwp : ⦃fun s => ⌜P s⌝⦄ prog ⦃⇓? r s'' => ⌜Q r s''⌝⦄) : Q a s' := by
  have hs := hwp s
  simp only [WP.wp, PredTrans.apply_pushArg] at hs
  rw [h] at hs
  exact hs hp

/-! ## Group 2 — transport

Four facts; after them no proof below ever unfolds `denote*`. -/

/-- con-leche: ConLeche/Verify/SimI.lean:244 SimAt — a denotation survives
every arena extension.  This is `Ext.expr` under the name the proofs use. -/
@[grind →] theorem denote_ext {st st' : EStore} {h : EIdx} {e : Expr}
    (hd : denoteE st h = some e) (hx : Ext st st') : denoteE st' h = some e :=
  hx.expr h e hd

/-- con-leche: ConLeche/Verify/SimI.lean:244 SimAt — the same for a NAME
handle: `Ext` carries the three nested stores too. -/
@[grind →] theorem denoteN_ext {st st' : EStore} {c : NIdx} {x : ConLeche.Name}
    (hd : denoteN st.ns c = some x) (hx : Ext st st') : denoteN st'.ns c = some x :=
  hx.lss.ls.ns c x hd

/-- con-leche: ConLeche/Verify/SimI.lean:244 SimAt — and for a LEVEL
handle. -/
@[grind →] theorem denoteL_ext {st st' : EStore} {c : LIdx} {u : Level}
    (hd : denoteL st.ls c = some u) (hx : Ext st st') : denoteL st'.ls c = some u :=
  hx.lss.ls.lvl c u hd

/-- con-leche: ConLeche/Verify/SimI.lean:244 SimAt — and for a
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

/-! ## Group 3 — the denote-inversion layer

Ten lemmas, one per constructor: the *only* place this module unfolds
`denoteE`.  `mvcgen` hands the view as a branch condition, so one of these
per branch puts the children's denotations in context and everything after is
pure. -/

/-- con-leche: none — trade the fuel for the rank once, at the top of each
inversion. -/
theorem denoteE_view_eq {st : EStore} (hwf : StoreWF st) {h : EIdx}
    {w : ENodeView} (hw : st.view h = some w) : denoteE st h = denoteEView st w := by
  obtain ⟨rk, hr⟩ := hwf; exact denoteE_unfold hr hw

/-- con-leche: none — the `bvar` inversion. -/
theorem denote_bvar_inv {st : EStore} (hwf : StoreWF st) {h : EIdx} {i : Nat}
    {e : Expr} (hw : st.view h = some (.bvar i)) (he : denoteE st h = some e) :
    e = .bvar i := by
  rw [denoteE_view_eq hwf hw, denoteEView] at he; exact (Option.some.inj he).symm

/-- con-leche: none — the `fvar` inversion. -/
theorem denote_fvar_inv {st : EStore} (hwf : StoreWF st) {h : EIdx} {k : Nat}
    {ty : EIdx} {e : Expr} (hw : st.view h = some (.fvar k ty))
    (he : denoteE st h = some e) : ∃ t, e = .fvar k t ∧ denoteE st ty = some t := by
  rw [denoteE_view_eq hwf hw, denoteEView, Option.map_eq_some_iff] at he
  obtain ⟨t, ht, rfl⟩ := he; exact ⟨t, rfl, ht⟩

/-- con-leche: none — the `sort` inversion; the level is carried, because
`instLPGo` rebuilds it. -/
theorem denote_sort_inv {st : EStore} (hwf : StoreWF st) {h : EIdx} {u : LIdx}
    {e : Expr} (hw : st.view h = some (.sort u)) (he : denoteE st h = some e) :
    ∃ l, e = .sort l ∧ denoteL st.ls u = some l := by
  rw [denoteE_view_eq hwf hw, denoteEView, Option.map_eq_some_iff] at he
  obtain ⟨l, hl, rfl⟩ := he; exact ⟨l, rfl, hl⟩

/-- con-leche: none — the `const` inversion. -/
theorem denote_const_inv {st : EStore} (hwf : StoreWF st) {h : EIdx} {n : NIdx}
    {us : LsIdx} {e : Expr} (hw : st.view h = some (.const n us))
    (he : denoteE st h = some e) :
    ∃ nm ls, e = .const nm ls ∧ denoteN st.ns n = some nm ∧
      denoteLs st.lss us = some ls := by
  rw [denoteE_view_eq hwf hw, denoteEView, opt2_eq_some_iff] at he
  obtain ⟨nm, ls, hn, hl, rfl⟩ := he; exact ⟨nm, ls, rfl, hn, hl⟩

/-- con-leche: none — the `lit` inversion. -/
theorem denote_lit_inv {st : EStore} (hwf : StoreWF st) {h : EIdx} {l : Literal}
    {e : Expr} (hw : st.view h = some (.lit l)) (he : denoteE st h = some e) :
    e = .lit l := by
  rw [denoteE_view_eq hwf hw, denoteEView] at he; exact (Option.some.inj he).symm

/-- con-leche: none — the `app` inversion. -/
theorem denote_app_inv {st : EStore} (hwf : StoreWF st) {h f a : EIdx} {e : Expr}
    (hw : st.view h = some (.app f a)) (he : denoteE st h = some e) :
    ∃ ef ea, e = .app ef ea ∧ denoteE st f = some ef ∧ denoteE st a = some ea := by
  rw [denoteE_view_eq hwf hw, denoteEView, opt2_eq_some_iff] at he
  obtain ⟨x, y, hx, hy, rfl⟩ := he; exact ⟨x, y, rfl, hx, hy⟩

/-- con-leche: none — the `lam` inversion. -/
theorem denote_lam_inv {st : EStore} (hwf : StoreWF st) {h ty b : EIdx}
    {m : BinderMeta} {e : Expr} (hw : st.view h = some (.lam ty b m))
    (he : denoteE st h = some e) :
    ∃ et eb, e = .lam et eb m ∧ denoteE st ty = some et ∧ denoteE st b = some eb := by
  rw [denoteE_view_eq hwf hw, denoteEView, opt2_eq_some_iff] at he
  obtain ⟨x, y, hx, hy, rfl⟩ := he; exact ⟨x, y, rfl, hx, hy⟩

/-- con-leche: none — the `forallE` inversion. -/
theorem denote_forallE_inv {st : EStore} (hwf : StoreWF st) {h ty b : EIdx}
    {m : BinderMeta} {e : Expr} (hw : st.view h = some (.forallE ty b m))
    (he : denoteE st h = some e) :
    ∃ et eb, e = .forallE et eb m ∧ denoteE st ty = some et ∧
      denoteE st b = some eb := by
  rw [denoteE_view_eq hwf hw, denoteEView, opt2_eq_some_iff] at he
  obtain ⟨x, y, hx, hy, rfl⟩ := he; exact ⟨x, y, rfl, hx, hy⟩

/-- con-leche: none — the `letE` inversion. -/
theorem denote_letE_inv {st : EStore} (hwf : StoreWF st) {h ty w b : EIdx}
    {e : Expr} (hw : st.view h = some (.letE ty w b)) (he : denoteE st h = some e) :
    ∃ et ew eb, e = .letE et ew eb ∧ denoteE st ty = some et ∧
      denoteE st w = some ew ∧ denoteE st b = some eb := by
  rw [denoteE_view_eq hwf hw, denoteEView, opt3_eq_some_iff] at he
  obtain ⟨x, y, z, hx, hy, hz, rfl⟩ := he; exact ⟨x, y, z, rfl, hx, hy, hz⟩

/-- con-leche: none — the `proj` inversion. -/
theorem denote_proj_inv {st : EStore} (hwf : StoreWF st) {h : EIdx} {n : NIdx}
    {i : Nat} {sub : EIdx} {e : Expr} (hw : st.view h = some (.proj n i sub))
    (he : denoteE st h = some e) :
    ∃ nm es, e = .proj nm i es ∧ denoteN st.ns n = some nm ∧
      denoteE st sub = some es := by
  rw [denoteE_view_eq hwf hw, denoteEView, opt2_eq_some_iff] at he
  obtain ⟨x, y, hx, hy, rfl⟩ := he; exact ⟨x, y, rfl, hx, hy⟩

/-! ## Group 4 — the `isSome` calculus

A twin's *precondition* is "this handle denotes" — `isSome`, with no `Expr`
in it, so that a recursive call's side goal carries no metavariable
(rule 4). -/

/-- con-leche: none — `isSome` survives an arena extension. -/
@[grind →] theorem denote_isSome_ext {st st' : EStore} {c : EIdx}
    (hs : (denoteE st c).isSome = true) (hx : Ext st st') :
    (denoteE st' c).isSome = true := by
  obtain ⟨e, he⟩ := Option.isSome_iff_exists.mp hs
  rw [denote_ext he hx]; rfl

/-- con-leche: none — an `fvar`'s annotation denotes. -/
@[grind →] theorem isSome_fvar {st : EStore} (hwf : StoreWF st) {h : EIdx}
    {k : Nat} {ty : EIdx} (hw : st.view h = some (.fvar k ty))
    (hs : (denoteE st h).isSome = true) : (denoteE st ty).isSome = true := by
  obtain ⟨e, he⟩ := Option.isSome_iff_exists.mp hs
  obtain ⟨t, _, ht⟩ := denote_fvar_inv hwf hw he
  rw [ht]; rfl

/-- con-leche: none — an application's children denote. -/
@[grind →] theorem isSome_app {st : EStore} (hwf : StoreWF st) {h f a : EIdx}
    (hw : st.view h = some (.app f a)) (hs : (denoteE st h).isSome = true) :
    (denoteE st f).isSome = true ∧ (denoteE st a).isSome = true := by
  obtain ⟨e, he⟩ := Option.isSome_iff_exists.mp hs
  obtain ⟨x, y, _, hx, hy⟩ := denote_app_inv hwf hw he
  exact ⟨by rw [hx]; rfl, by rw [hy]; rfl⟩

/-- con-leche: none — a λ's children denote. -/
@[grind →] theorem isSome_lam {st : EStore} (hwf : StoreWF st) {h ty b : EIdx}
    {m : BinderMeta} (hw : st.view h = some (.lam ty b m))
    (hs : (denoteE st h).isSome = true) :
    (denoteE st ty).isSome = true ∧ (denoteE st b).isSome = true := by
  obtain ⟨e, he⟩ := Option.isSome_iff_exists.mp hs
  obtain ⟨x, y, _, hx, hy⟩ := denote_lam_inv hwf hw he
  exact ⟨by rw [hx]; rfl, by rw [hy]; rfl⟩

/-- con-leche: none — a ∀'s children denote. -/
@[grind →] theorem isSome_forallE {st : EStore} (hwf : StoreWF st) {h ty b : EIdx}
    {m : BinderMeta} (hw : st.view h = some (.forallE ty b m))
    (hs : (denoteE st h).isSome = true) :
    (denoteE st ty).isSome = true ∧ (denoteE st b).isSome = true := by
  obtain ⟨e, he⟩ := Option.isSome_iff_exists.mp hs
  obtain ⟨x, y, _, hx, hy⟩ := denote_forallE_inv hwf hw he
  exact ⟨by rw [hx]; rfl, by rw [hy]; rfl⟩

/-- con-leche: none — a `let`'s three children denote. -/
@[grind →] theorem isSome_letE {st : EStore} (hwf : StoreWF st) {h ty w b : EIdx}
    (hw : st.view h = some (.letE ty w b)) (hs : (denoteE st h).isSome = true) :
    (denoteE st ty).isSome = true ∧ (denoteE st w).isSome = true ∧
      (denoteE st b).isSome = true := by
  obtain ⟨e, he⟩ := Option.isSome_iff_exists.mp hs
  obtain ⟨x, y, z, _, hx, hy, hz⟩ := denote_letE_inv hwf hw he
  exact ⟨by rw [hx]; rfl, by rw [hy]; rfl, by rw [hz]; rfl⟩

/-- con-leche: none — a projection's subject denotes. -/
@[grind →] theorem isSome_proj {st : EStore} (hwf : StoreWF st) {h : EIdx}
    {n : NIdx} {i : Nat} {sub : EIdx} (hw : st.view h = some (.proj n i sub))
    (hs : (denoteE st h).isSome = true) : (denoteE st sub).isSome = true := by
  obtain ⟨e, he⟩ := Option.isSome_iff_exists.mp hs
  obtain ⟨x, y, _, _, hy⟩ := denote_proj_inv hwf hw he
  rw [hy]; rfl

/-! ## Group 5 — the `isSome`-flavoured inversions

The same ten facts, stated so that the *view* is the ematch pattern and the
denotation is a conclusion rather than a hypothesis.  This is what makes the
uniform closer work: `mvcgen` hands each branch its view, and these fire on
it. -/

/-- con-leche: none — the `bvar` reading. -/
@[grind →] theorem denote_eq_bvar {st : EStore} (hwf : StoreWF st) {h : EIdx}
    {i : Nat} (hw : st.view h = some (.bvar i)) (hs : (denoteE st h).isSome = true) :
    denoteE st h = some (.bvar i) := by
  obtain ⟨e, he⟩ := Option.isSome_iff_exists.mp hs
  rw [he, denote_bvar_inv hwf hw he]

/-- con-leche: none — the `fvar` reading. -/
@[grind →] theorem denote_eq_fvar {st : EStore} (hwf : StoreWF st) {h : EIdx}
    {k : Nat} {ty : EIdx} (hw : st.view h = some (.fvar k ty))
    (hs : (denoteE st h).isSome = true) :
    ∃ t, denoteE st h = some (.fvar k t) ∧ denoteE st ty = some t := by
  obtain ⟨e, he⟩ := Option.isSome_iff_exists.mp hs
  obtain ⟨t, rfl, ht⟩ := denote_fvar_inv hwf hw he
  exact ⟨t, he, ht⟩

/-- con-leche: none — the `sort` reading. -/
@[grind →] theorem denote_eq_sort {st : EStore} (hwf : StoreWF st) {h : EIdx}
    {u : LIdx} (hw : st.view h = some (.sort u)) (hs : (denoteE st h).isSome = true) :
    ∃ l, denoteE st h = some (.sort l) ∧ denoteL st.ls u = some l := by
  obtain ⟨e, he⟩ := Option.isSome_iff_exists.mp hs
  obtain ⟨l, rfl, hl⟩ := denote_sort_inv hwf hw he
  exact ⟨l, he, hl⟩

/-- con-leche: none — the `const` reading. -/
@[grind →] theorem denote_eq_const {st : EStore} (hwf : StoreWF st) {h : EIdx}
    {n : NIdx} {us : LsIdx} (hw : st.view h = some (.const n us))
    (hs : (denoteE st h).isSome = true) :
    ∃ nm ls, denoteE st h = some (.const nm ls) ∧ denoteN st.ns n = some nm ∧
      denoteLs st.lss us = some ls := by
  obtain ⟨e, he⟩ := Option.isSome_iff_exists.mp hs
  obtain ⟨nm, ls, rfl, hn, hl⟩ := denote_const_inv hwf hw he
  exact ⟨nm, ls, he, hn, hl⟩

/-- con-leche: none — the `lit` reading. -/
@[grind →] theorem denote_eq_lit {st : EStore} (hwf : StoreWF st) {h : EIdx}
    {l : Literal} (hw : st.view h = some (.lit l)) (hs : (denoteE st h).isSome = true) :
    denoteE st h = some (.lit l) := by
  obtain ⟨e, he⟩ := Option.isSome_iff_exists.mp hs
  rw [he, denote_lit_inv hwf hw he]

/-- con-leche: none — the `app` reading. -/
@[grind →] theorem denote_eq_app {st : EStore} (hwf : StoreWF st) {h f a : EIdx}
    (hw : st.view h = some (.app f a)) (hs : (denoteE st h).isSome = true) :
    ∃ ef ea, denoteE st h = some (.app ef ea) ∧
      denoteE st f = some ef ∧ denoteE st a = some ea := by
  obtain ⟨e, he⟩ := Option.isSome_iff_exists.mp hs
  obtain ⟨x, y, rfl, hx, hy⟩ := denote_app_inv hwf hw he
  exact ⟨x, y, he, hx, hy⟩

/-- con-leche: none — the `lam` reading. -/
@[grind →] theorem denote_eq_lam {st : EStore} (hwf : StoreWF st) {h ty b : EIdx}
    {m : BinderMeta} (hw : st.view h = some (.lam ty b m))
    (hs : (denoteE st h).isSome = true) :
    ∃ et eb, denoteE st h = some (.lam et eb m) ∧
      denoteE st ty = some et ∧ denoteE st b = some eb := by
  obtain ⟨e, he⟩ := Option.isSome_iff_exists.mp hs
  obtain ⟨x, y, rfl, hx, hy⟩ := denote_lam_inv hwf hw he
  exact ⟨x, y, he, hx, hy⟩

/-- con-leche: none — the `forallE` reading. -/
@[grind →] theorem denote_eq_forallE {st : EStore} (hwf : StoreWF st) {h ty b : EIdx}
    {m : BinderMeta} (hw : st.view h = some (.forallE ty b m))
    (hs : (denoteE st h).isSome = true) :
    ∃ et eb, denoteE st h = some (.forallE et eb m) ∧
      denoteE st ty = some et ∧ denoteE st b = some eb := by
  obtain ⟨e, he⟩ := Option.isSome_iff_exists.mp hs
  obtain ⟨x, y, rfl, hx, hy⟩ := denote_forallE_inv hwf hw he
  exact ⟨x, y, he, hx, hy⟩

/-- con-leche: none — the `letE` reading. -/
@[grind →] theorem denote_eq_letE {st : EStore} (hwf : StoreWF st) {h ty w b : EIdx}
    (hw : st.view h = some (.letE ty w b)) (hs : (denoteE st h).isSome = true) :
    ∃ et ew eb, denoteE st h = some (.letE et ew eb) ∧ denoteE st ty = some et ∧
      denoteE st w = some ew ∧ denoteE st b = some eb := by
  obtain ⟨e, he⟩ := Option.isSome_iff_exists.mp hs
  obtain ⟨x, y, z, rfl, hx, hy, hz⟩ := denote_letE_inv hwf hw he
  exact ⟨x, y, z, he, hx, hy, hz⟩

/-- con-leche: none — the `proj` reading. -/
@[grind →] theorem denote_eq_proj {st : EStore} (hwf : StoreWF st) {h : EIdx}
    {n : NIdx} {i : Nat} {sub : EIdx} (hw : st.view h = some (.proj n i sub))
    (hs : (denoteE st h).isSome = true) :
    ∃ nm es, denoteE st h = some (.proj nm i es) ∧
      denoteN st.ns n = some nm ∧ denoteE st sub = some es := by
  obtain ⟨e, he⟩ := Option.isSome_iff_exists.mp hs
  obtain ⟨x, y, rfl, hx, hy⟩ := denote_proj_inv hwf hw he
  exact ⟨x, y, he, hx, hy⟩

/-! ## Group 6 — the answer relation and its eliminators

**The one generalisation over the spike.**  `RelAt f st c st' r` is the
conditional postcondition, named (rule 5) and parametric in the pure function
— so the five eliminators exist once for all eleven walks of this module
instead of once each. -/

/-- con-leche: ConLeche/Verify/SimI.lean:250 RelE — "`r` in `st'` is what `f`
makes of what `c` denotes in `st`". -/
def RelAt (f : Expr → Expr) (st : EStore) (c : EIdx) (st' : EStore) (r : EIdx) :
    Prop :=
  ∀ e, denoteE st c = some e → denoteE st' r = some (f e)

/-- con-leche: none — apply the answer at a known denotation. -/
@[grind →] theorem RelAt.apply {f : Expr → Expr} {st st' : EStore} {c r : EIdx}
    {e : Expr} (h : RelAt f st c st' r) (he : denoteE st c = some e) :
    denoteE st' r = some (f e) := h e he

/-- con-leche: none — the answer denotes. -/
@[grind →] theorem RelAt.isSome {f : Expr → Expr} {st st' : EStore} {c r : EIdx}
    (h : RelAt f st c st' r) (hs : (denoteE st c).isSome = true) :
    (denoteE st' r).isSome = true := by
  obtain ⟨e, he⟩ := Option.isSome_iff_exists.mp hs
  rw [h e he]; rfl

/-- con-leche: none — the answer travels forward with the arena. -/
@[grind →] theorem RelAt.ext {f : Expr → Expr} {st st' st'' : EStore} {c r : EIdx}
    (h : RelAt f st c st' r) (hx : Ext st' st'') : RelAt f st c st'' r :=
  fun e he => denote_ext (h e he) hx

/-- con-leche: none — and backward along an extension of the *source*. -/
@[grind →] theorem RelAt.of_ext {f : Expr → Expr} {st st0 st' : EStore} {c r : EIdx}
    (h : RelAt f st c st' r) (hx : Ext st0 st) : RelAt f st0 c st' r :=
  fun e he => h e (denote_ext he hx)

/-- con-leche: none — **retarget the source store**.  The answer was
established against the store the call *started* in; the memo records it
against the store the call *ended* in.  They agree because `denoteE` is a
function and `Ext` transports the input's denotation forward.  This is the
one lemma con-leche's tree-shaped proof never needed. -/
@[grind →] theorem RelAt.retarget {f : Expr → Expr} {st st0 st' : EStore}
    {c r : EIdx} (h : RelAt f st c st' r) (hx : Ext st st0)
    (hs : (denoteE st c).isSome = true) : RelAt f st0 c st' r := by
  intro e he
  obtain ⟨e0, he0⟩ := Option.isSome_iff_exists.mp hs
  have hh := denote_ext he0 hx
  rw [he] at hh
  rw [Option.some.inj hh]
  exact h e0 he0

/-- con-leche: none — the identity answer: a node the walk returns unchanged,
because the pure function fixes what it denotes.  Every leaf arm and every
cutoff of this module is an instance. -/
theorem RelAt.self {f : Expr → Expr} {st st' : EStore} {h : EIdx}
    (hx : Ext st st') (hfix : ∀ e, denoteE st h = some e → f e = e) :
    RelAt f st h st' h := by
  intro e he
  rw [hfix e he]
  exact denote_ext he hx

/-- con-leche: none — two extensions at once; `grind` chains `Ext.trans` and
`RelAt.ext` only when it has the budget for two nested instantiations. -/
theorem RelAt.ext2 {f : Expr → Expr} {st a b c : EStore} {x r : EIdx}
    (h : RelAt f st x a r) (h1 : Ext a b) (h2 : Ext b c) : RelAt f st x c r :=
  (h.ext h1).ext h2

/-! ## Group 7 — the per-site step lemmas

One per branching constructor: "the children's answers, interned, are the
parent's answer".  This is the piece `grind` cannot invent, because it is
where the pure equation `f (.app x y) = .app (ff x) (fa y)` meets the store —
and taking that equation as a HYPOTHESIS is what makes one lemma serve all
eleven walks.  For every twin in this module the equation is `rfl`. -/

/-- con-leche: none — the `fvar` site (the walks that descend into an
annotation: `resetMeta`, `renameConsts`, `instantiateLevelParams`). -/
theorem RelAt.fvar {f ft : Expr → Expr} {st st' : EStore} {h ty rt r : EIdx}
    {k : Nat} (hwf : StoreWF st)
    (hdec : ∀ t, f (.fvar k t) = .fvar k (ft t))
    (hview : st.view h = some (.fvar k ty))
    (ht : RelAt ft st ty st' rt)
    (hr : denoteE st' r = denoteEView st' (.fvar k rt)) : RelAt f st h st' r := by
  intro e he
  obtain ⟨et, rfl, hdt⟩ := denote_fvar_inv hwf hview he
  rw [hr, denoteEView, ht et hdt, hdec]; rfl

/-- con-leche: none — the `app` site. -/
theorem RelAt.app {f ff fa : Expr → Expr} {st st' : EStore}
    {h fh a rf ra r : EIdx} (hwf : StoreWF st)
    (hdec : ∀ x y, f (.app x y) = .app (ff x) (fa y))
    (hview : st.view h = some (.app fh a))
    (hf : RelAt ff st fh st' rf) (ha : RelAt fa st a st' ra)
    (hr : denoteE st' r = denoteEView st' (.app rf ra)) : RelAt f st h st' r := by
  intro e he
  obtain ⟨ef, ea, rfl, hdf, hda⟩ := denote_app_inv hwf hview he
  rw [hr, denoteEView, hf ef hdf, ha ea hda, hdec]; rfl

/-- con-leche: none — the `lam` site.  The binder metadata the twin writes
back is `mr`, which is `m` for every walk but `resetMeta` (the parse
placeholder) and `instantiateLevelParams` (the substituted datum). -/
theorem RelAt.lam {f ft fb : Expr → Expr} {st st' : EStore}
    {h ty b rt rb r : EIdx} {m mr : BinderMeta} (hwf : StoreWF st)
    (hdec : ∀ x y, f (.lam x y m) = .lam (ft x) (fb y) mr)
    (hview : st.view h = some (.lam ty b m))
    (ht : RelAt ft st ty st' rt) (hb : RelAt fb st b st' rb)
    (hr : denoteE st' r = denoteEView st' (.lam rt rb mr)) : RelAt f st h st' r := by
  intro e he
  obtain ⟨et, eb, rfl, hdt, hdb⟩ := denote_lam_inv hwf hview he
  rw [hr, denoteEView, ht et hdt, hb eb hdb, hdec]; rfl

/-- con-leche: none — the `forallE` site. -/
theorem RelAt.forallE {f ft fb : Expr → Expr} {st st' : EStore}
    {h ty b rt rb r : EIdx} {m mr : BinderMeta} (hwf : StoreWF st)
    (hdec : ∀ x y, f (.forallE x y m) = .forallE (ft x) (fb y) mr)
    (hview : st.view h = some (.forallE ty b m))
    (ht : RelAt ft st ty st' rt) (hb : RelAt fb st b st' rb)
    (hr : denoteE st' r = denoteEView st' (.forallE rt rb mr)) :
    RelAt f st h st' r := by
  intro e he
  obtain ⟨et, eb, rfl, hdt, hdb⟩ := denote_forallE_inv hwf hview he
  rw [hr, denoteEView, ht et hdt, hb eb hdb, hdec]; rfl

/-- con-leche: none — the `letE` site. -/
theorem RelAt.letE {f ft fv fb : Expr → Expr} {st st' : EStore}
    {h ty w b rt rw rb r : EIdx} (hwf : StoreWF st)
    (hdec : ∀ x y z, f (.letE x y z) = .letE (ft x) (fv y) (fb z))
    (hview : st.view h = some (.letE ty w b))
    (ht : RelAt ft st ty st' rt) (hw : RelAt fv st w st' rw)
    (hb : RelAt fb st b st' rb)
    (hr : denoteE st' r = denoteEView st' (.letE rt rw rb)) :
    RelAt f st h st' r := by
  intro e he
  obtain ⟨et, ew, eb, rfl, hdt, hdw, hdb⟩ := denote_letE_inv hwf hview he
  rw [hr, denoteEView, ht et hdt, hw ew hdw, hb eb hdb, hdec]; rfl

/-- con-leche: none — the `proj` site.  The one site whose step needs a fact
about the NAME store: the struct name is carried through unchanged, so its
denotation must be the same on both sides of the extension. -/
theorem RelAt.proj {f fs : Expr → Expr} {st st' : EStore}
    {h sub rs r : EIdx} {n : NIdx} {i : Nat} {nm : ConLeche.Name} (hwf : StoreWF st)
    (hdec : ∀ x, f (.proj nm i x) = .proj nm i (fs x))
    (hview : st.view h = some (.proj n i sub))
    (hs : RelAt fs st sub st' rs)
    (hr : denoteE st' r = denoteEView st' (.proj n i rs))
    (hn : denoteN st'.ns n = some nm) (hn0 : denoteN st.ns n = some nm) :
    RelAt f st h st' r := by
  intro e he
  obtain ⟨nm', es, rfl, hdn, hds⟩ := denote_proj_inv hwf hview he
  rw [hn0] at hdn
  obtain rfl := Option.some.inj hdn
  rw [hr, denoteEView, hs es hds, hn, hdec]; rfl

/-! ### The same lemmas, as the verification condition presents them

The children's answers stated against the store each call *started* in, with
the extension chain spelled out.  Composing `of_ext`/`ext`/`trans` on the fly
costs `grind` three nested instantiations and it does not find them; with the
chain inside the lemma the verification condition is one `exact`.

**These six are NOT `@[grind →]`, and that is the price of the generic
relation.**  `hdec`'s head symbol is the *variable* `f`, so `grind` reports
"failed to find patterns in the antecedents" and refuses the registration.
The spike's monomorphic `Inst1At.*_step` could be registered; here the two
structural verification conditions of every arm are applied by hand with
`exact`, which task #97s round 2 already recommends as the cheaper move
("`grind` spends thousands of E-matching instances rediscovering them;
`exact` spends none"). -/

/-- con-leche: none — the `fvar` site as `mvcgen` presents it. -/
theorem RelAt.fvar_step {f ft : Expr → Expr} {st s1 s2 : EStore}
    {h ty rt r : EIdx} {k : Nat} (hwf : StoreWF st)
    (hdec : ∀ t, f (.fvar k t) = .fvar k (ft t))
    (hview : st.view h = some (.fvar k ty))
    (_hx1 : Ext st s1) (ht : RelAt ft st ty s1 rt) (hx2 : Ext s1 s2)
    (hr : denoteE s2 r = denoteEView s2 (.fvar k rt)) : RelAt f st h s2 r :=
  RelAt.fvar hwf hdec hview (ht.ext hx2) hr

/-- con-leche: none — the `app` site as `mvcgen` presents it. -/
theorem RelAt.app_step {f ff fa : Expr → Expr} {st s1 s2 s3 : EStore}
    {h fh a rf ra r : EIdx} (hwf : StoreWF st)
    (hdec : ∀ x y, f (.app x y) = .app (ff x) (fa y))
    (hview : st.view h = some (.app fh a))
    (hx1 : Ext st s1) (hf : RelAt ff st fh s1 rf)
    (hx2 : Ext s1 s2) (ha : RelAt fa s1 a s2 ra)
    (hx3 : Ext s2 s3)
    (hr : denoteE s3 r = denoteEView s3 (.app rf ra)) : RelAt f st h s3 r :=
  RelAt.app hwf hdec hview ((hf.ext hx2).ext hx3) ((ha.of_ext hx1).ext hx3) hr

/-- con-leche: none — the `lam` site as `mvcgen` presents it. -/
theorem RelAt.lam_step {f ft fb : Expr → Expr} {st s1 s2 s3 : EStore}
    {h ty b rt rb r : EIdx} {m mr : BinderMeta} (hwf : StoreWF st)
    (hdec : ∀ x y, f (.lam x y m) = .lam (ft x) (fb y) mr)
    (hview : st.view h = some (.lam ty b m))
    (hx1 : Ext st s1) (ht : RelAt ft st ty s1 rt)
    (hx2 : Ext s1 s2) (hb : RelAt fb s1 b s2 rb)
    (hx3 : Ext s2 s3)
    (hr : denoteE s3 r = denoteEView s3 (.lam rt rb mr)) : RelAt f st h s3 r :=
  RelAt.lam hwf hdec hview ((ht.ext hx2).ext hx3) ((hb.of_ext hx1).ext hx3) hr

/-- con-leche: none — the `forallE` site as `mvcgen` presents it. -/
theorem RelAt.forallE_step {f ft fb : Expr → Expr} {st s1 s2 s3 : EStore}
    {h ty b rt rb r : EIdx} {m mr : BinderMeta} (hwf : StoreWF st)
    (hdec : ∀ x y, f (.forallE x y m) = .forallE (ft x) (fb y) mr)
    (hview : st.view h = some (.forallE ty b m))
    (hx1 : Ext st s1) (ht : RelAt ft st ty s1 rt)
    (hx2 : Ext s1 s2) (hb : RelAt fb s1 b s2 rb)
    (hx3 : Ext s2 s3)
    (hr : denoteE s3 r = denoteEView s3 (.forallE rt rb mr)) : RelAt f st h s3 r :=
  RelAt.forallE hwf hdec hview ((ht.ext hx2).ext hx3) ((hb.of_ext hx1).ext hx3) hr

/-- con-leche: none — the `letE` site as `mvcgen` presents it: three children,
four intermediate stores. -/
theorem RelAt.letE_step {f ft fv fb : Expr → Expr}
    {st s1 s2 s3 s4 : EStore} {h ty w b rt rw rb r : EIdx} (hwf : StoreWF st)
    (hdec : ∀ x y z, f (.letE x y z) = .letE (ft x) (fv y) (fb z))
    (hview : st.view h = some (.letE ty w b))
    (hx1 : Ext st s1) (ht : RelAt ft st ty s1 rt)
    (hx2 : Ext s1 s2) (hw : RelAt fv s1 w s2 rw)
    (hx3 : Ext s2 s3) (hb : RelAt fb s2 b s3 rb)
    (hx4 : Ext s3 s4)
    (hr : denoteE s4 r = denoteEView s4 (.letE rt rw rb)) : RelAt f st h s4 r :=
  RelAt.letE hwf hdec hview (((ht.ext hx2).ext hx3).ext hx4)
    (((hw.of_ext hx1).ext hx3).ext hx4) ((hb.of_ext (hx1.trans hx2)).ext hx4) hr

/-- con-leche: none — the `proj` site as `mvcgen` presents it. -/
theorem RelAt.proj_step {f fs : Expr → Expr} {st s1 s2 : EStore}
    {h sub rs r : EIdx} {n : NIdx} {i : Nat} {nm : ConLeche.Name} (hwf : StoreWF st)
    (hdec : ∀ x, f (.proj nm i x) = .proj nm i (fs x))
    (hview : st.view h = some (.proj n i sub))
    (hx1 : Ext st s1) (hs : RelAt fs st sub s1 rs)
    (hx2 : Ext s1 s2)
    (hr : denoteE s2 r = denoteEView s2 (.proj n i rs))
    (hn0 : denoteN st.ns n = some nm) : RelAt f st h s2 r :=
  RelAt.proj hwf hdec hview (hs.ext hx2) hr (denoteN_ext (denoteN_ext hn0 hx1) hx2) hn0

/-! ## Group 8a — `ViewOK`, `intern`'s precondition

One lemma per node shape the twins build: "the children denote, hence they
have views". -/

/-- con-leche: none — a handle that denotes has a view (the `isSome`
spelling, so nothing has to be guessed). -/
theorem view_isSome {st : EStore} {c : EIdx} (hs : (denoteE st c).isSome = true) :
    (st.view c).isSome = true := by
  obtain ⟨e, he⟩ := Option.isSome_iff_exists.mp hs
  exact view_isSome_of_denote he

/-- con-leche: none — a name handle that denotes has a view. -/
@[grind →] theorem nview_isSome_of_denote {st : NStore} {c : NIdx}
    {x : ConLeche.Name} (hd : denoteN st c = some x) : (st.view c).isSome = true := by
  obtain ⟨w, hw⟩ := denoteN_view hd; rw [hw]; rfl

/-- con-leche: none — `ViewOK` of a `bvar` node. -/
theorem viewOK_bvar {st : EStore} {i : Nat} : st.ViewOK (.bvar i) :=
  ⟨by simp [ENodeView.echildren], by simp [ENodeView.nchildren],
   by simp [ENodeView.lchildren], by simp [ENodeView.lschildren]⟩

/-- con-leche: none — `ViewOK` of a `lit` node. -/
theorem viewOK_lit {st : EStore} {l : Literal} : st.ViewOK (.lit l) :=
  ⟨by simp [ENodeView.echildren], by simp [ENodeView.nchildren],
   by simp [ENodeView.lchildren], by simp [ENodeView.lschildren]⟩

/-- con-leche: none — `ViewOK` of an `fvar` node. -/
theorem viewOK_fvar {st : EStore} {k : Nat} {ty : EIdx}
    (ht : (denoteE st ty).isSome = true) : st.ViewOK (.fvar k ty) :=
  ⟨by intro c hc; simp [ENodeView.echildren] at hc; subst hc; exact view_isSome ht,
   by simp [ENodeView.nchildren], by simp [ENodeView.lchildren],
   by simp [ENodeView.lschildren]⟩

/-- con-leche: none — `ViewOK` of an `app` node. -/
theorem viewOK_app {st : EStore} {f a : EIdx}
    (hf : (denoteE st f).isSome = true) (ha : (denoteE st a).isSome = true) :
    st.ViewOK (.app f a) :=
  ⟨by intro c hc; simp [ENodeView.echildren] at hc
      rcases hc with rfl | rfl
      · exact view_isSome hf
      · exact view_isSome ha,
   by simp [ENodeView.nchildren], by simp [ENodeView.lchildren],
   by simp [ENodeView.lschildren]⟩

/-- con-leche: none — `ViewOK` of a `lam` node. -/
theorem viewOK_lam {st : EStore} {ty b : EIdx} {m : BinderMeta}
    (ht : (denoteE st ty).isSome = true) (hb : (denoteE st b).isSome = true) :
    st.ViewOK (.lam ty b m) :=
  ⟨by intro c hc; simp [ENodeView.echildren] at hc
      rcases hc with rfl | rfl
      · exact view_isSome ht
      · exact view_isSome hb,
   by simp [ENodeView.nchildren], by simp [ENodeView.lchildren],
   by simp [ENodeView.lschildren]⟩

/-- con-leche: none — `ViewOK` of a `forallE` node. -/
theorem viewOK_forallE {st : EStore} {ty b : EIdx} {m : BinderMeta}
    (ht : (denoteE st ty).isSome = true) (hb : (denoteE st b).isSome = true) :
    st.ViewOK (.forallE ty b m) :=
  ⟨by intro c hc; simp [ENodeView.echildren] at hc
      rcases hc with rfl | rfl
      · exact view_isSome ht
      · exact view_isSome hb,
   by simp [ENodeView.nchildren], by simp [ENodeView.lchildren],
   by simp [ENodeView.lschildren]⟩

/-- con-leche: none — `ViewOK` of a `letE` node. -/
theorem viewOK_letE {st : EStore} {ty w b : EIdx}
    (ht : (denoteE st ty).isSome = true) (hw : (denoteE st w).isSome = true)
    (hb : (denoteE st b).isSome = true) : st.ViewOK (.letE ty w b) :=
  ⟨by intro c hc; simp [ENodeView.echildren] at hc
      rcases hc with rfl | rfl | rfl
      · exact view_isSome ht
      · exact view_isSome hw
      · exact view_isSome hb,
   by simp [ENodeView.nchildren], by simp [ENodeView.lchildren],
   by simp [ENodeView.lschildren]⟩

/-- con-leche: none — `ViewOK` of a `proj` node. -/
theorem viewOK_proj {st : EStore} {n : NIdx} {i : Nat} {sub : EIdx}
    (hn : (st.ns.view n).isSome = true) (hs : (denoteE st sub).isSome = true) :
    st.ViewOK (.proj n i sub) :=
  ⟨by intro c hc; simp [ENodeView.echildren] at hc; subst hc
      exact view_isSome hs,
   by intro c hc; simp [ENodeView.nchildren] at hc; subst hc; exact hn,
   by simp [ENodeView.lchildren], by simp [ENodeView.lschildren]⟩

/-! ## Group 8b — the state invariant and the memo invariants -/

/-- con-leche: ConLeche/Verify/SimI.lean:54 ISOK — the state invariant, cut to
P2b's one clause: the arena is well formed.  P2c adds the environment index
and the per-declaration caches. -/
structure StateOK (s : AState) : Prop where
  wf : StoreWF s.store

/-- con-leche: ConLeche/Kernel/ExprOps.lean:60-62 Inst1MemoInv — the invariant
of a cursor-keyed handle memo, transported through `denoteE`: every recorded
answer is the real one, at the key's own cursor.  Generic in the pure
function, so the four eliminators below serve all nine tables. -/
def MemoOK (f : Nat → Expr → Expr) (tbl : Std.HashMap (EIdx × Nat) EIdx)
    (st : EStore) : Prop :=
  ∀ (k : EIdx × Nat) (r : EIdx), tbl[k]? = some r →
    ∃ e, denoteE st k.1 = some e ∧ denoteE st r = some (f k.2 e)

/-- con-leche: ConLeche/Kernel/ExprOps.lean:1494-1496 MemoBInv — the invariant
of a `Nat`-valued memo (`bvarBound`, `fvarRange`). -/
def MemoNOK (f : Expr → Nat) (tbl : Std.HashMap EIdx Nat) (st : EStore) : Prop :=
  ∀ (k : EIdx) (r : Nat), tbl[k]? = some r → ∃ e, denoteE st k = some e ∧ r = f e

/-- con-leche: ConLeche/Kernel/ExprOps.lean:60-62 Inst1MemoInv — the memo
survives an arena extension that leaves the table alone. -/
theorem MemoOK.mono {f : Nat → Expr → Expr} {t t' : Std.HashMap (EIdx × Nat) EIdx}
    {st st' : EStore} (hm : MemoOK f t st) (hx : Ext st st') (hc : t' = t) :
    MemoOK f t' st' := by
  intro k r hk
  rw [hc] at hk
  obtain ⟨e, h1, h2⟩ := hm k r hk
  exact ⟨e, denote_ext h1 hx, denote_ext h2 hx⟩

/-- con-leche: ConLeche/Kernel/ExprOps.lean:64-65 Inst1MemoInv.empty — the
*dropped* memo satisfies the invariant for every pure function.  That is why
a per-call memo never appears in a caller's invariant. -/
theorem MemoOK.of_empty {t : Std.HashMap (EIdx × Nat) EIdx} {st : EStore}
    (h : t = ∅) : ∀ f : Nat → Expr → Expr, MemoOK f t st := by
  intro f k r hk; rw [h] at hk; simp at hk

/-- con-leche: ConLeche/Kernel/ExprOps.lean:60-62 Inst1MemoInv — **the memo
hit**: a recorded entry *is* the answer.  Stated as `RelAt` so that the caller
never has to unfold `MemoOK` (and so that `MemoOK` can stay out of `grind`'s
unfold list, where it would skolemise the goal). -/
@[grind →] theorem MemoOK.get {f : Nat → Expr → Expr}
    {t : Std.HashMap (EIdx × Nat) EIdx} {st : EStore} {k : EIdx × Nat} {r : EIdx}
    (hm : MemoOK f t st) (hk : t[k]? = some r) : RelAt (f k.2) st k.1 st r := by
  intro e he
  obtain ⟨e', h1, h2⟩ := hm k r hk
  rw [he] at h1
  obtain rfl := Option.some.inj h1
  exact h2

/-- con-leche: ConLeche/Kernel/ExprOps.lean:67-77 Inst1MemoInv.insert — stated
in the `isSome` + `RelAt` idiom, so that nothing has to be *guessed* when
`grind` applies it (rule 6: the spec of an insert says the invariant is
preserved, not that the table grew). -/
theorem MemoOK.insert {f : Nat → Expr → Expr} {t : Std.HashMap (EIdx × Nat) EIdx}
    {st : EStore} {k : EIdx × Nat} {r : EIdx} (hm : MemoOK f t st)
    (hk : (denoteE st k.1).isSome = true) (hr : RelAt (f k.2) st k.1 st r) :
    MemoOK f (t.insert k r) st := by
  obtain ⟨e, he⟩ := Option.isSome_iff_exists.mp hk
  intro k' r' hk'
  rw [Std.HashMap.getElem?_insert] at hk'
  split at hk'
  · rename_i hbeq
    cases hk'
    obtain rfl := eq_of_beq hbeq
    exact ⟨e, he, hr e he⟩
  · exact hm k' r' hk'

/-- con-leche: ConLeche/Kernel/ExprOps.lean:1494-1496 MemoBInv — the
`Nat`-valued memo survives an extension. -/
theorem MemoNOK.mono {f : Expr → Nat} {t t' : Std.HashMap EIdx Nat}
    {st st' : EStore} (hm : MemoNOK f t st) (hx : Ext st st') (hc : t' = t) :
    MemoNOK f t' st' := by
  intro k r hk
  rw [hc] at hk
  obtain ⟨e, h1, h2⟩ := hm k r hk
  exact ⟨e, denote_ext h1 hx, h2⟩

/-- con-leche: ConLeche/Kernel/ExprOps.lean:1494-1496 MemoBInv — the dropped
`Nat`-valued memo. -/
theorem MemoNOK.of_empty {t : Std.HashMap EIdx Nat} {st : EStore} (h : t = ∅) :
    ∀ f : Expr → Nat, MemoNOK f t st := by
  intro f k r hk; rw [h] at hk; simp at hk

/-- con-leche: ConLeche/Kernel/ExprOps.lean:1494-1496 MemoBInv — the hit. -/
@[grind →] theorem MemoNOK.get {f : Expr → Nat} {t : Std.HashMap EIdx Nat}
    {st : EStore} {k : EIdx} {r : Nat} {e : Expr} (hm : MemoNOK f t st)
    (hk : t[k]? = some r) (he : denoteE st k = some e) : r = f e := by
  obtain ⟨e', h1, h2⟩ := hm k r hk
  rw [he] at h1
  obtain rfl := Option.some.inj h1
  exact h2

/-- con-leche: ConLeche/Kernel/ExprOps.lean:1494-1496 MemoBInv — the insert. -/
theorem MemoNOK.insert {f : Expr → Nat} {t : Std.HashMap EIdx Nat} {st : EStore}
    {k : EIdx} {r : Nat} {e : Expr} (hm : MemoNOK f t st)
    (he : denoteE st k = some e) (hr : r = f e) : MemoNOK f (t.insert k r) st := by
  intro k' r' hk'
  rw [Std.HashMap.getElem?_insert] at hk'
  split at hk'
  · rename_i hbeq
    cases hk'
    obtain rfl := eq_of_beq hbeq
    exact ⟨e, he, hr⟩
  · exact hm k' r' hk'

/-! ## The `@[spec]` theorems for the store primitives

One per primitive of `Monad.lean`, in the template's shape.  These are what
`mvcgen` walks a twin's body with; after them no twin proof mentions the
store layer. -/

/-- con-leche: ConLeche/Kernel/Core.lean:47-66 CheckError — **the failure
spec**: a `fail` never returns, so under `⇓?` its success barrel is `False`
and every continuation goal it produces closes by `.elim`. -/
@[spec] theorem fail_spec {α : Type} (e : CheckError) :
    ⦃fun _ => ⌜True⌝⦄ (fail e : AM α) ⦃⇓? _r _s' => ⌜False⌝⦄ := by
  intro _ _; trivial

/-- con-leche: none — `view` does not touch the state and returns the store's
own decoding. -/
@[spec] theorem view_spec (s₀ : AState) (h : EIdx) :
    ⦃fun s => ⌜s = s₀⌝⦄ view h
    ⦃⇓? v s' => ⌜s' = s₀ ∧ s₀.store.view h = some v⌝⦄ := by
  mvcgen [view]
  · grind
  · exact fun hf => hf.elim

/-- con-leche: none — `viewN` does not touch the state. -/
@[spec] theorem viewN_spec (s₀ : AState) (h : NIdx) :
    ⦃fun s => ⌜s = s₀⌝⦄ viewN h
    ⦃⇓? v s' => ⌜s' = s₀ ∧ s₀.store.ns.view h = some v⌝⦄ := by
  mvcgen [viewN]
  · grind
  · exact fun hf => hf.elim

/-- con-leche: none — `viewL` does not touch the state. -/
@[spec] theorem viewL_spec (s₀ : AState) (h : LIdx) :
    ⦃fun s => ⌜s = s₀⌝⦄ viewL h
    ⦃⇓? v s' => ⌜s' = s₀ ∧ s₀.store.ls.view h = some v⌝⦄ := by
  mvcgen [viewL]
  · grind
  · exact fun hf => hf.elim

/-- con-leche: none — `viewLs` does not touch the state. -/
@[spec] theorem viewLs_spec (s₀ : AState) (h : LsIdx) :
    ⦃fun s => ⌜s = s₀⌝⦄ viewLs h
    ⦃⇓? v s' => ⌜s' = s₀ ∧ s₀.store.lss.view h = some v⌝⦄ := by
  mvcgen [viewLs]
  · grind
  · exact fun hf => hf.elim

/-- con-leche: ConLeche/Kernel/Expr.lean:343-402 Expr — `derivedE` reads the
packed word; with `EStore.derived_exact` that word is `e.data` for the
denoted `e`. -/
@[spec] theorem derivedE_spec (s₀ : AState) (h : EIdx) :
    ⦃fun s => ⌜s = s₀⌝⦄ derivedE h
    ⦃⇓? w s' => ⌜s' = s₀ ∧ w = s₀.store.derived h⌝⦄ := by
  mvcgen [derivedE]
  grind

/-- con-leche: ConLeche/Kernel/Expr.lean:40-53 Level — `derivedL` reads the
level's derived pair. -/
@[spec] theorem derivedL_spec (s₀ : AState) (h : LIdx) :
    ⦃fun s => ⌜s = s₀⌝⦄ derivedL h
    ⦃⇓? w s' => ⌜s' = s₀ ∧ w = s₀.store.lder h⌝⦄ := by
  mvcgen [derivedL]
  grind

/-- con-leche: ConLeche/Kernel/Level.lean:26-37 subst — the level readback IS
`denoteL`, so its spec is an equation and not a simulation (DESIGN §8.3
lesson 4). -/
@[spec] theorem readLevel_spec (s₀ : AState) (h : LIdx) :
    ⦃fun s => ⌜s = s₀⌝⦄ readLevel h
    ⦃⇓? u s' => ⌜s' = s₀ ∧ denoteL s₀.store.ls h = some u⌝⦄ := by
  mvcgen [readLevel]
  · grind
  · exact fun hf => hf.elim

/-- con-leche: ConLeche/Kernel/Name.lean:34-37 Name — the name readback. -/
@[spec] theorem readName_spec (s₀ : AState) (h : NIdx) :
    ⦃fun s => ⌜s = s₀⌝⦄ readName h
    ⦃⇓? x s' => ⌜s' = s₀ ∧ denoteN s₀.store.ns h = some x⌝⦄ := by
  mvcgen [readName]
  · grind
  · exact fun hf => hf.elim

/-- con-leche: ConLeche/Kernel/Level.lean:26-37 subst — the level-list
readback. -/
@[spec] theorem readLevels_spec (s₀ : AState) (h : LsIdx) :
    ⦃fun s => ⌜s = s₀⌝⦄ readLevels h
    ⦃⇓? us s' => ⌜s' = s₀ ∧ denoteLs s₀.store.lss h = some us⌝⦄ := by
  mvcgen [readLevels]
  · grind
  · exact fun hf => hf.elim

/-- con-leche: Setlec/Kernel/IExpr.lean:464 intern — **the one spec that
carries the arena**: a handle for the node, the store still well formed, the
arena only grown, the memo tables untouched, and the three nested stores
literally unchanged (so a name or level handle that had a view still has
one).  The capacity branch raises `native` and claims nothing. -/
@[spec] theorem internE_spec (s₀ : AState) (w : ENodeView)
    (hwf : StoreWF s₀.store) (hv : s₀.store.ViewOK w) :
    ⦃fun s => ⌜s = s₀⌝⦄ internE w
    ⦃⇓? h s' => ⌜StoreWF s'.store ∧ Ext s₀.store s'.store ∧
        s'.store.lss = s₀.store.lss ∧ s'.memos = s₀.memos ∧
        s'.store.view h = some w ∧
        denoteE s'.store h = denoteEView s'.store w⌝⦄ := by
  mvcgen [internE]
  case vc1.isTrue =>
    rename_i s hs _n hcap _st _s'
    subst hs
    obtain ⟨h1, h2, h3, h4⟩ := EStore.intern_spec hwf hv hcap
    exact ⟨h1, h2, EStore.lss_intern _ _, rfl, h3, h4⟩
  case vc2.isFalse.success => exact fun hf => hf.elim

/-! ## The `@[spec]` theorems for the memo tables

Eleven triples, one per con-leche `…Go`.  Every `Get` leaves the state alone;
every `Set` states that the INVARIANT is preserved (rule 6) and that the
`Memos` record moved in exactly one field — which is what lets a nested call
(`instantiate1Lift`'s `bvar` arm runs `liftLooseBVars`) carry the outer
walk's invariant across the inner one; every `Clear` re-establishes the
invariant for EVERY pure function, which is why a per-call memo never
appears in a caller's precondition. -/

/-- con-leche: ConLeche/Kernel/ExprOps.lean:80-116 instantiate1Go — probe the `instantiate1` memo. -/
@[spec] theorem inst1Get_spec (s₀ : AState) (k : EIdx × Nat) :
    ⦃fun s => ⌜s = s₀⌝⦄ inst1Get k
    ⦃⇓? r s' => ⌜s' = s₀ ∧ r = s₀.memos.inst1C[k]?⌝⦄ := by
  mvcgen [inst1Get]
  grind

/-- con-leche: ConLeche/Kernel/ExprOps.lean:80-116 instantiate1Go — record a `instantiate1` answer. -/
@[spec] theorem inst1Set_spec (s₀ : AState) (f : Nat → Expr → Expr)
    (k : EIdx × Nat) (r : EIdx) (hm : MemoOK f s₀.memos.inst1C s₀.store)
    (hk : (denoteE s₀.store k.1).isSome = true)
    (hr : RelAt (f k.2) s₀.store k.1 s₀.store r) :
    ⦃fun s => ⌜s = s₀⌝⦄ inst1Set k r
    ⦃⇓? _u s' => ⌜s'.store = s₀.store ∧
        s'.memos = { s₀.memos with inst1C := s₀.memos.inst1C.insert k r } ∧
        MemoOK f s'.memos.inst1C s'.store⌝⦄ := by
  mvcgen [inst1Set]
  rename_i s hs _ _
  subst hs
  exact ⟨rfl, rfl, MemoOK.insert hm hk hr⟩

/-- con-leche: ConLeche/Kernel/ExprOps.lean:182-184 instantiate1Fast — drop the `instantiate1` memo. -/
@[spec] theorem inst1Clear_spec (s₀ : AState) :
    ⦃fun s => ⌜s = s₀⌝⦄ inst1Clear
    ⦃⇓? _u s' => ⌜s'.store = s₀.store ∧
        s'.memos = { s₀.memos with inst1C := ∅ } ∧
        ∀ f, MemoOK f s'.memos.inst1C s'.store⌝⦄ := by
  mvcgen [inst1Clear]
  exact ⟨by grind, by grind, fun f => MemoOK.of_empty rfl f⟩

/-- con-leche: ConLeche/Kernel/ExprOps.lean:267-303 instantiateListGo — probe the `instantiateList` memo. -/
@[spec] theorem instLGet_spec (s₀ : AState) (k : EIdx × Nat) :
    ⦃fun s => ⌜s = s₀⌝⦄ instLGet k
    ⦃⇓? r s' => ⌜s' = s₀ ∧ r = s₀.memos.instLC[k]?⌝⦄ := by
  mvcgen [instLGet]
  grind

/-- con-leche: ConLeche/Kernel/ExprOps.lean:267-303 instantiateListGo — record a `instantiateList` answer. -/
@[spec] theorem instLSet_spec (s₀ : AState) (f : Nat → Expr → Expr)
    (k : EIdx × Nat) (r : EIdx) (hm : MemoOK f s₀.memos.instLC s₀.store)
    (hk : (denoteE s₀.store k.1).isSome = true)
    (hr : RelAt (f k.2) s₀.store k.1 s₀.store r) :
    ⦃fun s => ⌜s = s₀⌝⦄ instLSet k r
    ⦃⇓? _u s' => ⌜s'.store = s₀.store ∧
        s'.memos = { s₀.memos with instLC := s₀.memos.instLC.insert k r } ∧
        MemoOK f s'.memos.instLC s'.store⌝⦄ := by
  mvcgen [instLSet]
  rename_i s hs _ _
  subst hs
  exact ⟨rfl, rfl, MemoOK.insert hm hk hr⟩

/-- con-leche: ConLeche/Kernel/ExprOps.lean:371-373 instantiateListFast — drop the `instantiateList` memo. -/
@[spec] theorem instLClear_spec (s₀ : AState) :
    ⦃fun s => ⌜s = s₀⌝⦄ instLClear
    ⦃⇓? _u s' => ⌜s'.store = s₀.store ∧
        s'.memos = { s₀.memos with instLC := ∅ } ∧
        ∀ f, MemoOK f s'.memos.instLC s'.store⌝⦄ := by
  mvcgen [instLClear]
  exact ⟨by grind, by grind, fun f => MemoOK.of_empty rfl f⟩

/-- con-leche: ConLeche/Kernel/ExprOps.lean:430-466 liftLooseBVarsGo — probe the `liftLooseBVars` memo. -/
@[spec] theorem liftGet_spec (s₀ : AState) (k : EIdx × Nat) :
    ⦃fun s => ⌜s = s₀⌝⦄ liftGet k
    ⦃⇓? r s' => ⌜s' = s₀ ∧ r = s₀.memos.liftC[k]?⌝⦄ := by
  mvcgen [liftGet]
  grind

/-- con-leche: ConLeche/Kernel/ExprOps.lean:430-466 liftLooseBVarsGo — record a `liftLooseBVars` answer. -/
@[spec] theorem liftSet_spec (s₀ : AState) (f : Nat → Expr → Expr)
    (k : EIdx × Nat) (r : EIdx) (hm : MemoOK f s₀.memos.liftC s₀.store)
    (hk : (denoteE s₀.store k.1).isSome = true)
    (hr : RelAt (f k.2) s₀.store k.1 s₀.store r) :
    ⦃fun s => ⌜s = s₀⌝⦄ liftSet k r
    ⦃⇓? _u s' => ⌜s'.store = s₀.store ∧
        s'.memos = { s₀.memos with liftC := s₀.memos.liftC.insert k r } ∧
        MemoOK f s'.memos.liftC s'.store⌝⦄ := by
  mvcgen [liftSet]
  rename_i s hs _ _
  subst hs
  exact ⟨rfl, rfl, MemoOK.insert hm hk hr⟩

/-- con-leche: ConLeche/Kernel/ExprOps.lean:532-534 liftLooseBVarsFast — drop the `liftLooseBVars` memo. -/
@[spec] theorem liftClear_spec (s₀ : AState) :
    ⦃fun s => ⌜s = s₀⌝⦄ liftClear
    ⦃⇓? _u s' => ⌜s'.store = s₀.store ∧
        s'.memos = { s₀.memos with liftC := ∅ } ∧
        ∀ f, MemoOK f s'.memos.liftC s'.store⌝⦄ := by
  mvcgen [liftClear]
  exact ⟨by grind, by grind, fun f => MemoOK.of_empty rfl f⟩

/-- con-leche: ConLeche/Kernel/ExprOps.lean:579-615 resetMetaGo — probe the `resetMeta` memo. -/
@[spec] theorem resetGet_spec (s₀ : AState) (k : EIdx × Nat) :
    ⦃fun s => ⌜s = s₀⌝⦄ resetGet k
    ⦃⇓? r s' => ⌜s' = s₀ ∧ r = s₀.memos.resetC[k]?⌝⦄ := by
  mvcgen [resetGet]
  grind

/-- con-leche: ConLeche/Kernel/ExprOps.lean:579-615 resetMetaGo — record a `resetMeta` answer. -/
@[spec] theorem resetSet_spec (s₀ : AState) (f : Nat → Expr → Expr)
    (k : EIdx × Nat) (r : EIdx) (hm : MemoOK f s₀.memos.resetC s₀.store)
    (hk : (denoteE s₀.store k.1).isSome = true)
    (hr : RelAt (f k.2) s₀.store k.1 s₀.store r) :
    ⦃fun s => ⌜s = s₀⌝⦄ resetSet k r
    ⦃⇓? _u s' => ⌜s'.store = s₀.store ∧
        s'.memos = { s₀.memos with resetC := s₀.memos.resetC.insert k r } ∧
        MemoOK f s'.memos.resetC s'.store⌝⦄ := by
  mvcgen [resetSet]
  rename_i s hs _ _
  subst hs
  exact ⟨rfl, rfl, MemoOK.insert hm hk hr⟩

/-- con-leche: ConLeche/Kernel/ExprOps.lean:687-688 resetMetaFast — drop the `resetMeta` memo. -/
@[spec] theorem resetClear_spec (s₀ : AState) :
    ⦃fun s => ⌜s = s₀⌝⦄ resetClear
    ⦃⇓? _u s' => ⌜s'.store = s₀.store ∧
        s'.memos = { s₀.memos with resetC := ∅ } ∧
        ∀ f, MemoOK f s'.memos.resetC s'.store⌝⦄ := by
  mvcgen [resetClear]
  exact ⟨by grind, by grind, fun f => MemoOK.of_empty rfl f⟩

/-- con-leche: ConLeche/Kernel/ExprOps.lean:999-1036 renameConstsGo — probe the `renameConsts` memo. -/
@[spec] theorem renameGet_spec (s₀ : AState) (k : EIdx × Nat) :
    ⦃fun s => ⌜s = s₀⌝⦄ renameGet k
    ⦃⇓? r s' => ⌜s' = s₀ ∧ r = s₀.memos.renameC[k]?⌝⦄ := by
  mvcgen [renameGet]
  grind

/-- con-leche: ConLeche/Kernel/ExprOps.lean:999-1036 renameConstsGo — record a `renameConsts` answer. -/
@[spec] theorem renameSet_spec (s₀ : AState) (f : Nat → Expr → Expr)
    (k : EIdx × Nat) (r : EIdx) (hm : MemoOK f s₀.memos.renameC s₀.store)
    (hk : (denoteE s₀.store k.1).isSome = true)
    (hr : RelAt (f k.2) s₀.store k.1 s₀.store r) :
    ⦃fun s => ⌜s = s₀⌝⦄ renameSet k r
    ⦃⇓? _u s' => ⌜s'.store = s₀.store ∧
        s'.memos = { s₀.memos with renameC := s₀.memos.renameC.insert k r } ∧
        MemoOK f s'.memos.renameC s'.store⌝⦄ := by
  mvcgen [renameSet]
  rename_i s hs _ _
  subst hs
  exact ⟨rfl, rfl, MemoOK.insert hm hk hr⟩

/-- con-leche: ConLeche/Kernel/ExprOps.lean:1109-1111 renameConstsFast — drop the `renameConsts` memo. -/
@[spec] theorem renameClear_spec (s₀ : AState) :
    ⦃fun s => ⌜s = s₀⌝⦄ renameClear
    ⦃⇓? _u s' => ⌜s'.store = s₀.store ∧
        s'.memos = { s₀.memos with renameC := ∅ } ∧
        ∀ f, MemoOK f s'.memos.renameC s'.store⌝⦄ := by
  mvcgen [renameClear]
  exact ⟨by grind, by grind, fun f => MemoOK.of_empty rfl f⟩

/-- con-leche: ConLeche/Kernel/ExprOps.lean:1789-1833 abstract1Go — probe the `abstract1` memo. -/
@[spec] theorem abs1Get_spec (s₀ : AState) (k : EIdx × Nat) :
    ⦃fun s => ⌜s = s₀⌝⦄ abs1Get k
    ⦃⇓? r s' => ⌜s' = s₀ ∧ r = s₀.memos.abs1C[k]?⌝⦄ := by
  mvcgen [abs1Get]
  grind

/-- con-leche: ConLeche/Kernel/ExprOps.lean:1789-1833 abstract1Go — record a `abstract1` answer. -/
@[spec] theorem abs1Set_spec (s₀ : AState) (f : Nat → Expr → Expr)
    (k : EIdx × Nat) (r : EIdx) (hm : MemoOK f s₀.memos.abs1C s₀.store)
    (hk : (denoteE s₀.store k.1).isSome = true)
    (hr : RelAt (f k.2) s₀.store k.1 s₀.store r) :
    ⦃fun s => ⌜s = s₀⌝⦄ abs1Set k r
    ⦃⇓? _u s' => ⌜s'.store = s₀.store ∧
        s'.memos = { s₀.memos with abs1C := s₀.memos.abs1C.insert k r } ∧
        MemoOK f s'.memos.abs1C s'.store⌝⦄ := by
  mvcgen [abs1Set]
  rename_i s hs _ _
  subst hs
  exact ⟨rfl, rfl, MemoOK.insert hm hk hr⟩

/-- con-leche: ConLeche/Kernel/ExprOps.lean:1927-1929 abstract1Fast — drop the `abstract1` memo. -/
@[spec] theorem abs1Clear_spec (s₀ : AState) :
    ⦃fun s => ⌜s = s₀⌝⦄ abs1Clear
    ⦃⇓? _u s' => ⌜s'.store = s₀.store ∧
        s'.memos = { s₀.memos with abs1C := ∅ } ∧
        ∀ f, MemoOK f s'.memos.abs1C s'.store⌝⦄ := by
  mvcgen [abs1Clear]
  exact ⟨by grind, by grind, fun f => MemoOK.of_empty rfl f⟩

/-- con-leche: ConLeche/Kernel/ExprOps.lean:2012-2049 lowerBVarsGo — probe the `lowerBVars` memo. -/
@[spec] theorem lowerGet_spec (s₀ : AState) (k : EIdx × Nat) :
    ⦃fun s => ⌜s = s₀⌝⦄ lowerGet k
    ⦃⇓? r s' => ⌜s' = s₀ ∧ r = s₀.memos.lowerC[k]?⌝⦄ := by
  mvcgen [lowerGet]
  grind

/-- con-leche: ConLeche/Kernel/ExprOps.lean:2012-2049 lowerBVarsGo — record a `lowerBVars` answer. -/
@[spec] theorem lowerSet_spec (s₀ : AState) (f : Nat → Expr → Expr)
    (k : EIdx × Nat) (r : EIdx) (hm : MemoOK f s₀.memos.lowerC s₀.store)
    (hk : (denoteE s₀.store k.1).isSome = true)
    (hr : RelAt (f k.2) s₀.store k.1 s₀.store r) :
    ⦃fun s => ⌜s = s₀⌝⦄ lowerSet k r
    ⦃⇓? _u s' => ⌜s'.store = s₀.store ∧
        s'.memos = { s₀.memos with lowerC := s₀.memos.lowerC.insert k r } ∧
        MemoOK f s'.memos.lowerC s'.store⌝⦄ := by
  mvcgen [lowerSet]
  rename_i s hs _ _
  subst hs
  exact ⟨rfl, rfl, MemoOK.insert hm hk hr⟩

/-- con-leche: ConLeche/Kernel/ExprOps.lean:2144-2146 lowerBVarsFast — drop the `lowerBVars` memo. -/
@[spec] theorem lowerClear_spec (s₀ : AState) :
    ⦃fun s => ⌜s = s₀⌝⦄ lowerClear
    ⦃⇓? _u s' => ⌜s'.store = s₀.store ∧
        s'.memos = { s₀.memos with lowerC := ∅ } ∧
        ∀ f, MemoOK f s'.memos.lowerC s'.store⌝⦄ := by
  mvcgen [lowerClear]
  exact ⟨by grind, by grind, fun f => MemoOK.of_empty rfl f⟩

/-- con-leche: ConLeche/Kernel/ExprOps.lean:2222-2261 instantiate1LiftGo — probe the `instantiate1Lift` memo. -/
@[spec] theorem inst1LGet_spec (s₀ : AState) (k : EIdx × Nat) :
    ⦃fun s => ⌜s = s₀⌝⦄ inst1LGet k
    ⦃⇓? r s' => ⌜s' = s₀ ∧ r = s₀.memos.inst1LC[k]?⌝⦄ := by
  mvcgen [inst1LGet]
  grind

/-- con-leche: ConLeche/Kernel/ExprOps.lean:2222-2261 instantiate1LiftGo — record a `instantiate1Lift` answer. -/
@[spec] theorem inst1LSet_spec (s₀ : AState) (f : Nat → Expr → Expr)
    (k : EIdx × Nat) (r : EIdx) (hm : MemoOK f s₀.memos.inst1LC s₀.store)
    (hk : (denoteE s₀.store k.1).isSome = true)
    (hr : RelAt (f k.2) s₀.store k.1 s₀.store r) :
    ⦃fun s => ⌜s = s₀⌝⦄ inst1LSet k r
    ⦃⇓? _u s' => ⌜s'.store = s₀.store ∧
        s'.memos = { s₀.memos with inst1LC := s₀.memos.inst1LC.insert k r } ∧
        MemoOK f s'.memos.inst1LC s'.store⌝⦄ := by
  mvcgen [inst1LSet]
  rename_i s hs _ _
  subst hs
  exact ⟨rfl, rfl, MemoOK.insert hm hk hr⟩

/-- con-leche: ConLeche/Kernel/ExprOps.lean:2356-2358 instantiate1LiftFast — drop the `instantiate1Lift` memo. -/
@[spec] theorem inst1LClear_spec (s₀ : AState) :
    ⦃fun s => ⌜s = s₀⌝⦄ inst1LClear
    ⦃⇓? _u s' => ⌜s'.store = s₀.store ∧
        s'.memos = { s₀.memos with inst1LC := ∅ } ∧
        ∀ f, MemoOK f s'.memos.inst1LC s'.store⌝⦄ := by
  mvcgen [inst1LClear]
  exact ⟨by grind, by grind, fun f => MemoOK.of_empty rfl f⟩

/-- con-leche: ConLeche/Kernel/ExprOps.lean:2564-2603 Expr.instLPGo — probe the `instantiateLevelParams` memo. -/
@[spec] theorem instLPGet_spec (s₀ : AState) (k : EIdx × Nat) :
    ⦃fun s => ⌜s = s₀⌝⦄ instLPGet k
    ⦃⇓? r s' => ⌜s' = s₀ ∧ r = s₀.memos.instLPC[k]?⌝⦄ := by
  mvcgen [instLPGet]
  grind

/-- con-leche: ConLeche/Kernel/ExprOps.lean:2564-2603 Expr.instLPGo — record a `instantiateLevelParams` answer. -/
@[spec] theorem instLPSet_spec (s₀ : AState) (f : Nat → Expr → Expr)
    (k : EIdx × Nat) (r : EIdx) (hm : MemoOK f s₀.memos.instLPC s₀.store)
    (hk : (denoteE s₀.store k.1).isSome = true)
    (hr : RelAt (f k.2) s₀.store k.1 s₀.store r) :
    ⦃fun s => ⌜s = s₀⌝⦄ instLPSet k r
    ⦃⇓? _u s' => ⌜s'.store = s₀.store ∧
        s'.memos = { s₀.memos with instLPC := s₀.memos.instLPC.insert k r } ∧
        MemoOK f s'.memos.instLPC s'.store⌝⦄ := by
  mvcgen [instLPSet]
  rename_i s hs _ _
  subst hs
  exact ⟨rfl, rfl, MemoOK.insert hm hk hr⟩

/-- con-leche: ConLeche/Kernel/ExprOps.lean:2718-2720 Expr.instLPFast — drop the `instantiateLevelParams` memo. -/
@[spec] theorem instLPClear_spec (s₀ : AState) :
    ⦃fun s => ⌜s = s₀⌝⦄ instLPClear
    ⦃⇓? _u s' => ⌜s'.store = s₀.store ∧
        s'.memos = { s₀.memos with instLPC := ∅ } ∧
        ∀ f, MemoOK f s'.memos.instLPC s'.store⌝⦄ := by
  mvcgen [instLPClear]
  exact ⟨by grind, by grind, fun f => MemoOK.of_empty rfl f⟩

/-- con-leche: ConLeche/Kernel/ExprOps.lean:1368-1392 bvarBoundGo — probe the `bvarBound` memo. -/
@[spec] theorem bvarBGet_spec (s₀ : AState) (k : EIdx) :
    ⦃fun s => ⌜s = s₀⌝⦄ bvarBGet k
    ⦃⇓? r s' => ⌜s' = s₀ ∧ r = s₀.memos.bvarBC[k]?⌝⦄ := by
  mvcgen [bvarBGet]
  grind

/-- con-leche: ConLeche/Kernel/ExprOps.lean:1368-1392 bvarBoundGo — record a `bvarBound` answer. -/
@[spec] theorem bvarBSet_spec (s₀ : AState) (f : Expr → Nat) (k : EIdx) (r : Nat)
    (e : Expr) (hm : MemoNOK f s₀.memos.bvarBC s₀.store)
    (he : denoteE s₀.store k = some e) (hr : r = f e) :
    ⦃fun s => ⌜s = s₀⌝⦄ bvarBSet k r
    ⦃⇓? _u s' => ⌜s'.store = s₀.store ∧
        s'.memos = { s₀.memos with bvarBC := s₀.memos.bvarBC.insert k r } ∧
        MemoNOK f s'.memos.bvarBC s'.store⌝⦄ := by
  mvcgen [bvarBSet]
  rename_i s hs _ _
  subst hs
  exact ⟨rfl, rfl, MemoNOK.insert hm he hr⟩

/-- con-leche: ConLeche/Kernel/ExprOps.lean:1394-1395 bvarBoundMemo — drop the `bvarBound` memo. -/
@[spec] theorem bvarBClear_spec (s₀ : AState) :
    ⦃fun s => ⌜s = s₀⌝⦄ bvarBClear
    ⦃⇓? _u s' => ⌜s'.store = s₀.store ∧
        s'.memos = { s₀.memos with bvarBC := ∅ } ∧
        ∀ f, MemoNOK f s'.memos.bvarBC s'.store⌝⦄ := by
  mvcgen [bvarBClear]
  exact ⟨by grind, by grind, fun f => MemoNOK.of_empty rfl f⟩

/-- con-leche: ConLeche/Kernel/ExprOps.lean:1397-1422 fvarRangeGo — probe the `fvarRange` memo. -/
@[spec] theorem fvarBGet_spec (s₀ : AState) (k : EIdx) :
    ⦃fun s => ⌜s = s₀⌝⦄ fvarBGet k
    ⦃⇓? r s' => ⌜s' = s₀ ∧ r = s₀.memos.fvarBC[k]?⌝⦄ := by
  mvcgen [fvarBGet]
  grind

/-- con-leche: ConLeche/Kernel/ExprOps.lean:1397-1422 fvarRangeGo — record a `fvarRange` answer. -/
@[spec] theorem fvarBSet_spec (s₀ : AState) (f : Expr → Nat) (k : EIdx) (r : Nat)
    (e : Expr) (hm : MemoNOK f s₀.memos.fvarBC s₀.store)
    (he : denoteE s₀.store k = some e) (hr : r = f e) :
    ⦃fun s => ⌜s = s₀⌝⦄ fvarBSet k r
    ⦃⇓? _u s' => ⌜s'.store = s₀.store ∧
        s'.memos = { s₀.memos with fvarBC := s₀.memos.fvarBC.insert k r } ∧
        MemoNOK f s'.memos.fvarBC s'.store⌝⦄ := by
  mvcgen [fvarBSet]
  rename_i s hs _ _
  subst hs
  exact ⟨rfl, rfl, MemoNOK.insert hm he hr⟩

/-- con-leche: ConLeche/Kernel/ExprOps.lean:1424-1425 fvarRangeMemo — drop the `fvarRange` memo. -/
@[spec] theorem fvarBClear_spec (s₀ : AState) :
    ⦃fun s => ⌜s = s₀⌝⦄ fvarBClear
    ⦃⇓? _u s' => ⌜s'.store = s₀.store ∧
        s'.memos = { s₀.memos with fvarBC := ∅ } ∧
        ∀ f, MemoNOK f s'.memos.fvarBC s'.store⌝⦄ := by
  mvcgen [fvarBClear]
  exact ⟨by grind, by grind, fun f => MemoNOK.of_empty rfl f⟩


end ConRon.Arena
