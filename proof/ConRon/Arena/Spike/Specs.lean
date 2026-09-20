/-
# The P2s spike: the `@[spec]` layer

Experiment A's infrastructure, and the thing the spike is really for: **one
spec theorem per store primitive**, in one shape, so that `mvcgen` can walk a
(B) body without any store reasoning appearing in the proof text.

The shape — the template DESIGN §8.6 asks the spike to fix for P2b–P2d:

```lean
@[spec] theorem f_spec (s₀ : AState) (args…) (pre…) :
    ⦃fun s => ⌜s = s₀⌝⦄ f args ⦃⇓? r s' => ⌜Post s₀ r s'⌝⦄
```

* the precondition is `s = s₀` **and nothing else** — every real
  precondition is an ordinary hypothesis of the theorem, so `mspec` turns it
  into a side goal instead of an entailment to discharge in the logic;
* the postcondition is `⇓?` (partial correctness): a (B) function may fail,
  and Theorem 1 claims nothing then — con-leche's `SimAt` shape
  (`Verify/SimI.lean:244`) exactly.  `⇓` (total correctness) would force
  every proof to rule out `fail`, which the bridge never does;
* the postcondition names `s₀`, which is the only way to get
  `Ext s₀.store s'.store` into a Hoare triple at all — `mspec` instantiates
  `s₀` by `mintro ∀s` at the call site, which is exactly the documented
  behaviour for a schematic pre of this shape.

`AM.of_run` is the one soundness step at the top: it turns the triple back
into the `c s₀ = .ok (v', s') → …` statement Theorem 1 is written as.
-/
import ConRon.Arena.Spike.Twins

namespace ConRon.Arena.Spike

open ConLeche Std.Do

set_option mvcgen.warning false

/-! ## Soundness: from the triple back to a run -/

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

/-! ## The transport lemmas

Two facts; after them no proof below ever unfolds `denoteE`. -/

/-- con-leche: ConLeche/Verify/SimI.lean:244 SimAt (the `Ext` conjunct) — a
denotation survives every arena extension.  This is `Ext.expr` under the name
the spike proofs use; registered for `grind` so that the residue after
`mvcgen` is discharged without naming it. -/
@[grind →] theorem denote_ext {st st' : EStore} {h : EIdx} {e : Expr}
    (hd : denoteE st h = some e) (hx : Ext st st') : denoteE st' h = some e :=
  hx.expr h e hd

/-- con-leche: ConLeche/Verify/SimI.lean:244 SimAt — the same for a *name*
handle: `Ext` carries the three nested stores too. -/
@[grind →] theorem denoteN_ext {st st' : EStore} {c : NIdx} {x : ConLeche.Name}
    (hd : denoteN st.ns c = some x) (hx : Ext st st') : denoteN st'.ns c = some x :=
  hx.lss.ls.ns c x hd

/-- con-leche: none — a denoting handle has a view; this is what discharges
`intern`'s `ViewOK` at a node whose children denote. -/
theorem view_isSome_of_denote {st : EStore} {h : EIdx} {e : Expr}
    (hd : denoteE st h = some e) : (st.view h).isSome = true := by
  obtain ⟨v, hv⟩ := denoteE_view hd
  rw [hv]; rfl

/-! ## The denote-inversion layer

Ten lemmas, one per constructor — the *only* place the spike unfolds
`denoteE`.  Each says: given the handle's view, the denoted term has the
matching shape and the children denote.  `mvcgen` hands the view as a branch
condition, so one `obtain` per branch puts the children's denotations in
context and everything after is pure.  (con-leche's `Verify/Disc.lean` is the
same layer, site by site.) -/

/-- con-leche: none — trade the fuel for the rank once, at the top of each
inversion. -/
theorem denoteE_view_eq {st : EStore} (hwf : StoreWF st) {h : EIdx}
    {w : ENodeView} (hw : st.view h = some w) : denoteE st h = denoteEView st w := by
  obtain ⟨rk, hr⟩ := hwf; exact denoteE_unfold hr hw

theorem denote_bvar_inv {st : EStore} (hwf : StoreWF st) {h : EIdx} {i : Nat}
    {e : Expr} (hw : st.view h = some (.bvar i)) (he : denoteE st h = some e) :
    e = .bvar i := by
  rw [denoteE_view_eq hwf hw, denoteEView] at he; exact (Option.some.inj he).symm

theorem denote_fvar_inv {st : EStore} (hwf : StoreWF st) {h : EIdx} {k : Nat}
    {ty : EIdx} {e : Expr} (hw : st.view h = some (.fvar k ty))
    (he : denoteE st h = some e) : ∃ t, e = .fvar k t ∧ denoteE st ty = some t := by
  rw [denoteE_view_eq hwf hw, denoteEView, Option.map_eq_some_iff] at he
  obtain ⟨t, ht, rfl⟩ := he; exact ⟨t, rfl, ht⟩

theorem denote_sort_inv {st : EStore} (hwf : StoreWF st) {h : EIdx} {u : LIdx}
    {e : Expr} (hw : st.view h = some (.sort u)) (he : denoteE st h = some e) :
    ∃ l, e = .sort l := by
  rw [denoteE_view_eq hwf hw, denoteEView, Option.map_eq_some_iff] at he
  obtain ⟨l, _, rfl⟩ := he; exact ⟨l, rfl⟩

theorem denote_const_inv {st : EStore} (hwf : StoreWF st) {h : EIdx} {n : NIdx}
    {us : LsIdx} {e : Expr} (hw : st.view h = some (.const n us))
    (he : denoteE st h = some e) : ∃ nm ls, e = .const nm ls := by
  rw [denoteE_view_eq hwf hw, denoteEView, opt2_eq_some_iff] at he
  obtain ⟨nm, ls, _, _, rfl⟩ := he; exact ⟨nm, ls, rfl⟩

theorem denote_lit_inv {st : EStore} (hwf : StoreWF st) {h : EIdx} {l : Literal}
    {e : Expr} (hw : st.view h = some (.lit l)) (he : denoteE st h = some e) :
    e = .lit l := by
  rw [denoteE_view_eq hwf hw, denoteEView] at he; exact (Option.some.inj he).symm

theorem denote_app_inv {st : EStore} (hwf : StoreWF st) {h f a : EIdx} {e : Expr}
    (hw : st.view h = some (.app f a)) (he : denoteE st h = some e) :
    ∃ ef ea, e = .app ef ea ∧ denoteE st f = some ef ∧ denoteE st a = some ea := by
  rw [denoteE_view_eq hwf hw, denoteEView, opt2_eq_some_iff] at he
  obtain ⟨x, y, hx, hy, rfl⟩ := he; exact ⟨x, y, rfl, hx, hy⟩

theorem denote_lam_inv {st : EStore} (hwf : StoreWF st) {h ty b : EIdx}
    {m : BinderMeta} {e : Expr} (hw : st.view h = some (.lam ty b m))
    (he : denoteE st h = some e) :
    ∃ et eb, e = .lam et eb m ∧ denoteE st ty = some et ∧ denoteE st b = some eb := by
  rw [denoteE_view_eq hwf hw, denoteEView, opt2_eq_some_iff] at he
  obtain ⟨x, y, hx, hy, rfl⟩ := he; exact ⟨x, y, rfl, hx, hy⟩

theorem denote_forallE_inv {st : EStore} (hwf : StoreWF st) {h ty b : EIdx}
    {m : BinderMeta} {e : Expr} (hw : st.view h = some (.forallE ty b m))
    (he : denoteE st h = some e) :
    ∃ et eb, e = .forallE et eb m ∧ denoteE st ty = some et ∧ denoteE st b = some eb := by
  rw [denoteE_view_eq hwf hw, denoteEView, opt2_eq_some_iff] at he
  obtain ⟨x, y, hx, hy, rfl⟩ := he; exact ⟨x, y, rfl, hx, hy⟩

theorem denote_letE_inv {st : EStore} (hwf : StoreWF st) {h ty w b : EIdx}
    {e : Expr} (hw : st.view h = some (.letE ty w b)) (he : denoteE st h = some e) :
    ∃ et ew eb, e = .letE et ew eb ∧ denoteE st ty = some et ∧
      denoteE st w = some ew ∧ denoteE st b = some eb := by
  rw [denoteE_view_eq hwf hw, denoteEView, opt3_eq_some_iff] at he
  obtain ⟨x, y, z, hx, hy, hz, rfl⟩ := he; exact ⟨x, y, z, rfl, hx, hy, hz⟩

theorem denote_proj_inv {st : EStore} (hwf : StoreWF st) {h : EIdx} {n : NIdx}
    {i : Nat} {sub : EIdx} {e : Expr} (hw : st.view h = some (.proj n i sub))
    (he : denoteE st h = some e) :
    ∃ nm es, e = .proj nm i es ∧ denoteN st.ns n = some nm ∧ denoteE st sub = some es := by
  rw [denoteE_view_eq hwf hw, denoteEView, opt2_eq_some_iff] at he
  obtain ⟨x, y, hx, hy, rfl⟩ := he; exact ⟨x, y, rfl, hx, hy⟩

/-! ## The `isSome` calculus

A (B) function's *precondition* is "this handle denotes" — `isSome`, with no
`Expr` in it, so that a recursive call's side goal carries **no
metavariable**.  (The spike's first shape made the denoted term an argument;
every recursive call then left `denoteE s.store f = some ?e` for the user to
solve, and `grind` cannot invent `?e`.)  These five lemmas push `isSome` down
a node and along an extension, which is all the automation needs. -/

/-- con-leche: none — `isSome` survives an arena extension. -/
@[grind →] theorem denote_isSome_ext {st st' : EStore} {c : EIdx}
    (hs : (denoteE st c).isSome = true) (hx : Ext st st') :
    (denoteE st' c).isSome = true := by
  obtain ⟨e, he⟩ := Option.isSome_iff_exists.mp hs
  rw [denote_ext he hx]; rfl

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

@[grind →] theorem isSome_forallE {st : EStore} (hwf : StoreWF st) {h ty b : EIdx}
    {m : BinderMeta} (hw : st.view h = some (.forallE ty b m))
    (hs : (denoteE st h).isSome = true) :
    (denoteE st ty).isSome = true ∧ (denoteE st b).isSome = true := by
  obtain ⟨e, he⟩ := Option.isSome_iff_exists.mp hs
  obtain ⟨x, y, _, hx, hy⟩ := denote_forallE_inv hwf hw he
  exact ⟨by rw [hx]; rfl, by rw [hy]; rfl⟩

@[grind →] theorem isSome_letE {st : EStore} (hwf : StoreWF st) {h ty w b : EIdx}
    (hw : st.view h = some (.letE ty w b)) (hs : (denoteE st h).isSome = true) :
    (denoteE st ty).isSome = true ∧ (denoteE st w).isSome = true ∧
      (denoteE st b).isSome = true := by
  obtain ⟨e, he⟩ := Option.isSome_iff_exists.mp hs
  obtain ⟨x, y, z, _, hx, hy, hz⟩ := denote_letE_inv hwf hw he
  exact ⟨by rw [hx]; rfl, by rw [hy]; rfl, by rw [hz]; rfl⟩

@[grind →] theorem isSome_proj {st : EStore} (hwf : StoreWF st) {h : EIdx}
    {n : NIdx} {i : Nat} {sub : EIdx} (hw : st.view h = some (.proj n i sub))
    (hs : (denoteE st h).isSome = true) : (denoteE st sub).isSome = true := by
  obtain ⟨e, he⟩ := Option.isSome_iff_exists.mp hs
  obtain ⟨x, y, _, _, hy⟩ := denote_proj_inv hwf hw he
  rw [hy]; rfl

/-- con-leche: none — the conditional postcondition, applied: if the input
denotes, so does the output. -/
theorem isSome_of_cond {st st' : EStore} {c r : EIdx} {ve : Expr}
    {d : Nat} (hs : (denoteE st c).isSome = true)
    (hp : ∀ e, denoteE st c = some e → denoteE st' r = some (e.instantiate1 ve d)) :
    (denoteE st' r).isSome = true := by
  obtain ⟨e, he⟩ := Option.isSome_iff_exists.mp hs
  rw [hp e he]; rfl

/-! ## The `isSome`-flavoured inversions — the form `grind` can use

The same ten facts as above, but stated so that the *view* is the ematch
pattern and the denotation is a conclusion rather than a hypothesis.  This is
what makes the uniform closer work: `mvcgen` hands each branch its view, and
these fire on it. -/

@[grind →] theorem denote_eq_bvar {st : EStore} (hwf : StoreWF st) {h : EIdx}
    {i : Nat} (hw : st.view h = some (.bvar i)) (hs : (denoteE st h).isSome = true) :
    denoteE st h = some (.bvar i) := by
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
    {u : LIdx} (hw : st.view h = some (.sort u)) (hs : (denoteE st h).isSome = true) :
    ∃ l, denoteE st h = some (.sort l) := by
  obtain ⟨e, he⟩ := Option.isSome_iff_exists.mp hs
  obtain ⟨l, rfl⟩ := denote_sort_inv hwf hw he
  exact ⟨l, he⟩

@[grind →] theorem denote_eq_const {st : EStore} (hwf : StoreWF st) {h : EIdx}
    {n : NIdx} {us : LsIdx} (hw : st.view h = some (.const n us))
    (hs : (denoteE st h).isSome = true) :
    ∃ nm ls, denoteE st h = some (.const nm ls) := by
  obtain ⟨e, he⟩ := Option.isSome_iff_exists.mp hs
  obtain ⟨nm, ls, rfl⟩ := denote_const_inv hwf hw he
  exact ⟨nm, ls, he⟩

@[grind →] theorem denote_eq_lit {st : EStore} (hwf : StoreWF st) {h : EIdx}
    {l : Literal} (hw : st.view h = some (.lit l)) (hs : (denoteE st h).isSome = true) :
    denoteE st h = some (.lit l) := by
  obtain ⟨e, he⟩ := Option.isSome_iff_exists.mp hs
  rw [he, denote_lit_inv hwf hw he]

@[grind →] theorem denote_eq_app {st : EStore} (hwf : StoreWF st) {h f a : EIdx}
    (hw : st.view h = some (.app f a)) (hs : (denoteE st h).isSome = true) :
    ∃ ef ea, denoteE st h = some (.app ef ea) ∧
      denoteE st f = some ef ∧ denoteE st a = some ea := by
  obtain ⟨e, he⟩ := Option.isSome_iff_exists.mp hs
  obtain ⟨x, y, rfl, hx, hy⟩ := denote_app_inv hwf hw he
  exact ⟨x, y, he, hx, hy⟩

@[grind →] theorem denote_eq_lam {st : EStore} (hwf : StoreWF st) {h ty b : EIdx}
    {m : BinderMeta} (hw : st.view h = some (.lam ty b m))
    (hs : (denoteE st h).isSome = true) :
    ∃ et eb, denoteE st h = some (.lam et eb m) ∧
      denoteE st ty = some et ∧ denoteE st b = some eb := by
  obtain ⟨e, he⟩ := Option.isSome_iff_exists.mp hs
  obtain ⟨x, y, rfl, hx, hy⟩ := denote_lam_inv hwf hw he
  exact ⟨x, y, he, hx, hy⟩

@[grind →] theorem denote_eq_forallE {st : EStore} (hwf : StoreWF st) {h ty b : EIdx}
    {m : BinderMeta} (hw : st.view h = some (.forallE ty b m))
    (hs : (denoteE st h).isSome = true) :
    ∃ et eb, denoteE st h = some (.forallE et eb m) ∧
      denoteE st ty = some et ∧ denoteE st b = some eb := by
  obtain ⟨e, he⟩ := Option.isSome_iff_exists.mp hs
  obtain ⟨x, y, rfl, hx, hy⟩ := denote_forallE_inv hwf hw he
  exact ⟨x, y, he, hx, hy⟩

@[grind →] theorem denote_eq_letE {st : EStore} (hwf : StoreWF st) {h ty w b : EIdx}
    (hw : st.view h = some (.letE ty w b)) (hs : (denoteE st h).isSome = true) :
    ∃ et ew eb, denoteE st h = some (.letE et ew eb) ∧ denoteE st ty = some et ∧
      denoteE st w = some ew ∧ denoteE st b = some eb := by
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

/-! ## The answer relation

The conditional postcondition, **named**.  Writing it as a bare
`∀ e, denoteE st c = some e → …` costs the automation dearly: a `∀`-hypothesis
has no head symbol, so `grind` cannot ematch on it and every use has to be
supplied by hand.  Behind a `def` it has one, and the two eliminators below
carry every use. -/

/-- con-leche: ConLeche/Verify/SimI.lean:250 RelE — "`r` in `st'` is what
`instantiate1` makes of `c` in `st`, at cursor `d`". -/
def Inst1At (ve : Expr) (d : Nat) (st : EStore) (c : EIdx) (st' : EStore) (r : EIdx) :
    Prop :=
  ∀ e, denoteE st c = some e → denoteE st' r = some (e.instantiate1 ve d)

@[grind →] theorem Inst1At.apply {ve : Expr} {d : Nat} {st st' : EStore} {c r : EIdx}
    {e : Expr} (h : Inst1At ve d st c st' r) (he : denoteE st c = some e) :
    denoteE st' r = some (e.instantiate1 ve d) := h e he

@[grind →] theorem Inst1At.isSome {ve : Expr} {d : Nat} {st st' : EStore} {c r : EIdx}
    (h : Inst1At ve d st c st' r) (hs : (denoteE st c).isSome = true) :
    (denoteE st' r).isSome = true := by
  obtain ⟨e, he⟩ := Option.isSome_iff_exists.mp hs
  rw [h e he]; rfl

/-- con-leche: none — the answer travels forward with the arena. -/
@[grind →] theorem Inst1At.ext {ve : Expr} {d : Nat} {st st' st'' : EStore} {c r : EIdx}
    (h : Inst1At ve d st c st' r) (hx : Ext st' st'') : Inst1At ve d st c st'' r :=
  fun e he => denote_ext (h e he) hx

/-- con-leche: none — **retarget the source store**.  The answer relation was
established against the store the call started in; the memo records it against
the store the call ended in.  They agree because `denoteE` is a function and
`Ext` transports the input's denotation forward.  This is the one lemma that
is invisible in con-leche's tree-shaped proof and unavoidable here. -/
@[grind →] theorem Inst1At.retarget {ve : Expr} {d : Nat} {st st0 st' : EStore}
    {c r : EIdx} (h : Inst1At ve d st c st' r) (hx : Ext st st0)
    (hs : (denoteE st c).isSome = true) : Inst1At ve d st0 c st' r := by
  intro e he
  obtain ⟨e0, he0⟩ := Option.isSome_iff_exists.mp hs
  have hh := denote_ext he0 hx
  rw [he] at hh
  rw [Option.some.inj hh]
  exact h e0 he0

/-- con-leche: none — and backward along an extension of the *source*. -/
@[grind →] theorem Inst1At.of_ext {ve : Expr} {d : Nat} {st st0 st' : EStore}
    {c r : EIdx} (h : Inst1At ve d st c st' r) (hx : Ext st0 st) :
    Inst1At ve d st0 c st' r :=
  fun e he => h e (denote_ext he hx)

/-- con-leche: ConLeche/Kernel/ExprOps.lean:1454 bvarBRaw_exact — **the
derived-word cutoff**, packaged as one step lemma.  Left as three separate
hints (`EStore.derived_exact`, `Expr.bvarBRaw`, `instantiate1_of_raw_le`) it
sends `grind` into an ematching spiral on
`((ve.instantiate1 ve d).instantiate1 ve d)…`; as one lemma with the store
read as its pattern it fires once. -/
theorem Inst1At.cutoff {st : EStore} (hwf : StoreWF st) {h : EIdx}
    {d : Nat} {ve : Expr}
    (hsat : (bvarOfData (st.derived h)).toNat < satRange)
    (hle : (bvarOfData (st.derived h)).toNat ≤ d) : Inst1At ve d st h st h := by
  intro e he
  have hd := EStore.derived_exact hwf he
  rw [hd] at hsat hle
  rw [instantiate1_of_raw_le hsat hle]
  exact he

/-- con-leche: none — two extensions at once.  `grind` chains `Ext.trans`
and `Inst1At.ext` only when it has the budget for two nested
instantiations; the composite fires in one. -/
theorem Inst1At.ext2 {ve : Expr} {d : Nat} {st a b c : EStore}
    {x r : EIdx} (h : Inst1At ve d st x a r) (h1 : Ext a b) (h2 : Ext b c) :
    Inst1At ve d st x c r := (h.ext h1).ext h2

/-- con-leche: none — retarget the source and extend the target in one step:
the shape every *second* child of a node needs, because its answer was
established against the store the first child's call left behind. -/
theorem Inst1At.back_ext {ve : Expr} {d : Nat} {st st1 a b : EStore}
    {x r : EIdx} (h : Inst1At ve d st1 x a r) (h0 : Ext st st1) (h1 : Ext a b) :
    Inst1At ve d st x b r := (h.of_ext h0).ext h1

/-- con-leche: none — and with two extensions after the retarget (the third
child of `letE`). -/
theorem Inst1At.back_ext2 {ve : Expr} {d : Nat} {st st1 a b c : EStore}
    {x r : EIdx} (h : Inst1At ve d st1 x a r) (h0 : Ext st st1) (h1 : Ext a b)
    (h2 : Ext b c) : Inst1At ve d st x c r := ((h.of_ext h0).ext h1).ext h2

/-! ## The per-site step lemmas

One per branching constructor: "the children's answers, interned, are the
parent's answer".  This is con-leche's `Verify/Disc.lean` layer — one lemma
per *site* of the body — and it is the piece `grind` cannot invent, because it
is where the pure equation `instantiate1 (.app f a) v d = .app (…) (…)` meets
the store.  Five lemmas, six lines each. -/

theorem Inst1At.app {ve : Expr} {d : Nat} {st st' : EStore}
    {h f a rf ra r : EIdx} (hwf : StoreWF st) (hview : st.view h = some (.app f a))
    (hf : Inst1At ve d st f st' rf) (ha : Inst1At ve d st a st' ra)
    (hr : denoteE st' r = denoteEView st' (.app rf ra)) :
    Inst1At ve d st h st' r := by
  intro e he
  obtain ⟨ef, ea, rfl, hdf, hda⟩ := denote_app_inv hwf hview he
  rw [hr, denoteEView, hf ef hdf, ha ea hda]; rfl

theorem Inst1At.lam {ve : Expr} {d : Nat} {st st' : EStore}
    {h ty b rt rb r : EIdx} {m : BinderMeta} (hwf : StoreWF st)
    (hview : st.view h = some (.lam ty b m))
    (ht : Inst1At ve d st ty st' rt) (hb : Inst1At ve (d + 1) st b st' rb)
    (hr : denoteE st' r = denoteEView st' (.lam rt rb m)) :
    Inst1At ve d st h st' r := by
  intro e he
  obtain ⟨et, eb, rfl, hdt, hdb⟩ := denote_lam_inv hwf hview he
  rw [hr, denoteEView, ht et hdt, hb eb hdb]; rfl

theorem Inst1At.forallE {ve : Expr} {d : Nat} {st st' : EStore}
    {h ty b rt rb r : EIdx} {m : BinderMeta} (hwf : StoreWF st)
    (hview : st.view h = some (.forallE ty b m))
    (ht : Inst1At ve d st ty st' rt) (hb : Inst1At ve (d + 1) st b st' rb)
    (hr : denoteE st' r = denoteEView st' (.forallE rt rb m)) :
    Inst1At ve d st h st' r := by
  intro e he
  obtain ⟨et, eb, rfl, hdt, hdb⟩ := denote_forallE_inv hwf hview he
  rw [hr, denoteEView, ht et hdt, hb eb hdb]; rfl

theorem Inst1At.letE {ve : Expr} {d : Nat} {st st' : EStore}
    {h ty w b rt rw rb r : EIdx} (hwf : StoreWF st)
    (hview : st.view h = some (.letE ty w b))
    (ht : Inst1At ve d st ty st' rt) (hw : Inst1At ve d st w st' rw)
    (hb : Inst1At ve (d + 1) st b st' rb)
    (hr : denoteE st' r = denoteEView st' (.letE rt rw rb)) :
    Inst1At ve d st h st' r := by
  intro e he
  obtain ⟨et, ew, eb, rfl, hdt, hdw, hdb⟩ := denote_letE_inv hwf hview he
  rw [hr, denoteEView, ht et hdt, hw ew hdw, hb eb hdb]; rfl

theorem Inst1At.proj {ve : Expr} {d : Nat} {st st' : EStore}
    {h sub rs r : EIdx} {n : NIdx} {i : Nat} (hwf : StoreWF st)
    (hview : st.view h = some (.proj n i sub))
    (hs : Inst1At ve d st sub st' rs)
    (hr : denoteE st' r = denoteEView st' (.proj n i rs))
    (hn : denoteN st'.ns n = some nm) (hn0 : denoteN st.ns n = some nm) :
    Inst1At ve d st h st' r := by
  intro e he
  obtain ⟨nm', es, rfl, hdn, hds⟩ := denote_proj_inv hwf hview he
  rw [hr, denoteEView, hs es hds, hn]
  rw [hn0] at hdn
  rw [Option.some.inj hdn]; rfl

/-! ## The per-site step lemmas, as the verification condition presents them

The lemmas above are the *mathematical* content; these are the same facts with
their hypotheses in the shape `mvcgen` actually produces — the children's
answers stated against the store each call *started* in, and the extension
chain spelled out.  Composing `of_ext`/`ext`/`trans` on the fly costs `grind`
three nested instantiations and it does not find them; with the chain inside
the lemma each verification condition is one ematch. -/

@[grind →] theorem Inst1At.app_step {ve : Expr} {d : Nat} {st s1 s2 s3 : EStore}
    {h f a rf ra r : EIdx} (hwf : StoreWF st) (hview : st.view h = some (.app f a))
    (hx1 : Ext st s1) (hf : Inst1At ve d st f s1 rf)
    (hx2 : Ext s1 s2) (ha : Inst1At ve d s1 a s2 ra)
    (hx3 : Ext s2 s3)
    (hr : denoteE s3 r = denoteEView s3 (.app rf ra)) : Inst1At ve d st h s3 r :=
  Inst1At.app hwf hview ((hf.ext hx2).ext hx3) ((ha.of_ext hx1).ext hx3) hr

@[grind →] theorem Inst1At.lam_step {ve : Expr} {d : Nat} {st s1 s2 s3 : EStore}
    {h ty b rt rb r : EIdx} {m : BinderMeta} (hwf : StoreWF st)
    (hview : st.view h = some (.lam ty b m))
    (hx1 : Ext st s1) (ht : Inst1At ve d st ty s1 rt)
    (hx2 : Ext s1 s2) (hb : Inst1At ve (d + 1) s1 b s2 rb)
    (hx3 : Ext s2 s3)
    (hr : denoteE s3 r = denoteEView s3 (.lam rt rb m)) : Inst1At ve d st h s3 r :=
  Inst1At.lam hwf hview ((ht.ext hx2).ext hx3) ((hb.of_ext hx1).ext hx3) hr

@[grind →] theorem Inst1At.forallE_step {ve : Expr} {d : Nat} {st s1 s2 s3 : EStore}
    {h ty b rt rb r : EIdx} {m : BinderMeta} (hwf : StoreWF st)
    (hview : st.view h = some (.forallE ty b m))
    (hx1 : Ext st s1) (ht : Inst1At ve d st ty s1 rt)
    (hx2 : Ext s1 s2) (hb : Inst1At ve (d + 1) s1 b s2 rb)
    (hx3 : Ext s2 s3)
    (hr : denoteE s3 r = denoteEView s3 (.forallE rt rb m)) : Inst1At ve d st h s3 r :=
  Inst1At.forallE hwf hview ((ht.ext hx2).ext hx3) ((hb.of_ext hx1).ext hx3) hr

@[grind →] theorem Inst1At.letE_step {ve : Expr} {d : Nat} {st s1 s2 s3 s4 : EStore}
    {h ty w b rt rw rb r : EIdx} (hwf : StoreWF st)
    (hview : st.view h = some (.letE ty w b))
    (hx1 : Ext st s1) (ht : Inst1At ve d st ty s1 rt)
    (hx2 : Ext s1 s2) (hw : Inst1At ve d s1 w s2 rw)
    (hx3 : Ext s2 s3) (hb : Inst1At ve (d + 1) s2 b s3 rb)
    (hx4 : Ext s3 s4)
    (hr : denoteE s4 r = denoteEView s4 (.letE rt rw rb)) : Inst1At ve d st h s4 r :=
  Inst1At.letE hwf hview (((ht.ext hx2).ext hx3).ext hx4)
    (((hw.of_ext hx1).ext hx3).ext hx4) ((hb.of_ext (hx1.trans hx2)).ext hx4) hr

@[grind →] theorem Inst1At.proj_step {ve : Expr} {d : Nat} {st s1 s2 : EStore}
    {h sub rs r : EIdx} {n : NIdx} {i : Nat} {nm : ConLeche.Name} (hwf : StoreWF st)
    (hview : st.view h = some (.proj n i sub))
    (hx1 : Ext st s1) (hs : Inst1At ve d st sub s1 rs)
    (hx2 : Ext s1 s2)
    (hr : denoteE s2 r = denoteEView s2 (.proj n i rs))
    (hn0 : denoteN st.ns n = some nm) : Inst1At ve d st h s2 r :=
  Inst1At.proj hwf hview (hs.ext hx2) hr (denoteN_ext (denoteN_ext hn0 hx1) hx2) hn0

/-! ## The `ViewOK` layer

`internE`'s precondition, one lemma per node shape the twins build.  Each is
"the children denote, hence they have views". -/

theorem viewOK_bvar {st : EStore} {i : Nat} : st.ViewOK (.bvar i) :=
  ⟨by simp [ENodeView.echildren], by simp [ENodeView.nchildren],
   by simp [ENodeView.lchildren], by simp [ENodeView.lschildren]⟩

/-- con-leche: none — a handle that denotes has a view (the `isSome`
spelling, so nothing has to be guessed). -/
theorem view_isSome {st : EStore} {c : EIdx} (hs : (denoteE st c).isSome = true) :
    (st.view c).isSome = true := by
  obtain ⟨e, he⟩ := Option.isSome_iff_exists.mp hs
  exact view_isSome_of_denote he

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

theorem viewOK_proj {st : EStore} {n : NIdx} {i : Nat} {sub : EIdx}
    (hn : (st.ns.view n).isSome = true) (hs : (denoteE st sub).isSome = true) :
    st.ViewOK (.proj n i sub) :=
  ⟨by intro c hc; simp [ENodeView.echildren] at hc; subst hc
      exact view_isSome hs,
   by intro c hc; simp [ENodeView.nchildren] at hc; subst hc; exact hn,
   by simp [ENodeView.lchildren], by simp [ENodeView.lschildren]⟩

/-- con-leche: none — a name handle that denotes has a view. -/
@[grind →] theorem nview_isSome_of_denote {st : NStore} {c : NIdx} {x : ConLeche.Name}
    (hd : denoteN st c = some x) : (st.view c).isSome = true := by
  obtain ⟨w, hw⟩ := denoteN_view hd; rw [hw]; rfl

/-! ## The memo-invariant layer -/

/-- con-leche: ConLeche/Kernel/ExprOps.lean:62 Inst1MemoInv — the memo
survives an arena extension that leaves the table alone. -/
theorem Inst1MemoA.mono {ve : Expr} {s s' : AState} (hm : Inst1MemoA ve s)
    (hx : Ext s.store s'.store) (hc : s'.inst1C = s.inst1C) : Inst1MemoA ve s' := by
  intro k r hk
  rw [hc] at hk
  obtain ⟨e, h1, h2⟩ := hm k r hk
  exact ⟨e, denote_ext h1 hx, denote_ext h2 hx⟩

/-- con-leche: ConLeche/Kernel/ExprOps.lean:65 Inst1MemoInv.empty — the
*dropped* memo satisfies the invariant for every substituted term.  That is
why `instantiate1`'s per-call memo never appears in a caller's invariant. -/
theorem Inst1MemoA.of_empty {s : AState} (h : s.inst1C = ∅) :
    ∀ ve : Expr, Inst1MemoA ve s := by
  intro ve k r hk; rw [h] at hk; simp at hk

/-- con-leche: ConLeche/Kernel/ExprOps.lean:62 Inst1MemoInv — **the memo
hit**: a recorded entry *is* the answer.  Stated as `Inst1At` so that the
caller never has to unfold `Inst1MemoA` (and so that `Inst1MemoA` can stay
out of `grind`'s unfold list, where it would skolemise the goal). -/
@[grind →] theorem Inst1MemoA.get {ve : Expr} {s : AState} {k : EIdx × Nat}
    {r : EIdx} (hm : Inst1MemoA ve s) (hk : s.inst1C[k]? = some r) :
    Inst1At ve k.2 s.store k.1 s.store r := by
  intro e he
  obtain ⟨e', h1, h2⟩ := hm k r hk
  rw [he] at h1
  have heq : e = e' := Option.some.inj h1
  subst heq
  exact h2

/-- con-leche: ConLeche/Kernel/ExprOps.lean:69 Inst1MemoInv.insert — stated
in the `isSome` + `Inst1At` idiom, so that nothing has to be *guessed* when
`grind` applies it. -/
theorem Inst1MemoA.insert {ve : Expr} {s s' : AState} {k : EIdx × Nat} {r : EIdx}
    (hm : Inst1MemoA ve s) (hst : s'.store = s.store)
    (hc : s'.inst1C = s.inst1C.insert k r)
    (hk : (denoteE s.store k.1).isSome = true)
    (hr : Inst1At ve k.2 s.store k.1 s.store r) : Inst1MemoA ve s' := by
  obtain ⟨e, he⟩ := Option.isSome_iff_exists.mp hk
  intro k' r' hk'
  rw [hc, Std.HashMap.getElem?_insert] at hk'
  rw [hst]
  split at hk'
  · rename_i hbeq
    cases hk'
    obtain rfl := eq_of_beq hbeq
    exact ⟨e, he, hr e he⟩
  · exact hm k' r' hk'

/-! ## The spec theorems -/

/-- con-leche: ConLeche/Kernel/Core.lean:62 CheckError — **the failure
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

/-- con-leche: ConLeche/Kernel/Expr.lean:356-402 Expr.data — `derivedE` does
not touch the state and returns the packed word; with `EStore.derived_exact`
that word is `e.data` for the denoted `e`. -/
@[spec] theorem derivedE_spec (s₀ : AState) (h : EIdx) :
    ⦃fun s => ⌜s = s₀⌝⦄ derivedE h
    ⦃⇓? w s' => ⌜s' = s₀ ∧ w = s₀.store.derived h⌝⦄ := by
  mvcgen [derivedE]
  grind

/-- con-leche: Setlec/Kernel/IExpr.lean:464 intern — **the one spec that
carries the arena**: a handle for the node, the store still well formed, the
arena only grown, the two memo tables untouched, and the three nested stores
literally unchanged (so a name or level handle that had a view still has
one). -/
@[spec] theorem internE_spec (s₀ : AState) (w : ENodeView)
    (hwf : StoreWF s₀.store) (hv : s₀.store.ViewOK w) :
    ⦃fun s => ⌜s = s₀⌝⦄ internE w
    ⦃⇓? h s' => ⌜StoreWF s'.store ∧ Ext s₀.store s'.store ∧
        s'.store.lss = s₀.store.lss ∧
        s'.inst1C = s₀.inst1C ∧ s'.whnfCoreC = s₀.whnfCoreC ∧
        s'.store.view h = some w ∧
        denoteE s'.store h = denoteEView s'.store w⌝⦄ := by
  mvcgen [internE]
  case vc1.isTrue =>
    rename_i s hs _n hcap _st _s'
    subst hs
    obtain ⟨h1, h2, h3, h4⟩ := EStore.intern_spec hwf hv hcap
    exact ⟨h1, h2, EStore.lss_intern _ _, rfl, rfl, h3, h4⟩
  case vc2.isFalse.success => exact fun hf => hf.elim

/-- con-leche: ConLeche/Kernel/ExprOps.lean:81 instantiate1Go — the memo
probe leaves the state alone and hands back the table's own answer. -/
@[spec] theorem inst1Get_spec (s₀ : AState) (k : EIdx × Nat) :
    ⦃fun s => ⌜s = s₀⌝⦄ inst1Get k
    ⦃⇓? r s' => ⌜s' = s₀ ∧ r = s₀.inst1C[k]?⌝⦄ := by
  mvcgen [inst1Get]
  grind

/-- con-leche: ConLeche/Kernel/ExprOps.lean:116 instantiate1Go — the insert
changes the memo and nothing else.

**The spec of a memo insert states that the invariant is preserved**, not
that the table grew: it is the one place in the spike where the naive spec
(`s'.inst1C = s₀.inst1C.insert k r`) left `grind` with a goal it could not
take.  `Inst1MemoA` has no useful ematching pattern in *goal* position — the
negated goal is skolemised into `∀ k r, table[k]? = some r → …` before any
lemma can fire — so the invariant has to arrive as a *hypothesis*, which is
what this shape does.  The price is that the caller's obligations (the key
denotes, the value is the answer) become side goals of the spec, and those
are exactly the facts the caller has. -/
@[spec] theorem inst1Set_spec (s₀ : AState) (ve : Expr) (k : EIdx × Nat) (r : EIdx)
    (hm : Inst1MemoA ve s₀) (hk : (denoteE s₀.store k.1).isSome = true)
    (hr : Inst1At ve k.2 s₀.store k.1 s₀.store r) :
    ⦃fun s => ⌜s = s₀⌝⦄ inst1Set k r
    ⦃⇓? _u s' => ⌜s'.store = s₀.store ∧ s'.whnfCoreC = s₀.whnfCoreC ∧
        s'.inst1C = s₀.inst1C.insert k r ∧ Inst1MemoA ve s'⌝⦄ := by
  mvcgen [inst1Set]
  rename_i s hs _ _
  subst hs
  exact ⟨rfl, rfl, rfl, Inst1MemoA.insert hm rfl rfl hk hr⟩

/-- con-leche: ConLeche/Kernel/ExprOps.lean:56 instantiate1Go — dropping the
per-call memo changes the memo and nothing else. -/
@[spec] theorem inst1Clear_spec (s₀ : AState) :
    ⦃fun s => ⌜s = s₀⌝⦄ inst1Clear
    ⦃⇓? _u s' => ⌜s'.store = s₀.store ∧ s'.whnfCoreC = s₀.whnfCoreC ∧
        s'.inst1C = ∅ ∧ ∀ ve, Inst1MemoA ve s'⌝⦄ := by
  mvcgen [inst1Clear]
  exact ⟨by grind, by grind, trivial, fun ve => Inst1MemoA.of_empty rfl ve⟩

/-- con-leche: ConLeche/Cached/CoreC.lean:1880 memoEI — the `whnfCore` memo
probe. -/
@[spec] theorem whnfCoreGet_spec (s₀ : AState) (h : EIdx) :
    ⦃fun s => ⌜s = s₀⌝⦄ whnfCoreGet h
    ⦃⇓? r s' => ⌜s' = s₀ ∧ r = s₀.whnfCoreC[h]?⌝⦄ := by
  mvcgen [whnfCoreGet]
  grind

/-- con-leche: ConLeche/Cached/CoreC.lean:1885 memoEI — the `whnfCore` memo
insert. -/
@[spec] theorem whnfCoreSet_spec (s₀ : AState) (h r : EIdx) :
    ⦃fun s => ⌜s = s₀⌝⦄ whnfCoreSet h r
    ⦃⇓? _u s' => ⌜s'.store = s₀.store ∧ s'.inst1C = s₀.inst1C ∧
        s'.whnfCoreC = s₀.whnfCoreC.insert h r⌝⦄ := by
  mvcgen [whnfCoreSet]
  grind

end ConRon.Arena.Spike
