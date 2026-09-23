/-
# `ConRon.Bridge.ExprOps.Inst1` — Theorem 1 for `instantiate1`

DESIGN §8.2's Theorem 1 at `ExprOps.lean`'s first twin, and the module the
rest of the tier is written against: it fixes the shape of a walk's statement,
the shape of its arm's step lemma, and what the tag dispatch costs the proof.

## The statement

```lean
structure Inst1Spec (v : EIdx) (ve : Expr) (rec : EIdx → Nat → AM EIdx) : Prop where
  run : ∀ s₁ c dd, StateOK s₁ → Inst1MemoA ve s₁ →
    denoteE s₁.store v = some ve → (denoteE s₁.store c).isSome = true →
    ⦃fun s => ⌜s = s₁⌝⦄ rec c dd
    ⦃⇓? r s' => ⌜StateOK s' ∧ Inst1MemoA ve s' ∧ Ext s₁.store s'.store ∧
        s'.caches = s₁.caches ∧ s'.pins = s₁.pins ∧
        Inst1At ve dd s₁.store c s'.store r⌝⦄
```

* `Inst1At ve dd` is `Bridge/Rel.lean`'s **generic** `RelE` with the pure
  function fixed (task #97b finding 1), so all of `RelE`'s eliminators apply
  and `grind` still sees a head symbol;
* the record wraps the triple so that the arms can take it as a hypothesis
  and the dispatcher can discharge it with the fuel induction — task #97s's
  rule 8 shape;
* `s'.caches = s₁.caches` and `s'.pins = s₁.pins` are the frame `CheckOK.mono`
  consumes; **the twelve other per-call memo tables are NOT framed here** —
  see "What this module does not claim" at the end.

## The two deviations from con-leche this twin carries

1. **The derived-word cutoff** (DESIGN §8.3 lesson 20, the one §8.3 asks for
   by name and con-leche's `instantiate1Go` does not have): the walk returns
   `h` when the packed loose-bvar bound is exact and at most the cursor.  Its
   licence is `instantiate1_of_raw_le` below — `Expr.bvarBRaw_exact` (con-leche
   `ExprOps.lean:1456`) plus an induction on `Expr`.
2. **Fuel**, because a handle DAG has no structural order the elaborator can
   see.  Exhaustion is a failure and Theorem 1 claims nothing on failure
   (con-leche's `SimAt`), which is what `⇓?` says.

Everything else is clause for clause: the five leaf kinds answer without
touching the memo, and the four branching kinds probe the memo, run the body
one level down and insert.

## The tag dispatch

The twin tests `h.tag` before reading the store (task #97-P6-13), so the arms
are guarded by tag equations rather than by `view` patterns.
`Bridge/Rel.lean`'s group 6 turns each guard into a `view` fact
(`view_of_viewApp` and its siblings), and `EStore.tagOf_of_view` +
`denote_leaf_of_tag` are what let the catch-all `else` arm know it is looking
at one of the four leaves.
-/
import ConRon.Bridge.Specs

namespace ConRon.Bridge.ExprOps

set_option autoImplicit false
set_option mvcgen.warning false
set_option maxHeartbeats 2000000

open ConLeche ConRon.Arena ConRon.Bridge Std.Do

/-! ### Attribute hygiene (task #97s round 2, item 1)

`RelE.ext`, `.of_ext` and `.retarget` close the answer relation under `Ext` in
both directions, so every intermediate store multiplies every answer already
known.  The `_step` lemmas below already carry the whole chain, so the three
are redundant *and* explosive — measured on the spike's one file, 11.5 s
against 70 s.  `attribute [-grind]` does not travel through an import, so
every file of this tier repeats the line. -/
attribute [-grind] RelE.ext RelE.of_ext RelE.retarget

/-- con-leche: none — `mvcgen` hands an arm its projection read as
`some fields = st.viewC h`, i.e. REVERSED, so the one-line `assumption` that
supplies a step lemma's hypothesis has to try both orientations. -/
macro "arm_hyp" : tactic => `(tactic| first
  | assumption
  | (symm; assumption)
  | grind only [Ext.trans, Ext.refl])

/-! ## The cutoff's licence

The one pure lemma this twin needs that con-leche does not have, because
con-leche's `instantiate1Go` has no cutoff. -/

/-- con-leche: ConLeche/Kernel/ExprOps.lean:33-45 instantiate1 — **the
cutoff's licence**: a term with no loose `bvar` at or above the cursor is its
own instantiation.  DESIGN §8.3's "instantiate returns at `bvarB ≤
offset`". -/
theorem instantiate1_of_bvarBound_le {v : Expr} :
    ∀ (e : Expr) (d : Nat), e.bvarBound ≤ d → e.instantiate1 v d = e := by
  intro e
  induction e with
  | bvar i =>
    intro d h
    simp only [Expr.bvarBound] at h
    simp only [Expr.instantiate1, if_neg (show ¬ i = d by omega),
      if_neg (show ¬ i > d by omega)]
  | fvar _ _ _ | sort _ | const _ _ | lit _ => intro d _; simp [Expr.instantiate1]
  | app f a ihf iha =>
    intro d h
    simp only [Expr.bvarBound, Nat.max_le] at h
    simp [Expr.instantiate1, ihf d h.1, iha d h.2]
  | lam ty b m iht ihb =>
    intro d h
    simp only [Expr.bvarBound, Nat.max_le] at h
    simp [Expr.instantiate1, iht d h.1, ihb (d + 1) (by omega)]
  | forallE ty b m iht ihb =>
    intro d h
    simp only [Expr.bvarBound, Nat.max_le] at h
    simp [Expr.instantiate1, iht d h.1, ihb (d + 1) (by omega)]
  | letE ty w b iht ihw ihb =>
    intro d h
    simp only [Expr.bvarBound, Nat.max_le] at h
    simp [Expr.instantiate1, iht d h.1.1, ihw d h.1.2, ihb (d + 1) (by omega)]
  | proj n i e ih =>
    intro d h
    simp only [Expr.bvarBound] at h
    simp [Expr.instantiate1, ih d h]

/-- con-leche: ConLeche/Kernel/ExprOps.lean:1456 bvarBRaw_exact — the cutoff
as the arena TESTS it: the packed field, below saturation, licences the early
return. -/
theorem instantiate1_of_raw_le {v e : Expr} {d : Nat}
    (hsat : e.bvarBRaw < satRange) (hle : e.bvarBRaw ≤ d) :
    e.instantiate1 v d = e :=
  instantiate1_of_bvarBound_le e d (by rw [← Expr.bvarBRaw_exact e hsat]; exact hle)

/-- con-leche: ConLeche/Kernel/ExprOps.lean:33-45 instantiate1 — the four LEAF
constructors the catch-all `else` arm covers are all fixed points. -/
theorem instantiate1_leaf {v e : Expr} {d : Nat}
    (h : (∃ k t, e = .fvar k t) ∨ (∃ u, e = .sort u) ∨
      (∃ n us, e = .const n us) ∨ ∃ l, e = .lit l) :
    e.instantiate1 v d = e := by
  rcases h with ⟨k, t, rfl⟩ | ⟨u, rfl⟩ | ⟨n, us, rfl⟩ | ⟨l, rfl⟩ <;>
    simp [Expr.instantiate1]

/-! ## The answer relation, and the four step lemmas

`Inst1At` is `RelE` at `instantiate1`'s pure function.  The four `_step`
lemmas are `Bridge/Rel.lean`'s generic `RelE.app` / `.lam` / `.forallE` /
`.letE` / `.proj` with the decomposition discharged and the extension chain
spelled out in the shape `mvcgen` produces — which, per task #97s round 2's
item 3, is what makes each arm's two structural verification conditions one
`exact` instead of thousands of E-matching instances.

**They are applied BY HAND and not tagged `@[grind →]`**, and that is a
finding of its own: the spike could tag its monomorphic `Inst1At.app_step`
because its `Inst1At` was a `def` with a head symbol, while the generic `RelE`
behind this tier's `abbrev` leaves `grind` reporting *failed to find patterns
in the antecedents of the theorem*.  Round 2's item 3 asks for the hand
application anyway, so the generic relation costs nothing here. -/

/-- con-leche: ConLeche/Verify/SimI.lean:250 RelE — `instantiate1`'s answer
relation. -/
abbrev Inst1At (ve : Expr) (d : Nat) : EStore → EIdx → EStore → EIdx → Prop :=
  RelE (fun e => e.instantiate1 ve d)

theorem Inst1At.app_step {ve : Expr} {d : Nat}
    {st s1 s2 s3 : EStore} {h f a rf ra r : EIdx} (hwf : StoreWF st)
    (hview : st.view h = some (.app f a))
    (hx1 : Ext st s1) (hf : Inst1At ve d st f s1 rf)
    (hx2 : Ext s1 s2) (ha : Inst1At ve d s1 a s2 ra)
    (hx3 : Ext s2 s3)
    (hr : denoteE s3 r = denoteEView s3 (.app rf ra)) :
    Inst1At ve d st h s3 r :=
  RelE.app hwf hview (fun _ _ => rfl) ((hf.ext hx2).ext hx3)
    ((ha.of_ext hx1).ext hx3) hr

theorem Inst1At.bind_step {ve : Expr} {d : Nat}
    {st s1 s2 s3 : EStore} {h ty b rt rb r : EIdx} {m : BinderMeta}
    {tg : UInt32} (hwf : StoreWF st) (htg : ETag.isBind tg = true)
    (hview : st.view h = some (eBindView tg ty b m))
    (hx1 : Ext st s1) (ht : Inst1At ve d st ty s1 rt)
    (hx2 : Ext s1 s2) (hb : Inst1At ve (d + 1) s1 b s2 rb)
    (hx3 : Ext s2 s3)
    (hr : denoteE s3 r = denoteEView s3 (eBindView tg rt rb m)) :
    Inst1At ve d st h s3 r := by
  rcases (show tg = ETag.lam ∨ tg = ETag.forallE by
      simp only [ETag.isBind, Bool.or_eq_true, beq_iff_eq] at htg; exact htg)
    with rfl | rfl
  · rw [eBindView] at hview hr; simp only [beq_self_eq_true, if_true] at hview hr
    exact RelE.lam hwf hview (fun _ _ => rfl) ((ht.ext hx2).ext hx3)
      ((hb.of_ext hx1).ext hx3) hr
  · rw [eBindView] at hview hr
    simp only [ETag.lam, ETag.forallE, reduceCtorEq] at hview hr
    exact RelE.forallE hwf hview (fun _ _ => rfl) ((ht.ext hx2).ext hx3)
      ((hb.of_ext hx1).ext hx3) hr

theorem Inst1At.letE_step {ve : Expr} {d : Nat}
    {st s1 s2 s3 s4 : EStore} {h ty w b rt rw rb r : EIdx} (hwf : StoreWF st)
    (hview : st.view h = some (.letE ty w b))
    (hx1 : Ext st s1) (ht : Inst1At ve d st ty s1 rt)
    (hx2 : Ext s1 s2) (hw : Inst1At ve d s1 w s2 rw)
    (hx3 : Ext s2 s3) (hb : Inst1At ve (d + 1) s2 b s3 rb)
    (hx4 : Ext s3 s4)
    (hr : denoteE s4 r = denoteEView s4 (.letE rt rw rb)) :
    Inst1At ve d st h s4 r :=
  RelE.letE hwf hview (fun _ _ _ => rfl) (((ht.ext hx2).ext hx3).ext hx4)
    (((hw.of_ext hx1).ext hx3).ext hx4) ((hb.of_ext (hx1.trans hx2)).ext hx4) hr

theorem Inst1At.proj_step {ve : Expr} {d : Nat} {st s1 s2 : EStore}
    {h sub rs r : EIdx} {n : NIdx} {i : Nat} {nm : ConLeche.Name}
    (hwf : StoreWF st) (hview : st.view h = some (.proj n i sub))
    (hx1 : Ext st s1) (hs : Inst1At ve d st sub s1 rs)
    (hx2 : Ext s1 s2)
    (hr : denoteE s2 r = denoteEView s2 (.proj n i rs))
    (hn0 : denoteN st.ns n = some nm) : Inst1At ve d st h s2 r :=
  RelE.proj hwf hview (fun _ => rfl) (hs.ext hx2) hn0
    (denoteN_ext (denoteN_ext hn0 hx1) hx2) hr

/-! ### The same four, in the shape `mvcgen` actually produces

Task #97s round 1's group 7 ("the per-site step lemmas, as the verification
condition presents them"), and it is load-bearing for a different reason here
than there: the twin dispatches on the TAG and then projects, so what the arm
has is `(h.tag == ETag.app) = true` and `some (f, a) = st.viewApp h` —
REVERSED, because `mvcgen` orients a spec's postcondition equation that way.
With the view derived inside the lemma, `f` and `a` are determined by the
hypothesis `assumption` finds; with a `have` in front of the `exact` they are
metavariables when `assumption` runs, and it fails (measured).

-/

/-- con-leche: none — `Inst1At.app_step` at the arm's own hypotheses. -/
theorem Inst1At.app_step' {ve : Expr} {d : Nat} {st s1 s2 s3 : EStore}
    {h f a rf ra r : EIdx} (hwf : StoreWF st)
    (htg : (h.tag == ETag.app) = true) (hva : some (f, a) = st.viewApp h)
    (hx1 : Ext st s1) (hf : Inst1At ve d st f s1 rf)
    (hx2 : Ext s1 s2) (ha : Inst1At ve d s1 a s2 ra)
    (hx3 : Ext s2 s3)
    (hr : denoteE s3 r = denoteEView s3 (.app rf ra)) :
    Inst1At ve d st h s3 r :=
  Inst1At.app_step hwf (view_of_viewApp_tag htg hva.symm) hx1 hf hx2 ha hx3 hr

/-- con-leche: none — `Inst1At.letE_step` at the arm's own hypotheses. -/
theorem Inst1At.letE_step' {ve : Expr} {d : Nat} {st s1 s2 s3 s4 : EStore}
    {h ty w b rt rw rb r : EIdx} (hwf : StoreWF st)
    (htg : (h.tag == ETag.letE) = true)
    (hvl : some (ty, w, b) = st.viewLet h)
    (hx1 : Ext st s1) (ht : Inst1At ve d st ty s1 rt)
    (hx2 : Ext s1 s2) (hw : Inst1At ve d s1 w s2 rw)
    (hx3 : Ext s2 s3) (hb : Inst1At ve (d + 1) s2 b s3 rb)
    (hx4 : Ext s3 s4)
    (hr : denoteE s4 r = denoteEView s4 (.letE rt rw rb)) :
    Inst1At ve d st h s4 r :=
  Inst1At.letE_step hwf (view_of_viewLet_tag htg hvl.symm) hx1 ht hx2 hw hx3 hb
    hx4 hr

/-- con-leche: none — `Inst1At.proj_step` at the arm's own hypotheses.  The
name fact is supplied by the caller (it comes from `denote_eq_proj`, whose
existential `grind` cannot see through). -/
theorem Inst1At.proj_step' {ve : Expr} {d : Nat} {st s1 s2 : EStore}
    {h sub rs r : EIdx} {n : NIdx} {i : Nat} {nm : ConLeche.Name}
    (hwf : StoreWF st) (htg : (h.tag == ETag.proj) = true)
    (hvp : some (n, i, sub) = st.viewProj h)
    (hx1 : Ext st s1) (hs : Inst1At ve d st sub s1 rs)
    (hx2 : Ext s1 s2)
    (hr : denoteE s2 r = denoteEView s2 (.proj n i rs))
    (hn0 : denoteN st.ns n = some nm) : Inst1At ve d st h s2 r :=
  Inst1At.proj_step hwf (view_of_viewProj_tag htg hvp.symm) hx1 hs hx2 hr hn0

/-- con-leche: none — `Inst1At.bind_step` at the arm's own hypotheses: the
binder arm reads the datum's HANDLE, so the view fact needs the datum's value
and `view_of_viewBindI_wf` supplies it. -/
theorem Inst1At.bind_step' {ve : Expr} {d : Nat} {st s1 s2 s3 : EStore}
    {h ty b rt rb r : EIdx} {mi : BMIdx} {m : BinderMeta} {tg : UInt32}
    (hwf : StoreWF st) (htg : ETag.isBind tg = true) (htg2 : tg = h.tag)
    (hvb : some (ty, b, mi) = st.viewBindI h)
    (hbm : st.viewBM mi = some m)
    (hx1 : Ext st s1) (ht : Inst1At ve d st ty s1 rt)
    (hx2 : Ext s1 s2) (hb : Inst1At ve (d + 1) s1 b s2 rb)
    (hx3 : Ext s2 s3)
    (hr : denoteE s3 r = denoteEView s3 (eBindView tg rt rb m)) :
    Inst1At ve d st h s3 r := by
  refine Inst1At.bind_step hwf htg ?_ hx1 ht hx2 hb hx3 hr
  rw [htg2] at htg ⊢
  exact view_of_viewBindI htg hvb.symm hbm

/-- con-leche: ConLeche/Kernel/ExprOps.lean:33-45 instantiate1 — the CUTOFF
arm, packaged as one step lemma.  Left as three separate hints
(`EStore.derived_exact`, `Expr.bvarBRaw`, `instantiate1_of_raw_le`) it sends
`grind` into an ematching spiral on `((ve.instantiate1 ve d).instantiate1 ve
d)…`; as one lemma with the store read as its pattern it fires once (task
#97s's one manual verification condition). -/
theorem Inst1At.cutoff {st : EStore} (hwf : StoreWF st) {h : EIdx} {d : Nat}
    {ve : Expr} (hsat : (bvarOfData (st.derived h)).toNat < satRange)
    (hle : (bvarOfData (st.derived h)).toNat ≤ d) : Inst1At ve d st h st h := by
  intro e he
  show denoteE st h = some (e.instantiate1 ve d)
  have hd := EStore.derived_exact hwf he
  rw [hd] at hsat hle
  rw [instantiate1_of_raw_le hsat hle]
  exact he

/-- con-leche: ConLeche/Kernel/ExprOps.lean:33-45 instantiate1 — the CATCH-ALL
arm: a handle whose tag is none of the six the walk dispatches on denotes a
leaf, and `instantiate1` is the identity there. -/
theorem Inst1At.leaf {st : EStore} (hwf : StoreWF st) {h : EIdx}
    {v : ENodeView} {d : Nat} {ve : Expr} (hview : st.view h = some v)
    (happ : ¬ (h.tag = ETag.app)) (hbind : ETag.isBind h.tag = false)
    (hbvar : ¬ (h.tag = ETag.bvar)) (hlet : ¬ (h.tag = ETag.letE))
    (hproj : ¬ (h.tag = ETag.proj)) : Inst1At ve d st h st h := by
  intro e he
  show denoteE st h = some (e.instantiate1 ve d)
  rw [instantiate1_leaf
    (denote_leaf_of_tag hwf hview happ hbind hbvar hlet hproj he)]
  exact he

/-! ## Theorem 1 for `instantiate1Go`

One level of the recursion as a record, so that the fuel induction has
something to hand the arms (task #97s rule 8).

**Since DESIGN §8.6's arm-split ruling** (coordinator, 2026-09-22) the twin
is a `mutual` block — a dispatcher and one `def` per constructor arm — and
the proof follows it exactly: one theorem per arm, each taking the previous
fuel level's record as its induction hypothesis, and a dispatcher whose
`mvcgen` list is the five arm theorems.  The dispatcher's body is then the
cutoff, the tag chain and six calls, so `mvcgen` leaves a handful of
verification conditions instead of the seventy-nine the inline body left, and
`grind` — which was 66 of the 71 net seconds — never sees more than one arm's
worth of context at a time.

**Each arm carries its own tag hypothesis.**  `EStore.viewApp` does not test
the tag (it is the array read the tag dispatch has already decided, tasks
#97-P6-10 and #97-P6-13), so `view_of_viewApp` needs `h.tag = ETag.app` and
the arm theorem takes it as a parameter; the dispatcher supplies it from the
branch it is in, as one more verification condition that `assumption` closes.

**The record carries `BMExt`** (task #97-P3-1, `Bridge/StoreBM.lean`): the
binder-datum store's own extension, which `Ext` cannot say because a `BMIdx`
denotes nothing.  It is what closes the binder arm — `internBindIE`'s
precondition is asked at the store the two recursive calls left behind, while
the `viewBindI` read was taken in the store they started in. -/

/-- con-leche: ConLeche/Verify/SimI.lean:244 SimAt — Theorem 1's statement for
one level of `instantiate1Go`'s recursion. -/
structure Inst1Spec (v : EIdx) (ve : Expr) (rec : EIdx → Nat → AM EIdx) :
    Prop where
  run : ∀ (s₁ : AState) (c : EIdx) (dd : Nat), StateOK s₁ → Inst1MemoA ve s₁ →
    denoteE s₁.store v = some ve → (denoteE s₁.store c).isSome = true →
    ⦃fun s => ⌜s = s₁⌝⦄ rec c dd
    ⦃⇓? r s' => ⌜StateOK s' ∧ Inst1MemoA ve s' ∧ Ext s₁.store s'.store ∧
        BMExt s₁.store s'.store ∧
        s'.caches = s₁.caches ∧ s'.pins = s₁.pins ∧
        Inst1At ve dd s₁.store c s'.store r⌝⦄

/-- con-leche: ConLeche/Kernel/ExprOps.lean:80-116 instantiate1Go — the `bvar`
ARM, which is not recursive and needs no induction hypothesis.  The three
branches are `Expr.instantiate1`'s own three, and they are written out because
the closer will not unfold `RelE` (a `def`); at one arm in one theorem that is
nine lines rather than the file-wide `unfold RelE` that task #97-P3-0 measured
breaking the `proj` arm. -/
theorem instantiate1ArmBVar_spec (v : EIdx) (ve : Expr) (s₁ : AState)
    (c : EIdx) (dd : Nat) (hok : StateOK s₁) (hm : Inst1MemoA ve s₁)
    (hv : denoteE s₁.store v = some ve)
    (hden : (denoteE s₁.store c).isSome = true)
    (htg : (c.tag == ETag.bvar) = true) :
    ⦃fun s => ⌜s = s₁⌝⦄ instantiate1ArmBVar v c dd
    ⦃⇓? r s' => ⌜StateOK s' ∧ Inst1MemoA ve s' ∧ Ext s₁.store s'.store ∧
        BMExt s₁.store s'.store ∧
        s'.caches = s₁.caches ∧ s'.pins = s₁.pins ∧
        Inst1At ve dd s₁.store c s'.store r⌝⦄ := by
  mvcgen [instantiate1ArmBVar]
  all_goals try bridge_vcs [Expr.instantiate1]
  all_goals (bridge_peel; subst_vars)
  -- `i = dd`: the answer is the substituted handle itself.
  next =>
    rename_i i st hvb
    refine ⟨hok, hm, Ext.refl _, BMExt.refl _, rfl, rfl, ?_⟩
    intro e he
    have heq := denote_bvar_inv hok.wf (view_of_viewBVar_tag htg hvb.symm) he
    subst heq
    simpa [Expr.instantiate1] using hv
  -- `i > dd`: the lowered index is interned.  Template rule 7 — the
  -- verification condition arrives as an implication chain.
  next =>
    rename_i i hne hgt s1 r st hvb
    intro hwf' hx hbx _hlss _hscr _hmemos hcaches hpins _hview' hden'
    refine ⟨⟨hwf'⟩, hm.mono hx (by grind), hx, hbx, hcaches, hpins, ?_⟩
    intro e he
    have heq := denote_bvar_inv hok.wf (view_of_viewBVar_tag htg hvb.symm) he
    subst heq
    rw [hden']
    simp [Expr.instantiate1, hne, hgt, denoteEView]
  -- `i < dd`: the node is its own instantiation.
  next =>
    rename_i i hne hle st hvb
    refine ⟨hok, hm, Ext.refl _, BMExt.refl _, rfl, rfl, ?_⟩
    intro e he
    have heq := denote_bvar_inv hok.wf (view_of_viewBVar_tag htg hvb.symm) he
    subst heq
    simpa [Expr.instantiate1, hne, hle] using he

/-- con-leche: ConLeche/Kernel/ExprOps.lean:80-116 instantiate1Go — the `app`
ARM: probe, project, recurse into both children, rebuild, insert. -/
theorem instantiate1ArmApp_spec (v : EIdx) (ve : Expr) (fuel : Nat)
    (ih : Inst1Spec v ve (instantiate1Go v fuel)) (s₁ : AState) (c : EIdx)
    (dd : Nat) (hok : StateOK s₁) (hm : Inst1MemoA ve s₁)
    (hv : denoteE s₁.store v = some ve)
    (hden : (denoteE s₁.store c).isSome = true)
    (htg : (c.tag == ETag.app) = true) :
    ⦃fun s => ⌜s = s₁⌝⦄ instantiate1ArmApp v fuel c dd
    ⦃⇓? r s' => ⌜StateOK s' ∧ Inst1MemoA ve s' ∧ Ext s₁.store s'.store ∧
        BMExt s₁.store s'.store ∧
        s'.caches = s₁.caches ∧ s'.pins = s₁.pins ∧
        Inst1At ve dd s₁.store c s'.store r⌝⦄ := by
  have hrec := ih.run
  mvcgen [instantiate1ArmApp, hrec]
  all_goals try bridge_vcs [Expr.instantiate1]
  -- the memo insert's answer, then the arm's postcondition
  next =>
    bridge_peel
    subst_vars
    refine RelE.retarget ?_ ?_ hden
    · exact Inst1At.app_step' hok.wf (by arm_hyp) (by arm_hyp) (by arm_hyp)
        (by arm_hyp) (by arm_hyp) (by arm_hyp) (by arm_hyp) (by arm_hyp)
    · grind only [Ext.trans]
  next =>
    bridge_peel
    subst_vars
    refine ⟨by grind only [StateOK, StateOK.mk], by arm_hyp,
      by grind only [Ext.trans], by grind only [BMExt.trans, BMExt.refl],
      by grind, by grind, ?_⟩
    exact Inst1At.app_step' hok.wf (by arm_hyp) (by arm_hyp) (by arm_hyp)
      (by arm_hyp) (by arm_hyp) (by arm_hyp) (by arm_hyp) (by arm_hyp)

/-- con-leche: ConLeche/Kernel/ExprOps.lean:80-116 instantiate1Go — the BINDER
ARM (`lam` and `forallE` in one, as the tag dispatch tests them).  This is the
arm `BMExt` exists for. -/
theorem instantiate1ArmBind_spec (v : EIdx) (ve : Expr) (fuel : Nat)
    (ih : Inst1Spec v ve (instantiate1Go v fuel)) (s₁ : AState) (c : EIdx)
    (dd : Nat) (hok : StateOK s₁) (hm : Inst1MemoA ve s₁)
    (hv : denoteE s₁.store v = some ve)
    (hden : (denoteE s₁.store c).isSome = true)
    (htg : ETag.isBind c.tag = true) :
    ⦃fun s => ⌜s = s₁⌝⦄ instantiate1ArmBind v fuel c dd
    ⦃⇓? r s' => ⌜StateOK s' ∧ Inst1MemoA ve s' ∧ Ext s₁.store s'.store ∧
        BMExt s₁.store s'.store ∧
        s'.caches = s₁.caches ∧ s'.pins = s₁.pins ∧
        Inst1At ve dd s₁.store c s'.store r⌝⦄ := by
  have hrec := ih.run
  mvcgen [instantiate1ArmBind, hrec]
  all_goals try bridge_vcs [Expr.instantiate1]
  -- the two recursive calls' subjects denote
  next =>
    bridge_peel
    subst_vars
    obtain ⟨m, hbm, _, hvw⟩ :=
      view_of_viewBindI_wf hok.wf (i := c) htg (by arm_hyp)
    exact (isSome_eBindView hok.wf hvw hden).1
  next =>
    bridge_peel
    subst_vars
    obtain ⟨m, hbm, _, hvw⟩ :=
      view_of_viewBindI_wf hok.wf (i := c) htg (by arm_hyp)
    have h2 := isSome_eBindView hok.wf hvw hden
    grind
  -- `internBindIE`'s three side conditions.  The datum survives the two
  -- recursive calls by `BMExt` — the conjunct `Bridge/StoreBM.lean` exists
  -- for, and the reason task #97-P3-0 left this arm open.
  next =>
    bridge_peel
    subst_vars
    obtain ⟨m, hbm, _htag0, _hvw⟩ :=
      view_of_viewBindI_wf hok.wf (i := c) htg (by arm_hyp)
    grind [BMExt.get]
  next =>
    bridge_peel
    subst_vars
    obtain ⟨m, hbm, _, hvw⟩ :=
      view_of_viewBindI_wf hok.wf (i := c) htg (by arm_hyp)
    have h2 := isSome_eBindView hok.wf hvw hden
    exact view_isSome (by grind)
  next =>
    bridge_peel
    subst_vars
    obtain ⟨m, hbm, _, hvw⟩ :=
      view_of_viewBindI_wf hok.wf (i := c) htg (by arm_hyp)
    have h2 := isSome_eBindView hok.wf hvw hden
    exact view_isSome (by grind)
  -- the memo insert's answer, then the postcondition
  next =>
    bridge_peel
    subst_vars
    obtain ⟨m, hbm, _htag0, _hvw⟩ :=
      view_of_viewBindI_wf hok.wf (i := c) htg (by arm_hyp)
    refine RelE.retarget ?_ ?_ hden
    · refine Inst1At.bind_step' hok.wf htg rfl (by arm_hyp) hbm (by arm_hyp)
        (by arm_hyp) (by arm_hyp) (by arm_hyp) (by arm_hyp) ?_
      grind
    · grind only [Ext.trans]
  next =>
    bridge_peel
    subst_vars
    obtain ⟨m, hbm, _htag0, _hvw⟩ :=
      view_of_viewBindI_wf hok.wf (i := c) htg (by arm_hyp)
    refine ⟨by grind only [StateOK, StateOK.mk], by arm_hyp,
      by grind only [Ext.trans], by grind only [BMExt.trans, BMExt.refl],
      by grind, by grind, ?_⟩
    refine Inst1At.bind_step' hok.wf htg rfl (by arm_hyp) hbm (by arm_hyp)
      (by arm_hyp) (by arm_hyp) (by arm_hyp) (by arm_hyp) ?_
    grind

/-- con-leche: ConLeche/Kernel/ExprOps.lean:80-116 instantiate1Go — the `letE`
ARM; the body descends at `dd + 1`. -/
theorem instantiate1ArmLet_spec (v : EIdx) (ve : Expr) (fuel : Nat)
    (ih : Inst1Spec v ve (instantiate1Go v fuel)) (s₁ : AState) (c : EIdx)
    (dd : Nat) (hok : StateOK s₁) (hm : Inst1MemoA ve s₁)
    (hv : denoteE s₁.store v = some ve)
    (hden : (denoteE s₁.store c).isSome = true)
    (htg : (c.tag == ETag.letE) = true) :
    ⦃fun s => ⌜s = s₁⌝⦄ instantiate1ArmLet v fuel c dd
    ⦃⇓? r s' => ⌜StateOK s' ∧ Inst1MemoA ve s' ∧ Ext s₁.store s'.store ∧
        BMExt s₁.store s'.store ∧
        s'.caches = s₁.caches ∧ s'.pins = s₁.pins ∧
        Inst1At ve dd s₁.store c s'.store r⌝⦄ := by
  have hrec := ih.run
  mvcgen [instantiate1ArmLet, hrec]
  all_goals try bridge_vcs [Expr.instantiate1]
  next =>
    bridge_peel
    subst_vars
    refine RelE.retarget ?_ ?_ hden
    · exact Inst1At.letE_step' hok.wf (by arm_hyp) (by arm_hyp) (by arm_hyp)
        (by arm_hyp) (by arm_hyp) (by arm_hyp) (by arm_hyp) (by arm_hyp)
        (by arm_hyp) (by arm_hyp)
    · grind only [Ext.trans]
  next =>
    bridge_peel
    subst_vars
    refine ⟨by grind only [StateOK, StateOK.mk], by arm_hyp,
      by grind only [Ext.trans], by grind only [BMExt.trans, BMExt.refl],
      by grind, by grind, ?_⟩
    exact Inst1At.letE_step' hok.wf (by arm_hyp) (by arm_hyp) (by arm_hyp)
      (by arm_hyp) (by arm_hyp) (by arm_hyp) (by arm_hyp) (by arm_hyp)
      (by arm_hyp) (by arm_hyp)

/-- con-leche: ConLeche/Kernel/ExprOps.lean:80-116 instantiate1Go — the `proj`
ARM.  The struct NAME is carried unchanged, and its denotation comes from
`denote_eq_proj`'s existential, which `grind` cannot see through. -/
theorem instantiate1ArmProj_spec (v : EIdx) (ve : Expr) (fuel : Nat)
    (ih : Inst1Spec v ve (instantiate1Go v fuel)) (s₁ : AState) (c : EIdx)
    (dd : Nat) (hok : StateOK s₁) (hm : Inst1MemoA ve s₁)
    (hv : denoteE s₁.store v = some ve)
    (hden : (denoteE s₁.store c).isSome = true)
    (htg : (c.tag == ETag.proj) = true) :
    ⦃fun s => ⌜s = s₁⌝⦄ instantiate1ArmProj v fuel c dd
    ⦃⇓? r s' => ⌜StateOK s' ∧ Inst1MemoA ve s' ∧ Ext s₁.store s'.store ∧
        BMExt s₁.store s'.store ∧
        s'.caches = s₁.caches ∧ s'.pins = s₁.pins ∧
        Inst1At ve dd s₁.store c s'.store r⌝⦄ := by
  have hrec := ih.run
  mvcgen [instantiate1ArmProj, hrec]
  all_goals try bridge_vcs [Expr.instantiate1]
  next =>
    bridge_peel
    subst_vars
    obtain ⟨nm, es, _, hn0, _⟩ :=
      denote_eq_proj hok.wf (view_of_viewProj_tag (i := c) htg (by arm_hyp))
        hden
    refine RelE.retarget ?_ ?_ hden
    · exact Inst1At.proj_step' hok.wf htg (by arm_hyp) (by arm_hyp)
        (by arm_hyp) (by arm_hyp) (by arm_hyp) hn0
    · grind only [Ext.trans]
  next =>
    bridge_peel
    subst_vars
    obtain ⟨nm, es, _, hn0, _⟩ :=
      denote_eq_proj hok.wf (view_of_viewProj_tag (i := c) htg (by arm_hyp))
        hden
    refine ⟨by grind only [StateOK, StateOK.mk], by arm_hyp,
      by grind only [Ext.trans], by grind only [BMExt.trans, BMExt.refl],
      by grind, by grind, ?_⟩
    exact Inst1At.proj_step' hok.wf htg (by arm_hyp) (by arm_hyp)
      (by arm_hyp) (by arm_hyp) (by arm_hyp) hn0

/-- con-leche: ConLeche/Kernel/ExprOps.lean:33-45 instantiate1
con-leche: ConLeche/Kernel/ExprOps.lean:80-116 instantiate1Go
**THEOREM 1 for `instantiate1`**, at one level of the recursion, by induction
on the fuel.  The dispatcher: the cutoff, the tag chain, the five arms by
name, and the catch-all. -/
theorem instantiate1Go_spec (v : EIdx) (ve : Expr) :
    ∀ fuel, Inst1Spec v ve (instantiate1Go v fuel) := by
  intro fuel
  induction fuel with
  | zero =>
    constructor
    intro s₀ h d _ _ _ _
    mvcgen [instantiate1Go_zero]
    all_goals bridge_vcs [Expr.instantiate1]
  | succ fuel ih =>
    constructor
    intro s₀ h d hok hm hv hden
    have happ := instantiate1ArmApp_spec v ve fuel ih
    have hbind := instantiate1ArmBind_spec v ve fuel ih
    have hbvar := instantiate1ArmBVar_spec v ve
    have hlet := instantiate1ArmLet_spec v ve fuel ih
    have hproj := instantiate1ArmProj_spec v ve fuel ih
    mvcgen [instantiate1Go_succ, happ, hbind, hbvar, hlet, hproj]
    all_goals try bridge_vcs [Expr.instantiate1]
    -- TWO verification conditions survive the closer, against the inline
    -- body's eighteen: the derived-word cutoff and the catch-all.
    next =>
      bridge_peel
      subst_vars
      exact ⟨hok, hm, Ext.refl _, BMExt.refl _, rfl, rfl,
        Inst1At.cutoff hok.wf (by grind) (by grind)⟩
    next =>
      bridge_peel
      subst_vars
      obtain ⟨e, he⟩ := Option.isSome_iff_exists.mp hden
      obtain ⟨vw, hvw⟩ := denoteE_view he
      exact ⟨hok, hm, Ext.refl _, BMExt.refl _, rfl, rfl,
        Inst1At.leaf hok.wf hvw (by grind) (by grind) (by grind) (by grind)
          (by grind)⟩
/-! ## The top-level entry, and Theorem 1 as a statement about a RUN

`instantiate1Fast` is con-leche's `(instantiate1Go v {} e d).1`: the memo is
fresh before and dropped after, because its answers depend on the substituted
term.  The dropped memo satisfies `Inst1MemoA` for EVERY substituted term
(`MemoOK.of_empty`), which is why the per-call memo never appears in a
caller's invariant. -/

/-- con-leche: ConLeche/Kernel/ExprOps.lean:182-184 instantiate1Fast —
**THEOREM 1 for `instantiate1`, at the entry point**. -/
theorem instantiate1Fast_spec (fuel : Nat) (s₀ : AState) (e v : EIdx) (d : Nat)
    (ve : Expr) (hok : StateOK s₀) (hv : denoteE s₀.store v = some ve)
    (hden : (denoteE s₀.store e).isSome = true) :
    ⦃fun s => ⌜s = s₀⌝⦄ instantiate1Fast fuel e v d
    ⦃⇓? r s' => ⌜StateOK s' ∧ Ext s₀.store s'.store ∧
        BMExt s₀.store s'.store ∧
        s'.caches = s₀.caches ∧ s'.pins = s₀.pins ∧
        s'.memos.inst1C = ∅ ∧
        Inst1At ve d s₀.store e s'.store r⌝⦄ := by
  have hr := (instantiate1Go_spec v ve fuel).run
  mvcgen [instantiate1Fast, hr]
  all_goals bridge_vcs [Expr.instantiate1]

/-- con-leche: ConLeche/Verify/SimI.lean:244 SimAt — the same statement about
a RUN, which is the form the tier above consumes. -/
theorem instantiate1Fast_run {fuel : Nat} {s₀ s' : AState} {e v r : EIdx}
    {d : Nat} {ve : Expr} (hok : StateOK s₀)
    (hv : denoteE s₀.store v = some ve)
    (hden : (denoteE s₀.store e).isSome = true)
    (hrun : (instantiate1Fast fuel e v d).run s₀ = Except.ok (r, s')) :
    StateOK s' ∧ Ext s₀.store s'.store ∧ BMExt s₀.store s'.store ∧
      s'.caches = s₀.caches ∧ s'.pins = s₀.pins ∧ s'.memos.inst1C = ∅ ∧
      Inst1At ve d s₀.store e s'.store r :=
  AM.of_run (P := fun s => s = s₀) rfl hrun
    (instantiate1Fast_spec fuel s₀ e v d ve hok hv hden)

/-! ## The axiom check -/

#print axioms instantiate1_of_bvarBound_le
#print axioms instantiate1_of_raw_le
#print axioms Inst1At.cutoff
#print axioms Inst1At.leaf

end ConRon.Bridge.ExprOps
