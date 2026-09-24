/-
# `ConRon.Bridge.ExprOps.Reset` — Theorem 1 for `resetMeta` and `renameConsts`

DESIGN §8.2's Theorem 1 at the four twins of `Arena/ExprOps.lean` that rebuild
a term leaving its SHAPE alone and changing one datum: `resetMetaGo` /
`resetMetaFast` (`:567`, `:633`) reset every binder's prop-ness datum to the
parse placeholder, and `renameConstsGo` / `renameConstsFast` (`:1102`,
`:1168`) rename every `const` node's name.

Written against `ExprOps/Inst1.lean`, the tier's exemplar, and the two walks
are the cheapest of the tier's five rebuilding walks: they dispatch on the
VIEW rather than on the tag (so `Bridge/Rel.lean`'s inversions apply directly,
with no `EStore.tagOf_of_view` step), and they carry no derived-word cutoff at
all.

## The deviations these twins carry

1. **The upward `internRebuilt` cutoff** (task #97-P6-5) at every rebuilding
   arm.  `ExprOps/MemoSpecs.lean`'s `internRebuilt*_specV` family discharges
   it: `internRebuilt h same v` answers `h` when the children came back
   unchanged, and the arm's obligation "if `same` then `v` IS `h`'s view" is
   discharged from the walk's own `view`-monotonicity conjunct (see that
   module's header — the conjunct `Bridge/Specs.lean` is missing and the
   reason five walks needed it).
2. **The memo is keyed at cursor `0`** (`Arena/ExprOps.lean`'s note: "The memo
   has no cursor in con-leche; the arena keys it at `0` so that every
   handle-valued memo has one shape"), which is why `ResetMemoA` and
   `RenameMemoA` ignore the key's second component.
3. **`renameConsts`' renaming is a function on NAME HANDLES**
   (`Arena/ExprOps.lean`: "The renaming is a function on NAME HANDLES, not on
   names … it is the module's one higher-order argument, and it is
   con-leche's own"), while con-leche's `renameConsts` takes
   `f : Name → Name`.  The two are related by this module's hypothesis
   `hf` — "the handle renaming denotes the name renaming" — which is the
   twin's interface obligation and is what the call site (task #175's
   modeled-block contract) supplies.  `renameConstsGo`'s `const` arm is a
   LEAF that rebuilds (con-leche's is too), so it is the one arm of the tier
   that is neither a leaf nor memoised.

## What is NOT deviation

`resetMeta`'s binder arms write the datum `⟨.never⟩` and con-leche's pure
`resetMeta` writes the same, so `Bridge/Rel.lean`'s `RelE.lam` / `.forallE`
are applied at a CHANGED binder datum `m'` — which is exactly what those two
lemmas' `m'` argument is for.  Likewise `renameConsts` changes the `const`
node's NAME, which is `RelE.proj`'s `nm'` played at `RelE.of_view`.
-/
import ConRon.Bridge.ExprOps.MemoSpecs

namespace ConRon.Bridge.ExprOps

set_option autoImplicit false
set_option mvcgen.warning false
set_option maxHeartbeats 8000000

open ConLeche ConRon.Arena ConRon.Bridge Std.Do

/-! ### Attribute hygiene (task #97s round 2, item 1) -/
attribute [-grind] RelE.ext RelE.of_ext RelE.retarget

/-- con-leche: none — `mvcgen` hands an arm its projection read as
`some fields = st.viewC h`, i.e. REVERSED, so the one-line `assumption` that
supplies a step lemma's hypothesis has to try both orientations. -/
macro "arm_hyp2" : tactic => `(tactic| first
  | assumption
  | (symm; assumption)
  | grind only [Ext.trans, Ext.refl]
  | grind [StateOK])

/-! ## The answer relations -/

/-- con-leche: ConLeche/Verify/SimI.lean:250 RelE — `resetMeta`'s answer
relation. -/
abbrev ResetAt : EStore → EIdx → EStore → EIdx → Prop := RelE Expr.resetMeta

/-- con-leche: ConLeche/Verify/SimI.lean:250 RelE — `renameConsts`' answer
relation, at con-leche's own `Name → Name` renaming. -/
abbrev RenameAt (fn : ConLeche.Name → ConLeche.Name) :
    EStore → EIdx → EStore → EIdx → Prop :=
  RelE (Expr.renameConsts fn)

/-! ## The pure leaf facts -/

/-- con-leche: ConLeche/Kernel/ExprOps.lean:552-559 resetMeta — the four leaf
constructors are fixed points. -/
theorem resetMeta_leaf {e : Expr}
    (h : (∃ i, e = .bvar i) ∨ (∃ u, e = .sort u) ∨
      (∃ n us, e = .const n us) ∨ ∃ l, e = .lit l) : Expr.resetMeta e = e := by
  rcases h with ⟨i, rfl⟩ | ⟨u, rfl⟩ | ⟨n, us, rfl⟩ | ⟨l, rfl⟩ <;>
    simp [Expr.resetMeta]

/-- con-leche: ConLeche/Kernel/ExprOps.lean:934-956 renameConsts — the three
leaf constructors that are fixed points (`const` is NOT one: it is the arm
the walk exists for). -/
theorem renameConsts_leaf {fn : ConLeche.Name → ConLeche.Name} {e : Expr}
    (h : (∃ i, e = .bvar i) ∨ (∃ u, e = .sort u) ∨ ∃ l, e = .lit l) :
    Expr.renameConsts fn e = e := by
  rcases h with ⟨i, rfl⟩ | ⟨u, rfl⟩ | ⟨l, rfl⟩ <;> simp [Expr.renameConsts]

/-! ## The step lemmas, arm by arm

`Bridge/Rel.lean`'s group 7 at each walk's own clause.  The `fvar` arm uses
`RelE.fvar` from `ExprOps/MemoSpecs.lean` (the generic step lemma
`Bridge/Rel.lean` is missing — see that module). -/

theorem ResetAt.fvar_step {st s1 s2 : EStore} {h ty rt r : EIdx} {idx : Nat}
    (hwf : StoreWF st) (hview : st.view h = some (.fvar idx ty))
    (hx1 : Ext st s1) (ht : ResetAt st ty s1 rt) (hx2 : Ext s1 s2)
    (hr : denoteE s2 r = denoteEView s2 (.fvar idx rt)) : ResetAt st h s2 r :=
  RelE.fvar hwf hview (fun _ => rfl) (ht.ext hx2) hr

theorem ResetAt.app_step {st s1 s2 s3 : EStore} {h f a rf ra r : EIdx}
    (hwf : StoreWF st) (hview : st.view h = some (.app f a))
    (hx1 : Ext st s1) (hf : ResetAt st f s1 rf)
    (hx2 : Ext s1 s2) (ha : ResetAt s1 a s2 ra)
    (hx3 : Ext s2 s3)
    (hr : denoteE s3 r = denoteEView s3 (.app rf ra)) : ResetAt st h s3 r :=
  RelE.app hwf hview (fun _ _ => rfl) ((hf.ext hx2).ext hx3)
    ((ha.of_ext hx1).ext hx3) hr

/-- con-leche: ConLeche/Kernel/ExprOps.lean:552-559 resetMeta — the binder
arm, whose DATUM is the one thing that changes: `RelE.lam`'s `m'` at
`⟨.never⟩`. -/
theorem ResetAt.lam_step {st s1 s2 s3 : EStore} {h ty b rt rb r : EIdx}
    {m : BinderMeta} (hwf : StoreWF st)
    (hview : st.view h = some (.lam ty b m))
    (hx1 : Ext st s1) (ht : ResetAt st ty s1 rt)
    (hx2 : Ext s1 s2) (hb : ResetAt s1 b s2 rb)
    (hx3 : Ext s2 s3)
    (hr : denoteE s3 r = denoteEView s3 (.lam rt rb ⟨.never⟩)) :
    ResetAt st h s3 r :=
  RelE.lam hwf hview (fun _ _ => rfl) ((ht.ext hx2).ext hx3)
    ((hb.of_ext hx1).ext hx3) hr

theorem ResetAt.forallE_step {st s1 s2 s3 : EStore} {h ty b rt rb r : EIdx}
    {m : BinderMeta} (hwf : StoreWF st)
    (hview : st.view h = some (.forallE ty b m))
    (hx1 : Ext st s1) (ht : ResetAt st ty s1 rt)
    (hx2 : Ext s1 s2) (hb : ResetAt s1 b s2 rb)
    (hx3 : Ext s2 s3)
    (hr : denoteE s3 r = denoteEView s3 (.forallE rt rb ⟨.never⟩)) :
    ResetAt st h s3 r :=
  RelE.forallE hwf hview (fun _ _ => rfl) ((ht.ext hx2).ext hx3)
    ((hb.of_ext hx1).ext hx3) hr

theorem ResetAt.letE_step {st s1 s2 s3 s4 : EStore}
    {h ty w b rt rw rb r : EIdx} (hwf : StoreWF st)
    (hview : st.view h = some (.letE ty w b))
    (hx1 : Ext st s1) (ht : ResetAt st ty s1 rt)
    (hx2 : Ext s1 s2) (hw : ResetAt s1 w s2 rw)
    (hx3 : Ext s2 s3) (hb : ResetAt s2 b s3 rb)
    (hx4 : Ext s3 s4)
    (hr : denoteE s4 r = denoteEView s4 (.letE rt rw rb)) :
    ResetAt st h s4 r :=
  RelE.letE hwf hview (fun _ _ _ => rfl) (((ht.ext hx2).ext hx3).ext hx4)
    (((hw.of_ext hx1).ext hx3).ext hx4) ((hb.of_ext (hx1.trans hx2)).ext hx4) hr

theorem ResetAt.proj_step {st s1 s2 : EStore} {h sub rs r : EIdx} {n : NIdx}
    {i : Nat} {nm : ConLeche.Name} (hwf : StoreWF st)
    (hview : st.view h = some (.proj n i sub))
    (hx1 : Ext st s1) (hs : ResetAt st sub s1 rs) (hx2 : Ext s1 s2)
    (hr : denoteE s2 r = denoteEView s2 (.proj n i rs))
    (hn0 : denoteN st.ns n = some nm) : ResetAt st h s2 r :=
  RelE.proj hwf hview (fun _ => rfl) (hs.ext hx2) hn0
    (denoteN_ext (denoteN_ext hn0 hx1) hx2) hr

/-- con-leche: ConLeche/Kernel/ExprOps.lean:552-559 resetMeta — the LEAF
arms. -/
theorem ResetAt.leaf {st : EStore} {h : EIdx} {v : ENodeView} (hwf : StoreWF st)
    (hview : st.view h = some v)
    (hv : (∃ i, v = .bvar i) ∨ (∃ u, v = .sort u) ∨
      (∃ n us, v = .const n us) ∨ ∃ l, v = .lit l) : ResetAt st h st h := by
  intro e he
  show denoteE st h = some (Expr.resetMeta e)
  have hleaf : (∃ i, e = .bvar i) ∨ (∃ u, e = .sort u) ∨
      (∃ n us, e = .const n us) ∨ ∃ l, e = .lit l := by
    rcases hv with ⟨i, rfl⟩ | ⟨u, rfl⟩ | ⟨n, us, rfl⟩ | ⟨l, rfl⟩
    · exact Or.inl ⟨i, denote_bvar_inv hwf hview he⟩
    · obtain ⟨l, rfl, _⟩ := denote_sort_inv hwf hview he
      exact Or.inr (Or.inl ⟨l, rfl⟩)
    · obtain ⟨nm, ls, rfl, _, _⟩ := denote_const_inv hwf hview he
      exact Or.inr (Or.inr (Or.inl ⟨nm, ls, rfl⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨l, denote_lit_inv hwf hview he⟩))
  rw [resetMeta_leaf hleaf]
  exact he

/-! ### The same eight for `renameConsts` -/

theorem RenameAt.fvar_step {fn : ConLeche.Name → ConLeche.Name}
    {st s1 s2 : EStore} {h ty rt r : EIdx} {idx : Nat} (hwf : StoreWF st)
    (hview : st.view h = some (.fvar idx ty))
    (hx1 : Ext st s1) (ht : RenameAt fn st ty s1 rt) (hx2 : Ext s1 s2)
    (hr : denoteE s2 r = denoteEView s2 (.fvar idx rt)) :
    RenameAt fn st h s2 r :=
  RelE.fvar hwf hview (fun _ => rfl) (ht.ext hx2) hr

theorem RenameAt.app_step {fn : ConLeche.Name → ConLeche.Name}
    {st s1 s2 s3 : EStore} {h f a rf ra r : EIdx} (hwf : StoreWF st)
    (hview : st.view h = some (.app f a))
    (hx1 : Ext st s1) (hf : RenameAt fn st f s1 rf)
    (hx2 : Ext s1 s2) (ha : RenameAt fn s1 a s2 ra)
    (hx3 : Ext s2 s3)
    (hr : denoteE s3 r = denoteEView s3 (.app rf ra)) :
    RenameAt fn st h s3 r :=
  RelE.app hwf hview (fun _ _ => rfl) ((hf.ext hx2).ext hx3)
    ((ha.of_ext hx1).ext hx3) hr

theorem RenameAt.lam_step {fn : ConLeche.Name → ConLeche.Name}
    {st s1 s2 s3 : EStore} {h ty b rt rb r : EIdx} {m : BinderMeta}
    (hwf : StoreWF st) (hview : st.view h = some (.lam ty b m))
    (hx1 : Ext st s1) (ht : RenameAt fn st ty s1 rt)
    (hx2 : Ext s1 s2) (hb : RenameAt fn s1 b s2 rb)
    (hx3 : Ext s2 s3)
    (hr : denoteE s3 r = denoteEView s3 (.lam rt rb m)) :
    RenameAt fn st h s3 r :=
  RelE.lam hwf hview (fun _ _ => rfl) ((ht.ext hx2).ext hx3)
    ((hb.of_ext hx1).ext hx3) hr

theorem RenameAt.forallE_step {fn : ConLeche.Name → ConLeche.Name}
    {st s1 s2 s3 : EStore} {h ty b rt rb r : EIdx} {m : BinderMeta}
    (hwf : StoreWF st) (hview : st.view h = some (.forallE ty b m))
    (hx1 : Ext st s1) (ht : RenameAt fn st ty s1 rt)
    (hx2 : Ext s1 s2) (hb : RenameAt fn s1 b s2 rb)
    (hx3 : Ext s2 s3)
    (hr : denoteE s3 r = denoteEView s3 (.forallE rt rb m)) :
    RenameAt fn st h s3 r :=
  RelE.forallE hwf hview (fun _ _ => rfl) ((ht.ext hx2).ext hx3)
    ((hb.of_ext hx1).ext hx3) hr

theorem RenameAt.letE_step {fn : ConLeche.Name → ConLeche.Name}
    {st s1 s2 s3 s4 : EStore} {h ty w b rt rw rb r : EIdx} (hwf : StoreWF st)
    (hview : st.view h = some (.letE ty w b))
    (hx1 : Ext st s1) (ht : RenameAt fn st ty s1 rt)
    (hx2 : Ext s1 s2) (hw : RenameAt fn s1 w s2 rw)
    (hx3 : Ext s2 s3) (hb : RenameAt fn s2 b s3 rb)
    (hx4 : Ext s3 s4)
    (hr : denoteE s4 r = denoteEView s4 (.letE rt rw rb)) :
    RenameAt fn st h s4 r :=
  RelE.letE hwf hview (fun _ _ _ => rfl) (((ht.ext hx2).ext hx3).ext hx4)
    (((hw.of_ext hx1).ext hx3).ext hx4) ((hb.of_ext (hx1.trans hx2)).ext hx4) hr

theorem RenameAt.proj_step {fn : ConLeche.Name → ConLeche.Name}
    {st s1 s2 : EStore} {h sub rs r : EIdx} {n : NIdx} {i : Nat}
    {nm : ConLeche.Name} (hwf : StoreWF st)
    (hview : st.view h = some (.proj n i sub))
    (hx1 : Ext st s1) (hs : RenameAt fn st sub s1 rs) (hx2 : Ext s1 s2)
    (hr : denoteE s2 r = denoteEView s2 (.proj n i rs))
    (hn0 : denoteN st.ns n = some nm) : RenameAt fn st h s2 r :=
  RelE.proj hwf hview (fun _ => rfl) (hs.ext hx2) hn0
    (denoteN_ext (denoteN_ext hn0 hx1) hx2) hr

/-- con-leche: ConLeche/Kernel/ExprOps.lean:934-956 renameConsts — **the arm
the walk exists for**: a `const` node's name is replaced, its universe
arguments are not, and the walk does not recurse.  The hypothesis `hfn` is
this module's interface obligation at the one handle it is used on. -/
theorem RenameAt.const_step {fn : ConLeche.Name → ConLeche.Name}
    {st st' : EStore} {h r : EIdx} {n n' : NIdx} {us : LsIdx}
    (hwf : StoreWF st) (hview : st.view h = some (.const n us))
    (hfn : ∀ nm, denoteN st.ns n = some nm → denoteN st'.ns n' = some (fn nm))
    (hus : ∀ ls, denoteLs st.lss us = some ls → denoteLs st'.lss us = some ls)
    (hr : denoteE st' r = denoteEView st' (.const n' us)) :
    RenameAt fn st h st' r := by
  intro e he
  obtain ⟨nm, ls, rfl, hn, hl⟩ := denote_const_inv hwf hview he
  rw [hr, denoteEView, hfn nm hn, hus ls hl]
  simp [Expr.renameConsts]

/-- con-leche: ConLeche/Kernel/ExprOps.lean:934-956 renameConsts — the three
LEAF arms. -/
theorem RenameAt.leaf {fn : ConLeche.Name → ConLeche.Name} {st : EStore}
    {h : EIdx} {v : ENodeView} (hwf : StoreWF st) (hview : st.view h = some v)
    (hv : (∃ i, v = .bvar i) ∨ (∃ u, v = .sort u) ∨ ∃ l, v = .lit l) :
    RenameAt fn st h st h := by
  intro e he
  show denoteE st h = some (Expr.renameConsts fn e)
  have hleaf : (∃ i, e = .bvar i) ∨ (∃ u, e = .sort u) ∨ ∃ l, e = .lit l := by
    rcases hv with ⟨i, rfl⟩ | ⟨u, rfl⟩ | ⟨l, rfl⟩
    · exact Or.inl ⟨i, denote_bvar_inv hwf hview he⟩
    · obtain ⟨l, rfl, _⟩ := denote_sort_inv hwf hview he
      exact Or.inr (Or.inl ⟨l, rfl⟩)
    · exact Or.inr (Or.inr ⟨l, denote_lit_inv hwf hview he⟩)
  rw [renameConsts_leaf hleaf]
  exact he

/-! ## Theorem 1 for `resetMeta` — `ExprOps.lean:567`, `:633` -/

/-- con-leche: ConLeche/Verify/SimI.lean:244 SimAt — Theorem 1's statement for
one level of `resetMetaGo`'s recursion. -/
structure ResetSpec (rec : EIdx → AM EIdx) : Prop where
  run : ∀ (s₁ : AState) (h : EIdx), StateOK s₁ → ResetMemoA s₁ →
    (denoteE s₁.store h).isSome = true →
    ⦃fun s => ⌜s = s₁⌝⦄ rec h
    ⦃⇓? r s' => ⌜StateOK s' ∧ ResetMemoA s' ∧ Ext s₁.store s'.store ∧
        s'.caches = s₁.caches ∧ s'.pins = s₁.pins ∧
        (∀ i v, s₁.store.view i = some v → s'.store.view i = some v) ∧
        (∀ mi m, s₁.store.viewBM mi = some m → s'.store.viewBM mi = some m) ∧
        ResetAt s₁.store h s'.store r⌝⦄

/-- con-leche: ConLeche/Kernel/ExprOps.lean:552-559 resetMeta
con-leche: ConLeche/Kernel/ExprOps.lean:579-615 resetMetaGo
**THEOREM 1 for `resetMeta`**, at one level of the recursion, by induction on
the fuel. -/
theorem resetMetaGo_spec : ∀ fuel, ResetSpec (resetMetaGo fuel) := by
  intro fuel
  induction fuel with
  | zero =>
    constructor
    intro s₀ h _ _ _
    mvcgen [resetMetaGo_zero]
    all_goals bridge_vcs [Expr.resetMeta]
  | succ fuel ih =>
    constructor
    intro s₀ h hok hm hden
    have hrec := ih.run
    mvcgen [resetMetaGo_succ, resetArmFVar, resetArmApp, resetArmLam, resetArmForallE, resetArmLet, resetArmProj, hrec]
    all_goals try bridge_vcs [Expr.resetMeta]
    -- Ten structural verification conditions remain, in goal order: the four
    -- LEAF views, then the six rebuilding arms.  This is task #97s round 2's
    -- item 3 at six arms; the memo insert's invariant is inside each arm's
    -- postcondition because `ExprOps/MemoSpecs.lean`'s memo-set spec puts the
    -- pure function there (see its header).
    next =>
      bridge_peel
      subst_vars
      exact ⟨hok, hm, Ext.refl _, rfl, rfl, fun _ _ hi => hi,
        fun _ _ hi => hi, ResetAt.leaf hok.wf (by arm_hyp2) (by grind)⟩
    next =>
      bridge_peel
      subst_vars
      exact ⟨hok, hm, Ext.refl _, rfl, rfl, fun _ _ hi => hi,
        fun _ _ hi => hi, ResetAt.leaf hok.wf (by arm_hyp2) (by grind)⟩
    next =>
      bridge_peel
      subst_vars
      exact ⟨hok, hm, Ext.refl _, rfl, rfl, fun _ _ hi => hi,
        fun _ _ hi => hi, ResetAt.leaf hok.wf (by arm_hyp2) (by grind)⟩
    next =>
      bridge_peel
      subst_vars
      exact ⟨hok, hm, Ext.refl _, rfl, rfl, fun _ _ hi => hi,
        fun _ _ hi => hi, ResetAt.leaf hok.wf (by arm_hyp2) (by grind)⟩
    -- `fvar`: the annotation is descended into
    next =>
      bridge_peel
      subst_vars
      have hans := ResetAt.fvar_step hok.wf (by arm_hyp2) (by arm_hyp2) (by arm_hyp2) (by arm_hyp2) (by arm_hyp2)
      have hret := RelE.retarget_self hans (by grind only [Ext.trans]) hden
      exact ⟨by grind only [StateOK, StateOK.mk],
        by grind [MemoOK.mono, MemoOK.insert, Ext.refl],
        by grind only [Ext.trans], by grind, by grind, by grind, by grind,
        hans.ext (by grind only [Ext.refl])⟩
    -- `app`
    next =>
      bridge_peel
      subst_vars
      have hans := ResetAt.app_step hok.wf (by arm_hyp2) (by arm_hyp2) (by arm_hyp2) (by arm_hyp2) (by arm_hyp2) (by arm_hyp2) (by arm_hyp2)
      have hret := RelE.retarget_self hans (by grind only [Ext.trans]) hden
      exact ⟨by grind only [StateOK, StateOK.mk],
        by grind [MemoOK.mono, MemoOK.insert, Ext.refl],
        by grind only [Ext.trans], by grind, by grind, by grind, by grind,
        hans.ext (by grind only [Ext.refl])⟩
    -- `lam` and `forallE`: the datum is REPLACED by the placeholder
    next =>
      bridge_peel
      subst_vars
      have hans := ResetAt.lam_step hok.wf (by arm_hyp2) (by arm_hyp2) (by arm_hyp2) (by arm_hyp2) (by arm_hyp2) (by arm_hyp2) (by arm_hyp2)
      have hret := RelE.retarget_self hans (by grind only [Ext.trans]) hden
      exact ⟨by grind only [StateOK, StateOK.mk],
        by grind [MemoOK.mono, MemoOK.insert, Ext.refl],
        by grind only [Ext.trans], by grind, by grind, by grind, by grind,
        hans.ext (by grind only [Ext.refl])⟩
    next =>
      bridge_peel
      subst_vars
      have hans := ResetAt.forallE_step hok.wf (by arm_hyp2) (by arm_hyp2) (by arm_hyp2) (by arm_hyp2) (by arm_hyp2) (by arm_hyp2) (by arm_hyp2)
      have hret := RelE.retarget_self hans (by grind only [Ext.trans]) hden
      exact ⟨by grind only [StateOK, StateOK.mk],
        by grind [MemoOK.mono, MemoOK.insert, Ext.refl],
        by grind only [Ext.trans], by grind, by grind, by grind, by grind,
        hans.ext (by grind only [Ext.refl])⟩
    -- `letE`
    next =>
      bridge_peel
      subst_vars
      have hans := ResetAt.letE_step hok.wf (by arm_hyp2) (by arm_hyp2) (by arm_hyp2) (by arm_hyp2) (by arm_hyp2) (by arm_hyp2) (by arm_hyp2) (by arm_hyp2) (by arm_hyp2)
      have hret := RelE.retarget_self hans (by grind only [Ext.trans]) hden
      exact ⟨by grind only [StateOK, StateOK.mk],
        by grind [MemoOK.mono, MemoOK.insert, Ext.refl],
        by grind only [Ext.trans], by grind, by grind, by grind, by grind,
        hans.ext (by grind only [Ext.refl])⟩
    -- `proj`
    next =>
      bridge_peel
      subst_vars
      obtain ⟨nm, es, _, hn0, _⟩ := denote_eq_proj hok.wf (by arm_hyp2) hden
      have hans := ResetAt.proj_step hok.wf (by arm_hyp2) (by arm_hyp2)
        (by arm_hyp2) (by arm_hyp2) (by arm_hyp2) hn0
      have hret := RelE.retarget_self hans (by grind only [Ext.trans]) hden
      exact ⟨by grind only [StateOK, StateOK.mk],
        by grind [MemoOK.mono, MemoOK.insert, Ext.refl],
        by grind only [Ext.trans], by grind, by grind, by grind, by grind,
        hans.ext (by grind only [Ext.refl])⟩

end ConRon.Bridge.ExprOps
