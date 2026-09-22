/-
# `ConRon.Bridge.ExprOps.Owed` — the eight twins the earlier round only stated

DESIGN §8.2's Theorem 1 for the eight twins of `Arena/ExprOps.lean` whose
STATEMENT an earlier round owed and whose PROOF it did not reach.  **All eight
are proved here** (task #97-P3-2): five `…Fast` entry brackets and the three
walks whose fuel induction the round ran out on —

* `abstract1Fast` and `abstractRangeFast`, the two brackets over the EXECUTED
  abstraction walks, and `abstractRangeGo` itself;
* `renameConstsGo` and `renameConstsFast`;
* `resetMetaFast`, the bracket over `Reset.lean`'s `resetMetaGo_spec`;
* `instLPGo` and `instLPFast`.

`Bridge/ExprOps/{Abs,Reset,InstLP,MemoSpecs}.lean` carry the step-lemma layer
each of them consumes; what is added here is the three `…Spec` records the
three walks are inducted over (`AbsRangeGoSpec`, `RenameSpec`, `InstLPSpec`),
the arm step lemmas those three need that the other modules do not already
have, and four pieces of arena/spec infrastructure that belong further down
the stack and are flagged in place (`ns_of_lss`, `view_eq_of_tables`,
`readNameM_specF` / `readNamesM_specF`).

## The deviations each statement carries

The ones `Arena/ExprOps.lean`'s own doc comments name:

* `abstractRangeGo` / `abstractRangeFast` are the EXECUTED form and
  `abstractRange` (proved in `Abs.lean`) is the SPEC descent — task
  #97-P6-11's clause change, whose equations are `Abs.lean`'s
  `abstractRange_zero_eq` and `abstractRange_of_fvarRange_le`.  Both call
  `fvarB` before they read the store, so both carry `Abs.lean`'s `FvarBSpec`
  as a hypothesis (this module does not import `ExprOps/Ranges.lean` and
  cannot discharge it);
* `renameConstsGo`'s `f : NIdx → NIdx` is a map on HANDLES, so its theorem
  carries the hypothesis that `f` denotes con-leche's `fn : Name → Name`.
  That hypothesis is about `denoteN` at ONE store and the walk's recursive
  calls run at later ones; it transports because the walk never interns a
  NAME, which is what `RenameSpec`'s `s'.store.ns = ns0` conjunct records;
* `instLPGo`'s `ks`/`us` are TRANSIENT `List Name` / `List Level` (DESIGN
  §8.3 lesson 4), so `instLPFast`'s theorem carries the readback hypotheses
  its entry establishes with `readNamesM` / `readLevelsM`.

## Three statement changes this round had to make

The shapes the earlier round wrote down were not provable, and the reasons are
worth keeping:

1. **`abstractRangeGo_spec`'s memo invariant is `AbsRangeMemoA d k`, not
   `Abs1MemoA d`.**  The table `abs1C` is shared by the two abstraction walks
   (`Arena/ExprOps.lean`: "That is a table IDENTITY, not a clause"), and what
   it holds inside an `abstractRangeFast` call is `abstractRange` answers.
   `Abs1MemoA d` is the `abstract1` reading and is false of this walk for
   every `k ≠ 1`.
2. **`abstractRangeFast_spec`'s and `instLPFast_spec`'s memo clause is a
   DISJUNCTION**, `s'.memos.xC = ∅ ∨ s' = s₀`, where the other three entries
   carry the equation.  Both of these entries test their cutoff FIRST and
   return the subject without clearing anything — `abstractRangeFast` at
   `k = 0` (task #97-P6-11) and `instLPFast` at `hasLP = false` (the cutoff
   hoisted over the readbacks, task #97-P6-10).  The second disjunct is the
   stronger of the two for a caller: nothing moved at all.
3. **`instLPGo_spec` and `instLPFast_spec` do NOT frame `s'.caches`.**
   `ExprOps/InstLP.lean`'s header says why: the two LEVEL arms read a level
   back and the memoised readback WRITES `caches.readLC` / `caches.readLsC`.
   What is carried instead is the readback CLAUSES `ReadLCacheOK` and
   `ReadLsCacheOK`, as hypotheses and as conjuncts.  The third clause
   (`ReadNCacheOK`, which `readNamesM` needs) is a hypothesis of
   `instLPFast_spec` and NOT a conjunct: `ExprOps/InstLP.lean`'s
   `substLMemoAt_spec` does not frame `caches.readNC`, and adding that one
   conjunct there would give it back.
-/
import ConRon.Bridge.ExprOps.Abs
import ConRon.Bridge.ExprOps.Reset
import ConRon.Bridge.ExprOps.InstLP
import ConRon.Bridge.SpecsL

namespace ConRon.Bridge.ExprOps

set_option autoImplicit false
set_option mvcgen.warning false
set_option maxHeartbeats 4000000

open ConLeche ConRon.Arena ConRon.Bridge Std.Do

/-! ### Attribute hygiene

`ExprOps/Abs.lean`'s `internRebuiltBindI_specV` — `Bridge/Specs.lean`'s
`internRebuiltBindI_spec'` with the view-monotonicity conjunct
`Bridge/StoreBM.lean`'s "what is left to do" list asks for — is tagged
`@[local spec high]` there, and a LOCAL attribute does not travel through an
import.  The executed `abstractRange` walk below needs it for exactly the
reason the executed `abstract1` walk does, so this file repeats the line (as
every file of this tier repeats `attribute [-grind] RelE.ext …`). -/
attribute [local spec high] internRebuiltBindI_specV


/-! ## `abstract1`'s entry -/

/-- con-leche: ConLeche/Kernel/ExprOps.lean:1930-1932 abstract1Fast — the
bracket over `abstract1Go_spec`, whose shape is `ExprOps/Inst1.lean`'s
`instantiate1Fast_spec`: the memo is cleared before and after, and the cleared
memo satisfies `Abs1MemoA` for free (`MemoOK.of_empty`).  `hfv` is the
`fvarB` assumption `abstract1Go_spec` takes and this module cannot discharge
(it does not import `ExprOps/Ranges.lean`). -/
theorem abstract1Fast_spec (hfv : FvarBSpec) (fuel : Nat) (s₀ : AState)
    (e : EIdx) (d k : Nat)
    (hok : StateOK s₀) (hden : (denoteE s₀.store e).isSome = true) :
    ⦃fun s => ⌜s = s₀⌝⦄ abstract1Fast fuel e d k
    ⦃⇓? r s' => ⌜StateOK s' ∧ Ext s₀.store s'.store ∧
        s'.caches = s₀.caches ∧ s'.pins = s₀.pins ∧ s'.memos.abs1C = ∅ ∧
        RelE (fun x => Expr.abstract1 x d k) s₀.store e s'.store r⌝⦄ := by
  have hr := (abstract1Go_spec hfv d fuel).run
  mvcgen [abstract1Fast, hr]
  all_goals bridge_vcs [Expr.abstract1]

/-! ## `abstractRange`'s executed form -/

/-! ### `AbsRangeAt`'s step lemmas at the EXECUTED walk's own hypotheses

`ExprOps/Abs.lean`'s `AbsRangeAt.*_step` are stated at `st.view`; the executed
walk reads the PROJECTIONS behind a tag test and calls `fvarB` before it reads
the store at all.  These are `Abs1At.*_step'`'s shape at `abstractRange`: the
extra hypothesis `hst : st0 = st` is the `fvarB` hop (`fvarB`'s Theorem 1
frames the store with an EQUATION, not by leaving the state alone), and with
it every other hypothesis of an arm is found by `assumption`. -/

/-- con-leche: none — `AbsRangeAt.app_step` at the arm's own hypotheses. -/
theorem AbsRangeAt.app_step' {d k c : Nat} {st st0 s1 s2 s3 : EStore}
    {h f a rf ra r : EIdx} (hst : st0 = st) (hwf : StoreWF st)
    (htg : (h.tag == ETag.app) = true) (hva : some (f, a) = st0.viewApp h)
    (hx1 : Ext st0 s1) (hf : AbsRangeAt d k c st0 f s1 rf)
    (hx2 : Ext s1 s2) (ha : AbsRangeAt d k c s1 a s2 ra)
    (hx3 : Ext s2 s3) (hr : denoteE s3 r = denoteEView s3 (.app rf ra)) :
    AbsRangeAt d k c st h s3 r := by
  subst hst
  exact AbsRangeAt.app_step hwf (view_of_viewApp_tag htg hva.symm) hx1 hf hx2
    ha hx3 hr

/-- con-leche: none — `AbsRangeAt.bind_step` at the arm's own hypotheses: the
binder arm reads the datum's HANDLE, and the BODY descends at `c + 1`. -/
theorem AbsRangeAt.bind_step' {d k c : Nat} {st st0 s1 s2 s3 : EStore}
    {h ty b rt rb r : EIdx} {mi : BMIdx} (hst : st0 = st) (hwf : StoreWF st)
    (htg : ETag.isBind h.tag = true)
    (hvb : some (ty, b, mi) = st0.viewBindI h)
    (hx1 : Ext st0 s1) (ht : AbsRangeAt d k c st0 ty s1 rt)
    (_hvm1 : ∀ j w, st0.view j = some w → s1.view j = some w)
    (hbm1 : ∀ mj mv, st0.viewBM mj = some mv → s1.viewBM mj = some mv)
    (hx2 : Ext s1 s2) (hb : AbsRangeAt d k (c + 1) s1 b s2 rb)
    (_hvm2 : ∀ j w, s1.view j = some w → s2.view j = some w)
    (hbm2 : ∀ mj mv, s1.viewBM mj = some mv → s2.viewBM mj = some mv)
    (hx3 : Ext s2 s3)
    (hr : ∀ mv, s2.viewBM mi = some mv →
      s3.view r = some (eBindView h.tag rt rb mv) ∧
      denoteE s3 r = denoteEView s3 (eBindView h.tag rt rb mv)) :
    AbsRangeAt d k c st h s3 r := by
  subst hst
  obtain ⟨mv, hbm0, _, hvw0⟩ := view_of_viewBindI_wf hwf htg hvb.symm
  obtain ⟨_, hden3⟩ := hr mv (hbm2 mi mv (hbm1 mi mv hbm0))
  exact AbsRangeAt.bind_step hwf htg hvw0 hx1 ht hx2 hb hx3 hden3

/-- con-leche: none — `AbsRangeAt.letE_step` at the arm's own hypotheses. -/
theorem AbsRangeAt.letE_step' {d k c : Nat} {st st0 s1 s2 s3 s4 : EStore}
    {h ty w b rt rw rb r : EIdx} (hst : st0 = st) (hwf : StoreWF st)
    (htg : (h.tag == ETag.letE) = true)
    (hvl : some (ty, w, b) = st0.viewLet h)
    (hx1 : Ext st0 s1) (ht : AbsRangeAt d k c st0 ty s1 rt)
    (hx2 : Ext s1 s2) (hw : AbsRangeAt d k c s1 w s2 rw)
    (hx3 : Ext s2 s3) (hb : AbsRangeAt d k (c + 1) s2 b s3 rb)
    (hx4 : Ext s3 s4)
    (hr : denoteE s4 r = denoteEView s4 (.letE rt rw rb)) :
    AbsRangeAt d k c st h s4 r := by
  subst hst
  exact AbsRangeAt.letE_step hwf (view_of_viewLet_tag htg hvl.symm) hx1 ht hx2
    hw hx3 hb hx4 hr

/-- con-leche: none — `AbsRangeAt.proj_step` at the arm's own hypotheses.
The struct name's denotation comes from `denote_eq_proj`, whose existential
`grind` cannot see through, so the lemma takes it out itself. -/
theorem AbsRangeAt.proj_step' {d k c : Nat} {st st0 s1 s2 : EStore}
    {h sub rs r : EIdx} {n : NIdx} {i : Nat}
    (hst : st0 = st) (hwf : StoreWF st)
    (hden : (denoteE st h).isSome = true)
    (htg : (h.tag == ETag.proj) = true)
    (hvp : some (n, i, sub) = st0.viewProj h)
    (hx1 : Ext st0 s1) (hs : AbsRangeAt d k c st0 sub s1 rs)
    (hx2 : Ext s1 s2)
    (hr : denoteE s2 r = denoteEView s2 (.proj n i rs)) :
    AbsRangeAt d k c st h s2 r := by
  subst hst
  obtain ⟨nm, es, _, hn0, _⟩ :=
    denote_eq_proj hwf (view_of_viewProj_tag htg hvp.symm) hden
  exact AbsRangeAt.proj_step hwf (view_of_viewProj_tag htg hvp.symm) hx1 hs hx2
    hr hn0

/-- con-leche: none — the `fvar` arm IN the range, at the arm's own
hypotheses: `absRangeArmFVar` reads only the index. -/
theorem AbsRangeAt.fvar_hit' {d k c idx : Nat} {st st0 st' : EStore}
    {h r : EIdx} (hst : st0 = st) (hwf : StoreWF st)
    (htg : (h.tag == ETag.fvar) = true) (hidxv : some idx = st0.viewFVarIdx h)
    (hin : (decide (d ≤ idx) && decide (idx < d + k)) = true)
    (hr : denoteE st' r = some (.bvar (c + (d + k - 1 - idx)))) :
    AbsRangeAt d k c st h st' r := by
  subst hst
  obtain ⟨ty, hty⟩ := viewFVarTy_of_viewFVarIdx hidxv.symm
  exact AbsRangeAt.fvar_hitB hwf (view_of_viewFVar_tag htg hidxv.symm hty) hin
    hr

/-- con-leche: none — and OUTSIDE it, where the handle answers itself. -/
theorem AbsRangeAt.fvar_miss' {d k c idx : Nat} {st st0 st' : EStore}
    {h : EIdx} (hst : st0 = st) (hwf : StoreWF st)
    (htg : (h.tag == ETag.fvar) = true) (hidxv : some idx = st0.viewFVarIdx h)
    (hout : ¬ ((decide (d ≤ idx) && decide (idx < d + k)) = true))
    (hx : Ext st0 st') : AbsRangeAt d k c st h st' h := by
  subst hst
  obtain ⟨ty, hty⟩ := viewFVarTy_of_viewFVarIdx hidxv.symm
  exact (AbsRangeAt.fvar_missB hwf (view_of_viewFVar_tag htg hidxv.symm hty)
    hout).ext hx

/-- con-leche: none — the catch-all arm, at the arm's own hypotheses: a
handle whose tag is none of the five the walk dispatches on denotes `bvar`,
`sort`, `const` or `lit`.  The view the lemma needs is the one its own
denotation gives, so the arm supplies `hden` and nothing else. -/
theorem AbsRangeAt.leaf'' {st st' : EStore} (hwf : StoreWF st) {h : EIdx}
    {d k c : Nat} (hden : (denoteE st h).isSome = true)
    (hfvar : ¬ ((h.tag == ETag.fvar) = true))
    (happ : ¬ ((h.tag == ETag.app) = true))
    (hbind : ¬ (ETag.isBind h.tag = true))
    (hlet : ¬ ((h.tag == ETag.letE) = true))
    (hproj : ¬ ((h.tag == ETag.proj) = true)) (hx : Ext st st') :
    AbsRangeAt d k c st h st' h := by
  obtain ⟨e, he⟩ := Option.isSome_iff_exists.mp hden
  obtain ⟨v, hv⟩ := denoteE_view he
  exact (AbsRangeAt.leaf hwf hv (by simpa using hfvar) (by simpa using happ)
    (by simpa using hbind) (by simpa using hlet) (by simpa using hproj)).ext hx

/-- con-leche: ConLeche/Kernel/ExprOps.lean:791-811 abstractRange —
Theorem 1's statement for one level of the EXECUTED descent's recursion.
The memo invariant is `AbsRangeMemoA d k` and NOT `Abs1MemoA d`: the table
`abs1C` is shared by the two walks, and what it holds inside an
`abstractRangeFast` call is `abstractRange` answers (`Arena/ExprOps.lean`'s
"That is a table IDENTITY, not a clause"). -/
structure AbsRangeGoSpec (d k : Nat) (rec : EIdx → Nat → AM EIdx) : Prop where
  run : ∀ (s₁ : AState) (h : EIdx) (c : Nat), StateOK s₁ →
    AbsRangeMemoA d k s₁ → (denoteE s₁.store h).isSome = true →
    ⦃fun s => ⌜s = s₁⌝⦄ rec h c
    ⦃⇓? r s' => ⌜StateOK s' ∧ AbsRangeMemoA d k s' ∧ Ext s₁.store s'.store ∧
        s'.caches = s₁.caches ∧ s'.pins = s₁.pins ∧
        (∀ i v, s₁.store.view i = some v → s'.store.view i = some v) ∧
        (∀ mi m, s₁.store.viewBM mi = some m → s'.store.viewBM mi = some m) ∧
        AbsRangeAt d k c s₁.store h s'.store r⌝⦄

/-- con-leche: ConLeche/Kernel/ExprOps.lean:791-811 abstractRange —
**THEOREM 1 for the EXECUTED `abstractRange`**, at one level of the
recursion, by induction on the fuel.  `abstract1Go_spec`'s shape: the `fvarB`
cutoff, the tag chain, the five arms by name and the catch-all. -/
theorem abstractRangeGo_specS (hfv : FvarBSpec) (d k : Nat) :
    ∀ fuel, AbsRangeGoSpec d k (fun h c => abstractRangeGo d k fuel h c) := by
  intro fuel
  induction fuel with
  | zero =>
    constructor
    intro s₀ h c _ _ _
    mvcgen [abstractRangeGo_zero]
    all_goals bridge_vcs [Expr.abstractRange]
  | succ fuel ih =>
    constructor
    intro s₀ h c hok hm hden
    have hrec := ih.run
    have hfvb := hfv.run
    mvcgen [abstractRangeGo_succ, absRangeGoArmApp, absRangeGoArmBind,
      absRangeArmFVar, absRangeGoArmLet, absRangeGoArmProj, hrec, hfvb]
    all_goals try bridge_vcs [Expr.abstractRange]
    all_goals try bridge_vcs [Expr.abstractRange, view_of_viewBindI,
      view_of_viewBindI_wf, isSome_eBindView, view_isSome]
    -- Eleven structural verification conditions remain, in goal order: the
    -- derived-word cutoff, `app`'s postcondition, the binder arm's four side
    -- conditions and its postcondition, the `fvar` arm's two branches,
    -- `letE`'s and `proj`'s postconditions and the catch-all.  This is
    -- `abstract1Go_spec`'s list exactly — the two executed walks differ only
    -- at the `fvar` arm and at the binder body's cursor.
    -- the cutoff
    next =>
      bridge_peel
      subst_vars
      refine ⟨by grind only [StateOK, StateOK.mk],
        by grind [MemoOK.mono, Ext.refl], by grind only [Ext.refl], by grind,
        by grind, by grind, by grind, ?_⟩
      exact (AbsRangeAt.cutoff (by abs_hyp) (by abs_hyp)).ext
        (by grind only [Ext.refl])
    -- `app`
    next =>
      bridge_peel
      subst_vars
      have hans := AbsRangeAt.app_step' (by abs_hyp) hok.wf
        (by abs_hyp) (by abs_hyp) (by abs_hyp) (by abs_hyp) (by abs_hyp)
        (by abs_hyp) (by abs_hyp) (by abs_hyp)
      have hret := RelE.retarget_self hans (by grind only [Ext.trans]) hden
      exact ⟨by grind only [StateOK, StateOK.mk],
        by grind [MemoOK.mono, MemoOK.insert, Ext.refl],
        by grind only [Ext.trans], by grind, by grind, by grind, by grind,
        hans.ext (by grind only [Ext.refl])⟩
    -- the binder arm's four side conditions
    next =>
      bridge_peel
      subst_vars
      exact bmOK_hop (by abs_hyp) hok.wf (by abs_hyp) (by abs_hyp) (by abs_hyp)
    next =>
      bridge_peel
      subst_vars
      obtain ⟨hty, _⟩ :=
        bindI_children_hop (by abs_hyp) hok.wf (by abs_hyp) (by abs_hyp) hden
      exact view_isSome_of_rel hty (by abs_hyp) (by abs_hyp)
    next =>
      bridge_peel
      subst_vars
      obtain ⟨_, hb⟩ :=
        bindI_children_hop (by abs_hyp) hok.wf (by abs_hyp) (by abs_hyp) hden
      exact view_isSome_of_rel (denote_isSome_ext hb (by abs_hyp)) (by abs_hyp)
        (by grind only [Ext.refl])
    next =>
      bridge_peel
      subst_vars
      refine bindI_hsame ?_ rfl (by abs_hyp) (by abs_hyp)
        (by abs_hyp) (by abs_hyp) (by abs_hyp) (by abs_hyp)
      grind [StateOK]
    -- the binder arm's postcondition
    next =>
      bridge_peel
      subst_vars
      have hans := AbsRangeAt.bind_step' (by abs_hyp) hok.wf (by abs_hyp)
        (by abs_hyp) (by abs_hyp) (by abs_hyp) (by abs_hyp) (by abs_hyp)
        (by abs_hyp) (by abs_hyp) (by abs_hyp) (by abs_hyp) (by abs_hyp)
        (by abs_hyp)
      have hret := RelE.retarget_self hans (by grind only [Ext.trans]) hden
      exact ⟨by grind only [StateOK, StateOK.mk],
        by grind [MemoOK.mono, MemoOK.insert, Ext.refl],
        by grind only [Ext.trans], by grind, by grind, by grind, by grind,
        hans.ext (by grind only [Ext.refl])⟩
    -- the `fvar` arm: in the range, then outside it
    next =>
      bridge_peel
      subst_vars
      intro _hwf2 hx _hlss _hmem _hcach _hpin _hvm _hbm _hview2 hr
      refine ⟨by grind only [StateOK, StateOK.mk],
        by grind [MemoOK.mono, Ext.refl], by grind only [Ext.trans],
        by grind, by grind, by grind, by grind, ?_⟩
      exact AbsRangeAt.fvar_hit' (by abs_hyp) hok.wf (by abs_hyp) (by abs_hyp)
        (by abs_hyp) (by rw [hr, denoteEView])
    next =>
      bridge_peel
      subst_vars
      exact ⟨by grind only [StateOK, StateOK.mk],
        by grind [MemoOK.mono, Ext.refl], by grind only [Ext.refl], by grind,
        by grind, by grind, by grind,
        AbsRangeAt.fvar_miss' (by abs_hyp) hok.wf (by abs_hyp) (by abs_hyp)
          (by abs_hyp) (by grind only [Ext.refl])⟩
    -- `letE`
    next =>
      bridge_peel
      subst_vars
      have hans := AbsRangeAt.letE_step' (by abs_hyp) hok.wf
        (by abs_hyp) (by abs_hyp) (by abs_hyp) (by abs_hyp) (by abs_hyp)
        (by abs_hyp) (by abs_hyp) (by abs_hyp) (by abs_hyp) (by abs_hyp)
      have hret := RelE.retarget_self hans (by grind only [Ext.trans]) hden
      exact ⟨by grind only [StateOK, StateOK.mk],
        by grind [MemoOK.mono, MemoOK.insert, Ext.refl],
        by grind only [Ext.trans], by grind, by grind, by grind, by grind,
        hans.ext (by grind only [Ext.refl])⟩
    -- `proj`
    next =>
      bridge_peel
      subst_vars
      have hans := AbsRangeAt.proj_step' (by abs_hyp) hok.wf hden
        (by abs_hyp) (by abs_hyp) (by abs_hyp) (by abs_hyp) (by abs_hyp)
        (by abs_hyp)
      have hret := RelE.retarget_self hans (by grind only [Ext.trans]) hden
      exact ⟨by grind only [StateOK, StateOK.mk],
        by grind [MemoOK.mono, MemoOK.insert, Ext.refl],
        by grind only [Ext.trans], by grind, by grind, by grind, by grind,
        hans.ext (by grind only [Ext.refl])⟩
    -- the catch-all: the four leaves
    next =>
      bridge_peel
      subst_vars
      exact ⟨by grind only [StateOK, StateOK.mk],
        by grind [MemoOK.mono, Ext.refl], by grind only [Ext.refl], by grind,
        by grind, by grind, by grind,
        AbsRangeAt.leaf'' hok.wf hden (by abs_hyp) (by abs_hyp) (by abs_hyp)
          (by abs_hyp) (by abs_hyp) (by grind only [Ext.refl])⟩

/-- con-leche: ConLeche/Kernel/ExprOps.lean:791-811 abstractRange — the
EXECUTED descent at one state, against the SPEC descent `Abs.lean` proves.
Its step lemmas are `Abs.lean`'s `AbsRangeAt.*`. -/
theorem abstractRangeGo_spec (hfv : FvarBSpec) (d k : Nat) (fuel : Nat)
    (s₀ : AState) (c : EIdx)
    (cur : Nat) (hok : StateOK s₀) (hm : AbsRangeMemoA d k s₀)
    (hden : (denoteE s₀.store c).isSome = true) :
    ⦃fun s => ⌜s = s₀⌝⦄ abstractRangeGo d k fuel c cur
    ⦃⇓? r s' => ⌜StateOK s' ∧ Ext s₀.store s'.store ∧
        s'.caches = s₀.caches ∧ s'.pins = s₀.pins ∧
        RelE (fun x => Expr.abstractRange x d k cur) s₀.store c s'.store r⌝⦄ := by
  have hr := (abstractRangeGo_specS hfv d k fuel).run
  mvcgen [hr]
  all_goals bridge_vcs [Expr.abstractRange]

/-- con-leche: ConLeche/Cached/ExprOpsC.lean:748-755 abstractRangeC — the
bracket over `abstractRangeGo_spec`.

**The memo clause is a DISJUNCTION here and an equation at the other four
entries** (a statement change this round had to make: the shape the round
owed was not provable).  `abstractRangeFast` tests `k = 0` FIRST and returns
the subject without clearing anything (`Arena/ExprOps.lean`'s own clause, and
what makes the annotation telescope's outermost binder domain cost nothing),
so on that branch the shared `abs1C` table is whatever the caller had.  What
is true of BOTH branches is "either the table was dropped or nothing moved at
all", and the second disjunct is the stronger of the two for a caller. -/
theorem abstractRangeFast_spec (hfv : FvarBSpec) (fuel : Nat) (s₀ : AState)
    (e : EIdx) (d k c : Nat) (hok : StateOK s₀)
    (hden : (denoteE s₀.store e).isSome = true) :
    ⦃fun s => ⌜s = s₀⌝⦄ abstractRangeFast fuel e d k c
    ⦃⇓? r s' => ⌜StateOK s' ∧ Ext s₀.store s'.store ∧
        s'.caches = s₀.caches ∧ s'.pins = s₀.pins ∧
        (s'.memos.abs1C = ∅ ∨ s' = s₀) ∧
        RelE (fun x => Expr.abstractRange x d k c) s₀.store e s'.store r⌝⦄ := by
  have hr := fun (s₁ : AState) (cc : EIdx) (cur : Nat) =>
    abstractRangeGo_spec hfv d k fuel s₁ cc cur
  mvcgen [abstractRangeFast, hr]
  all_goals try bridge_vcs [Expr.abstractRange]
  -- The `k = 0` clause, which returns the subject: `abstractRange_zero_eq` is
  -- its licence and nothing in the state moves.
  all_goals
    (bridge_peel
     subst_vars
     refine ⟨hok, Ext.refl _, rfl, rfl, Or.inr rfl, ?_⟩
     intro x hx
     rw [hx]
     simp only [abstractRange_zero_eq])

/-! ## `resetMeta`'s entry -/

/-- con-leche: ConLeche/Kernel/ExprOps.lean:688 resetMetaFast — the bracket
over `Reset.lean`'s `resetMetaGo_spec`, in `ExprOps/Inst1.lean`'s
`instantiate1Fast_spec` shape: the memo is cleared before and after, and the
cleared memo satisfies `ResetMemoA` for free (`MemoOK.of_empty`). -/
theorem resetMetaFast_spec (fuel : Nat) (s₀ : AState) (e : EIdx)
    (hok : StateOK s₀) (hden : (denoteE s₀.store e).isSome = true) :
    ⦃fun s => ⌜s = s₀⌝⦄ resetMetaFast fuel e
    ⦃⇓? r s' => ⌜StateOK s' ∧ Ext s₀.store s'.store ∧
        s'.caches = s₀.caches ∧ s'.pins = s₀.pins ∧ s'.memos.resetC = ∅ ∧
        RelE Expr.resetMeta s₀.store e s'.store r⌝⦄ := by
  have hr := (resetMetaGo_spec fuel).run
  mvcgen [resetMetaFast, hr]
  all_goals bridge_vcs [Expr.resetMeta]

/-! ## `renameConsts`

`f : NIdx → NIdx` is a map on HANDLES; con-leche's is `fn : Name → Name`.
The hypothesis that relates them is what `Arena/ExprOps.lean`'s own note
("the only call site is the modeled-block contract, whose map is a lookup in
a table") says the `DeclCheck` tier will discharge. -/

/-- con-leche: none — `EStore.ns` is a PROJECTION of `lss`
(`Arena/Store.lean:1149`), so any step that frames `lss` frames the name
store too.  `Arena/WFProofs.lean:2318` makes the same step inline; this is it
as a lemma, which is what lets the walk below transport `hf`. -/
theorem ns_of_lss {st st' : EStore} (h : st'.lss = st.lss) :
    st'.ns = st.ns := by
  simp only [EStore.ns, h]

/-- con-leche: ConLeche/Kernel/ExprOps.lean:999-1036 renameConstsGo —
Theorem 1's statement for one level of `renameConstsGo`'s recursion.

**The name store is a parameter, not a state.**  The interface obligation
`hf` ("the handle renaming denotes the name renaming") is a statement about
`denoteN`, and the walk's recursive calls run at LATER stores.  It transports
because the walk never interns a NAME: every intern spec of
`ExprOps/MemoSpecs.lean` frames `s'.store.lss`, and `EStore.ns` is a
projection of `lss` (`ns_of_lss`).  Carrying `s'.store.ns = ns0` as a
postcondition conjunct — rather than re-proving the obligation at every
intermediate store — is what makes the induction go through. -/
structure RenameSpec (f : NIdx → NIdx) (fn : ConLeche.Name → ConLeche.Name)
    (ns0 : NStore) (rec : EIdx → AM EIdx) : Prop where
  run : ∀ (s₁ : AState) (h : EIdx), StateOK s₁ → RenameMemoA fn s₁ →
    s₁.store.ns = ns0 → (denoteE s₁.store h).isSome = true →
    ⦃fun s => ⌜s = s₁⌝⦄ rec h
    ⦃⇓? r s' => ⌜StateOK s' ∧ RenameMemoA fn s' ∧ Ext s₁.store s'.store ∧
        s'.store.ns = ns0 ∧
        s'.caches = s₁.caches ∧ s'.pins = s₁.pins ∧
        (∀ i v, s₁.store.view i = some v → s'.store.view i = some v) ∧
        (∀ mi m, s₁.store.viewBM mi = some m → s'.store.viewBM mi = some m) ∧
        RenameAt fn s₁.store h s'.store r⌝⦄

/-- con-leche: ConLeche/Kernel/ExprOps.lean:930-956 renameConsts
con-leche: ConLeche/Kernel/ExprOps.lean:999-1036 renameConstsGo
**THEOREM 1 for `renameConsts`**, at one level of the recursion, by induction
on the fuel.  `resetMetaGo_spec`'s six rebuilding arms plus the inline
`const` arm the walk exists for (`Reset.lean`'s `RenameAt.const_step`). -/
theorem renameConstsGo_specS (f : NIdx → NIdx)
    (fn : ConLeche.Name → ConLeche.Name) (ns0 : NStore)
    (hf : ∀ (n : NIdx) (x : ConLeche.Name), denoteN ns0 n = some x →
      denoteN ns0 (f n) = some (fn x)) :
    ∀ fuel, RenameSpec f fn ns0 (renameConstsGo f fuel) := by
  intro fuel
  induction fuel with
  | zero =>
    constructor
    intro s₀ h _ _ _ _
    mvcgen [renameConstsGo_zero]
    all_goals bridge_vcs [Expr.renameConsts]
  | succ fuel ih =>
    constructor
    intro s₀ h hok hm hns hden
    have hrec := ih.run
    mvcgen [renameConstsGo_succ, renameArmFVar, renameArmApp, renameArmLam,
      renameArmForallE, renameArmLet, renameArmProj, hrec]
    all_goals try bridge_vcs [Expr.renameConsts, EStore.ns]
    -- Eleven structural verification conditions remain, in goal order: the
    -- three LEAF views, the inline `const` arm (its postcondition and its
    -- universe-argument `ViewOK` side condition), then the six rebuilding
    -- arms.  `resetMetaGo_spec`'s list with `const` inserted.
    next =>
      bridge_peel
      subst_vars
      exact ⟨hok, hm, Ext.refl _, rfl, rfl, rfl, fun _ _ hi => hi,
        fun _ _ hi => hi, RenameAt.leaf hok.wf (by arm_hyp2) (by grind)⟩
    next =>
      bridge_peel
      subst_vars
      exact ⟨hok, hm, Ext.refl _, rfl, rfl, rfl, fun _ _ hi => hi,
        fun _ _ hi => hi, RenameAt.leaf hok.wf (by arm_hyp2) (by grind)⟩
    next =>
      bridge_peel
      subst_vars
      exact ⟨hok, hm, Ext.refl _, rfl, rfl, rfl, fun _ _ hi => hi,
        fun _ _ hi => hi, RenameAt.leaf hok.wf (by arm_hyp2) (by grind)⟩
    -- `const`: the arm the walk exists for, inline in the dispatcher and so
    -- not memoised (`Arena/ExprOps.lean`'s own note).  This is the one place
    -- `hf` is used.
    next =>
      bridge_peel
      subst_vars
      intro _hwf2 hx hlss _hmem _hcach _hpin hvm hbm hr
      have hns' := ns_of_lss hlss
      refine ⟨by grind only [StateOK, StateOK.mk],
        by grind [MemoOK.mono, Ext.refl], hx, hns', by grind, by grind,
        hvm, hbm, ?_⟩
      exact RenameAt.const_step hok.wf (by arm_hyp2)
        (fun nm hnm => by rw [hns']; exact hf _ _ hnm)
        (fun ls hls => denoteLs_ext hls hx) hr
    next =>
      intro s hs hv
      subst_vars
      obtain ⟨nm, ls, _, _, hl0⟩ := denote_eq_const hok.wf hv hden
      obtain ⟨w, hw, _⟩ := denoteLs_view hl0
      rw [hw]; rfl
    -- `fvar`: the annotation is descended into
    next =>
      bridge_peel
      subst_vars
      have hans := RenameAt.fvar_step hok.wf (by arm_hyp2) (by arm_hyp2) (by arm_hyp2) (by arm_hyp2) (by arm_hyp2)
      have hret := RelE.retarget_self hans (by grind only [Ext.trans]) hden
      exact ⟨by grind only [StateOK, StateOK.mk],
        by grind [MemoOK.mono, MemoOK.insert, Ext.refl],
        by grind only [Ext.trans], by grind [EStore.ns], by grind, by grind,
        by grind, by grind, hans.ext (by grind only [Ext.refl])⟩
    -- `app`
    next =>
      bridge_peel
      subst_vars
      have hans := RenameAt.app_step hok.wf (by arm_hyp2) (by arm_hyp2) (by arm_hyp2) (by arm_hyp2) (by arm_hyp2) (by arm_hyp2) (by arm_hyp2)
      have hret := RelE.retarget_self hans (by grind only [Ext.trans]) hden
      exact ⟨by grind only [StateOK, StateOK.mk],
        by grind [MemoOK.mono, MemoOK.insert, Ext.refl],
        by grind only [Ext.trans], by grind [EStore.ns], by grind, by grind,
        by grind, by grind, hans.ext (by grind only [Ext.refl])⟩
    -- `lam` and `forallE`: the binder datum is carried through unchanged
    next =>
      bridge_peel
      subst_vars
      have hans := RenameAt.lam_step hok.wf (by arm_hyp2) (by arm_hyp2) (by arm_hyp2) (by arm_hyp2) (by arm_hyp2) (by arm_hyp2) (by arm_hyp2)
      have hret := RelE.retarget_self hans (by grind only [Ext.trans]) hden
      exact ⟨by grind only [StateOK, StateOK.mk],
        by grind [MemoOK.mono, MemoOK.insert, Ext.refl],
        by grind only [Ext.trans], by grind [EStore.ns], by grind, by grind,
        by grind, by grind, hans.ext (by grind only [Ext.refl])⟩
    next =>
      bridge_peel
      subst_vars
      have hans := RenameAt.forallE_step hok.wf (by arm_hyp2) (by arm_hyp2) (by arm_hyp2) (by arm_hyp2) (by arm_hyp2) (by arm_hyp2) (by arm_hyp2)
      have hret := RelE.retarget_self hans (by grind only [Ext.trans]) hden
      exact ⟨by grind only [StateOK, StateOK.mk],
        by grind [MemoOK.mono, MemoOK.insert, Ext.refl],
        by grind only [Ext.trans], by grind [EStore.ns], by grind, by grind,
        by grind, by grind, hans.ext (by grind only [Ext.refl])⟩
    -- `letE`
    next =>
      bridge_peel
      subst_vars
      have hans := RenameAt.letE_step hok.wf (by arm_hyp2) (by arm_hyp2) (by arm_hyp2) (by arm_hyp2) (by arm_hyp2) (by arm_hyp2) (by arm_hyp2) (by arm_hyp2) (by arm_hyp2)
      have hret := RelE.retarget_self hans (by grind only [Ext.trans]) hden
      exact ⟨by grind only [StateOK, StateOK.mk],
        by grind [MemoOK.mono, MemoOK.insert, Ext.refl],
        by grind only [Ext.trans], by grind [EStore.ns], by grind, by grind,
        by grind, by grind, hans.ext (by grind only [Ext.refl])⟩
    -- `proj`
    next =>
      bridge_peel
      subst_vars
      obtain ⟨nm, es, _, hn0, _⟩ := denote_eq_proj hok.wf (by arm_hyp2) hden
      have hans := RenameAt.proj_step hok.wf (by arm_hyp2) (by arm_hyp2)
        (by arm_hyp2) (by arm_hyp2) (by arm_hyp2) hn0
      have hret := RelE.retarget_self hans (by grind only [Ext.trans]) hden
      exact ⟨by grind only [StateOK, StateOK.mk],
        by grind [MemoOK.mono, MemoOK.insert, Ext.refl],
        by grind only [Ext.trans], by grind [EStore.ns], by grind, by grind,
        by grind, by grind, hans.ext (by grind only [Ext.refl])⟩

/-- con-leche: ConLeche/Kernel/ExprOps.lean:999-1036 renameConstsGo — the
same at one state, which is the form the entry consumes.  Its step lemmas are
`Reset.lean`'s `RenameAt.*`, `RenameAt.const_step` included. -/
theorem renameConstsGo_spec (f : NIdx → NIdx) (fn : ConLeche.Name → ConLeche.Name)
    (fuel : Nat) (s₀ : AState) (c : EIdx) (hok : StateOK s₀)
    (hm : RenameMemoA fn s₀)
    (hf : ∀ (n : NIdx) (x : ConLeche.Name), denoteN s₀.store.ns n = some x →
      denoteN s₀.store.ns (f n) = some (fn x))
    (hden : (denoteE s₀.store c).isSome = true) :
    ⦃fun s => ⌜s = s₀⌝⦄ renameConstsGo f fuel c
    ⦃⇓? r s' => ⌜StateOK s' ∧ RenameMemoA fn s' ∧ Ext s₀.store s'.store ∧
        s'.caches = s₀.caches ∧ s'.pins = s₀.pins ∧
        RelE (Expr.renameConsts fn) s₀.store c s'.store r⌝⦄ := by
  have hr := (renameConstsGo_specS f fn s₀.store.ns hf fuel).run
  mvcgen [hr]
  all_goals bridge_vcs [Expr.renameConsts]

/-- con-leche: ConLeche/Kernel/ExprOps.lean:1112-1114 renameConstsFast — the
bracket over `renameConstsGo_spec`, in `ExprOps/Inst1.lean`'s
`instantiate1Fast_spec` shape. -/
theorem renameConstsFast_spec (fuel : Nat) (f : NIdx → NIdx)
    (fn : ConLeche.Name → ConLeche.Name) (s₀ : AState) (e : EIdx)
    (hok : StateOK s₀)
    (hf : ∀ (n : NIdx) (x : ConLeche.Name), denoteN s₀.store.ns n = some x →
      denoteN s₀.store.ns (f n) = some (fn x))
    (hden : (denoteE s₀.store e).isSome = true) :
    ⦃fun s => ⌜s = s₀⌝⦄ renameConstsFast fuel f e
    ⦃⇓? r s' => ⌜StateOK s' ∧ Ext s₀.store s'.store ∧
        s'.caches = s₀.caches ∧ s'.pins = s₀.pins ∧ s'.memos.renameC = ∅ ∧
        RelE (Expr.renameConsts fn) s₀.store e s'.store r⌝⦄ := by
  have hr := renameConstsGo_spec f fn fuel
  mvcgen [renameConstsFast, hr]
  all_goals bridge_vcs [Expr.renameConsts]

/-! ## `instantiateLevelParams`

DESIGN §8.3 lesson 4: the level ALGORITHM runs on transient trees, so `ks`
and `us` are `List Name` and `List Level` in the walk and handles only at the
entry, which reads them back with `readNames` / `readLevels`.  The cutoff is
the `hasLP` bit and its licence is con-leche's
`Expr.instantiateLevelParams_eq_self` (`ExprOps.lean:2465`). -/

/-! ### The answer relation, the cutoff's licence and the step lemmas -/

/-- con-leche: ConLeche/Verify/SimI.lean:250 RelE — `instantiateLevelParams`'
answer relation. -/
abbrev InstLPAt (ks : List ConLeche.Name) (us : List Level) :
    EStore → EIdx → EStore → EIdx → Prop :=
  RelE (fun x => x.instantiateLevelParams ks us)

/-- con-leche: none — arena infrastructure: `EStore.view` reads `pers`, `scr`
and `scratchOn` and nothing else, so a step that frames those three frames
every view.  This is what carries a rebuilding arm's `internRebuilt` cutoff
across `substLMemoAt` / `substLsMemoAt`, which move only the LEVEL store. -/
theorem view_eq_of_tables {st st' : EStore} (hp : st'.pers = st.pers)
    (hs : st'.scr = st.scr) (ho : st'.scratchOn = st.scratchOn) (i : EIdx) :
    st'.view i = st.view i := by
  simp only [EStore.view, EStore.viewBind, EStore.viewBindI, EStore.viewBM,
    EStore.persGetBind, EStore.persGetBM, hp, hs, ho]

/-- con-leche: ConLeche/Kernel/ExprOps.lean:2465
Expr.instantiateLevelParams_eq_self — **the `hasLP` cutoff's licence**, at the
packed bit the arena reads: a subtree with no level parameter is its own
instantiation.  `EStore.derived_exact` says the word is `e.data` and
`Expr.hasLP_eq` (con-leche `ExprOps.lean:2541`) says `lpOfData e.data` is
`e.hasLevelParam`. -/
theorem InstLPAt.cutoff {ks : List ConLeche.Name} {us : List Level}
    {st : EStore} (hwf : StoreWF st) {h : EIdx}
    (hlp : lpOfData (st.derived h) = false) : InstLPAt ks us st h st h := by
  intro e he
  have h1 : lpOfData (st.derived h) = e.hasLevelParam := by
    rw [EStore.derived_exact hwf he]; exact Expr.Expr.hasLP_eq e
  show denoteE st h = some (e.instantiateLevelParams ks us)
  rw [Expr.instantiateLevelParams_eq_self (by rw [← h1]; exact hlp)]
  exact he

/-- con-leche: ConLeche/Kernel/Level.lean:234-249 Expr.instantiateLevelParams —
the two leaf constructors that are fixed points (`sort` and `const` are the
two the walk exists for, and `fvar` is descended into). -/
theorem instantiateLevelParams_leaf {ks : List ConLeche.Name}
    {us : List Level} {e : Expr}
    (h : (∃ i, e = .bvar i) ∨ ∃ l, e = .lit l) :
    e.instantiateLevelParams ks us = e := by
  rcases h with ⟨i, rfl⟩ | ⟨l, rfl⟩ <;> simp [Expr.instantiateLevelParams]

/-- con-leche: ConLeche/Kernel/Level.lean:234-249 Expr.instantiateLevelParams —
the LEAF arms. -/
theorem InstLPAt.leaf {ks : List ConLeche.Name} {us : List Level}
    {st : EStore} {h : EIdx} {v : ENodeView} (hwf : StoreWF st)
    (hview : st.view h = some v)
    (hv : (∃ i, v = .bvar i) ∨ ∃ l, v = .lit l) : InstLPAt ks us st h st h := by
  intro e he
  show denoteE st h = some (e.instantiateLevelParams ks us)
  have hleaf : (∃ i, e = .bvar i) ∨ ∃ l, e = .lit l := by
    rcases hv with ⟨i, rfl⟩ | ⟨l, rfl⟩
    · exact Or.inl ⟨i, denote_bvar_inv hwf hview he⟩
    · exact Or.inr ⟨l, denote_lit_inv hwf hview he⟩
  rw [instantiateLevelParams_leaf hleaf]
  exact he

/-- con-leche: ConLeche/Kernel/Level.lean:237 Expr.instantiateLevelParams — the
`sort` arm, the one place an expression walk calls a LEVEL algorithm. -/
theorem InstLPAt.sort_step {ks : List ConLeche.Name} {us : List Level}
    {st st' : EStore} {h r : EIdx} {u ru : LIdx} (hwf : StoreWF st)
    (hview : st.view h = some (.sort u))
    (hu : RelL (Level.subst ks us) st u st' ru)
    (hr : denoteE st' r = denoteEView st' (.sort ru)) :
    InstLPAt ks us st h st' r :=
  RelE.sort hwf hview (fun _ => rfl) hu hr

/-- con-leche: ConLeche/Kernel/Level.lean:238 Expr.instantiateLevelParams — the
`const` arm: the NAME is carried, the universe arguments are substituted. -/
theorem InstLPAt.const_step {ks : List ConLeche.Name} {us : List Level}
    {st st' : EStore} {h r : EIdx} {n : NIdx} {vs rvs : LsIdx}
    {nm : ConLeche.Name} (hwf : StoreWF st)
    (hview : st.view h = some (.const n vs))
    (hn0 : denoteN st.ns n = some nm) (hx : Ext st st')
    (hvs : RelLs (fun ws => ws.map (Level.subst ks us)) st vs st' rvs)
    (hr : denoteE st' r = denoteEView st' (.const n rvs)) :
    InstLPAt ks us st h st' r :=
  RelE.const hwf hview (fun _ => rfl) hn0 (denoteN_ext hn0 hx) hvs hr

/-- con-leche: ConLeche/Kernel/Level.lean:236 Expr.instantiateLevelParams — the
`fvar` arm; the type ANNOTATION is descended into. -/
theorem InstLPAt.fvar_step {ks : List ConLeche.Name} {us : List Level}
    {st s1 s2 : EStore} {h ty rt r : EIdx} {idx : Nat} (hwf : StoreWF st)
    (hview : st.view h = some (.fvar idx ty))
    (_hx1 : Ext st s1) (ht : InstLPAt ks us st ty s1 rt) (hx2 : Ext s1 s2)
    (hr : denoteE s2 r = denoteEView s2 (.fvar idx rt)) :
    InstLPAt ks us st h s2 r :=
  RelE.fvar hwf hview (fun _ => rfl) (ht.ext hx2) hr

/-- con-leche: ConLeche/Kernel/Level.lean:239 Expr.instantiateLevelParams — the
`app` arm. -/
theorem InstLPAt.app_step {ks : List ConLeche.Name} {us : List Level}
    {st s1 s2 s3 : EStore} {h f a rf ra r : EIdx} (hwf : StoreWF st)
    (hview : st.view h = some (.app f a))
    (hx1 : Ext st s1) (hf : InstLPAt ks us st f s1 rf)
    (hx2 : Ext s1 s2) (ha : InstLPAt ks us s1 a s2 ra)
    (hx3 : Ext s2 s3)
    (hr : denoteE s3 r = denoteEView s3 (.app rf ra)) :
    InstLPAt ks us st h s3 r :=
  RelE.app hwf hview (fun _ _ => rfl) ((hf.ext hx2).ext hx3)
    ((ha.of_ext hx1).ext hx3) hr

/-- con-leche: ConLeche/Kernel/Level.lean:240-242 Expr.instantiateLevelParams —
the `lam` arm, whose binder prop-ness DATUM is substituted too (con-leche's
task #161, and the arena's `m2`). -/
theorem InstLPAt.lam_step {ks : List ConLeche.Name} {us : List Level}
    {st s1 s2 s3 : EStore} {h ty b rt rb r : EIdx} {m : BinderMeta}
    (hwf : StoreWF st) (hview : st.view h = some (.lam ty b m))
    (hx1 : Ext st s1) (ht : InstLPAt ks us st ty s1 rt)
    (hx2 : Ext s1 s2) (hb : InstLPAt ks us s1 b s2 rb)
    (hx3 : Ext s2 s3)
    (hr : denoteE s3 r =
      denoteEView s3 (.lam rt rb ⟨Level.substPW ks us m.pw⟩)) :
    InstLPAt ks us st h s3 r :=
  RelE.lam hwf hview (fun _ _ => rfl) ((ht.ext hx2).ext hx3)
    ((hb.of_ext hx1).ext hx3) hr

/-- con-leche: ConLeche/Kernel/Level.lean:243-245 Expr.instantiateLevelParams —
and the `forallE` arm. -/
theorem InstLPAt.forallE_step {ks : List ConLeche.Name} {us : List Level}
    {st s1 s2 s3 : EStore} {h ty b rt rb r : EIdx} {m : BinderMeta}
    (hwf : StoreWF st) (hview : st.view h = some (.forallE ty b m))
    (hx1 : Ext st s1) (ht : InstLPAt ks us st ty s1 rt)
    (hx2 : Ext s1 s2) (hb : InstLPAt ks us s1 b s2 rb)
    (hx3 : Ext s2 s3)
    (hr : denoteE s3 r =
      denoteEView s3 (.forallE rt rb ⟨Level.substPW ks us m.pw⟩)) :
    InstLPAt ks us st h s3 r :=
  RelE.forallE hwf hview (fun _ _ => rfl) ((ht.ext hx2).ext hx3)
    ((hb.of_ext hx1).ext hx3) hr

/-- con-leche: ConLeche/Kernel/Level.lean:246-247
Expr.instantiateLevelParams — the `letE` arm. -/
theorem InstLPAt.letE_step {ks : List ConLeche.Name} {us : List Level}
    {st s1 s2 s3 s4 : EStore} {h ty w b rt rw rb r : EIdx}
    (hwf : StoreWF st) (hview : st.view h = some (.letE ty w b))
    (hx1 : Ext st s1) (ht : InstLPAt ks us st ty s1 rt)
    (hx2 : Ext s1 s2) (hw : InstLPAt ks us s1 w s2 rw)
    (hx3 : Ext s2 s3) (hb : InstLPAt ks us s2 b s3 rb)
    (hx4 : Ext s3 s4)
    (hr : denoteE s4 r = denoteEView s4 (.letE rt rw rb)) :
    InstLPAt ks us st h s4 r :=
  RelE.letE hwf hview (fun _ _ _ => rfl) (((ht.ext hx2).ext hx3).ext hx4)
    (((hw.of_ext hx1).ext hx3).ext hx4) ((hb.of_ext (hx1.trans hx2)).ext hx4) hr

/-- con-leche: ConLeche/Kernel/Level.lean:249 Expr.instantiateLevelParams — the
`proj` arm. -/
theorem InstLPAt.proj_step {ks : List ConLeche.Name} {us : List Level}
    {st s1 s2 : EStore} {h sub rs r : EIdx} {n : NIdx} {i : Nat}
    {nm : ConLeche.Name} (hwf : StoreWF st)
    (hview : st.view h = some (.proj n i sub))
    (hx1 : Ext st s1) (hs : InstLPAt ks us st sub s1 rs) (hx2 : Ext s1 s2)
    (hr : denoteE s2 r = denoteEView s2 (.proj n i rs))
    (hn0 : denoteN st.ns n = some nm) : InstLPAt ks us st h s2 r :=
  RelE.proj hwf hview (fun _ => rfl) (hs.ext hx2) hn0
    (denoteN_ext (denoteN_ext hn0 hx1) hx2) hr

/-- con-leche: ConLeche/Verify/SimI.lean:244 SimAt — Theorem 1's statement for
one level of `instLPGo`'s recursion.

**The frame is NOT `s'.caches = s₁.caches`** (`ExprOps/InstLP.lean`'s header
says why): the `sort` and `const` arms read a level back, and the memoised
readback WRITES `caches.readLC` / `caches.readLsC`.  What the walk preserves
instead — and what its own recursive calls need — is the two readback
CLAUSES, so those are hypotheses and conjuncts both. -/
structure InstLPSpec (ks : List ConLeche.Name) (us : List Level)
    (rec : EIdx → AM EIdx) : Prop where
  run : ∀ (s₁ : AState) (h : EIdx), StateOK s₁ → InstLPMemoA ks us s₁ →
    InstLPLMemoA ks us s₁ → InstLPLsMemoA ks us s₁ →
    ReadLCacheOK s₁.caches.readLC s₁.store →
    ReadLsCacheOK s₁.caches.readLsC s₁.store →
    (denoteE s₁.store h).isSome = true →
    ⦃fun s => ⌜s = s₁⌝⦄ rec h
    ⦃⇓? r s' => ⌜StateOK s' ∧ InstLPMemoA ks us s' ∧ InstLPLMemoA ks us s' ∧
        InstLPLsMemoA ks us s' ∧ Ext s₁.store s'.store ∧
        ReadLCacheOK s'.caches.readLC s'.store ∧
        ReadLsCacheOK s'.caches.readLsC s'.store ∧
        s'.pins = s₁.pins ∧
        (∀ i v, s₁.store.view i = some v → s'.store.view i = some v) ∧
        InstLPAt ks us s₁.store h s'.store r⌝⦄

/-- con-leche: ConLeche/Kernel/ExprOps.lean:2566-2605 Expr.instLPGo —
**THEOREM 1 for `instantiateLevelParams`**, at one level of the recursion, by
induction on the fuel.  `resetMetaGo_spec`'s shape with the `hasLP` cutoff in
front and the two LEVEL arms `ExprOps/InstLP.lean` closes. -/
theorem instLPGo_specS (ks : List ConLeche.Name) (us : List Level) :
    ∀ fuel, InstLPSpec ks us (instLPGo ks us fuel) := by
  intro fuel
  induction fuel with
  | zero =>
    constructor
    intro s₀ h _ _ _ _ _ _ _
    mvcgen [instLPGo_zero]
    all_goals bridge_vcs [Expr.instantiateLevelParams]
  | succ fuel ih =>
    constructor
    intro s₀ h hok hm hml hmls hcl hcls hden
    have hrec := ih.run
    mvcgen [instLPGo_succ, instLPArmFVar, instLPArmApp, instLPArmLam,
      instLPArmForallE, instLPArmLet, instLPArmProj, hrec,
      substLMemoAt_spec, substLsMemoAt_spec]
    all_goals try bridge_vcs [Expr.instantiateLevelParams, ReadLCacheOK.mono,
      ReadLsCacheOK.mono, view_eq_of_tables]
    -- Fourteen structural verification conditions remain, in goal order: the
    -- `hasLP` cutoff, the two LEAF views, the `sort` arm (postcondition and
    -- `internRebuilt` cutoff), the `const` arm (postcondition, its
    -- universe-argument `ViewOK` and its `internRebuilt` cutoff), then the
    -- six rebuilding arms.  `resetMetaGo_spec`'s list with the cutoff and the
    -- two LEVEL arms added.
    -- the `hasLP` cutoff
    next =>
      bridge_peel
      subst_vars
      exact ⟨hok, hm, hml, hmls, Ext.refl _, hcl, hcls, rfl, fun _ _ hi => hi,
        InstLPAt.cutoff hok.wf (by grind)⟩
    -- `bvar`, `lit`
    next =>
      bridge_peel
      subst_vars
      exact ⟨hok, hm, hml, hmls, Ext.refl _, hcl, hcls, rfl, fun _ _ hi => hi,
        InstLPAt.leaf hok.wf (by lp_hyp) (by grind)⟩
    next =>
      bridge_peel
      subst_vars
      exact ⟨hok, hm, hml, hmls, Ext.refl _, hcl, hcls, rfl, fun _ _ hi => hi,
        InstLPAt.leaf hok.wf (by lp_hyp) (by grind)⟩
    -- `sort`: the LEVEL arm, `ExprOps/InstLP.lean`'s `substLMemoAt_spec`
    next =>
      bridge_peel
      subst_vars
      intro _hwf2 hx _hlss _hmem _hcach _hpin _hvm _hbm hr
      refine ⟨by grind only [StateOK, StateOK.mk], by grind [MemoOK.mono],
        by grind [MemoLOK.mono], by grind [MemoLsOK.mono],
        by grind only [Ext.trans], by grind [ReadLCacheOK.mono],
        by grind [ReadLsCacheOK.mono], by grind, by grind [view_eq_of_tables],
        ?_⟩
      exact InstLPAt.sort_step hok.wf (by lp_hyp)
        (RelL.ext (by lp_hyp) hx) hr
    -- `const`: the universe-argument LIST arm
    next =>
      bridge_peel
      subst_vars
      obtain ⟨nm, ls, _, hn0, hl0⟩ := denote_eq_const hok.wf (by lp_hyp) hden
      intro _hwf2 hx _hlss _hmem _hcach _hpin _hvm _hbm hr
      refine ⟨by grind only [StateOK, StateOK.mk], by grind [MemoOK.mono],
        by grind [MemoLOK.mono], by grind [MemoLsOK.mono],
        by grind only [Ext.trans], by grind [ReadLCacheOK.mono],
        by grind [ReadLsCacheOK.mono], by grind, by grind [view_eq_of_tables],
        ?_⟩
      exact InstLPAt.const_step hok.wf (by lp_hyp) hn0
        (by grind only [Ext.trans]) (RelLs.ext (by lp_hyp) hx) hr
    -- `const`'s `ViewOK` at the substituted universe-argument list
    next =>
      bridge_peel
      subst_vars
      obtain ⟨nm, ls, _, hn0, hl0⟩ := denote_eq_const hok.wf (by lp_hyp) hden
      intro s _hok2 _hx _hp _hsc _ho _ _ _ _ _ _ hrls
      obtain ⟨w, hw, _⟩ := denoteLs_view (hrls ls hl0)
      rw [hw]; rfl
    -- `fvar`: the annotation is descended into
    next =>
      bridge_peel
      subst_vars
      have hans := InstLPAt.fvar_step hok.wf (by lp_hyp) (by lp_hyp) (by lp_hyp) (by lp_hyp) (by lp_hyp)
      have hret := RelE.retarget_self hans (by grind only [Ext.trans]) hden
      exact ⟨by grind only [StateOK, StateOK.mk],
        by grind [MemoOK.mono, MemoOK.insert, Ext.refl],
        by grind [MemoLOK.mono], by grind [MemoLsOK.mono],
        by grind only [Ext.trans], by grind [ReadLCacheOK.mono],
        by grind [ReadLsCacheOK.mono], by grind, by grind,
        hans.ext (by grind only [Ext.refl])⟩
    -- `app`
    next =>
      bridge_peel
      subst_vars
      have hans := InstLPAt.app_step hok.wf (by lp_hyp) (by lp_hyp) (by lp_hyp) (by lp_hyp) (by lp_hyp) (by lp_hyp) (by lp_hyp)
      have hret := RelE.retarget_self hans (by grind only [Ext.trans]) hden
      exact ⟨by grind only [StateOK, StateOK.mk],
        by grind [MemoOK.mono, MemoOK.insert, Ext.refl],
        by grind [MemoLOK.mono], by grind [MemoLsOK.mono],
        by grind only [Ext.trans], by grind [ReadLCacheOK.mono],
        by grind [ReadLsCacheOK.mono], by grind, by grind,
        hans.ext (by grind only [Ext.refl])⟩
    -- `lam` and `forallE`: the binder DATUM is substituted too
    next =>
      bridge_peel
      subst_vars
      have hans := InstLPAt.lam_step hok.wf (by lp_hyp) (by lp_hyp) (by lp_hyp) (by lp_hyp) (by lp_hyp) (by lp_hyp) (by lp_hyp)
      have hret := RelE.retarget_self hans (by grind only [Ext.trans]) hden
      exact ⟨by grind only [StateOK, StateOK.mk],
        by grind [MemoOK.mono, MemoOK.insert, Ext.refl],
        by grind [MemoLOK.mono], by grind [MemoLsOK.mono],
        by grind only [Ext.trans], by grind [ReadLCacheOK.mono],
        by grind [ReadLsCacheOK.mono], by grind, by grind,
        hans.ext (by grind only [Ext.refl])⟩
    next =>
      bridge_peel
      subst_vars
      have hans := InstLPAt.forallE_step hok.wf (by lp_hyp) (by lp_hyp) (by lp_hyp) (by lp_hyp) (by lp_hyp) (by lp_hyp) (by lp_hyp)
      have hret := RelE.retarget_self hans (by grind only [Ext.trans]) hden
      exact ⟨by grind only [StateOK, StateOK.mk],
        by grind [MemoOK.mono, MemoOK.insert, Ext.refl],
        by grind [MemoLOK.mono], by grind [MemoLsOK.mono],
        by grind only [Ext.trans], by grind [ReadLCacheOK.mono],
        by grind [ReadLsCacheOK.mono], by grind, by grind,
        hans.ext (by grind only [Ext.refl])⟩
    -- `letE`
    next =>
      bridge_peel
      subst_vars
      have hans := InstLPAt.letE_step hok.wf (by lp_hyp) (by lp_hyp) (by lp_hyp) (by lp_hyp) (by lp_hyp) (by lp_hyp) (by lp_hyp) (by lp_hyp) (by lp_hyp)
      have hret := RelE.retarget_self hans (by grind only [Ext.trans]) hden
      exact ⟨by grind only [StateOK, StateOK.mk],
        by grind [MemoOK.mono, MemoOK.insert, Ext.refl],
        by grind [MemoLOK.mono], by grind [MemoLsOK.mono],
        by grind only [Ext.trans], by grind [ReadLCacheOK.mono],
        by grind [ReadLsCacheOK.mono], by grind, by grind,
        hans.ext (by grind only [Ext.refl])⟩
    -- `proj`
    next =>
      bridge_peel
      subst_vars
      obtain ⟨nm, es, _, hn0, _⟩ := denote_eq_proj hok.wf (by lp_hyp) hden
      have hans := InstLPAt.proj_step hok.wf (by lp_hyp) (by lp_hyp)
        (by lp_hyp) (by lp_hyp) (by lp_hyp) hn0
      have hret := RelE.retarget_self hans (by grind only [Ext.trans]) hden
      exact ⟨by grind only [StateOK, StateOK.mk],
        by grind [MemoOK.mono, MemoOK.insert, Ext.refl],
        by grind [MemoLOK.mono], by grind [MemoLsOK.mono],
        by grind only [Ext.trans], by grind [ReadLCacheOK.mono],
        by grind [ReadLsCacheOK.mono], by grind, by grind,
        hans.ext (by grind only [Ext.refl])⟩

/-- con-leche: ConLeche/Kernel/ExprOps.lean:2566-2605 Expr.instLPGo — the walk
at one state, which is the form the entry consumes. -/
theorem instLPGo_spec (ks : List ConLeche.Name) (us : List Level) (fuel : Nat)
    (s₀ : AState) (c : EIdx) (hok : StateOK s₀) (hm : InstLPMemoA ks us s₀)
    (hml : InstLPLMemoA ks us s₀) (hmls : InstLPLsMemoA ks us s₀)
    (hcl : ReadLCacheOK s₀.caches.readLC s₀.store)
    (hcls : ReadLsCacheOK s₀.caches.readLsC s₀.store)
    (hden : (denoteE s₀.store c).isSome = true) :
    ⦃fun s => ⌜s = s₀⌝⦄ instLPGo ks us fuel c
    ⦃⇓? r s' => ⌜StateOK s' ∧ InstLPMemoA ks us s' ∧ Ext s₀.store s'.store ∧
        ReadLCacheOK s'.caches.readLC s'.store ∧
        ReadLsCacheOK s'.caches.readLsC s'.store ∧
        s'.pins = s₀.pins ∧
        RelE (fun x => x.instantiateLevelParams ks us) s₀.store c
          s'.store r⌝⦄ := by
  have hr := (instLPGo_specS ks us fuel).run
  mvcgen [hr]
  all_goals bridge_vcs [Expr.instantiateLevelParams]

/-! ### The NAME readback with the sibling readback tables framed

`ExprOps/MemoSpecs.lean` did this for `readLevelM` / `readLevelsM`
(`readLevelM_specF`, `readLevelsM_specF`) and gives the reason: a walk that
reads more than one kind of handle back must carry the OTHER kind's cache
clause across.  `instLPFast` reads NAMES back and then LEVELS, so it needs
the third face of the same lemma, and `Bridge/SpecsL.lean`'s
`readNamesM_spec` does not frame `caches.readLC` / `caches.readLsC`.  These
two belong in `Bridge/SpecsL.lean` beside the specs they strengthen. -/

/-- con-leche: ConLeche/Kernel/Name.lean:34-37 Name — `readNameM` with the
sibling readback tables framed. -/
@[spec high] theorem readNameM_specF (s₀ : AState) (h : NIdx)
    (hc : ReadNCacheOK s₀.caches.readNC s₀.store) :
    ⦃fun s => ⌜s = s₀⌝⦄ readNameM h
    ⦃⇓? x s' => ⌜s'.store = s₀.store ∧ s'.memos = s₀.memos ∧
        s'.pins = s₀.pins ∧
        s'.caches.readLC = s₀.caches.readLC ∧
        s'.caches.readLsC = s₀.caches.readLsC ∧
        denoteN s₀.store.ns h = some x ∧
        ReadNCacheOK s'.caches.readNC s'.store⌝⦄ := by
  unfold readNameM
  mvcgen
  all_goals (bridge_peel; subst_vars) <;>
    first
    | (refine ⟨rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩ <;> grind [ReadNCacheOK])
    | (intro hf; exact False.elim hf)
    | grind [ReadNCacheOK]

/-- con-leche: ConLeche/Kernel/Name.lean:34-37 Name — and `readNamesM`, whose
recursion is on the list as `readNames`' is. -/
@[spec high] theorem readNamesM_specF (s₀ : AState) (hs : List NIdx)
    (hc : ReadNCacheOK s₀.caches.readNC s₀.store) :
    ⦃fun s => ⌜s = s₀⌝⦄ readNamesM hs
    ⦃⇓? xs s' => ⌜s'.store = s₀.store ∧ s'.memos = s₀.memos ∧
        s'.pins = s₀.pins ∧
        s'.caches.readLC = s₀.caches.readLC ∧
        s'.caches.readLsC = s₀.caches.readLsC ∧
        Frontend.denoteNList s₀.store.ns hs = some xs ∧
        ReadNCacheOK s'.caches.readNC s'.store⌝⦄ := by
  induction hs generalizing s₀ with
  | nil =>
    unfold readNamesM
    mvcgen
    all_goals (bridge_peel; subst_vars
               grind [Frontend.denoteNList, ReadNCacheOK])
  | cons a as ih =>
    -- **The tail is generalised to a VARIABLE first.**  `mvcgen` prefers a
    -- database spec to the structural induction hypothesis, and
    -- `Bridge/SpecsL.lean`'s `readNamesM_spec` matches `readNamesM as`
    -- exactly — so with the recursive call left in place the tail's two
    -- cache equations are simply not in the context (measured).  `[-spec]`
    -- is refused by the attribute and `spec low` does not displace it; a
    -- program VARIABLE matches no database spec at all, which is the lever.
    have key : ∀ p : AM (List ConLeche.Name),
        (∀ s₁ : AState, ReadNCacheOK s₁.caches.readNC s₁.store →
          ⦃fun s => ⌜s = s₁⌝⦄ p
          ⦃⇓? xs s' => ⌜s'.store = s₁.store ∧ s'.memos = s₁.memos ∧
              s'.pins = s₁.pins ∧
              s'.caches.readLC = s₁.caches.readLC ∧
              s'.caches.readLsC = s₁.caches.readLsC ∧
              Frontend.denoteNList s₁.store.ns as = some xs ∧
              ReadNCacheOK s'.caches.readNC s'.store⌝⦄) →
        ⦃fun s => ⌜s = s₀⌝⦄
          (do let x ← readNameM a; let xs ← p; pure (x :: xs))
        ⦃⇓? xs s' => ⌜s'.store = s₀.store ∧ s'.memos = s₀.memos ∧
            s'.pins = s₀.pins ∧
            s'.caches.readLC = s₀.caches.readLC ∧
            s'.caches.readLsC = s₀.caches.readLsC ∧
            Frontend.denoteNList s₀.store.ns (a :: as) = some xs ∧
            ReadNCacheOK s'.caches.readNC s'.store⌝⦄ := by
      intro p hp
      mvcgen [readNameM_specF, hp]
      all_goals (bridge_peel; subst_vars
                 grind [Frontend.denoteNList, ReadNCacheOK])
    exact key (readNamesM as) ih

/-- con-leche: ConLeche/Kernel/ExprOps.lean:2718-2722 Expr.instLPFast — the
entry, which reads `ks` and `us` back ONCE (`readNamesM` / `readLevelsM`) and
then runs `instLPGo` on the transient trees.

**Two statement changes this round had to make** (the shape the round owed
was not provable):

* the frame is NOT `s'.caches = s₀.caches` — the readbacks and the walk's two
  level arms WRITE the readback caches (`ExprOps/InstLP.lean`'s header).  The
  two readback CLAUSES are carried instead, as hypotheses and conjuncts both;
  the THIRD (`ReadNCacheOK`, which `readNamesM` needs) is a hypothesis and
  cannot be a conjunct, because `ExprOps/InstLP.lean`'s `substLMemoAt_spec`
  does not frame `caches.readNC` — a one-conjunct change there would give it
  back;
* the memo clause is a DISJUNCTION, exactly as `abstractRangeFast_spec`'s is
  and for the same reason: the `hasLP` cutoff is HOISTED over the readbacks
  (task #97-P6-10), so on a level-parameter-free subject the entry returns
  without clearing anything. -/
theorem instLPFast_spec (fuel : Nat) (s₀ : AState) (ks : List NIdx)
    (us : LsIdx) (e : EIdx) (ksv : List ConLeche.Name) (usv : List Level)
    (hok : StateOK s₀)
    (hcn : ReadNCacheOK s₀.caches.readNC s₀.store)
    (hcl : ReadLCacheOK s₀.caches.readLC s₀.store)
    (hcls : ReadLsCacheOK s₀.caches.readLsC s₀.store)
    (hks : Frontend.denoteNList s₀.store.ns ks = some ksv)
    (hus : denoteLs s₀.store.lss us = some usv)
    (hden : (denoteE s₀.store e).isSome = true) :
    ⦃fun s => ⌜s = s₀⌝⦄ instLPFast fuel ks us e
    ⦃⇓? r s' => ⌜StateOK s' ∧ Ext s₀.store s'.store ∧
        ReadLCacheOK s'.caches.readLC s'.store ∧
        ReadLsCacheOK s'.caches.readLsC s'.store ∧
        s'.pins = s₀.pins ∧
        (s'.memos.instLPC = ∅ ∨ s' = s₀) ∧
        RelE (fun x => x.instantiateLevelParams ksv usv) s₀.store e
          s'.store r⌝⦄ := by
  have hr := fun (kk : List ConLeche.Name) (uu : List Level) (s₁ : AState)
      (c : EIdx) => instLPGo_spec kk uu fuel s₁ c
  mvcgen [instLPFast, hr]
  all_goals try bridge_vcs [Expr.instantiateLevelParams]
  -- The HOISTED `hasLP` cutoff (task #97-P6-10), which returns the subject
  -- without reading `ks`/`us` back and without clearing the memo.
  next =>
    bridge_peel
    subst_vars
    exact ⟨hok, Ext.refl _, hcl, hcls, rfl, Or.inr rfl,
      InstLPAt.cutoff hok.wf (by grind)⟩

/-! ## The axiom check -/

#print axioms abstract1Fast_spec
#print axioms abstractRangeGo_spec
#print axioms abstractRangeFast_spec
#print axioms resetMetaFast_spec
#print axioms renameConstsGo_spec
#print axioms renameConstsFast_spec
#print axioms instLPGo_spec
#print axioms instLPFast_spec

end ConRon.Bridge.ExprOps
