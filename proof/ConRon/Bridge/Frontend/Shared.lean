/-
# `ConRon.Bridge.Frontend.Shared` — the memoised readback IS the denotation,
and its inverse

`Arena/Frontend/Readback.lean`'s module note states the obligation this module
discharges, in its own words:

> `denoteEShared st h = denoteE st h` is the exactness obligation this owes
> P3; the two differ only in how many times the tree is built.

The reason the two functions exist at all is measured, not stylistic:
`Arena/Denote.lean`'s `denoteE` recurses at each child independently, so on a
DAG whose expression table doubles at every second entry (con-leche's own
`tests/e2e/tower_struct.ndjson`) it unfolds the sharing and does not finish.
`denoteEGo` threads a `Std.HashMap EIdx Expr` and rebuilds each node once.
**The value is the same and the sharing is the same; only the work differs.**

## What the equation costs

The memo makes the induction a two-parameter one — the fuel AND the memo's
own invariant — and the invariant is exactly the shape task #97-P3-0 §6
records for `fvarLeavesGo_spec`:

    DMemoOK st m  :  ∀ h e, m[h]? = some e → denoteE st h = some e

with the difference that `denoteEGo`'s memo is WHITE (a node is inserted after
its children are built), so there is no gray phase and no second induction on
`StoreWF`'s rank.  That is why this one is a straight fuel induction where
`fvarLeavesGo_spec`'s is not.

## The other direction

`internExpr` is the readback's inverse; the frontend needs it for the pin
variants (`Bridge/Checker/Pins.lean`'s item 13) — the in-process modeller
(`Arena/Frontend/InModel.lean`) and the projection rewrite's two recognisers
that used to need it too are gone (task #105).  Its exactness is the mirror
statement, `denoteE st' (internExpr e) = some e`, with `Ext` and `StoreWF`
threaded: it is `Bridge/Specs.lean`'s `internE_spec` composed along a
`ConLeche.Expr`'s own structural recursion, with the `EMemo` invariant in the
same shape.

**Task #105 deletion**: the tail section relating `BlockRec`/`Ctx`
(`denoteM{Type,Ctor,Rec}Go_of_rel`, `denoteBlockRec_eq_of_rel`,
`nameHandle?_sound`, `find?_isSome_of_view`, `nameHandle?_isSome`,
`ctxOf_eq_of_rel`, eleven lemmas) served only the modeller seam's context
readback and is gone with it.
-/
import ConRon.Bridge.Frontend.Rel
import ConRon.Bridge.SpecsL
import ConRon.Arena.Frontend.Readback

namespace ConRon.Bridge.Frontend

set_option autoImplicit false

open ConLeche ConRon.Arena ConRon.Arena.Frontend

/-! ## The readback's memo -/

/-! ## The intern direction -/

/-- con-leche: none — the intern memo's invariant: every recorded handle
denotes its key. -/
def EMemoOK (st : EStore) (m : EMemo) : Prop :=
  ∀ e h, m[e]? = some h → denoteE st h = some e

theorem EMemoOK.empty (st : EStore) : EMemoOK st (∅ : EMemo) := by
  intro e h hm; simp at hm

theorem EMemoOK.mono {st st' : EStore} {m : EMemo} (h : EMemoOK st m)
    (hx : Ext st st') : EMemoOK st' m :=
  fun e i hi => denote_ext (h e i hi) hx

theorem EMemoOK.insert {st : EStore} {m : EMemo} (hm : EMemoOK st m)
    {e : Expr} {i : EIdx} (hd : denoteE st i = some e) :
    EMemoOK st (m.insert e i) := by
  intro k x hk
  rw [Std.HashMap.getElem?_insert] at hk
  split at hk
  · rename_i heq
    obtain rfl : e = k := by simpa using heq
    simp only [Option.some.injEq] at hk
    subst hk; exact hd
  · exact hm k x hk

/-! ## The intern direction's frame -/

structure IStep (s s' : AState) : Prop where
  ok : StateOK s'
  ext : Ext s.store s'.store
  off : s'.store.scratchOn = false
  memos : s'.memos = s.memos
  caches : s'.caches = s.caches
  pins : s'.pins = s.pins

theorem IStep.trans {a b c : AState} (h₁ : IStep a b) (h₂ : IStep b c) :
    IStep a c :=
  ⟨h₂.ok, h₁.ext.trans h₂.ext, h₂.off, by rw [h₂.memos, h₁.memos],
    by rw [h₂.caches, h₁.caches], by rw [h₂.pins, h₁.pins]⟩

theorem IStep.toParse {s s' : AState} (h : IStep s s')
    (hoff : s.store.scratchOn = false) : ParseStep s s' :=
  ParseStep.of_caches h.ok h.ext (by rw [h.off, hoff]) h.caches h.pins

/-! ## The same frame, WITHOUT the scratch flag

`IStep`'s third field pins the scratch tier CLOSED at the state the step
leaves; `IStepS`'s says only that the step did not TOUCH it.  That is the whole
difference between them, and it is what makes the intern family below readable
from INSIDE the per-declaration bracket: `Bridge/Checker/Basis.lean`'s
`basisPinHit` runs with `scratchOn = true` and can never supply an `hoff`.

**There is no second copy of the induction.**  The family is stated once, over
`IStepS`, with the denotation alone, and the `IStep` version — `hoff` in,
`Pers…` out — is a three-line corollary: `IStepS.toIStep` carries the frame and
`Bridge/Frontend/Rel.lean`'s `Pers…_of_denote` carries the persistence, because
persistence is a CONSEQUENCE of the denotation at a state whose scratch tier is
closed and not extra content the intern has to prove.  The five leaves that
conclude a `denoteEView`/`denoteNView` equation rather than a `some` keep their
own four-line derivation from the spec's `view` conjunct, since a view equation
is not a denotation.  DESIGN #97-P3-Frontend round 6. -/
structure IStepS (s s' : AState) : Prop where
  ok : StateOK s'
  ext : Ext s.store s'.store
  scratch : s'.store.scratchOn = s.store.scratchOn
  memos : s'.memos = s.memos
  caches : s'.caches = s.caches
  pins : s'.pins = s.pins

theorem IStepS.refl {s : AState} (hok : StateOK s) : IStepS s s :=
  ⟨hok, Ext.refl _, rfl, rfl, rfl, rfl⟩

theorem IStepS.trans {a b c : AState} (h₁ : IStepS a b) (h₂ : IStepS b c) :
    IStepS a c :=
  ⟨h₂.ok, h₁.ext.trans h₂.ext, by rw [h₂.scratch, h₁.scratch],
    by rw [h₂.memos, h₁.memos], by rw [h₂.caches, h₁.caches],
    by rw [h₂.pins, h₁.pins]⟩

/-- con-leche: none — the flag, transported: a step that leaves the scratch
tier as it found it leaves it closed if it was closed. -/
theorem IStepS.off {s s' : AState} (h : IStepS s s')
    (hoff : s.store.scratchOn = false) : s'.store.scratchOn = false := by
  rw [h.scratch]; exact hoff

/-- con-leche: none — the frame at a caller that HAS the flag closed. -/
theorem IStepS.toIStep {s s' : AState} (h : IStepS s s')
    (hoff : s.store.scratchOn = false) : IStep s s' :=
  ⟨h.ok, h.ext, h.off hoff, h.memos, h.caches, h.pins⟩

/-! ## `internE`'s scratch flag -/

theorem internE_scratchOn {s s' : AState} {v : ENodeView} {h : EIdx}
    (hrun : internE v s = .ok (h, s')) :
    s'.store.scratchOn = s.store.scratchOn := by
  -- the two binder arms (task #97-T2-LOCKSTEP D6): the datum step, then the
  -- node step at its handle, each read off by `Arena/PersistentRun.lean`
  cases v
  case lam ty b m =>
    obtain ⟨mi, s₁, h1, h2⟩ := internE_lam_split hrun
    obtain ⟨-, rfl, rfl⟩ := internBME_ok h1
    obtain ⟨-, rfl⟩ := internLamIE_ok h2
    simp only [EStore.internLamI, EStore.scratchOn_internBindI, EStore.scratchOn_internBM]
  case forallE ty b m =>
    obtain ⟨mi, s₁, h1, h2⟩ := internE_forallE_split hrun
    obtain ⟨-, rfl, rfl⟩ := internBME_ok h1
    obtain ⟨-, rfl⟩ := internForallEIE_ok h2
    simp only [EStore.internForallEI, EStore.scratchOn_internBindI,
      EStore.scratchOn_internBM]
  all_goals
    rcases internNodeE_ok hrun with ⟨-, rfl⟩ | ⟨-, -, rfl⟩
    · rfl
    · exact EStore.scratchOn_intern _ _

/-! ## The four leaf interns, in run form -/

theorem internE_sstep {s s' : AState} (hok : StateOK s)
    {v : ENodeView} (hv : s.store.ViewOK v)
    {h : EIdx} (hrun : internE v s = .ok (h, s')) :
    IStepS s s' ∧ denoteE s'.store h = denoteEView s'.store v := by
  obtain ⟨hwf, hx, -, -, -, hm, hc, hp, -, hden⟩ :=
    AM.of_run (P := fun t => t = s) rfl hrun (internE_spec s v hok.wf hv)
  exact ⟨⟨⟨hwf⟩, hx, internE_scratchOn hrun, hm, hc, hp⟩, hden⟩

theorem internName_sstep {s s' : AState} (hok : StateOK s)
    {nm : ConLeche.Name} {h : NIdx}
    (hrun : ConRon.Arena.internName nm s = .ok (h, s')) :
    IStepS s s' ∧ denoteN s'.store.ns h = some nm := by
  obtain ⟨hwf, hx, -, -, hon, hm, hc, hp, hden⟩ :=
    AM.of_run (P := fun t => t = s) rfl hrun (internName_spec s nm hok.wf)
  exact ⟨⟨⟨hwf⟩, hx, hon, hm, hc, hp⟩, hden⟩

theorem internLevel_sstep {s s' : AState} (hok : StateOK s)
    {u : Level} {h : LIdx}
    (hrun : ConRon.Arena.internLevel u s = .ok (h, s')) :
    IStepS s s' ∧ denoteL s'.store.ls h = some u := by
  obtain ⟨hwf, hx, -, -, hon, hm, hc, hp, hden⟩ :=
    AM.of_run (P := fun t => t = s) rfl hrun (internLevel_spec s u hok.wf)
  exact ⟨⟨⟨hwf⟩, hx, hon, hm, hc, hp⟩, hden⟩

theorem internLevels_sstep {s s' : AState} (hok : StateOK s)
    {us : List Level} {h : LsIdx}
    (hrun : ConRon.Arena.internLevels us s = .ok (h, s')) :
    IStepS s s' ∧ denoteLs s'.store.lss h = some us := by
  obtain ⟨hwf, hx, -, -, hon, hm, hc, hp, hden⟩ :=
    AM.of_run (P := fun t => t = s) rfl hrun (internLevels_spec s us hok.wf)
  exact ⟨⟨⟨hwf⟩, hx, hon, hm, hc, hp⟩, hden⟩

/-! ## Two handle lists -/

theorem internNameList_sstep : ∀ (ns : List ConLeche.Name) {s s' : AState}
    {hs : List NIdx}, StateOK s →
    ConRon.Arena.Frontend.internNameList ns s = .ok (hs, s') →
    IStepS s s' ∧ denoteNList s'.store.ns hs = some ns := by
  intro ns
  induction ns with
  | nil =>
    intro s s' hs hok hrun
    rw [ConRon.Arena.Frontend.internNameList] at hrun
    obtain ⟨hv, hst⟩ := AM.pure_ok hrun
    subst hst; subst hv
    exact ⟨IStepS.refl hok, rfl⟩
  | cons a as ih =>
    intro s s' hs hok hrun
    rw [ConRon.Arena.Frontend.internNameList] at hrun
    obtain ⟨h1, s₁, hn, hrest⟩ := AM.bind_ok hrun
    obtain ⟨hstep1, hdn⟩ := internName_sstep hok hn
    obtain ⟨t1, s₂, hns, hrest2⟩ := AM.bind_ok hrest
    obtain ⟨hstep2, hdns⟩ := ih hstep1.ok hns
    obtain ⟨hv, hst⟩ := AM.pure_ok hrest2
    subst hst; subst hv
    refine ⟨hstep1.trans hstep2, ?_⟩
    simp only [denoteNList, denoteN_ext hdn hstep2.ext, hdns]

theorem internLevelList_sstep : ∀ (us : List Level) {s s' : AState}
    {hs : List LIdx}, StateOK s →
    ConRon.Arena.internLevelList us s = .ok (hs, s') →
    IStepS s s' ∧ denoteLList s'.store.ls hs = some us := by
  intro us
  induction us with
  | nil =>
    intro s s' hs hok hrun
    rw [ConRon.Arena.internLevelList] at hrun
    obtain ⟨hv, hst⟩ := AM.pure_ok hrun
    subst hst; subst hv
    exact ⟨IStepS.refl hok, rfl⟩
  | cons a as ih =>
    intro s s' hs hok hrun
    rw [ConRon.Arena.internLevelList] at hrun
    obtain ⟨h1, s₁, hl, hrest⟩ := AM.bind_ok hrun
    obtain ⟨hstep1, hdl⟩ := internLevel_sstep hok hl
    obtain ⟨t1, s₂, hls, hrest2⟩ := AM.bind_ok hrest
    obtain ⟨hstep2, hdls⟩ := ih hstep1.ok hls
    obtain ⟨hv, hst⟩ := AM.pure_ok hrest2
    subst hst; subst hv
    refine ⟨hstep1.trans hstep2, ?_⟩
    simp only [denoteLList, opt2_eq_some_iff]
    exact ⟨a, as, denoteL_ext hdl hstep2.ext, hdls, rfl⟩

/-! ## The expression intern, arm by arm -/

theorem internExprGo_sstep :
    ∀ (e : Expr) {s s' : AState} {m m' : EMemo} {h : EIdx},
      StateOK s → EMemoOK s.store m →
      internExprGo m e s = .ok ((m', h), s') →
      IStepS s s' ∧ denoteE s'.store h = some e ∧
        EMemoOK s'.store m' := by
  intro e
  induction e with
  | bvar i =>
    intro s s' m m' h hok hm hrun
    rw [internExprGo] at hrun
    obtain ⟨x, s₁, hin, hrest⟩ := AM.bind_ok hrun
    obtain ⟨hv, hst⟩ := AM.pure_ok hrest
    subst hst
    simp only [Prod.mk.injEq] at hv
    obtain ⟨hmm, hhh⟩ := hv
    subst hmm; subst hhh
    obtain ⟨hstep1, hden⟩ := internE_sstep hok viewOK_bvar hin
    exact ⟨hstep1, by rw [hden]; rfl, hm.mono hstep1.ext⟩
  | lit l =>
    intro s s' m m' h hok hm hrun
    rw [internExprGo] at hrun
    obtain ⟨x, s₁, hin, hrest⟩ := AM.bind_ok hrun
    obtain ⟨hv, hst⟩ := AM.pure_ok hrest
    subst hst
    simp only [Prod.mk.injEq] at hv
    obtain ⟨hmm, hhh⟩ := hv
    subst hmm; subst hhh
    obtain ⟨hstep1, hden⟩ := internE_sstep hok viewOK_lit hin
    exact ⟨hstep1, by rw [hden]; rfl, hm.mono hstep1.ext⟩
  | sort u =>
    intro s s' m m' h hok hm hrun
    rw [internExprGo] at hrun
    obtain ⟨lu, s₁, hl, hrest⟩ := AM.bind_ok hrun
    obtain ⟨hstep1, hdl⟩ := internLevel_sstep hok hl
    obtain ⟨x, s₂, hin, hrest2⟩ := AM.bind_ok hrest
    obtain ⟨hstep2, hden⟩ :=
      internE_sstep hstep1.ok
        (viewOK_sort (lview_isSome_of_denote hdl)) hin
    obtain ⟨hv, hst⟩ := AM.pure_ok hrest2
    subst hst
    simp only [Prod.mk.injEq] at hv
    obtain ⟨hmm, hhh⟩ := hv
    subst hmm; subst hhh
    refine ⟨hstep1.trans hstep2, ?_,
      (hm.mono hstep1.ext).mono hstep2.ext⟩
    rw [hden]
    simp only [denoteEView, denoteL_ext hdl hstep2.ext, Option.map_some]
  | const n us =>
    intro s s' m m' h hok hm hrun
    rw [internExprGo] at hrun
    obtain ⟨hn, s₁, hnm, hrest⟩ := AM.bind_ok hrun
    obtain ⟨hstep1, hdn⟩ := internName_sstep hok hnm
    obtain ⟨hus, s₂, hls, hrest2⟩ := AM.bind_ok hrest
    obtain ⟨hstep2, hdls⟩ := internLevels_sstep hstep1.ok hls
    obtain ⟨x, s₃, hin, hrest3⟩ := AM.bind_ok hrest2
    obtain ⟨hstep3, hden⟩ :=
      internE_sstep hstep2.ok
        (viewOK_const (nview_isSome_of_denote (denoteN_ext hdn hstep2.ext))
          (by obtain ⟨w, hw, -⟩ := Arena.denoteLs_view hdls; rw [hw]; rfl)) hin
    obtain ⟨hv, hst⟩ := AM.pure_ok hrest3
    subst hst
    simp only [Prod.mk.injEq] at hv
    obtain ⟨hmm, hhh⟩ := hv
    subst hmm; subst hhh
    refine ⟨(hstep1.trans hstep2).trans hstep3, ?_,
      ((hm.mono hstep1.ext).mono hstep2.ext).mono hstep3.ext⟩
    rw [hden]
    simp only [denoteEView, opt2_eq_some_iff]
    exact ⟨n, us, denoteN_ext hdn (hstep2.ext.trans hstep3.ext),
      hstep3.ext.lss.lst hus us hdls, rfl⟩
  | fvar i ty ih =>
    intro s s' m m' h hok hm hrun
    rw [internExprGo] at hrun
    cases hmem : m[Expr.fvar i ty]? with
    | some hh =>
      rw [hmem] at hrun
      simp only [] at hrun
      obtain ⟨hv, hst⟩ := AM.pure_ok hrun
      subst hst
      simp only [Prod.mk.injEq] at hv
      obtain ⟨hmm, hhh⟩ := hv
      subst hmm; subst hhh
      have hd := hm _ _ hmem
      obtain ⟨w, hw⟩ := Arena.denoteE_view hd
      exact ⟨IStepS.refl hok, hd, hm⟩
    | none =>
      rw [hmem] at hrun
      simp only [] at hrun
      obtain ⟨p1, s₁, h1, hrest⟩ := AM.bind_ok hrun
      obtain ⟨m1, t1⟩ := p1
      obtain ⟨hstep1, hdt, hm1⟩ := ih hok hm h1
      simp only [] at hrest
      obtain ⟨x, s₂, hin, hrest2⟩ := AM.bind_ok hrest
      obtain ⟨hstep2, hden⟩ :=
        internE_sstep hstep1.ok (viewOK_fvar (by rw [hdt]; rfl)) hin
      have hde : denoteE s₂.store x = some (Expr.fvar i ty) := by
        rw [hden]
        simp only [denoteEView, denote_ext hdt hstep2.ext, Option.map_some]
      obtain ⟨hv, hst⟩ := AM.pure_ok hrest2
      subst hst
      simp only [Prod.mk.injEq] at hv
      obtain ⟨hmm, hhh⟩ := hv
      subst hmm; subst hhh
      exact ⟨hstep1.trans hstep2, hde,
        (hm1.mono hstep2.ext).insert hde⟩
  | app f a ihf iha =>
    intro s s' m m' h hok hm hrun
    rw [internExprGo] at hrun
    cases hmem : m[Expr.app f a]? with
    | some hh =>
      rw [hmem] at hrun
      simp only [] at hrun
      obtain ⟨hv, hst⟩ := AM.pure_ok hrun
      subst hst
      simp only [Prod.mk.injEq] at hv
      obtain ⟨hmm, hhh⟩ := hv
      subst hmm; subst hhh
      have hd := hm _ _ hmem
      obtain ⟨w, hw⟩ := Arena.denoteE_view hd
      exact ⟨IStepS.refl hok, hd, hm⟩
    | none =>
      rw [hmem] at hrun
      simp only [] at hrun
      obtain ⟨p1, s₁, h1, hrest⟩ := AM.bind_ok hrun
      obtain ⟨m1, hf⟩ := p1
      obtain ⟨hstep1, hdf, hm1⟩ := ihf hok hm h1
      simp only [] at hrest
      obtain ⟨p2, s₂, h2, hrest2⟩ := AM.bind_ok hrest
      obtain ⟨m2, ha⟩ := p2
      obtain ⟨hstep2, hda, hm2⟩ := iha hstep1.ok hm1 h2
      simp only [] at hrest2
      obtain ⟨x, s₃, hin, hrest3⟩ := AM.bind_ok hrest2
      obtain ⟨hstep3, hden⟩ :=
        internE_sstep hstep2.ok
          (viewOK_app (by rw [denote_ext hdf hstep2.ext]; rfl)
            (by rw [hda]; rfl)) hin
      have hde : denoteE s₃.store x = some (Expr.app f a) := by
        rw [hden]
        simp only [denoteEView, opt2_eq_some_iff]
        exact ⟨f, a, denote_ext hdf (hstep2.ext.trans hstep3.ext),
          denote_ext hda hstep3.ext, rfl⟩
      obtain ⟨hv, hst⟩ := AM.pure_ok hrest3
      subst hst
      simp only [Prod.mk.injEq] at hv
      obtain ⟨hmm, hhh⟩ := hv
      subst hmm; subst hhh
      exact ⟨(hstep1.trans hstep2).trans hstep3, hde,
        (hm2.mono hstep3.ext).insert hde⟩
  | lam ty b bi ihty ihb =>
    intro s s' m m' h hok hm hrun
    rw [internExprGo] at hrun
    cases hmem : m[Expr.lam ty b bi]? with
    | some hh =>
      rw [hmem] at hrun
      simp only [] at hrun
      obtain ⟨hv, hst⟩ := AM.pure_ok hrun
      subst hst
      simp only [Prod.mk.injEq] at hv
      obtain ⟨hmm, hhh⟩ := hv
      subst hmm; subst hhh
      have hd := hm _ _ hmem
      obtain ⟨w, hw⟩ := Arena.denoteE_view hd
      exact ⟨IStepS.refl hok, hd, hm⟩
    | none =>
      rw [hmem] at hrun
      simp only [] at hrun
      obtain ⟨p1, s₁, h1, hrest⟩ := AM.bind_ok hrun
      obtain ⟨m1, ht⟩ := p1
      obtain ⟨hstep1, hdt, hm1⟩ := ihty hok hm h1
      simp only [] at hrest
      obtain ⟨p2, s₂, h2, hrest2⟩ := AM.bind_ok hrest
      obtain ⟨m2, hb⟩ := p2
      obtain ⟨hstep2, hdb, hm2⟩ := ihb hstep1.ok hm1 h2
      simp only [] at hrest2
      obtain ⟨x, s₃, hin, hrest3⟩ := AM.bind_ok hrest2
      obtain ⟨hstep3, hden⟩ :=
        internE_sstep hstep2.ok
          (viewOK_lam (by rw [denote_ext hdt hstep2.ext]; rfl)
            (by rw [hdb]; rfl)) hin
      have hde : denoteE s₃.store x = some (Expr.lam ty b bi) := by
        rw [hden]
        simp only [denoteEView, opt2_eq_some_iff]
        exact ⟨ty, b, denote_ext hdt (hstep2.ext.trans hstep3.ext),
          denote_ext hdb hstep3.ext, rfl⟩
      obtain ⟨hv, hst⟩ := AM.pure_ok hrest3
      subst hst
      simp only [Prod.mk.injEq] at hv
      obtain ⟨hmm, hhh⟩ := hv
      subst hmm; subst hhh
      exact ⟨(hstep1.trans hstep2).trans hstep3, hde,
        (hm2.mono hstep3.ext).insert hde⟩
  | forallE ty b bi ihty ihb =>
    intro s s' m m' h hok hm hrun
    rw [internExprGo] at hrun
    cases hmem : m[Expr.forallE ty b bi]? with
    | some hh =>
      rw [hmem] at hrun
      simp only [] at hrun
      obtain ⟨hv, hst⟩ := AM.pure_ok hrun
      subst hst
      simp only [Prod.mk.injEq] at hv
      obtain ⟨hmm, hhh⟩ := hv
      subst hmm; subst hhh
      have hd := hm _ _ hmem
      obtain ⟨w, hw⟩ := Arena.denoteE_view hd
      exact ⟨IStepS.refl hok, hd, hm⟩
    | none =>
      rw [hmem] at hrun
      simp only [] at hrun
      obtain ⟨p1, s₁, h1, hrest⟩ := AM.bind_ok hrun
      obtain ⟨m1, ht⟩ := p1
      obtain ⟨hstep1, hdt, hm1⟩ := ihty hok hm h1
      simp only [] at hrest
      obtain ⟨p2, s₂, h2, hrest2⟩ := AM.bind_ok hrest
      obtain ⟨m2, hb⟩ := p2
      obtain ⟨hstep2, hdb, hm2⟩ := ihb hstep1.ok hm1 h2
      simp only [] at hrest2
      obtain ⟨x, s₃, hin, hrest3⟩ := AM.bind_ok hrest2
      obtain ⟨hstep3, hden⟩ :=
        internE_sstep hstep2.ok
          (viewOK_forallE (by rw [denote_ext hdt hstep2.ext]; rfl)
            (by rw [hdb]; rfl)) hin
      have hde : denoteE s₃.store x = some (Expr.forallE ty b bi) := by
        rw [hden]
        simp only [denoteEView, opt2_eq_some_iff]
        exact ⟨ty, b, denote_ext hdt (hstep2.ext.trans hstep3.ext),
          denote_ext hdb hstep3.ext, rfl⟩
      obtain ⟨hv, hst⟩ := AM.pure_ok hrest3
      subst hst
      simp only [Prod.mk.injEq] at hv
      obtain ⟨hmm, hhh⟩ := hv
      subst hmm; subst hhh
      exact ⟨(hstep1.trans hstep2).trans hstep3, hde,
        (hm2.mono hstep3.ext).insert hde⟩
  | letE ty v b ihty ihv ihb =>
    intro s s' m m' h hok hm hrun
    rw [internExprGo] at hrun
    cases hmem : m[Expr.letE ty v b]? with
    | some hh =>
      rw [hmem] at hrun
      simp only [] at hrun
      obtain ⟨hv', hst⟩ := AM.pure_ok hrun
      subst hst
      simp only [Prod.mk.injEq] at hv'
      obtain ⟨hmm, hhh⟩ := hv'
      subst hmm; subst hhh
      have hd := hm _ _ hmem
      obtain ⟨w, hw⟩ := Arena.denoteE_view hd
      exact ⟨IStepS.refl hok, hd, hm⟩
    | none =>
      rw [hmem] at hrun
      simp only [] at hrun
      obtain ⟨p1, s₁, h1, hrest⟩ := AM.bind_ok hrun
      obtain ⟨m1, ht⟩ := p1
      obtain ⟨hstep1, hdt, hm1⟩ := ihty hok hm h1
      simp only [] at hrest
      obtain ⟨p2, s₂, h2, hrest2⟩ := AM.bind_ok hrest
      obtain ⟨m2, hvv⟩ := p2
      obtain ⟨hstep2, hdv, hm2⟩ := ihv hstep1.ok hm1 h2
      simp only [] at hrest2
      obtain ⟨p3, s₃, h3, hrest3⟩ := AM.bind_ok hrest2
      obtain ⟨m3, hb⟩ := p3
      obtain ⟨hstep3, hdb, hm3⟩ := ihb hstep2.ok hm2 h3
      simp only [] at hrest3
      obtain ⟨x, s₄, hin, hrest4⟩ := AM.bind_ok hrest3
      obtain ⟨hstep4, hden⟩ :=
        internE_sstep hstep3.ok
          (viewOK_letE
            (by rw [denote_ext hdt (hstep2.ext.trans hstep3.ext)]; rfl)
            (by rw [denote_ext hdv hstep3.ext]; rfl) (by rw [hdb]; rfl)) hin
      have hde : denoteE s₄.store x = some (Expr.letE ty v b) := by
        rw [hden]
        simp only [denoteEView, opt3_eq_some_iff]
        exact ⟨ty, v, b,
          denote_ext hdt ((hstep2.ext.trans hstep3.ext).trans hstep4.ext),
          denote_ext hdv (hstep3.ext.trans hstep4.ext),
          denote_ext hdb hstep4.ext, rfl⟩
      obtain ⟨hv', hst⟩ := AM.pure_ok hrest4
      subst hst
      simp only [Prod.mk.injEq] at hv'
      obtain ⟨hmm, hhh⟩ := hv'
      subst hmm; subst hhh
      exact ⟨((hstep1.trans hstep2).trans hstep3).trans hstep4, hde,
        (hm3.mono hstep4.ext).insert hde⟩
  | proj n i sub ih =>
    intro s s' m m' h hok hm hrun
    rw [internExprGo] at hrun
    cases hmem : m[Expr.proj n i sub]? with
    | some hh =>
      rw [hmem] at hrun
      simp only [] at hrun
      obtain ⟨hv, hst⟩ := AM.pure_ok hrun
      subst hst
      simp only [Prod.mk.injEq] at hv
      obtain ⟨hmm, hhh⟩ := hv
      subst hmm; subst hhh
      have hd := hm _ _ hmem
      obtain ⟨w, hw⟩ := Arena.denoteE_view hd
      exact ⟨IStepS.refl hok, hd, hm⟩
    | none =>
      rw [hmem] at hrun
      simp only [] at hrun
      -- the name first, then the subterm: the port's order (task
      -- #97-T2-LOCKSTEP lane Promote, divergence P1)
      obtain ⟨hn, s₁, hnm, hrest⟩ := AM.bind_ok hrun
      obtain ⟨hstep1, hdn⟩ := internName_sstep hok hnm
      obtain ⟨p1, s₂, h1, hrest2⟩ := AM.bind_ok hrest
      obtain ⟨m1, hsu⟩ := p1
      obtain ⟨hstep2, hds, hm1⟩ := ih hstep1.ok (hm.mono hstep1.ext) h1
      simp only [] at hrest2
      obtain ⟨x, s₃, hin, hrest3⟩ := AM.bind_ok hrest2
      obtain ⟨hstep3, hden⟩ :=
        internE_sstep hstep2.ok
          (viewOK_proj (nview_isSome_of_denote (denoteN_ext hdn hstep2.ext))
            (by rw [hds]; rfl)) hin
      have hde : denoteE s₃.store x = some (Expr.proj n i sub) := by
        rw [hden]
        simp only [denoteEView, opt2_eq_some_iff]
        exact ⟨n, sub, denoteN_ext hdn (hstep2.ext.trans hstep3.ext),
          denote_ext hds hstep3.ext, rfl⟩
      obtain ⟨hv, hst⟩ := AM.pure_ok hrest3
      subst hst
      simp only [Prod.mk.injEq] at hv
      obtain ⟨hmm, hhh⟩ := hv
      subst hmm; subst hhh
      exact ⟨(hstep1.trans hstep2).trans hstep3, hde,
        (hm1.mono hstep3.ext).insert hde⟩

theorem internExprList_sstep : ∀ (es : List Expr) {s s' : AState}
    {m m' : EMemo} {hs : List EIdx}, StateOK s →
    EMemoOK s.store m → ConRon.Arena.Frontend.internExprList m es s = .ok ((m', hs), s') →
    IStepS s s' ∧ denoteEList s'.store hs = some es ∧
      EMemoOK s'.store m' := by
  intro es
  induction es with
  | nil =>
    intro s s' m m' hs hok hm hrun
    rw [ConRon.Arena.Frontend.internExprList] at hrun
    obtain ⟨hv, hst⟩ := AM.pure_ok hrun
    subst hst
    simp only [Prod.mk.injEq] at hv
    obtain ⟨hmm, hhh⟩ := hv
    subst hmm; subst hhh
    exact ⟨IStepS.refl hok, rfl, hm⟩
  | cons e es ih =>
    intro s s' m m' hs hok hm hrun
    rw [ConRon.Arena.Frontend.internExprList] at hrun
    obtain ⟨p1, s₁, h1, hrest⟩ := AM.bind_ok hrun
    obtain ⟨m1, x1⟩ := p1
    obtain ⟨hstep1, hde, hm1⟩ := internExprGo_sstep e hok hm h1
    simp only [] at hrest
    obtain ⟨p2, s₂, h2, hrest2⟩ := AM.bind_ok hrest
    obtain ⟨m2, xs⟩ := p2
    obtain ⟨hstep2, hdes, hm2⟩ :=
      ih hstep1.ok hm1 h2
    simp only [] at hrest2
    obtain ⟨hv, hst⟩ := AM.pure_ok hrest2
    subst hst
    simp only [Prod.mk.injEq] at hv
    obtain ⟨hmm, hhh⟩ := hv
    subst hmm; subst hhh
    refine ⟨hstep1.trans hstep2, ?_, hm2⟩
    simp only [denoteEList, denote_ext hde hstep2.ext, hdes]

/-! ## The reserved projection-table name -/

theorem internNNode_sstep {s s' : AState} (hok : StateOK s)
    {v : NNodeView}
    (hv : s.store.ns.ViewOK v) {h : NIdx}
    (hrun : internNNode v s = .ok (h, s')) :
    IStepS s s' ∧
      denoteN s'.store.ns h = denoteNView s'.store.ns v := by
  obtain ⟨hwf, hx, -, -, hon, hm, hc, hp, -, hden⟩ :=
    AM.of_run (P := fun t => t = s) rfl hrun (internNNode_spec s v hok.wf hv)
  exact ⟨⟨⟨hwf⟩, hx, hon, hm, hc, hp⟩, hden⟩

/-- con-leche: ConLeche/Kernel/Expr.lean Level — a LEVEL node, in the `IStep`
frame: `parseLevelEntryD`'s four arms intern one apiece. -/
theorem internLNode_sstep {s s' : AState} (hok : StateOK s)
    {v : LNodeView}
    (hv : s.store.ls.ViewOK v) {h : LIdx}
    (hrun : ConRon.Arena.internLNode v s = .ok (h, s')) :
    IStepS s s' ∧
      denoteL s'.store.ls h = denoteLView s'.store.ls v := by
  obtain ⟨hwf, hx, -, -, hon, hm, hc, hp, -, hden⟩ :=
    AM.of_run (P := fun t => t = s) rfl hrun (internLNode_spec s v hok.wf hv)
  exact ⟨⟨⟨hwf⟩, hx, hon, hm, hc, hp⟩, hden⟩

/-- con-leche: none — a LEVEL-LIST node, in the `IStep` frame: the one
`const` arm of `parseExprEntryD` interns it (DESIGN §8.3's `LsIdx`). -/
theorem internLsNode_sstep {s s' : AState} (hok : StateOK s)
    {v : LsNodeView}
    (hv : s.store.lss.ViewOK v) {h : LsIdx}
    (hrun : ConRon.Arena.internLsNode v s = .ok (h, s')) :
    IStepS s s' ∧ denoteLs s'.store.lss h = denoteLsView s'.store.lss v := by
  obtain ⟨hwf, hx, -, -, hon, hm, hc, hp, -, hden⟩ :=
    AM.of_run (P := fun t => t = s) rfl hrun (internLsNode_spec s v hok.wf hv)
  exact ⟨⟨⟨hwf⟩, hx, hon, hm, hc, hp⟩, hden⟩

/-- con-leche: ConLeche/Kernel/Env.lean:631-635 projTableName — the reserved
table name, interned.  **The denotation conjunct is round 5's addition**: it is
the whole of what `Bridge/Frontend/Rel.lean`'s `IProjNamed` asks of an interned
table, and therefore the whole of what the seam's new clause rests on
(DESIGN #97-P3-Frontend round 5, the repair of finding 16). -/
theorem projTableName_sstep {s s' : AState} (hok : StateOK s)
    {T : NIdx} {Tn : ConLeche.Name}
    (hT : denoteN s.store.ns T = some Tn) {h : NIdx}
    (hrun : ConRon.Arena.projTableName T s = .ok (h, s')) :
    IStepS s s' ∧
      denoteN s'.store.ns h = some (ConLeche.projTableName Tn) := by
  rw [ConRon.Arena.projTableName] at hrun
  obtain ⟨a, s₁, h1, hrest⟩ := AM.bind_ok hrun
  obtain ⟨hstep1, hda⟩ :=
    internNNode_sstep hok
      (by intro c hc
          simp only [NNodeView.children, List.mem_singleton] at hc
          subst hc; exact nview_isSome_of_denote hT) h1
  have hda' : (s₁.store.ns.view a).isSome = true := by
    obtain ⟨w, hw⟩ := Arena.denoteN_view
      (show denoteN s₁.store.ns a = some (Tn.str "projTable") by
        rw [hda]; simp only [denoteNView, denoteN_ext hT hstep1.ext,
          Option.map_some])
    rw [hw]; rfl
  obtain ⟨hstep2, hdb⟩ :=
    internNNode_sstep hstep1.ok
      (by intro c hc
          simp only [NNodeView.children, List.mem_singleton] at hc
          subst hc; exact hda') hrest
  refine ⟨hstep1.trans hstep2, ?_⟩
  rw [hdb]
  simp only [denoteNView, denoteN_ext
    (show denoteN s₁.store.ns a = some (Tn.str "projTable") by
      rw [hda]; simp only [denoteNView, denoteN_ext hT hstep1.ext,
        Option.map_some]) hstep2.ext, Option.map_some]
  rfl

/-! ## The record layers -/

theorem internCV_sstep {s s' : AState} (hok : StateOK s)
    {m m' : EMemo} (hm : EMemoOK s.store m)
    {cv : ConstantVal} {icv : IConstantVal}
    (hrun : internCV m cv s = .ok ((m', icv), s')) :
    IStepS s s' ∧ denoteCV s'.store icv = some cv ∧
      EMemoOK s'.store m' := by
  rw [ConRon.Arena.Frontend.internCV] at hrun
  obtain ⟨hn, s₁, h1, hrest⟩ := AM.bind_ok hrun
  obtain ⟨hstep1, hdn⟩ := internName_sstep hok h1
  obtain ⟨hlps, s₂, h2, hrest2⟩ := AM.bind_ok hrest
  obtain ⟨hstep2, hdlps⟩ :=
    internNameList_sstep cv.levelParams hstep1.ok h2
  obtain ⟨p3, s₃, h3, hrest3⟩ := AM.bind_ok hrest2
  obtain ⟨m3, hty⟩ := p3
  obtain ⟨hstep3, hdty, hm3⟩ :=
    internExprGo_sstep cv.type hstep2.ok
      (hm.mono (hstep1.ext.trans hstep2.ext)) h3
  simp only [] at hrest3
  have hd : denoteCV s₃.store ⟨hn, hlps, hty⟩ = some cv := by
    simp only [denoteCV, denoteN_ext hdn (hstep2.ext.trans hstep3.ext),
      denoteNListE_ext hstep3.ext _ _ hdlps, hdty]
  obtain ⟨hv, hst⟩ := AM.pure_ok hrest3
  subst hst
  simp only [Prod.mk.injEq] at hv
  obtain ⟨hmm, hii⟩ := hv
  subst hmm; subst hii
  exact ⟨(hstep1.trans hstep2).trans hstep3,
    hd, hm3⟩

theorem internFire_sstep {s s' : AState} (hok : StateOK s)
    {m m' : EMemo} (hm : EMemoOK s.store m)
    {f : RecRuleFire} {fi : IRecRuleFire}
    (hrun : internFire m f s = .ok ((m', fi), s')) :
    IStepS s s' ∧ denoteFire s'.store fi = some f ∧
      EMemoOK s'.store m' := by
  cases f with
  | inert =>
    rw [ConRon.Arena.Frontend.internFire] at hrun
    obtain ⟨hv, hst⟩ := AM.pure_ok hrun
    subst hst
    simp only [Prod.mk.injEq] at hv
    obtain ⟨hmm, hii⟩ := hv
    subst hmm; subst hii
    exact ⟨IStepS.refl hok, rfl, hm⟩
  | plain =>
    rw [ConRon.Arena.Frontend.internFire] at hrun
    obtain ⟨hv, hst⟩ := AM.pure_ok hrun
    subst hst
    simp only [Prod.mk.injEq] at hv
    obtain ⟨hmm, hii⟩ := hv
    subst hmm; subst hii
    exact ⟨IStepS.refl hok, rfl, hm⟩
  | nested lvls pins =>
    rw [ConRon.Arena.Frontend.internFire] at hrun
    obtain ⟨hls, s₁, h1, hrest⟩ := AM.bind_ok hrun
    obtain ⟨hstep1, hdls⟩ := internLevelList_sstep lvls hok h1
    obtain ⟨p2, s₂, h2, hrest2⟩ := AM.bind_ok hrest
    obtain ⟨m2, hps⟩ := p2
    obtain ⟨hstep2, hdps, hm2⟩ :=
      internExprList_sstep pins hstep1.ok (hm.mono hstep1.ext) h2
    simp only [] at hrest2
    have hd : denoteFire s₂.store (.nested hls hps) = some (.nested lvls pins) := by
      simp only [denoteFire, denoteLListE_ext hstep2.ext _ _ hdls, hdps]
    obtain ⟨hv, hst⟩ := AM.pure_ok hrest2
    subst hst
    simp only [Prod.mk.injEq] at hv
    obtain ⟨hmm, hii⟩ := hv
    subst hmm; subst hii
    exact ⟨hstep1.trans hstep2, hd, hm2⟩

theorem internRule_sstep {s s' : AState} (hok : StateOK s)
    {m m' : EMemo} (hm : EMemoOK s.store m)
    {rl : RecRule} {ri : IRecRule}
    (hrun : internRule m rl s = .ok ((m', ri), s')) :
    IStepS s s' ∧ denoteRule s'.store ri = some rl ∧
      EMemoOK s'.store m' := by
  rw [ConRon.Arena.Frontend.internRule] at hrun
  obtain ⟨hc, s₁, h1, hrest⟩ := AM.bind_ok hrun
  obtain ⟨hstep1, hdc⟩ := internName_sstep hok h1
  obtain ⟨p2, s₂, h2, hrest2⟩ := AM.bind_ok hrest
  obtain ⟨m2, hf⟩ := p2
  obtain ⟨hstep2, hdf, hm2⟩ :=
    internFire_sstep hstep1.ok (hm.mono hstep1.ext) h2
  simp only [] at hrest2
  obtain ⟨p3, s₃, h3, hrest3⟩ := AM.bind_ok hrest2
  obtain ⟨m3, hr⟩ := p3
  obtain ⟨hstep3, hdr, hm3⟩ :=
    internExprGo_sstep rl.rhs hstep2.ok hm2 h3
  simp only [] at hrest3
  have hd : denoteRule s₃.store
      ⟨hc, rl.nfields, rl.ctorParams, hf, hr, rl.k, rl.eta, rl.paramsBlind⟩
      = some rl := by
    simp only [denoteRule, denoteN_ext hdc (hstep2.ext.trans hstep3.ext),
      denoteFire_ext hdf hstep3.ext, hdr]
  obtain ⟨hv, hst⟩ := AM.pure_ok hrest3
  subst hst
  simp only [Prod.mk.injEq] at hv
  obtain ⟨hmm, hii⟩ := hv
  subst hmm; subst hii
  exact ⟨(hstep1.trans hstep2).trans hstep3, hd, hm3⟩

theorem internRules_sstep : ∀ (rs : List RecRule) {s s' : AState}
    {m m' : EMemo} {ris : List IRecRule}, StateOK s →
    EMemoOK s.store m →
    internRules m rs s = .ok ((m', ris), s') →
    IStepS s s' ∧ denoteRules s'.store ris = some rs ∧
      EMemoOK s'.store m' := by
  intro rs
  induction rs with
  | nil =>
    intro s s' m m' ris hok hm hrun
    rw [ConRon.Arena.Frontend.internRules] at hrun
    obtain ⟨hv, hst⟩ := AM.pure_ok hrun
    subst hst
    simp only [Prod.mk.injEq] at hv
    obtain ⟨hmm, hii⟩ := hv
    subst hmm; subst hii
    exact ⟨IStepS.refl hok, rfl, hm⟩
  | cons r rs ih =>
    intro s s' m m' ris hok hm hrun
    rw [ConRon.Arena.Frontend.internRules] at hrun
    obtain ⟨p1, s₁, h1, hrest⟩ := AM.bind_ok hrun
    obtain ⟨m1, x1⟩ := p1
    obtain ⟨hstep1, hdr, hm1⟩ := internRule_sstep hok hm h1
    simp only [] at hrest
    obtain ⟨p2, s₂, h2, hrest2⟩ := AM.bind_ok hrest
    obtain ⟨m2, xs⟩ := p2
    obtain ⟨hstep2, hdrs, hm2⟩ := ih hstep1.ok hm1 h2
    simp only [] at hrest2
    have hd : denoteRules s₂.store (x1 :: xs) = some (r :: rs) := by
      simp only [denoteRules, denoteRule_ext hdr hstep2.ext, hdrs]
    obtain ⟨hv, hst⟩ := AM.pure_ok hrest2
    subst hst
    simp only [Prod.mk.injEq] at hv
    obtain ⟨hmm, hii⟩ := hv
    subst hmm; subst hii
    exact ⟨hstep1.trans hstep2, hd, hm2⟩

theorem internCaps_sstep {s s' : AState} (hok : StateOK s)
    {c : IndCaps} {ci : IIndCaps}
    (hrun : internCaps c s = .ok (ci, s')) :
    IStepS s s' ∧ denoteCaps s'.store ci = some c := by
  rw [ConRon.Arena.Frontend.internCaps] at hrun
  obtain ⟨ct, s₁, h1, hrest⟩ := AM.bind_ok hrun
  obtain ⟨hstep1, hdc⟩ := internName_sstep hok h1
  obtain ⟨all, s₂, h2, hrest2⟩ := AM.bind_ok hrest
  obtain ⟨hstep2, hda⟩ := internNameList_sstep c.all hstep1.ok h2
  obtain ⟨ctors, s₃, h3, hrest3⟩ := AM.bind_ok hrest2
  obtain ⟨hstep3, hdct⟩ := internNameList_sstep c.ctors hstep2.ok h3
  obtain ⟨hv, hst⟩ := AM.pure_ok hrest3
  subst hst; subst hv
  refine ⟨(hstep1.trans hstep2).trans hstep3, ?_⟩
  simp only [denoteCaps, denoteN_ext hdc (hstep2.ext.trans hstep3.ext),
    denoteNListE_ext hstep3.ext _ _ hda, hdct]

theorem internProjTable_sstep {s s' : AState} (hok : StateOK s)
    {m m' : EMemo} (hm : EMemoOK s.store m)
    {t : ProjTable} {ti : IProjTable}
    (hrun : internProjTable m t s = .ok ((m', ti), s')) :
    IStepS s s' ∧ denoteProjTable s'.store ti = some t ∧
      EMemoOK s'.store m' ∧ IProjNamed s'.store ti := by
  rw [ConRon.Arena.Frontend.internProjTable] at hrun
  obtain ⟨sn, s₁, h1, hrest⟩ := AM.bind_ok hrun
  obtain ⟨hstep1, hdsn⟩ := internName_sstep hok h1
  obtain ⟨tn, s₂, h2, hrest2⟩ := AM.bind_ok hrest
  obtain ⟨hstep2, hdtn⟩ := projTableName_sstep hstep1.ok hdsn h2
  obtain ⟨lps, s₃, h3, hrest3⟩ := AM.bind_ok hrest2
  obtain ⟨hstep3, hdlps⟩ :=
    internNameList_sstep t.levelParams hstep2.ok h3
  obtain ⟨cn, s₄, h4, hrest4⟩ := AM.bind_ok hrest3
  obtain ⟨hstep4, hdcn⟩ := internName_sstep hstep3.ok h4
  obtain ⟨ss, s₅, h5, hrest5⟩ := AM.bind_ok hrest4
  obtain ⟨hstep5, hdss⟩ := internLevel_sstep hstep4.ok h5
  obtain ⟨p6, s₆, h6, hrest6⟩ := AM.bind_ok hrest5
  obtain ⟨m6, bs⟩ := p6
  obtain ⟨hstep6, hdbs, hm6⟩ :=
    internExprList_sstep t.bodies.toList hstep5.ok
      (hm.mono ((((hstep1.ext.trans hstep2.ext).trans hstep3.ext).trans
        hstep4.ext).trans hstep5.ext)) h6
  simp only [] at hrest6
  obtain ⟨gs, s₇, h7, hrest7⟩ := AM.bind_ok hrest6
  obtain ⟨hstep7, hdgs⟩ :=
    internLevelList_sstep t.guards hstep6.ok h7
  have hxs : Ext s₃.store s₇.store :=
    ((hstep4.ext.trans hstep5.ext).trans hstep6.ext).trans hstep7.ext
  have hd : denoteProjTable s₇.store
      ⟨sn, tn, lps, t.numParams, cn, t.numFields, ss, bs.toArray, gs, t.off⟩
      = some t := by
    simp only [denoteProjTable,
      denoteN_ext hdsn ((hstep2.ext.trans hstep3.ext).trans hxs),
      denoteNListE_ext hxs _ _ hdlps,
      denoteN_ext hdcn ((hstep5.ext.trans hstep6.ext).trans hstep7.ext),
      denoteL_ext hdss (hstep6.ext.trans hstep7.ext),
      denoteEArray, denoteEList_ext hstep7.ext _ _ hdbs, hdgs]
  obtain ⟨hv, hst⟩ := AM.pure_ok hrest7
  subst hst
  simp only [Prod.mk.injEq] at hv
  obtain ⟨hmm, hii⟩ := hv
  subst hmm; subst hii
  exact ⟨((((((hstep1.trans hstep2).trans hstep3).trans hstep4).trans
      hstep5).trans hstep6).trans hstep7),
    hd, hm6.mono hstep7.ext,
    ⟨t.structName,
      denoteN_ext hdsn ((hstep2.ext.trans hstep3.ext).trans hxs),
      denoteN_ext hdtn (hstep3.ext.trans hxs)⟩⟩


theorem internCI_sstep {s s' : AState} (hok : StateOK s)
    {m m' : EMemo} (hm : EMemoOK s.store m)
    {c : ConstantInfo} {ci : IConstantInfo}
    (hrun : internCI m c s = .ok ((m', ci), s')) :
    IStepS s s' ∧ denoteCI s'.store ci = some c ∧
      EMemoOK s'.store m' ∧ CIProjNamed s'.store ci := by
  cases c with
  | axiomInfo v =>
    rw [ConRon.Arena.Frontend.internCI] at hrun
    obtain ⟨p1, s₁, h1, hrest⟩ := AM.bind_ok hrun
    obtain ⟨m1, cv⟩ := p1
    obtain ⟨hstep1, hdcv, hm1⟩ := internCV_sstep hok hm h1
    simp only [] at hrest
    obtain ⟨hv, hst⟩ := AM.pure_ok hrest
    subst hst
    simp only [Prod.mk.injEq] at hv
    obtain ⟨hmm, hii⟩ := hv
    subst hmm; subst hii
    exact ⟨hstep1, by simp only [denoteCI, hdcv, Option.map_some], hm1,
      CIProjNamed.of_ne (by simp)⟩
  | ctorInfo v nP nF =>
    rw [ConRon.Arena.Frontend.internCI] at hrun
    obtain ⟨p1, s₁, h1, hrest⟩ := AM.bind_ok hrun
    obtain ⟨m1, cv⟩ := p1
    obtain ⟨hstep1, hdcv, hm1⟩ := internCV_sstep hok hm h1
    simp only [] at hrest
    obtain ⟨hv, hst⟩ := AM.pure_ok hrest
    subst hst
    simp only [Prod.mk.injEq] at hv
    obtain ⟨hmm, hii⟩ := hv
    subst hmm; subst hii
    exact ⟨hstep1, by simp only [denoteCI, hdcv, Option.map_some], hm1,
      CIProjNamed.of_ne (by simp)⟩
  | defnInfo v e hh =>
    rw [ConRon.Arena.Frontend.internCI] at hrun
    obtain ⟨p1, s₁, h1, hrest⟩ := AM.bind_ok hrun
    obtain ⟨m1, cv⟩ := p1
    obtain ⟨hstep1, hdcv, hm1⟩ := internCV_sstep hok hm h1
    simp only [] at hrest
    obtain ⟨p2, s₂, h2, hrest2⟩ := AM.bind_ok hrest
    obtain ⟨m2, x⟩ := p2
    obtain ⟨hstep2, hdx, hm2⟩ :=
      internExprGo_sstep e hstep1.ok hm1 h2
    simp only [] at hrest2
    have hd : denoteCI s₂.store (.defnInfo cv x hh) = some (.defnInfo v e hh) := by
      simp only [denoteCI, denoteCV_ext hdcv hstep2.ext, hdx]
    obtain ⟨hv, hst⟩ := AM.pure_ok hrest2
    subst hst
    simp only [Prod.mk.injEq] at hv
    obtain ⟨hmm, hii⟩ := hv
    subst hmm; subst hii
    exact ⟨hstep1.trans hstep2, hd, hm2,
      CIProjNamed.of_ne (by simp)⟩
  | thmInfo v e =>
    rw [ConRon.Arena.Frontend.internCI] at hrun
    obtain ⟨p1, s₁, h1, hrest⟩ := AM.bind_ok hrun
    obtain ⟨m1, cv⟩ := p1
    obtain ⟨hstep1, hdcv, hm1⟩ := internCV_sstep hok hm h1
    simp only [] at hrest
    obtain ⟨p2, s₂, h2, hrest2⟩ := AM.bind_ok hrest
    obtain ⟨m2, x⟩ := p2
    obtain ⟨hstep2, hdx, hm2⟩ :=
      internExprGo_sstep e hstep1.ok hm1 h2
    simp only [] at hrest2
    have hd : denoteCI s₂.store (.thmInfo cv x) = some (.thmInfo v e) := by
      simp only [denoteCI, denoteCV_ext hdcv hstep2.ext, hdx]
    obtain ⟨hv, hst⟩ := AM.pure_ok hrest2
    subst hst
    simp only [Prod.mk.injEq] at hv
    obtain ⟨hmm, hii⟩ := hv
    subst hmm; subst hii
    exact ⟨hstep1.trans hstep2, hd, hm2,
      CIProjNamed.of_ne (by simp)⟩
  | indInfo v cps =>
    rw [ConRon.Arena.Frontend.internCI] at hrun
    obtain ⟨p1, s₁, h1, hrest⟩ := AM.bind_ok hrun
    obtain ⟨m1, cv⟩ := p1
    obtain ⟨hstep1, hdcv, hm1⟩ := internCV_sstep hok hm h1
    simp only [] at hrest
    obtain ⟨caps, s₂, h2, hrest2⟩ := AM.bind_ok hrest
    obtain ⟨hstep2, hdcaps⟩ :=
      internCaps_sstep hstep1.ok h2
    have hd : denoteCI s₂.store (.indInfo cv caps) = some (.indInfo v cps) := by
      simp only [denoteCI, denoteCV_ext hdcv hstep2.ext, hdcaps]
    obtain ⟨hv, hst⟩ := AM.pure_ok hrest2
    subst hst
    simp only [Prod.mk.injEq] at hv
    obtain ⟨hmm, hii⟩ := hv
    subst hmm; subst hii
    exact ⟨hstep1.trans hstep2, hd, hm1.mono hstep2.ext,
      CIProjNamed.of_ne (by simp)⟩
  | recInfo v mI rP rs =>
    rw [ConRon.Arena.Frontend.internCI] at hrun
    obtain ⟨p1, s₁, h1, hrest⟩ := AM.bind_ok hrun
    obtain ⟨m1, cv⟩ := p1
    obtain ⟨hstep1, hdcv, hm1⟩ := internCV_sstep hok hm h1
    simp only [] at hrest
    obtain ⟨p2, s₂, h2, hrest2⟩ := AM.bind_ok hrest
    obtain ⟨m2, rules⟩ := p2
    obtain ⟨hstep2, hdrs, hm2⟩ :=
      internRules_sstep rs hstep1.ok hm1 h2
    simp only [] at hrest2
    have hd : denoteCI s₂.store (.recInfo cv mI rP rules)
        = some (.recInfo v mI rP rs) := by
      simp only [denoteCI, denoteCV_ext hdcv hstep2.ext, hdrs]
    obtain ⟨hv, hst⟩ := AM.pure_ok hrest2
    subst hst
    simp only [Prod.mk.injEq] at hv
    obtain ⟨hmm, hii⟩ := hv
    subst hmm; subst hii
    exact ⟨hstep1.trans hstep2, hd, hm2,
      CIProjNamed.of_ne (by simp)⟩
  | projInfo t =>
    rw [ConRon.Arena.Frontend.internCI] at hrun
    obtain ⟨p1, s₁, h1, hrest⟩ := AM.bind_ok hrun
    obtain ⟨m1, tbl⟩ := p1
    obtain ⟨hstep1, hdt, hm1, hnt⟩ := internProjTable_sstep hok hm h1
    simp only [] at hrest
    obtain ⟨hv, hst⟩ := AM.pure_ok hrest
    subst hst
    simp only [Prod.mk.injEq] at hv
    obtain ⟨hmm, hii⟩ := hv
    subst hmm; subst hii
    exact ⟨hstep1, by simp only [denoteCI, hdt, Option.map_some], hm1,
      CIProjNamed.of_proj hnt⟩

theorem internCIList_sstep : ∀ (cs : List ConstantInfo) {s s' : AState}
    {m m' : EMemo} {cis : List IConstantInfo}, StateOK s →
    EMemoOK s.store m →
    internCIList m cs s = .ok ((m', cis), s') →
    IStepS s s' ∧ denoteCIList s'.store cis = some cs ∧
      EMemoOK s'.store m' ∧ (∀ ci ∈ cis, CIProjNamed s'.store ci) := by
  intro cs
  induction cs with
  | nil =>
    intro s s' m m' cis hok hm hrun
    rw [ConRon.Arena.Frontend.internCIList] at hrun
    obtain ⟨hv, hst⟩ := AM.pure_ok hrun
    subst hst
    simp only [Prod.mk.injEq] at hv
    obtain ⟨hmm, hii⟩ := hv
    subst hmm; subst hii
    exact ⟨IStepS.refl hok, rfl, hm,
      by intro x hx; simp at hx⟩
  | cons c cs ih =>
    intro s s' m m' cis hok hm hrun
    rw [ConRon.Arena.Frontend.internCIList] at hrun
    obtain ⟨p1, s₁, h1, hrest⟩ := AM.bind_ok hrun
    obtain ⟨m1, x1⟩ := p1
    obtain ⟨hstep1, hdc, hm1, hnc⟩ := internCI_sstep hok hm h1
    simp only [] at hrest
    obtain ⟨p2, s₂, h2, hrest2⟩ := AM.bind_ok hrest
    obtain ⟨m2, xs⟩ := p2
    obtain ⟨hstep2, hdcs, hm2, hncs⟩ := ih hstep1.ok hm1 h2
    simp only [] at hrest2
    have hd : denoteCIList s₂.store (x1 :: xs) = some (c :: cs) := by
      simp only [denoteCIList, denoteCI_ext hdc hstep2.ext, hdcs]
    obtain ⟨hv, hst⟩ := AM.pure_ok hrest2
    subst hst
    simp only [Prod.mk.injEq] at hv
    obtain ⟨hmm, hii⟩ := hv
    subst hmm; subst hii
    refine ⟨hstep1.trans hstep2, hd, hm2, ?_⟩
    intro x hx
    simp only [List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact hnc.mono hstep2.ext
    · exact hncs x hx

/-! ## The same twenty-two, with the scratch tier CLOSED

The `IStep` face of the family above, and the shape every caller of this module
had before round 6.  Seventeen of them are three lines — `IStepS.toIStep` for
the frame, `Bridge/Frontend/Rel.lean`'s `Pers…_of_denote` for the persistence
conjunct, the denotation carried across unchanged — because **persistence is a
consequence of the denotation** at a state whose scratch tier is closed.

The five that are not are the VIEW leaves.  Their conclusion is a
`denoteEView` / `denoteNView` / `denoteLView` equation rather than a `some`,
and a handle known only to denote whatever some view denotes is not yet known
to denote at all; so those five read the spec's `view` conjunct directly
through `Pers…_of_view`, exactly as they did before.  DESIGN #97-P3-Frontend
round 6. -/

/-- con-leche: none — `internE`, with the scratch tier closed: a view leaf. -/
theorem internE_istep {s s' : AState} (hok : StateOK s)
    (hoff : s.store.scratchOn = false) {v : ENodeView} (hv : s.store.ViewOK v)
    {h : EIdx} (hrun : internE v s = .ok (h, s')) :
    IStep s s' ∧ PersE h ∧ denoteE s'.store h = denoteEView s'.store v := by
  obtain ⟨hwf, hx, -, -, -, hm, hc, hp, hview, hden⟩ :=
    AM.of_run (P := fun t => t = s) rfl hrun (internE_spec s v hok.wf hv)
  have hon : s'.store.scratchOn = false := by
    rw [internE_scratchOn hrun]; exact hoff
  exact ⟨⟨⟨hwf⟩, hx, hon, hm, hc, hp⟩, PersE_of_view hwf hon hview, hden⟩

/-- con-leche: none — a NAME node: a view leaf. -/
theorem internNNode_istep {s s' : AState} (hok : StateOK s)
    (hoff : s.store.scratchOn = false) {v : NNodeView}
    (hv : s.store.ns.ViewOK v) {h : NIdx}
    (hrun : internNNode v s = .ok (h, s')) :
    IStep s s' ∧ PersN h ∧
      denoteN s'.store.ns h = denoteNView s'.store.ns v := by
  obtain ⟨hwf, hx, -, -, hon, hm, hc, hp, hview, hden⟩ :=
    AM.of_run (P := fun t => t = s) rfl hrun (internNNode_spec s v hok.wf hv)
  have hon' : s'.store.scratchOn = false := by rw [hon]; exact hoff
  exact ⟨⟨⟨hwf⟩, hx, hon', hm, hc, hp⟩, PersN_of_view hwf hon' hview, hden⟩

/-- con-leche: ConLeche/Kernel/Expr.lean Level — a LEVEL node: a view leaf. -/
theorem internLNode_istep {s s' : AState} (hok : StateOK s)
    (hoff : s.store.scratchOn = false) {v : LNodeView}
    (hv : s.store.ls.ViewOK v) {h : LIdx}
    (hrun : ConRon.Arena.internLNode v s = .ok (h, s')) :
    IStep s s' ∧ PersL h ∧
      denoteL s'.store.ls h = denoteLView s'.store.ls v := by
  obtain ⟨hwf, hx, -, -, hon, hm, hc, hp, hview, hden⟩ :=
    AM.of_run (P := fun t => t = s) rfl hrun (internLNode_spec s v hok.wf hv)
  have hon' : s'.store.scratchOn = false := by rw [hon]; exact hoff
  exact ⟨⟨⟨hwf⟩, hx, hon', hm, hc, hp⟩, PersL_of_view hwf hon' hview, hden⟩

/-- con-leche: none — a LEVEL-LIST node; no persistence conjunct. -/
theorem internLsNode_istep {s s' : AState} (hok : StateOK s)
    (hoff : s.store.scratchOn = false) {v : LsNodeView}
    (hv : s.store.lss.ViewOK v) {h : LsIdx}
    (hrun : ConRon.Arena.internLsNode v s = .ok (h, s')) :
    IStep s s' ∧ denoteLs s'.store.lss h = denoteLsView s'.store.lss v := by
  obtain ⟨hst, hd⟩ := internLsNode_sstep hok hv hrun
  exact ⟨hst.toIStep hoff, hd⟩

/-- con-leche: none — the same at a fresh memo and with no flag: what a caller
INSIDE the per-declaration scratch bracket can use.  `internExprGo_sstep` at
`∅`. -/
theorem internExpr_sstep {s s' : AState} (hok : StateOK s) {e : Expr}
    {h : EIdx} (hrun : ConRon.Arena.Frontend.internExpr e s = .ok (h, s')) :
    IStepS s s' ∧ denoteE s'.store h = some e := by
  rw [ConRon.Arena.Frontend.internExpr] at hrun
  obtain ⟨p, s₁, hgo, hrest⟩ := AM.bind_ok hrun
  obtain ⟨m1, hh⟩ := p
  obtain ⟨hv, hst⟩ := AM.pure_ok hrest
  subst hst; subst hv
  obtain ⟨hstep, hden, -⟩ :=
    internExprGo_sstep e hok (EMemoOK.empty s.store) hgo
  exact ⟨hstep, hden⟩

/-! ### The readback's existence direction, at the record layers

`denoteEGo_isSome` is the leaf; each layer above it is the same three lines
(destructure the plain denotation, apply the layer below, rebuild). -/

end ConRon.Bridge.Frontend
