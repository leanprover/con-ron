/-
# `ConRon.Bridge.Promote.Walk` — the four handle-kind promotions, run forwards

Each walk is proved in ONE form, the core:

    PSrc src s.store → PMemoPi m src s.store → promoteX m fuel h s = .ok ((m', r), s') →
      PSrc src s'.store ∧ PMemoPi m' src s'.store ∧
        Ext s.store.dropScratch s'.store.dropScratch ∧ PersX r ∧
        Kept (denoteX src h) (denoteX s'.store.dropScratch r)

The source's denotation is an implication: nothing says the subject denotes in the
source, or at all.  What the walk reads it reads from the store, whose scratch tier may
be junk; what it builds it builds in the persistent tier, out of children it has already
promoted, so the node denotes in the projection whatever the subject was.  If the
subject does denote in the source then the source read the node the store read
(`PSrc.srcE`), so the two denotations are the same node's.

A persistent leaf is decoded, so it denotes in the projection by that projection's
well-formedness (`PSrc.leafE`).

The run's frame is not re-proved: `Arena/PromoteExt.lean`'s `AExtOf` gives it for every
run, unconditionally.
-/
module

public import ConRon.Bridge.Promote.Proj
import ConRon.Bridge.Promote.Weak
import ConRon.Bridge.Rel
import ConRon.Arena.PersistentRun

public section

namespace ConRon.Bridge

set_option autoImplicit false

open ConLeche ConRon.Arena

variable {src : EStore}

/-! ## The readers, as run equations -/

theorem viewN_ok {h : NIdx} {s s' : AState} {v : NNodeView}
    (hr : viewN h s = .ok (v, s')) : s' = s ∧ s.store.ns.view h = some v := by
  cases hv : s.store.ns.view h with
  | some w =>
    simp only [viewN, bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get,
      pure, StateT.pure, Except.bind, Except.pure, hv, Except.ok.injEq,
      Prod.mk.injEq] at hr
    obtain ⟨rfl, rfl⟩ := hr
    exact ⟨rfl, rfl⟩
  | none =>
    simp only [viewN, bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get,
      pure, Except.bind, Except.pure, hv, ConRon.Bridge.fail_apply] at hr
    exact absurd hr (by simp)

theorem viewL_ok {h : LIdx} {s s' : AState} {v : LNodeView}
    (hr : viewL h s = .ok (v, s')) : s' = s ∧ s.store.ls.view h = some v := by
  cases hv : s.store.ls.view h with
  | some w =>
    simp only [viewL, bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get,
      pure, StateT.pure, Except.bind, Except.pure, hv, Except.ok.injEq,
      Prod.mk.injEq] at hr
    obtain ⟨rfl, rfl⟩ := hr
    exact ⟨rfl, rfl⟩
  | none =>
    simp only [viewL, bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get,
      pure, Except.bind, Except.pure, hv, ConRon.Bridge.fail_apply] at hr
    exact absurd hr (by simp)

theorem viewLs_ok {h : LsIdx} {s s' : AState} {v : LsNodeView}
    (hr : viewLs h s = .ok (v, s')) : s' = s ∧ s.store.lss.view h = some v := by
  cases hv : s.store.lss.view h with
  | some w =>
    simp only [viewLs, bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get,
      pure, StateT.pure, Except.bind, Except.pure, hv, Except.ok.injEq,
      Prod.mk.injEq] at hr
    obtain ⟨rfl, rfl⟩ := hr
    exact ⟨rfl, rfl⟩
  | none =>
    simp only [viewLs, bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get,
      pure, Except.bind, Except.pure, hv, ConRon.Bridge.fail_apply] at hr
    exact absurd hr (by simp)

theorem view_ok {h : EIdx} {s s' : AState} {v : ENodeView}
    (hr : view h s = .ok (v, s')) : s' = s ∧ s.store.view h = some v := by
  cases hv : s.store.view h with
  | some w =>
    simp only [view, bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get,
      pure, StateT.pure, Except.bind, Except.pure, hv, Except.ok.injEq,
      Prod.mk.injEq] at hr
    obtain ⟨rfl, rfl⟩ := hr
    exact ⟨rfl, rfl⟩
  | none =>
    simp only [view, bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get,
      pure, Except.bind, Except.pure, hv, ConRon.Bridge.fail_apply] at hr
    exact absurd hr (by simp)

/-! ## `promoteN` -/

theorem denoteNView_ext {st st' : NStore} {w : NNodeView} {x : ConLeche.Name}
    (hd : denoteNView st w = some x) (hx : NExt st st') : denoteNView st' w = some x := by
  cases w with
  | anonymous => exact hd
  | str p t =>
    simp only [denoteNView, Option.map_eq_some_iff] at hd ⊢
    obtain ⟨q, hq, he⟩ := hd
    exact ⟨q, hx _ _ hq, he⟩
  | num p k =>
    simp only [denoteNView, Option.map_eq_some_iff] at hd ⊢
    obtain ⟨q, hq, he⟩ := hd
    exact ⟨q, hx _ _ hq, he⟩

theorem NStore.ViewOK.of_denoteNView {st : NStore} {w : NNodeView} {x : ConLeche.Name}
    (hd : denoteNView st w = some x) : st.ViewOK w := by
  intro c hc
  cases w with
  | anonymous => simp [NNodeView.children] at hc
  | str p t =>
    simp only [NNodeView.children, List.mem_singleton] at hc; subst hc
    simp only [denoteNView, Option.map_eq_some_iff] at hd
    obtain ⟨q, hq, -⟩ := hd
    obtain ⟨v, hv⟩ := denoteN_view hq
    rw [hv]; rfl
  | num p k =>
    simp only [NNodeView.children, List.mem_singleton] at hc; subst hc
    simp only [denoteNView, Option.map_eq_some_iff] at hd
    obtain ⟨q, hq, -⟩ := hd
    obtain ⟨v, hv⟩ := denoteN_view hq
    rw [hv]; rfl

/-- con-leche: none — arena infrastructure; a name node the promotion builds denotes
what its view denotes in the projection. -/
theorem promoteN_node {s s' : AState} {w : NNodeView} {r : NIdx} {d : Option ConLeche.Name}
    (hs : PSrc src s.store) (hd : Kept d (denoteNView s.store.dropScratch.ns w))
    (hp : NViewPers w) (hrun : internPersistentN w s = .ok (r, s')) :
    PSrc src s'.store ∧ Ext s.store.dropScratch s'.store.dropScratch ∧ PersN r ∧
      Kept d (denoteN s'.store.dropScratch.ns r) := by
  obtain ⟨y, hy⟩ := hd.1
  obtain ⟨hwf', hx, hsc, hview, hpers⟩ :=
    internPersistentN_pi hs.piWF (NStore.ViewOK.of_denoteNView hy) hp hrun
  obtain ⟨rk, hw⟩ := (StoreWF'.of_wf hwf').nsWF
  refine ⟨hs.step hwf' hx hsc, hx, hpers, hd.post fun y' hy' => ?_⟩
  rw [denoteN_unfold' hw hview]
  exact denoteNView_ext hy' hx.lss.ls.ns

/-- con-leche: none — arena infrastructure; **the name promotion, run
forwards**: the invariant and the memo survive, the answer is persistent, and
it keeps the subject's denotation. -/
theorem promoteN_core : ∀ (fuel : Nat) (m : PMemo) (h : NIdx) (s : AState)
    (m' : PMemo) (r : NIdx) (s' : AState),
    PSrc src s.store → PMemoPi m src s.store →
    promoteN m fuel h s = .ok ((m', r), s') →
    PSrc src s'.store ∧ PMemoPi m' src s'.store ∧
      Ext s.store.dropScratch s'.store.dropScratch ∧ PersN r ∧
      Kept (denoteN src.ns h) (denoteN s'.store.dropScratch.ns r) := by
  intro fuel
  induction fuel with
  | zero =>
    intro m h s m' r s' _ _ hrun
    simp only [promoteN, ConRon.Bridge.fail_apply] at hrun
    exact absurd hrun (by simp)
  | succ fuel ih =>
    intro m h s m' r s' hs hm hrun
    unfold promoteN at hrun
    rcases AM.ite_ok hrun with ⟨hp, hrun⟩ | ⟨hp, hrun⟩
    · obtain ⟨v, s1, hv, h1⟩ := AM.bind_ok hrun
      obtain ⟨rfl, hview⟩ := viewN_ok hv
      obtain ⟨hr, rfl⟩ := AM.pure_ok h1
      simp only [Prod.mk.injEq] at hr
      obtain ⟨rfl, rfl⟩ := hr
      exact ⟨hs, hm, Ext.refl _, hp, hs.leafN hp hview⟩
    · cases hmemo : m.nM[h]? with
      | some r0 =>
        simp only [hmemo] at hrun
        obtain ⟨hr, rfl⟩ := AM.pure_ok hrun
        simp only [Prod.mk.injEq] at hr
        obtain ⟨rfl, rfl⟩ := hr
        obtain ⟨hpr, hk⟩ := hm.nM h _ hmemo
        exact ⟨hs, hm, Ext.refl _, hpr, hk⟩
      | none =>
        simp only [hmemo] at hrun
        obtain ⟨v, s1, hv, h1⟩ := AM.bind_ok hrun
        obtain ⟨rfl, hview⟩ := viewN_ok hv
        have hsrc := hs.srcN (by simpa using hp) hview
        -- every arm ends the same way: the node rebuilt at `(m1, r1)` in
        -- `s2`, recorded in the memo
        have fin : ∀ (m1 : PMemo) (r1 : NIdx) (s2 : AState),
            PSrc src s2.store → PMemoPi m1 src s2.store →
            Ext s1.store.dropScratch s2.store.dropScratch →
            PersN r1 → Kept (denoteNView src.ns v) (denoteN s2.store.dropScratch.ns r1) →
            (m', r) = ({ m1 with nM := m1.nM.insert h r1 }, r1) → s' = s2 →
            PSrc src s'.store ∧ PMemoPi m' src s'.store ∧
              Ext s1.store.dropScratch s'.store.dropScratch ∧ PersN r ∧
              Kept (denoteN src.ns h) (denoteN s'.store.dropScratch.ns r) := by
          intro m1 r1 s2 hs2 hm2 hx2 hp2 hd2 hr hs'
          simp only [Prod.mk.injEq] at hr
          obtain ⟨rfl, rfl⟩ := hr
          subst hs'
          have hk := hd2.pre hsrc
          exact ⟨hs2, hm2.insertN hp2 hk, hx2, hp2, hk⟩
        cases v with
        | anonymous =>
          obtain ⟨r2, s3, h3, h4⟩ := AM.bind_ok h1
          obtain ⟨hr, rfl⟩ := AM.pure_ok (AM.pure_bind_ok h4)
          obtain ⟨hs3, hx3, hp3, hd3⟩ := promoteN_node hs (w := .anonymous) (Kept.some _)
            (by intro c hc; simp [NNodeView.children] at hc) h3
          exact fin m r2 _ hs3 (hm.mono hx3) hx3 hp3 hd3 hr rfl
        | str p t =>
          obtain ⟨⟨m2, p2⟩, s3, h3, h4⟩ := AM.bind_ok h1
          obtain ⟨hs3, hm3, hx13, hpp, hkp⟩ := ih m p s1 m2 p2 s3 hs hm h3
          obtain ⟨r2, s4, h5, h6⟩ := AM.bind_ok h4
          obtain ⟨hr, rfl⟩ := AM.pure_ok (AM.pure_bind_ok h6)
          obtain ⟨hs4, hx4, hp4, hd4⟩ := promoteN_node hs3
            (w := .str p2 t) (Kept.map (fun q => Name.str q t) hkp)
            (by intro c hc; simp only [NNodeView.children, List.mem_singleton] at hc
                subst hc; exact hpp) h5
          exact fin m2 r2 _ hs4 (hm3.mono hx4) (hx13.trans hx4) hp4 hd4 hr rfl
        | num p k =>
          obtain ⟨⟨m2, p2⟩, s3, h3, h4⟩ := AM.bind_ok h1
          obtain ⟨hs3, hm3, hx13, hpp, hkp⟩ := ih m p s1 m2 p2 s3 hs hm h3
          obtain ⟨r2, s4, h5, h6⟩ := AM.bind_ok h4
          obtain ⟨hr, rfl⟩ := AM.pure_ok (AM.pure_bind_ok h6)
          obtain ⟨hs4, hx4, hp4, hd4⟩ := promoteN_node hs3
            (w := .num p2 k) (Kept.map (fun q => Name.num q k) hkp)
            (by intro c hc; simp only [NNodeView.children, List.mem_singleton] at hc
                subst hc; exact hpp) h5
          exact fin m2 r2 _ hs4 (hm3.mono hx4) (hx13.trans hx4) hp4 hd4 hr rfl

/-- con-leche: none — arena infrastructure; `promoteN_core` in the shape the walks
above it call. -/
theorem promoteN_step {m m' : PMemo} {fuel : Nat} {h r : NIdx} {s s' : AState}
    (hs : PSrc src s.store) (hm : PMemoPi m src s.store)
    (hrun : promoteN m fuel h s = .ok ((m', r), s')) :
    PSrc src s'.store ∧ PMemoPi m' src s'.store ∧
      Ext s.store.dropScratch s'.store.dropScratch ∧ PersN r ∧
      Kept (denoteN src.ns h) (denoteN s'.store.dropScratch.ns r) :=
  promoteN_core fuel m h s m' r s' hs hm hrun

/-! ## `promoteL` -/

theorem LStore.ViewOK.of_denoteLView {st : LStore} {w : LNodeView} {u : Level}
    (hd : denoteLView st w = some u) : st.ViewOK w := by
  have hL : ∀ {c : LIdx} {a : Level}, denoteL st c = some a → (st.view c).isSome = true := by
    intro c a hc; obtain ⟨v, hv⟩ := denoteL_view hc; rw [hv]; rfl
  cases w with
  | zero => exact ⟨by simp [LNodeView.lchildren], by simp [LNodeView.nchildren]⟩
  | succ a =>
    simp only [denoteLView, Option.map_eq_some_iff] at hd
    obtain ⟨q, hq, -⟩ := hd
    refine ⟨?_, by simp [LNodeView.nchildren]⟩
    intro c hc
    simp only [LNodeView.lchildren, List.mem_singleton] at hc
    subst hc; exact hL hq
  | max a b =>
    simp only [denoteLView, opt2_eq_some_iff] at hd
    obtain ⟨p, q, hp, hq, -⟩ := hd
    refine ⟨?_, by simp [LNodeView.nchildren]⟩
    intro c hc
    simp only [LNodeView.lchildren, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · exact hL hp
    · exact hL hq
  | imax a b =>
    simp only [denoteLView, opt2_eq_some_iff] at hd
    obtain ⟨p, q, hp, hq, -⟩ := hd
    refine ⟨?_, by simp [LNodeView.nchildren]⟩
    intro c hc
    simp only [LNodeView.lchildren, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · exact hL hp
    · exact hL hq
  | param n =>
    simp only [denoteLView, Option.map_eq_some_iff] at hd
    obtain ⟨q, hq, -⟩ := hd
    refine ⟨by simp [LNodeView.lchildren], ?_⟩
    intro c hc
    simp only [LNodeView.nchildren, List.mem_singleton] at hc; subst hc
    obtain ⟨v, hv⟩ := denoteN_view hq; rw [hv]; rfl

theorem denoteLView_ext {st st' : LStore} {w : LNodeView} {u : Level}
    (hd : denoteLView st w = some u) (hx : LExt st st') : denoteLView st' w = some u := by
  cases w with
  | zero => exact hd
  | succ a =>
    simp only [denoteLView, Option.map_eq_some_iff] at hd ⊢
    obtain ⟨q, hq, he⟩ := hd
    exact ⟨q, hx.lvl _ _ hq, he⟩
  | max a b =>
    simp only [denoteLView, opt2_eq_some_iff] at hd ⊢
    obtain ⟨p, q, hp, hq, he⟩ := hd
    exact ⟨p, q, hx.lvl _ _ hp, hx.lvl _ _ hq, he⟩
  | imax a b =>
    simp only [denoteLView, opt2_eq_some_iff] at hd ⊢
    obtain ⟨p, q, hp, hq, he⟩ := hd
    exact ⟨p, q, hx.lvl _ _ hp, hx.lvl _ _ hq, he⟩
  | param n =>
    simp only [denoteLView, Option.map_eq_some_iff] at hd ⊢
    obtain ⟨q, hq, he⟩ := hd
    exact ⟨q, hx.ns _ _ hq, he⟩

/-- con-leche: none — arena infrastructure; a level node the promotion builds denotes
what its view denotes in the projection. -/
theorem promoteL_node {s s' : AState} {w : LNodeView} {r : LIdx} {d : Option Level}
    (hs : PSrc src s.store) (hd : Kept d (denoteLView s.store.dropScratch.ls w))
    (hp : LViewPers w) (hrun : internPersistentL w s = .ok (r, s')) :
    PSrc src s'.store ∧ Ext s.store.dropScratch s'.store.dropScratch ∧ PersL r ∧
      Kept d (denoteL s'.store.dropScratch.ls r) := by
  obtain ⟨y, hy⟩ := hd.1
  obtain ⟨hwf', hx, hsc, hview, hpers⟩ :=
    internPersistentL_pi hs.piWF (LStore.ViewOK.of_denoteLView hy) hp hrun
  obtain ⟨rk, hw⟩ := (StoreWF'.of_wf hwf').lsWF
  refine ⟨hs.step hwf' hx hsc, hx, hpers, hd.post fun y' hy' => ?_⟩
  rw [denoteL_unfold' hw hview]
  exact denoteLView_ext hy' hx.lss.ls

/-- con-leche: none — arena infrastructure; **the level promotion, run
forwards**. -/
theorem promoteL_core : ∀ (fuel : Nat) (m : PMemo) (h : LIdx) (s : AState)
    (m' : PMemo) (r : LIdx) (s' : AState),
    PSrc src s.store → PMemoPi m src s.store →
    promoteL m fuel h s = .ok ((m', r), s') →
    PSrc src s'.store ∧ PMemoPi m' src s'.store ∧
      Ext s.store.dropScratch s'.store.dropScratch ∧ PersL r ∧
      Kept (denoteL src.ls h) (denoteL s'.store.dropScratch.ls r) := by
  intro fuel
  induction fuel with
  | zero =>
    intro m h s m' r s' _ _ hrun
    simp only [promoteL, ConRon.Bridge.fail_apply] at hrun
    exact absurd hrun (by simp)
  | succ fuel ih =>
    intro m h s m' r s' hs hm hrun
    unfold promoteL at hrun
    rcases AM.ite_ok hrun with ⟨hp, hrun⟩ | ⟨hp, hrun⟩
    · obtain ⟨v, s1, hv, h1⟩ := AM.bind_ok hrun
      obtain ⟨rfl, hview⟩ := viewL_ok hv
      obtain ⟨hr, rfl⟩ := AM.pure_ok h1
      simp only [Prod.mk.injEq] at hr
      obtain ⟨rfl, rfl⟩ := hr
      exact ⟨hs, hm, Ext.refl _, hp, hs.leafL hp hview⟩
    · cases hmemo : m.lM[h]? with
      | some r0 =>
        simp only [hmemo] at hrun
        obtain ⟨hr, rfl⟩ := AM.pure_ok hrun
        simp only [Prod.mk.injEq] at hr
        obtain ⟨rfl, rfl⟩ := hr
        obtain ⟨hpr, hk⟩ := hm.lM h _ hmemo
        exact ⟨hs, hm, Ext.refl _, hpr, hk⟩
      | none =>
        simp only [hmemo] at hrun
        obtain ⟨v, s1, hv, h1⟩ := AM.bind_ok hrun
        obtain ⟨rfl, hview⟩ := viewL_ok hv
        have hsrc := hs.srcL (by simpa using hp) hview
        have fin : ∀ (m1 : PMemo) (r1 : LIdx) (s2 : AState),
            PSrc src s2.store → PMemoPi m1 src s2.store →
            Ext s1.store.dropScratch s2.store.dropScratch →
            PersL r1 → Kept (denoteLView src.ls v) (denoteL s2.store.dropScratch.ls r1) →
            (m', r) = ({ m1 with lM := m1.lM.insert h r1 }, r1) → s' = s2 →
            PSrc src s'.store ∧ PMemoPi m' src s'.store ∧
              Ext s1.store.dropScratch s'.store.dropScratch ∧ PersL r ∧
              Kept (denoteL src.ls h) (denoteL s'.store.dropScratch.ls r) := by
          intro m1 r1 s2 hs2 hm2 hx2 hp2 hd2 hr hs'
          simp only [Prod.mk.injEq] at hr
          obtain ⟨rfl, rfl⟩ := hr
          subst hs'
          have hk := hd2.pre hsrc
          exact ⟨hs2, hm2.insertL hp2 hk, hx2, hp2, hk⟩
        cases v with
        | zero =>
          obtain ⟨r2, s3, h3, h4⟩ := AM.bind_ok h1
          obtain ⟨hr, rfl⟩ := AM.pure_ok (AM.pure_bind_ok h4)
          obtain ⟨hs3, hx3, hp3, hd3⟩ := promoteL_node hs (w := .zero) (Kept.some _)
            ⟨by simp [LNodeView.lchildren], by simp [LNodeView.nchildren]⟩ h3
          exact fin m r2 _ hs3 (hm.mono hx3) hx3 hp3 hd3 hr rfl
        | succ u =>
          obtain ⟨⟨m2, u2⟩, s3, h3, h4⟩ := AM.bind_ok h1
          obtain ⟨hs3, hm3, hx13, hpu, hku⟩ := ih m u s1 m2 u2 s3 hs hm h3
          obtain ⟨r2, s4, h5, h6⟩ := AM.bind_ok h4
          obtain ⟨hr, rfl⟩ := AM.pure_ok (AM.pure_bind_ok h6)
          obtain ⟨hs4, hx4, hp4, hd4⟩ := promoteL_node hs3
            (w := .succ u2) (Kept.map Level.succ hku)
            ⟨by intro c hc; simp only [LNodeView.lchildren, List.mem_singleton] at hc
                subst hc; exact hpu,
             by simp [LNodeView.nchildren]⟩ h5
          exact fin m2 r2 _ hs4 (hm3.mono hx4) (hx13.trans hx4) hp4 hd4 hr rfl
        | max u w =>
          obtain ⟨⟨m2, u2⟩, s3, h3, h4⟩ := AM.bind_ok h1
          obtain ⟨hs3, hm3, hx13, hpu, hku⟩ := ih m u s1 m2 u2 s3 hs hm h3
          obtain ⟨⟨m3, w2⟩, s4, h5, h6⟩ := AM.bind_ok h4
          obtain ⟨hs4, hm4, hx34, hpw, hkw⟩ := ih m2 w s3 m3 w2 s4 hs3 hm3 h5
          obtain ⟨r2, s5, h7, h8⟩ := AM.bind_ok h6
          obtain ⟨hr, rfl⟩ := AM.pure_ok (AM.pure_bind_ok h8)
          obtain ⟨hs5, hx5, hp5, hd5⟩ := promoteL_node hs4
            (w := .max u2 w2) (Kept.opt2 Level.max (hku.post (hx34.lss.ls.lvl u2)) hkw)
            ⟨by intro c hc
                simp only [LNodeView.lchildren, List.mem_cons, List.not_mem_nil,
                  or_false] at hc
                rcases hc with rfl | rfl
                · exact hpu
                · exact hpw,
             by simp [LNodeView.nchildren]⟩ h7
          exact fin m3 r2 _ hs5 (hm4.mono hx5) ((hx13.trans hx34).trans hx5) hp5 hd5 hr rfl
        | imax u w =>
          obtain ⟨⟨m2, u2⟩, s3, h3, h4⟩ := AM.bind_ok h1
          obtain ⟨hs3, hm3, hx13, hpu, hku⟩ := ih m u s1 m2 u2 s3 hs hm h3
          obtain ⟨⟨m3, w2⟩, s4, h5, h6⟩ := AM.bind_ok h4
          obtain ⟨hs4, hm4, hx34, hpw, hkw⟩ := ih m2 w s3 m3 w2 s4 hs3 hm3 h5
          obtain ⟨r2, s5, h7, h8⟩ := AM.bind_ok h6
          obtain ⟨hr, rfl⟩ := AM.pure_ok (AM.pure_bind_ok h8)
          obtain ⟨hs5, hx5, hp5, hd5⟩ := promoteL_node hs4
            (w := .imax u2 w2) (Kept.opt2 Level.imax (hku.post (hx34.lss.ls.lvl u2)) hkw)
            ⟨by intro c hc
                simp only [LNodeView.lchildren, List.mem_cons, List.not_mem_nil,
                  or_false] at hc
                rcases hc with rfl | rfl
                · exact hpu
                · exact hpw,
             by simp [LNodeView.nchildren]⟩ h7
          exact fin m3 r2 _ hs5 (hm4.mono hx5) ((hx13.trans hx34).trans hx5) hp5 hd5 hr rfl
        | param n =>
          obtain ⟨⟨m2, n2⟩, s3, h3, h4⟩ := AM.bind_ok h1
          obtain ⟨hs3, hm3, hx13, hpn, hkn⟩ := promoteN_step hs hm h3
          obtain ⟨r2, s4, h5, h6⟩ := AM.bind_ok h4
          obtain ⟨hr, rfl⟩ := AM.pure_ok (AM.pure_bind_ok h6)
          obtain ⟨hs4, hx4, hp4, hd4⟩ := promoteL_node hs3
            (w := .param n2) (Kept.map Level.param hkn)
            ⟨by simp [LNodeView.lchildren],
             by intro c hc; simp only [LNodeView.nchildren, List.mem_singleton] at hc
                subst hc; exact hpn⟩ h5
          exact fin m2 r2 _ hs4 (hm3.mono hx4) (hx13.trans hx4) hp4 hd4 hr rfl

/-! ## `promoteLList` and `promoteLs` -/

/-- con-leche: none — arena infrastructure; `promoteL_core` in the shape the walks
above it call. -/
theorem promoteL_step {m m' : PMemo} {fuel : Nat} {h r : LIdx} {s s' : AState}
    (hs : PSrc src s.store) (hm : PMemoPi m src s.store)
    (hrun : promoteL m fuel h s = .ok ((m', r), s')) :
    PSrc src s'.store ∧ PMemoPi m' src s'.store ∧
      Ext s.store.dropScratch s'.store.dropScratch ∧ PersL r ∧
      Kept (denoteL src.ls h) (denoteL s'.store.dropScratch.ls r) :=
  promoteL_core fuel m h s m' r s' hs hm hrun

/-- con-leche: none — arena infrastructure; the level list, promoted element
by element at one memo. -/
theorem promoteLList_step {fuel : Nat} : ∀ (us : List LIdx) {m m' : PMemo}
    {us' : List LIdx} {s s' : AState},
    PSrc src s.store → PMemoPi m src s.store →
    promoteLList m fuel us s = .ok ((m', us'), s') →
    PSrc src s'.store ∧ PMemoPi m' src s'.store ∧
      Ext s.store.dropScratch s'.store.dropScratch ∧
      PersLList us' ∧ us'.length = us.length ∧
      Kept (denoteLList src.ls us) (denoteLList s'.store.dropScratch.ls us') := by
  intro us
  induction us with
  | nil =>
    intro m m' us' s s' hs hm hrun
    simp only [promoteLList] at hrun
    obtain ⟨hr, rfl⟩ := AM.pure_ok hrun
    simp only [Prod.mk.injEq] at hr
    obtain ⟨rfl, rfl⟩ := hr
    exact ⟨hs, hm, Ext.refl _, fun _ h => absurd h (by simp), rfl, Kept.some _⟩
  | cons u us ih =>
    intro m m' us' s s' hs hm hrun
    simp only [promoteLList] at hrun
    obtain ⟨⟨m1, u1⟩, s1, h1, h2⟩ := AM.bind_ok hrun
    obtain ⟨hs1, hm1, hx1, hp1, hd1⟩ := promoteL_step hs hm h1
    obtain ⟨⟨m2, us2⟩, s2, h3, h4⟩ := AM.bind_ok h2
    obtain ⟨hs2, hm2, hx2, hp2, hl2, hd2⟩ := ih hs1 hm1 h3
    obtain ⟨hr, rfl⟩ := AM.pure_ok h4
    simp only [Prod.mk.injEq] at hr
    obtain ⟨rfl, rfl⟩ := hr
    refine ⟨hs2, hm2, hx1.trans hx2, ?_, by simp [hl2],
      Kept.opt2 List.cons (hd1.post (hx2.lss.ls.lvl u1)) hd2⟩
    intro c hc
    simp only [List.mem_cons] at hc
    rcases hc with rfl | hc
    · exact hp1
    · exact hp2 c hc

theorem LsStore.ViewOK.of_denoteLList {st : LsStore} :
    ∀ {us : List LIdx} {xs : List Level}, denoteLList st.ls us = some xs → st.ViewOK us := by
  intro us
  induction us with
  | nil => intro _ _ c hc; simp at hc
  | cons u rest ih =>
    intro xs hxs c hc
    simp only [denoteLList, opt2_eq_some_iff] at hxs
    obtain ⟨a, as, ha, has, -⟩ := hxs
    simp only [List.mem_cons] at hc
    rcases hc with rfl | hc
    · obtain ⟨v, hv⟩ := denoteL_view ha; rw [hv]; rfl
    · exact ih has c hc

/-- con-leche: none — arena infrastructure; **the level-list promotion, run
forwards**. -/
theorem promoteLs_step {m m' : PMemo} {fuel : Nat} {h r : LsIdx} {s s' : AState}
    (hs : PSrc src s.store) (hm : PMemoPi m src s.store)
    (hrun : promoteLs m fuel h s = .ok ((m', r), s')) :
    PSrc src s'.store ∧ PMemoPi m' src s'.store ∧
      Ext s.store.dropScratch s'.store.dropScratch ∧ PersLs r ∧
      Kept (denoteLs src.lss h) (denoteLs s'.store.dropScratch.lss r) := by
  unfold promoteLs at hrun
  rcases AM.ite_ok hrun with ⟨hp, hrun⟩ | ⟨hp, hrun⟩
  · obtain ⟨v, s1, hv, h1⟩ := AM.bind_ok hrun
    obtain ⟨rfl, hview⟩ := viewLs_ok hv
    obtain ⟨hr, rfl⟩ := AM.pure_ok h1
    simp only [Prod.mk.injEq] at hr
    obtain ⟨rfl, rfl⟩ := hr
    exact ⟨hs, hm, Ext.refl _, hp, hs.leafLs hp hview⟩
  · cases hmemo : m.lsM[h]? with
    | some r0 =>
      simp only [hmemo] at hrun
      obtain ⟨hr, rfl⟩ := AM.pure_ok hrun
      simp only [Prod.mk.injEq] at hr
      obtain ⟨rfl, rfl⟩ := hr
      obtain ⟨hpr, hk⟩ := hm.lsM h _ hmemo
      exact ⟨hs, hm, Ext.refl _, hpr, hk⟩
    | none =>
      simp only [hmemo] at hrun
      obtain ⟨us, s1, hv, h1⟩ := AM.bind_ok hrun
      obtain ⟨rfl, hview⟩ := viewLs_ok hv
      have hsrc := hs.srcLs (by simpa using hp) hview
      obtain ⟨⟨m2, us2⟩, s2, h2, h3⟩ := AM.bind_ok h1
      obtain ⟨hs2, hm2, hx12, hp2, -, hd2⟩ := promoteLList_step us hs hm h2
      obtain ⟨r2, s3, h4, h5⟩ := AM.bind_ok h3
      obtain ⟨hr, rfl⟩ := AM.pure_ok h5
      simp only [Prod.mk.injEq] at hr
      obtain ⟨rfl, rfl⟩ := hr
      obtain ⟨y, hy⟩ := hd2.1
      obtain ⟨hwf3, hx23, hsc, hview3, hp3⟩ := internPersistentLs_pi hs2.piWF
        (LsStore.ViewOK.of_denoteLList hy) hp2 h4
      have hk : Kept (denoteLs src.lss h) (denoteLs s'.store.dropScratch.lss r) := by
        refine (hd2.pre hsrc).post fun y' hy' => ?_
        simp only [denoteLs, hview3]
        exact denoteLList_ext hx23.lss.ls us2 y' hy'
      exact ⟨hs2.step hwf3 hx23 hsc, (hm2.mono hx23).insertLs hp3 hk, hx12.trans hx23, hp3, hk⟩

/-! ## `promoteE` -/

/-- con-leche: none — arena infrastructure; a node view that denotes has
children that decode: `intern`'s `ViewOK` precondition, read off the
denotation. -/
theorem EStore.ViewOK.of_denoteEView {st : EStore} {w : ENodeView} {e : Expr}
    (hd : denoteEView st w = some e) : st.ViewOK w := by
  have hE : ∀ {c : EIdx} {a : Expr}, denoteE st c = some a → (st.view c).isSome = true := by
    intro c a hc; obtain ⟨v, hv⟩ := denoteE_view hc; rw [hv]; rfl
  have hN : ∀ {c : NIdx} {a : ConLeche.Name}, denoteN st.ns c = some a →
      (st.ns.view c).isSome = true := by
    intro c a hc; obtain ⟨v, hv⟩ := denoteN_view hc; rw [hv]; rfl
  have hL : ∀ {c : LIdx} {a : Level}, denoteL st.ls c = some a →
      (st.ls.view c).isSome = true := by
    intro c a hc; obtain ⟨v, hv⟩ := denoteL_view hc; rw [hv]; rfl
  have hLs : ∀ {c : LsIdx} {a : List Level}, denoteLs st.lss c = some a →
      (st.lss.view c).isSome = true := by
    intro c a hc; obtain ⟨v, hv, -⟩ := denoteLs_view hc; rw [hv]; rfl
  cases w with
  | bvar _ | lit _ =>
    exact ⟨by simp [ENodeView.echildren], by simp [ENodeView.nchildren],
      by simp [ENodeView.lchildren], by simp [ENodeView.lschildren]⟩
  | fvar k ty =>
    simp only [denoteEView, Option.map_eq_some_iff] at hd
    obtain ⟨a, ha, -⟩ := hd
    refine ⟨?_, by simp [ENodeView.nchildren], by simp [ENodeView.lchildren],
      by simp [ENodeView.lschildren]⟩
    intro c hc; simp only [ENodeView.echildren, List.mem_singleton] at hc
    subst hc; exact hE ha
  | sort u =>
    simp only [denoteEView, Option.map_eq_some_iff] at hd
    obtain ⟨a, ha, -⟩ := hd
    refine ⟨by simp [ENodeView.echildren], by simp [ENodeView.nchildren], ?_,
      by simp [ENodeView.lschildren]⟩
    intro c hc; simp only [ENodeView.lchildren, List.mem_singleton] at hc
    subst hc; exact hL ha
  | const n us =>
    simp only [denoteEView, opt2_eq_some_iff] at hd
    obtain ⟨a, b, ha, hb, -⟩ := hd
    refine ⟨by simp [ENodeView.echildren], ?_, by simp [ENodeView.lchildren], ?_⟩
    · intro c hc; simp only [ENodeView.nchildren, List.mem_singleton] at hc
      subst hc; exact hN ha
    · intro c hc; simp only [ENodeView.lschildren, List.mem_singleton] at hc
      subst hc; exact hLs hb
  | app f a | lam f a | forallE f a =>
    simp only [denoteEView, opt2_eq_some_iff] at hd
    obtain ⟨x, y, hx, hy, -⟩ := hd
    refine ⟨?_, by simp [ENodeView.nchildren], by simp [ENodeView.lchildren],
      by simp [ENodeView.lschildren]⟩
    intro c hc
    simp only [ENodeView.echildren, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · exact hE hx
    · exact hE hy
  | letE t v b =>
    simp only [denoteEView, opt3_eq_some_iff] at hd
    obtain ⟨x, y, z, hx, hy, hz, -⟩ := hd
    refine ⟨?_, by simp [ENodeView.nchildren], by simp [ENodeView.lchildren],
      by simp [ENodeView.lschildren]⟩
    intro c hc
    simp only [ENodeView.echildren, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl
    · exact hE hx
    · exact hE hy
    · exact hE hz
  | proj n k e =>
    simp only [denoteEView, opt2_eq_some_iff] at hd
    obtain ⟨a, x, ha, hx, -⟩ := hd
    refine ⟨?_, ?_, by simp [ENodeView.lchildren], by simp [ENodeView.lschildren]⟩
    · intro c hc; simp only [ENodeView.echildren, List.mem_singleton] at hc
      subst hc; exact hE hx
    · intro c hc; simp only [ENodeView.nchildren, List.mem_singleton] at hc
      subst hc; exact hN ha

/-- con-leche: none — arena infrastructure; an expression node the promotion builds
denotes what its view denotes in the projection. -/
theorem promoteE_node {s s' : AState} {w : ENodeView} {r : EIdx} {d : Option Expr}
    (hs : PSrc src s.store) (hd : Kept d (denoteEView s.store.dropScratch w))
    (hp : EViewPers w) (hrun : internPersistentE w s = .ok (r, s')) :
    PSrc src s'.store ∧ Ext s.store.dropScratch s'.store.dropScratch ∧ PersE r ∧
      Kept d (denoteE s'.store.dropScratch r) := by
  obtain ⟨y, hy⟩ := hd.1
  obtain ⟨hwf', hx, hsc, hview, hpers⟩ :=
    internPersistentE_pi hs.piWF (EStore.ViewOK.of_denoteEView hy) hp hrun
  obtain ⟨rk, hw⟩ := StoreWF'.of_wf hwf'
  refine ⟨hs.step hwf' hx hsc, hx, hpers, hd.post fun y' hy' => ?_⟩
  rw [denoteE_unfold' hw hview]
  exact denoteEView_ext hy' hx

/-- con-leche: none — arena infrastructure; **the expression promotion, run
forwards** — `Arena/Promote.lean`'s "`denote (promote h) = denote h`", with the
invariant and the memo carried through. -/
theorem promoteE_core : ∀ (fuel : Nat) (m : PMemo) (h : EIdx) (s : AState)
    (m' : PMemo) (r : EIdx) (s' : AState),
    PSrc src s.store → PMemoPi m src s.store →
    promoteE m fuel h s = .ok ((m', r), s') →
    PSrc src s'.store ∧ PMemoPi m' src s'.store ∧
      Ext s.store.dropScratch s'.store.dropScratch ∧ PersE r ∧
      Kept (denoteE src h) (denoteE s'.store.dropScratch r) := by
  intro fuel
  induction fuel with
  | zero =>
    intro m h s m' r s' _ _ hrun
    simp only [promoteE, ConRon.Bridge.fail_apply] at hrun
    exact absurd hrun (by simp)
  | succ fuel ih =>
    intro m h s m' r s' hs hm hrun
    unfold promoteE at hrun
    rcases AM.ite_ok hrun with ⟨hp, hrun⟩ | ⟨hp, hrun⟩
    · obtain ⟨v, s1, hv, h1⟩ := AM.bind_ok hrun
      obtain ⟨rfl, hview⟩ := view_ok hv
      obtain ⟨hr, rfl⟩ := AM.pure_ok h1
      simp only [Prod.mk.injEq] at hr
      obtain ⟨rfl, rfl⟩ := hr
      exact ⟨hs, hm, Ext.refl _, hp, hs.leafE hp hview⟩
    · cases hmemo : m.eM[h]? with
      | some r0 =>
        simp only [hmemo] at hrun
        obtain ⟨hr, rfl⟩ := AM.pure_ok hrun
        simp only [Prod.mk.injEq] at hr
        obtain ⟨rfl, rfl⟩ := hr
        obtain ⟨hpr, hk⟩ := hm.eM h _ hmemo
        exact ⟨hs, hm, Ext.refl _, hpr, hk⟩
      | none =>
        simp only [hmemo] at hrun
        obtain ⟨v, s1, hv, h1⟩ := AM.bind_ok hrun
        obtain ⟨rfl, hview⟩ := view_ok hv
        have hsrc := hs.srcE (by simpa using hp) hview
        have fin : ∀ (m1 : PMemo) (r1 : EIdx) (s2 : AState),
            PSrc src s2.store → PMemoPi m1 src s2.store →
            Ext s1.store.dropScratch s2.store.dropScratch →
            PersE r1 → Kept (denoteEView src v) (denoteE s2.store.dropScratch r1) →
            (m', r) = ({ m1 with eM := m1.eM.insert h r1 }, r1) → s' = s2 →
            PSrc src s'.store ∧ PMemoPi m' src s'.store ∧
              Ext s1.store.dropScratch s'.store.dropScratch ∧ PersE r ∧
              Kept (denoteE src h) (denoteE s'.store.dropScratch r) := by
          intro m1 r1 s2 hs2 hm2 hx2 hp2 hd2 hr hs'
          simp only [Prod.mk.injEq] at hr
          obtain ⟨rfl, rfl⟩ := hr
          subst hs'
          have hk := hd2.pre hsrc
          exact ⟨hs2, hm2.insertE hp2 hk, hx2, hp2, hk⟩
        cases v with
        | bvar i =>
          obtain ⟨r2, s3, h3, h4⟩ := AM.bind_ok h1
          obtain ⟨hr, rfl⟩ := AM.pure_ok (AM.pure_bind_ok h4)
          obtain ⟨hs3, hx3, hp3, hd3⟩ := promoteE_node hs (w := .bvar i) (Kept.some _)
            ⟨by simp [ENodeView.echildren], by simp [ENodeView.nchildren],
              by simp [ENodeView.lchildren], by simp [ENodeView.lschildren]⟩ h3
          exact fin m r2 _ hs3 (hm.mono hx3) hx3 hp3 hd3 hr rfl
        | fvar k ty =>
          obtain ⟨⟨m2, t2⟩, s3, h3, h4⟩ := AM.bind_ok h1
          obtain ⟨hs3, hm3, hx13, hpt, hkt⟩ := ih m ty s1 m2 t2 s3 hs hm h3
          obtain ⟨r2, s4, h5, h6⟩ := AM.bind_ok h4
          obtain ⟨hr, rfl⟩ := AM.pure_ok (AM.pure_bind_ok h6)
          obtain ⟨hs4, hx4, hp4, hd4⟩ := promoteE_node hs3
            (w := .fvar k t2) (Kept.map (Expr.fvar k) hkt)
            ⟨by simp [ENodeView.echildren, hpt], by simp [ENodeView.nchildren],
              by simp [ENodeView.lchildren], by simp [ENodeView.lschildren]⟩ h5
          exact fin m2 r2 _ hs4 (hm3.mono hx4) (hx13.trans hx4) hp4 hd4 hr rfl
        | sort u =>
          obtain ⟨⟨m2, u2⟩, s3, h3, h4⟩ := AM.bind_ok h1
          obtain ⟨hs3, hm3, hx13, hpu, hku⟩ := promoteL_step hs hm h3
          obtain ⟨r2, s4, h5, h6⟩ := AM.bind_ok h4
          obtain ⟨hr, rfl⟩ := AM.pure_ok (AM.pure_bind_ok h6)
          obtain ⟨hs4, hx4, hp4, hd4⟩ := promoteE_node hs3
            (w := .sort u2) (Kept.map Expr.sort hku)
            ⟨by simp [ENodeView.echildren], by simp [ENodeView.nchildren],
              by simp [ENodeView.lchildren, hpu], by simp [ENodeView.lschildren]⟩ h5
          exact fin m2 r2 _ hs4 (hm3.mono hx4) (hx13.trans hx4) hp4 hd4 hr rfl
        | const n us =>
          obtain ⟨⟨m2, n2⟩, s3, h3, h4⟩ := AM.bind_ok h1
          obtain ⟨hs3, hm3, hx13, hpn, hkn⟩ := promoteN_step hs hm h3
          obtain ⟨⟨m3, us2⟩, s4, h5, h6⟩ := AM.bind_ok h4
          obtain ⟨hs4, hm4, hx34, hpus, hkus⟩ := promoteLs_step hs3 hm3 h5
          obtain ⟨r2, s5, h7, h8⟩ := AM.bind_ok h6
          obtain ⟨hr, rfl⟩ := AM.pure_ok (AM.pure_bind_ok h8)
          obtain ⟨hs5, hx5, hp5, hd5⟩ := promoteE_node hs4
            (w := .const n2 us2) (Kept.opt2 Expr.const (hkn.post (hx34.lss.ls.ns n2)) hkus)
            ⟨by simp [ENodeView.echildren], by simp [ENodeView.nchildren, hpn],
              by simp [ENodeView.lchildren], by simp [ENodeView.lschildren, hpus]⟩ h7
          exact fin m3 r2 _ hs5 (hm4.mono hx5) ((hx13.trans hx34).trans hx5) hp5 hd5 hr rfl
        | app a b =>
          obtain ⟨⟨m2, a2⟩, s3, h3, h4⟩ := AM.bind_ok h1
          obtain ⟨hs3, hm3, hx13, hpa, hka⟩ := ih m a s1 m2 a2 s3 hs hm h3
          obtain ⟨⟨m3, b2⟩, s4, h5, h6⟩ := AM.bind_ok h4
          obtain ⟨hs4, hm4, hx34, hpb, hkb⟩ := ih m2 b s3 m3 b2 s4 hs3 hm3 h5
          obtain ⟨r2, s5, h7, h8⟩ := AM.bind_ok h6
          obtain ⟨hr, rfl⟩ := AM.pure_ok (AM.pure_bind_ok h8)
          obtain ⟨hs5, hx5, hp5, hd5⟩ := promoteE_node hs4
            (w := .app a2 b2) (Kept.opt2 Expr.app (hka.post (hx34.expr a2)) hkb)
            ⟨by simp [ENodeView.echildren, hpa, hpb], by simp [ENodeView.nchildren],
              by simp [ENodeView.lchildren], by simp [ENodeView.lschildren]⟩ h7
          exact fin m3 r2 _ hs5 (hm4.mono hx5) ((hx13.trans hx34).trans hx5) hp5 hd5 hr rfl
        | lam a b =>
          obtain ⟨⟨m2, a2⟩, s3, h3, h4⟩ := AM.bind_ok h1
          obtain ⟨hs3, hm3, hx13, hpa, hka⟩ := ih m a s1 m2 a2 s3 hs hm h3
          obtain ⟨⟨m3, b2⟩, s4, h5, h6⟩ := AM.bind_ok h4
          obtain ⟨hs4, hm4, hx34, hpb, hkb⟩ := ih m2 b s3 m3 b2 s4 hs3 hm3 h5
          obtain ⟨r2, s5, h7, h8⟩ := AM.bind_ok h6
          obtain ⟨hr, rfl⟩ := AM.pure_ok (AM.pure_bind_ok h8)
          obtain ⟨hs5, hx5, hp5, hd5⟩ := promoteE_node hs4
            (w := .lam a2 b2) (Kept.opt2 Expr.lam (hka.post (hx34.expr a2)) hkb)
            ⟨by simp [ENodeView.echildren, hpa, hpb], by simp [ENodeView.nchildren],
              by simp [ENodeView.lchildren], by simp [ENodeView.lschildren]⟩ h7
          exact fin m3 r2 _ hs5 (hm4.mono hx5) ((hx13.trans hx34).trans hx5) hp5 hd5 hr rfl
        | forallE a b =>
          obtain ⟨⟨m2, a2⟩, s3, h3, h4⟩ := AM.bind_ok h1
          obtain ⟨hs3, hm3, hx13, hpa, hka⟩ := ih m a s1 m2 a2 s3 hs hm h3
          obtain ⟨⟨m3, b2⟩, s4, h5, h6⟩ := AM.bind_ok h4
          obtain ⟨hs4, hm4, hx34, hpb, hkb⟩ := ih m2 b s3 m3 b2 s4 hs3 hm3 h5
          obtain ⟨r2, s5, h7, h8⟩ := AM.bind_ok h6
          obtain ⟨hr, rfl⟩ := AM.pure_ok (AM.pure_bind_ok h8)
          obtain ⟨hs5, hx5, hp5, hd5⟩ := promoteE_node hs4
            (w := .forallE a2 b2) (Kept.opt2 Expr.forallE (hka.post (hx34.expr a2)) hkb)
            ⟨by simp [ENodeView.echildren, hpa, hpb], by simp [ENodeView.nchildren],
              by simp [ENodeView.lchildren], by simp [ENodeView.lschildren]⟩ h7
          exact fin m3 r2 _ hs5 (hm4.mono hx5) ((hx13.trans hx34).trans hx5) hp5 hd5 hr rfl
        | letE a b c =>
          obtain ⟨⟨m2, a2⟩, s3, h3, h4⟩ := AM.bind_ok h1
          obtain ⟨hs3, hm3, hx13, hpa, hka⟩ := ih m a s1 m2 a2 s3 hs hm h3
          obtain ⟨⟨m3, b2⟩, s4, h5, h6⟩ := AM.bind_ok h4
          obtain ⟨hs4, hm4, hx34, hpb, hkb⟩ := ih m2 b s3 m3 b2 s4 hs3 hm3 h5
          obtain ⟨⟨m4, c2⟩, s5, h7, h8⟩ := AM.bind_ok h6
          obtain ⟨hs5, hm5, hx45, hpc, hkc⟩ := ih m3 c s4 m4 c2 s5 hs4 hm4 h7
          obtain ⟨r2, s6, h9, h10⟩ := AM.bind_ok h8
          obtain ⟨hr, rfl⟩ := AM.pure_ok (AM.pure_bind_ok h10)
          obtain ⟨hs6, hx6, hp6, hd6⟩ := promoteE_node hs5
            (w := .letE a2 b2 c2) (Kept.opt3 Expr.letE
              (hka.post ((hx34.trans hx45).expr a2)) (hkb.post (hx45.expr b2)) hkc)
            ⟨by simp [ENodeView.echildren, hpa, hpb, hpc], by simp [ENodeView.nchildren],
              by simp [ENodeView.lchildren], by simp [ENodeView.lschildren]⟩ h9
          exact fin m4 r2 _ hs6 (hm5.mono hx6)
            (((hx13.trans hx34).trans hx45).trans hx6) hp6 hd6 hr rfl
        | lit l =>
          obtain ⟨r2, s3, h3, h4⟩ := AM.bind_ok h1
          obtain ⟨hr, rfl⟩ := AM.pure_ok (AM.pure_bind_ok h4)
          obtain ⟨hs3, hx3, hp3, hd3⟩ := promoteE_node hs (w := .lit l) (Kept.some _)
            ⟨by simp [ENodeView.echildren], by simp [ENodeView.nchildren],
              by simp [ENodeView.lchildren], by simp [ENodeView.lschildren]⟩ h3
          exact fin m r2 _ hs3 (hm.mono hx3) hx3 hp3 hd3 hr rfl
        | proj n k e =>
          obtain ⟨⟨m2, n2⟩, s3, h3, h4⟩ := AM.bind_ok h1
          obtain ⟨hs3, hm3, hx13, hpn, hkn⟩ := promoteN_step hs hm h3
          obtain ⟨⟨m3, e2⟩, s4, h5, h6⟩ := AM.bind_ok h4
          obtain ⟨hs4, hm4, hx34, hpe, hke⟩ := ih m2 e s3 m3 e2 s4 hs3 hm3 h5
          obtain ⟨r2, s5, h7, h8⟩ := AM.bind_ok h6
          obtain ⟨hr, rfl⟩ := AM.pure_ok (AM.pure_bind_ok h8)
          obtain ⟨hs5, hx5, hp5, hd5⟩ := promoteE_node hs4
            (w := .proj n2 k e2) (Kept.opt2 (fun nm x => Expr.proj nm k x)
              (hkn.post (hx34.lss.ls.ns n2)) hke)
            ⟨by simp [ENodeView.echildren, hpe], by simp [ENodeView.nchildren, hpn],
              by simp [ENodeView.lchildren], by simp [ENodeView.lschildren]⟩ h7
          exact fin m3 r2 _ hs5 (hm4.mono hx5) ((hx13.trans hx34).trans hx5) hp5 hd5 hr rfl

/-- con-leche: none — arena infrastructure; `promoteE_core` in the shape the walks
above it call. -/
theorem promoteE_step {m m' : PMemo} {fuel : Nat} {h r : EIdx} {s s' : AState}
    (hs : PSrc src s.store) (hm : PMemoPi m src s.store)
    (hrun : promoteE m fuel h s = .ok ((m', r), s')) :
    PSrc src s'.store ∧ PMemoPi m' src s'.store ∧
      Ext s.store.dropScratch s'.store.dropScratch ∧ PersE r ∧
      Kept (denoteE src h) (denoteE s'.store.dropScratch r) :=
  promoteE_core fuel m h s m' r s' hs hm hrun

/-! ## The store's own promotions -/

/-- con-leche: none — arena infrastructure; **an expression promotion, with no
invariant on the scratch tier**: the projection stays well formed and only grows, the
answer is persistent and denotes there, and it denotes what the subject denotes in the
source, if it does. -/
theorem promoteE_pi {m m' : PMemo} {fuel : Nat} {h r : EIdx} {s s' : AState}
    (hs : PSrc src s.store) (hm : PMemoPi m src s.store)
    (hrun : promoteE m fuel h s = .ok ((m', r), s')) :
    PSrc src s'.store ∧ PMemoPi m' src s'.store ∧
      Ext s.store.dropScratch s'.store.dropScratch ∧ PersE r ∧
      (∃ y, denoteE s'.store.dropScratch r = some y) ∧
      (∀ x, denoteE src h = some x → denoteE s'.store.dropScratch r = some x) :=
  promoteE_core fuel m h s m' r s' hs hm hrun

/-- con-leche: none — arena infrastructure; the same at a level handle. -/
theorem promoteL_pi {m m' : PMemo} {fuel : Nat} {h r : LIdx} {s s' : AState}
    (hs : PSrc src s.store) (hm : PMemoPi m src s.store)
    (hrun : promoteL m fuel h s = .ok ((m', r), s')) :
    PSrc src s'.store ∧ PMemoPi m' src s'.store ∧
      Ext s.store.dropScratch s'.store.dropScratch ∧ PersL r ∧
      (∃ y, denoteL s'.store.dropScratch.ls r = some y) ∧
      (∀ x, denoteL src.ls h = some x → denoteL s'.store.dropScratch.ls r = some x) :=
  promoteL_core fuel m h s m' r s' hs hm hrun

/-- con-leche: none — arena infrastructure; the same at a level list. -/
theorem promoteLList_pi {m m' : PMemo} {fuel : Nat} {us us' : List LIdx} {s s' : AState}
    (hs : PSrc src s.store) (hm : PMemoPi m src s.store)
    (hrun : promoteLList m fuel us s = .ok ((m', us'), s')) :
    PSrc src s'.store ∧ PMemoPi m' src s'.store ∧
      Ext s.store.dropScratch s'.store.dropScratch ∧ PersLList us' ∧
      us'.length = us.length ∧
      (∃ y, denoteLList s'.store.dropScratch.ls us' = some y) ∧
      (∀ x, denoteLList src.ls us = some x → denoteLList s'.store.dropScratch.ls us' = some x) :=
  promoteLList_step us hs hm hrun

/-! ## A persistent handle promotes to itself -/

/-- con-leche: none — arena infrastructure; `promoteN`'s first test: a
persistent name handle is its own promotion. -/
theorem promoteN_pers_self {m m' : PMemo} {fuel : Nat} {h r : NIdx} {s s' : AState}
    (hp : PersN h) (hrun : promoteN m fuel h s = .ok ((m', r), s')) : r = h := by
  cases fuel with
  | zero =>
    simp only [promoteN, ConRon.Bridge.fail_apply] at hrun
    exact absurd hrun (by simp)
  | succ fuel =>
    unfold promoteN at hrun
    rcases AM.ite_ok hrun with ⟨-, hrun⟩ | ⟨hn, -⟩
    · obtain ⟨v, s1, -, h1⟩ := AM.bind_ok hrun
      obtain ⟨hr, -⟩ := AM.pure_ok h1
      simp only [Prod.mk.injEq] at hr
      exact hr.2
    · exact absurd hp hn

/-- con-leche: none — arena infrastructure; **what a promotion does to one
name handle**: it denotes in the projection `st'` what it denoted in the source `src`,
and a persistent one did not move. -/
structure NameKept (src st' : EStore) (n n' : NIdx) : Prop where
  denote : ∀ x, denoteN src.ns n = some x → denoteN st'.ns n' = some x
  pers : PersN n → n' = n

theorem NameKept.post {src st' st'' : EStore} {n n' : NIdx} (h : NameKept src st' n n')
    (hx : Ext st' st'') : NameKept src st'' n n' :=
  ⟨fun x hd => hx.lss.ls.ns _ _ (h.denote x hd), h.pers⟩

theorem promoteN_kept {m m' : PMemo} {fuel : Nat} {h r : NIdx} {s s' : AState}
    (hs : PSrc src s.store) (hm : PMemoPi m src s.store)
    (hrun : promoteN m fuel h s = .ok ((m', r), s')) :
    NameKept src s'.store.dropScratch h r :=
  ⟨(promoteN_step hs hm hrun).2.2.2.2.2, fun hp => promoteN_pers_self hp hrun⟩

/-! ## Census -/

/-- info: 'ConRon.Bridge.promoteN_core' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms promoteN_core

/-- info: 'ConRon.Bridge.promoteL_core' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms promoteL_core

/-- info: 'ConRon.Bridge.promoteLList_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms promoteLList_step

/-- info: 'ConRon.Bridge.promoteLs_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms promoteLs_step

/-- info: 'ConRon.Bridge.promoteE_core' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms promoteE_core

end ConRon.Bridge
