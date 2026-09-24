/-
# `ConRon.Bridge.Promote.Walk` — the four handle-kind promotions, run forwards

The induction under `Bridge/Promote/Exact.lean`'s `promote{N,L,Ls,E}_spec`
(task #97-P3-Promote).  Each walk is proved in ONE form, the core:

    StoreWF' s.store → PMemoOK m s.store → promoteX m fuel h s = .ok ((m', r), s') →
      StoreWF' s'.store ∧ PMemoOK m' s'.store ∧ PersX r ∧
        (∀ x, denoteX s.store h = some x → denoteX s'.store r = some x)

with the DENOTATION as an implication rather than a hypothesis.  That is not
cosmetic: a projection table's `tableName` is promoted by `promoteN` and is
not read back by `denoteProjTable` (con-leche recomputes it), so the
declaration layer has to promote a handle nobody has asked to denote, and
still needs the invariant and the memo afterwards.  The implication form
costs nothing inside the induction, because under the promote window's
invariant **every handle that has a view denotes** (`denote*_of_view'`, a rank
induction): a node the walk reads it can also read back, so the memo row it
records is a promoted pair whether or not the caller cared.

`Ext` and the frame are not re-proved: `Arena/PromoteExt.lean`'s `AExtOf`
gives them for every run, unconditionally.
-/
import ConRon.Bridge.Promote.Memo

namespace ConRon.Bridge

set_option autoImplicit false

open ConLeche ConRon.Arena

/-! ## Under the promote window's invariant, a view denotes -/

theorem denoteN_of_view' {st : NStore} {rk : NIdx → Nat} (h : NWFAt' st rk) :
    ∀ (n : Nat) (i : NIdx), rk i < n → (st.view i).isSome = true →
      ∃ x, denoteN st i = some x := by
  intro n
  induction n with
  | zero => intro i hn; omega
  | succ n ih =>
    intro i hn hv
    obtain ⟨v, hv'⟩ := Option.isSome_iff_exists.mp hv
    rw [denoteN_unfold' h hv']
    cases v with
    | anonymous => exact ⟨_, rfl⟩
    | str p s =>
      have hc := h.childOK i _ hv' p (by simp [NNodeView.children])
      obtain ⟨q, hq⟩ := ih p (by omega) hc.1
      exact ⟨.str q s, by simp [denoteNView, hq]⟩
    | num p k =>
      have hc := h.childOK i _ hv' p (by simp [NNodeView.children])
      obtain ⟨q, hq⟩ := ih p (by omega) hc.1
      exact ⟨.num q k, by simp [denoteNView, hq]⟩

theorem denoteN_of_view {st : NStore} (h : NStoreWF' st) {i : NIdx}
    (hv : (st.view i).isSome = true) : ∃ x, denoteN st i = some x := by
  obtain ⟨rk, h⟩ := h
  exact denoteN_of_view' h _ i (Nat.lt_succ_self _) hv

/-! ## The readers and the promote-interns, as run equations -/

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

theorem internPersistentN_run {v : NNodeView} {s : AState} {r : NIdx} {s' : AState}
    (hwf : StoreWF' s.store) (hv : s.store.ns.ViewOK v) (hp : NViewPers v)
    (h : internPersistentN v s = .ok (r, s')) :
    StoreWF' s'.store ∧ s'.store.ns.view r = some v ∧ PersN r := by
  have hns := hwf.nsWF
  cases hf : s.store.ns.pers.find? v with
  | some hh =>
    simp only [internPersistentN, bind, StateT.bind, get, getThe, MonadStateOf.get,
      StateT.get, pure, StateT.pure, Except.bind, Except.pure, hf, Except.ok.injEq,
      Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨rk, hn⟩ := hns
    exact ⟨hwf, ((hn.consP v _).mp hf).1, ((hn.consP v _).mp hf).2⟩
  | none =>
    by_cases hc : s.store.ns.pers.sizeOf v < Idx.idxCap
    · simp only [internPersistentN, bind, StateT.bind, get, getThe, MonadStateOf.get,
        StateT.get, pure, StateT.pure, set, StateT.set, Except.bind, Except.pure, hf,
        if_pos hc, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨EStore.internNamePersistent_wf' hwf hv hp hc,
        NStore.internPersistent_view hns (fun _ => hc),
        NStore.internPersistent_pers hns (fun _ => hc)⟩
    · simp only [internPersistentN, bind, StateT.bind, get, getThe, MonadStateOf.get,
        StateT.get, pure, set, Except.bind, Except.pure, hf,
        if_neg hc, ConRon.Bridge.fail_apply] at h
      exact absurd h (by simp)

/-! ## `promoteN` -/

/-- con-leche: none — arena infrastructure; a name node the promotion builds
denotes what the node it copies denotes. -/
theorem promoteN_node {s s' : AState} {w : NNodeView} {r : NIdx} {x : ConLeche.Name}
    (hwf : StoreWF' s.store) (hd : denoteNView s.store.ns w = some x)
    (hp : NViewPers w) (hrun : internPersistentN w s = .ok (r, s')) :
    StoreWF' s'.store ∧ Ext s.store s'.store ∧ PersN r ∧
      denoteN s'.store.ns r = some x := by
  have hvok : s.store.ns.ViewOK w := by
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
  obtain ⟨hwf', hview, hpers⟩ := internPersistentN_run hwf hvok hp hrun
  have hx : Ext s.store s'.store := (internPersistentN_aext hrun).ext
  obtain ⟨rk, hw⟩ := hwf'.nsWF
  refine ⟨hwf', hx, hpers, ?_⟩
  rw [denoteN_unfold' hw hview]
  cases w with
  | anonymous => simpa [denoteNView] using hd
  | str p t =>
    simp only [denoteNView, Option.map_eq_some_iff] at hd ⊢
    obtain ⟨q, hq, he⟩ := hd
    exact ⟨q, hx.lss.ls.ns _ _ hq, he⟩
  | num p k =>
    simp only [denoteNView, Option.map_eq_some_iff] at hd ⊢
    obtain ⟨q, hq, he⟩ := hd
    exact ⟨q, hx.lss.ls.ns _ _ hq, he⟩

theorem PMemoOK.insertN {m : PMemo} {st : EStore} (hm : PMemoOK m st) {h r : NIdx}
    {x : ConLeche.Name} (hp : PersN r) (hh : denoteN st.ns h = some x)
    (hr : denoteN st.ns r = some x) :
    PMemoOK { m with nM := m.nM.insert h r } st := by
  refine ⟨hm.eM, ?_, hm.lM, hm.lsM⟩
  intro k r' hk
  simp only [Std.HashMap.getElem?_insert] at hk
  split at hk
  · rename_i he
    obtain rfl := Option.some.inj hk
    obtain rfl := eq_of_beq he
    exact ⟨hp, x, hh, hr⟩
  · exact hm.nM k r' hk

/-- con-leche: none — arena infrastructure; **the name promotion, run
forwards**: the invariant and the memo survive, the answer is persistent, and
it denotes whatever the subject denoted. -/
theorem promoteN_core : ∀ (fuel : Nat) (m : PMemo) (h : NIdx) (s : AState)
    (m' : PMemo) (r : NIdx) (s' : AState),
    StoreWF' s.store → PMemoOK m s.store →
    promoteN m fuel h s = .ok ((m', r), s') →
    StoreWF' s'.store ∧ PMemoOK m' s'.store ∧ PersN r ∧
      (∀ x, denoteN s.store.ns h = some x → denoteN s'.store.ns r = some x) := by
  intro fuel
  induction fuel with
  | zero =>
    intro m h s m' r s' _ _ hrun
    simp only [promoteN, ConRon.Bridge.fail_apply] at hrun
    exact absurd hrun (by simp)
  | succ fuel ih =>
    intro m h s m' r s' hwf hm hrun
    unfold promoteN at hrun
    rcases AM.ite_ok hrun with ⟨hp, hrun⟩ | ⟨hp, hrun⟩
    · obtain ⟨hr, rfl⟩ := AM.pure_ok hrun
      simp only [Prod.mk.injEq] at hr
      obtain ⟨rfl, rfl⟩ := hr
      exact ⟨hwf, hm, hp, fun _ hx => hx⟩
    · cases hmemo : m.nM[h]? with
      | some r0 =>
        simp only [hmemo] at hrun
        obtain ⟨hr, rfl⟩ := AM.pure_ok hrun
        simp only [Prod.mk.injEq] at hr
        obtain ⟨rfl, rfl⟩ := hr
        obtain ⟨hpr, x0, hx0, hr0⟩ := hm.nM h _ hmemo
        refine ⟨hwf, hm, hpr, fun x hx => ?_⟩
        rw [hx0] at hx; obtain rfl := Option.some.inj hx; exact hr0
      | none =>
        simp only [hmemo] at hrun
        obtain ⟨v, s1, hv, h1⟩ := AM.bind_ok hrun
        obtain ⟨rfl, hview⟩ := viewN_ok hv
        obtain ⟨x0, hx0⟩ := denoteN_of_view hwf.nsWF (by rw [hview]; rfl)
        have hden : denoteN s1.store.ns h = denoteNView s1.store.ns v := by
          obtain ⟨rk, hw⟩ := hwf.nsWF; exact denoteN_unfold' hw hview
        -- every arm ends the same way: the node rebuilt at `(m1, r1)` in
        -- `s2`, recorded in the memo
        have fin : ∀ (m1 : PMemo) (r1 : NIdx) (s2 : AState),
            StoreWF' s2.store → PMemoOK m1 s2.store → Ext s1.store s2.store →
            PersN r1 → denoteN s2.store.ns r1 = some x0 →
            (m', r) = ({ m1 with nM := m1.nM.insert h r1 }, r1) → s' = s2 →
            StoreWF' s'.store ∧ PMemoOK m' s'.store ∧ PersN r ∧
              (∀ x, denoteN s1.store.ns h = some x → denoteN s'.store.ns r = some x) := by
          intro m1 r1 s2 hwf2 hm2 hx2 hp2 hd2 hr hs
          simp only [Prod.mk.injEq] at hr
          obtain ⟨rfl, rfl⟩ := hr
          subst hs
          refine ⟨hwf2, hm2.insertN hp2 (hx2.lss.ls.ns _ _ hx0) hd2, hp2, ?_⟩
          intro x hx; rw [hx0] at hx; obtain rfl := Option.some.inj hx; exact hd2
        rw [hden] at hx0
        cases v with
        | anonymous =>
          obtain ⟨r2, s3, h3, h4⟩ := AM.bind_ok h1
          obtain ⟨hr, rfl⟩ := AM.pure_ok (AM.pure_bind_ok h4)
          obtain ⟨hwf3, hx3, hp3, hd3⟩ :=
            promoteN_node hwf hx0 (by intro c hc; simp [NNodeView.children] at hc) h3
          rw [← hden] at hx0
          exact fin m r2 _ hwf3 (hm.mono hx3) hx3 hp3 hd3 hr rfl
        | str p t =>
          have hx0' := hx0
          simp only [denoteNView, Option.map_eq_some_iff] at hx0'
          obtain ⟨q, hq, hxq⟩ := hx0'
          obtain ⟨⟨m2, p2⟩, s3, h3, h4⟩ := AM.bind_ok h1
          obtain ⟨hwf3, hm3, hpp, hdp⟩ := ih m p s1 m2 p2 s3 hwf hm h3
          have hx13 := (promoteN_aext m fuel p s1 (m2, p2) s3 h3).ext
          obtain ⟨r2, s4, h5, h6⟩ := AM.bind_ok h4
          obtain ⟨hr, rfl⟩ := AM.pure_ok (AM.pure_bind_ok h6)
          obtain ⟨hwf4, hx4, hp4, hd4⟩ := promoteN_node hwf3
            (w := .str p2 t) (x := x0) (by simp [denoteNView, hdp q hq, hxq])
            (by intro c hc; simp only [NNodeView.children, List.mem_singleton] at hc
                subst hc; exact hpp) h5
          rw [← hden] at hx0
          exact fin m2 r2 _ hwf4 (hm3.mono hx4) (hx13.trans hx4) hp4 hd4 hr rfl
        | num p k =>
          have hx0' := hx0
          simp only [denoteNView, Option.map_eq_some_iff] at hx0'
          obtain ⟨q, hq, hxq⟩ := hx0'
          obtain ⟨⟨m2, p2⟩, s3, h3, h4⟩ := AM.bind_ok h1
          obtain ⟨hwf3, hm3, hpp, hdp⟩ := ih m p s1 m2 p2 s3 hwf hm h3
          have hx13 := (promoteN_aext m fuel p s1 (m2, p2) s3 h3).ext
          obtain ⟨r2, s4, h5, h6⟩ := AM.bind_ok h4
          obtain ⟨hr, rfl⟩ := AM.pure_ok (AM.pure_bind_ok h6)
          obtain ⟨hwf4, hx4, hp4, hd4⟩ := promoteN_node hwf3
            (w := .num p2 k) (x := x0) (by simp [denoteNView, hdp q hq, hxq])
            (by intro c hc; simp only [NNodeView.children, List.mem_singleton] at hc
                subst hc; exact hpp) h5
          rw [← hden] at hx0
          exact fin m2 r2 _ hwf4 (hm3.mono hx4) (hx13.trans hx4) hp4 hd4 hr rfl

/-! ## `promoteL` -/

theorem denoteL_of_view' {st : LStore} {rk : LIdx → Nat} (h : LWFAt' st rk) :
    ∀ (n : Nat) (i : LIdx), rk i < n → (st.view i).isSome = true →
      ∃ x, denoteL st i = some x := by
  intro n
  induction n with
  | zero => intro i hn; omega
  | succ n ih =>
    intro i hn hv
    obtain ⟨v, hv'⟩ := Option.isSome_iff_exists.mp hv
    rw [denoteL_unfold' h hv']
    cases v with
    | zero => exact ⟨_, rfl⟩
    | succ u =>
      have hc := h.childOK i _ hv' u (by simp [LNodeView.lchildren])
      obtain ⟨a, ha⟩ := ih u (by omega) hc.1
      exact ⟨.succ a, by simp [denoteLView, ha]⟩
    | max u w =>
      have hc := h.childOK i _ hv' u (by simp [LNodeView.lchildren])
      have hc' := h.childOK i _ hv' w (by simp [LNodeView.lchildren])
      obtain ⟨a, ha⟩ := ih u (by omega) hc.1
      obtain ⟨b, hb⟩ := ih w (by omega) hc'.1
      exact ⟨.max a b, by simp [denoteLView, ha, hb, opt2]⟩
    | imax u w =>
      have hc := h.childOK i _ hv' u (by simp [LNodeView.lchildren])
      have hc' := h.childOK i _ hv' w (by simp [LNodeView.lchildren])
      obtain ⟨a, ha⟩ := ih u (by omega) hc.1
      obtain ⟨b, hb⟩ := ih w (by omega) hc'.1
      exact ⟨.imax a b, by simp [denoteLView, ha, hb, opt2]⟩
    | param nm =>
      have hc := h.nchildOK i _ hv' nm (by simp [LNodeView.nchildren])
      obtain ⟨x, hx⟩ := denoteN_of_view h.ns hc.1
      exact ⟨.param x, by simp [denoteLView, hx]⟩

theorem denoteL_of_view {st : LStore} (h : LStoreWF' st) {i : LIdx}
    (hv : (st.view i).isSome = true) : ∃ x, denoteL st i = some x := by
  obtain ⟨rk, h⟩ := h
  exact denoteL_of_view' h _ i (Nat.lt_succ_self _) hv

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

theorem internPersistentL_run {v : LNodeView} {s : AState} {r : LIdx} {s' : AState}
    (hwf : StoreWF' s.store) (hv : s.store.ls.ViewOK v) (hp : LViewPers v)
    (h : internPersistentL v s = .ok (r, s')) :
    StoreWF' s'.store ∧ s'.store.ls.view r = some v ∧ PersL r := by
  have hls := hwf.lsWF
  cases hf : s.store.ls.pers.find? v with
  | some hh =>
    simp only [internPersistentL, bind, StateT.bind, get, getThe, MonadStateOf.get,
      StateT.get, pure, StateT.pure, Except.bind, Except.pure, hf, Except.ok.injEq,
      Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨rk, hl⟩ := hls
    exact ⟨hwf, ((hl.consP v _).mp hf).1, ((hl.consP v _).mp hf).2⟩
  | none =>
    by_cases hc : s.store.ls.pers.sizeOf v < Idx.idxCap
    · simp only [internPersistentL, bind, StateT.bind, get, getThe, MonadStateOf.get,
        StateT.get, pure, StateT.pure, set, StateT.set, Except.bind, Except.pure, hf,
        if_pos hc, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨EStore.internLevelPersistent_wf' hwf hv hp hc,
        LStore.internPersistent_view hls (fun _ => hc),
        LStore.internPersistent_pers hls (fun _ => hc)⟩
    · simp only [internPersistentL, bind, StateT.bind, get, getThe, MonadStateOf.get,
        StateT.get, pure, set, Except.bind, Except.pure, hf,
        if_neg hc, ConRon.Bridge.fail_apply] at h
      exact absurd h (by simp)

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

theorem promoteL_node {s s' : AState} {w : LNodeView} {r : LIdx} {x : Level}
    (hwf : StoreWF' s.store) (hd : denoteLView s.store.ls w = some x)
    (hp : LViewPers w) (hrun : internPersistentL w s = .ok (r, s')) :
    StoreWF' s'.store ∧ Ext s.store s'.store ∧ PersL r ∧
      denoteL s'.store.ls r = some x := by
  obtain ⟨hwf', hview, hpers⟩ :=
    internPersistentL_run hwf (LStore.ViewOK.of_denoteLView hd) hp hrun
  have hx : Ext s.store s'.store := (internPersistentL_aext hrun).ext
  obtain ⟨rk, hw⟩ := hwf'.lsWF
  refine ⟨hwf', hx, hpers, ?_⟩
  rw [denoteL_unfold' hw hview]
  exact denoteLView_ext hd hx.lss.ls

theorem PMemoOK.insertL {m : PMemo} {st : EStore} (hm : PMemoOK m st) {h r : LIdx}
    {x : Level} (hp : PersL r) (hh : denoteL st.ls h = some x)
    (hr : denoteL st.ls r = some x) :
    PMemoOK { m with lM := m.lM.insert h r } st := by
  refine ⟨hm.eM, hm.nM, ?_, hm.lsM⟩
  intro k r' hk
  simp only [Std.HashMap.getElem?_insert] at hk
  split at hk
  · rename_i he
    obtain rfl := Option.some.inj hk
    obtain rfl := eq_of_beq he
    exact ⟨hp, x, hh, hr⟩
  · exact hm.lM k r' hk

/-- con-leche: none — arena infrastructure; `promoteN_core` in the name
walk's shape, the form the walks above it call. -/
theorem promoteN_step {m m' : PMemo} {fuel : Nat} {h r : NIdx} {s s' : AState}
    (hwf : StoreWF' s.store) (hm : PMemoOK m s.store)
    (hrun : promoteN m fuel h s = .ok ((m', r), s')) :
    StoreWF' s'.store ∧ PMemoOK m' s'.store ∧ Ext s.store s'.store ∧ PersN r ∧
      (∀ x, denoteN s.store.ns h = some x → denoteN s'.store.ns r = some x) := by
  obtain ⟨a, b, c, d⟩ := promoteN_core fuel m h s m' r s' hwf hm hrun
  exact ⟨a, b, (promoteN_aext m fuel h s (m', r) s' hrun).ext, c, d⟩

/-- con-leche: none — arena infrastructure; **the level promotion, run
forwards**. -/
theorem promoteL_core : ∀ (fuel : Nat) (m : PMemo) (h : LIdx) (s : AState)
    (m' : PMemo) (r : LIdx) (s' : AState),
    StoreWF' s.store → PMemoOK m s.store →
    promoteL m fuel h s = .ok ((m', r), s') →
    StoreWF' s'.store ∧ PMemoOK m' s'.store ∧ PersL r ∧
      (∀ x, denoteL s.store.ls h = some x → denoteL s'.store.ls r = some x) := by
  intro fuel
  induction fuel with
  | zero =>
    intro m h s m' r s' _ _ hrun
    simp only [promoteL, ConRon.Bridge.fail_apply] at hrun
    exact absurd hrun (by simp)
  | succ fuel ih =>
    intro m h s m' r s' hwf hm hrun
    have ihs : ∀ {m m' : PMemo} {h r : LIdx} {s s' : AState},
        StoreWF' s.store → PMemoOK m s.store →
        promoteL m fuel h s = .ok ((m', r), s') →
        StoreWF' s'.store ∧ PMemoOK m' s'.store ∧ Ext s.store s'.store ∧ PersL r ∧
          (∀ x, denoteL s.store.ls h = some x → denoteL s'.store.ls r = some x) := by
      intro m m' h r s s' hwf hm hrun
      obtain ⟨a, b, c, d⟩ := ih m h s m' r s' hwf hm hrun
      exact ⟨a, b, (promoteL_aext m fuel h s (m', r) s' hrun).ext, c, d⟩
    unfold promoteL at hrun
    rcases AM.ite_ok hrun with ⟨hp, hrun⟩ | ⟨hp, hrun⟩
    · obtain ⟨hr, rfl⟩ := AM.pure_ok hrun
      simp only [Prod.mk.injEq] at hr
      obtain ⟨rfl, rfl⟩ := hr
      exact ⟨hwf, hm, hp, fun _ hx => hx⟩
    · cases hmemo : m.lM[h]? with
      | some r0 =>
        simp only [hmemo] at hrun
        obtain ⟨hr, rfl⟩ := AM.pure_ok hrun
        simp only [Prod.mk.injEq] at hr
        obtain ⟨rfl, rfl⟩ := hr
        obtain ⟨hpr, x0, hx0, hr0⟩ := hm.lM h _ hmemo
        refine ⟨hwf, hm, hpr, fun x hx => ?_⟩
        rw [hx0] at hx; obtain rfl := Option.some.inj hx; exact hr0
      | none =>
        simp only [hmemo] at hrun
        obtain ⟨v, s1, hv, h1⟩ := AM.bind_ok hrun
        obtain ⟨rfl, hview⟩ := viewL_ok hv
        obtain ⟨x0, hx0⟩ := denoteL_of_view hwf.lsWF (by rw [hview]; rfl)
        have hden : denoteL s1.store.ls h = denoteLView s1.store.ls v := by
          obtain ⟨rk, hw⟩ := hwf.lsWF; exact denoteL_unfold' hw hview
        have fin : ∀ (m1 : PMemo) (r1 : LIdx) (s2 : AState),
            StoreWF' s2.store → PMemoOK m1 s2.store → Ext s1.store s2.store →
            PersL r1 → denoteL s2.store.ls r1 = some x0 →
            (m', r) = ({ m1 with lM := m1.lM.insert h r1 }, r1) → s' = s2 →
            StoreWF' s'.store ∧ PMemoOK m' s'.store ∧ PersL r ∧
              (∀ x, denoteL s1.store.ls h = some x → denoteL s'.store.ls r = some x) := by
          intro m1 r1 s2 hwf2 hm2 hx2 hp2 hd2 hr hs
          simp only [Prod.mk.injEq] at hr
          obtain ⟨rfl, rfl⟩ := hr
          subst hs
          refine ⟨hwf2, hm2.insertL hp2 (hx2.lss.ls.lvl _ _ hx0) hd2, hp2, ?_⟩
          intro x hx; rw [hx0] at hx; obtain rfl := Option.some.inj hx; exact hd2
        rw [hden] at hx0
        cases v with
        | zero =>
          obtain ⟨r2, s3, h3, h4⟩ := AM.bind_ok h1
          obtain ⟨hr, rfl⟩ := AM.pure_ok (AM.pure_bind_ok h4)
          obtain ⟨hwf3, hx3, hp3, hd3⟩ := promoteL_node hwf hx0
            ⟨by simp [LNodeView.lchildren], by simp [LNodeView.nchildren]⟩ h3
          exact fin m r2 _ hwf3 (hm.mono hx3) hx3 hp3 hd3 hr rfl
        | succ u =>
          have hx0' := hx0
          simp only [denoteLView, Option.map_eq_some_iff] at hx0'
          obtain ⟨a, ha, hxa⟩ := hx0'
          obtain ⟨⟨m2, u2⟩, s3, h3, h4⟩ := AM.bind_ok h1
          obtain ⟨hwf3, hm3, hx13, hpu, hdu⟩ := ihs hwf hm h3
          obtain ⟨r2, s4, h5, h6⟩ := AM.bind_ok h4
          obtain ⟨hr, rfl⟩ := AM.pure_ok (AM.pure_bind_ok h6)
          obtain ⟨hwf4, hx4, hp4, hd4⟩ := promoteL_node hwf3
            (w := .succ u2) (x := x0) (by simp [denoteLView, hdu a ha, hxa])
            ⟨by intro c hc; simp only [LNodeView.lchildren, List.mem_singleton] at hc
                subst hc; exact hpu,
             by simp [LNodeView.nchildren]⟩ h5
          exact fin m2 r2 _ hwf4 (hm3.mono hx4) (hx13.trans hx4) hp4 hd4 hr rfl
        | max u w =>
          have hx0' := hx0
          simp only [denoteLView, opt2_eq_some_iff] at hx0'
          obtain ⟨a, b, ha, hb, hxab⟩ := hx0'
          obtain ⟨⟨m2, u2⟩, s3, h3, h4⟩ := AM.bind_ok h1
          obtain ⟨hwf3, hm3, hx13, hpu, hdu⟩ := ihs hwf hm h3
          obtain ⟨⟨m3, w2⟩, s4, h5, h6⟩ := AM.bind_ok h4
          obtain ⟨hwf4, hm4, hx34, hpw, hdw⟩ := ihs hwf3 hm3 h5
          obtain ⟨r2, s5, h7, h8⟩ := AM.bind_ok h6
          obtain ⟨hr, rfl⟩ := AM.pure_ok (AM.pure_bind_ok h8)
          have hu4 : denoteL s4.store.ls u2 = some a := hx34.lss.ls.lvl _ _ (hdu a ha)
          have hw4 : denoteL s4.store.ls w2 = some b := hdw b (hx13.lss.ls.lvl _ _ hb)
          obtain ⟨hwf5, hx5, hp5, hd5⟩ := promoteL_node hwf4
            (w := .max u2 w2) (x := x0)
            (by simp [denoteLView, hu4, hw4, opt2, hxab])
            ⟨by intro c hc
                simp only [LNodeView.lchildren, List.mem_cons, List.not_mem_nil,
                  or_false] at hc
                rcases hc with rfl | rfl
                · exact hpu
                · exact hpw,
             by simp [LNodeView.nchildren]⟩ h7
          exact fin m3 r2 _ hwf5 (hm4.mono hx5) ((hx13.trans hx34).trans hx5) hp5 hd5 hr rfl
        | imax u w =>
          have hx0' := hx0
          simp only [denoteLView, opt2_eq_some_iff] at hx0'
          obtain ⟨a, b, ha, hb, hxab⟩ := hx0'
          obtain ⟨⟨m2, u2⟩, s3, h3, h4⟩ := AM.bind_ok h1
          obtain ⟨hwf3, hm3, hx13, hpu, hdu⟩ := ihs hwf hm h3
          obtain ⟨⟨m3, w2⟩, s4, h5, h6⟩ := AM.bind_ok h4
          obtain ⟨hwf4, hm4, hx34, hpw, hdw⟩ := ihs hwf3 hm3 h5
          obtain ⟨r2, s5, h7, h8⟩ := AM.bind_ok h6
          obtain ⟨hr, rfl⟩ := AM.pure_ok (AM.pure_bind_ok h8)
          have hu4 : denoteL s4.store.ls u2 = some a := hx34.lss.ls.lvl _ _ (hdu a ha)
          have hw4 : denoteL s4.store.ls w2 = some b := hdw b (hx13.lss.ls.lvl _ _ hb)
          obtain ⟨hwf5, hx5, hp5, hd5⟩ := promoteL_node hwf4
            (w := .imax u2 w2) (x := x0)
            (by simp [denoteLView, hu4, hw4, opt2, hxab])
            ⟨by intro c hc
                simp only [LNodeView.lchildren, List.mem_cons, List.not_mem_nil,
                  or_false] at hc
                rcases hc with rfl | rfl
                · exact hpu
                · exact hpw,
             by simp [LNodeView.nchildren]⟩ h7
          exact fin m3 r2 _ hwf5 (hm4.mono hx5) ((hx13.trans hx34).trans hx5) hp5 hd5 hr rfl
        | param n =>
          have hx0' := hx0
          simp only [denoteLView, Option.map_eq_some_iff] at hx0'
          obtain ⟨a, ha, hxa⟩ := hx0'
          obtain ⟨⟨m2, n2⟩, s3, h3, h4⟩ := AM.bind_ok h1
          obtain ⟨hwf3, hm3, hx13, hpn, hdn⟩ := promoteN_step hwf hm h3
          obtain ⟨r2, s4, h5, h6⟩ := AM.bind_ok h4
          obtain ⟨hr, rfl⟩ := AM.pure_ok (AM.pure_bind_ok h6)
          have hn3 : denoteN s3.store.ls.ns n2 = some a := hdn a ha
          obtain ⟨hwf4, hx4, hp4, hd4⟩ := promoteL_node hwf3
            (w := .param n2) (x := x0) (by simp [denoteLView, hn3, hxa])
            ⟨by simp [LNodeView.lchildren],
             by intro c hc; simp only [LNodeView.nchildren, List.mem_singleton] at hc
                subst hc; exact hpn⟩ h5
          exact fin m2 r2 _ hwf4 (hm3.mono hx4) (hx13.trans hx4) hp4 hd4 hr rfl

/-! ## `promoteLList` and `promoteLs` -/

theorem promoteL_step {m m' : PMemo} {fuel : Nat} {h r : LIdx} {s s' : AState}
    (hwf : StoreWF' s.store) (hm : PMemoOK m s.store)
    (hrun : promoteL m fuel h s = .ok ((m', r), s')) :
    StoreWF' s'.store ∧ PMemoOK m' s'.store ∧ Ext s.store s'.store ∧ PersL r ∧
      (∀ x, denoteL s.store.ls h = some x → denoteL s'.store.ls r = some x) := by
  obtain ⟨a, b, c, d⟩ := promoteL_core fuel m h s m' r s' hwf hm hrun
  exact ⟨a, b, (promoteL_aext m fuel h s (m', r) s' hrun).ext, c, d⟩

/-- con-leche: none — arena infrastructure; the level list, promoted element
by element at one memo. -/
theorem promoteLList_step {fuel : Nat} : ∀ (us : List LIdx) {m m' : PMemo}
    {us' : List LIdx} {s s' : AState},
    StoreWF' s.store → PMemoOK m s.store →
    promoteLList m fuel us s = .ok ((m', us'), s') →
    StoreWF' s'.store ∧ PMemoOK m' s'.store ∧ Ext s.store s'.store ∧
      PersLList us' ∧ us'.length = us.length ∧
      (∀ xs, denoteLList s.store.ls us = some xs → denoteLList s'.store.ls us' = some xs) := by
  intro us
  induction us with
  | nil =>
    intro m m' us' s s' hwf hm hrun
    simp only [promoteLList] at hrun
    obtain ⟨hr, rfl⟩ := AM.pure_ok hrun
    simp only [Prod.mk.injEq] at hr
    obtain ⟨rfl, rfl⟩ := hr
    exact ⟨hwf, hm, Ext.refl _, fun _ h => absurd h (by simp), rfl, fun _ h => h⟩
  | cons u us ih =>
    intro m m' us' s s' hwf hm hrun
    simp only [promoteLList] at hrun
    obtain ⟨⟨m1, u1⟩, s1, h1, h2⟩ := AM.bind_ok hrun
    obtain ⟨hwf1, hm1, hx1, hp1, hd1⟩ := promoteL_step hwf hm h1
    obtain ⟨⟨m2, us2⟩, s2, h3, h4⟩ := AM.bind_ok h2
    obtain ⟨hwf2, hm2, hx2, hp2, hl2, hd2⟩ := ih hwf1 hm1 h3
    obtain ⟨hr, rfl⟩ := AM.pure_ok h4
    simp only [Prod.mk.injEq] at hr
    obtain ⟨rfl, rfl⟩ := hr
    refine ⟨hwf2, hm2, hx1.trans hx2, ?_, by simp [hl2], ?_⟩
    · intro c hc
      simp only [List.mem_cons] at hc
      rcases hc with rfl | hc
      · exact hp1
      · exact hp2 c hc
    · intro xs hxs
      simp only [denoteLList, opt2_eq_some_iff] at hxs ⊢
      obtain ⟨a, as, ha, has, rfl⟩ := hxs
      exact ⟨a, as, hx2.lss.ls.lvl _ _ (hd1 a ha),
        hd2 as (denoteLList_ext hx1.lss.ls us as has), rfl⟩

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

theorem internPersistentLs_run {v : LsNodeView} {s : AState} {r : LsIdx} {s' : AState}
    (hwf : StoreWF' s.store) (hv : s.store.lss.ViewOK v) (hp : LsViewPers v)
    (h : internPersistentLs v s = .ok (r, s')) :
    StoreWF' s'.store ∧ s'.store.lss.view r = some v ∧ PersLs r := by
  have hlss := hwf.lssWF
  cases hf : s.store.lss.pers.find? v with
  | some hh =>
    simp only [internPersistentLs, bind, StateT.bind, get, getThe, MonadStateOf.get,
      StateT.get, pure, StateT.pure, Except.bind, Except.pure, hf, Except.ok.injEq,
      Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨hwf, ((hlss.consP v _).mp hf).1, ((hlss.consP v _).mp hf).2⟩
  | none =>
    by_cases hc : s.store.lss.pers.sizeOf v < Idx.idxCap
    · simp only [internPersistentLs, bind, StateT.bind, get, getThe, MonadStateOf.get,
        StateT.get, pure, StateT.pure, set, StateT.set, Except.bind, Except.pure, hf,
        if_pos hc, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨EStore.internLevelsPersistent_wf' hwf hv hp hc,
        LsStore.internPersistent_view hlss (fun _ => hc),
        LsStore.internPersistent_pers hlss (fun _ => hc)⟩
    · simp only [internPersistentLs, bind, StateT.bind, get, getThe, MonadStateOf.get,
        StateT.get, pure, set, Except.bind, Except.pure, hf,
        if_neg hc, ConRon.Bridge.fail_apply] at h
      exact absurd h (by simp)

/-- con-leche: none — arena infrastructure; under the promote window's
invariant a level-list handle with a view denotes. -/
theorem denoteLs_of_view {st : LsStore} (h : LsStoreWF' st) {i : LsIdx} {us : LsNodeView}
    (hv : st.view i = some us) : ∃ xs, denoteLList st.ls us = some xs := by
  have hel : ∀ c ∈ us, (st.ls.view c).isSome = true := fun c hc =>
    (h.lchildOK i us hv c hc).1
  clear hv
  induction us with
  | nil => exact ⟨[], rfl⟩
  | cons u rest ih =>
    obtain ⟨a, ha⟩ := denoteL_of_view h.ls (hel u (by simp))
    obtain ⟨as, has⟩ := ih (fun c hc => hel c (by simp [hc]))
    exact ⟨a :: as, by simp [denoteLList, ha, has, opt2]⟩

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

theorem PMemoOK.insertLs {m : PMemo} {st : EStore} (hm : PMemoOK m st) {h r : LsIdx}
    {x : List Level} (hp : PersLs r) (hh : denoteLs st.lss h = some x)
    (hr : denoteLs st.lss r = some x) :
    PMemoOK { m with lsM := m.lsM.insert h r } st := by
  refine ⟨hm.eM, hm.nM, hm.lM, ?_⟩
  intro k r' hk
  simp only [Std.HashMap.getElem?_insert] at hk
  split at hk
  · rename_i he
    obtain rfl := Option.some.inj hk
    obtain rfl := eq_of_beq he
    exact ⟨hp, x, hh, hr⟩
  · exact hm.lsM k r' hk

/-- con-leche: none — arena infrastructure; **the level-list promotion, run
forwards**. -/
theorem promoteLs_step {m m' : PMemo} {fuel : Nat} {h r : LsIdx} {s s' : AState}
    (hwf : StoreWF' s.store) (hm : PMemoOK m s.store)
    (hrun : promoteLs m fuel h s = .ok ((m', r), s')) :
    StoreWF' s'.store ∧ PMemoOK m' s'.store ∧ Ext s.store s'.store ∧ PersLs r ∧
      (∀ x, denoteLs s.store.lss h = some x → denoteLs s'.store.lss r = some x) := by
  have hx : Ext s.store s'.store := (promoteLs_aext m fuel h s (m', r) s' hrun).ext
  refine (fun (H : StoreWF' s'.store ∧ PMemoOK m' s'.store ∧ PersLs r ∧
      (∀ x, denoteLs s.store.lss h = some x → denoteLs s'.store.lss r = some x)) =>
    ⟨H.1, H.2.1, hx, H.2.2⟩) ?_
  unfold promoteLs at hrun
  rcases AM.ite_ok hrun with ⟨hp, hrun⟩ | ⟨hp, hrun⟩
  · obtain ⟨hr, rfl⟩ := AM.pure_ok hrun
    simp only [Prod.mk.injEq] at hr
    obtain ⟨rfl, rfl⟩ := hr
    exact ⟨hwf, hm, hp, fun _ hx => hx⟩
  · cases hmemo : m.lsM[h]? with
    | some r0 =>
      simp only [hmemo] at hrun
      obtain ⟨hr, rfl⟩ := AM.pure_ok hrun
      simp only [Prod.mk.injEq] at hr
      obtain ⟨rfl, rfl⟩ := hr
      obtain ⟨hpr, x0, hx0, hr0⟩ := hm.lsM h _ hmemo
      refine ⟨hwf, hm, hpr, fun x hx => ?_⟩
      rw [hx0] at hx; obtain rfl := Option.some.inj hx; exact hr0
    | none =>
      simp only [hmemo] at hrun
      obtain ⟨us, s1, hv, h1⟩ := AM.bind_ok hrun
      obtain ⟨rfl, hview⟩ := viewLs_ok hv
      obtain ⟨xs, hxs⟩ := denoteLs_of_view hwf.lssWF hview
      have hden : denoteLs s1.store.lss h = some xs := by
        simp only [denoteLs, hview]; exact hxs
      obtain ⟨⟨m2, us2⟩, s2, h2, h3⟩ := AM.bind_ok h1
      obtain ⟨hwf2, hm2, hx12, hp2, -, hd2⟩ := promoteLList_step us hwf hm h2
      obtain ⟨r2, s3, h4, h5⟩ := AM.bind_ok h3
      obtain ⟨hr, rfl⟩ := AM.pure_ok h5
      simp only [Prod.mk.injEq] at hr
      obtain ⟨rfl, rfl⟩ := hr
      have hl2 : denoteLList s2.store.lss.ls us2 = some xs := hd2 xs hxs
      obtain ⟨hwf3, hview3, hp3⟩ := internPersistentLs_run hwf2
        (LsStore.ViewOK.of_denoteLList hl2) hp2 h4
      have hx23 : Ext s2.store s'.store := (internPersistentLs_aext h4).ext
      have hd3 : denoteLs s'.store.lss r = some xs := by
        simp only [denoteLs, hview3]
        exact denoteLList_ext hx23.lss.ls us2 xs hl2
      refine ⟨hwf3, ?_, hp3, ?_⟩
      · exact (hm2.mono hx23).insertLs hp3 ((hx12.trans hx23).lss.lst _ _ hden) hd3
      · intro x hx; rw [hden] at hx; obtain rfl := Option.some.inj hx; exact hd3

/-! ## `promoteE` -/

theorem denoteE_of_view' {st : EStore} {rk : EIdx → Nat} (h : EWFAt' st rk) :
    ∀ (n : Nat) (i : EIdx), rk i < n → (st.view i).isSome = true →
      ∃ x, denoteE st i = some x := by
  have hN : ∀ {c : NIdx}, (st.ns.view c).isSome = true → ∃ x, denoteN st.ns c = some x :=
    fun hc => denoteN_of_view h.nsWF hc
  have hL : ∀ {c : LIdx}, (st.ls.view c).isSome = true → ∃ x, denoteL st.ls c = some x :=
    fun hc => denoteL_of_view h.lsWF hc
  have hLs : ∀ {c : LsIdx}, (st.lss.view c).isSome = true →
      ∃ x, denoteLs st.lss c = some x := by
    intro c hc
    obtain ⟨us, hus⟩ := Option.isSome_iff_exists.mp hc
    obtain ⟨xs, hxs⟩ := denoteLs_of_view h.lssWF hus
    exact ⟨xs, by simp only [denoteLs, hus]; exact hxs⟩
  intro n
  induction n with
  | zero => intro i hn; omega
  | succ n ih =>
    intro i hn hv
    obtain ⟨v, hv'⟩ := Option.isSome_iff_exists.mp hv
    have hE : ∀ c ∈ v.echildren, ∃ x, denoteE st c = some x := by
      intro c hc
      have := h.childOK i v hv' c hc
      exact ih c (by omega) this.1
    rw [denoteE_unfold' h hv']
    cases v with
    | bvar k => exact ⟨_, rfl⟩
    | lit l => exact ⟨_, rfl⟩
    | fvar k ty =>
      obtain ⟨a, ha⟩ := hE ty (by simp [ENodeView.echildren])
      exact ⟨.fvar k a, by simp [denoteEView, ha]⟩
    | sort u =>
      obtain ⟨a, ha⟩ := hL (h.lchildOK i _ hv' u (by simp [ENodeView.lchildren])).1
      exact ⟨.sort a, by simp [denoteEView, ha]⟩
    | const c us =>
      obtain ⟨a, ha⟩ := hN (h.nchildOK i _ hv' c (by simp [ENodeView.nchildren])).1
      obtain ⟨b, hb⟩ := hLs (h.lschildOK i _ hv' us (by simp [ENodeView.lschildren])).1
      exact ⟨.const a b, by simp [denoteEView, ha, hb, opt2]⟩
    | app f a =>
      obtain ⟨x, hx⟩ := hE f (by simp [ENodeView.echildren])
      obtain ⟨y, hy⟩ := hE a (by simp [ENodeView.echildren])
      exact ⟨.app x y, by simp [denoteEView, hx, hy, opt2]⟩
    | lam ty b m =>
      obtain ⟨x, hx⟩ := hE ty (by simp [ENodeView.echildren])
      obtain ⟨y, hy⟩ := hE b (by simp [ENodeView.echildren])
      exact ⟨.lam x y m, by simp [denoteEView, hx, hy, opt2]⟩
    | forallE ty b m =>
      obtain ⟨x, hx⟩ := hE ty (by simp [ENodeView.echildren])
      obtain ⟨y, hy⟩ := hE b (by simp [ENodeView.echildren])
      exact ⟨.forallE x y m, by simp [denoteEView, hx, hy, opt2]⟩
    | letE ty w b =>
      obtain ⟨x, hx⟩ := hE ty (by simp [ENodeView.echildren])
      obtain ⟨y, hy⟩ := hE w (by simp [ENodeView.echildren])
      obtain ⟨z, hz⟩ := hE b (by simp [ENodeView.echildren])
      exact ⟨.letE x y z, by simp [denoteEView, hx, hy, hz, opt3]⟩
    | proj c k e =>
      obtain ⟨a, ha⟩ := hN (h.nchildOK i _ hv' c (by simp [ENodeView.nchildren])).1
      obtain ⟨x, hx⟩ := hE e (by simp [ENodeView.echildren])
      exact ⟨.proj a k x, by simp [denoteEView, ha, hx, opt2]⟩

theorem denoteE_of_view {st : EStore} (h : StoreWF' st) {i : EIdx}
    (hv : (st.view i).isSome = true) : ∃ x, denoteE st i = some x := by
  obtain ⟨rk, h⟩ := h
  exact denoteE_of_view' h _ i (Nat.lt_succ_self _) hv

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

theorem internPersistentE_run {v : ENodeView} {s : AState} {r : EIdx} {s' : AState}
    (hwf : StoreWF' s.store) (hv : s.store.ViewOK v) (hp : EViewPers v)
    (h : internPersistentE v s = .ok (r, s')) :
    StoreWF' s'.store ∧ s'.store.view r = some v ∧ PersE r := by
  -- audit D3: the wrapper runs in the Rust's order, and its success says the
  -- Rust's two miss-path capacity tests held (`Arena.internPersistentE_ok`)
  obtain ⟨hb, hn, rfl, rfl⟩ := Arena.internPersistentE_ok h
  exact EStore.internPersistent_spec' hwf hv hp hb hn

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
  | app f a | lam f a _ | forallE f a _ =>
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

theorem promoteE_node {s s' : AState} {w : ENodeView} {r : EIdx} {x : Expr}
    (hwf : StoreWF' s.store) (hd : denoteEView s.store w = some x)
    (hp : EViewPers w) (hrun : internPersistentE w s = .ok (r, s')) :
    StoreWF' s'.store ∧ Ext s.store s'.store ∧ PersE r ∧
      denoteE s'.store r = some x := by
  obtain ⟨hwf', hview, hpers⟩ :=
    internPersistentE_run hwf (EStore.ViewOK.of_denoteEView hd) hp hrun
  have hx : Ext s.store s'.store := (internPersistentE_aext hrun).ext
  obtain ⟨rk, hw⟩ := hwf'
  refine ⟨⟨rk, hw⟩, hx, hpers, ?_⟩
  rw [denoteE_unfold' hw hview]
  exact denoteEView_ext hd hx

theorem PMemoOK.insertE {m : PMemo} {st : EStore} (hm : PMemoOK m st) {h r : EIdx}
    {x : Expr} (hp : PersE r) (hh : denoteE st h = some x)
    (hr : denoteE st r = some x) :
    PMemoOK { m with eM := m.eM.insert h r } st := by
  refine ⟨?_, hm.nM, hm.lM, hm.lsM⟩
  intro k r' hk
  simp only [Std.HashMap.getElem?_insert] at hk
  split at hk
  · rename_i he
    obtain rfl := Option.some.inj hk
    obtain rfl := eq_of_beq he
    exact ⟨hp, x, hh, hr⟩
  · exact hm.eM k r' hk

/-- con-leche: none — arena infrastructure; **the expression promotion, run
forwards** — `Arena/Promote.lean`'s "`denote (promote h) = denote h` is the
exactness lemma P3 owes", with the invariant and the memo carried through. -/
theorem promoteE_core : ∀ (fuel : Nat) (m : PMemo) (h : EIdx) (s : AState)
    (m' : PMemo) (r : EIdx) (s' : AState),
    StoreWF' s.store → PMemoOK m s.store →
    promoteE m fuel h s = .ok ((m', r), s') →
    StoreWF' s'.store ∧ PMemoOK m' s'.store ∧ PersE r ∧
      (∀ x, denoteE s.store h = some x → denoteE s'.store r = some x) := by
  intro fuel
  induction fuel with
  | zero =>
    intro m h s m' r s' _ _ hrun
    simp only [promoteE, ConRon.Bridge.fail_apply] at hrun
    exact absurd hrun (by simp)
  | succ fuel ih =>
    intro m h s m' r s' hwf hm hrun
    have ihs : ∀ {m m' : PMemo} {h r : EIdx} {s s' : AState},
        StoreWF' s.store → PMemoOK m s.store →
        promoteE m fuel h s = .ok ((m', r), s') →
        StoreWF' s'.store ∧ PMemoOK m' s'.store ∧ Ext s.store s'.store ∧ PersE r ∧
          (∀ x, denoteE s.store h = some x → denoteE s'.store r = some x) := by
      intro m m' h r s s' hwf hm hrun
      obtain ⟨a, b, c, d⟩ := ih m h s m' r s' hwf hm hrun
      exact ⟨a, b, (promoteE_aext m fuel h s (m', r) s' hrun).ext, c, d⟩
    unfold promoteE at hrun
    rcases AM.ite_ok hrun with ⟨hp, hrun⟩ | ⟨hp, hrun⟩
    · obtain ⟨hr, rfl⟩ := AM.pure_ok hrun
      simp only [Prod.mk.injEq] at hr
      obtain ⟨rfl, rfl⟩ := hr
      exact ⟨hwf, hm, hp, fun _ hx => hx⟩
    · cases hmemo : m.eM[h]? with
      | some r0 =>
        simp only [hmemo] at hrun
        obtain ⟨hr, rfl⟩ := AM.pure_ok hrun
        simp only [Prod.mk.injEq] at hr
        obtain ⟨rfl, rfl⟩ := hr
        obtain ⟨hpr, x0, hx0, hr0⟩ := hm.eM h _ hmemo
        refine ⟨hwf, hm, hpr, fun x hx => ?_⟩
        rw [hx0] at hx; obtain rfl := Option.some.inj hx; exact hr0
      | none =>
        simp only [hmemo] at hrun
        obtain ⟨v, s1, hv, h1⟩ := AM.bind_ok hrun
        obtain ⟨rfl, hview⟩ := view_ok hv
        obtain ⟨x0, hx0⟩ := denoteE_of_view hwf (by rw [hview]; rfl)
        have hden : denoteE s1.store h = denoteEView s1.store v := by
          obtain ⟨rk, hw⟩ := hwf; exact denoteE_unfold' hw hview
        have fin : ∀ (m1 : PMemo) (r1 : EIdx) (s2 : AState),
            StoreWF' s2.store → PMemoOK m1 s2.store → Ext s1.store s2.store →
            PersE r1 → denoteE s2.store r1 = some x0 →
            (m', r) = ({ m1 with eM := m1.eM.insert h r1 }, r1) → s' = s2 →
            StoreWF' s'.store ∧ PMemoOK m' s'.store ∧ PersE r ∧
              (∀ x, denoteE s1.store h = some x → denoteE s'.store r = some x) := by
          intro m1 r1 s2 hwf2 hm2 hx2 hp2 hd2 hr hs
          simp only [Prod.mk.injEq] at hr
          obtain ⟨rfl, rfl⟩ := hr
          subst hs
          refine ⟨hwf2, hm2.insertE hp2 (hx2.expr _ _ hx0) hd2, hp2, ?_⟩
          intro x hx; rw [hx0] at hx; obtain rfl := Option.some.inj hx; exact hd2
        rw [hden] at hx0
        cases v with
        | bvar i =>
          obtain ⟨r2, s3, h3, h4⟩ := AM.bind_ok h1
          obtain ⟨hr, rfl⟩ := AM.pure_ok (AM.pure_bind_ok h4)
          obtain ⟨hwf3, hx3, hp3, hd3⟩ := promoteE_node hwf hx0
            ⟨by simp [ENodeView.echildren], by simp [ENodeView.nchildren],
              by simp [ENodeView.lchildren], by simp [ENodeView.lschildren]⟩ h3
          exact fin m r2 _ hwf3 (hm.mono hx3) hx3 hp3 hd3 hr rfl
        | fvar k ty =>
          have hx0' := hx0
          simp only [denoteEView, Option.map_eq_some_iff] at hx0'
          obtain ⟨et, het, hxe⟩ := hx0'
          obtain ⟨⟨m2, t2⟩, s3, h3, h4⟩ := AM.bind_ok h1
          obtain ⟨hwf3, hm3, hx13, hpt, hdt⟩ := ihs hwf hm h3
          obtain ⟨r2, s4, h5, h6⟩ := AM.bind_ok h4
          obtain ⟨hr, rfl⟩ := AM.pure_ok (AM.pure_bind_ok h6)
          have ht3 : denoteE s3.store t2 = some et := hdt et het
          obtain ⟨hwf4, hx4, hp4, hd4⟩ := promoteE_node hwf3
            (w := .fvar k t2) (x := x0) (by simp [denoteEView, ht3, hxe])
            ⟨by simp [ENodeView.echildren, hpt], by simp [ENodeView.nchildren],
              by simp [ENodeView.lchildren], by simp [ENodeView.lschildren]⟩ h5
          exact fin m2 r2 _ hwf4 (hm3.mono hx4) (hx13.trans hx4) hp4 hd4 hr rfl
        | sort u =>
          have hx0' := hx0
          simp only [denoteEView, Option.map_eq_some_iff] at hx0'
          obtain ⟨a, ha, hxe⟩ := hx0'
          obtain ⟨⟨m2, u2⟩, s3, h3, h4⟩ := AM.bind_ok h1
          obtain ⟨hwf3, hm3, hx13, hpu, hdu⟩ := promoteL_step hwf hm h3
          obtain ⟨r2, s4, h5, h6⟩ := AM.bind_ok h4
          obtain ⟨hr, rfl⟩ := AM.pure_ok (AM.pure_bind_ok h6)
          have hu3 : denoteL s3.store.ls u2 = some a := hdu a ha
          obtain ⟨hwf4, hx4, hp4, hd4⟩ := promoteE_node hwf3
            (w := .sort u2) (x := x0) (by simp [denoteEView, hu3, hxe])
            ⟨by simp [ENodeView.echildren], by simp [ENodeView.nchildren],
              by simp [ENodeView.lchildren, hpu], by simp [ENodeView.lschildren]⟩ h5
          exact fin m2 r2 _ hwf4 (hm3.mono hx4) (hx13.trans hx4) hp4 hd4 hr rfl
        | const n us =>
          have hx0' := hx0
          simp only [denoteEView, opt2_eq_some_iff] at hx0'
          obtain ⟨a, b, ha, hb, hxe⟩ := hx0'
          obtain ⟨⟨m2, n2⟩, s3, h3, h4⟩ := AM.bind_ok h1
          obtain ⟨hwf3, hm3, hx13, hpn, hdn⟩ := promoteN_step hwf hm h3
          obtain ⟨⟨m3, us2⟩, s4, h5, h6⟩ := AM.bind_ok h4
          obtain ⟨hwf4, hm4, hx34, hpus, hdus⟩ := promoteLs_step hwf3 hm3 h5
          obtain ⟨r2, s5, h7, h8⟩ := AM.bind_ok h6
          obtain ⟨hr, rfl⟩ := AM.pure_ok (AM.pure_bind_ok h8)
          have hn4 : denoteN s4.store.ns n2 = some a := hx34.lss.ls.ns _ _ (hdn a ha)
          have hus4 : denoteLs s4.store.lss us2 = some b := hdus b (hx13.lss.lst _ _ hb)
          obtain ⟨hwf5, hx5, hp5, hd5⟩ := promoteE_node hwf4
            (w := .const n2 us2) (x := x0) (by simp [denoteEView, hn4, hus4, opt2, hxe])
            ⟨by simp [ENodeView.echildren], by simp [ENodeView.nchildren, hpn],
              by simp [ENodeView.lchildren], by simp [ENodeView.lschildren, hpus]⟩ h7
          exact fin m3 r2 _ hwf5 (hm4.mono hx5) ((hx13.trans hx34).trans hx5) hp5 hd5 hr rfl
        | app a b =>
          have hx0' := hx0
          simp only [denoteEView, opt2_eq_some_iff] at hx0'
          obtain ⟨ea, eb, hea, heb, hxe⟩ := hx0'
          obtain ⟨⟨m2, a2⟩, s3, h3, h4⟩ := AM.bind_ok h1
          obtain ⟨hwf3, hm3, hx13, hpa, hda⟩ := ihs hwf hm h3
          obtain ⟨⟨m3, b2⟩, s4, h5, h6⟩ := AM.bind_ok h4
          obtain ⟨hwf4, hm4, hx34, hpb, hdb⟩ := ihs hwf3 hm3 h5
          obtain ⟨r2, s5, h7, h8⟩ := AM.bind_ok h6
          obtain ⟨hr, rfl⟩ := AM.pure_ok (AM.pure_bind_ok h8)
          have ha4 : denoteE s4.store a2 = some ea := hx34.expr _ _ (hda ea hea)
          have hb4 : denoteE s4.store b2 = some eb := hdb eb (hx13.expr _ _ heb)
          obtain ⟨hwf5, hx5, hp5, hd5⟩ := promoteE_node hwf4
            (w := .app a2 b2) (x := x0) (by simp [denoteEView, ha4, hb4, opt2, hxe])
            ⟨by simp [ENodeView.echildren, hpa, hpb], by simp [ENodeView.nchildren],
              by simp [ENodeView.lchildren], by simp [ENodeView.lschildren]⟩ h7
          exact fin m3 r2 _ hwf5 (hm4.mono hx5) ((hx13.trans hx34).trans hx5) hp5 hd5 hr rfl
        | lam a b bm =>
          have hx0' := hx0
          simp only [denoteEView, opt2_eq_some_iff] at hx0'
          obtain ⟨ea, eb, hea, heb, hxe⟩ := hx0'
          obtain ⟨⟨m2, a2⟩, s3, h3, h4⟩ := AM.bind_ok h1
          obtain ⟨hwf3, hm3, hx13, hpa, hda⟩ := ihs hwf hm h3
          obtain ⟨⟨m3, b2⟩, s4, h5, h6⟩ := AM.bind_ok h4
          obtain ⟨hwf4, hm4, hx34, hpb, hdb⟩ := ihs hwf3 hm3 h5
          obtain ⟨r2, s5, h7, h8⟩ := AM.bind_ok h6
          obtain ⟨hr, rfl⟩ := AM.pure_ok (AM.pure_bind_ok h8)
          have ha4 : denoteE s4.store a2 = some ea := hx34.expr _ _ (hda ea hea)
          have hb4 : denoteE s4.store b2 = some eb := hdb eb (hx13.expr _ _ heb)
          obtain ⟨hwf5, hx5, hp5, hd5⟩ := promoteE_node hwf4
            (w := .lam a2 b2 bm) (x := x0) (by simp [denoteEView, ha4, hb4, opt2, hxe])
            ⟨by simp [ENodeView.echildren, hpa, hpb], by simp [ENodeView.nchildren],
              by simp [ENodeView.lchildren], by simp [ENodeView.lschildren]⟩ h7
          exact fin m3 r2 _ hwf5 (hm4.mono hx5) ((hx13.trans hx34).trans hx5) hp5 hd5 hr rfl
        | forallE a b bm =>
          have hx0' := hx0
          simp only [denoteEView, opt2_eq_some_iff] at hx0'
          obtain ⟨ea, eb, hea, heb, hxe⟩ := hx0'
          obtain ⟨⟨m2, a2⟩, s3, h3, h4⟩ := AM.bind_ok h1
          obtain ⟨hwf3, hm3, hx13, hpa, hda⟩ := ihs hwf hm h3
          obtain ⟨⟨m3, b2⟩, s4, h5, h6⟩ := AM.bind_ok h4
          obtain ⟨hwf4, hm4, hx34, hpb, hdb⟩ := ihs hwf3 hm3 h5
          obtain ⟨r2, s5, h7, h8⟩ := AM.bind_ok h6
          obtain ⟨hr, rfl⟩ := AM.pure_ok (AM.pure_bind_ok h8)
          have ha4 : denoteE s4.store a2 = some ea := hx34.expr _ _ (hda ea hea)
          have hb4 : denoteE s4.store b2 = some eb := hdb eb (hx13.expr _ _ heb)
          obtain ⟨hwf5, hx5, hp5, hd5⟩ := promoteE_node hwf4
            (w := .forallE a2 b2 bm) (x := x0) (by simp [denoteEView, ha4, hb4, opt2, hxe])
            ⟨by simp [ENodeView.echildren, hpa, hpb], by simp [ENodeView.nchildren],
              by simp [ENodeView.lchildren], by simp [ENodeView.lschildren]⟩ h7
          exact fin m3 r2 _ hwf5 (hm4.mono hx5) ((hx13.trans hx34).trans hx5) hp5 hd5 hr rfl
        | letE a b c =>
          have hx0' := hx0
          simp only [denoteEView, opt3_eq_some_iff] at hx0'
          obtain ⟨ea, eb, ec, hea, heb, hec, hxe⟩ := hx0'
          obtain ⟨⟨m2, a2⟩, s3, h3, h4⟩ := AM.bind_ok h1
          obtain ⟨hwf3, hm3, hx13, hpa, hda⟩ := ihs hwf hm h3
          obtain ⟨⟨m3, b2⟩, s4, h5, h6⟩ := AM.bind_ok h4
          obtain ⟨hwf4, hm4, hx34, hpb, hdb⟩ := ihs hwf3 hm3 h5
          obtain ⟨⟨m4, c2⟩, s5, h7, h8⟩ := AM.bind_ok h6
          obtain ⟨hwf5, hm5, hx45, hpc, hdc⟩ := ihs hwf4 hm4 h7
          obtain ⟨r2, s6, h9, h10⟩ := AM.bind_ok h8
          obtain ⟨hr, rfl⟩ := AM.pure_ok (AM.pure_bind_ok h10)
          have ha5 : denoteE s5.store a2 = some ea := hx45.expr _ _ (hx34.expr _ _ (hda ea hea))
          have hb5 : denoteE s5.store b2 = some eb := hx45.expr _ _ (hdb eb (hx13.expr _ _ heb))
          have hc5 : denoteE s5.store c2 = some ec :=
            hdc ec (hx34.expr _ _ (hx13.expr _ _ hec))
          obtain ⟨hwf6, hx6, hp6, hd6⟩ := promoteE_node hwf5
            (w := .letE a2 b2 c2) (x := x0) (by simp [denoteEView, ha5, hb5, hc5, opt3, hxe])
            ⟨by simp [ENodeView.echildren, hpa, hpb, hpc], by simp [ENodeView.nchildren],
              by simp [ENodeView.lchildren], by simp [ENodeView.lschildren]⟩ h9
          exact fin m4 r2 _ hwf6 (hm5.mono hx6)
            (((hx13.trans hx34).trans hx45).trans hx6) hp6 hd6 hr rfl
        | lit l =>
          obtain ⟨r2, s3, h3, h4⟩ := AM.bind_ok h1
          obtain ⟨hr, rfl⟩ := AM.pure_ok (AM.pure_bind_ok h4)
          obtain ⟨hwf3, hx3, hp3, hd3⟩ := promoteE_node hwf hx0
            ⟨by simp [ENodeView.echildren], by simp [ENodeView.nchildren],
              by simp [ENodeView.lchildren], by simp [ENodeView.lschildren]⟩ h3
          exact fin m r2 _ hwf3 (hm.mono hx3) hx3 hp3 hd3 hr rfl
        | proj n k e =>
          have hx0' := hx0
          simp only [denoteEView, opt2_eq_some_iff] at hx0'
          obtain ⟨a, ee, ha, hee, hxe⟩ := hx0'
          obtain ⟨⟨m2, n2⟩, s3, h3, h4⟩ := AM.bind_ok h1
          obtain ⟨hwf3, hm3, hx13, hpn, hdn⟩ := promoteN_step hwf hm h3
          obtain ⟨⟨m3, e2⟩, s4, h5, h6⟩ := AM.bind_ok h4
          obtain ⟨hwf4, hm4, hx34, hpe, hde⟩ := ihs hwf3 hm3 h5
          obtain ⟨r2, s5, h7, h8⟩ := AM.bind_ok h6
          obtain ⟨hr, rfl⟩ := AM.pure_ok (AM.pure_bind_ok h8)
          have hn4 : denoteN s4.store.ns n2 = some a := hx34.lss.ls.ns _ _ (hdn a ha)
          have he4 : denoteE s4.store e2 = some ee := hde ee (hx13.expr _ _ hee)
          obtain ⟨hwf5, hx5, hp5, hd5⟩ := promoteE_node hwf4
            (w := .proj n2 k e2) (x := x0) (by simp [denoteEView, hn4, he4, opt2, hxe])
            ⟨by simp [ENodeView.echildren, hpe], by simp [ENodeView.nchildren, hpn],
              by simp [ENodeView.lchildren], by simp [ENodeView.lschildren]⟩ h7
          exact fin m3 r2 _ hwf5 (hm4.mono hx5) ((hx13.trans hx34).trans hx5) hp5 hd5 hr rfl

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
    · obtain ⟨hr, -⟩ := AM.pure_ok hrun
      simp only [Prod.mk.injEq] at hr
      exact hr.2
    · exact absurd hp hn

/-- con-leche: none — arena infrastructure; **what a promotion does to one
name handle**: it denotes what it denoted, and a persistent one did not
move. -/
structure NameKept (st st' : EStore) (n n' : NIdx) : Prop where
  denote : ∀ x, denoteN st.ns n = some x → denoteN st'.ns n' = some x
  pers : PersN n → n' = n

theorem NameKept.post {st st' st'' : EStore} {n n' : NIdx} (h : NameKept st st' n n')
    (hx : Ext st' st'') : NameKept st st'' n n' :=
  ⟨fun x hd => hx.lss.ls.ns _ _ (h.denote x hd), h.pers⟩

theorem NameKept.pre {st0 st st' : EStore} {n n' : NIdx} (h : NameKept st st' n n')
    (hx : Ext st0 st) : NameKept st0 st' n n' :=
  ⟨fun x hd => h.denote x (hx.lss.ls.ns _ _ hd), h.pers⟩

theorem promoteN_kept {m m' : PMemo} {fuel : Nat} {h r : NIdx} {s s' : AState}
    (hwf : StoreWF' s.store) (hm : PMemoOK m s.store)
    (hrun : promoteN m fuel h s = .ok ((m', r), s')) : NameKept s.store s'.store h r :=
  ⟨(promoteN_step hwf hm hrun).2.2.2.2, fun hp => promoteN_pers_self hp hrun⟩

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
