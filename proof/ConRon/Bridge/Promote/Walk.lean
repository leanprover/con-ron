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

theorem viewN_run {h : NIdx} {s s' : AState} {v : NNodeView}
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
        obtain ⟨rfl, hview⟩ := viewN_run hv
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

end ConRon.Bridge
