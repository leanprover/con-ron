/-
# `ConRon.Bridge.Promote.Proj` — a promotion's writes, at the persistent projection

A persistent intern changes nothing but a persistent table, and a view whose children
are persistent reads the same derived words with or without the scratch tier.  So it
commutes with `dropScratch` (`internPersistent_dropScratch` and its lifts): the
projection of the store it wrote is the projection it would have written, and the
well-formedness of a store with its scratch tier gone is the existing theorems'
(`StoreWF'.dropScratch_wf`), with nothing asked of the scratch tier.

`PSrc`'s two constructors are here: `PSrc.self` (the source is the projection) and
`PSrc.of_run` (the source is where a scratch run ended, the store is that state framed,
`Arena/Promote.lean`'s `scratchRun`).
-/
module

public import ConRon.Bridge.Promote.Memo
import ConRon.Bridge.Promote.Weak
import ConRon.Bridge.Rel
import ConRon.Arena.PersistentRun
import ConRon.Arena.WFProofs

public section

namespace ConRon.Bridge

set_option autoImplicit false

open ConLeche ConRon.Arena

/-! ## The projection is idempotent -/

/-- con-leche: none — arena infrastructure; dropping a dropped tier changes nothing. -/
theorem EStore.dropScratch_idem (st : EStore) : st.dropScratch.dropScratch = st.dropScratch :=
  rfl

/-! ## A persistent intern, at the projection -/

/-- con-leche: none — arena infrastructure; a name view with persistent children
interns the same with or without the scratch tier. -/
theorem NStore.internPersistent_dropScratch (st : NStore) (v : NNodeView) (hp : NViewPers v) :
    st.dropScratch.internPersistent v =
      ((st.internPersistent v).1.dropScratch, (st.internPersistent v).2) := by
  have hd : st.dropScratch.derOfView v = st.derOfView v :=
    NStore.derOfView_congr fun c hc => NStore.derived_dropScratch_pers st (hp c hc)
  simp only [NStore.internPersistent, NStore.dropScratch] at hd ⊢
  split <;> simp_all

/-- con-leche: none — arena infrastructure; the same at a level view. -/
theorem LStore.internPersistent_dropScratch (st : LStore) (v : LNodeView) (hp : LViewPers v) :
    st.dropScratch.internPersistent v =
      ((st.internPersistent v).1.dropScratch, (st.internPersistent v).2) := by
  have hd : st.dropScratch.derOfView v = st.derOfView v :=
    LStore.derOfView_congr (fun c hc => LStore.derived_dropScratch_pers st (hp.lvl c hc))
      (fun c hc => NStore.derived_dropScratch_pers st.ns (hp.nm c hc))
  simp only [LStore.internPersistent, LStore.dropScratch] at hd ⊢
  split <;> simp_all

/-- con-leche: none — arena infrastructure; the same at a level-list view. -/
theorem LsStore.internPersistent_dropScratch (st : LsStore) (v : LsNodeView)
    (hp : LsViewPers v) :
    st.dropScratch.internPersistent v =
      ((st.internPersistent v).1.dropScratch, (st.internPersistent v).2) := by
  have hd : st.dropScratch.derOfView v = st.derOfView v :=
    LsStore.derOfView_congr v fun c hc => LStore.derived_dropScratch_pers st.ls (hp c hc)
  simp only [LsStore.internPersistent, LsStore.dropScratch] at hd ⊢
  split <;> simp_all

/-- con-leche: none — arena infrastructure; the same at an expression view. -/
theorem EStore.internPersistent_dropScratch (st : EStore) (v : ENodeView) (hp : EViewPers v) :
    st.dropScratch.internPersistent v =
      ((st.internPersistent v).1.dropScratch, (st.internPersistent v).2) := by
  have hd : st.dropScratch.derOfView v = st.derOfView v :=
    EStore.derOfView_congr
      (fun c hc => by
        show (st.dropScratch).derived c = st.derived c
        rw [EStore.derived_pers (hp.expr c hc), EStore.derived_pers (hp.expr c hc)]; rfl)
      (fun c hc => NStore.derived_dropScratch_pers st.ns (hp.nm c hc))
      (fun c hc => LStore.derived_dropScratch_pers st.ls (hp.lvl c hc))
      (fun c hc => by
        show (st.lss.dropScratch).derived c = st.lss.derived c
        rw [LsStore.derived_pers (hp.lst c hc), LsStore.derived_pers (hp.lst c hc)]; rfl)
  simp only [EStore.internPersistent, EStore.dropScratch] at hd ⊢
  split <;> simp_all

/-- con-leche: none — arena infrastructure; `NStore.internPersistent_dropScratch`,
through the nesting. -/
theorem EStore.internNamePersistent_dropScratch (st : EStore) (v : NNodeView) (hp : NViewPers v) :
    st.dropScratch.internNamePersistent v =
      ((st.internNamePersistent v).1.dropScratch, (st.internNamePersistent v).2) := by
  have h := NStore.internPersistent_dropScratch st.ns v hp
  have h2 := congrArg Prod.snd h
  refine Prod.ext ?_ h2
  exact congrArg (fun ns : NStore => ({ st.dropScratch with
    lss := { st.dropScratch.lss with ls := { st.dropScratch.ls with ns := ns } } } : EStore))
    (congrArg Prod.fst h)

/-- con-leche: none — arena infrastructure; `LStore.internPersistent_dropScratch`,
through the nesting. -/
theorem EStore.internLevelPersistent_dropScratch (st : EStore) (v : LNodeView) (hp : LViewPers v) :
    st.dropScratch.internLevelPersistent v =
      ((st.internLevelPersistent v).1.dropScratch, (st.internLevelPersistent v).2) := by
  have h := LStore.internPersistent_dropScratch st.ls v hp
  have h2 := congrArg Prod.snd h
  refine Prod.ext ?_ h2
  exact congrArg (fun ls : LStore => ({ st.dropScratch with
    lss := { st.dropScratch.lss with ls := ls } } : EStore)) (congrArg Prod.fst h)

/-- con-leche: none — arena infrastructure; `LsStore.internPersistent_dropScratch`,
through the nesting. -/
theorem EStore.internLevelsPersistent_dropScratch (st : EStore) (v : LsNodeView)
    (hp : LsViewPers v) :
    st.dropScratch.internLevelsPersistent v =
      ((st.internLevelsPersistent v).1.dropScratch, (st.internLevelsPersistent v).2) := by
  have h := LsStore.internPersistent_dropScratch st.lss v hp
  have h2 := congrArg Prod.snd h
  refine Prod.ext ?_ h2
  exact congrArg (fun lss : LsStore => ({ st.dropScratch with lss := lss } : EStore))
    (congrArg Prod.fst h)

/-! ## A persistent intern leaves the scratch tier alone -/

/-- con-leche: none — arena infrastructure; a scratch handle the store reads, it
still reads the same after the step. -/
structure ScrSame (st st' : EStore) : Prop where
  e : ∀ i v, i.isPersistent = false → st.view i = some v → st'.view i = some v
  ls : ∀ i v, i.isPersistent = false → st.lss.view i = some v → st'.lss.view i = some v
  l : ∀ i v, i.isPersistent = false → st.ls.view i = some v → st'.ls.view i = some v
  n : ∀ i v, i.isPersistent = false → st.ns.view i = some v → st'.ns.view i = some v

/-- con-leche: none — arena infrastructure; a persistent name intern, at a scratch
handle. -/
theorem NStore.view_internPersistent_scr (st : NStore) (w : NNodeView) {i : NIdx}
    (hi : i.isPersistent = false) : (st.internPersistent w).1.view i = st.view i := by
  rcases NStore.internPersistent_cases st w with he | he <;> rw [he]
  simp [NStore.view, hi]

/-- con-leche: none — arena infrastructure; a persistent level intern, at a scratch
handle. -/
theorem LStore.view_internPersistent_scr (st : LStore) (w : LNodeView) {i : LIdx}
    (hi : i.isPersistent = false) : (st.internPersistent w).1.view i = st.view i := by
  rcases LStore.internPersistent_cases st w with he | he <;> rw [he]
  simp [LStore.view, hi]

/-- con-leche: none — arena infrastructure; a persistent level-list intern, at a
scratch handle. -/
theorem LsStore.view_internPersistent_scr (st : LsStore) (w : LsNodeView) {i : LsIdx}
    (hi : i.isPersistent = false) : (st.internPersistent w).1.view i = st.view i := by
  rcases LsStore.internPersistent_cases st w with he | he <;> rw [he]
  simp [LsStore.view, hi]

/-- con-leche: none — arena infrastructure; a persistent expression intern, at a
scratch handle. -/
theorem EStore.view_internPersistent_scr (st : EStore) (w : ENodeView) {i : EIdx}
    (hi : i.isPersistent = false) : (st.internPersistent w).1.view i = st.view i := by
  rcases EStore.internPersistent_cases st w with he | he <;> rw [he]
  simp [EStore.view, hi]

/-- con-leche: none — arena infrastructure; `ScrSame` across an expression intern. -/
theorem ScrSame.internPersistent (st : EStore) (w : ENodeView) :
    ScrSame st (st.internPersistent w).1 where
  e := fun i v hi h => by rw [EStore.view_internPersistent_scr st w hi]; exact h
  ls := fun i v _ h => by rw [EStore.lss_internPersistent]; exact h
  l := fun i v _ h => by
    show (st.internPersistent w).1.lss.ls.view i = some v
    rw [EStore.lss_internPersistent]; exact h
  n := fun i v _ h => by
    show (st.internPersistent w).1.lss.ls.ns.view i = some v
    rw [EStore.lss_internPersistent]; exact h

/-- con-leche: none — arena infrastructure; `ScrSame` across a name intern. -/
theorem ScrSame.internNamePersistent (st : EStore) (w : NNodeView) :
    ScrSame st (st.internNamePersistent w).1 where
  e := fun _ _ _ h => h
  ls := fun _ _ _ h => h
  l := fun _ _ _ h => h
  n := fun i v hi h => by
    show (st.ns.internPersistent w).1.view i = some v
    rw [NStore.view_internPersistent_scr st.ns w hi]; exact h

/-- con-leche: none — arena infrastructure; `ScrSame` across a level intern. -/
theorem ScrSame.internLevelPersistent (st : EStore) (w : LNodeView) :
    ScrSame st (st.internLevelPersistent w).1 where
  e := fun _ _ _ h => h
  ls := fun _ _ _ h => h
  l := fun i v hi h => by
    show (st.ls.internPersistent w).1.view i = some v
    rw [LStore.view_internPersistent_scr st.ls w hi]; exact h
  n := fun i v _ h => by
    show (st.ls.internPersistent w).1.ns.view i = some v
    rw [LStore.ns_internPersistent]; exact h

/-- con-leche: none — arena infrastructure; `ScrSame` across a level-list intern. -/
theorem ScrSame.internLevelsPersistent (st : EStore) (w : LsNodeView) :
    ScrSame st (st.internLevelsPersistent w).1 where
  e := fun _ _ _ h => h
  ls := fun i v hi h => by
    show (st.lss.internPersistent w).1.view i = some v
    rw [LsStore.view_internPersistent_scr st.lss w hi]; exact h
  l := fun i v _ h => by
    show (st.lss.internPersistent w).1.ls.view i = some v
    rw [LsStore.ls_internPersistent]; exact h
  n := fun i v _ h => by
    show (st.lss.internPersistent w).1.ls.ns.view i = some v
    rw [LsStore.ls_internPersistent]; exact h

/-- con-leche: none — arena infrastructure; **a step `PSrc` survives**: the projection
stayed well formed and only grew, and the scratch tier stood still. -/
theorem PSrc.step {src st st' : EStore} (h : PSrc src st) (hwf : StoreWF st'.dropScratch)
    (hx : Ext st.dropScratch st'.dropScratch) (hs : ScrSame st st') : PSrc src st' where
  piWF := hwf
  srcWF := h.srcWF
  scrE := fun i v hi hv => hs.e i v hi (h.scrE i v hi hv)
  scrLs := fun i v hi hv => hs.ls i v hi (h.scrLs i v hi hv)
  scrL := fun i v hi hv => hs.l i v hi (h.scrL i v hi hv)
  scrN := fun i v hi hv => hs.n i v hi (h.scrN i v hi hv)
  persE := fun i x hi hd => hx.expr i x (h.persE i x hi hd)
  persLs := fun i x hi hd => hx.lss.lst i x (h.persLs i x hi hd)
  persL := fun i x hi hd => hx.lss.ls.lvl i x (h.persL i x hi hd)
  persN := fun i x hi hd => hx.lss.ls.ns i x (h.persN i x hi hd)

/-! ## The four promote-interns, run forwards at the projection -/

/-- con-leche: none — arena infrastructure; a cons hit interns nothing. -/
theorem EStore.internNamePersistent_hit {st : EStore} {v : NNodeView} {i : NIdx}
    (hf : st.ns.pers.find? v = some i) : st.internNamePersistent v = (st, i) := by
  have he : st.lss.ls.ns.internPersistent v = (st.lss.ls.ns, i) := by
    simp only [NStore.internPersistent]; rw [show st.lss.ls.ns.pers.find? v = some i from hf]
  simp only [EStore.internNamePersistent, LsStore.internNamePersistent,
    LStore.internNamePersistent, he]

/-- con-leche: none — arena infrastructure; a cons hit interns nothing. -/
theorem EStore.internLevelPersistent_hit {st : EStore} {v : LNodeView} {i : LIdx}
    (hf : st.ls.pers.find? v = some i) : st.internLevelPersistent v = (st, i) := by
  have he : st.lss.ls.internPersistent v = (st.lss.ls, i) := by
    simp only [LStore.internPersistent]; rw [show st.lss.ls.pers.find? v = some i from hf]
  simp only [EStore.internLevelPersistent, LsStore.internLevelPersistent, he]

/-- con-leche: none — arena infrastructure; a cons hit interns nothing. -/
theorem EStore.internLevelsPersistent_hit {st : EStore} {v : LsNodeView} {i : LsIdx}
    (hf : st.lss.pers.find? v = some i) : st.internLevelsPersistent v = (st, i) := by
  have he : st.lss.internPersistent v = (st.lss, i) := by
    simp only [LsStore.internPersistent]; rw [show st.lss.pers.find? v = some i from hf]
  simp only [EStore.internLevelsPersistent, he]

/-- con-leche: none — arena infrastructure; `internPersistentN` succeeds exactly as
`EStore.internNamePersistent`, and only where its capacity test held. -/
theorem internPersistentN_ok {v : NNodeView} {s : AState} {r : NIdx} {s' : AState}
    (h : internPersistentN v s = .ok (r, s')) :
    (s.store.ns.pers.find? v = none → s.store.ns.pers.sizeOf v < Idx.idxCap) ∧
      r = (s.store.internNamePersistent v).2 ∧
      s' = { s with store := (s.store.internNamePersistent v).1 } := by
  cases hf : s.store.ns.pers.find? v with
  | some hh =>
    simp only [internPersistentN, bind, StateT.bind, get, getThe, MonadStateOf.get,
      StateT.get, pure, StateT.pure, Except.bind, Except.pure, hf, Except.ok.injEq,
      Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rw [EStore.internNamePersistent_hit hf]
    exact ⟨by simp, rfl, rfl⟩
  | none =>
    by_cases hc : s.store.ns.pers.sizeOf v < Idx.idxCap
    · simp only [internPersistentN, bind, StateT.bind, get, getThe, MonadStateOf.get,
        StateT.get, pure, StateT.pure, set, StateT.set, Except.bind, Except.pure, hf,
        ite_eq_left hc, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨fun _ => hc, rfl, rfl⟩
    · simp only [internPersistentN, bind, StateT.bind, get, getThe, MonadStateOf.get,
        StateT.get, pure, set, Except.bind, Except.pure, hf,
        ite_eq_right hc, ConRon.Bridge.fail_apply] at h
      exact absurd h (by simp)

/-- con-leche: none — arena infrastructure; `internPersistentL` succeeds exactly as
`EStore.internLevelPersistent`, and only where its capacity test held. -/
theorem internPersistentL_ok {v : LNodeView} {s : AState} {r : LIdx} {s' : AState}
    (h : internPersistentL v s = .ok (r, s')) :
    (s.store.ls.pers.find? v = none → s.store.ls.pers.sizeOf v < Idx.idxCap) ∧
      r = (s.store.internLevelPersistent v).2 ∧
      s' = { s with store := (s.store.internLevelPersistent v).1 } := by
  cases hf : s.store.ls.pers.find? v with
  | some hh =>
    simp only [internPersistentL, bind, StateT.bind, get, getThe, MonadStateOf.get,
      StateT.get, pure, StateT.pure, Except.bind, Except.pure, hf, Except.ok.injEq,
      Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rw [EStore.internLevelPersistent_hit hf]
    exact ⟨by simp, rfl, rfl⟩
  | none =>
    by_cases hc : s.store.ls.pers.sizeOf v < Idx.idxCap
    · simp only [internPersistentL, bind, StateT.bind, get, getThe, MonadStateOf.get,
        StateT.get, pure, StateT.pure, set, StateT.set, Except.bind, Except.pure, hf,
        ite_eq_left hc, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨fun _ => hc, rfl, rfl⟩
    · simp only [internPersistentL, bind, StateT.bind, get, getThe, MonadStateOf.get,
        StateT.get, pure, set, Except.bind, Except.pure, hf,
        ite_eq_right hc, ConRon.Bridge.fail_apply] at h
      exact absurd h (by simp)

/-- con-leche: none — arena infrastructure; `internPersistentLs` succeeds exactly as
`EStore.internLevelsPersistent`, and only where its capacity test held. -/
theorem internPersistentLs_ok {v : LsNodeView} {s : AState} {r : LsIdx} {s' : AState}
    (h : internPersistentLs v s = .ok (r, s')) :
    (s.store.lss.pers.find? v = none → s.store.lss.pers.sizeOf v < Idx.idxCap) ∧
      r = (s.store.internLevelsPersistent v).2 ∧
      s' = { s with store := (s.store.internLevelsPersistent v).1 } := by
  cases hf : s.store.lss.pers.find? v with
  | some hh =>
    simp only [internPersistentLs, bind, StateT.bind, get, getThe, MonadStateOf.get,
      StateT.get, pure, StateT.pure, Except.bind, Except.pure, hf, Except.ok.injEq,
      Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rw [EStore.internLevelsPersistent_hit hf]
    exact ⟨by simp, rfl, rfl⟩
  | none =>
    by_cases hc : s.store.lss.pers.sizeOf v < Idx.idxCap
    · simp only [internPersistentLs, bind, StateT.bind, get, getThe, MonadStateOf.get,
        StateT.get, pure, StateT.pure, set, StateT.set, Except.bind, Except.pure, hf,
        ite_eq_left hc, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨fun _ => hc, rfl, rfl⟩
    · simp only [internPersistentLs, bind, StateT.bind, get, getThe, MonadStateOf.get,
        StateT.get, pure, set, Except.bind, Except.pure, hf,
        ite_eq_right hc, ConRon.Bridge.fail_apply] at h
      exact absurd h (by simp)

/-- con-leche: none — arena infrastructure; **a name promote-intern, at the
projection**: it stays well formed and only grows, the scratch tier stands still, and
the answer is persistent and decodes to the view. -/
theorem internPersistentN_pi {v : NNodeView} {s : AState} {r : NIdx} {s' : AState}
    (hwf : StoreWF s.store.dropScratch) (hv : s.store.dropScratch.ns.ViewOK v)
    (hp : NViewPers v) (h : internPersistentN v s = .ok (r, s')) :
    StoreWF s'.store.dropScratch ∧ Ext s.store.dropScratch s'.store.dropScratch ∧
      ScrSame s.store s'.store ∧ s'.store.dropScratch.ns.view r = some v ∧ PersN r := by
  obtain ⟨hc, rfl, rfl⟩ := internPersistentN_ok h
  have e1 := EStore.internNamePersistent_dropScratch s.store v hp
  have e2 := EStore.internNamePersistent_dropScratch s.store.dropScratch v hp
  have hfst := congrArg Prod.fst e1
  have hsnd := congrArg Prod.snd e1
  have hf2 := congrArg Prod.fst e2
  simp only at hfst hsnd hf2
  have hw : StoreWF (s.store.dropScratch.internNamePersistent v).1 := by
    cases hf : s.store.ns.pers.find? v with
    | some i =>
      rw [EStore.internNamePersistent_hit (st := s.store.dropScratch) hf]; exact hwf
    | none =>
      have := StoreWF'.dropScratch_wf
        (EStore.internNamePersistent_wf' (StoreWF'.of_wf hwf) hv hp (hc hf))
      exact hf2 ▸ this
  have hnw := (StoreWF'.of_wf hwf).nsWF
  show StoreWF (s.store.internNamePersistent v).1.dropScratch ∧
    Ext s.store.dropScratch (s.store.internNamePersistent v).1.dropScratch ∧
    ScrSame s.store (s.store.internNamePersistent v).1 ∧
    (s.store.internNamePersistent v).1.dropScratch.ns.view (s.store.internNamePersistent v).2
      = some v ∧ PersN (s.store.internNamePersistent v).2
  rw [← hfst, ← hsnd]
  exact ⟨hw, EStore.internNamePersistent_ext _ v, ScrSame.internNamePersistent s.store v,
    NStore.internPersistent_view hnw hc, NStore.internPersistent_pers hnw hc⟩

/-- con-leche: none — arena infrastructure; **a level promote-intern, at the
projection**. -/
theorem internPersistentL_pi {v : LNodeView} {s : AState} {r : LIdx} {s' : AState}
    (hwf : StoreWF s.store.dropScratch) (hv : s.store.dropScratch.ls.ViewOK v)
    (hp : LViewPers v) (h : internPersistentL v s = .ok (r, s')) :
    StoreWF s'.store.dropScratch ∧ Ext s.store.dropScratch s'.store.dropScratch ∧
      ScrSame s.store s'.store ∧ s'.store.dropScratch.ls.view r = some v ∧ PersL r := by
  obtain ⟨hc, rfl, rfl⟩ := internPersistentL_ok h
  have e1 := EStore.internLevelPersistent_dropScratch s.store v hp
  have e2 := EStore.internLevelPersistent_dropScratch s.store.dropScratch v hp
  have hfst := congrArg Prod.fst e1
  have hsnd := congrArg Prod.snd e1
  have hf2 := congrArg Prod.fst e2
  simp only at hfst hsnd hf2
  have hw : StoreWF (s.store.dropScratch.internLevelPersistent v).1 := by
    cases hf : s.store.ls.pers.find? v with
    | some i =>
      rw [EStore.internLevelPersistent_hit (st := s.store.dropScratch) hf]; exact hwf
    | none =>
      have := StoreWF'.dropScratch_wf
        (EStore.internLevelPersistent_wf' (StoreWF'.of_wf hwf) hv hp (hc hf))
      exact hf2 ▸ this
  have hlw := (StoreWF'.of_wf hwf).lsWF
  show StoreWF (s.store.internLevelPersistent v).1.dropScratch ∧
    Ext s.store.dropScratch (s.store.internLevelPersistent v).1.dropScratch ∧
    ScrSame s.store (s.store.internLevelPersistent v).1 ∧
    (s.store.internLevelPersistent v).1.dropScratch.ls.view (s.store.internLevelPersistent v).2
      = some v ∧ PersL (s.store.internLevelPersistent v).2
  rw [← hfst, ← hsnd]
  exact ⟨hw, EStore.internLevelPersistent_ext _ v, ScrSame.internLevelPersistent s.store v,
    LStore.internPersistent_view hlw hc, LStore.internPersistent_pers hlw hc⟩

/-- con-leche: none — arena infrastructure; **a level-list promote-intern, at the
projection**. -/
theorem internPersistentLs_pi {v : LsNodeView} {s : AState} {r : LsIdx} {s' : AState}
    (hwf : StoreWF s.store.dropScratch) (hv : s.store.dropScratch.lss.ViewOK v)
    (hp : LsViewPers v) (h : internPersistentLs v s = .ok (r, s')) :
    StoreWF s'.store.dropScratch ∧ Ext s.store.dropScratch s'.store.dropScratch ∧
      ScrSame s.store s'.store ∧ s'.store.dropScratch.lss.view r = some v ∧ PersLs r := by
  obtain ⟨hc, rfl, rfl⟩ := internPersistentLs_ok h
  have e1 := EStore.internLevelsPersistent_dropScratch s.store v hp
  have e2 := EStore.internLevelsPersistent_dropScratch s.store.dropScratch v hp
  have hfst := congrArg Prod.fst e1
  have hsnd := congrArg Prod.snd e1
  have hf2 := congrArg Prod.fst e2
  simp only at hfst hsnd hf2
  have hw : StoreWF (s.store.dropScratch.internLevelsPersistent v).1 := by
    cases hf : s.store.lss.pers.find? v with
    | some i =>
      rw [EStore.internLevelsPersistent_hit (st := s.store.dropScratch) hf]; exact hwf
    | none =>
      have := StoreWF'.dropScratch_wf
        (EStore.internLevelsPersistent_wf' (StoreWF'.of_wf hwf) hv hp (hc hf))
      exact hf2 ▸ this
  have hlw := (StoreWF'.of_wf hwf).lssWF
  show StoreWF (s.store.internLevelsPersistent v).1.dropScratch ∧
    Ext s.store.dropScratch (s.store.internLevelsPersistent v).1.dropScratch ∧
    ScrSame s.store (s.store.internLevelsPersistent v).1 ∧
    (s.store.internLevelsPersistent v).1.dropScratch.lss.view
      (s.store.internLevelsPersistent v).2 = some v ∧
      PersLs (s.store.internLevelsPersistent v).2
  rw [← hfst, ← hsnd]
  exact ⟨hw, EStore.internLevelsPersistent_ext _ v, ScrSame.internLevelsPersistent s.store v,
    LsStore.internPersistent_view hlw hc, LsStore.internPersistent_pers hlw hc⟩

/-- con-leche: none — arena infrastructure; **an expression promote-intern, at the
projection**. -/
theorem internPersistentE_pi {v : ENodeView} {s : AState} {r : EIdx} {s' : AState}
    (hwf : StoreWF s.store.dropScratch) (hv : s.store.dropScratch.ViewOK v)
    (hp : EViewPers v) (h : internPersistentE v s = .ok (r, s')) :
    StoreWF s'.store.dropScratch ∧ Ext s.store.dropScratch s'.store.dropScratch ∧
      ScrSame s.store s'.store ∧ s'.store.dropScratch.view r = some v ∧ PersE r := by
  obtain ⟨hc, rfl, rfl⟩ := Arena.internPersistentE_ok h
  have e1 := EStore.internPersistent_dropScratch s.store v hp
  have e2 := EStore.internPersistent_dropScratch s.store.dropScratch v hp
  have hfst := congrArg Prod.fst e1
  have hsnd := congrArg Prod.snd e1
  have hf2 := congrArg Prod.fst e2
  simp only at hfst hsnd hf2
  obtain ⟨wf', hview, hpers⟩ :=
    EStore.internPersistent_spec' (StoreWF'.of_wf hwf) hv hp (st := s.store.dropScratch) hc
  have hw : StoreWF (s.store.dropScratch.internPersistent v).1 :=
    hf2 ▸ StoreWF'.dropScratch_wf wf'
  show StoreWF (s.store.internPersistent v).1.dropScratch ∧
    Ext s.store.dropScratch (s.store.internPersistent v).1.dropScratch ∧
    ScrSame s.store (s.store.internPersistent v).1 ∧
    (s.store.internPersistent v).1.dropScratch.view (s.store.internPersistent v).2 = some v ∧
      PersE (s.store.internPersistent v).2
  rw [← hfst, ← hsnd]
  exact ⟨hw, EStore.internPersistent_ext _ v, ScrSame.internPersistent s.store v, hview, hpers⟩

/-! ## A view denotes -/

theorem denoteN_of_view' {st : NStore} {rk : NIdx → Nat} (h : NWFAt' st rk) :
    ∀ (n : Nat) (i : NIdx), rk i < n → (st.view i).isSome = true →
      ∃ x, denoteN st i = some x := by
  intro n
  induction n with
  | zero => intro i hn; grind
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

theorem denoteL_of_view' {st : LStore} {rk : LIdx → Nat} (h : LWFAt' st rk) :
    ∀ (n : Nat) (i : LIdx), rk i < n → (st.view i).isSome = true →
      ∃ x, denoteL st i = some x := by
  intro n
  induction n with
  | zero => intro i hn; grind
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
    | lam ty b =>
      obtain ⟨x, hx⟩ := hE ty (by simp [ENodeView.echildren])
      obtain ⟨y, hy⟩ := hE b (by simp [ENodeView.echildren])
      exact ⟨.lam x y, by simp [denoteEView, hx, hy, opt2]⟩
    | forallE ty b =>
      obtain ⟨x, hx⟩ := hE ty (by simp [ENodeView.echildren])
      obtain ⟨y, hy⟩ := hE b (by simp [ENodeView.echildren])
      exact ⟨.forallE x y, by simp [denoteEView, hx, hy, opt2]⟩
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

/-! ## What `PSrc` reads -/

/-- con-leche: none — arena infrastructure; a persistent name handle the store reads
is kept by itself: it denotes in the projection because the projection is well formed,
and what it denotes in the source it denotes there. -/
theorem PSrc.leafN {src st : EStore} (hs : PSrc src st) {h : NIdx} {v : NNodeView}
    (hp : h.isPersistent = true) (hv : st.ns.view h = some v) :
    Kept (denoteN src.ns h) (denoteN st.dropScratch.ns h) :=
  ⟨denoteN_of_view (StoreWF'.of_wf hs.piWF).nsWF (by
      rw [show st.dropScratch.ns.view h = st.ns.view h from NStore.view_dropScratch_pers st.ns hp,
        hv]; rfl),
    fun x hd => hs.persN h x hp hd⟩

/-- con-leche: none — arena infrastructure; the same at a level handle. -/
theorem PSrc.leafL {src st : EStore} (hs : PSrc src st) {h : LIdx} {v : LNodeView}
    (hp : h.isPersistent = true) (hv : st.ls.view h = some v) :
    Kept (denoteL src.ls h) (denoteL st.dropScratch.ls h) :=
  ⟨denoteL_of_view (StoreWF'.of_wf hs.piWF).lsWF (by
      rw [show st.dropScratch.ls.view h = st.ls.view h from LStore.view_dropScratch_pers st.ls hp,
        hv]; rfl),
    fun x hd => hs.persL h x hp hd⟩

/-- con-leche: none — arena infrastructure; the same at a level-list handle. -/
theorem PSrc.leafLs {src st : EStore} (hs : PSrc src st) {h : LsIdx} {v : LsNodeView}
    (hp : h.isPersistent = true) (hv : st.lss.view h = some v) :
    Kept (denoteLs src.lss h) (denoteLs st.dropScratch.lss h) := by
  have hv' : st.dropScratch.lss.view h = some v := by
    rw [show st.dropScratch.lss.view h = st.lss.view h from
      LsStore.view_dropScratch_pers st.lss hp, hv]
  obtain ⟨xs, hxs⟩ := denoteLs_of_view (StoreWF'.of_wf hs.piWF).lssWF hv'
  exact ⟨⟨xs, by simp only [denoteLs, hv']; exact hxs⟩, fun x hd => hs.persLs h x hp hd⟩

/-- con-leche: none — arena infrastructure; the same at an expression handle. -/
theorem PSrc.leafE {src st : EStore} (hs : PSrc src st) {h : EIdx} {v : ENodeView}
    (hp : h.isPersistent = true) (hv : st.view h = some v) :
    Kept (denoteE src h) (denoteE st.dropScratch h) :=
  ⟨denoteE_of_view (StoreWF'.of_wf hs.piWF) (by
      rw [EStore.view_dropScratch_pers st hp, hv]; rfl),
    fun x hd => hs.persE h x hp hd⟩

/-- con-leche: none — arena infrastructure; **what a scratch handle denotes in the
source is the node the store reads, read back in the source**: the source reads the
same node, and the source is well formed. -/
theorem PSrc.srcN {src st : EStore} (hs : PSrc src st) {h : NIdx} {v : NNodeView}
    (hp : h.isPersistent = false) (hv : st.ns.view h = some v) (x : ConLeche.Name)
    (hd : denoteN src.ns h = some x) : denoteNView src.ns v = some x := by
  obtain ⟨w, hw⟩ := denoteN_view hd
  have e := hs.scrN h w hp hw
  rw [hv] at e
  obtain rfl := Option.some.inj e
  obtain ⟨rk, hn⟩ := (StoreWF'.of_wf hs.srcWF).nsWF
  rw [← denoteN_unfold' hn hw]; exact hd

/-- con-leche: none — arena infrastructure; the same at a level handle. -/
theorem PSrc.srcL {src st : EStore} (hs : PSrc src st) {h : LIdx} {v : LNodeView}
    (hp : h.isPersistent = false) (hv : st.ls.view h = some v) (x : Level)
    (hd : denoteL src.ls h = some x) : denoteLView src.ls v = some x := by
  obtain ⟨w, hw⟩ := denoteL_view hd
  have e := hs.scrL h w hp hw
  rw [hv] at e
  obtain rfl := Option.some.inj e
  obtain ⟨rk, hn⟩ := (StoreWF'.of_wf hs.srcWF).lsWF
  rw [← denoteL_unfold' hn hw]; exact hd

/-- con-leche: none — arena infrastructure; the same at a level-list handle. -/
theorem PSrc.srcLs {src st : EStore} (hs : PSrc src st) {h : LsIdx} {v : LsNodeView}
    (hp : h.isPersistent = false) (hv : st.lss.view h = some v) (x : List Level)
    (hd : denoteLs src.lss h = some x) : denoteLList src.ls v = some x := by
  obtain ⟨w, hw, hl⟩ := denoteLs_view hd
  have e := hs.scrLs h w hp hw
  rw [hv] at e
  obtain rfl := Option.some.inj e
  exact hl

/-- con-leche: none — arena infrastructure; the same at an expression handle. -/
theorem PSrc.srcE {src st : EStore} (hs : PSrc src st) {h : EIdx} {v : ENodeView}
    (hp : h.isPersistent = false) (hv : st.view h = some v) (x : Expr)
    (hd : denoteE src h = some x) : denoteEView src v = some x := by
  obtain ⟨w, hw⟩ := denoteE_view hd
  have e := hs.scrE h w hp hw
  rw [hv] at e
  obtain rfl := Option.some.inj e
  obtain ⟨rk, hn⟩ := StoreWF'.of_wf hs.srcWF
  rw [← denoteE_unfold' hn hw]; exact hd

/-! ## `PSrc`'s constructors -/

/-- con-leche: none — arena infrastructure; **the source is the projection**: a
scratch handle reads nothing there, a persistent one reads what it reads. -/
theorem PSrc.self {st : EStore} (h : StoreWF st.dropScratch) : PSrc st.dropScratch st where
  piWF := h
  srcWF := h
  scrE := fun i v hi hv => by simp [EStore.view, EStore.dropScratch, hi] at hv
  scrLs := fun i v hi hv => by simp [LsStore.view, EStore.dropScratch, LsStore.dropScratch, hi] at hv
  scrL := fun i v hi hv => by
    simp [LStore.view, EStore.ls, EStore.dropScratch, LsStore.dropScratch, LStore.dropScratch,
      hi] at hv
  scrN := fun i v hi hv => by
    simp [NStore.view, EStore.ns, EStore.dropScratch, LsStore.dropScratch, LStore.dropScratch,
      NStore.dropScratch, hi] at hv
  persE := fun _ _ _ hd => hd
  persLs := fun _ _ _ hd => hd
  persL := fun _ _ _ hd => hd
  persN := fun _ _ _ hd => hd

/-- con-leche: none — arena infrastructure; a framed state's projection is the start
state's: `frameFrom` took the persistent tables from it, and `dropScratch` empties the
rest. -/
theorem EStore.dropScratch_frameFrom (st s₀ : EStore) :
    (st.frameFrom s₀).dropScratch = s₀.dropScratch := rfl

/-- con-leche: none — arena infrastructure; a name-tier read in range of one array set
is in range of another of the same sizes. -/
theorem NTables.get_isSome_of_sizes {t t' : NTables} {i : NIdx} (hs : t.sizes = t'.sizes)
    (h : (t.get i).isSome = true) : (t'.get i).isSome = true := by
  simp only [NTables.sizes, List.cons.injEq, and_true] at hs
  obtain ⟨h1, h2, h3⟩ := hs
  simp only [NTables.get, Tbl.node?, Tbl.size] at h h1 h2 h3 ⊢
  grind

/-- con-leche: none — arena infrastructure; the same at a level tier. -/
theorem LTables.get_isSome_of_sizes {t t' : LTables} {i : LIdx} (hs : t.sizes = t'.sizes)
    (h : (t.get i).isSome = true) : (t'.get i).isSome = true := by
  simp only [LTables.sizes, List.cons.injEq, and_true] at hs
  obtain ⟨h1, h2, h3, h4, h5⟩ := hs
  simp only [LTables.get, Tbl.node?, Tbl.size] at h h1 h2 h3 h4 h5 ⊢
  grind

/-- con-leche: none — arena infrastructure; the same at a level-list tier. -/
theorem LsTables.get_isSome_of_sizes {t t' : LsTables} {i : LsIdx} (hs : t.sizes = t'.sizes)
    (h : (t.get i).isSome = true) : (t'.get i).isSome = true := by
  simp only [LsTables.sizes, List.cons.injEq, and_true] at hs
  simp only [LsTables.get, Tbl.node?, Tbl.size] at h hs ⊢
  grind

/-- con-leche: none — arena infrastructure; the same at an expression tier. -/
theorem ETables.get_isSome_of_sizes {t t' : ETables} {i : EIdx} (hs : t.sizes = t'.sizes)
    (h : (t.get i).isSome = true) : (t'.get i).isSome = true := by
  simp only [ETables.sizes, List.cons.injEq, and_true] at hs
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := hs
  simp only [ETables.get, Tbl.node?, Tbl.size] at h h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 ⊢
  -- one split per constructor tag, and the `app` arm's width
  grind (splits := 40)

/-- con-leche: none — arena infrastructure; `persSizes` at its four tiers. -/
theorem EStore.persSizes_eq {a b : EStore} (h : a.persSizes = b.persSizes) :
    a.pers.sizes = b.pers.sizes ∧ a.lss.pers.sizes = b.lss.pers.sizes ∧
      a.lss.ls.pers.sizes = b.lss.ls.pers.sizes ∧
      a.lss.ls.ns.pers.sizes = b.lss.ls.ns.pers.sizes := by
  simp only [EStore.persSizes, ETables.sizes, LsTables.sizes, LTables.sizes, NTables.sizes,
    List.cons_append, List.nil_append, List.cons.injEq, and_true] at h ⊢
  grind

/-- con-leche: none — arena infrastructure; **the source is where a scratch run ended
and the store is that state framed** (`Arena/Promote.lean`'s `scratchRun`, whose flag
the start state's scratch tier being open makes the framed store's).

A scratch handle reads the run's tier under the start state's flag.  A persistent
handle that denotes where the run ended has a view there, so by the sizes one in the
start state, so it denotes there, and by the extension that denotation is the one it
has where the run ended; the framed store's projection is the start state's. -/
theorem PSrc.of_run {st₁ st₂ : EStore} (h1 : StoreWF st₁) (h2 : StoreWF st₂)
    (hx : Ext st₁ st₂) (hs : st₂.persSizes = st₁.persSizes) (hon : st₁.scratchOn = true) :
    PSrc st₂ (st₂.frameFrom st₁) := by
  obtain ⟨hsE, hsLs, hsL, hsN⟩ := EStore.persSizes_eq hs
  have hw' := StoreWF'.of_wf h1
  have hsy : st₁.lss.scratchOn = true ∧ st₁.lss.ls.scratchOn = true ∧
      st₁.lss.ls.ns.scratchOn = true := by
    obtain ⟨rk, hw⟩ := h1
    have a := hw.sync
    have b := hw.lss.sync
    obtain ⟨rkl, hl⟩ := hw.lss.ls
    have c := hl.sync
    exact ⟨by rw [← a, hon], by rw [← b, ← a, hon], by rw [← c, ← b, ← a, hon]⟩
  have hpe := PExt.dropScratch h1
  refine ⟨show StoreWF st₁.dropScratch from EStore.dropScratch_wf h1, h2, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_⟩
  · intro i v hi hv
    have hv' : st₂.scr.get i = some v := by
      simp only [EStore.view, hi, Bool.false_eq_true, ite_false] at hv
      split at hv
      · exact hv
      · cases hv
    simp [EStore.view, EStore.frameFrom, hi, hon, hv']
  · intro i v hi hv
    have hv' : st₂.lss.scr.get i = some v := by
      simp only [LsStore.view, hi, Bool.false_eq_true, ite_false] at hv
      split at hv
      · exact hv
      · cases hv
    simp [LsStore.view, EStore.frameFrom, LsStore.frameFrom, hi, hsy.1, hv']
  · intro i v hi hv
    have hv' : st₂.lss.ls.scr.get i = some v := by
      simp only [EStore.ls, LStore.view, hi, Bool.false_eq_true, ite_false] at hv
      split at hv
      · exact hv
      · cases hv
    simp [EStore.ls, LStore.view, EStore.frameFrom, LsStore.frameFrom, LStore.frameFrom, hi,
      hsy.2.1, hv']
  · intro i v hi hv
    have hv' : st₂.lss.ls.ns.scr.get i = some v := by
      simp only [EStore.ns, NStore.view, hi, Bool.false_eq_true, ite_false] at hv
      split at hv
      · exact hv
      · cases hv
    simp [EStore.ns, NStore.view, EStore.frameFrom, LsStore.frameFrom, LStore.frameFrom,
      NStore.frameFrom, hi, hsy.2.2, hv']
  · intro i x hi hd
    obtain ⟨v, hv⟩ := denoteE_view hd
    have hvs : (st₁.view i).isSome = true := by
      simp only [EStore.view, hi, ite_true] at hv ⊢
      exact ETables.get_isSome_of_sizes hsE (by rw [hv]; rfl)
    obtain ⟨y, hy⟩ := denoteE_of_view hw' hvs
    have e := hx.expr i y hy
    rw [hd] at e
    obtain rfl := Option.some.inj e
    exact hpe.expr i _ hi hy
  · intro i x hi hd
    obtain ⟨v, hv, -⟩ := denoteLs_view hd
    have hvs : (st₁.lss.view i).isSome = true := by
      simp only [LsStore.view, hi, ite_true] at hv ⊢
      exact LsTables.get_isSome_of_sizes hsLs (by rw [hv]; rfl)
    obtain ⟨us, hus⟩ := Option.isSome_iff_exists.mp hvs
    obtain ⟨y, hy⟩ := denoteLs_of_view hw'.lssWF hus
    have hy' : denoteLs st₁.lss i = some y := by simp only [denoteLs, hus]; exact hy
    have e := hx.lss.lst i y hy'
    rw [hd] at e
    obtain rfl := Option.some.inj e
    exact hpe.lss.lst i _ hi hy'
  · intro i x hi hd
    obtain ⟨v, hv⟩ := denoteL_view hd
    have hvs : (st₁.ls.view i).isSome = true := by
      simp only [EStore.ls, LStore.view, hi, ite_true] at hv ⊢
      exact LTables.get_isSome_of_sizes hsL (by rw [hv]; rfl)
    obtain ⟨y, hy⟩ := denoteL_of_view hw'.lsWF hvs
    have e : denoteL st₂.ls i = some y := hx.lss.ls.lvl i y hy
    rw [hd] at e
    obtain rfl := Option.some.inj e
    exact hpe.lss.ls.lvl i _ hi hy
  · intro i x hi hd
    obtain ⟨v, hv⟩ := denoteN_view hd
    have hvs : (st₁.ns.view i).isSome = true := by
      simp only [EStore.ns, NStore.view, hi, ite_true] at hv ⊢
      exact NTables.get_isSome_of_sizes hsN (by rw [hv]; rfl)
    obtain ⟨y, hy⟩ := denoteN_of_view hw'.nsWF hvs
    have e : denoteN st₂.ns i = some y := hx.lss.ls.ns i y hy
    rw [hd] at e
    obtain rfl := Option.some.inj e
    exact hpe.lss.ls.ns i _ hi hy

end ConRon.Bridge
