/-
# `ConRon.Arena.PersistentRun` — `internPersistentE`'s run, both directions

Task #97-T2-LOCKSTEP step 1, audit D3.  `Arena/Monad.lean`'s
`internPersistentE` runs in the Rust's order — the binder datum's
promote-intern with its own miss-path capacity test, then the node probe at
the persistent tier, then the node's miss-path test, then the append — so it
is two monadic steps where it used to be one.  This module reads its run off
once, for both theorems: `Bridge/Promote/Walk.lean` (Theorem 1) and
`Refine2/Specs.lean` (Theorem 2) quote the lemmas here and never unfold the
wrapper.  It imports nothing but `Monad.lean` so that `Refine2` can import it
without reaching `Bridge`.
-/
import ConRon.Arena.Monad

namespace ConRon.Arena

open ConLeche

private theorem failRun {α : Type} (e : CheckError) (s : AState) :
    (fail e : AM α) s = .error e := rfl

/-! ### `internPersistentE`, in the Rust's order (task #97-T2-LOCKSTEP, audit D3)

The wrapper is two monadic steps now — the datum's promote-intern with its own
capacity test, then the node's — so its run is read off once, here, in both
directions: success says exactly that the two tests the Rust makes held where
the Rust makes them (`EStore.persCapBM`, `EStore.persCapNode`) and that the
step is `EStore.internPersistent`; and conversely.  Every consumer (the
`AExt` below, `Bridge/Promote/Walk.lean`, `Refine2/Specs.lean`) quotes these
two and never unfolds the wrapper. -/

/-- con-leche: none — arena infrastructure; `internBMPersistentE` succeeds
exactly as `EStore.internBMPersistent`, and only where the datum test held. -/
theorem internBMPersistentE_ok {m : ConLeche.BinderMeta} {s : AState} {r : BMIdx}
    {s' : AState} (h : internBMPersistentE m s = .ok (r, s')) :
    (s.store.persFindBM m = none → s.store.capOKBMPersistent) ∧
      r = (s.store.internBMPersistent m).2 ∧
      s' = { s with store := (s.store.internBMPersistent m).1 } := by
  cases hf : s.store.persFindBM m with
  | some i =>
    simp only [internBMPersistentE, bind, StateT.bind, get, getThe, MonadStateOf.get,
      StateT.get, pure, StateT.pure, Except.bind, Except.pure, hf, Except.ok.injEq,
      Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp [EStore.internBMPersistent, hf]
  | none =>
    by_cases hc : s.store.pers.bmSize < Idx.idxCap
    · simp only [internBMPersistentE, bind, StateT.bind, get, getThe, MonadStateOf.get,
        StateT.get, pure, StateT.pure, set, StateT.set, Except.bind, Except.pure, hf,
        if_pos hc, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨fun _ => hc, rfl, rfl⟩
    · simp only [internBMPersistentE, bind, StateT.bind, get, getThe, MonadStateOf.get,
        StateT.get, pure, set, Except.bind, Except.pure, hf,
        if_neg hc, failRun] at h
      exact absurd h (by simp)

/-- con-leche: none — arena infrastructure; the converse. -/
theorem internBMPersistentE_run {m : ConLeche.BinderMeta} {s : AState}
    (hc : s.store.persFindBM m = none → s.store.capOKBMPersistent) :
    internBMPersistentE m s = .ok ((s.store.internBMPersistent m).2,
      { s with store := (s.store.internBMPersistent m).1 }) := by
  cases hf : s.store.persFindBM m with
  | some i =>
    simp only [internBMPersistentE, bind, StateT.bind, get, getThe, MonadStateOf.get,
      StateT.get, pure, StateT.pure, Except.bind, Except.pure, hf,
      EStore.internBMPersistent]
  | none =>
    have hc' : s.store.pers.bmSize < Idx.idxCap := hc hf
    simp only [internBMPersistentE, bind, StateT.bind, get, getThe, MonadStateOf.get,
      StateT.get, pure, StateT.pure, set, StateT.set, Except.bind, Except.pure, hf,
      if_pos hc']

/-- con-leche: none — arena infrastructure; the same at the view. -/
theorem internBMOfViewPersistentE_ok {v : ENodeView} {s : AState} {r : BMIdx}
    {s' : AState} (h : internBMOfViewPersistentE v s = .ok (r, s')) :
    s.store.persCapBM v ∧
      r = (s.store.internBMOfViewPersistent v).2 ∧
      s' = { s with store := (s.store.internBMOfViewPersistent v).1 } := by
  cases v
  case lam ty b m => exact internBMPersistentE_ok h
  case forallE ty b m => exact internBMPersistentE_ok h
  all_goals
    simp only [internBMOfViewPersistentE, pure, StateT.pure, Except.pure,
      Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨trivial, rfl, rfl⟩

/-- con-leche: none — arena infrastructure; the converse. -/
theorem internBMOfViewPersistentE_run {v : ENodeView} {s : AState}
    (hc : s.store.persCapBM v) :
    internBMOfViewPersistentE v s = .ok ((s.store.internBMOfViewPersistent v).2,
      { s with store := (s.store.internBMOfViewPersistent v).1 }) := by
  cases v
  case lam ty b m => exact internBMPersistentE_run hc
  case forallE ty b m => exact internBMPersistentE_run hc
  all_goals rfl

/-- con-leche: none — arena infrastructure; **`internPersistentE` succeeds
exactly as `EStore.internPersistent`, and only where the Rust's two capacity
tests held**. -/
theorem internPersistentE_ok {v : ENodeView} {s : AState} {r : EIdx} {s' : AState}
    (h : internPersistentE v s = .ok (r, s')) :
    s.store.persCapBM v ∧ s.store.persCapNode v ∧
      r = (s.store.internPersistent v).2 ∧
      s' = { s with store := (s.store.internPersistent v).1 } := by
  simp only [internPersistentE, bind, StateT.bind] at h
  cases h1 : internBMOfViewPersistentE v s with
  | error e => rw [h1] at h; simp [Except.bind] at h
  | ok p =>
    obtain ⟨mi, s1⟩ := p
    rw [h1] at h
    obtain ⟨hbm, rfl, rfl⟩ := internBMOfViewPersistentE_ok h1
    refine ⟨hbm, ?_⟩
    rw [EStore.internPersistent_eq_at]
    simp only [EStore.persCapNode]
    generalize s.store.internBMOfViewPersistent v = q at h ⊢
    obtain ⟨st1, mi⟩ := q
    cases hf : st1.pers.find? v mi with
    | some hh =>
      simp only [Except.bind, get, getThe, MonadStateOf.get, StateT.get, pure,
        StateT.pure, Except.pure, hf, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp [EStore.internPersistentAt, hf]
    | none =>
      by_cases hc : st1.pers.sizeOf v < Idx.idxCap
      · simp only [Except.bind, get, getThe, MonadStateOf.get, StateT.get, pure,
          set, Except.pure, hf, if_pos hc] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨fun _ => hc, rfl, rfl⟩
      · simp only [Except.bind, get, getThe, MonadStateOf.get, StateT.get, pure,
          set, Except.pure, hf, if_neg hc, failRun] at h
        exact absurd h (by simp)

/-- con-leche: none — arena infrastructure; the converse: where the Rust's two
tests hold, the wrapper runs `EStore.internPersistent`. -/
theorem internPersistentE_run_eq {v : ENodeView} {s : AState}
    (hb : s.store.persCapBM v) (hn : s.store.persCapNode v) :
    internPersistentE v s = .ok ((s.store.internPersistent v).2,
      { s with store := (s.store.internPersistent v).1 }) := by
  simp only [internPersistentE, bind, StateT.bind]
  rw [internBMOfViewPersistentE_run hb, EStore.internPersistent_eq_at]
  simp only [EStore.persCapNode] at hn
  generalize s.store.internBMOfViewPersistent v = q at hn ⊢
  obtain ⟨st1, mi⟩ := q
  cases hf : st1.pers.find? v mi with
  | some hh =>
    simp only [Except.bind, get, getThe, MonadStateOf.get, StateT.get, pure,
      StateT.pure, Except.pure, hf, EStore.internPersistentAt]
  | none =>
    have hc : st1.pers.sizeOf v < Idx.idxCap := hn hf
    simp only [Except.bind, get, getThe, MonadStateOf.get, StateT.get, pure,
      StateT.pure, set, StateT.set, StateT.bind, Except.pure, hf, if_pos hc]
    rfl

end ConRon.Arena
