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

/-! ### `internE`'s binder arm, in the Rust's order (task #97-T2-LOCKSTEP, D6)

`internE` at a `lam`/`forallE` view is two monadic steps now — `internBME` (the
port's `intern_bm`), then `internLamIE` / `internForallEIE` at the datum handle
that step answered (the port's `intern_lam_i` / `intern_forall_e_i`) — so, as
for `internPersistentE` above, their runs are read off once, here, for
Theorem 1 (`Bridge/Specs.lean`, `Bridge/ExprOps/MemoSpecs.lean`).
`Refine2/Specs.lean` states the same facts in its own capacity vocabulary. -/

/-- con-leche: none — arena infrastructure; a datum the two-tier probe already
answers is not interned again. -/
theorem EStore.internBM_eq_of_findBM {st : EStore} {m : ConLeche.BinderMeta} {i : BMIdx}
    (hf : st.findBM m = some i) : st.internBM m = (st, i) := by
  unfold EStore.findBM at hf
  cases hp : st.persFindBM m with
  | some j =>
    rw [hp] at hf
    cases hf
    simp [EStore.internBM, hp]
  | none =>
    rw [hp] at hf
    cases hon : st.scratchOn with
    | false => simp [hon] at hf
    | true =>
      simp only [hon, if_true] at hf
      simp [EStore.internBM, hp, hon, hf]

/-- con-leche: none — arena infrastructure; `internBME` succeeds exactly as
`EStore.internBM`, and only where the port's `intern_bm` test held (on the
datum miss). -/
theorem internBME_ok {m : ConLeche.BinderMeta} {s : AState} {r : BMIdx} {s' : AState}
    (h : internBME m s = .ok (r, s')) :
    (s.store.findBM m = none → s.store.capOKBM) ∧
      r = (s.store.internBM m).2 ∧
      s' = { s with store := (s.store.internBM m).1 } := by
  cases hf : s.store.findBM m with
  | some i =>
    simp only [internBME, bind, StateT.bind, get, getThe, MonadStateOf.get,
      StateT.get, pure, StateT.pure, Except.bind, Except.pure, hf, Except.ok.injEq,
      Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rw [EStore.internBM_eq_of_findBM hf]
    exact ⟨fun h => absurd h (by simp), rfl, rfl⟩
  | none =>
    by_cases hc : (if s.store.scratchOn then s.store.scr.bmSize
        else s.store.pers.bmSize) < Idx.idxCap
    · simp only [internBME, bind, StateT.bind, get, getThe, MonadStateOf.get,
        StateT.get, pure, StateT.pure, set, StateT.set, Except.bind, Except.pure, hf,
        if_pos hc, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨fun _ => hc, rfl, rfl⟩
    · simp only [internBME, bind, StateT.bind, get, getThe, MonadStateOf.get,
        StateT.get, pure, set, Except.bind, Except.pure, hf,
        if_neg hc, failRun] at h
      exact absurd h (by simp)

/-- con-leche: none — arena infrastructure; a binder record the two-tier probe
already answers is not interned again. -/
theorem EStore.internBindI_eq_of_findBindI {st : EStore} {tag : UInt32} {ty b : EIdx}
    {mi : BMIdx} {i : EIdx} (hf : st.findBindI tag ty b mi = some i) :
    st.internBindI tag ty b mi = (st, i) := by
  unfold EStore.findBindI at hf
  unfold EStore.internBindI
  cases hp : st.persFindBindMaybe tag ⟨ty, b, mi⟩ with
  | some j =>
    simp only [hp, Option.some.injEq] at hf
    simp only [hp, hf]
  | none =>
    simp only [hp] at hf ⊢
    cases hon : st.scratchOn with
    | false => simp [hon] at hf
    | true =>
      simp only [hon, if_true] at hf ⊢
      simp only [hf]

/-- con-leche: none — arena infrastructure; `internBindIE`'s two arms end at
`EStore.internBindI` (the capacity branch is the only other exit, and it
fails). -/
theorem internLamIE_ok {ty b : EIdx} {mi : BMIdx} {s : AState} {r : EIdx} {s' : AState}
    (h : internLamIE ty b mi s = .ok (r, s')) :
    r = (s.store.internLamI ty b mi).2 ∧
      s' = { s with store := (s.store.internLamI ty b mi).1 } := by
  cases hf : s.store.findBindI ETag.lam ty b mi with
  | some i =>
    simp only [internLamIE, bind, StateT.bind, get, getThe, MonadStateOf.get,
      StateT.get, pure, StateT.pure, Except.bind, Except.pure, hf, Except.ok.injEq,
      Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rw [EStore.internLamI, EStore.internBindI_eq_of_findBindI hf]
    exact ⟨rfl, rfl⟩
  | none =>
    by_cases hc : (if s.store.scratchOn then s.store.scr.bindSizeOf ETag.lam
        else s.store.pers.bindSizeOf ETag.lam) < Idx.idxCap
    · simp only [internLamIE, bind, StateT.bind, get, getThe, MonadStateOf.get,
        StateT.get, pure, StateT.pure, set, StateT.set, Except.bind, Except.pure, hf,
        if_pos hc, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨rfl, rfl⟩
    · simp only [internLamIE, bind, StateT.bind, get, getThe, MonadStateOf.get,
        StateT.get, pure, set, Except.bind, Except.pure, hf,
        if_neg hc, failRun] at h
      exact absurd h (by simp)

/-- con-leche: none — arena infrastructure; the same at the other array. -/
theorem internForallEIE_ok {ty b : EIdx} {mi : BMIdx} {s : AState} {r : EIdx}
    {s' : AState} (h : internForallEIE ty b mi s = .ok (r, s')) :
    r = (s.store.internForallEI ty b mi).2 ∧
      s' = { s with store := (s.store.internForallEI ty b mi).1 } := by
  cases hf : s.store.findBindI ETag.forallE ty b mi with
  | some i =>
    simp only [internForallEIE, bind, StateT.bind, get, getThe, MonadStateOf.get,
      StateT.get, pure, StateT.pure, Except.bind, Except.pure, hf, Except.ok.injEq,
      Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rw [EStore.internForallEI, EStore.internBindI_eq_of_findBindI hf]
    exact ⟨rfl, rfl⟩
  | none =>
    by_cases hc : (if s.store.scratchOn then s.store.scr.bindSizeOf ETag.forallE
        else s.store.pers.bindSizeOf ETag.forallE) < Idx.idxCap
    · simp only [internForallEIE, bind, StateT.bind, get, getThe, MonadStateOf.get,
        StateT.get, pure, StateT.pure, set, StateT.set, Except.bind, Except.pure, hf,
        if_pos hc, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨rfl, rfl⟩
    · simp only [internForallEIE, bind, StateT.bind, get, getThe, MonadStateOf.get,
        StateT.get, pure, set, Except.bind, Except.pure, hf,
        if_neg hc, failRun] at h
      exact absurd h (by simp)

/-- con-leche: none — arena infrastructure; `internNodeE` (the eight non-binder
arms of `internE`) either answers a cons hit and moves nothing, or ends at
`EStore.intern`. -/
theorem internNodeE_ok {v : ENodeView} {s : AState} {r : EIdx} {s' : AState}
    (h : internNodeE v s = .ok (r, s')) :
    (s.store.find? v = some r ∧ s' = s) ∨
      (s.store.find? v = none ∧ r = (s.store.intern v).2 ∧
        s' = { s with store := (s.store.intern v).1 }) := by
  cases hf : s.store.find? v with
  | some i =>
    simp only [internNodeE, bind, StateT.bind, get, getThe, MonadStateOf.get,
      StateT.get, pure, StateT.pure, Except.bind, Except.pure, hf, Except.ok.injEq,
      Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact Or.inl ⟨rfl, rfl⟩
  | none =>
    by_cases hc : (if s.store.scratchOn then s.store.scr.sizeOf v
        else s.store.pers.sizeOf v) < Idx.idxCap
    · simp only [internNodeE, bind, StateT.bind, get, getThe, MonadStateOf.get,
        StateT.get, pure, StateT.pure, set, StateT.set, Except.bind, Except.pure, hf,
        if_pos hc, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact Or.inr ⟨rfl, rfl, rfl⟩
    · simp only [internNodeE, bind, StateT.bind, get, getThe, MonadStateOf.get,
        StateT.get, pure, set, Except.bind, Except.pure, hf,
        if_neg hc, failRun] at h
      exact absurd h (by simp)

/-- con-leche: none — arena infrastructure; **`internE` at a `lam` view is its
two steps**: the datum step's run and the node step's run at the handle and
state it answered. -/
theorem internE_lam_split {ty b : EIdx} {m : ConLeche.BinderMeta} {s : AState}
    {r : EIdx} {s' : AState} (h : internE (.lam ty b m) s = .ok (r, s')) :
    ∃ mi s1, internBME m s = .ok (mi, s1) ∧ internLamIE ty b mi s1 = .ok (r, s') := by
  simp only [internE, bind, StateT.bind] at h
  cases h1 : internBME m s with
  | error e => rw [h1] at h; simp [Except.bind] at h
  | ok p =>
    obtain ⟨mi, s1⟩ := p
    rw [h1] at h
    exact ⟨mi, s1, rfl, h⟩

/-- con-leche: none — arena infrastructure; the same at a `forallE` view. -/
theorem internE_forallE_split {ty b : EIdx} {m : ConLeche.BinderMeta} {s : AState}
    {r : EIdx} {s' : AState} (h : internE (.forallE ty b m) s = .ok (r, s')) :
    ∃ mi s1, internBME m s = .ok (mi, s1) ∧ internForallEIE ty b mi s1 = .ok (r, s') := by
  simp only [internE, bind, StateT.bind] at h
  cases h1 : internBME m s with
  | error e => rw [h1] at h; simp [Except.bind] at h
  | ok p =>
    obtain ⟨mi, s1⟩ := p
    rw [h1] at h
    exact ⟨mi, s1, rfl, h⟩

end ConRon.Arena
