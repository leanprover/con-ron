/-
# `ConRon.Arena.PersistentRun` — `internPersistentE`'s run, both directions

Task #97-T2-LOCKSTEP step 1, audit D3.  `Arena/Monad.lean`'s
`internPersistentE` runs in the Rust's order — the node probe at the
persistent tier, then the node's miss-path test, then the append.  (Until
task #119 a binder datum's promote-intern came first.)  This module reads its
run off once, for both theorems: `Bridge/Promote/Walk.lean` (Theorem 1) and
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

Its run is read off once, here, in both directions: success says exactly that
the test the Rust makes held where the Rust makes it (`EStore.persCapNode`)
and that the step is `EStore.internPersistent`; and conversely.  Every consumer (the
`AExt` below, `Bridge/Promote/Walk.lean`, `Refine2/Specs.lean`) quotes these
two and never unfolds the wrapper. -/

/-- con-leche: none — arena infrastructure; **`internPersistentE` succeeds
exactly as `EStore.internPersistent`, and only where the Rust's capacity
test held**. -/
theorem internPersistentE_ok {v : ENodeView} {s : AState} {r : EIdx} {s' : AState}
    (h : internPersistentE v s = .ok (r, s')) :
    s.store.persCapNode v ∧
      r = (s.store.internPersistent v).2 ∧
      s' = { s with store := (s.store.internPersistent v).1 } := by
  simp only [EStore.persCapNode]
  cases hf : s.store.pers.find? v with
  | some hh =>
    simp only [internPersistentE, bind, StateT.bind, get, getThe, MonadStateOf.get,
      StateT.get, pure, StateT.pure, Except.bind, Except.pure, hf, Except.ok.injEq,
      Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp [EStore.internPersistent, hf]
  | none =>
    by_cases hc : s.store.pers.sizeOf v < Idx.idxCap
    · simp only [internPersistentE, bind, StateT.bind, get, getThe, MonadStateOf.get,
        StateT.get, pure, StateT.pure, set, StateT.set, Except.bind, Except.pure, hf,
        ite_eq_left hc, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨fun _ => hc, rfl, rfl⟩
    · simp only [internPersistentE, bind, StateT.bind, get, getThe, MonadStateOf.get,
        StateT.get, pure, set, Except.bind, Except.pure, hf,
        ite_eq_right hc, failRun] at h
      exact absurd h (by simp)

/-- con-leche: none — arena infrastructure; the converse: where the Rust's
test holds, the wrapper runs `EStore.internPersistent`. -/
theorem internPersistentE_run_eq {v : ENodeView} {s : AState}
    (hn : s.store.persCapNode v) :
    internPersistentE v s = .ok ((s.store.internPersistent v).2,
      { s with store := (s.store.internPersistent v).1 }) := by
  simp only [EStore.persCapNode] at hn
  cases hf : s.store.pers.find? v with
  | some hh =>
    simp only [internPersistentE, bind, StateT.bind, get, getThe, MonadStateOf.get,
      StateT.get, pure, StateT.pure, Except.bind, Except.pure, hf,
      EStore.internPersistent]
  | none =>
    have hc : s.store.pers.sizeOf v < Idx.idxCap := hn hf
    simp only [internPersistentE, bind, StateT.bind, get, getThe, MonadStateOf.get,
      StateT.get, pure, StateT.pure, set, StateT.set, Except.bind, Except.pure, hf,
      ite_eq_left hc]

/-! ### `internE`'s binder arm, in the Rust's order (task #97-T2-LOCKSTEP, D6)

`internE` at a `lam`/`forallE` view is `internLamE` / `internForallEE` (the
port's `intern_lam` / `intern_forall_e`); their runs are read off once, here,
for Theorem 1 (`Bridge/Specs.lean`, `Bridge/ExprOps/MemoSpecs.lean`). -/

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
        ite_eq_left hc, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact Or.inr ⟨rfl, rfl, rfl⟩
    · simp only [internNodeE, bind, StateT.bind, get, getThe, MonadStateOf.get,
        StateT.get, pure, set, Except.bind, Except.pure, hf,
        ite_eq_right hc, failRun] at h
      exact absurd h (by simp)

/-- con-leche: none — arena infrastructure; **`internE` at a `lam` view is
`internLamE`**. -/
theorem internE_lam_split {ty b : EIdx} {s : AState}
    {r : EIdx} {s' : AState} (h : internE (.lam ty b) s = .ok (r, s')) :
    internLamE ty b s = .ok (r, s') := h

/-- con-leche: none — arena infrastructure; the same at a `forallE` view. -/
theorem internE_forallE_split {ty b : EIdx} {s : AState}
    {r : EIdx} {s' : AState} (h : internE (.forallE ty b) s = .ok (r, s')) :
    internForallEE ty b s = .ok (r, s') := h

end ConRon.Arena
