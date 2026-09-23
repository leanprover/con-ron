import ConRon.Arena.Checker

/-!
# `ConRon.Arena.Phased` — the declaration fold as the binary's driver runs it

**Task #97-P5-Driver.**  `installThenCheck` (`Arena/Checker.lean`) threads
ONE state through both phases.  The Rust driver does not: at the phase
boundary it freezes the persistent tier (`arena::checker::freeze_tier`) and
runs phase B on WORKERS, each with a state of its own over that tier
(`arena::checker::worker_state`), and the sequential projection it is argued
equal to is one such worker checking every record in order
(`arena::checker::check_pending_worker`).  This module is the twin of that
shape, so that Theorem 2 can relate the driver's sequential projection
(`arena::checker::check_decls_phased`) to something:

* `AState.worker` — the twin has no tier to freeze, so a worker's state is the
  phase-A state with the scratch tier closed and emptied and the per-call memos
  and per-declaration caches fresh; the persistent tier and the pins are the
  phase-A state's own;
* `checkPendingWorker` — `checkPendingList` from that state, the phase-A state
  handed back untouched (the Rust thaws its store to exactly what phase A
  left);
* `installThenCheckPhased` — `installThenCheck` with that phase B.

**It is `installThenCheck` whenever phase A leaves the caches empty**, which
the fold does (every phase-A step ends in `dropScratch`):
`checkPendingList_worker` below says so, and it rests on one structural fact
— `enterScratch`, which opens every phase-B record, overwrites exactly what
`AState.worker` changes, except the caches.  `Bridge/Checker/Phased.lean`
uses it to carry Theorem 1 over.
-/

namespace ConRon.Arena

open ConLeche

/-- con-leche: Main.lean:262-278 checkWorker — **a phase-B worker's state**:
the phase-A state with the scratch tier closed and empty, and fresh memos and
caches.  The Rust's `worker_state` builds the same thing over the FROZEN tier
(an empty store whose reads go to the `PersTier`); the twin has one store and
reads its persistent tier where it is. -/
def AState.worker (s : AState) : AState :=
  { s with store := s.store.dropScratch, memos := Memos.empty,
           caches := Caches.empty }

/-- con-leche: ConLeche/Cached/Installed.lean:429-436 checkPendingList —
**phase B on one worker, in record order**: `checkPendingList` from
`AState.worker`, and the phase-A state handed back as it was, which is what
the Rust's `thaw_tier` restores. -/
def checkPendingWorker (mode : CheckMode) (fe : IFEnv) (pend : List PendingCheck) :
    AM (Except (CheckError × Nat) Unit) := fun s =>
  match checkPendingList mode fe pend s.worker with
  | .ok (r, _) => .ok (r, s)
  | .error e => .error e

/-- con-leche: ConLeche/Cached/Installed.lean:438-455 checkDecls — **the
declaration fold as the driver runs it**: phase A (`annotFold`), then phase B
on one worker (`checkPendingWorker`).  The twin of
`arena::checker::check_decls_phased`. -/
def installThenCheckPhased (mode : CheckMode) (pins : List INatOpPinSet)
    (ds : Array IDeclaration) : AM (Except (CheckError × Nat) IFEnv) := do
  match ← annotFold mode pins (0, mkIFEnv IEnv.empty, #[]) ds.toList with
  | .error e => pure (.error e)
  | .ok (_, fe, pend) =>
    match ← checkPendingWorker mode fe pend.toList with
    | .error e => pure (.error e)
    | .ok () => pure (.ok fe)

/-! ## A worker is the phase-A state, as far as phase B can tell -/

theorem NStore.enableScratch_dropScratch (st : NStore) :
    st.dropScratch.enableScratch = st.enableScratch := rfl

theorem LStore.enableScratch_dropScratch (st : LStore) :
    st.dropScratch.enableScratch = st.enableScratch := rfl

theorem LsStore.enableScratch_dropScratch (st : LsStore) :
    st.dropScratch.enableScratch = st.enableScratch := rfl

/-- Opening the scratch tier forgets whether it was closed first. -/
theorem EStore.enableScratch_dropScratch (st : EStore) :
    st.dropScratch.enableScratch = st.enableScratch := rfl

/-- **Opening a worker's scratch tier is opening the phase-A state's**, when
the caches are empty there: `enterScratch` resets the memos and opens an
empty scratch tier over the same persistent one. -/
theorem enterScratch_worker {s : AState} (hc : s.caches = Caches.empty) :
    enterScratch s.worker = enterScratch s := by
  cases s
  simp only [AState.worker] at hc ⊢
  subst hc
  rfl

/-- **One record's check from a worker is the check from the phase-A state**,
when the caches are empty there: the two runs meet after their first
action. -/
theorem checkPending_worker {mode : CheckMode} {fe : IFEnv} {pc : PendingCheck}
    {s : AState} (hc : s.caches = Caches.empty) :
    checkPending mode fe pc s.worker = checkPending mode fe pc s := by
  unfold checkPending
  simp only [bind, StateT.bind]
  rw [enterScratch_worker hc]

/-- **Phase B on a worker accepts what phase B on the phase-A state
accepts**, and conversely: the two walks are the same after the first
record's `enterScratch`, given empty caches whenever there is a record. -/
theorem checkPendingList_worker {mode : CheckMode} {fe : IFEnv}
    {pend : List PendingCheck} {s : AState}
    (hc : pend ≠ [] → s.caches = Caches.empty) :
    ∀ {r s'}, checkPendingList mode fe pend s.worker = .ok (r, s') →
      ∃ s'', checkPendingList mode fe pend s = .ok (r, s'') := by
  intro r s' h
  cases pend with
  | nil =>
    simp only [checkPendingList, pure, StateT.pure, Except.pure] at h ⊢
    obtain ⟨rfl, -⟩ := Prod.mk.inj (Except.ok.inj h)
    exact ⟨s, rfl⟩
  | cons pc rest =>
    have hpc := checkPending_worker (mode := mode) (fe := fe) (pc := pc) (hc (by simp))
    simp only [checkPendingList] at h ⊢
    rw [hpc] at h
    exact ⟨s', h⟩

/-- A worker's walk, run: the phase-A state comes back whatever the walk
left. -/
theorem checkPendingWorker_run {mode : CheckMode} {fe : IFEnv}
    {pend : List PendingCheck} {s s₂ : AState} {r : Except (CheckError × Nat) Unit}
    (h : checkPendingList mode fe pend s.worker = .ok (r, s₂)) :
    checkPendingWorker mode fe pend s = .ok (r, s) := by
  simp only [checkPendingWorker, h]

end ConRon.Arena
