import ConRon.Bridge.Grouping.Checker

/-!
# `ConRon.Bridge.Checker.Grouping` — phase B does not care how records are grouped

**Task #98-GROUP, part 1.**  Phase B runs on a pool: each worker builds one
state (`AState.worker`, `Arena/Phased.lean`) and folds `checkPending` over the
records it claims.  The capstone used to take the pool's partition as a
premise (`PoolAccepts`, `Refine2/Checker/Phased.lean`).  This module proves, at
the TWIN, that the partition does not matter: a record's outcome does not
depend on the records the same worker checked before it.

## Why

`checkPending` is a bracket.  `enterScratch` opens an empty scratch tier over
the persistent one and resets the per-call memos; `checkValueGroup` runs;
`dropScratch` flushes the per-declaration caches and drops the scratch tier.
So a check READS exactly three things of the state it starts from — the
persistent tiers (`s.store.enableScratch`), the caches and the pin table —
and that is `PhaseBEquiv` below (`checkPending_congr`: equivalent starts give
the SAME result, state included).

What it WRITES back is the frame: an accepting check leaves the persistent
tiers and the pins exactly as it found them and the caches empty
(`checkPending_frame`).  The persistent half is the one real theorem: every
function the check reaches interns only into the open scratch tier and never
writes the pins.  That is `Bridge/Grouping/*.lean`: one `@[spec]` Hoare
triple per twin function reachable from `checkValueGroup` (≈ 400 of them,
`Monad` → `ExprOps` → `Pins`/`Env`/`PropRead` → `Core` → the knot →
`CheckerSplit`), each saying the invariant `Inv k p` — all four scratch flags
up, persistent tiers `k`, pins `p` — is kept.  The triples are uniform, so
they are stated and proved by three commands (`#keeps`, `#keeps_ind`,
`#keeps_fuel`, `Bridge/Grouping/Gen.lean`) over `mvcgen`; the handful of
functions whose recursion `mvcgen` cannot unfold on its own (well-founded
recursion, the `whnfApp`/`betaPeel` mutual block, continuation-passing
`whnfStep`/`defeqStep`, the structural `defeqPeel` whose equation lemmas
time out) are written by hand.

## The statements

* `checkPending_congr` — equivalent starts, identical runs;
* `checkPending_frame` — an accepting run ends equivalent to its start (with
  the caches empty, which every worker start has);
* `checkPending_after_accept` — hence after an accepting record, every
  further record runs exactly as it would have from the start;
* `checkPendingList_accepts_iff` — the fold over any record list accepts
  from a cache-empty state iff every record accepts from that state;
* `checkPendingList_grouping` — so for any grouping `ws` covering the same
  records as `ks`, the fold over `ks` accepts iff every group's fold accepts
  (all from the same worker start);
* `checkPendingWorker_accepts_iff` / `checkPendingWorker_grouping` — the same
  at `Arena.checkPendingWorker`, the driver's sequential projection, and its
  per-record form at the phase-A state itself.
-/

namespace ConRon.Bridge.Grouping

open ConRon.Arena Std.Do

/-! ## The frame of `checkValueGroup` -/

/-- A Hoare triple of `AM` read as a run. -/
theorem triple_run {α : Type} {prog : AM α} {s s' : AState} {a : α}
    {P : AState → Prop} {Q : AState → Prop}
    (hp : P s) (h : prog s = .ok (a, s'))
    (hwp : ⦃fun s => ⌜P s⌝⦄ prog ⦃⇓? _r s'' => ⌜Q s''⌝⦄) : Q s' := by
  have hs := hwp s
  simp only [WP.wp, PredTrans.apply_pushArg] at hs
  change (StateT.run prog s) = _ at h
  rw [h] at hs
  exact hs hp

theorem EStore.enableScratch_idem (st : EStore) :
    st.enableScratch.enableScratch = st.enableScratch := rfl

theorem allOn_enableScratch (st : EStore) : AllOn st.enableScratch :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- **`checkValueGroup` keeps the persistent tiers and the pins**, from any
state whose scratch tier is open. -/
theorem checkValueGroup_frame {mode : ConLeche.CheckMode} {fe : IFEnv} {g : ValueGroup}
    {s s' : AState} (hon : AllOn s.store) (h : checkValueGroup mode fe g s = .ok ((), s')) :
    s'.store.enableScratch = s.store.enableScratch ∧ s'.pins = s.pins := by
  have := triple_run (P := Inv s.store.enableScratch s.pins)
    (Q := Inv s.store.enableScratch s.pins) ⟨hon, rfl, rfl⟩ h
    (checkValueGroup_keeps _ _)
  exact ⟨this.2.1, this.2.2⟩

/-! ## The bracket -/

/-- `checkPending` as an equation: the entry state, the check, the drop. -/
theorem checkPending_eq (mode : ConLeche.CheckMode) (fe : IFEnv) (pc : PendingCheck) (s : AState) :
    checkPending mode fe pc s =
      match checkValueGroup mode (fe.restrictTo pc.vis) pc.vg
          { store := s.store.enableScratch, memos := Memos.empty, caches := s.caches,
            pins := s.pins } with
      | .ok ((), s₂) => .ok ((), { store := s₂.store.dropScratch, memos := s₂.memos,
                                   caches := Caches.empty, pins := s₂.pins })
      | .error e => .error e := by
  have he : enterScratch s = .ok ((),
      { store := s.store.enableScratch, memos := Memos.empty, caches := s.caches,
        pins := s.pins }) := rfl
  simp only [checkPending, bind, StateT.bind, he, Except.bind]
  cases h : checkValueGroup mode (fe.restrictTo pc.vis) pc.vg
      { store := s.store.enableScratch, memos := Memos.empty, caches := s.caches,
        pins := s.pins } with
  | error e => rfl
  | ok v => obtain ⟨⟨⟩, s₂⟩ := v; rfl

/-- **What a phase-B check reads of its start state**: the persistent tiers,
the caches and the pins.  (The scratch tier and the memos are reset by
`enterScratch`.) -/
def PhaseBEquiv (s t : AState) : Prop :=
  s.store.enableScratch = t.store.enableScratch ∧ s.caches = t.caches ∧ s.pins = t.pins

theorem PhaseBEquiv.refl (s : AState) : PhaseBEquiv s s := ⟨rfl, rfl, rfl⟩

theorem PhaseBEquiv.symm {s t : AState} (h : PhaseBEquiv s t) : PhaseBEquiv t s :=
  ⟨h.1.symm, h.2.1.symm, h.2.2.symm⟩

theorem PhaseBEquiv.trans {s t u : AState} (h₁ : PhaseBEquiv s t) (h₂ : PhaseBEquiv t u) :
    PhaseBEquiv s u :=
  ⟨h₁.1.trans h₂.1, h₁.2.1.trans h₂.2.1, h₁.2.2.trans h₂.2.2⟩

/-- **(a), congruence**: from equivalent start states a check runs
IDENTICALLY — same verdict, same final state. -/
theorem checkPending_congr {mode : ConLeche.CheckMode} {fe : IFEnv} {pc : PendingCheck}
    {s t : AState} (h : PhaseBEquiv s t) :
    checkPending mode fe pc s = checkPending mode fe pc t := by
  obtain ⟨h1, h2, h3⟩ := h
  rw [checkPending_eq, checkPending_eq, h1, h2, h3]

/-- **(a), the frame**: an accepting check ends in a state equivalent to its
start with the caches emptied — the persistent tiers and the pins are
untouched. -/
theorem checkPending_frame {mode : ConLeche.CheckMode} {fe : IFEnv} {pc : PendingCheck}
    {s s' : AState} (h : checkPending mode fe pc s = .ok ((), s')) :
    s'.store.enableScratch = s.store.enableScratch ∧ s'.caches = Caches.empty ∧
      s'.pins = s.pins := by
  rw [checkPending_eq] at h
  split at h
  · rename_i s₂ hvg
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    obtain ⟨he, hp⟩ := checkValueGroup_frame (allOn_enableScratch _) hvg
    exact ⟨he.trans (EStore.enableScratch_idem _), rfl, hp⟩
  · exact nomatch h

/-- The frame as an equivalence, at a cache-empty start. -/
theorem checkPending_equiv {mode : ConLeche.CheckMode} {fe : IFEnv} {pc : PendingCheck}
    {s s' : AState} (hc : s.caches = Caches.empty)
    (h : checkPending mode fe pc s = .ok ((), s')) : PhaseBEquiv s' s := by
  obtain ⟨h1, h2, h3⟩ := checkPending_frame h
  exact ⟨h1, h2.trans hc.symm, h3⟩

/-- **(a)**: after an accepting check from a cache-empty state (every worker
start is one, `AState.worker`), every further check — of any record, at any
mode and environment — runs exactly as it would have from the start. -/
theorem checkPending_after_accept {mode : ConLeche.CheckMode} {fe : IFEnv} {pc : PendingCheck}
    {s s' : AState} (hc : s.caches = Caches.empty)
    (h : checkPending mode fe pc s = .ok ((), s')) (mode' : ConLeche.CheckMode) (fe' : IFEnv)
    (pc' : PendingCheck) :
    checkPending mode' fe' pc' s' = checkPending mode' fe' pc' s :=
  checkPending_congr (checkPending_equiv hc h)

/-! ## (b) Grouping independence -/

/-- A record accepted from a state. -/
def Accepts (mode : ConLeche.CheckMode) (fe : IFEnv) (pc : PendingCheck) (s : AState) : Prop :=
  ∃ s', checkPending mode fe pc s = .ok ((), s')

/-- A record list's fold accepted from a state. -/
def ListAccepts (mode : ConLeche.CheckMode) (fe : IFEnv) (ks : List PendingCheck)
    (s : AState) : Prop :=
  ∃ s', checkPendingList mode fe ks s = .ok (.ok (), s')

theorem Accepts.congr {mode : ConLeche.CheckMode} {fe : IFEnv} {pc : PendingCheck}
    {s t : AState} (h : PhaseBEquiv s t) : Accepts mode fe pc s ↔ Accepts mode fe pc t := by
  unfold Accepts; rw [checkPending_congr h]

/-- **The fold accepts iff every record does, from the start state**, for
any cache-empty start. -/
theorem checkPendingList_accepts_iff {mode : ConLeche.CheckMode} {fe : IFEnv} :
    ∀ (ks : List PendingCheck) (s : AState), s.caches = Caches.empty →
      (ListAccepts mode fe ks s ↔ ∀ pc ∈ ks, Accepts mode fe pc s) := by
  intro ks
  induction ks with
  | nil =>
    intro s _
    simp only [ListAccepts, checkPendingList, List.not_mem_nil, false_implies, implies_true,
      iff_true]
    exact ⟨s, rfl⟩
  | cons pc rest ih =>
    intro s hc
    constructor
    · rintro ⟨s', h⟩
      simp only [checkPendingList] at h
      split at h
      · rename_i s₁ h1
        have heq := checkPending_equiv hc h1
        have hc₁ : s₁.caches = Caches.empty := heq.2.1.trans hc
        have hrest := (ih s₁ hc₁).1 ⟨s', h⟩
        intro q hq
        rcases List.mem_cons.mp hq with rfl | hq
        · exact ⟨s₁, h1⟩
        · exact (Accepts.congr heq).1 (hrest q hq)
      · exact absurd h (by simp)
    · intro hall
      obtain ⟨s₁, h1⟩ := hall pc List.mem_cons_self
      have heq := checkPending_equiv hc h1
      have hc₁ : s₁.caches = Caches.empty := heq.2.1.trans hc
      obtain ⟨s', hr⟩ := (ih s₁ hc₁).2 (fun q hq =>
        (Accepts.congr heq).2 (hall q (List.mem_cons_of_mem _ hq)))
      refine ⟨s', ?_⟩
      simp only [checkPendingList, h1]
      exact hr

/-- **(b) GROUPING INDEPENDENCE**: for any grouping `ws` of the records `ks`
(any lists covering exactly the same records — a partition among workers, in
any order), the single fold over `ks` from a cache-empty worker start accepts
iff every group's fold from that same start accepts. -/
theorem checkPendingList_grouping {mode : ConLeche.CheckMode} {fe : IFEnv}
    {ks : List PendingCheck} {ws : List (List PendingCheck)} {s : AState}
    (hc : s.caches = Caches.empty) (hcover : ∀ pc, pc ∈ ks ↔ ∃ w ∈ ws, pc ∈ w) :
    ListAccepts mode fe ks s ↔ ∀ w ∈ ws, ListAccepts mode fe w s := by
  rw [checkPendingList_accepts_iff ks s hc]
  constructor
  · intro h w hw
    rw [checkPendingList_accepts_iff w s hc]
    exact fun pc hpc => h pc ((hcover pc).2 ⟨w, hw, hpc⟩)
  · intro h pc hpc
    obtain ⟨w, hw, hpcw⟩ := (hcover pc).1 hpc
    exact (checkPendingList_accepts_iff w s hc).1 (h w hw) pc hpcw

theorem AState.worker_caches (s : AState) : s.worker.caches = Caches.empty := rfl

/-- **The driver's sequential projection, per record**: `checkPendingWorker`
accepts iff every record accepts from the worker start. -/
theorem checkPendingWorker_accepts_iff {mode : ConLeche.CheckMode} {fe : IFEnv}
    {pend : List PendingCheck} {s : AState} :
    (∃ s', checkPendingWorker mode fe pend s = .ok (.ok (), s')) ↔
      ∀ pc ∈ pend, Accepts mode fe pc s.worker := by
  rw [← checkPendingList_accepts_iff pend s.worker (AState.worker_caches s)]
  constructor
  · rintro ⟨s', h⟩
    simp only [checkPendingWorker] at h
    split at h
    · rename_i r s₂ h2
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, -⟩ := h
      exact ⟨s₂, h2⟩
    · exact nomatch h
  · rintro ⟨s₂, h⟩
    exact ⟨s, checkPendingWorker_run h⟩

/-- … and per record at the phase-A state itself, when its caches are empty
(`Arena.checkPending_worker`). -/
theorem checkPendingWorker_accepts_iff' {mode : ConLeche.CheckMode} {fe : IFEnv}
    {pend : List PendingCheck} {s : AState} (hc : s.caches = Caches.empty) :
    (∃ s', checkPendingWorker mode fe pend s = .ok (.ok (), s')) ↔
      ∀ pc ∈ pend, Accepts mode fe pc s := by
  rw [checkPendingWorker_accepts_iff]
  simp only [Accepts, checkPending_worker hc]

/-- **(b) at the driver**: a pool whose workers' lists `ws` cover the pending
records `pend` accepts on every worker (each from its own fresh
`AState.worker`) iff the single sequential worker `checkPendingWorker`
accepts. -/
theorem checkPendingWorker_grouping {mode : ConLeche.CheckMode} {fe : IFEnv}
    {pend : List PendingCheck} {ws : List (List PendingCheck)} {s : AState}
    (hcover : ∀ pc, pc ∈ pend ↔ ∃ w ∈ ws, pc ∈ w) :
    (∀ w ∈ ws, ListAccepts mode fe w s.worker) ↔
      ∃ s', checkPendingWorker mode fe pend s = .ok (.ok (), s') := by
  rw [checkPendingWorker_accepts_iff, ← checkPendingList_accepts_iff pend s.worker
    (AState.worker_caches s), checkPendingList_grouping (AState.worker_caches s) hcover]

end ConRon.Bridge.Grouping
