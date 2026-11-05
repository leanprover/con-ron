/-
# `ConRon.Bridge.Checker.Frame` — what a scratch run leaves, whatever ran

`Arena.scratchRun` puts the persistent tables, the scratch flags and the pins of its
start state back, so everything here holds of ANY run, with no spec of what ran and no
hypothesis on the environment it ran at.  Two facts:

* `Store` level: a framed run projects to the projection it started from
  (by definition), and a bracket opened on a store and closed again is that
  store's projection.
* **A job's start state is the worker's, whatever ran before it**
  (`checkJobList_each`): each job ends with the worker's store, pins and empty caches,
  and opening its bracket overwrites the memos.  So a worker's list of jobs is each
  job's accept from `s'.worker`, in any order.
-/
module

public import ConRon.Arena.Checker
public import ConRon.Bridge.Promote.Pers

public section

open ConLeche ConRon.Arena

namespace ConRon.Bridge

set_option autoImplicit false

/-- con-leche: none — a scratch run, inverted. -/
theorem scratchRun_ok {α : Type} {c : AM α} {s₀ s' : AState} {a : α}
    (h : scratchRun c s₀ = .ok (a, s')) :
    ∃ s₁, c s₀ = .ok (a, s₁) ∧ s₁.store.persSizes = s₀.store.persSizes ∧
      s' = { s₁ with store := s₁.store.frameFrom s₀.store, pins := s₀.pins } := by
  unfold scratchRun at h
  cases hc : c s₀ with
  | error e => rw [hc] at h; exact nomatch h
  | ok v =>
    obtain ⟨a₁, s₁⟩ := v
    rw [hc] at h
    simp only at h
    split at h
    · rename_i hs
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨s₁, rfl, by simpa using hs, rfl⟩
    · exact nomatch h

/-- con-leche: none — `enterScratch`, inverted. -/
theorem enterScratch_inv {s s₁ : AState} {u : Unit}
    (h : enterScratch s = .ok (u, s₁)) :
    s₁ = { store := s.store.enableScratch, memos := Memos.empty, caches := s.caches,
           pins := s.pins } := by
  have h' : ((),
      ({ store := s.store.enableScratch, memos := Memos.empty, caches := s.caches,
         pins := s.pins } : AState)) = (u, s₁) := Except.ok.inj h
  exact (Prod.mk.inj h').2.symm

/-- con-leche: none — `dropScratch`, inverted. -/
theorem dropScratch_inv {s s₁ : AState} {u : Unit}
    (h : dropScratch s = .ok (u, s₁)) :
    s₁ = { store := s.store.dropScratch, memos := s.memos, caches := Caches.empty,
           pins := s.pins } := by
  have h' : ((),
      ({ store := s.store.dropScratch, memos := s.memos, caches := Caches.empty,
         pins := s.pins } : AState)) = (u, s₁) := Except.ok.inj h
  exact (Prod.mk.inj h').2.symm

/-- con-leche: none — **a recorded check ends at the projection of its start state**,
whatever `checkValueGroup` did. -/
theorem checkPending_end {mode : CheckMode} {fe : IFEnv} {pc : PendingCheck} {s s' : AState}
    (h : checkPending mode fe pc s = .ok ((), s')) :
    s'.store = s.store.dropScratch ∧ s'.caches = Caches.empty ∧ s'.pins = s.pins := by
  unfold checkPending at h
  obtain ⟨_, s₁, g1, r1⟩ := AM.bind_ok h
  obtain ⟨_, s₂, g2, r2⟩ := AM.bind_ok r1
  obtain ⟨s₃, -, -, rfl⟩ := scratchRun_ok g2
  obtain rfl := enterScratch_inv g1
  obtain rfl := dropScratch_inv r2
  exact ⟨rfl, rfl, rfl⟩

/-- con-leche: none — **a block job ends at the projection of its start state**, whatever
its checked install did. -/
theorem blockCheck_end {mode : CheckMode} {pins : List INatOpPinSet} {b : BlockCheck}
    {s s' : AState} (h : blockCheck mode pins b s = .ok ((), s')) :
    s'.store = s.store.dropScratch ∧ s'.caches = Caches.empty ∧ s'.pins = s.pins := by
  unfold blockCheck at h
  obtain ⟨_, s₁, g1, r1⟩ := AM.bind_ok h
  obtain ⟨W', s₂, g2, r2⟩ := AM.bind_ok r1
  obtain ⟨s₃, -, -, rfl⟩ := scratchRun_ok g2
  obtain rfl := enterScratch_inv g1
  obtain ⟨-, r3⟩ := AM.dunless_ok (AM.Never.fail_any) r2
  obtain rfl := dropScratch_inv r3
  exact ⟨rfl, rfl, rfl⟩

/-- con-leche: none — an accepted job ends at the projection of its start state. -/
theorem runJob_end {mode : CheckMode} {pins : List INatOpPinSet} {fe : IFEnv}
    {pend : Array PendingCheck} {D : Array BlockCheck} {j : Job} {s s' : AState}
    (h : runJob mode pins fe pend D j s = .ok (.ok (), s')) :
    s'.store = s.store.dropScratch ∧ s'.caches = Caches.empty ∧ s'.pins = s.pins := by
  unfold runJob at h
  split at h
  · split at h
    · split at h
      · rename_i hb
        simp only [Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨-, rfl⟩ := h
        exact blockCheck_end hb
      · exact nomatch h
    · exact nomatch h
  · split at h
    · split at h
      · rename_i hb
        simp only [Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨-, rfl⟩ := h
        exact checkPending_end hb
      · exact nomatch h
    · exact nomatch h

/-- con-leche: none — **a job from a state that agrees with the worker on what opening a
bracket reads is the job from the worker**. -/
theorem runJob_of_agree {mode : CheckMode} {pins : List INatOpPinSet} {fe : IFEnv}
    {pend : Array PendingCheck} {D : Array BlockCheck} {j : Job} {w y : AState}
    (hst : y.store = w.store) (hc : y.caches = w.caches) (hp : y.pins = w.pins) :
    runJob mode pins fe pend D j y = runJob mode pins fe pend D j w := by
  have hes : enterScratch y = enterScratch w := by
    obtain ⟨st, m, c, p⟩ := y
    obtain ⟨st', m', c', p'⟩ := w
    simp only at hst hc hp
    subst hst hc hp
    rfl
  unfold runJob
  split
  · split
    · unfold blockCheck
      simp only [bind, StateT.bind]
      rw [hes]
    · rfl
  · split
    · unfold checkPending
      simp only [bind, StateT.bind]
      rw [hes]
    · rfl

/-- con-leche: ConLeche/Verify/Cached/Defer.lean:246-247 JobOk — **a worker's accepted list
is each of its jobs' accept from the worker**: a job's start state is the worker's up to
what opening its bracket overwrites, whatever ran before it. -/
theorem checkJobList_each {mode : CheckMode} {pins : List INatOpPinSet} {fe : IFEnv}
    {pend : Array PendingCheck} {D : Array BlockCheck} {w : AState}
    (hw : w.store.dropScratch = w.store) (hcw : w.caches = Caches.empty) :
    ∀ (js : List Job) (y s' : AState), y.store = w.store → y.caches = Caches.empty →
      y.pins = w.pins →
      checkJobList mode pins fe pend D js y = .ok (.ok (), s') →
      ∀ j ∈ js, ∃ t, runJob mode pins fe pend D j w = .ok (.ok (), t) := by
  intro js
  induction js with
  | nil => intro _ _ _ _ _ _ _ h; exact absurd h (by simp)
  | cons a as ih =>
    intro y s' hs hc hp hrun j hj
    simp only [checkJobList] at hrun
    cases hA : runJob mode pins fe pend D a y with
    | error e => rw [hA] at hrun; exact nomatch hrun
    | ok v =>
      obtain ⟨r, y₁⟩ := v
      rw [hA] at hrun
      cases r with
      | error e => exact nomatch hrun
      | ok u =>
        have hag := runJob_of_agree (mode := mode) (pins := pins) (fe := fe) (pend := pend)
          (D := D) (j := a) hs (hc.trans hcw.symm) hp
        rcases List.mem_cons.mp hj with rfl | hj
        · exact ⟨y₁, by rw [← hag]; exact hA⟩
        · obtain ⟨h1, h2, h3⟩ := runJob_end hA
          exact ih y₁ s' (by rw [h1, hs, hw]) h2 (h3.trans hp) hrun j hj

/-- con-leche: ConLeche/Verify/Cached/Defer.lean:246-247 JobOk — **from a worker**: every
job of an accepted list is accepted by the phase-A state's worker. -/
theorem checkJobList_worker_each {mode : CheckMode} {pins : List INatOpPinSet} {fe : IFEnv}
    {pend : Array PendingCheck} {D : Array BlockCheck} {s s' : AState} {js : List Job}
    (hrun : checkJobList mode pins fe pend D js s.worker = .ok (.ok (), s')) :
    ∀ j ∈ js, ∃ t, runJob mode pins fe pend D j s.worker = .ok (.ok (), t) :=
  checkJobList_each (w := s.worker) rfl rfl js s.worker s' rfl rfl rfl hrun

/-- con-leche: ConLeche/Verify/Cached/Defer.lean:255-276 runJob — a block job the worker
accepted, as the job's own accept. -/
theorem runJob_block {mode : CheckMode} {pins : List INatOpPinSet} {fe : IFEnv}
    {pend : Array PendingCheck} {D : Array BlockCheck} {j : Job} {w t : AState}
    (hj : j.1 = true) (h : runJob mode pins fe pend D j w = .ok (.ok (), t)) :
    ∃ b, D[j.2]? = some b ∧ blockCheck mode pins b w = .ok ((), t) := by
  unfold runJob at h
  rw [hj] at h
  simp only [↓reduceIte] at h
  split at h
  · rename_i b hb
    split at h
    · rename_i hc
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h
      exact ⟨b, hb, hc⟩
    · exact nomatch h
  · exact nomatch h

/-- con-leche: ConLeche/Verify/Cached/Defer.lean:255-276 runJob — a value check the worker
accepted, as the check's own accept. -/
theorem runJob_pending {mode : CheckMode} {pins : List INatOpPinSet} {fe : IFEnv}
    {pend : Array PendingCheck} {D : Array BlockCheck} {j : Job} {w t : AState}
    (hj : j.1 = false) (h : runJob mode pins fe pend D j w = .ok (.ok (), t)) :
    ∃ pc, pend[j.2]? = some pc ∧ checkPending mode fe pc w = .ok ((), t) := by
  unfold runJob at h
  rw [hj] at h
  simp only [Bool.false_eq_true, ↓reduceIte] at h
  split at h
  · rename_i pc hb
    split at h
    · rename_i hc
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h
      exact ⟨pc, hb, hc⟩
    · exact nomatch h
  · exact nomatch h

end ConRon.Bridge
