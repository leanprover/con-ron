/-
# `ConRon.Refine2.Checker.Phased` — Theorem 2 at the check phase the driver runs

The binary's driver (`crates/con-ron/src/driver.rs`, unverified) is a straight line of
calls into the verified crate after the pins:

    build_index → freeze_tier → pool::parallel_all (worker_state, run_job) → thaw_tier

and the check phase is the pool's fold of the verified `run_job` over the record
positions, from one `worker_state` per worker over the frozen tier.  This module is
Theorem 2 for that line, against `Arena/Pooled.lean`'s `PooledAccepts`:

* **the index** — `build_index` from the empty index is the twin's `buildIndex`
  (`build_index_empty_refines`), the indexes related by `StreamIndexRel`;
* **the boundary** — `freeze_tier` moves the store's four persistent tables and the index
  into a `frozen` tier, and `thaw_tier` puts them back, so the store comes back exactly
  (`freeze_tier_ok`);
* **the worker** — `worker_state` is an empty store, frozen, `AIdle` against the twin's
  `AState.worker` of the driver's state at the tier (`worker_state_rel`), so
  `run_job_refines` applies job by job;
* **the result** — the Rust's state after the pool is the index build's (the store
  thawed back), which is what the twin's jobs start from too.

The one hypothesis beyond the relation is `hpers : pers.frozen = false`, the driver's
reader (the capstone reads it off `PersTier::empty`).
-/
import ConRon.Refine2.Checker.Jobs
import ConRon.Refine2.Checker.IndexBuild
import ConRon.Refine2.Checker.Init
import ConRon.Arena.Pooled

open Aeneas Aeneas.Std Result
open ConRon.Generated

attribute [-grind] U32.bv_eq_imp_eq UScalar.val_eq_imp

namespace ConRon.Refine2

open ConRon.Arena

/-! ## The boundary and the worker -/

/-- **`freeze_tier` moves the four persistent tables and the index out, and `thaw_tier`
puts them back**: the tier is the store's own tables and the index, `frozen`, and the
store comes back exactly. -/
theorem freeze_tier_ok {ar ar' : arena.store.EStore} {ix : arena.stream_index.IStreamIndex}
    {tier : arena.store.PersTier}
    (h : arena.checker.freeze_tier ar ix = ok (tier, ar')) :
    tier = tierWith ar ix ∧ arena.checker.thaw_tier ar' tier = ok (ix, ar) := by
  rw [arena.checker.freeze_tier] at h
  obtain ⟨n, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  simp only [core.mem.replace] at h
  obtain ⟨l, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨lt, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨e, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have h' := Result.ok_injective h
  simp only [Prod.mk.injEq] at h'
  obtain ⟨rfl, rfl⟩ := h'
  exact ⟨rfl, rfl⟩

/-- **A check-phase worker over the frozen tier is the twin's worker of the
driver's state, idle** (task #98-FREEZE).  `worker_state` builds an empty store
and freezes it (`EStore::empty_frozen`): its scratch tiers are on and empty,
fresh memos and caches and a copy of the pins.  Read through `tierOf` of the
driver's store — the tier `freeze_tier` moved out of it — its persistent arm
is exactly the tables the driver's store's reads went to (`hpers`: the phase-A
reader is an owned store's), so it is `AIdle` against `AState.worker` of the
twin state the driver's store relates to: related to the twin worker with its
scratch tier opened, at the TIER as the reader parameter. -/
theorem worker_state_rel {pers : arena.store.PersTier} {st : arena.monad.AState}
    {lst : AState} {w : arena.monad.AState} (ix : arena.stream_index.IStreamIndex)
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hpers : pers.frozen = false)
    (hw : arena.checker.worker_state st.pins = ok w) :
    AIdle (tierWith st.store ix) w lst.worker ∧ AStateInv (tierWith st.store ix) w := by
  rw [arena.checker.worker_state] at hw
  obtain ⟨est, hest, hw⟩ := ConRon.Refine.bind_eq_ok_iff.mp hw
  obtain ⟨st0, hst0, hw⟩ := ConRon.Refine.bind_eq_ok_iff.mp hw
  obtain ⟨p, hp, hw⟩ := ConRon.Refine.bind_eq_ok_iff.mp hw
  have hw' := (Result.ok_injective hw).symm
  subst hw'
  have hpv := pins_dup_val hp
  subst hpv
  -- the empty store, frozen
  rw [arena.store.EStore.empty_frozen] at hest
  obtain ⟨e0, he0, hest⟩ := ConRon.Refine.bind_eq_ok_iff.mp hest
  obtain ⟨⟨t0, e1⟩, hfz, hest⟩ := ConRon.Refine.bind_eq_ok_iff.mp hest
  have he1 : e1 = est := Result.ok_injective hest
  subst he1
  rw [arena.store.EStore.empty] at he0
  obtain ⟨lss, hlss, he0⟩ := ConRon.Refine.bind_eq_ok_iff.mp he0
  obtain ⟨e, he, he0⟩ := ConRon.Refine.bind_eq_ok_iff.mp he0
  have h' := (Result.ok_injective he0).symm
  subst h'
  rw [arena.store.LsStore.empty] at hlss
  obtain ⟨l, hl, hlss⟩ := ConRon.Refine.bind_eq_ok_iff.mp hlss
  obtain ⟨lt, hlt, hlss⟩ := ConRon.Refine.bind_eq_ok_iff.mp hlss
  have h' := (Result.ok_injective hlss).symm
  subst h'
  rw [arena.store.LStore.empty] at hl
  obtain ⟨n, hn, hl⟩ := ConRon.Refine.bind_eq_ok_iff.mp hl
  obtain ⟨lt2, hlt2, hl⟩ := ConRon.Refine.bind_eq_ok_iff.mp hl
  have h' := (Result.ok_injective hl).symm
  subst h'
  rw [arena.store.NStore.empty] at hn
  obtain ⟨nt, hnt, hn⟩ := ConRon.Refine.bind_eq_ok_iff.mp hn
  have h' := (Result.ok_injective hn).symm
  subst h'
  obtain ⟨-, hNI⟩ := ntables_empty hnt
  obtain ⟨-, hLI⟩ := ltables_empty hlt2
  obtain ⟨-, hLsI⟩ := lstables_empty hlt
  obtain ⟨-, hEI⟩ := etables_empty he
  rw [arena.store.EStore.freeze] at hfz
  obtain ⟨⟨n0, n1⟩, hn0, hfz⟩ := ConRon.Refine.bind_eq_ok_iff.mp hfz
  obtain ⟨⟨l0, l1⟩, hl0, hfz⟩ := ConRon.Refine.bind_eq_ok_iff.mp hfz
  obtain ⟨⟨ls0, ls1⟩, hls0, hfz⟩ := ConRon.Refine.bind_eq_ok_iff.mp hfz
  obtain ⟨ee, -, hfz⟩ := ConRon.Refine.bind_eq_ok_iff.mp hfz
  simp only [core.mem.replace] at hfz
  obtain ⟨es, hes, hfz⟩ := ConRon.Refine.bind_eq_ok_iff.mp hfz
  obtain ⟨le0, -, hfz⟩ := ConRon.Refine.bind_eq_ok_iff.mp hfz
  have h' := Result.ok_injective hfz
  simp only [Prod.mk.injEq] at h'
  obtain ⟨-, rfl⟩ := h'
  obtain ⟨ne, ns, hns, -, rfl⟩ := nstore_freeze_eq hn0
  obtain ⟨le, lsc, hlsc, -, rfl⟩ := lstore_freeze_eq hl0
  obtain ⟨lse, lssc, hlssc, -, rfl⟩ := lsstore_freeze_eq hls0
  obtain ⟨rN, iN⟩ := ntables_reset hNI hns
  obtain ⟨rL, iL⟩ := ltables_reset hLI hlsc
  obtain ⟨rLs, iLs⟩ := lstables_reset hLsI hlssc
  obtain ⟨rE, iE⟩ := etables_reset hEI hes
  -- the fresh memos and caches
  rw [arena.monad.AState.init] at hst0
  obtain ⟨m, hm, hst0⟩ := ConRon.Refine.bind_eq_ok_iff.mp hst0
  obtain ⟨c, hc, hst0⟩ := ConRon.Refine.bind_eq_ok_iff.mp hst0
  obtain ⟨p0, -, hst0⟩ := ConRon.Refine.bind_eq_ok_iff.mp hst0
  have h' := (Result.ok_injective hst0).symm
  subst h'
  obtain ⟨hMR, hMI⟩ := memos_empty hm
  obtain ⟨hCR, hCI⟩ := caches_empty hc
  -- the driver's store's persistent arm, which the tier now is
  have hS := hrel.store
  have hSI := hinv.store
  refine ⟨⟨⟨⟨⟨⟨?_, rN, rfl⟩, ?_, rL, rfl⟩, ?_, rLs, rfl⟩, ?_, rE, rfl⟩, hMR, hCR,
      hrel.pins⟩,
    ⟨⟨⟨⟨⟨?_, iN, fun _ => rfl⟩, ?_, iL, fun _ => rfl⟩, ?_, iLs, fun _ => rfl⟩, ?_, iE,
      fun _ => rfl⟩, hMI, hCI⟩⟩
  · simpa [rPersN, tierWith, hpers, AState.worker, EStore.enableScratch, EStore.dropScratch,
      LsStore.enableScratch, LsStore.dropScratch, LStore.enableScratch, LStore.dropScratch,
      NStore.enableScratch, NStore.dropScratch] using hS.lss.lvl.ns.perst
  · simpa [rPersL, tierWith, hpers, AState.worker, EStore.enableScratch, EStore.dropScratch,
      LsStore.enableScratch, LsStore.dropScratch, LStore.enableScratch,
      LStore.dropScratch] using hS.lss.lvl.perst
  · simpa [rPersLs, tierWith, hpers, AState.worker, EStore.enableScratch, EStore.dropScratch,
      LsStore.enableScratch, LsStore.dropScratch] using hS.lss.perst
  · simpa [rPersE, tierWith, hpers, AState.worker, EStore.enableScratch,
      EStore.dropScratch] using hS.perst
  · simpa [rPersN, tierWith, hpers] using hSI.lss.lvl.ns.perst
  · simpa [rPersL, tierWith, hpers] using hSI.lss.lvl.perst
  · simpa [rPersLs, tierWith, hpers] using hSI.lss.perst
  · simpa [rPersE, tierWith, hpers] using hSI.perst

/-! ## The pool (tasks #97-P5-POOL, #98-POOL)

The check phase is `pool::parallel_all` (`crates/con-ron/src/pool.rs`), a generic
combinator that runs a per-index `step` on a pool of workers, each folding it over the
indices it claimed, in increasing order, on ONE state it built with `init`.  Its contract
is `ParallelAll`, stated here generically — nothing in it is about checking — and it is
the whole of the pool's trust.  The driver instantiates it with two calls into the
verified crate, `init := worker_state pins` and `step := fun st k => run_job tier st mode
pins ds (k as u64)` (`jobStep`). -/

/-- **A fold with every step `Ok`**: `step` from `s` over `ks` in order,
threading the state, every call answering `.Ok ()`. -/
def FoldAllOk {S E I : Type} (step : S → I → Result (core.result.Result Unit E × S)) :
    S → List I → Prop
  | _, [] => True
  | s, k :: ks => ∃ s', step s k = ok (.Ok (), s') ∧ FoldAllOk step s' ks

/-- **The contract of `crates/con-ron/src/pool.rs`'s `parallel_all`** (task #98-POOL) —
the pool's one trusted claim, stated with nothing about what the pool runs.
`parallel_all(n, workers, init, step, after)` returning `Ok(())` means: every index in
`0..n` was claimed by some worker; and each worker built its state with `init()` ONCE and
folded `step` over its claims, in claim order, which is increasing (one monotone counter
hands them out), every step answering `Ok(())`.  Nothing is promised about an index
claimed twice.  An index `≥ n` needs no clause: the driver's `step` fails there
(`jobStep`), so an accepting fold never claims one.  `init` and `step` are the Aeneas
models of the two closures; `after`, the heartbeat hook, holds the state by `&` and is not
in the contract.  It holds at every worker count. -/
def ParallelAll {S E : Type} (n : Nat) (init : Result S)
    (step : S → Nat → Result (core.result.Result Unit E × S)) : Prop :=
  ∃ parts : List (List Nat),
    (∀ k < n, ∃ w ∈ parts, k ∈ w) ∧
    ∀ w ∈ parts, w.Pairwise (· < ·) ∧ ∃ s₀, init = ok s₀ ∧ FoldAllOk step s₀ w

/-- **The driver's `step` closure**, `|w, k| checker::run_job(&tier, w, &mode, &ipins, ds,
k as u64)` (`crates/con-ron/src/driver.rs` `check_decls_driver`), as the Aeneas model
reads it: `run_job` at the `usize` index cast up to a `u64`.  The pool's indices are
`usize`s, so a `Nat` past one is a panic. -/
def jobStep (tier : arena.store.PersTier) (mode : kernel.env.CheckMode)
    (pins : alloc.vec.Vec arena.nat_op_pin_set.INatOpPinSet)
    (ds : alloc.vec.Vec arena.env.IDeclaration) (st : arena.monad.AState) (k : Nat) :
    Result ((core.result.Result Unit (kernel.core_types.CheckError × Std.U64)) ×
      arena.monad.AState) :=
  if h : k < 2 ^ UScalarTy.Usize.numBits then
    arena.checker.run_job tier st mode pins ds
      (UScalar.cast .U64 (UScalar.ofNatCore (ty := .Usize) k h))
  else fail .panic

/-- con-leche: ConLeche/Driver/CheckPool.lean:236-269 checkPool — **the driver's check
phase, accepted** (`crates/con-ron/src/driver.rs` `check_decls_driver`, one conjunct per
call): the index built from the empty one, accepting with index `ix` and state `st'`; the
tier frozen out of `st'.store` and `ix`; and `parallel_all` over the record positions
with the driver's two closures, accepted — `ParallelAll`, the pool's contract.  The
driver's `thaw_tier` then restores `st'.store` exactly (`freeze_tier_ok`), so `st'` is the
state the phase hands back. -/
def PoolAccepts (pers : arena.store.PersTier) (st : arena.monad.AState)
    (mode : kernel.env.CheckMode)
    (pins : alloc.vec.Vec arena.nat_op_pin_set.INatOpPinSet)
    (ds : alloc.vec.Vec arena.env.IDeclaration)
    (ix : arena.stream_index.IStreamIndex) (st' : arena.monad.AState) : Prop :=
  ∃ (tier : arena.store.PersTier) (est : arena.store.EStore),
    arena.stream_index.build_index pers st ixEmpty ds 0#usize = ok (.Ok ix, st') ∧
    arena.checker.freeze_tier st'.store ix = ok (tier, est) ∧
    ParallelAll ds.length (arena.checker.worker_state st'.pins) (jobStep tier mode pins ds)

/-- `PoolAccepts` from one premise per call of the driver — the shape the headlines state
it in: the index build from `stream_index_empty()`, the freeze, the pool. -/
theorem poolAccepts_intro {pers st mode pins ds ix st'}
    {tier : arena.store.PersTier} {est : arena.store.EStore}
    (hI : (do
        let e ← arena.stream_index.stream_index_empty
        arena.stream_index.build_index pers st e ds 0#usize) = ok (.Ok ix, st'))
    (hF : arena.checker.freeze_tier st'.store ix = ok (tier, est))
    (hB : ParallelAll ds.length (arena.checker.worker_state st'.pins)
      (jobStep tier mode pins ds)) :
    PoolAccepts pers st mode pins ds ix st' := by
  rw [stream_index_empty_eq, bind_ok] at hI
  exact ⟨tier, est, hI, hF, hB⟩

/-- **A worker's fold ⊑ `checkJobList`**: each claimed index is a record position, and the
worker's jobs, from its one idle state, are the twin's. -/
theorem foldAllOk_jobStep_refines {tier} {I : IStreamIndex} {mode : kernel.env.CheckMode}
    {pins : alloc.vec.Vec arena.nat_op_pin_set.INatOpPinSet}
    {ds : alloc.vec.Vec arena.env.IDeclaration}
    (hI : StreamIndexRel tier.env I) (htf : tier.frozen = true) :
    ∀ (ks : List Nat) {st lst},
      AIdle tier st lst → AStateInv tier st →
      FoldAllOk (jobStep tier mode pins ds) st ks →
      (∀ k ∈ ks, k < ds.val.length) ∧
      ∃ s'', checkJobList (ConRon.Refine.absMode mode) (absINatOpPinSetL pins) I
        (absIDeclL ds).toArray ks lst = .ok (.ok (), s'')
  | [], _, lst, _, _, _ => ⟨by simp, lst, rfl⟩
  | k :: ks, _, lst, hidle, hinv, ⟨_, hs1, hf⟩ => by
    unfold jobStep at hs1
    split at hs1
    · rename_i hk
      have hu : (UScalar.cast .U64 (UScalar.ofNatCore (ty := .Usize) k hk)).val = k := by
        rw [usize_cast_u64_val']; rfl
      have hkU : (UScalar.cast .U64 (UScalar.ofNatCore (ty := .Usize) k hk)).val
          ≤ Std.Usize.max := by
        rw [hu, Std.Usize.max]; simp only [UScalarTy.numBits] at hk ⊢; omega
      obtain ⟨hlt, lst1, hx, hidle1, hinv1⟩ := run_job_refines hidle hinv htf hI hkU hs1
      rw [hu] at hlt
      have hau : absU (UScalar.cast .U64 (UScalar.ofNatCore (ty := .Usize) k hk)) = k := hu
      rw [hau] at hx
      obtain ⟨hall, s'', h⟩ := foldAllOk_jobStep_refines hI htf ks hidle1 hinv1 hf
      refine ⟨?_, s'', ?_⟩
      · intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact hlt
        · exact hall x hx
      · simp only [checkJobList]
        rw [show runJob _ _ I _ k lst = .ok (.ok (), lst1) from hx]
        exact h
    · simp at hs1

/-- **`pool_accepts_refines` — Theorem 2 at the check phase the binary runs, pool and all**
(tasks #97-P5-POOL, #141, #143).

*An accept of the Aeneas model — the index build, the freeze, and every worker's fold of
`run_job` over its claims — implies the twin's `PooledAccepts` from the related state,
the indexes related, ending in a related state.*

Lockstep hypotheses (`AStateRel₀` and `AStateInv`, nothing about the twin).  Each worker
is related on its own: `worker_state_rel` puts its fresh state against `lst'.worker`, and
`foldAllOk_jobStep_refines` walks that worker's list. -/
theorem pool_accepts_refines {pers st lst}
    {mode : kernel.env.CheckMode}
    {pins : alloc.vec.Vec arena.nat_op_pin_set.INatOpPinSet}
    {ds : alloc.vec.Vec arena.env.IDeclaration} {ix st'}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hpers : pers.frozen = false)
    (hpool : PoolAccepts pers st mode pins ds ix st') :
    ∃ I lst', PooledAccepts (ConRon.Refine.absMode mode) (absINatOpPinSetL pins)
        (absIDeclL ds).toArray lst I lst' ∧
      AStateRel₀ pers st' lst' ∧ StreamIndexRel ix I := by
  obtain ⟨tier, est, hB, hfr, parts, hcov, hw⟩ := hpool
  obtain ⟨I, lst', hx, hrel1, hinv1, hI⟩ := build_index_empty_refines hrel hinv hB
  obtain ⟨htier, -⟩ := freeze_tier_ok hfr
  subst htier
  have hwork : ∀ w ∈ parts, (∀ k ∈ w, k < ds.val.length) ∧
      ∃ s'', checkJobList (ConRon.Refine.absMode mode) (absINatOpPinSetL pins) I
        (absIDeclL ds).toArray w lst'.worker = .ok (.ok (), s'') := by
    intro w hwm
    obtain ⟨-, ws, hws, hf⟩ := hw w hwm
    obtain ⟨hrelW, hinvW⟩ := worker_state_rel ix hrel1 hinv1 hpers hws
    exact foldAllOk_jobStep_refines hI rfl w hrelW hinvW hf
  refine ⟨I, lst', ⟨parts, hx, fun t ht => ?_, fun w hw' t ht => ?_,
    fun w hw' => (hw w hw').1, fun w hw' => (hwork w hw').2⟩, hrel1, hI⟩
  · exact hcov t (by simpa [absIDeclL] using ht)
  · simpa [absIDeclL] using (hwork w hw').1 t ht

/-- info: 'ConRon.Refine2.pool_accepts_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms pool_accepts_refines

end ConRon.Refine2
