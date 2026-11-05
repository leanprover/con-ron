/-
# `ConRon.Refine2.Checker.Phased` — Theorem 2 at the fold the driver runs

**Task #97-P5-Driver.**  The binary's driver (`crates/con-ron/src/driver.rs`,
unverified) is a straight line of calls into the verified crate:

    install_fold_hooked → job_order → freeze_tier → check_layer → pool::parallel_all → thaw_tier

and phase B is the pool's fold of the verified `run_job` over the jobs, from one
`worker_state` over the frozen tier.  This module is Theorem 2 for that line, against
`Arena/Pooled.lean`'s `PooledAccepts`:

* **phase A** — `install_fold_hooked` IS `install_fold` (`install_fold_hooked_eq`:
  the hook is `Unit`-valued and reads only), so `install_fold_refines` applies;
* **the boundary** — `freeze_tier` moves the store's four persistent tables and the
  installed index out into a `frozen` tier, and `thaw_tier` puts them back, so the store
  comes back exactly (`freeze_tier_ok`);
* **the worker** — `worker_state` is an empty store, frozen, and over that
  tier it is `AIdle` against the twin's `AState.worker` of the phase-A state,
  at the TIER as the reader parameter (`worker_state_rel`): its persistent
  reads go to the tier, which is exactly what the phase-A store's reads went
  to because phase A's reader is an owned store's (`hpers`).  So
  `run_job_refines` applies at `pers := tier`, job by job;
* **the environment** — a job reads an own layer over the frozen base (`Refine2/Checker/
  Jobs.lean`), the fold's `EnvExt` is why that answers as the twin's one environment does;
* **the result** — the Rust's state after the fold is the phase-A state (the
  store thawed back), which is what the twin's `checkJobList` hands back too, so
  `AStateRel₀` carries over unchanged.

The two hypotheses beyond the relation are `hpers : pers.frozen = false` and
`hpe : PersEnvEmpty pers`, the phase-A reader's shape (the capstone reads both off
`PersTier::empty`).
-/
import ConRon.Refine2.Checker.Jobs
import ConRon.Refine2.Checker.Init
import ConRon.Arena.Pooled

open Aeneas Aeneas.Std Result
open ConRon.Generated

attribute [-grind] U32.bv_eq_imp_eq UScalar.val_eq_imp

namespace ConRon.Refine2

open ConRon.Arena

/-! ## Phase A: the hook changes nothing -/

private theorem install_fold_hooked_aux {H : Type} (inst : arena.checker.InstallHook H)
    (h : H) (n : Nat) :
    ∀ {pers st mode pins p} {ds : alloc.vec.Vec arena.env.IDeclaration}
      {i : Std.Usize} {o},
      ds.val.length - i.val = n →
      arena.checker.install_fold_hooked inst pers st mode pins p ds i h = ok o →
      arena.checker.install_fold pers st mode pins p ds i = ok o := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro pers st mode pins p ds i o hn hrun
    rw [arena.checker.install_fold_hooked.eq_def] at hrun
    rw [arena.checker.install_fold.eq_def]
    try dsimp only at hrun ⊢
    split at hrun
    · rename_i hge
      rw [ite_eq_left hge]
      exact hrun
    · rename_i hge
      rw [ite_eq_right hge]
      obtain ⟨p0, p1, p2⟩ := p
      obtain ⟨d, hd, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      obtain ⟨u, -, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      rw [hd]
      simp only [bind_ok]
      obtain ⟨q, hq, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      rw [hq]
      simp only [bind_ok]
      obtain ⟨r, st1⟩ := q
      cases r with
      | Err e => exact hrun
      | Ok q' =>
        obtain ⟨i2, hi2, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        rw [hi2]
        simp only [bind_ok]
        have hi2v : i2.val = i.val + 1 := ConRon.Refine.HashMap.uscalar_add_eq hi2
        have hlt : i.val < ds.val.length := by
          have := alloc.vec.Vec.len_val ds; scalar_tac
        exact ih (ds.val.length - i2.val) (by omega) rfl hrun

/-- **`install_fold_hooked` IS `install_fold`**: the driver's phase A, with the
heartbeat's install line called before each step, has `install_fold`'s outcome
whatever the hook — the hook returns `()` and is handed the store by shared
reference, so it has nothing to change. -/
theorem install_fold_hooked_eq {H : Type} {inst : arena.checker.InstallHook H} {h : H}
    {pers st mode pins p} {ds : alloc.vec.Vec arena.env.IDeclaration}
    {i : Std.Usize} {o}
    (hrun : arena.checker.install_fold_hooked inst pers st mode pins p ds i h = ok o) :
    arena.checker.install_fold pers st mode pins p ds i = ok o :=
  install_fold_hooked_aux inst h _ rfl hrun

/-! ## The worker -/

/-- **`freeze_tier` moves the four persistent tables and the index out, and `thaw_tier`
puts them back**: the tier is the store's own tables and the installed environment,
`frozen`, and the store comes back exactly. -/
theorem freeze_tier_ok {ar ar' : arena.store.EStore} {fe : arena.env.IFEnv}
    {tier : arena.store.PersTier}
    (h : arena.checker.freeze_tier ar fe = ok (tier, ar')) :
    tier = tierWith ar fe ∧ arena.checker.thaw_tier ar' tier = ok (fe, ar) := by
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

/-- **A phase-B worker over the frozen tier is the twin's worker of the
phase-A state, idle** (task #98-FREEZE).  `worker_state` builds an empty store
and freezes it (`EStore::empty_frozen`): its scratch tiers are on and empty,
fresh memos and caches and a copy of the pins.  Read through `tierOf` of the
phase-A store — the tier `freeze_tier` moved out of it — its persistent arm
is exactly the tables the phase-A store's reads went to (`hpers`: the phase-A
reader is an owned store's), so it is `AIdle` against `AState.worker` of the
twin state the phase-A store relates to: related to the twin worker with its
scratch tier opened, at the TIER as the reader parameter. -/
theorem worker_state_rel {pers : arena.store.PersTier} {st : arena.monad.AState}
    {lst : AState} {w : arena.monad.AState} (fe : arena.env.IFEnv)
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hpers : pers.frozen = false)
    (hw : arena.checker.worker_state st.pins = ok w) :
    AIdle (tierWith st.store fe) w lst.worker ∧ AStateInv (tierWith st.store fe) w := by
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
  -- the phase-A store's persistent arm, which the tier now is
  have hS := hrel.store
  have hSI := hinv.store
  refine ⟨⟨⟨⟨⟨⟨?_, rN, rfl⟩, ?_, rL, rfl⟩, ?_, rLs, rfl⟩, ?_, rE, rfl⟩, hMR, hCR,
      hrel.pins⟩,
    ⟨⟨⟨⟨⟨?_, iN, fun _ => rfl⟩, ?_, iL, fun _ => rfl⟩, ?_, iLs, fun _ => rfl⟩, ?_, iE,
      fun _ => rfl⟩, hMI, hCI⟩⟩
  · simpa [rPersN, tierWith, tierOf, hpers, AState.worker, EStore.enableScratch, EStore.dropScratch,
      LsStore.enableScratch, LsStore.dropScratch, LStore.enableScratch, LStore.dropScratch,
      NStore.enableScratch, NStore.dropScratch] using hS.lss.lvl.ns.perst
  · simpa [rPersL, tierWith, tierOf, hpers, AState.worker, EStore.enableScratch, EStore.dropScratch,
      LsStore.enableScratch, LsStore.dropScratch, LStore.enableScratch,
      LStore.dropScratch] using hS.lss.lvl.perst
  · simpa [rPersLs, tierWith, tierOf, hpers, AState.worker, EStore.enableScratch, EStore.dropScratch,
      LsStore.enableScratch, LsStore.dropScratch] using hS.lss.perst
  · simpa [rPersE, tierWith, tierOf, hpers, AState.worker, EStore.enableScratch,
      EStore.dropScratch] using hS.perst
  · simpa [rPersN, tierWith, tierOf, hpers] using hSI.lss.lvl.ns.perst
  · simpa [rPersL, tierWith, tierOf, hpers] using hSI.lss.lvl.perst
  · simpa [rPersLs, tierWith, tierOf, hpers] using hSI.lss.perst
  · simpa [rPersE, tierWith, tierOf, hpers] using hSI.perst

/-! ## The fold -/

private theorem mk_ifenv_empty_refines' {pers : arena.store.PersTier} {E₀ : IEnv} {e f}
    (he : arena.env.i_env_empty = ok e) (hf : arena.env.mk_ifenv e = ok f) :
    IFEnvRel pers E₀ f (mkIFEnv IEnv.empty) ∧ IFEnvInv f := by
  rw [arena.env.i_env_empty] at he
  have he' : e =
      { consts := alloc.vec.Vec.new arena.env.IConstantInfo,
        tables := alloc.vec.Vec.new arena.env.IProjTable } :=
    (Result.ok_injective he).symm
  subst he'
  rw [arena.env.mk_ifenv] at hf
  obtain ⟨hm, hhm, hf⟩ := ConRon.Refine.bind_eq_ok_iff.mp hf
  obtain ⟨hinv0, -, hnone⟩ :=
    ConRon.Refine.HashMap2.with_capacity_refines
      (HashableInst := arena.handle.NIdx.Insts.Con_ron_coreRonHashmapHashable) hhm
  obtain ⟨q, hq, hf⟩ := ConRon.Refine.bind_eq_ok_iff.mp hf
  rw [arena.env.mk_ifenv_go] at hq
  simp only [alloc.vec.Vec.new, alloc.vec.Vec.len, ge_iff_le] at hq
  have hq' : q = (0#u64, hm) := (Result.ok_injective hq).symm
  subst hq'
  obtain ⟨hm1, hhm1, hf1⟩ := ConRon.Refine.bind_eq_ok_iff.mp hf
  obtain ⟨tinv0, -, tnone⟩ :=
    ConRon.Refine.HashMap2.with_capacity_refines
      (HashableInst := arena.handle.NIdx.Insts.Con_ron_coreRonHashmapHashable) hhm1
  obtain ⟨tb, htb, hf2⟩ := ConRon.Refine.bind_eq_ok_iff.mp hf1
  rw [arena.env.mk_tbls_go] at htb
  simp only [alloc.vec.Vec.new, alloc.vec.Vec.len, ge_iff_le] at htb
  have htb' : tb = hm1 := (Result.ok_injective htb).symm
  subst htb'
  have hf' := (Result.ok_injective hf2).symm
  subst hf'
  refine ⟨⟨rfl, ?_, rfl, fun ci h => by simp [alloc.vec.Vec.new] at h,
    fun k p hp => by rw [hnone k] at hp; exact absurd hp (by simp), ?_,
    fun k s hs => by rw [tnone k] at hs; exact absurd hs (by simp)⟩,
    hinv0, by simp, ?_, tinv0, ?_⟩
  · intro n
    rw [hnone n]
    simp [mkIFEnv, mkIFEnvGo, IEnv.empty]
  · intro n
    rw [tnone n]
    simp [mkIFEnv, mkIFEnvTblsGo, IEnv.empty]
  · intro n p hp
    rw [hnone n] at hp
    exact absurd hp (by simp)
  · intro n s hs
    rw [tnone n] at hs
    exact absurd hs (by simp)

/-! ## The pool (tasks #97-P5-POOL, #98-POOL)

The binary's phase B is `pool::parallel_all` (`crates/con-ron/src/pool.rs`), a generic
combinator that runs a per-index `step` on a pool of workers, each folding it over the
indices it claimed on ONE state it built with `init`.  Its contract is `ParallelAll`,
stated here generically — nothing in it is about checking — and it is the whole of the
pool's trust.  The driver instantiates it with two calls into the verified crate,
`init := worker_state pins` and `step := fun st k => run_job tier st mode layer pend d
order[k]` (`jobStep`).

`PoolAccepts` is the driver's fold, accepted: phase A, the jobs' order, the freeze, the
check layer and `ParallelAll` over the jobs.  `PoolAccepts.toParts` turns the claims into
the shape the proof consumes (`PoolAcceptsParts`: per worker, an accepting fold of
`run_job` from one `worker_state` over the jobs it ran, together covering them), and
`pool_accepts_refines` walks that into the twin's `PooledAccepts` with no argument about
a worker's history. -/

/-- **A fold with every step `Ok`**: `step` from `s` over `ks` in order,
threading the state, every call answering `.Ok ()`. -/
def FoldAllOk {S E I : Type} (step : S → I → Result (core.result.Result Unit E × S)) :
    S → List I → Prop
  | _, [] => True
  | s, k :: ks => ∃ s', step s k = ok (.Ok (), s') ∧ FoldAllOk step s' ks

/-- **The contract of `crates/con-ron/src/pool.rs`'s `parallel_all`** (task
#98-POOL) — the pool's one trusted claim, stated with nothing about what the
pool runs.  `parallel_all(n, workers, init, step, after)` returning `Ok(())`
means: every index in `0..n` was claimed by some worker; and each worker
built its state with `init()` ONCE and folded `step` over its claims, in claim
order, every step answering `Ok(())`.  Nothing more is promised about the
claims (task #98-H8): not that each index was claimed only once, nor that a
worker's claims increase.  `pool.rs` does hand them out off a monotone
counter, so both hold, but the proof uses neither — each job is checked
against its own environment, so Theorem 1 covers any order, any split and any
repetition.  An index `≥ n` needs no clause either: the driver's `step` fails
there (`jobStep`), so an accepting fold never claims one.  `init` and `step` are the
Aeneas models of the two closures (`init` in `Result`, as every extracted function is);
`after`, the heartbeat hook, holds the state by `&` and is not in the contract.  It
holds at every worker count, including the count the pool fell back to when the OS
refused a thread. -/
def ParallelAll {S E : Type} (n : Nat) (init : Result S)
    (step : S → Nat → Result (core.result.Result Unit E × S)) : Prop :=
  ∃ parts : List (List Nat),
    (∀ k < n, ∃ w ∈ parts, k ∈ w) ∧
    ∀ w ∈ parts, ∃ s₀, init = ok s₀ ∧ FoldAllOk step s₀ w

/-- **The driver's `step` closure**, `|w, k| checker::run_job(&tier, w, mode, &layer,
&pend, &blocks, &order[k])` (`crates/con-ron/src/driver.rs` `check_decls_driver`), as the
Aeneas model reads it: `run_job` on the `k`-th job, and a panic past the end. -/
def jobStep (tier : arena.store.PersTier) (mode : kernel.env.CheckMode)
    (layer : arena.env.IFEnv) (pend : alloc.vec.Vec arena.checker.PendingCheck)
    (d : alloc.vec.Vec arena.checker.BlockCheck) (order : alloc.vec.Vec (Bool × Std.U64))
    (st : arena.monad.AState) (k : Nat) :
    Result ((core.result.Result Unit (kernel.core_types.CheckError × Std.U64)) ×
      arena.monad.AState) :=
  match order.val[k]? with
  | some j => arena.checker.run_job tier st mode layer pend d j
  | none => fail .panic

/-- con-leche: ConLeche/Driver/CheckPool.lean:236-269 checkPool — **the driver's fold with
the pool, accepted** (`crates/con-ron/src/driver.rs` `check_decls_driver`, one conjunct
per call): `fold_start`, phase A (`install_fold_hooked`) accepting with environment `fe`,
pending records `pend`, block jobs `d` and state `st'`; the jobs' order; the tier frozen
out of `st'.store` and `fe`; the check layer; and phase B, `parallel_all` over the jobs
with the driver's two closures, accepted — `ParallelAll`, the pool's contract.  The
driver's `thaw_tier` then restores `st'.store` and `fe` exactly (`freeze_tier_ok`), so `st'`
is the state the fold hands back. -/
def PoolAccepts {H : Type} (inst : arena.checker.InstallHook H)
    (pers : arena.store.PersTier) (st : arena.monad.AState)
    (mode : kernel.env.CheckMode)
    (pins : alloc.vec.Vec arena.nat_op_pin_set.INatOpPinSet)
    (ds : alloc.vec.Vec arena.env.IDeclaration) (h : H)
    (fe : arena.env.IFEnv) (st' : arena.monad.AState) : Prop :=
  ∃ (t : Std.U64 × arena.env.IFEnv × alloc.vec.Vec arena.checker.PendingCheck ×
      alloc.vec.Vec arena.checker.BlockCheck)
    (n : Std.U64) (pend : alloc.vec.Vec arena.checker.PendingCheck)
    (d : alloc.vec.Vec arena.checker.BlockCheck)
    (order : alloc.vec.Vec (Bool × Std.U64))
    (tier : arena.store.PersTier) (est : arena.store.EStore) (layer : arena.env.IFEnv),
    arena.checker.fold_start = ok t ∧
    arena.checker.install_fold_hooked inst pers st mode pins t ds 0#usize h
      = ok (.Ok (n, fe, pend, d), st') ∧
    arena.checker.job_order pend d = ok order ∧
    arena.checker.freeze_tier st'.store fe = ok (tier, est) ∧
    arena.checker.check_layer = ok layer ∧
    ParallelAll order.length (arena.checker.worker_state st'.pins)
      (jobStep tier mode layer pend d order)

/-- `PoolAccepts` from one premise per step of the driver — the shape the headlines state
it in (`ConRon.Capstone`'s `h6`, `h7`, `h8`): phase A as the driver calls it,
`install_fold_hooked(…, fold_start(), ds, 0, obs)`; the order; the freeze; the layer; and
phase B, `ParallelAll`. -/
theorem poolAccepts_intro {H : Type} {inst : arena.checker.InstallHook H}
    {h : H} {pers st mode pins ds fe st'}
    {n : Std.U64} {pend : alloc.vec.Vec arena.checker.PendingCheck}
    {d : alloc.vec.Vec arena.checker.BlockCheck} {order : alloc.vec.Vec (Bool × Std.U64)}
    {tier : arena.store.PersTier} {est : arena.store.EStore} {layer : arena.env.IFEnv}
    (hA : (do
        let t ← arena.checker.fold_start
        arena.checker.install_fold_hooked inst pers st mode pins t ds 0#usize h)
      = ok (.Ok (n, fe, pend, d), st'))
    (hO : arena.checker.job_order pend d = ok order)
    (hF : arena.checker.freeze_tier st'.store fe = ok (tier, est))
    (hL : arena.checker.check_layer = ok layer)
    (hB : ParallelAll order.length (arena.checker.worker_state st'.pins)
      (jobStep tier mode layer pend d order)) :
    PoolAccepts inst pers st mode pins ds h fe st' := by
  obtain ⟨t, ht, hA⟩ := ConRon.Refine.bind_eq_ok_iff.mp hA
  exact ⟨t, n, pend, d, order, tier, est, layer, ht, hA, hO, hF, hL, hB⟩

/-- A `jobStep` fold names its jobs: every index is in range, and the jobs at those
indices are a `run_job` fold. -/
private theorem foldAllOk_jobStep {tier mode layer pend d order} :
    ∀ (ks : List Nat) (s : arena.monad.AState),
      FoldAllOk (jobStep tier mode layer pend d order) s ks →
      ∃ js : List (Bool × Std.U64),
        ks.map (fun k => order.val[k]?) = js.map some ∧
        FoldAllOk (fun st j => arena.checker.run_job tier st mode layer pend d j) s js := by
  intro ks
  induction ks with
  | nil => intro _ _; exact ⟨[], rfl, trivial⟩
  | cons k ks ih =>
    intro s hf
    obtain ⟨s1, hs1, hf⟩ := hf
    unfold jobStep at hs1
    split at hs1
    · rename_i j hj
      obtain ⟨js, hm, hf'⟩ := ih s1 hf
      exact ⟨j :: js, by simp [hj, hm], s1, hs1, hf'⟩
    · simp at hs1

/-- **A worker's fold ⊑ `checkJobList`**. -/
theorem foldAllOk_run_job_refines {tier layer pend d lf lp lD} {mode : kernel.env.CheckMode}
    {lpins : List INatOpPinSet}
    (hJ : JobsRel tier layer pend d lf lp lD) :
    ∀ (js : List (Bool × Std.U64)) {st lst},
      AIdle tier st lst → AStateInv tier st → tier.frozen = true →
      FoldAllOk (fun st j => arena.checker.run_job tier st mode layer pend d j) st js →
      ∃ s'', checkJobList (ConRon.Refine.absMode mode) lpins lf lp lD (js.map absJob) lst
        = .ok (.ok (), s'')
  | [], _, lst, _, _, _, _ => ⟨lst, rfl⟩
  | j :: js, _, lst, hidle, hinv, htf, ⟨_, hs1, hf⟩ => by
    obtain ⟨lst1, hx, hidle1, hinv1⟩ := run_job_refines hJ hidle hinv htf hs1
    obtain ⟨s'', h⟩ := foldAllOk_run_job_refines hJ js hidle1 hinv1 htf hf
    refine ⟨s'', ?_⟩
    simp only [List.map_cons, checkJobList, hx]
    exact h

/-- **`pool_accepts_refines` — Theorem 2 at the fold the binary runs, pool and all**
(task #97-P5-POOL, #141).

*A pooled accept of the Aeneas model — phase A, the order, the freeze, and every worker's
fold of `run_job` over its jobs — implies the twin's `PooledAccepts` from the related
state, with the related environment, ending in a related state.*

Lockstep hypotheses (`AStateRel₀` and `AStateInv`, nothing about the twin).  Each worker
is related on its own: `worker_state_rel` puts its fresh state against `lst'.worker`, and
`foldAllOk_run_job_refines` walks that worker's list. -/
theorem pool_accepts_refines {H : Type} {inst : arena.checker.InstallHook H}
    {h : H} {pers st lst}
    {mode : kernel.env.CheckMode}
    {pins : alloc.vec.Vec arena.nat_op_pin_set.INatOpPinSet}
    {ds : alloc.vec.Vec arena.env.IDeclaration} {fe st'}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hpers : pers.frozen = false) (hpe : PersEnvEmpty pers)
    (hpool : PoolAccepts inst pers st mode pins ds h fe st') :
    ∃ lfe lst', PooledAccepts (ConRon.Refine.absMode mode) (absINatOpPinSetL pins)
        (absIDeclL ds).toArray lst lfe lst' ∧
      IFEnvOwn fe lfe ∧ AStateRel₀ pers st' lst' := by
  obtain ⟨t, n, pend, d, order, tier, est, layer, ht, hq, hO, hfr, hL, parts, hcov, hw⟩ := hpool
  rw [arena.checker.fold_start] at ht
  obtain ⟨e, he, ht⟩ := ConRon.Refine.bind_eq_ok_iff.mp ht
  obtain ⟨f, hf, ht⟩ := ConRon.Refine.bind_eq_ok_iff.mp ht
  have ht' := (Result.ok_injective ht).symm
  subst ht'
  obtain ⟨hfe, hfinv⟩ := mk_ifenv_empty_refines' he hf
  have hq' := install_fold_hooked_eq hq
  have hstart : FoldR pers (0#u64, f, alloc.vec.Vec.new _, alloc.vec.Vec.new _)
      (0, mkIFEnv IEnv.empty, #[], #[]) :=
    ⟨rfl, ⟨hfe.toRel hpe, hfinv⟩, rfl, envOK_empty, List.Forall₂.nil⟩
  have hz1 : absIDeclLFrom ds 0#usize = absIDeclL ds := by simp
  have hA := install_fold_refines (i := 0#usize) hrel hinv hpers hpe hstart hq'
  simp only [SimFold, hz1] at hA
  obtain ⟨v, lst', hx, hR, hrel1, hinv1⟩ := hA
  obtain ⟨n1, fe1, lp, lD⟩ := v
  obtain ⟨-, hv2, hv3, hok, hjobs⟩ := hR
  simp only at hv2 hv3 hok hjobs
  obtain ⟨htier, -⟩ := freeze_tier_ok hfr
  subst htier
  have hown := hv2.rel.toOwn hpe
  obtain ⟨hJ, hOrd⟩ := jobs_rel hown hv2.inv hok hjobs hL hO hv3
  -- one worker: its own `worker_state`, its own list
  have hwork1 : ∀ w ∈ parts, ∃ js : List (Bool × Std.U64),
      w.map (fun k => order.val[k]?) = js.map some ∧
      ∃ s'', checkJobList (ConRon.Refine.absMode mode) (absINatOpPinSetL pins) fe1 lp lD
        (js.map absJob) lst'.worker = .ok (.ok (), s'') := by
    intro w hwm
    obtain ⟨ws, hws, hf⟩ := hw w hwm
    obtain ⟨hrelW, hinvW⟩ := worker_state_rel fe hrel1 hinv1 hpers hws
    obtain ⟨js, hm, hf'⟩ := foldAllOk_jobStep w ws hf
    exact ⟨js, hm, foldAllOk_run_job_refines hJ js hrelW hinvW rfl hf'⟩
  choose! recs hrecm hrecf using hwork1
  refine ⟨fe1, lst', ⟨n1, lp, lD, parts.map (fun w => (recs w).map absJob), ?_, ?_, ?_, ?_⟩,
    hown, hrel1⟩
  · exact hx
  · intro j hj
    rw [hOrd] at hj
    obtain ⟨x, hxm, rfl⟩ := List.mem_map.mp hj
    obtain ⟨i, hi, hix⟩ := List.getElem_of_mem hxm
    obtain ⟨w, hwm, hiw⟩ := hcov i hi
    refine ⟨(recs w).map absJob, List.mem_map_of_mem (f := fun w => (recs w).map absJob) hwm,
      List.mem_map_of_mem ?_⟩
    have hs : some x ∈ (recs w).map some := by
      rw [← hrecm w hwm]
      exact List.mem_map.mpr ⟨i, hiw, by rw [List.getElem?_eq_getElem hi, hix]⟩
    simpa using hs
  · intro lw hlw j hj
    obtain ⟨w, hwm, rfl⟩ := List.mem_map.mp hlw
    obtain ⟨x, hxm, rfl⟩ := List.mem_map.mp hj
    rw [hOrd]
    refine List.mem_map_of_mem ?_
    have hs : some x ∈ w.map (fun k => order.val[k]?) := by
      rw [hrecm w hwm]; exact List.mem_map_of_mem hxm
    obtain ⟨k, -, hk⟩ := List.mem_map.mp hs
    exact List.mem_of_getElem? hk
  · intro lw hlw
    obtain ⟨w, hwm, rfl⟩ := List.mem_map.mp hlw
    exact hrecf w hwm

end ConRon.Refine2
