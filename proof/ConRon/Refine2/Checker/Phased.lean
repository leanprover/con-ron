/-
# `ConRon.Refine2.Checker.Phased` — Theorem 2 at the fold the driver runs

**Task #97-P5-Driver.**  The binary's driver (`crates/con-ron/src/driver.rs`,
unverified) is a straight line of calls into the verified crate:

    annot_fold_hooked → freeze_tier → pool::parallel_all → thaw_tier

and `arena::checker::check_decls_phased` is the same line with the one call
that is not the verified crate's — the pool — replaced by the walk it is
argued equal to, `check_pending_worker` (one `worker_state`, and
`check_pending_list` from it over the frozen tier).  This module is Theorem 2
for that function, against `Arena/Phased.lean`'s `installThenCheckPhased`:

* **phase A** — `annot_fold_hooked` IS `annot_fold` (`annot_fold_hooked_eq`:
  the hook is `Unit`-valued and reads only), so `annot_fold_refines` applies;
* **the boundary** — `freeze_tier` moves the store's four persistent tables
  out into a `frozen` tier, and `thaw_tier` puts them back, so the store comes
  back exactly (`freeze_tier_ok`; task #98-FREEZE made it a pure move, with no
  flag and no decline);
* **the worker** — `worker_state` is an empty store, frozen, and over that
  tier it is `AIdle` against the twin's `AState.worker` of the phase-A state,
  at the TIER as the reader parameter (`worker_state_rel`): its persistent
  reads go to the tier, which is exactly what the phase-A store's reads went
  to because phase A's reader is an owned store's (`hpers`).  So
  `check_pending_list_refines` applies at `pers := tier`;
* **the result** — the Rust's state after the fold is the phase-A state (the
  store thawed back), which is what the twin's `checkPendingWorker` hands
  back too, so `AStateRel₀` carries over unchanged.

The one hypothesis beyond the relation is `hpers : pers.frozen = false`, the
phase-A reader's shape (task #98-FREEZE; the capstone reads it off
`PersTier::empty`).
-/
import ConRon.Refine2.Checker.Top
import ConRon.Refine2.Checker.Init
import ConRon.Arena.Pooled

open Aeneas Aeneas.Std Result
open ConRon.Generated

attribute [-grind] U32.bv_eq_imp_eq UScalar.val_eq_imp

namespace ConRon.Refine2

open ConRon.Arena

/-! ## Phase A: the hook changes nothing -/

private theorem annot_fold_hooked_aux {H : Type} (inst : arena.checker.InstallHook H)
    (h : H) (n : Nat) :
    ∀ {pers st mode pins p} {ds : alloc.vec.Vec arena.env.IDeclaration}
      {i : Std.Usize} {o},
      ds.val.length - i.val = n →
      arena.checker.annot_fold_hooked inst pers st mode pins p ds i h = ok o →
      arena.checker.annot_fold pers st mode pins p ds i = ok o := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro pers st mode pins p ds i o hn hrun
    rw [arena.checker.annot_fold_hooked.eq_def] at hrun
    rw [arena.checker.annot_fold.eq_def]
    try dsimp only at hrun ⊢
    split at hrun
    · rename_i hge
      rw [if_pos hge]
      exact hrun
    · rename_i hge
      rw [if_neg hge]
      obtain ⟨p0, p1, p2⟩ := p
      try dsimp only at hrun
      obtain ⟨d, hd, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      obtain ⟨u, -, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      rw [hd]
      simp only [bind_tc_ok]
      obtain ⟨q, hq, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      rw [hq]
      simp only [bind_tc_ok]
      obtain ⟨r, st1⟩ := q
      try dsimp only at hrun ⊢
      cases r with
      | Err e => exact hrun
      | Ok q' =>
        try dsimp only at hrun ⊢
        obtain ⟨i2, hi2, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        rw [hi2]
        simp only [bind_tc_ok]
        have hi2v : i2.val = i.val + 1 := ConRon.Refine.HashMap.uscalar_add_eq hi2
        have hlt : i.val < ds.val.length := by
          have := alloc.vec.Vec.len_val ds; scalar_tac
        exact ih (ds.val.length - i2.val) (by omega) rfl hrun

/-- **`annot_fold_hooked` IS `annot_fold`**: the driver's phase A, with the
heartbeat's install line called before each step, has `annot_fold`'s outcome
whatever the hook — the hook returns `()` and is handed the store by shared
reference, so it has nothing to change. -/
theorem annot_fold_hooked_eq {H : Type} {inst : arena.checker.InstallHook H} {h : H}
    {pers st mode pins p} {ds : alloc.vec.Vec arena.env.IDeclaration}
    {i : Std.Usize} {o}
    (hrun : arena.checker.annot_fold_hooked inst pers st mode pins p ds i h = ok o) :
    arena.checker.annot_fold pers st mode pins p ds i = ok o :=
  annot_fold_hooked_aux inst h _ rfl hrun

/-! ## The boundary -/

/-! `tierOf` is `Refine2/Core/Bracket.lean`'s (task #98-FREEZE). -/

/-! ## The worker -/

/-- **`pins_dup` is the identity on the value.** -/
theorem pins_dup_val {p q : arena.pins.Pins} (h : arena.checker.pins_dup p = ok q) :
    q = p := by
  rw [arena.checker.pins_dup] at h
  obtain ⟨v, hv, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨v1, hv1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨li, hli, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨l, hl, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨e, he, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have h' := (Result.ok_injective h).symm
  subst h'
  have e1 : v = p.names := alloc.vec.Vec.ext _ _ (nidx_vec_dup_val hv)
  have e2 : v1 = p.reserved := alloc.vec.Vec.ext _ _ (nidx_vec_dup_val hv1)
  rw [e1, e2, dupId_lsidx _ _ hli, dupId_lidx _ _ hl, dupId_eidx _ _ he]

/-- **`freeze_tier` moves the four persistent tables out, and `thaw_tier`
puts them back**: the tier is the store's own tables, `frozen`, and the store
comes back exactly (task #98-FREEZE: a pure move, no flag and no decline). -/
theorem freeze_tier_ok {ar ar' : arena.store.EStore} {tier : arena.store.PersTier}
    (h : arena.checker.freeze_tier ar = ok (tier, ar')) :
    tier = tierOf ar ∧ arena.checker.thaw_tier ar' tier = ok ar := by
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
    {lst : AState} {w : arena.monad.AState}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hpers : pers.frozen = false)
    (hw : arena.checker.worker_state st.pins = ok w) :
    AIdle (tierOf st.store) w lst.worker ∧ AStateInv (tierOf st.store) w := by
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
  · simpa [rPersN, tierOf, hpers, AState.worker, EStore.enableScratch, EStore.dropScratch,
      LsStore.enableScratch, LsStore.dropScratch, LStore.enableScratch, LStore.dropScratch,
      NStore.enableScratch, NStore.dropScratch] using hS.lss.lvl.ns.perst
  · simpa [rPersL, tierOf, hpers, AState.worker, EStore.enableScratch, EStore.dropScratch,
      LsStore.enableScratch, LsStore.dropScratch, LStore.enableScratch,
      LStore.dropScratch] using hS.lss.lvl.perst
  · simpa [rPersLs, tierOf, hpers, AState.worker, EStore.enableScratch, EStore.dropScratch,
      LsStore.enableScratch, LsStore.dropScratch] using hS.lss.perst
  · simpa [rPersE, tierOf, hpers, AState.worker, EStore.enableScratch,
      EStore.dropScratch] using hS.perst
  · simpa [rPersN, tierOf, hpers] using hSI.lss.lvl.ns.perst
  · simpa [rPersL, tierOf, hpers] using hSI.lss.lvl.perst
  · simpa [rPersLs, tierOf, hpers] using hSI.lss.perst
  · simpa [rPersE, tierOf, hpers] using hSI.perst

/-! ## The fold -/

private theorem mk_ifenv_empty_refines' {e f}
    (he : arena.env.i_env_empty = ok e) (hf : arena.env.mk_ifenv e = ok f) :
    IFEnvRel f (mkIFEnv IEnv.empty) ∧ IFEnvInv f := by
  rw [arena.env.i_env_empty] at he
  have he' : e = { consts := alloc.vec.Vec.new arena.env.IConstantInfo } :=
    (Result.ok_injective he).symm
  subst he'
  rw [arena.env.mk_ifenv] at hf
  obtain ⟨hm, hhm, hf⟩ := ConRon.Refine.bind_eq_ok_iff.mp hf
  obtain ⟨hinv0, -, hnone⟩ :=
    ConRon.Refine.HashMap2.with_capacity_refines
      (HashableInst := arena.handle.NIdx.Insts.Con_ron_coreRonHashmapHashable) hhm
  obtain ⟨q, hq, hf⟩ := ConRon.Refine.bind_eq_ok_iff.mp hf
  rw [arena.env.mk_ifenv_go] at hq
  simp only [alloc.vec.Vec.new, alloc.vec.Vec.len, ge_iff_le, le_refl, if_pos] at hq
  have hq' : q = (0#u64, hm) := (Result.ok_injective hq).symm
  subst hq'
  have hf' := (Result.ok_injective hf).symm
  subst hf'
  refine ⟨⟨rfl, ?_, rfl, fun ci h => by simp [alloc.vec.Vec.new] at h,
    fun k p hp => by rw [hnone k] at hp; exact absurd hp (by simp)⟩, hinv0, by simp, ?_⟩
  · intro n
    rw [hnone n]
    simp [mkIFEnv, mkIFEnvGo, IEnv.empty]
  · intro n p hp
    rw [hnone n] at hp
    exact absurd hp (by simp)

private theorem toList_toArray'' {α : Type} (l : List α) : l.toArray.toList = l := rfl

/-- **`check_decls_phased_refines` — Theorem 2 at the fold the binary's driver
runs** (task #97-P5-Driver).

*The Aeneas model of `arena::checker::check_decls_phased` accepting implies
the twin's `installThenCheckPhased` accepting with the related environment,
from the related state, ending in a related state; a Rust failure is the
twin's at the same kind and the same fold position, except the port's own
`Native`, which claims nothing.*

`install_then_check_refines`' statement with the driver's fold in place of
`install_then_check` on both sides, and its hypotheses — `AStateRel₀` and
`AStateInv`, nothing else (task #97-T2-LOCKSTEP lane Checker deleted `BrOK`,
ruling 2's `DeclResolves` and its `hwork`).  For ANY install hook: the
hook is the driver's `--progress` line, and `annot_fold_hooked_eq` says it
cannot matter. -/
theorem check_decls_phased_refines {H : Type} {inst : arena.checker.InstallHook H}
    {h : H} {pers st lst}
    {mode : kernel.env.CheckMode}
    {pins : alloc.vec.Vec arena.nat_op_pin_set.INatOpPinSet}
    {ds : alloc.vec.Vec arena.env.IDeclaration} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hpers : pers.frozen = false)
    (hrun : arena.checker.check_decls_phased inst pers st mode pins ds h = ok o) :
    SimFold (fun r v => IFEnvRel r v) pers lst o
      (installThenCheckPhased (ConRon.Refine.absMode mode) (absINatOpPinSetL pins)
        (absIDeclL ds).toArray) := by
  rw [arena.checker.check_decls_phased] at hrun
  obtain ⟨t, ht, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  rw [arena.checker.fold_start] at ht
  obtain ⟨e, he, ht⟩ := ConRon.Refine.bind_eq_ok_iff.mp ht
  obtain ⟨f, hf, ht⟩ := ConRon.Refine.bind_eq_ok_iff.mp ht
  have ht' := (Result.ok_injective ht).symm
  subst ht'
  obtain ⟨hfe, hfinv⟩ := mk_ifenv_empty_refines' he hf
  obtain ⟨q, hq, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  have hq' := annot_fold_hooked_eq hq
  have hz1 : absIDeclLFrom ds 0#usize = absIDeclL ds := by simp
  have hA := annot_fold_refines
    (p := (0#u64, f, alloc.vec.Vec.new arena.checker.PendingCheck))
    (lf := mkIFEnv IEnv.empty) (i := 0#usize) hrel hinv hpers hfe hfinv hq'
  have hz2 : (absPendingCheckL (alloc.vec.Vec.new arena.checker.PendingCheck)).toArray
      = (#[] : Array PendingCheck) := rfl
  have hz3 : absU (0#u64) = 0 := rfl
  simp only [SimFold, hz1, hz2, hz3] at hA
  obtain ⟨qr, qst⟩ := q
  simp only [SimFold] at hA ⊢
  simp only [installThenCheckPhased, am_run_bind, toList_toArray'']
  cases hqr : qr with
  | Err pr =>
    rw [hqr] at hA hrun
    have ho := Result.ok_injective hrun
    subst ho
    intro k hk
    obtain ⟨le, lst', hx, hlk⟩ := hA k hk
    exact ⟨le, lst', by rw [hx]; rfl, hlk⟩
  | Ok p' =>
    rw [hqr] at hA hrun
    obtain ⟨v, lst', hx, hR, hrel1, hinv1⟩ := hA
    obtain ⟨n1, fe1, pend1⟩ := v
    obtain ⟨p1, f1, pd1⟩ := p'
    obtain ⟨hv1, hv2, hv3⟩ := hR
    subst hv3
    try dsimp only at hrun
    obtain ⟨⟨tier, est1⟩, hfr, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    obtain ⟨htier, hthaw⟩ := freeze_tier_ok hfr
    subst htier
    have htf : (tierOf qst.store).frozen = true := rfl
    try dsimp only at hrun
    · obtain ⟨r2, hr2, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      obtain ⟨e1, he1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      rw [hthaw] at he1
      have he1' := (Result.ok_injective he1).symm
      subst he1'
      -- phase B on the worker
      rw [arena.checker.check_pending_worker] at hr2
      obtain ⟨w, hw, hr2⟩ := ConRon.Refine.bind_eq_ok_iff.mp hr2
      obtain ⟨wr, hwr, hr2⟩ := ConRon.Refine.bind_eq_ok_iff.mp hr2
      obtain ⟨wres, wst⟩ := wr
      have hr2' : wres = r2 := Result.ok_injective hr2
      subst hr2'
      obtain ⟨hrelW, hinvW⟩ := worker_state_rel hrel1 hinv1 hpers hw
      have hz4 : absPendingCheckLFrom pd1 0#usize = absPendingCheckL pd1 := by simp
      have hB := check_pending_list_refines (lf := fe1) (pend := pd1) (i := 0#usize)
        hrelW hinvW htf hv2.rel hv2.inv hwr
      simp only [SimFoldIdle, hz4] at hB
      rw [hx]
      simp only [toList_toArray'']
      cases hwres : wres with
      | Err pr =>
        rw [hwres] at hB hrun
        have ho := Result.ok_injective hrun
        subst ho
        intro k hk
        obtain ⟨le, lst2, hy, hlk⟩ := hB k hk
        refine ⟨le, lst', ?_, hlk⟩
        have hW : (checkPendingWorker (ConRon.Refine.absMode mode) fe1
            (absPendingCheckL pd1)).run lst' = .ok (.error (le, absU pr.2), lst') :=
          checkPendingWorker_run hy
        simp only [except_ok_bind]
        rw [am_run_bind, hW]
        rfl
      | Ok _ =>
        rw [hwres] at hB hrun
        obtain ⟨_, lst2, hy, -, -, -⟩ := hB
        have ho := Result.ok_injective hrun
        subst ho
        refine ⟨fe1, lst', ?_, hv2.rel, hrel1, hinv1⟩
        have hW : (checkPendingWorker (ConRon.Refine.absMode mode) fe1
            (absPendingCheckL pd1)).run lst' = .ok (.ok (), lst') :=
          checkPendingWorker_run hy
        simp only [except_ok_bind]
        rw [am_run_bind, hW]
        rfl

/-! ## The pool (tasks #97-P5-POOL, #98-POOL)

The binary does not run `check_decls_phased`'s one-worker walk: its phase B
is `pool::parallel_all` (`crates/con-ron/src/pool.rs`), a generic combinator
that runs a per-index `step` on a pool of workers, each folding it over the
indices it claimed on ONE state it built with `init`.  Its contract is
`ParallelAll`, stated here generically — nothing in it is about checking —
and it is the whole of the pool's trust: the claim of `pool.rs`'s note, an
argument about that function's control flow.  The driver instantiates it
with two calls into the verified crate, `init := worker_state pins` and
`step := fun st k => check_pending tier st mode fe pend[k]` (`pendingStep`).

`PoolAccepts` is the driver's fold, accepted: phase A, the freeze, and
`ParallelAll` over the pending records.  `PoolAccepts.toParts` turns the
partition into the shape the proof consumes (`PoolAcceptsParts`: one
accepting `check_pending_worker` per worker over the records it checked,
together covering the pending list), and `pool_accepts_refines` walks that
into the twin's `PooledAccepts` with no argument about a worker's history:
each worker's run IS `check_pending_worker` on its own list, which
`check_pending_list_refines` relates from `worker_state` exactly as it does
for the one-worker walk.  `poolAccepts_of_check_decls_phased` shows the
sequential walk is one such pool (a single worker claiming `0, 1, …, m-1`),
so the hypothesis is met by the verified crate. -/

/-- **A fold with every step `Ok`**: `step` from `s` over `ks` in order,
threading the state, every call answering `.Ok ()`. -/
def FoldAllOk {S E I : Type} (step : S → I → Result (core.result.Result Unit E × S)) :
    S → List I → Prop
  | _, [] => True
  | s, k :: ks => ∃ s', step s k = ok (.Ok (), s') ∧ FoldAllOk step s' ks

/-- **The contract of `crates/con-ron/src/pool.rs`'s `parallel_all`** (task
#98-POOL) — the pool's one trusted claim, stated with nothing about what the
pool runs.  `parallel_all(n, workers, init, step, after)` returning `Ok(())`
means: the indices `0..n` were claimed by the workers, each by exactly one
(`parts.flatten` is a permutation of `List.range n`); each worker's claims
came off a monotone counter, so they increase (claim order); and each worker
built its state with `init()` ONCE and folded `step` over its claims, in claim
order, every step answering `Ok(())`.  `init` and `step` are the Aeneas models
of the two closures (`init` in `Result`, as every extracted function is);
`after`, the heartbeat hook, holds the state by `&` and is not in the
contract.  It holds at every worker count, including the count the pool fell
back to when the OS refused a thread. -/
def ParallelAll {S E : Type} (n : Nat) (init : Result S)
    (step : S → Nat → Result (core.result.Result Unit E × S)) : Prop :=
  ∃ parts : List (List Nat),
    parts.flatten.Perm (List.range n) ∧
    ∀ w ∈ parts, w.Pairwise (· < ·) ∧ ∃ s₀, init = ok s₀ ∧ FoldAllOk step s₀ w

/-- **The driver's `step` closure**, `|w, k| checker::check_pending(&tier, w,
mode, &fe, &pend[k])` (`crates/con-ron/src/driver.rs`
`check_decls_driver`), as the Aeneas model reads it: `check_pending` on the
`k`-th pending record, and a panic past the end (`&pend[k]`'s bounds check). -/
def pendingStep (tier : arena.store.PersTier) (mode : kernel.env.CheckMode)
    (fe : arena.env.IFEnv) (pend : alloc.vec.Vec arena.checker.PendingCheck)
    (st : arena.monad.AState) (k : Nat) :
    Result ((core.result.Result Unit kernel.core_types.CheckError) × arena.monad.AState) :=
  match pend.val[k]? with
  | some pc => arena.checker.check_pending tier st mode fe pc
  | none => fail .panic

/-- con-leche: Main.lean:289-316 checkPool — **the driver's fold with the
pool, accepted** (`crates/con-ron/src/driver.rs` `check_decls_driver`, one
conjunct per call): `fold_start`, phase A (`annot_fold_hooked`) accepting with
environment `fe`, pending records `pend` and state `st'`; the tier frozen out
of `st'.store`; and phase B, `parallel_all` over the pending records with the
driver's two closures, accepted — `ParallelAll`, the pool's contract.  The
driver's `thaw_tier` then restores `st'.store` exactly (`freeze_tier_ok`), so
`st'` is the state the fold hands back. -/
def PoolAccepts {H : Type} (inst : arena.checker.InstallHook H)
    (pers : arena.store.PersTier) (st : arena.monad.AState)
    (mode : kernel.env.CheckMode)
    (pins : alloc.vec.Vec arena.nat_op_pin_set.INatOpPinSet)
    (ds : alloc.vec.Vec arena.env.IDeclaration) (h : H)
    (fe : arena.env.IFEnv) (st' : arena.monad.AState) : Prop :=
  ∃ (t : Std.U64 × arena.env.IFEnv × alloc.vec.Vec arena.checker.PendingCheck)
    (n : Std.U64) (pend : alloc.vec.Vec arena.checker.PendingCheck)
    (tier : arena.store.PersTier) (est : arena.store.EStore),
    arena.checker.fold_start = ok t ∧
    arena.checker.annot_fold_hooked inst pers st mode pins t ds 0#usize h
      = ok (.Ok (n, fe, pend), st') ∧
    arena.checker.freeze_tier st'.store = ok (tier, est) ∧
    ParallelAll pend.length (arena.checker.worker_state st'.pins)
      (pendingStep tier mode fe pend)

/-- `PoolAccepts` from one premise per step of the driver — the shape the
headlines state it in (`ConRon.Capstone`'s `h6`, `h7`, `h8`): phase A as the
driver calls it, `annot_fold_hooked(…, fold_start(), ds, 0, obs)`; the
freeze; and phase B, `ParallelAll`. -/
theorem poolAccepts_intro {H : Type} {inst : arena.checker.InstallHook H}
    {h : H} {pers st mode pins ds fe st'}
    {n : Std.U64} {pend : alloc.vec.Vec arena.checker.PendingCheck}
    {tier : arena.store.PersTier} {est : arena.store.EStore}
    (hA : (do
        let t ← arena.checker.fold_start
        arena.checker.annot_fold_hooked inst pers st mode pins t ds 0#usize h)
      = ok (.Ok (n, fe, pend), st'))
    (hF : arena.checker.freeze_tier st'.store = ok (tier, est))
    (hB : ParallelAll pend.length (arena.checker.worker_state st'.pins)
      (pendingStep tier mode fe pend)) :
    PoolAccepts inst pers st mode pins ds h fe st' := by
  obtain ⟨t, ht, hA⟩ := ConRon.Refine.bind_eq_ok_iff.mp hA
  exact ⟨t, n, pend, tier, est, ht, hA, hF, hB⟩

/-- **The pool's accept, per worker** (the shape of task #97-P5-POOL's
`PoolAccepts`): phase A, the freeze, and `parts`, the record lists the
workers checked — each drawn from `pend`, together covering it — each
accepted by `check_pending_worker` over the frozen tier. -/
def PoolAcceptsParts {H : Type} (inst : arena.checker.InstallHook H)
    (pers : arena.store.PersTier) (st : arena.monad.AState)
    (mode : kernel.env.CheckMode)
    (pins : alloc.vec.Vec arena.nat_op_pin_set.INatOpPinSet)
    (ds : alloc.vec.Vec arena.env.IDeclaration) (h : H)
    (fe : arena.env.IFEnv) (st' : arena.monad.AState) : Prop :=
  ∃ (t : Std.U64 × arena.env.IFEnv × alloc.vec.Vec arena.checker.PendingCheck)
    (n : Std.U64) (pend : alloc.vec.Vec arena.checker.PendingCheck)
    (tier : arena.store.PersTier) (est : arena.store.EStore)
    (parts : List (alloc.vec.Vec arena.checker.PendingCheck)),
    arena.checker.fold_start = ok t ∧
    arena.checker.annot_fold_hooked inst pers st mode pins t ds 0#usize h
      = ok (.Ok (n, fe, pend), st') ∧
    arena.checker.freeze_tier st'.store = ok (tier, est) ∧
    (∀ pc ∈ pend.val, ∃ w ∈ parts, pc ∈ w.val) ∧
    (∀ w ∈ parts, ∀ pc ∈ w.val, pc ∈ pend.val) ∧
    (∀ w ∈ parts,
      arena.checker.check_pending_worker tier mode fe st'.pins w = ok (.Ok ()))

/-- A fold of `check_pending` over the records `v.val.drop i` is
`check_pending_list` from cursor `i`, accepting. -/
private theorem check_pending_list_of_foldAllOk {tier mode fe}
    {v : alloc.vec.Vec arena.checker.PendingCheck} :
    ∀ (pcs : List arena.checker.PendingCheck) (i : Std.Usize) (s : arena.monad.AState),
      v.val.drop i.val = pcs →
      FoldAllOk (fun st pc => arena.checker.check_pending tier st mode fe pc) s pcs →
      ∃ s', arena.checker.check_pending_list tier s mode fe v i = ok (.Ok (), s') := by
  intro pcs
  induction pcs with
  | nil =>
    intro i s hd _
    have hle : v.val.length ≤ i.val := List.drop_eq_nil_iff.mp hd
    refine ⟨s, ?_⟩
    rw [arena.checker.check_pending_list.eq_def]
    have hge : i ≥ alloc.vec.Vec.len v := by
      have := alloc.vec.Vec.len_val v; scalar_tac
    simp only [hge, ↓reduceIte]
  | cons pc pcs ih =>
    intro i s hd hf
    obtain ⟨s1, hs1, hf⟩ := hf
    have hlt : i.val < v.val.length := by
      by_contra hc
      rw [List.drop_eq_nil_of_le (by omega)] at hd; simp at hd
    have hpc : v.val[i.val] = pc := by
      rw [List.drop_eq_getElem_cons hlt] at hd
      exact (List.cons.inj hd).1
    have hrest : v.val.drop (i.val + 1) = pcs := by
      rw [List.drop_eq_getElem_cons hlt] at hd
      exact (List.cons.inj hd).2
    obtain ⟨i2, hi2, hi2v⟩ := ConRon.Refine.usize_add_ok (i := i)
      (by have := alloc.vec.Vec.len_ineq v; omega)
    obtain ⟨s', hs'⟩ := ih i2 s1 (by rw [hi2v]; exact hrest) hf
    refine ⟨s', ?_⟩
    rw [arena.checker.check_pending_list.eq_def]
    have hge : ¬ (i ≥ alloc.vec.Vec.len v) := by
      have := alloc.vec.Vec.len_val v; scalar_tac
    have hidx : alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice
        arena.checker.PendingCheck) v i = ok pc := by
      rw [alloc.vec.Vec.index_slice_index, alloc.vec.Vec.index_usize]
      rw [show v[i.val]? = v.val[i.val]? from rfl, List.getElem?_eq_getElem hlt, hpc]
    simp only [hge, ↓reduceIte, hidx, bind_tc_ok, hs1, hi2]
    exact hs'

/-- The converse: an accepting `check_pending_list` from cursor `i` is a fold
of `pendingStep` over the indices `i, i+1, …` to the end. -/
private theorem foldAllOk_of_check_pending_list {tier mode fe}
    {v : alloc.vec.Vec arena.checker.PendingCheck} (n : Nat) :
    ∀ (i : Std.Usize) (s s' : arena.monad.AState), v.val.length - i.val = n →
      arena.checker.check_pending_list tier s mode fe v i = ok (.Ok (), s') →
      FoldAllOk (pendingStep tier mode fe v) s (List.range' i.val n) := by
  induction n with
  | zero => intro _ _ _ _ _; trivial
  | succ n ih =>
    intro i s s' hn hrun
    rw [arena.checker.check_pending_list.eq_def] at hrun
    dsimp only at hrun
    split at hrun
    · rename_i hge
      have := alloc.vec.Vec.len_val v; scalar_tac
    · rename_i hge
      have hlt : i.val < v.val.length := by
        have := alloc.vec.Vec.len_val v; scalar_tac
      obtain ⟨pc, hidx, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      have hpc : v.val[i.val]? = some pc := ConRon.Refine.ExprOps.vec_index_getElem? hidx
      obtain ⟨q, hq, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      obtain ⟨qr, s1⟩ := q
      cases qr with
      | Err e =>
        have h' := Result.ok_injective hrun
        simp at h'
      | Ok u =>
        obtain ⟨i2, hi2, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        have hi2v : i2.val = i.val + 1 := ConRon.Refine.HashMap.uscalar_add_eq hi2
        refine ⟨s1, ?_, ?_⟩
        · simp only [pendingStep, hpc]; exact hq
        · have := ih i2 s1 s' (by omega) hrun
          rw [hi2v] at this; exact this

/-- A `pendingStep` fold names its records: every index is in range, and the
records at those indices are a `check_pending` fold. -/
private theorem foldAllOk_pendingStep {tier mode fe}
    {pend : alloc.vec.Vec arena.checker.PendingCheck} :
    ∀ (ks : List Nat) (s : arena.monad.AState),
      FoldAllOk (pendingStep tier mode fe pend) s ks →
      ∃ pcs : List arena.checker.PendingCheck,
        ks.map (fun k => pend.val[k]?) = pcs.map some ∧
        FoldAllOk (fun st pc => arena.checker.check_pending tier st mode fe pc) s pcs := by
  intro ks
  induction ks with
  | nil => intro _ _; exact ⟨[], rfl, trivial⟩
  | cons k ks ih =>
    intro s hf
    obtain ⟨s1, hs1, hf⟩ := hf
    unfold pendingStep at hs1
    split at hs1
    · rename_i pc hpc
      obtain ⟨pcs, hm, hf'⟩ := ih s1 hf
      exact ⟨pc :: pcs, by simp [hpc, hm], s1, hs1, hf'⟩
    · simp at hs1

/-- **The pool's contract, per worker** (task #98-POOL): a `PoolAccepts` —
`ParallelAll` over the pending records — is a `PoolAcceptsParts`, each
worker's claims read as the list of records it checked. -/
theorem PoolAccepts.toParts {H : Type} {inst : arena.checker.InstallHook H}
    {h : H} {pers st mode pins ds fe st'}
    (hp : PoolAccepts inst pers st mode pins ds h fe st') :
    PoolAcceptsParts inst pers st mode pins ds h fe st' := by
  obtain ⟨t, n, pend, tier, est, ht, hA, hF, parts, hperm, hw⟩ := hp
  -- each worker's claims, as records
  have hrec : ∀ w ∈ parts, ∃ pcs : List arena.checker.PendingCheck,
      w.map (fun k => pend.val[k]?) = pcs.map some ∧
      ∃ s₀, arena.checker.worker_state st'.pins = ok s₀ ∧
        FoldAllOk (fun st pc => arena.checker.check_pending tier st mode fe pc) s₀ pcs := by
    intro w hwm
    obtain ⟨-, s₀, hs₀, hf⟩ := hw w hwm
    obtain ⟨pcs, hm, hf'⟩ := foldAllOk_pendingStep w s₀ hf
    exact ⟨pcs, hm, s₀, hs₀, hf'⟩
  choose! recs hrecm hrecf using hrec
  have hlen : ∀ w ∈ parts, (recs w).length ≤ Std.Usize.max := by
    intro w hwm
    have h1 : (recs w).length = w.length := by
      have := congrArg List.length (hrecm w hwm); simpa using this.symm
    have h2 : w.length ≤ parts.flatten.length :=
      (List.sublist_flatten_of_mem hwm).length_le
    have h3 : parts.flatten.length = pend.val.length := by
      rw [hperm.length_eq, List.length_range]
    have := alloc.vec.Vec.len_ineq pend
    omega
  let vecs : List (alloc.vec.Vec arena.checker.PendingCheck) :=
    parts.attach.map (fun w => alloc.vec.Vec.from (recs w.1) (hlen w.1 w.2))
  refine ⟨t, n, pend, tier, est, vecs, ht, hA, hF, ?_, ?_, ?_⟩
  · intro pc hpc
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hpc
    have hjr : j ∈ parts.flatten := hperm.mem_iff.mpr (List.mem_range.mpr hj)
    obtain ⟨w, hwm, hjw⟩ := List.mem_flatten.mp hjr
    refine ⟨alloc.vec.Vec.from (recs w) (hlen w hwm),
      List.mem_map.mpr ⟨⟨w, hwm⟩, List.mem_attach _ _, rfl⟩, ?_⟩
    rw [alloc.vec.Vec.from_val]
    have hs : some pend.val[j] ∈ (recs w).map some := by
      rw [← hrecm w hwm]
      exact List.mem_map.mpr ⟨j, hjw, List.getElem?_eq_getElem hj⟩
    simpa using hs
  · intro v hv pc hpc
    obtain ⟨⟨w, hwm⟩, -, rfl⟩ := List.mem_map.mp hv
    rw [alloc.vec.Vec.from_val] at hpc
    have hs : some pc ∈ w.map (fun k => pend.val[k]?) := by
      rw [hrecm w hwm]; exact List.mem_map_of_mem hpc
    obtain ⟨k, -, hk⟩ := List.mem_map.mp hs
    exact List.mem_of_getElem? hk
  · intro v hv
    obtain ⟨⟨w, hwm⟩, -, rfl⟩ := List.mem_map.mp hv
    obtain ⟨s₀, hs₀, hf⟩ := hrecf w hwm
    obtain ⟨s', hs'⟩ := check_pending_list_of_foldAllOk (v := alloc.vec.Vec.from (recs w) (hlen w hwm))
      (recs w) 0#usize s₀ (by simp) hf
    rw [arena.checker.check_pending_worker]
    simp only [hs₀, bind_tc_ok, hs']
    rfl

/-- **The one-worker walk is a pool**: an accepting `check_decls_phased` —
the verified sequential projection — is a `PoolAccepts` with one worker
checking every record, ending in the state it returns.  So the pooled stage
asks nothing the verified crate cannot deliver. -/
theorem poolAccepts_of_check_decls_phased {H : Type}
    {inst : arena.checker.InstallHook H} {h : H} {pers st mode pins ds fe st6}
    (hrun : arena.checker.check_decls_phased inst pers st mode pins ds h
      = ok (.Ok fe, st6)) :
    PoolAccepts inst pers st mode pins ds h fe st6 := by
  rw [arena.checker.check_decls_phased] at hrun
  obtain ⟨t, ht, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨q, hq, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨qr, st1⟩ := q
  try dsimp only at hrun
  cases qr with
  | Err e =>
    have h' := Result.ok_injective hrun
    simp at h'
  | Ok p =>
    try dsimp only at hrun
    obtain ⟨⟨tier, est⟩, hfr, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    · obtain ⟨n, i, v⟩ := p
      try dsimp only at hrun
      obtain ⟨r2, hr2, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      obtain ⟨e1, he1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      obtain ⟨-, hthaw⟩ := freeze_tier_ok hfr
      rw [hthaw] at he1
      have he1' := (Result.ok_injective he1).symm
      subst he1'
      cases r2 with
      | Err e =>
        have h' := Result.ok_injective hrun
        simp at h'
      | Ok u =>
        have h' := Result.ok_injective hrun
        simp only [Prod.mk.injEq, core.result.Result.Ok.injEq] at h'
        obtain ⟨rfl, rfl⟩ := h'
        refine ⟨t, n, v, tier, est, ht, hq, hfr, [List.range v.length], by simp,
          fun w hw => ?_⟩
        rw [List.mem_singleton.mp hw]
        refine ⟨List.pairwise_lt_range, ?_⟩
        rw [arena.checker.check_pending_worker] at hr2
        obtain ⟨s₀, hs₀, hr2⟩ := ConRon.Refine.bind_eq_ok_iff.mp hr2
        obtain ⟨wr, hwr, hr2⟩ := ConRon.Refine.bind_eq_ok_iff.mp hr2
        obtain ⟨wres, wst⟩ := wr
        have hr' : wres = .Ok () := Result.ok_injective hr2
        subst hr'
        refine ⟨s₀, hs₀, ?_⟩
        have := foldAllOk_of_check_pending_list (v := v) v.length 0#usize s₀ wst
          (by simp) hwr
        simpa [List.range_eq_range'] using this

/-- **`pool_accepts_refines` — Theorem 2 at the fold the binary runs, pool
and all** (task #97-P5-POOL).

*A pooled accept of the Aeneas model — phase A, the freeze, and every
worker's `check_pending_worker` over its records — implies the twin's
`PooledAccepts` from the related state, with the related environment, ending
in a related state.*

`check_decls_phased_refines`' hypotheses verbatim (lockstep: `AStateRel₀`
and `AStateInv`, nothing about the twin — task #97-T2-LOCKSTEP lane Checker).  Each worker is related on
its own: `worker_state_rel` puts its fresh state against `lst'.worker`, and
`check_pending_list_refines` walks that worker's list — whatever list the
pool gave it. -/
theorem pool_accepts_refines {H : Type} {inst : arena.checker.InstallHook H}
    {h : H} {pers st lst}
    {mode : kernel.env.CheckMode}
    {pins : alloc.vec.Vec arena.nat_op_pin_set.INatOpPinSet}
    {ds : alloc.vec.Vec arena.env.IDeclaration} {fe st'}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hpers : pers.frozen = false)
    (hpool : PoolAccepts inst pers st mode pins ds h fe st') :
    ∃ lfe lst', PooledAccepts (ConRon.Refine.absMode mode) (absINatOpPinSetL pins)
        (absIDeclL ds).toArray lst lfe lst' ∧
      IFEnvRel fe lfe ∧ AStateRel₀ pers st' lst' := by
  obtain ⟨t, n, pend, tier, est, parts, ht, hq, hfr, hcov, hsub, hw⟩ := hpool.toParts
  rw [arena.checker.fold_start] at ht
  obtain ⟨e, he, ht⟩ := ConRon.Refine.bind_eq_ok_iff.mp ht
  obtain ⟨f, hf, ht⟩ := ConRon.Refine.bind_eq_ok_iff.mp ht
  have ht' := (Result.ok_injective ht).symm
  subst ht'
  obtain ⟨hfe, hfinv⟩ := mk_ifenv_empty_refines' he hf
  have hq' := annot_fold_hooked_eq hq
  have hz1 : absIDeclLFrom ds 0#usize = absIDeclL ds := by simp
  have hA := annot_fold_refines
    (p := (0#u64, f, alloc.vec.Vec.new arena.checker.PendingCheck))
    (lf := mkIFEnv IEnv.empty) (i := 0#usize) hrel hinv hpers hfe hfinv hq'
  have hz2 : (absPendingCheckL (alloc.vec.Vec.new arena.checker.PendingCheck)).toArray
      = (#[] : Array PendingCheck) := rfl
  have hz3 : absU (0#u64) = 0 := rfl
  simp only [SimFold, hz1, hz2, hz3] at hA
  obtain ⟨v, lst', hx, hR, hrel1, hinv1⟩ := hA
  obtain ⟨n1, fe1, pend1⟩ := v
  obtain ⟨-, hv2, hv3⟩ := hR
  subst hv3
  obtain ⟨htier, -⟩ := freeze_tier_ok hfr
  subst htier
  have hx' : annotFold (ConRon.Refine.absMode mode) (absINatOpPinSetL pins)
      (0, mkIFEnv IEnv.empty, #[]) (absIDeclL ds) lst
      = .ok (.ok (n1, fe1, (absPendingCheckL pend).toArray), lst') := hx
  -- one worker: its own `worker_state`, its own list
  have hwork1 : ∀ w ∈ parts, ∃ s'', checkPendingList (ConRon.Refine.absMode mode) fe1
      (absPendingCheckL w) lst'.worker = .ok (.ok (), s'') := by
    intro w hwm
    have hr := hw w hwm
    rw [arena.checker.check_pending_worker] at hr
    obtain ⟨ws, hws, hr⟩ := ConRon.Refine.bind_eq_ok_iff.mp hr
    obtain ⟨wr, hwr, hr⟩ := ConRon.Refine.bind_eq_ok_iff.mp hr
    obtain ⟨wres, wst⟩ := wr
    have hr' : wres = .Ok () := Result.ok_injective hr
    subst hr'
    obtain ⟨hrelW, hinvW⟩ := worker_state_rel hrel1 hinv1 hpers hws
    have hz4 : absPendingCheckLFrom w 0#usize = absPendingCheckL w := by simp
    have hB := check_pending_list_refines (lf := fe1) (pend := w) (i := 0#usize)
      hrelW hinvW rfl hv2.rel hv2.inv hwr
    simp only [SimFoldIdle, hz4] at hB
    obtain ⟨_, lst2, hy, -⟩ := hB
    exact ⟨lst2, hy⟩
  refine ⟨fe1, lst', ⟨n1, (absPendingCheckL pend).toArray,
    parts.map absPendingCheckL, ?_, ?_, ?_, ?_⟩, hv2.rel, hrel1⟩
  · simpa only [toList_toArray''] using hx'
  · intro pc hpc
    simp only [toList_toArray'', absPendingCheckL, List.mem_map] at hpc
    obtain ⟨x, hx, rfl⟩ := hpc
    obtain ⟨w, hwm, hxw⟩ := hcov x hx
    exact ⟨absPendingCheckL w, List.mem_map_of_mem hwm,
      List.mem_map_of_mem hxw⟩
  · intro lw hlw pc hpc
    simp only [List.mem_map] at hlw
    obtain ⟨w, hwm, rfl⟩ := hlw
    simp only [toList_toArray'', absPendingCheckL, List.mem_map] at hpc ⊢
    obtain ⟨x, hx, rfl⟩ := hpc
    exact ⟨x, hsub w hwm x hx, rfl⟩
  · intro lw hlw
    simp only [List.mem_map] at hlw
    obtain ⟨w, hwm, rfl⟩ := hlw
    exact hwork1 w hwm

end ConRon.Refine2
