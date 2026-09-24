/-
# `ConRon.Refine2.Checker.Phased` — Theorem 2 at the fold the driver runs

**Task #97-P5-Driver.**  The binary's driver (`crates/con-ron/src/driver.rs`,
unverified) is a straight line of calls into the verified crate:

    annot_fold_hooked → freeze_tier → pool::check_pool → thaw_tier

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

/-! ## The pool (task #97-P5-POOL)

The binary does not run `check_decls_phased`'s one-worker walk: its phase B
is `pool::check_pool`, which shares the pending records among workers, each
checking the records it claimed on ONE state it built with `worker_state`.
`PoolAccepts` is that stage, accepted, stated with verified calls only: phase
A, the freeze, and one `check_pending_worker` accept per worker over the
records that worker checked, together covering the pending list.  The pool's
trusted claim (`pool.rs`'s note, OVERVIEW §8.2) is exactly that its accept
has this shape — control flow of `pool.rs`, nothing about the checker.

`pool_accepts_refines` walks it into the twin's `PooledAccepts` with no
argument about a worker's history: each worker's run IS
`check_pending_worker` on its own list, which `check_pending_list_refines`
relates from `worker_state` exactly as it does for the one-worker walk.
`poolAccepts_of_check_decls_phased` shows the sequential walk is one such
pool (a single worker), so the hypothesis is met by the verified crate. -/

/-- con-leche: Main.lean:289-316 checkPool — **the driver's fold with the
pool, accepted**: `fold_start`, phase A (`annot_fold_hooked`) accepting with
environment `fe`, pending records `pend` and state `st'`; the tier frozen out
of `st'.store`; and `parts`, the record lists the workers checked — each
drawn from `pend`, together covering it — each accepted by
`check_pending_worker` over the frozen tier.  The driver's `thaw_tier` then
restores `st'.store` exactly (`freeze_tier_ok`), so `st'` is the state the
fold hands back. -/
def PoolAccepts {H : Type} (inst : arena.checker.InstallHook H)
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
        refine ⟨t, n, v, tier, est, [v], ht, hq, hfr,
          fun pc hpc => ⟨v, List.mem_singleton_self _, hpc⟩,
          fun w hw pc hpc => by rw [List.mem_singleton.mp hw] at hpc; exact hpc,
          fun w hw => ?_⟩
        rw [List.mem_singleton.mp hw]
        exact hr2

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
  obtain ⟨t, n, pend, tier, est, parts, ht, hq, hfr, hcov, hsub, hw⟩ := hpool
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
