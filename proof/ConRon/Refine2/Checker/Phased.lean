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
* **the boundary** — `freeze_tier` either declines (`Native`, so the Rust
  run claims nothing: `freeze_tier_err`) or found the four flags down and
  handed back the store's own four persistent tables (`freeze_tier_ok`), and
  `thaw_tier` then restores the store exactly (`freeze_tier_ok`'s last
  conjunct);
* **the worker** — `worker_state` over that tier is related to the twin's
  `AState.worker` of the phase-A state, at the TIER as the reader parameter
  (`worker_state_rel`): its store's persistent reads go to the tier because
  its flags are up, and the tier is exactly what the phase-A store's reads
  went to because its flags were down.  So `check_pending_list_refines`
  applies at `pers := tier`;
* **the result** — the Rust's state after the fold is the phase-A state (the
  store thawed back), which is what the twin's `checkPendingWorker` hands
  back too, so `AStateRel` carries over unchanged.

Nothing here is a hypothesis: the flags, which the relation never mentions,
are read off the Rust's own guard in `freeze_tier`.
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

/-- The four `shared_on` flags of a store, down: the shape of every store the
parse and phase A work in, and what `freeze_tier`'s guard checks. -/
def Thawed (ar : arena.store.EStore) : Prop :=
  ar.shared_on = false ∧ ar.lss.shared_on = false ∧ ar.lss.ls.shared_on = false ∧
    ar.lss.ls.ns.shared_on = false

/-- The persistent tier `freeze_tier` moves out of a store: its four own
persistent tables. -/
def tierOf (ar : arena.store.EStore) : arena.store.PersTier :=
  { n := ar.lss.ls.ns.pers, l := ar.lss.ls.pers, ls := ar.lss.pers, e := ar.pers }

/-- **`freeze_tier`'s decline is the port's own**: it claims nothing. -/
theorem freeze_tier_err {ar ar' : arena.store.EStore} {e : kernel.core_types.CheckError}
    (h : arena.checker.freeze_tier ar = ok (.Err e, ar')) :
    absAErrKind e = none := by
  rw [arena.checker.freeze_tier] at h
  split at h
  · obtain ⟨s, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨v, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have h' := Result.ok_injective h
    simp only [Prod.mk.injEq, core.result.Result.Err.injEq] at h'
    rw [← h'.1]; rfl
  split at h
  · obtain ⟨s, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨v, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have h' := Result.ok_injective h
    simp only [Prod.mk.injEq, core.result.Result.Err.injEq] at h'
    rw [← h'.1]; rfl
  split at h
  · obtain ⟨s, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨v, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have h' := Result.ok_injective h
    simp only [Prod.mk.injEq, core.result.Result.Err.injEq] at h'
    rw [← h'.1]; rfl
  split at h
  · obtain ⟨s, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨v, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have h' := Result.ok_injective h
    simp only [Prod.mk.injEq, core.result.Result.Err.injEq] at h'
    rw [← h'.1]; rfl
  obtain ⟨_, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨_, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨_, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨_, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have h' := Result.ok_injective h
  simp at h'

/-- **`freeze_tier` accepts only a thawed store, and hands back its own
tier**; and `thaw_tier` of what it left, with that tier, is the store it was
handed — the boundary is invisible outside phase B. -/
theorem freeze_tier_ok {ar ar' : arena.store.EStore} {tier : arena.store.PersTier}
    (h : arena.checker.freeze_tier ar = ok (.Ok tier, ar')) :
    Thawed ar ∧ tier = tierOf ar ∧ arena.checker.thaw_tier ar' tier = ok ar := by
  rw [arena.checker.freeze_tier] at h
  split at h
  · obtain ⟨_, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨_, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have h' := Result.ok_injective h
    simp at h'
  rename_i h0
  split at h
  · obtain ⟨_, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨_, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have h' := Result.ok_injective h
    simp at h'
  rename_i h1
  split at h
  · obtain ⟨_, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨_, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have h' := Result.ok_injective h
    simp at h'
  rename_i h2
  split at h
  · obtain ⟨_, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨_, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have h' := Result.ok_injective h
    simp at h'
  rename_i h3
  obtain ⟨_, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨_, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨_, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨_, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have h' := Result.ok_injective h
  simp only [Prod.mk.injEq, core.result.Result.Ok.injEq] at h'
  obtain ⟨rfl, rfl⟩ := h'
  simp only [Bool.not_eq_true] at h0 h1 h2 h3
  refine ⟨⟨h0, h1, h2, h3⟩, rfl, ?_⟩
  rw [arena.checker.thaw_tier]
  obtain ⟨⟨⟨⟨np, ns, nsc, nsh⟩, lp, ls, lsc, lsh⟩, lsp, lss, lssc, lssh⟩, ep, es, esc, esh⟩ :=
    ar
  simp only at h0 h1 h2 h3
  subst h0 h1 h2 h3
  rfl

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

/-- **A phase-B worker over the frozen tier is the twin's worker of the
phase-A state.**  `worker_state` builds an empty store with its four flags
up, fresh memos and caches and a copy of the pins; read through `tierOf` of a
thawed phase-A store, its persistent arm is exactly the tables the phase-A
store's reads went to, so it relates to `AState.worker` of the twin state the
phase-A store relates to — at the TIER as the reader parameter, the one
`check_pending_list_refines` is then instantiated at. -/
theorem worker_state_rel {pers : arena.store.PersTier} {st : arena.monad.AState}
    {lst : AState} {w : arena.monad.AState}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st) (hth : Thawed st.store)
    (hw : arena.checker.worker_state st.pins = ok w) :
    AStateRel (tierOf st.store) w lst.worker ∧ AStateInv (tierOf st.store) w ∧
      BrOK lst.worker := by
  obtain ⟨h0, h1, h2, h3⟩ := hth
  rw [arena.checker.worker_state] at hw
  obtain ⟨est, hest, hw⟩ := ConRon.Refine.bind_eq_ok_iff.mp hw
  obtain ⟨st0, hst0, hw⟩ := ConRon.Refine.bind_eq_ok_iff.mp hw
  obtain ⟨p, hp, hw⟩ := ConRon.Refine.bind_eq_ok_iff.mp hw
  have hw' := (Result.ok_injective hw).symm
  subst hw'
  have hpv := pins_dup_val hp
  subst hpv
  -- the fresh store, one tier at a time
  rw [arena.store.EStore.empty] at hest
  obtain ⟨lss, hlss, hest⟩ := ConRon.Refine.bind_eq_ok_iff.mp hest
  obtain ⟨e, he, hest⟩ := ConRon.Refine.bind_eq_ok_iff.mp hest
  have h' := (Result.ok_injective hest).symm
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
  obtain ⟨hNR, hNI⟩ := ntables_empty hnt
  obtain ⟨hLR, hLI⟩ := ltables_empty hlt2
  obtain ⟨hLsR, hLsI⟩ := lstables_empty hlt
  obtain ⟨hER, hEI⟩ := etables_empty he
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
  refine ⟨⟨⟨⟨⟨⟨?_, hNR, rfl⟩, ?_, hLR, rfl⟩, ?_, hLsR, rfl⟩, ?_, hER, rfl⟩, hMR, hCR,
      hrel.pins, EStore.dropScratch_wf hrel.storeWF⟩,
    ⟨⟨⟨⟨⟨?_, hNI⟩, ?_, hLI⟩, ?_, hLsI⟩, ?_, hEI⟩, hMI, hCI⟩,
    EStore.dropScratch_wf hrel.storeWF, rfl⟩
  · simpa [rPersN, tierOf, h3, AState.worker, EStore.dropScratch, LsStore.dropScratch,
      LStore.dropScratch, NStore.dropScratch] using hS.lss.lvl.ns.perst
  · simpa [rPersL, tierOf, h2, AState.worker, EStore.dropScratch, LsStore.dropScratch,
      LStore.dropScratch] using hS.lss.lvl.perst
  · simpa [rPersLs, tierOf, h1, AState.worker, EStore.dropScratch, LsStore.dropScratch]
      using hS.lss.perst
  · simpa [rPersE, tierOf, h0, AState.worker, EStore.dropScratch] using hS.perst
  · simpa [rPersN, tierOf, h3] using hSI.lss.lvl.ns.perst
  · simpa [rPersL, tierOf, h2] using hSI.lss.lvl.perst
  · simpa [rPersLs, tierOf, h1] using hSI.lss.perst
  · simpa [rPersE, tierOf, h0] using hSI.perst

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
  refine ⟨⟨rfl, ?_, rfl⟩, hinv0, by simp, ?_⟩
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
`install_then_check` on both sides, and its hypotheses — `AStateRel`,
`AStateInv`, `BrOK`, ruling 2's `DeclResolves` — plus ONE more about the same
abstract invariant `Good`: `hwork`, that it survives `AState.worker` (the twin
worker drops only scratch nodes, memos and caches, none of which a resolving
handle of the environment can depend on; the capstone takes it from
`declResolves_of_stages` with the rest of `Good`).  For ANY install hook: the
hook is the driver's `--progress` line, and `annot_fold_hooked_eq` says it
cannot matter. -/
theorem check_decls_phased_refines {H : Type} {inst : arena.checker.InstallHook H}
    {h : H} {pers st lst}
    {mode : kernel.env.CheckMode}
    {pins : alloc.vec.Vec arena.nat_op_pin_set.INatOpPinSet}
    {ds : alloc.vec.Vec arena.env.IDeclaration} {o} {Good : IFEnv → AState → Prop}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st) (hbr : BrOK lst)
    (hres : DeclResolves (ConRon.Refine.absMode mode) (absINatOpPinSetL pins)
      (absIDeclL ds) lst Good)
    (hwork : ∀ {fe : IFEnv} {s : AState}, Good fe s → Good fe s.worker)
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
    (lf := mkIFEnv IEnv.empty) (i := 0#usize) hrel hinv hbr hfe hfinv hres.inv hres.entry
    (by rw [hz1]; exact hres.decls) hq'
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
    obtain ⟨v, lst', hx, hR, hrel1, hinv1, hext1⟩ := hA
    obtain ⟨n1, fe1, pend1⟩ := v
    obtain ⟨p1, f1, pd1⟩ := p'
    obtain ⟨hv1, hv2, hv3⟩ := hR
    subst hv3
    try dsimp only at hrun
    obtain ⟨fr, hfr, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    obtain ⟨r1, est1⟩ := fr
    try dsimp only at hrun
    cases hr1 : r1 with
    | Err e1 =>
      rw [hr1] at hfr hrun
      have ho := Result.ok_injective hrun
      subst ho
      intro k hk
      simp only [freeze_tier_err hfr] at hk
      exact absurd hk (by simp)
    | Ok tier =>
      rw [hr1] at hfr hrun
      obtain ⟨hth, htier, hthaw⟩ := freeze_tier_ok hfr
      subst htier
      try dsimp only at hrun
      obtain ⟨r2, hr2, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
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
      obtain ⟨hrelW, hinvW, hbrW⟩ := worker_state_rel hrel1 hinv1 hth hw
      have hx' : annotFold (ConRon.Refine.absMode mode) (absINatOpPinSetL pins)
          (0, mkIFEnv IEnv.empty, #[]) (absIDeclL ds) lst
          = .ok (.ok (n1, fe1, (absPendingCheckL pd1).toArray), lst') := hx
      have hg1 : Good fe1 lst' := annotFold_good hres.inv _ hres.entry hx'
      have hz4 : absPendingCheckLFrom pd1 0#usize = absPendingCheckL pd1 := by simp
      have hB := check_pending_list_refines (lf := fe1) (pend := pd1) (i := 0#usize)
        hrelW hinvW hbrW hv2.rel hv2.inv hres.inv (hwork hg1)
        (by
          rw [hz4]
          intro pc hpc
          exact hres.pending _ _ _ _ hx' pc (by simpa using hpc)) hwr
      simp only [SimFold, hz4] at hB
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
        obtain ⟨_, lst2, hy, -, -, -, -⟩ := hB
        have ho := Result.ok_injective hrun
        subst ho
        refine ⟨fe1, lst', ?_, hv2.rel, hrel1, hinv1, hext1⟩
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
    arena.checker.freeze_tier st'.store = ok (.Ok tier, est) ∧
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
    obtain ⟨fr, hfr, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    obtain ⟨r1, est⟩ := fr
    try dsimp only at hrun
    cases r1 with
    | Err e =>
      have h' := Result.ok_injective hrun
      simp at h'
    | Ok tier =>
      obtain ⟨n, i, v⟩ := p
      try dsimp only at hrun
      obtain ⟨r2, hr2, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      obtain ⟨e1, he1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      obtain ⟨-, -, hthaw⟩ := freeze_tier_ok hfr
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

`check_decls_phased_refines`' hypotheses verbatim.  Each worker is related on
its own: `worker_state_rel` puts its fresh state against `lst'.worker`, and
`check_pending_list_refines` walks that worker's list — whatever list the
pool gave it. -/
theorem pool_accepts_refines {H : Type} {inst : arena.checker.InstallHook H}
    {h : H} {pers st lst}
    {mode : kernel.env.CheckMode}
    {pins : alloc.vec.Vec arena.nat_op_pin_set.INatOpPinSet}
    {ds : alloc.vec.Vec arena.env.IDeclaration} {fe st'}
    {Good : IFEnv → AState → Prop}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st) (hbr : BrOK lst)
    (hres : DeclResolves (ConRon.Refine.absMode mode) (absINatOpPinSetL pins)
      (absIDeclL ds) lst Good)
    (hwork : ∀ {fe : IFEnv} {s : AState}, Good fe s → Good fe s.worker)
    (hpool : PoolAccepts inst pers st mode pins ds h fe st') :
    ∃ lfe lst', PooledAccepts (ConRon.Refine.absMode mode) (absINatOpPinSetL pins)
        (absIDeclL ds).toArray lst lfe lst' ∧
      IFEnvRel fe lfe ∧ AStateRel pers st' lst' := by
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
    (lf := mkIFEnv IEnv.empty) (i := 0#usize) hrel hinv hbr hfe hfinv hres.inv hres.entry
    (by rw [hz1]; exact hres.decls) hq'
  have hz2 : (absPendingCheckL (alloc.vec.Vec.new arena.checker.PendingCheck)).toArray
      = (#[] : Array PendingCheck) := rfl
  have hz3 : absU (0#u64) = 0 := rfl
  simp only [SimFold, hz1, hz2, hz3] at hA
  obtain ⟨v, lst', hx, hR, hrel1, hinv1, -⟩ := hA
  obtain ⟨n1, fe1, pend1⟩ := v
  obtain ⟨-, hv2, hv3⟩ := hR
  subst hv3
  obtain ⟨hth, htier, -⟩ := freeze_tier_ok hfr
  subst htier
  have hx' : annotFold (ConRon.Refine.absMode mode) (absINatOpPinSetL pins)
      (0, mkIFEnv IEnv.empty, #[]) (absIDeclL ds) lst
      = .ok (.ok (n1, fe1, (absPendingCheckL pend).toArray), lst') := hx
  have hg1 : Good fe1 lst' := annotFold_good hres.inv _ hres.entry hx'
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
    obtain ⟨hrelW, hinvW, hbrW⟩ := worker_state_rel hrel1 hinv1 hth hws
    have hz4 : absPendingCheckLFrom w 0#usize = absPendingCheckL w := by simp
    have hB := check_pending_list_refines (lf := fe1) (pend := w) (i := 0#usize)
      hrelW hinvW hbrW hv2.rel hv2.inv hres.inv (hwork hg1)
      (by
        rw [hz4]
        intro pc hpc
        refine hres.pending _ _ _ _ hx' pc ?_
        simp only [absPendingCheckL, List.mem_map] at hpc ⊢
        obtain ⟨x, hx, rfl⟩ := hpc
        exact ⟨x, hsub w hwm x hx, rfl⟩) hwr
    simp only [SimFold, hz4] at hB
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
