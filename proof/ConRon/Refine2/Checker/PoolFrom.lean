/-
# `ConRon.Refine2.Checker.PoolFrom` — Theorem 2 at the check phase of a module's worker

A module's worker (task #166, `frontend/modular/worker.rs`) checks the jobs from position
`start` on of the context's records followed by its own: the driver runs `parallel_all` over
`ds.len() - start` claims, claim `k` the job at position `start + k` (the binary's `olean_job`).
`OleanPoolAcceptsFromSol` is that accept; `olean_pool_accepts_from_sol_refines` relates it to the
twin's `PooledOleanAcceptsFromJ`, through the flat path's job lemma
(`foldAllOk_oleanJobStepSol_refines`) at the claims shifted by `start`.  At `start = 0` this is
`OleanPoolAcceptsSol`'s statement.
-/
import ConRon.Refine2.Checker.Phased

open Aeneas Aeneas.Std Result
open ConRon.Generated

namespace ConRon.Refine2

open ConRon.Arena

/-- A fold over shifted claims is the fold over the claims shifted. -/
theorem foldAllOk_shift {S E : Type} (step : S → Nat → Result (core.result.Result Unit E × S))
    (start : Nat) : ∀ (w : List Nat) (s : S),
    FoldAllOk (fun s k => step s (start + k)) s w → FoldAllOk step s (w.map (start + ·))
  | [], _, _ => trivial
  | _ :: ks, _, ⟨s', h, hf⟩ => ⟨s', h, foldAllOk_shift step start ks s' hf⟩

/-- con-leche: ConLeche/Driver/CheckMain.lean:154-177 checkOleansG — **the driver's check
phase on a module's worker, accepted**: the index built from the empty one over all of `ds`,
the tier frozen, and `parallel_all` over the `ds.length - start` claims, claim `k` the
`--olean` job at position `start + k`. -/
def OleanPoolAcceptsFromSol {F : Type} (inst : frontend.checker_io.CheckerFs F) (fs : F)
    (pers : arena.store.PersTier) (st : arena.monad.AState) (mode : kernel.env.CheckMode)
    (pins : alloc.vec.Vec arena.nat_op_pin_set.INatOpPinSet)
    (ds : alloc.vec.Vec arena.env.IDeclaration) (pk : frontend.olean.spec.OleanPins)
    (values : alloc.vec.Vec frontend.olean.records.ModRef)
    (sp : frontend.olean.files.Roots) (sol : Option arena.justify.Solution) (start : Nat)
    (ix : arena.stream_index.IStreamIndex) (st' : arena.monad.AState) : Prop :=
  ∃ (tier : arena.store.PersTier) (est : arena.store.EStore),
    arena.stream_index.build_index pers st ixEmpty ds 0#usize = ok (.Ok ix, st') ∧
    arena.checker.freeze_tier st'.store ix = ok (tier, est) ∧
    ParallelAll (ds.length - start) (oleanWorkerInit st'.pins)
      (fun w k => oleanJobStepSol inst fs tier mode pins ds pk values sp sol w (start + k))

/-- `OleanPoolAcceptsFromSol` from one premise per call of the driver. -/
theorem oleanPoolAcceptsFromSol_intro {F : Type} {inst : frontend.checker_io.CheckerFs F} {fs : F}
    {pers st mode pins ds pk values sp sol start ix st'}
    {tier : arena.store.PersTier} {est : arena.store.EStore}
    (hI : (do
        let e ← arena.stream_index.stream_index_empty
        arena.stream_index.build_index pers st e ds 0#usize) = ok (.Ok ix, st'))
    (hF : arena.checker.freeze_tier st'.store ix = ok (tier, est))
    (hB : ParallelAll (ds.length - start) (oleanWorkerInit st'.pins)
      (fun w k => oleanJobStepSol inst fs tier mode pins ds pk values sp sol w (start + k))) :
    OleanPoolAcceptsFromSol inst fs pers st mode pins ds pk values sp sol start ix st' := by
  rw [stream_index_empty_eq, bind_ok] at hI
  exact ⟨tier, est, hI, hF, hB⟩

open ConRon.Refine2.Frontend.Olean in
/-- **`olean_pool_accepts_from_sol_refines` — Theorem 2 at the check phase of a module's
worker**: an accept of the Aeneas model, the index, the freeze and every worker's fold of the
binary's `olean_job` at `sol` over its claims shifted by `start`, implies the twin's
`PooledOleanAcceptsFromJ` at `start`, from the related state, as
`olean_pool_accepts_sol_refines`. -/
theorem olean_pool_accepts_from_sol_refines {F : Type} {inst : frontend.checker_io.CheckerFs F}
    {fsv : F} {fs : Arena.Frontend.Olean.OleanFs} {pers st lst}
    {mode : kernel.env.CheckMode}
    {pins : alloc.vec.Vec arena.nat_op_pin_set.INatOpPinSet}
    {ds : alloc.vec.Vec arena.env.IDeclaration} {pk : frontend.olean.spec.OleanPins}
    {values : alloc.vec.Vec frontend.olean.records.ModRef}
    {values' : Array Arena.Frontend.Olean.ModRef} {sp : frontend.olean.files.Roots}
    {sol : Option arena.justify.Solution} {J : Option ISolution} (hJ : OptSolRel sol J)
    {start : Nat} {ix st'}
    (hfs : FsRel inst fsv fs) (hv : List.Forall₂ ModRefRel values.val values'.toList)
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hpers : pers.frozen = false)
    (hpool : OleanPoolAcceptsFromSol inst fsv pers st mode pins ds pk values sp sol start ix st') :
    ∃ I lst', PooledOleanAcceptsFromJ fs (absPins pk) (absRoots sp) values'
        (ConRon.Refine.absMode mode) (absINatOpPinSetL pins) J start (absIDeclL ds).toArray
        lst I lst' ∧
      AStateRel₀ pers st' lst' ∧ AStateInv pers st' ∧ StreamIndexRel ix I := by
  obtain ⟨tier, est, hB, hfr, parts, hcov, hw⟩ := hpool
  obtain ⟨I, lst', hx, hrel1, hinv1, hI, hF⟩ := build_index_empty_refines hrel hinv hB
  obtain ⟨htier, -⟩ := freeze_tier_ok hfr
  subst htier
  have hwork : ∀ w ∈ parts, (∀ k ∈ w.map (start + ·), k < ds.val.length) ∧
      ∃ s'', checkOleanJobListJ fs (absPins pk) (absRoots sp) values'
        (ConRon.Refine.absMode mode) (absINatOpPinSetL pins) J I (absIDeclL ds).toArray
        (w.map (start + ·)) {} lst'.worker = .ok (.ok (), s'') := by
    intro w hwm
    obtain ⟨-, ws, hws, hf⟩ := hw w hwm
    rw [oleanWorkerInit] at hws
    obtain ⟨w0, hw0, hws⟩ := ConRon.Refine.bind_eq_ok_iff.mp hws
    obtain ⟨c0, hc0, hws⟩ := ConRon.Refine.bind_eq_ok_iff.mp hws
    obtain rfl := (Result.ok_injective hws).symm
    obtain ⟨hrelW, hinvW⟩ := worker_state_rel ix hrel1 hinv1 hpers hw0
    exact foldAllOk_oleanJobStepSol_refines hfs hv hJ rfl ⟨hI, hF⟩ _ hrelW hinvW rfl
      (value_cache_empty_rel hc0) (foldAllOk_shift _ start w _ hf)
  refine ⟨I, lst', ⟨parts.map (List.map (start + ·)), hx, fun t hst ht => ?_,
    fun w hw' t ht => ?_, fun w hw' => ?_, fun w hw' => ?_⟩, hrel1, hinv1, hI⟩
  · have hlt : t - start < ds.length - start := by
      have : t < ds.length := by simpa [absIDeclL] using ht
      omega
    obtain ⟨w, hwm, hk⟩ := hcov (t - start) hlt
    exact ⟨w.map (start + ·), List.mem_map_of_mem hwm,
      List.mem_map.mpr ⟨t - start, hk, by omega⟩⟩
  · obtain ⟨w0, hw0, rfl⟩ := List.mem_map.mp hw'
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp ht
    refine ⟨Nat.le_add_right _ _, ?_⟩
    simpa [absIDeclL] using (hwork w0 hw0).1 (start + k) (List.mem_map_of_mem hk)
  · obtain ⟨w0, hw0, rfl⟩ := List.mem_map.mp hw'
    exact List.pairwise_map.mpr ((hw w0 hw0).1.imp fun h => by omega)
  · obtain ⟨w0, hw0, rfl⟩ := List.mem_map.mp hw'
    exact (hwork w0 hw0).2

end ConRon.Refine2
