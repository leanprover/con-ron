/-
# `ConRon.Capstone.Pool` — Theorem 2 at the check phase with a solution

The compared run's challenge goes through the driver's check phase with a solution
(`crates/con-ron/src/driver.rs` `check_decls_driver` at `sol = Some(&sol)`): the same
`build_index → freeze_tier → parallel_all → thaw_tier` line as the flat run, its step closure
`run_job` at the solution.  `Refine2/Checker/Phased.lean` states that line at `None`
(`jobStep`, `PoolAccepts`, `pool_accepts_refines`); this module is the same composition at any
solution related to the twin's (`OptSolRel`), over `Refine2/Checker/Jobs.lean`'s
`run_job_refines`, which already takes one.  Nothing here is a new Theorem-2 fact: each lemma
is the flat one's proof with the solution threaded.
-/
import ConRon.Refine2.Checker.Phased
import ConRon.Refine2.Checker.Justify

open Aeneas Aeneas.Std Result
open ConRon.Generated

attribute [-grind] U32.bv_eq_imp_eq UScalar.val_eq_imp

namespace ConRon.Capstone

set_option autoImplicit false

open ConRon.Refine2 ConRon.Arena

/-- con-leche: ConLeche/Driver/CheckPool.lean:211-239 checkPool — **the driver's `step` closure
with a solution**, `|w, k| checker::run_job(&tier, w, &mode, &ipins, sol, ds, k as u64)`:
`Refine2/Checker/Phased.lean`'s `jobStep` at `sol`. -/
def jobStepJ (tier : arena.store.PersTier) (mode : kernel.env.CheckMode)
    (pins : alloc.vec.Vec arena.nat_op_pin_set.INatOpPinSet)
    (sol : Option arena.justify.Solution)
    (ds : alloc.vec.Vec arena.env.IDeclaration) (st : arena.monad.AState) (k : Nat) :
    Result ((core.result.Result Unit (kernel.core_types.CheckError × Std.U64)) ×
      arena.monad.AState) :=
  if h : k < 2 ^ UScalarTy.Usize.numBits then
    arena.checker.run_job tier st mode pins sol ds
      (UScalar.cast .U64 (UScalar.ofNatCore (ty := .Usize) k h))
  else fail .panic

/-- con-leche: ConLeche/Driver/CheckPool.lean:211-239 checkPool — `jobStep` is `jobStepJ` without
a solution. -/
theorem jobStep_eq_J (tier : arena.store.PersTier) (mode : kernel.env.CheckMode)
    (pins : alloc.vec.Vec arena.nat_op_pin_set.INatOpPinSet)
    (ds : alloc.vec.Vec arena.env.IDeclaration) :
    jobStep tier mode pins ds = jobStepJ tier mode pins none ds := rfl

/-- con-leche: ConLeche/Driver/CheckPool.lean:211-239 checkPool — **a worker's fold with a
solution ⊑ `checkJobList` at the twin's**: `foldAllOk_jobStep_refines` at `sol`. -/
theorem foldAllOk_jobStepJ_refines {tier} {I : IStreamIndex} {mode : kernel.env.CheckMode}
    {pins : alloc.vec.Vec arena.nat_op_pin_set.INatOpPinSet}
    {ds : alloc.vec.Vec arena.env.IDeclaration}
    {sol : Option arena.justify.Solution} {J : Option ISolution} (hJ : OptSolRel sol J)
    (hI : StreamIndexRel tier.env I ∧ FrozenRel tier.env I) (htf : tier.frozen = true) :
    ∀ (ks : List Nat) {st lst},
      AIdle tier st lst → AStateInv tier st →
      FoldAllOk (jobStepJ tier mode pins sol ds) st ks →
      (∀ k ∈ ks, k < ds.val.length) ∧
      ∃ s'', checkJobList (ConRon.Refine.absMode mode) (absINatOpPinSetL pins) J I
        (absIDeclL ds).toArray ks lst = .ok (.ok (), s'')
  | [], _, lst, _, _, _ => ⟨by simp, lst, rfl⟩
  | k :: ks, _, lst, hidle, hinv, ⟨_, hs1, hf⟩ => by
    unfold jobStepJ at hs1
    split at hs1
    · rename_i hk
      have hu : (UScalar.cast .U64 (UScalar.ofNatCore (ty := .Usize) k hk)).val = k := by
        rw [usize_cast_u64_val']; rfl
      have hkU : (UScalar.cast .U64 (UScalar.ofNatCore (ty := .Usize) k hk)).val
          ≤ Std.Usize.max := by
        have h2 : Std.Usize.max = 2 ^ UScalarTy.Usize.numBits - 1 := by
          rw [← UScalar.max_USize_eq, UScalar.max_def]
        have h3 := Nat.one_le_two_pow (n := UScalarTy.Usize.numBits)
        rw [hu, h2]; omega
      obtain ⟨hlt, lst1, hx, hidle1, hinv1, -⟩ := run_job_refines hidle hinv htf hI hkU hJ hs1
      rw [hu] at hlt
      have hau : absU (UScalar.cast .U64 (UScalar.ofNatCore (ty := .Usize) k hk)) = k := hu
      rw [hau] at hx
      obtain ⟨hall, s'', h⟩ := foldAllOk_jobStepJ_refines hJ hI htf ks hidle1 hinv1 hf
      refine ⟨?_, s'', ?_⟩
      · intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact hlt
        · exact hall x hx
      · simp only [checkJobList]
        rw [show runJob _ _ J I _ k lst = .ok (.ok (), lst1) from hx]
        exact h
    · simp at hs1

/-- con-leche: ConLeche/Driver/CheckPool.lean:211-239 checkPool — **the driver's check phase
with a solution, accepted**: `PoolAccepts` with the step at `sol`. -/
def PoolAcceptsJ (pers : arena.store.PersTier) (st : arena.monad.AState)
    (mode : kernel.env.CheckMode)
    (pins : alloc.vec.Vec arena.nat_op_pin_set.INatOpPinSet)
    (sol : Option arena.justify.Solution)
    (ds : alloc.vec.Vec arena.env.IDeclaration)
    (ix : arena.stream_index.IStreamIndex) (st' : arena.monad.AState) : Prop :=
  ∃ (tier : arena.store.PersTier) (est : arena.store.EStore),
    arena.stream_index.build_index pers st ixEmpty ds 0#usize = ok (.Ok ix, st') ∧
    arena.checker.freeze_tier st'.store ix = ok (tier, est) ∧
    ParallelAll ds.length (arena.checker.worker_state st'.pins) (jobStepJ tier mode pins sol ds)

/-- `PoolAcceptsJ` from one premise per call of the driver. -/
theorem poolAcceptsJ_intro {pers st mode pins sol ds ix st'}
    {tier : arena.store.PersTier} {est : arena.store.EStore}
    (hI : (do
        let e ← arena.stream_index.stream_index_empty
        arena.stream_index.build_index pers st e ds 0#usize) = ok (.Ok ix, st'))
    (hF : arena.checker.freeze_tier st'.store ix = ok (tier, est))
    (hB : ParallelAll ds.length (arena.checker.worker_state st'.pins)
      (jobStepJ tier mode pins sol ds)) :
    PoolAcceptsJ pers st mode pins sol ds ix st' := by
  rw [stream_index_empty_eq, bind_ok] at hI
  exact ⟨tier, est, hI, hF, hB⟩

/-- con-leche: ConLeche/Driver/CheckPool.lean:211-239 checkPool — **Theorem 2 at the check phase
with a solution**: `pool_accepts_refines` at a solution related to the twin's — the twin's index
build, related, and every worker's list accepted by `checkJobList` at the twin's solution. -/
theorem pool_accepts_j_refines {pers st lst}
    {mode : kernel.env.CheckMode}
    {pins : alloc.vec.Vec arena.nat_op_pin_set.INatOpPinSet}
    {sol : Option arena.justify.Solution} {J : Option ISolution} (hJ : OptSolRel sol J)
    {ds : alloc.vec.Vec arena.env.IDeclaration} {ix st'}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hpers : pers.frozen = false)
    (hpool : PoolAcceptsJ pers st mode pins sol ds ix st') :
    ∃ I lst', (∃ (parts : List (List Nat)),
        buildIndex (absIDeclL ds).toArray lst = .ok (.ok I, lst') ∧
        (∀ t < (absIDeclL ds).toArray.size, ∃ w ∈ parts, t ∈ w) ∧
        (∀ w ∈ parts, ∀ t ∈ w, t < (absIDeclL ds).toArray.size) ∧
        (∀ w ∈ parts, w.Pairwise (· < ·)) ∧
        (∀ w ∈ parts, ∃ s'', checkJobList (ConRon.Refine.absMode mode)
          (absINatOpPinSetL pins) J I (absIDeclL ds).toArray w lst'.worker = .ok (.ok (), s''))) ∧
      AStateRel₀ pers st' lst' ∧ AStateInv pers st' ∧ StreamIndexRel ix I := by
  obtain ⟨tier, est, hB, hfr, parts, hcov, hw⟩ := hpool
  obtain ⟨I, lst', hx, hrel1, hinv1, hI, hF⟩ := build_index_empty_refines hrel hinv hB
  obtain ⟨htier, -⟩ := freeze_tier_ok hfr
  subst htier
  have hwork : ∀ w ∈ parts, (∀ k ∈ w, k < ds.val.length) ∧
      ∃ s'', checkJobList (ConRon.Refine.absMode mode) (absINatOpPinSetL pins) J I
        (absIDeclL ds).toArray w lst'.worker = .ok (.ok (), s'') := by
    intro w hwm
    obtain ⟨-, ws, hws, hf⟩ := hw w hwm
    obtain ⟨hrelW, hinvW⟩ := worker_state_rel ix hrel1 hinv1 hpers hws
    exact foldAllOk_jobStepJ_refines hJ ⟨hI, hF⟩ rfl w hrelW hinvW hf
  refine ⟨I, lst', ⟨parts, hx, fun t ht => ?_, fun w hw' t ht => ?_,
    fun w hw' => (hw w hw').1, fun w hw' => (hwork w hw').2⟩, hrel1, hinv1, hI⟩
  · exact hcov t (by simpa [absIDeclL] using ht)
  · simpa [absIDeclL] using (hwork w hw').1 t ht

end ConRon.Capstone
