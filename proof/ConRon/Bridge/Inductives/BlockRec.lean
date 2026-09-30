/-
# `ConRon.Bridge.Inductives.BlockRec` — Theorem 1 for the recursor stage's guard

`Arena/Inductives/BlockRec.lean`'s one twin, `blockLargeElimAllowed`, against
`ConLeche/Kernel/Inductives/BlockRec.lean` (task #105).  The twin reads the
result sort back through the CACHED `readLevelM`, whose answer is the
denotation only under `ReadLCacheOK`: the statement is at `PSpecL` (that one
table and nothing else), with the core-grade corollary beside it.
-/
import ConRon.Bridge.Inductives.BlockParts

namespace ConRon.Bridge.Inductives

set_option autoImplicit false

open ConLeche ConRon.Arena ConRon.Bridge

/-- con-leche: ConLeche/Kernel/Inductives/BlockRec.lean:82-84 blockLargeElimAllowed
When a large eliminator is allowed: the result sort, read back
(`readLevelM_denote_L`), is the record's; the cited `||` short-circuits after
that read. -/
theorem blockLargeElimAllowed_spec (p : Arena.BlockShape) (pP : ConLeche.BlockShape)
    (nested : Bool) :
    PSpecL (fun st => dShape st p = some pP) (Arena.blockLargeElimAllowed p nested)
      (RV (ConLeche.blockLargeElimAllowed pP nested)) := by
  intro s₀ s' r hok hrl hp hrun
  have hk := BlockShape.k_spec hp
  have hn := BlockShape.numCtors_spec hp
  simp only [Arena.blockLargeElimAllowed] at hrun
  obtain ⟨l, s₁, h1, h2⟩ := bindOk hrun
  have p1 := readLevelM_pstep hok h1
  have hl := readLevelM_denote_L hrl (PStep.refl hok) h1
  obtain ⟨-, -, -, -, hs, hlg, -⟩ := dShape_inv hp
  have hres : pP.resSort = l := by
    rw [hl] at hs; exact (Option.some.inj hs).symm
  replace hlg := hlg.symm
  simp only [RV, ConLeche.blockLargeElimAllowed, hres, hlg, ← hk, ← hn]
  by_cases hz : Level.isNeverZero l = true
  · rw [if_pos hz] at h2
    obtain ⟨rfl, rfl⟩ := pureOk h2
    exact ⟨p1, by simp [hz]⟩
  · rw [if_neg hz] at h2
    simp only [Bool.not_eq_true] at hz
    cases nested
    · obtain ⟨rfl, rfl⟩ := pureOk h2
      exact ⟨p1, by simp [hz]⟩
    · obtain ⟨rfl, rfl⟩ := pureOk h2
      exact ⟨p1, by simp [hz]⟩

/-- con-leche: ConLeche/Kernel/Inductives/BlockRec.lean:82-84 blockLargeElimAllowed
— the core-grade corollary: `CheckOK` carries the readback cache's licence. -/
theorem blockLargeElimAllowed_cspec {μ : CheckMode} {env : Env} (fe : IFEnv)
    (p : Arena.BlockShape) (pP : ConLeche.BlockShape) (nested : Bool) :
    CSpec μ env fe (fun st => dShape st p = some pP) (Arena.blockLargeElimAllowed p nested)
      (RV (ConLeche.blockLargeElimAllowed pP nested)) := by
  intro s₀ s' r hok hp hrun
  obtain ⟨hstep, hr⟩ :=
    blockLargeElimAllowed_spec p pP nested s₀ s' r hok.state hok.caches.readL hp hrun
  exact ⟨hstep.toCore hok, hr⟩

end ConRon.Bridge.Inductives
