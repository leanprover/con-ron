/-
# `ConRon.Refine2.Inductives.BlockRec` — Theorem 2 for `arena::inductives::block_rec`

**Task #105** (DESIGN.md §8.2, Theorem 2).
`crates/con-ron-core/src/arena/inductives/block_rec.rs` against
`proof/ConRon/Arena/Inductives/BlockRec.lean`: the elimination guard
`block_large_elim_allowed` ⊑ `blockLargeElimAllowed`.
-/
import ConRon.Refine2.Inductives.BlockParts
import ConRon.Arena.Inductives.BlockRec

open Aeneas Aeneas.Std Result
open ConRon.Generated

attribute [-grind] U32.bv_eq_imp_eq UScalar.val_eq_imp

namespace ConRon.Refine2

open ConRon.Arena
open Lockstep
open scoped IndSide

/-- `kernel::level::is_never_zero` is the twin's `Level.isNeverZero` (a
Rust-only step on a read-back level). -/
@[lockstep] theorem bp_is_never_zero_twin (l : kernel.level.Level) :
    LSP (kernel.level.is_never_zero l)
      (fun b => TwinEq (ConRon.Refine.absLevel l).isNeverZero b) :=
  fun _ h => (ConRon.Refine.Level.is_never_zero_refines h).symm

theorem absBlockShape_large (p : arena.inductives.block_parts.BlockShape) :
    (absBlockShape p).large = p.large := rfl

theorem u64_eq_one_iff (a : Std.U64) : a = 1#u64 ↔ a.val = 1 :=
  ⟨fun h => by subst h; rfl, fun h => by scalar_tac⟩

/-- `block_large_elim_allowed` ⊑ `blockLargeElimAllowed`. -/
@[lockstep] theorem block_large_elim_allowed_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (p : arena.inductives.block_parts.BlockShape) (nested : Bool) :
    LS pers (fun a b => b = a)
      (arena.inductives.block_rec.block_large_elim_allowed pers st p nested) lst
      (blockLargeElimAllowed (absBlockShape p) nested) := by
  rw [arena.inductives.block_rec.block_large_elim_allowed, blockLargeElimAllowed]
  lockstep
  all_goals
    refine LS.pure ?_ ‹_› ‹_›
    simp only [TwinEq] at *
    simp_all [absU, absBlockShape_large, u64_eq_one_iff]
  all_goals
    by_cases h1 : a.val = 1
    · simp [h1]
    · simp [h1, hc]

/-- info: 'ConRon.Refine2.block_large_elim_allowed_ls' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms block_large_elim_allowed_ls

end ConRon.Refine2
