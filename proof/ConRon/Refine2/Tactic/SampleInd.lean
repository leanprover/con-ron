/-
# `ConRon.Refine2.Tactic.SampleInd` — the tactic on an inductives state-free copy

Task #97-T2-TACTIC, sample 5.  `ctors_copy_from` (old:
`Inductives/SumParts.lean`, `ctors_copy_from_refines`, 27 lines, through the
`vec_cursor_copy` combinator).  State-free: there is no twin action, so the
goal is the Rust-only judgement `LSP` and `lockstep` steps the Rust alone.
-/
import ConRon.Refine2.Tactic.Prims
import ConRon.Refine2.Inductives.SumParts

open Aeneas Aeneas.Std Result
open ConRon.Generated

attribute [-grind] U32.bv_eq_imp_eq UScalar.val_eq_imp

namespace ConRon.Refine2.Lockstep.Sample

open ConRon.Arena ConRon.Refine2 ConRon.Refine2.Lockstep

@[lockstep] theorem i_constant_val_dup_spec (cv : arena.env.IConstantVal) :
    LSP (arena.env.i_constant_val_dup cv) (fun o => absIConstantVal o = absIConstantVal cv) :=
  fun _ h => i_constant_val_dup_abs h

theorem ctors_copy_from_refines' (n : Nat) :
    ∀ (cs : alloc.vec.Vec (arena.env.IConstantVal × Std.U64)) (i : Std.Usize)
      (out : alloc.vec.Vec (arena.env.IConstantVal × Std.U64)),
      cs.val.length - i.val = n →
      LSP (arena.inductives.sum_parts.ctors_copy_from cs i out)
        (fun o => absCtorsL o = absCtorsL out ++ absCtorsLFrom cs i) := by
  induction n with
  | zero =>
    intro cs i out hn
    rw [arena.inductives.sum_parts.ctors_copy_from]
    lockstep
  | succ k ih =>
    intro cs i out hn
    rw [arena.inductives.sum_parts.ctors_copy_from]
    lockstep
    -- the loop invariant's list algebra: what `vec_cursor_copy` packages
    refine LSP.tail (ih _ _ _ (by scalar_tac)) fun o h => ?_
    rename_i hlt _ hv _ hout
    rw [h]
    simp only [absCtorsL, absCtorsLFrom, hout, hP, List.map_append, List.map_cons,
      List.map_nil, List.append_assoc, List.drop_eq_getElem_cons hlt, hv]
    rfl

end ConRon.Refine2.Lockstep.Sample
