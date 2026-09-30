/-
# `ConRon.Refine2.Inductives.BlockInstall` — Theorem 2 for `arena::inductives::block_install`

**Task #105** (DESIGN.md §8.2, Theorem 2).
`crates/con-ron-core/src/arena/inductives/block_install.rs` against
`proof/ConRon/Arena/Inductives/BlockInstall.lean`: the capability record per
member, official's `is_rec`, the formers' stage, the constructors' stage, the
positivity check on the stored constructors, the index sorts and the
constructors' cons.
-/
import ConRon.Refine2.Inductives.PositivityNest
import ConRon.Refine2.Inductives.SumInstall
import ConRon.Arena.Inductives.BlockInstall

open Aeneas Aeneas.Std Result
open ConRon.Generated

attribute [-grind] U32.bv_eq_imp_eq UScalar.val_eq_imp

namespace ConRon.Refine2

open ConRon.Arena
open Lockstep
open scoped IndSide

@[local lockstep_simp] theorem bi_core_walk_fuel_val :
    (arena.core.CORE_WALK_FUEL).val = coreWalkFuel := core_walk_fuel_abs

/-! ## Official's `is_rec`: `pi_doms_mention_any`, `ctors_mention_any`,
`members_mention_any`, `block_raw_rec` -/

/-- `pi_doms_mention_any` ⊑ `piDomsMentionAny`, at the same fuel. -/
@[lockstep] theorem pi_doms_mention_any_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (names : alloc.vec.Vec arena.handle.NIdx) (fuel : Std.U64)
    (e : arena.handle.EIdx) :
    LSR pers (fun a b => b = a)
      (arena.inductives.block_install.pi_doms_mention_any pers st names fuel e) st lst
      (piDomsMentionAny (absNIdxL names) (absU fuel) (absEIdx e)) := by
  induction hf : fuel.val generalizing fuel e lst with
  | zero =>
    apply LSR.of_LS
    rw [arena.inductives.block_install.pi_doms_mention_any.eq_def, if_pos (by scalar_tac),
      show absU fuel = 0 from hf, piDomsMentionAny]
    lockstep
  | succ n ih =>
    apply LSR.of_LS
    rw [arena.inductives.block_install.pi_doms_mention_any.eq_def, if_neg (by scalar_tac),
      show absU fuel = n + 1 from hf, piDomsMentionAny]
    lockstep

/-- `ctors_mention_any` ⊑ `blockRawRec`'s inner `anyM`, from the cursor on. -/
@[lockstep] theorem ctors_mention_any_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (names : alloc.vec.Vec arena.handle.NIdx)
    (cs : alloc.vec.Vec (arena.env.IConstantVal × Std.U64)) (i : Std.Usize) :
    LSR pers (fun a b => b = a)
      (arena.inductives.block_install.ctors_mention_any pers st names cs i) st lst
      ((absCtorsLFrom cs i).anyM fun c => piDomsMentionAny (absNIdxL names) coreWalkFuel c.1.type) := by
  refine cursor_induction (fun i : Std.Usize => i.val) cs.val.length
    (fun i (_ : Unit) => ∀ lst, AStateRel₀ pers st lst → LSR pers (fun a b => b = a)
      (arena.inductives.block_install.ctors_mention_any pers st names cs i) st lst
      ((absCtorsLFrom cs i).anyM fun c => piDomsMentionAny (absNIdxL names) coreWalkFuel c.1.type))
    ?_ ?_ i () lst hrel
  · intro i _ hn lst hrel
    apply LSR.of_LS
    rw [arena.inductives.block_install.ctors_mention_any.eq_def,
      if_pos (show i ≥ alloc.vec.Vec.len cs by scalar_tac), absCtorsLFrom,
      List.drop_eq_nil_of_le hn, List.map_nil, List.anyM]
    lockstep
  · intro i _ hlt ih lst hrel
    have ih' : ∀ j : Std.Usize, j.val = i.val + 1 → ∀ lst, AStateRel₀ pers st lst →
        LSR pers (fun a b => b = a)
        (arena.inductives.block_install.ctors_mention_any pers st names cs j) st lst
        ((absCtorsLFrom cs j).anyM fun c =>
          piDomsMentionAny (absNIdxL names) coreWalkFuel c.1.type) :=
      fun j hj => ih j () hj
    clear ih
    apply LSR.of_LS
    rw [arena.inductives.block_install.ctors_mention_any.eq_def,
      if_neg (show ¬ i ≥ alloc.vec.Vec.len cs by scalar_tac), absCtorsLFrom,
      List.drop_eq_getElem_cons hlt, List.map_cons, List.anyM]
    lockstep

/-- A member list as the twin's `List MemberShape`, from a cursor on. -/
def absMemberShapeLFrom (v : alloc.vec.Vec arena.inductives.block_parts.MemberShape)
    (i : Std.Usize) : List MemberShape :=
  (v.val.drop i.val).map absMemberShape

/-- `members_mention_any` ⊑ `blockRawRec`'s outer `anyM`, from the cursor on. -/
@[lockstep] theorem members_mention_any_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (names : alloc.vec.Vec arena.handle.NIdx)
    (ms : alloc.vec.Vec arena.inductives.block_parts.MemberShape) (i : Std.Usize) :
    LSR pers (fun a b => b = a)
      (arena.inductives.block_install.members_mention_any pers st names ms i) st lst
      ((absMemberShapeLFrom ms i).anyM fun m => m.ctors.anyM fun c =>
        piDomsMentionAny (absNIdxL names) coreWalkFuel c.1.type) := by
  refine cursor_induction (fun i : Std.Usize => i.val) ms.val.length
    (fun i (_ : Unit) => ∀ lst, AStateRel₀ pers st lst → LSR pers (fun a b => b = a)
      (arena.inductives.block_install.members_mention_any pers st names ms i) st lst
      ((absMemberShapeLFrom ms i).anyM fun m => m.ctors.anyM fun c =>
        piDomsMentionAny (absNIdxL names) coreWalkFuel c.1.type))
    ?_ ?_ i () lst hrel
  · intro i _ hn lst hrel
    apply LSR.of_LS
    rw [arena.inductives.block_install.members_mention_any.eq_def,
      if_pos (show i ≥ alloc.vec.Vec.len ms by scalar_tac), absMemberShapeLFrom,
      List.drop_eq_nil_of_le hn, List.map_nil, List.anyM]
    lockstep
  · intro i _ hlt ih lst hrel
    have ih' : ∀ j : Std.Usize, j.val = i.val + 1 → ∀ lst, AStateRel₀ pers st lst →
        LSR pers (fun a b => b = a)
        (arena.inductives.block_install.members_mention_any pers st names ms j) st lst
        ((absMemberShapeLFrom ms j).anyM fun m => m.ctors.anyM fun c =>
          piDomsMentionAny (absNIdxL names) coreWalkFuel c.1.type) :=
      fun j hj => ih j () hj
    clear ih
    apply LSR.of_LS
    rw [arena.inductives.block_install.members_mention_any.eq_def,
      if_neg (show ¬ i ≥ alloc.vec.Vec.len ms by scalar_tac), absMemberShapeLFrom,
      List.drop_eq_getElem_cons hlt, List.map_cons, List.anyM]
    lockstep
    cases b
    · have ha : a.val = i.val + 1 := by scalar_tac
      exact LSR.tail_ls (ih' _ ha _ hrel) (by simp only [absMemberShapeLFrom, ha, absNIdxL])
        (fun _ _ h => h)
    · exact absurd rfl hc

end ConRon.Refine2
