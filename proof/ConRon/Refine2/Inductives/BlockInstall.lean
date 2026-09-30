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

/-! ## Stage 1: the formers -/

theorem bi_hvis {rf : arena.env.IFEnv} {lf : IFEnv} (hfe : IFEnvRelI rf lf) :
    absU rf.visible_below = lf.visibleBelow := hfe.rel.visibleBelow.symm

@[local lockstep_simp] theorem absMemberShape_cvT (m : arena.inductives.block_parts.MemberShape) :
    (absMemberShape m).cvT = absIConstantVal m.cv_t := rfl
@[local lockstep_simp] theorem absMemberShape_nIdx (m : arena.inductives.block_parts.MemberShape) :
    (absMemberShape m).nIdx = absU m.n_idx := rfl
@[local lockstep_simp] theorem absMemberShape_ctors (m : arena.inductives.block_parts.MemberShape) :
    (absMemberShape m).ctors = absCtorsL m.ctors := rfl

/-- `check_block_tele` ⊑ `checkBlockTele`: one member's type former. -/
@[lockstep] theorem check_block_tele_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (mode : kernel.env.CheckMode) {rf : arena.env.IFEnv} {lf : IFEnv}
    (hfe : IFEnvRelI rf lf) (n_p : Std.U64) (ms : arena.inductives.block_parts.MemberShape) :
    LS pers (fun a b => b = (absIConstantVal a.1, absLIdx a.2))
      (arena.inductives.block_install.check_block_tele pers st mode rf n_p ms) lst
      (checkBlockTele (ConRon.Refine.absMode mode) lf (absU n_p) (absMemberShape ms)) := by
  have hvis := bi_hvis hfe
  rw [arena.inductives.block_install.check_block_tele, checkBlockTele]
  lockstep

/-- The checked formers with their sorts, `Vec<(IConstantVal, LIdx)>`. -/
def absTeleL (v : alloc.vec.Vec (arena.env.IConstantVal × arena.handle.LIdx)) :
    List (IConstantVal × LIdx) :=
  v.val.map fun p => (absIConstantVal p.1, absLIdx p.2)

theorem check_block_teles_aux (m : Nat) :
    ∀ {pers st lst} {mode : kernel.env.CheckMode} {rf lf} {n_p : Std.U64}
      {ms : alloc.vec.Vec arena.inductives.block_parts.MemberShape} {i : Std.Usize}
      {out : alloc.vec.Vec (arena.env.IConstantVal × arena.handle.LIdx)},
      ms.val.length - i.val = m → AStateRel₀ pers st lst → AStateInv pers st →
      IFEnvRelI rf lf →
      LS pers (fun a b => b = absTeleL a)
        (arena.inductives.block_install.check_block_teles pers st mode rf n_p ms i out) lst
        (do
          let q ← checkBlockTeles (ConRon.Refine.absMode mode) lf (absU n_p)
            (absMemberShapeLFrom ms i)
          pure (absTeleL out ++ q)) := by
  induction m with
  | zero =>
    intro pers st lst mode rf lf n_p ms i out hn hrel hinv hfe
    rw [arena.inductives.block_install.check_block_teles, if_pos (by scalar_tac),
      absMemberShapeLFrom, sp_vecFrom_nil _ _ _ (by omega), checkBlockTeles]
    lockstep
  | succ m ih =>
    intro pers st lst mode rf lf n_p ms i out hn hrel hinv hfe
    rw [arena.inductives.block_install.check_block_teles, if_neg (by scalar_tac),
      absMemberShapeLFrom, sp_vecFrom_cons _ _ _ (by omega), checkBlockTeles]
    lockstep
    rename_i o1 ho1
    have ha : a.val = i.val + 1 := by scalar_tac
    refine LS.tail (ih (i := a) (out := o1) (by omega) hrel hinv hfe) ?_ (fun _ _ h => h)
    simp only [absMemberShapeLFrom, ha, absTeleL, ho1, List.map_append, List.map_cons,
      List.map_nil, List.append_assoc, List.cons_append, List.nil_append]

/-- `check_block_teles` ⊑ `checkBlockTeles` from the cursor on, the checked
formers accumulated in front (the Rust pushes, the twin conses on the way
out). -/
@[lockstep] theorem check_block_teles_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (mode : kernel.env.CheckMode) {rf : arena.env.IFEnv} {lf : IFEnv}
    (hfe : IFEnvRelI rf lf) (n_p : Std.U64)
    (ms : alloc.vec.Vec arena.inductives.block_parts.MemberShape) (i : Std.Usize)
    (out : alloc.vec.Vec (arena.env.IConstantVal × arena.handle.LIdx)) :
    LS pers (fun a b => b = absTeleL a)
      (arena.inductives.block_install.check_block_teles pers st mode rf n_p ms i out) lst
      (do
        let q ← checkBlockTeles (ConRon.Refine.absMode mode) lf (absU n_p)
          (absMemberShapeLFrom ms i)
        pure (absTeleL out ++ q)) :=
  check_block_teles_aux _ rfl hrel hinv hfe

end ConRon.Refine2
