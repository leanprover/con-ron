import ConRon.Refine2.Inductives.Positivity
import ConRon.Refine2.Inductives.Prims
import ConRon.Refine2.Inductives.StructParts

open Aeneas Aeneas.Std Result
open ConRon.Generated

attribute [-grind] U32.bv_eq_imp_eq UScalar.val_eq_imp

namespace ConRon.Refine2

open ConRon.Arena
open Lockstep
open scoped IndSide

/-! ## Environment lookups: `nest_container` and its fragments -/

-- `ind_caps_ctors` is the twin's `match fe.find? C with | some (.indInfo _ caps)
-- => … caps.nparams … caps.ctors`: an inline fragment of `nestContainer`.
attribute [lockstep_inline] arena.inductives.positivity.ind_caps_ctors

/-- `nest_ctor_entry_of` ⊑ `nestContainer`'s `filterMapM` lambda. -/
@[lockstep] theorem nest_ctor_entry_of_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) {vis : Std.U64} {rf : arena.env.IFEnv} {lf : IFEnv}
    (hctx : CoreCtx vis rf lf) (c n : arena.handle.NIdx) :
    LSR pers (fun a b => b = a.map fun p => (absIConstantVal p.1, absU p.2.1, absU p.2.2))
      (arena.inductives.positivity.nest_ctor_entry_of pers st vis rf c n) st lst
      (match lf.find? (absNIdx n) with
       | some ci => nestCtorEntry (absNIdx c) ci
       | none => pure none) := by
  apply LSR.of_LS
  rw [arena.inductives.positivity.nest_ctor_entry_of]
  lockstep

/-- One `List.filterMapM` step behind an accumulator. -/
theorem filterMapM_cons_acc {α β : Type} (F : α → AM (Option β)) (a : α) (l : List α)
    (w : List β) :
    ((a :: l).filterMapM F >>= fun r => pure (w ++ r)) =
      (F a >>= fun o => match o with
        | none => l.filterMapM F >>= fun r => pure (w ++ r)
        | some b => l.filterMapM F >>= fun r => pure ((w ++ [b]) ++ r)) := by
  rw [List.filterMapM_cons, bind_assoc]
  congr 1
  funext o
  cases o <;> simp

/-- `nestContainer`'s constructor lookup, the lambda of its `filterMapM`. -/
abbrev nestCtorEntryOf (lf : IFEnv) (C n : NIdx) : AM (Option (IConstantVal × Nat × Nat)) :=
  match lf.find? n with
  | some ci => nestCtorEntry C ci
  | none => pure none

/-- `nest_container_ctors` ⊑ `filterMapM` of the lookup from the cursor on,
behind the accumulator. -/
@[lockstep] theorem nest_container_ctors_ls {pers st} {vis : Std.U64} {rf : arena.env.IFEnv}
    {lf : IFEnv} (hctx : CoreCtx vis rf lf) (c : arena.handle.NIdx)
    (ns : alloc.vec.Vec arena.handle.NIdx) :
    ∀ (i : Std.Usize) (out : alloc.vec.Vec (arena.env.IConstantVal × Std.U64 × Std.U64)) lst,
      AStateRel₀ pers st lst → AStateInv pers st →
      LSR pers (fun a b => b = absCtors3L a)
        (arena.inductives.positivity.nest_container_ctors pers st vis rf c ns i out) st lst
        (do
          let r ← (absNIdxLFrom ns i).filterMapM (nestCtorEntryOf lf (absNIdx c))
          pure (absCtors3L out ++ r)) := by
  intro i
  refine cursor_induction (fun i : Std.Usize => i.val) ns.val.length
    (fun i (_ : Unit) => ∀ (out : alloc.vec.Vec (arena.env.IConstantVal × Std.U64 × Std.U64)) lst,
      AStateRel₀ pers st lst → AStateInv pers st →
      LSR pers (fun a b => b = absCtors3L a)
        (arena.inductives.positivity.nest_container_ctors pers st vis rf c ns i out) st lst
        (do
          let r ← (absNIdxLFrom ns i).filterMapM (nestCtorEntryOf lf (absNIdx c))
          pure (absCtors3L out ++ r))) ?_ ?_ i ()
  · intro i _ hn out lst hrel hinv
    apply LSR.of_LS
    rw [arena.inductives.positivity.nest_container_ctors.eq_def,
      if_pos (show i ≥ alloc.vec.Vec.len ns by scalar_tac), absNIdxLFrom,
      List.drop_eq_nil_of_le hn, List.map_nil, List.filterMapM_nil]
    simp only [pure_bind, List.append_nil]
    lockstep
  · intro i _ hlt ih out lst hrel hinv
    have ih' : ∀ j : Std.Usize, j.val = i.val + 1 →
        ∀ (out : alloc.vec.Vec (arena.env.IConstantVal × Std.U64 × Std.U64)) lst,
        AStateRel₀ pers st lst → AStateInv pers st →
        LSR pers (fun a b => b = absCtors3L a)
          (arena.inductives.positivity.nest_container_ctors pers st vis rf c ns j out) st lst
          (do
            let r ← (absNIdxLFrom ns j).filterMapM (nestCtorEntryOf lf (absNIdx c))
            pure (absCtors3L out ++ r)) :=
      fun j hj => ih j () hj
    clear ih
    apply LSR.of_LS
    rw [arena.inductives.positivity.nest_container_ctors.eq_def,
      if_neg (show ¬ i ≥ alloc.vec.Vec.len ns by scalar_tac), absNIdxLFrom,
      List.drop_eq_getElem_cons hlt, List.map_cons, filterMapM_cons_acc]
    lockstep

@[lockstep] theorem nest_container_ctors_new_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) {vis : Std.U64} {rf : arena.env.IFEnv}
    {lf : IFEnv} (hctx : CoreCtx vis rf lf) (c : arena.handle.NIdx)
    (ns : alloc.vec.Vec arena.handle.NIdx) :
    LSR pers (fun a b => b = absCtors3L a)
      (arena.inductives.positivity.nest_container_ctors pers st vis rf c ns 0#usize
        (alloc.vec.Vec.new _)) st lst
      ((absNIdxL ns).filterMapM (nestCtorEntryOf lf (absNIdx c))) := by
  have h := nest_container_ctors_ls hctx c ns 0#usize (alloc.vec.Vec.new _) lst hrel hinv
  have e : (do
      let r ← (absNIdxLFrom ns 0#usize).filterMapM (nestCtorEntryOf lf (absNIdx c))
      pure (absCtors3L (alloc.vec.Vec.new (arena.env.IConstantVal × Std.U64 × Std.U64)) ++ r)
        : AM _) = (absNIdxL ns).filterMapM (nestCtorEntryOf lf (absNIdx c)) := by
    simp [absCtors3L, alloc.vec.Vec.new]
  rwa [e] at h

/-- `nest_container` ⊑ `nestContainer` (Rust `vis, fe, c`; twin `fe C`). -/
@[lockstep] theorem nest_container_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) {vis : Std.U64} {rf : arena.env.IFEnv}
    {lf : IFEnv} (hctx : CoreCtx vis rf lf) (c : arena.handle.NIdx) :
    LSR pers (fun a b => b = a.map fun p => (absU p.1, absCtorsL p.2))
      (arena.inductives.positivity.nest_container pers st vis rf c) st lst
      (nestContainer lf (absNIdx c)) := by
  apply LSR.of_LS
  rw [arena.inductives.positivity.nest_container, nestContainer]
  lockstep
  rename_i a _ _ _ hc
  have h0 : absCtors3L a = [] := by
    have : a.val.length = 0 := by scalar_tac
    simp [absCtors3L, List.eq_nil_of_length_eq_zero this]
  rw [h0]
  lockstep
  rename_i cs hlt hd tl hdisc
  have hh : hd = (absIConstantVal cs.val[0].1, absU cs.val[0].2.1, absU cs.val[0].2.2) := by
    have e : cs.val = cs.val[0] :: cs.val.drop 1 := by
      rw [← List.drop_eq_getElem_cons (by simpa using hlt)]; rfl
    rw [absCtors3L, e, List.map_cons, List.cons.injEq] at hdisc
    exact hdisc.1.symm
  subst hh
  apply LS.pure _ (by assumption) (by assumption)
  rfl

end ConRon.Refine2
