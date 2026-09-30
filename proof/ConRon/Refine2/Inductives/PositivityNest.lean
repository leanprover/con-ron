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

/-! ## Environment lookups: the frame's readers -/

-- `ind_cv_of` is the twin's `match fe.find? C with | some (.indInfo cv _) => …`:
-- an inline fragment of `nestInstType`, `nestArity` and `nestHoles`.
attribute [lockstep_inline] arena.inductives.positivity.ind_cv_of

/-- `nest_block_of` ⊑ `nestBlockOf` (Rust `ctx, fe, c`; twin `fe C`). -/
@[lockstep] theorem nest_block_of_twin (ctx : arena.inductives.positivity.NestCtx)
    {rf : arena.env.IFEnv} {lf : IFEnv} (hctx : CoreCtx ctx.vis rf lf) (c : arena.handle.NIdx) :
    LSP (arena.inductives.positivity.nest_block_of ctx rf c)
      (fun o => TwinEq (nestBlockOf lf (absNIdx c)) (absNIdxL o)) := by
  intro o h
  rw [arena.inductives.positivity.nest_block_of] at h
  obtain ⟨oo, hoo, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have hf := ifenv_find_abs hctx hoo
  rw [TwinEq, nestBlockOf, ← hf]
  rcases oo with _ | ci
  · cases Result.ok_injective h; rfl
  · cases ci <;> (try (cases Result.ok_injective h; rfl))
    simp only [Option.map_some, absIConstantInfo, absIIndCaps]
    rw [absNIdxL, nidx_vec_dup_val h]

/-- `nest_frame_mates` ⊑ `nestFrameMates` (Rust `ctx, fe, c`; twin `fe C`). -/
@[lockstep] theorem nest_frame_mates_twin (ctx : arena.inductives.positivity.NestCtx)
    {rf : arena.env.IFEnv} {lf : IFEnv} (hctx : CoreCtx ctx.vis rf lf) (c : arena.handle.NIdx) :
    LSP (arena.inductives.positivity.nest_frame_mates ctx rf c)
      (fun o => TwinEq (nestFrameMates lf (absNIdx c)) (absNIdxL o)) := by
  intro o h
  rw [arena.inductives.positivity.nest_frame_mates] at h
  obtain ⟨all, hall, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have h1 := nest_block_of_twin ctx hctx c all hall
  have h2 := frame_mates_from_twin all c o h
  simp only [TwinEq] at h1 h2 ⊢
  rw [nestFrameMates, h1, h2]

/-- `nest_arity` ⊑ `nestArity` (Rust `ctx, fe, c`; twin `fe C`). -/
@[lockstep] theorem nest_arity_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (ctx : arena.inductives.positivity.NestCtx)
    {rf : arena.env.IFEnv} {lf : IFEnv} (hctx : CoreCtx ctx.vis rf lf) (c : arena.handle.NIdx) :
    LSR pers (fun a b => b = absU a)
      (arena.inductives.positivity.nest_arity pers st ctx rf c) st lst
      (nestArity lf (absNIdx c)) := by
  apply LSR.of_LS
  rw [arena.inductives.positivity.nest_arity, nestArity]
  lockstep

/-- `nest_group_ctors` ⊑ `nestGroupCtors` from the cursor on (Rust `fe, ctx,
n_pc, cs, i, out`; twin `fe nPc cs out`). -/
@[lockstep] theorem nest_group_ctors_ls {pers st} (ctx : arena.inductives.positivity.NestCtx)
    {rf : arena.env.IFEnv} {lf : IFEnv} (hctx : CoreCtx ctx.vis rf lf) (n_pc : Std.U64)
    (cs : alloc.vec.Vec arena.handle.NIdx) :
    ∀ (i : Std.Usize) (out : alloc.vec.Vec (arena.env.IConstantVal × Std.U64)) lst,
      AStateRel₀ pers st lst → AStateInv pers st →
      LSR pers (fun a b => b = absCtorsL a)
        (arena.inductives.positivity.nest_group_ctors pers st rf ctx n_pc cs i out) st lst
        (nestGroupCtors lf (absU n_pc) (absNIdxLFrom cs i) (absCtorsL out)) := by
  intro i
  refine cursor_induction (fun i : Std.Usize => i.val) cs.val.length
    (fun i (_ : Unit) => ∀ (out : alloc.vec.Vec (arena.env.IConstantVal × Std.U64)) lst,
      AStateRel₀ pers st lst → AStateInv pers st →
      LSR pers (fun a b => b = absCtorsL a)
        (arena.inductives.positivity.nest_group_ctors pers st rf ctx n_pc cs i out) st lst
        (nestGroupCtors lf (absU n_pc) (absNIdxLFrom cs i) (absCtorsL out))) ?_ ?_ i ()
  · intro i _ hn out lst hrel hinv
    apply LSR.of_LS
    rw [arena.inductives.positivity.nest_group_ctors.eq_def,
      if_pos (show i ≥ alloc.vec.Vec.len cs by scalar_tac), absNIdxLFrom,
      List.drop_eq_nil_of_le hn, List.map_nil, nestGroupCtors]
    lockstep
  · intro i _ hlt ih out lst hrel hinv
    have ih' : ∀ j : Std.Usize, j.val = i.val + 1 →
        ∀ (out : alloc.vec.Vec (arena.env.IConstantVal × Std.U64)) lst,
        AStateRel₀ pers st lst → AStateInv pers st →
        LSR pers (fun a b => b = absCtorsL a)
          (arena.inductives.positivity.nest_group_ctors pers st rf ctx n_pc cs j out) st lst
          (nestGroupCtors lf (absU n_pc) (absNIdxLFrom cs j) (absCtorsL out)) :=
      fun j hj => ih j () hj
    clear ih
    apply LSR.of_LS
    rw [arena.inductives.positivity.nest_group_ctors.eq_def,
      if_neg (show ¬ i ≥ alloc.vec.Vec.len cs by scalar_tac), absNIdxLFrom,
      List.drop_eq_getElem_cons hlt, List.map_cons, nestGroupCtors]
    lockstep

@[lockstep] theorem nest_group_ctors_new_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (ctx : arena.inductives.positivity.NestCtx)
    {rf : arena.env.IFEnv} {lf : IFEnv} (hctx : CoreCtx ctx.vis rf lf) (n_pc : Std.U64)
    (cs : alloc.vec.Vec arena.handle.NIdx) :
    LSR pers (fun a b => b = absCtorsL a)
      (arena.inductives.positivity.nest_group_ctors pers st rf ctx n_pc cs 0#usize
        (alloc.vec.Vec.new _)) st lst
      (nestGroupCtors lf (absU n_pc) (absNIdxL cs) []) := by
  have h := nest_group_ctors_ls ctx hctx n_pc cs 0#usize (alloc.vec.Vec.new _) lst hrel hinv
  rwa [absNIdxLFrom_zero, show absCtorsL (alloc.vec.Vec.new (arena.env.IConstantVal × Std.U64))
    = [] from rfl] at h

/-! ## The container's former: `nest_inst_type` -/

-- `nest_inst_type_at` / `nest_inst_type_sort` are the tail of `nestInstType`
-- (the instantiated former, its telescope and its sort; (N2) and (N3)).
attribute [lockstep_inline] arena.inductives.positivity.nest_inst_type_at
  arena.inductives.positivity.nest_inst_type_sort

-- `unwrap_or` of the looked-up container: the port matches the `Option` it
-- just built, the twin `unwrapOr`s it (local; `StructInstall`'s
-- `IndInstPrims.unwrapOr_*'` are the same equations, scoped there).
attribute [local lockstep_inline] arena.checker_base.unwrap_or
-- The constant's copy IS the constant (`Positivity.lean`'s local spec).
attribute [local lockstep high] pos_i_constant_val_dup_spec

/-- `eidx_vec_dup` is the identity (the exact form, ahead of the generic
abstraction-level spec, so that a copied key's parameters ARE the original's). -/
theorem pn_eidx_vec_dup_spec (v : alloc.vec.Vec arena.handle.EIdx) :
    LSP (arena.env.eidx_vec_dup v) (fun o => o = v) :=
  fun _ h => alloc.vec.Vec.ext _ _ (eidx_vec_dup_val h)

attribute [local lockstep high] pn_eidx_vec_dup_spec

@[local lockstep_simp] theorem pn_unwrapOr_some {α : Type} (a : α) (e : Arena.CheckError) :
    unwrapOr (some a) e = pure a := rfl

@[local lockstep_simp] theorem pn_unwrapOr_none {α : Type} (e : Arena.CheckError) :
    unwrapOr (none : Option α) e = Arena.fail e := rfl

/-- `nest_inst_type` ⊑ `nestInstType`. -/
@[lockstep] theorem nest_inst_type_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (ctx : arena.inductives.positivity.NestCtx)
    {rf : arena.env.IFEnv} {lf : IFEnv} (hctx : CoreCtx ctx.vis rf lf) (hi : Std.U64)
    (key : arena.inductives.positivity.NestKey) :
    LS pers (fun a b => b = (absU a.1, absEIdx a.2))
      (arena.inductives.positivity.nest_inst_type pers st rf ctx hi key) lst
      (nestInstType lf (absNestCtx ctx) (absU hi) (absNestKey key)) := by
  rw [arena.inductives.positivity.nest_inst_type, nestInstType]
  lockstep

/-- `nest_grow_group` ⊑ `nestGrowGroup` from the cursor on. -/
@[lockstep] theorem nest_grow_group_ls {pers} (ctx : arena.inductives.positivity.NestCtx)
    {rf : arena.env.IFEnv} {lf : IFEnv} (hctx : CoreCtx ctx.vis rf lf) (hi : Std.U64)
    (us : arena.handle.LsIdx) (ds : alloc.vec.Vec arena.handle.EIdx)
    (cs : alloc.vec.Vec arena.handle.NIdx) :
    ∀ (i : Std.Usize) st lst (grp : alloc.vec.Vec (arena.handle.NIdx × arena.handle.EIdx)),
      AStateRel₀ pers st lst → AStateInv pers st →
      LS pers (fun a b => b = absGrpL a)
        (arena.inductives.positivity.nest_grow_group pers st rf ctx hi us ds cs i grp) lst
        (nestGrowGroup lf (absNestCtx ctx) (absU hi) (absLsIdx us) (absEIdxL ds)
          (absNIdxLFrom cs i) (absGrpL grp)) := by
  intro i st lst grp hrel hinv
  refine ls_cursor_acc cs absNIdx
    (fun (w : alloc.vec.Vec (arena.handle.NIdx × arena.handle.EIdx)) l =>
      nestGrowGroup lf (absNestCtx ctx) (absU hi) (absLsIdx us) (absEIdxL ds) l (absGrpL w))
    (fun st k w => arena.inductives.positivity.nest_grow_group pers st rf ctx hi us ds cs k w)
    ?_ ?_ i st lst grp hrel hinv
  · intro st lst k w hn hrel hinv
    rw [arena.inductives.positivity.nest_grow_group.eq_def,
      if_pos (show k ≥ alloc.vec.Vec.len cs by scalar_tac), nestGrowGroup]
    lockstep
  · intro st lst k w hk hrel hinv ih
    have ih' : ∀ st' lst' (j : Std.Usize) (w' : alloc.vec.Vec (arena.handle.NIdx × arena.handle.EIdx)),
        j.val = k.val + 1 → AStateRel₀ pers st' lst' → AStateInv pers st' →
        LS pers (fun a b => b = absGrpL a)
          (arena.inductives.positivity.nest_grow_group pers st' rf ctx hi us ds cs j w') lst'
          (nestGrowGroup lf (absNestCtx ctx) (absU hi) (absLsIdx us) (absEIdxL ds)
            (absNIdxLFrom cs j) (absGrpL w')) := ih
    clear ih
    rw [arena.inductives.positivity.nest_grow_group.eq_def,
      if_neg (show ¬ k ≥ alloc.vec.Vec.len cs by scalar_tac), nestGrowGroup]
    lockstep
    rename_i _ _ grp1 hgrp
    refine LS.tail (ih' _ _ _ grp1 (by scalar_tac) (by assumption) (by assumption)) ?_
      (fun _ _ h => h)
    have hj' : a.val = k.val + 1 := by scalar_tac
    simp only [absEIdxL, absNIdxLFrom, absGrpL, hgrp, hj', List.map_append, List.map_cons,
      List.map_nil]

/-- `nest_grow_group` from the first mate on. -/
@[lockstep] theorem nest_grow_group_new_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (ctx : arena.inductives.positivity.NestCtx)
    {rf : arena.env.IFEnv} {lf : IFEnv} (hctx : CoreCtx ctx.vis rf lf) (hi : Std.U64)
    (us : arena.handle.LsIdx) (ds : alloc.vec.Vec arena.handle.EIdx)
    (cs : alloc.vec.Vec arena.handle.NIdx)
    (grp : alloc.vec.Vec (arena.handle.NIdx × arena.handle.EIdx)) :
    LS pers (fun a b => b = absGrpL a)
      (arena.inductives.positivity.nest_grow_group pers st rf ctx hi us ds cs 0#usize grp) lst
      (nestGrowGroup lf (absNestCtx ctx) (absU hi) (absLsIdx us) (absEIdxL ds)
        (absNIdxL cs) (absGrpL grp)) := by
  have h := nest_grow_group_ls ctx hctx hi us ds cs 0#usize st lst grp hrel hinv
  rwa [absNIdxLFrom_zero] at h

/-! ## The member holes: `nest_holes` -/

/-- `nest_holes` ⊑ `nestHoles.go` from the member cursor on. -/
theorem nest_holes_acc {pers} (ctx : arena.inductives.positivity.NestCtx)
    {rf : arena.env.IFEnv} {lf : IFEnv} (hctx : CoreCtx ctx.vis rf lf) :
    ∀ (mm : Std.Usize) st lst (out : alloc.vec.Vec arena.handle.EIdx),
      AStateRel₀ pers st lst → AStateInv pers st →
      LS pers (fun a b => b = a.map absEIdxL)
        (arena.inductives.positivity.nest_holes pers st rf ctx mm out) lst
        (nestHoles.go lf (absNestCtx ctx) mm.val (absNIdxLFrom ctx.names mm) (absEIdxL out)) := by
  intro mm
  refine cursor_induction (fun i : Std.Usize => i.val) ctx.names.val.length
    (fun i (_ : Unit) => ∀ st lst (out : alloc.vec.Vec arena.handle.EIdx),
      AStateRel₀ pers st lst → AStateInv pers st →
      LS pers (fun a b => b = a.map absEIdxL)
        (arena.inductives.positivity.nest_holes pers st rf ctx i out) lst
        (nestHoles.go lf (absNestCtx ctx) i.val (absNIdxLFrom ctx.names i) (absEIdxL out)))
    ?_ ?_ mm ()
  · intro i _ hn st lst out hrel hinv
    rw [arena.inductives.positivity.nest_holes.eq_def,
      if_pos (show i ≥ alloc.vec.Vec.len ctx.names by scalar_tac), absNIdxLFrom,
      List.drop_eq_nil_of_le hn, List.map_nil, nestHoles.go]
    lockstep
  · intro i _ hlt ih st lst out hrel hinv
    have ih' : ∀ j : Std.Usize, j.val = i.val + 1 → ∀ st lst (out : alloc.vec.Vec arena.handle.EIdx),
        AStateRel₀ pers st lst → AStateInv pers st →
        LS pers (fun a b => b = a.map absEIdxL)
          (arena.inductives.positivity.nest_holes pers st rf ctx j out) lst
          (nestHoles.go lf (absNestCtx ctx) j.val (absNIdxLFrom ctx.names j) (absEIdxL out)) :=
      fun j hj => ih j () hj
    clear ih
    rw [arena.inductives.positivity.nest_holes.eq_def,
      if_neg (show ¬ i ≥ alloc.vec.Vec.len ctx.names by scalar_tac), absNIdxLFrom,
      List.drop_eq_getElem_cons hlt, List.map_cons, nestHoles.go]
    unfold arena.inductives.positivity.ind_cv_of
    lockstep

/-- `nest_holes` from member `0` and an empty accumulator IS `nestHoles`. -/
@[lockstep] theorem nest_holes_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (ctx : arena.inductives.positivity.NestCtx)
    {rf : arena.env.IFEnv} {lf : IFEnv} (hctx : CoreCtx ctx.vis rf lf) :
    LS pers (fun a b => b = a.map absEIdxL)
      (arena.inductives.positivity.nest_holes pers st rf ctx 0#usize (alloc.vec.Vec.new _)) lst
      (nestHoles lf (absNestCtx ctx)) := by
  have h := nest_holes_acc ctx hctx 0#usize st lst (alloc.vec.Vec.new _) hrel hinv
  rwa [absNIdxLFrom_zero, show absEIdxL (alloc.vec.Vec.new arena.handle.EIdx) = [] from rfl,
    show (0#usize : Std.Usize).val = 0 from rfl] at h

/-! ## U4: `nest_u4` -/

/-- The twin's U4 test at field `i` (`nestCtors`' `anyM` lambda). -/
abbrev nestU4At (ks : List NestFieldKind) (closed : EIdx) (i : Nat) : AM Bool :=
  if (ks[i]?.map (· == .ordinary)).getD true then pure false
  else structUsedLater closed 0 i

/-- `nest_u4` ⊑ `nestCtors`' `(List.range nF).anyM …` from the counter on. -/
theorem nest_u4_acc {pers} (ks : alloc.vec.Vec arena.inductives.positivity.NestFieldKind)
    (closed : arena.handle.EIdx) (n_f : Std.U64) :
    ∀ (i : Std.U64) st lst, AStateRel₀ pers st lst → AStateInv pers st →
      LS pers (fun a b => b = a)
        (arena.inductives.positivity.nest_u4 pers st ks closed n_f i) lst
        ((List.range' i.val (n_f.val - i.val)).anyM
          (nestU4At (ks.val.map absNestFieldKind) (absEIdx closed))) := by
  intro i st lst hrel hinv
  refine ls_counted n_f (fun (_ : Unit) m j => (List.range' j m).anyM
      (nestU4At (ks.val.map absNestFieldKind) (absEIdx closed)))
    (fun st k _ => arena.inductives.positivity.nest_u4 pers st ks closed n_f k) ?_ ?_
    i st lst () hrel hinv
  · intro st lst k _ hn hrel hinv
    rw [arena.inductives.positivity.nest_u4.eq_def, if_pos (by scalar_tac), List.range'_zero,
      List.anyM_nil]
    lockstep
  · intro st lst k _ m hk hm hrel hinv ih
    rw [arena.inductives.positivity.nest_u4.eq_def, if_neg (by scalar_tac), List.range'_succ,
      List.anyM_cons]
    lockstep

/-- `nest_u4` from field `0`: `nestCtors`' U4 test. -/
@[lockstep] theorem nest_u4_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (ks : alloc.vec.Vec arena.inductives.positivity.NestFieldKind)
    (closed : arena.handle.EIdx) (n_f : Std.U64) :
    LS pers (fun a b => b = a)
      (arena.inductives.positivity.nest_u4 pers st ks closed n_f 0#u64) lst
      ((List.range (absU n_f)).anyM fun i =>
        if ((ks.val.map absNestFieldKind)[i]?.map (· == .ordinary)).getD true then pure false
        else structUsedLater (absEIdx closed) 0 i) := by
  have h := nest_u4_acc ks closed n_f 0#u64 st lst hrel hinv
  rwa [show (0#u64 : Std.U64).val = 0 from rfl, Nat.sub_zero, ← List.range_eq_range'] at h

/-! ## The `nest_pos` block

The Rust's one `partial_fixpoint` block is the twin's well-founded `mutual`
block on `(root, fuel, tag, size)`.  The induction is on the twin's fuel `F`:
`nest_pos` at `F` (`NestPosRel … F`) gives every container-frame member at
`F` (`nest_fields_of`, `nest_ctors_of`, `nest_frame_of`, `nest_cont_new_of`,
`nest_cont_key_of`, `nest_cont_of`, each by its own structural argument), and
those give `nest_pos` at `F + 1` (`nest_pos_all`).  The root frame's
constructors walk their fields at their own input-derived fuel, which is any
`F` (`nest_ctors_of` at `root = true`). -/

/-- The answer relation of `nest_pos`. -/
abbrev RPos : arena.inductives.positivity.NestFieldKind × arena.handle.EIdx ×
    arena.inductives.positivity.NestState → NestFieldKind × EIdx × NestState → Prop :=
  fun a b => b = (absNestFieldKind a.1, absEIdx a.2.1, absNestState a.2.2)

/-- **`nest_pos` ⊑ `nestPos` at the twin's fuel `F`** — the induction's
statement. -/
def NestPosRel (pers : arena.store.PersTier) (mode : kernel.env.CheckMode)
    (rf : arena.env.IFEnv) (lf : IFEnv) (ctx : arena.inductives.positivity.NestCtx)
    (F : Nat) : Prop :=
  ∀ (fuel : Std.U64) (prog : alloc.vec.Vec arena.inductives.positivity.NestHole)
    (dep kb : Std.U64) (e : arena.handle.EIdx) (ns : arena.inductives.positivity.NestState)
    st lst, fuel.val = F → AStateRel₀ pers st lst → AStateInv pers st →
    LS pers RPos (arena.inductives.positivity.nest_pos pers st mode rf ctx fuel prog dep kb e ns)
      lst (nestPos (ConRon.Refine.absMode mode) lf (absNestCtx ctx) F
        (prog.val.map absNestHole) (absU dep) (absU kb) (absEIdx e) (absNestState ns))

/-- The answer relation of `nest_fields`: the twin's tuple, and the walked
telescope's binder data well-formed (`close_telescope`'s premise). -/
abbrev RFields : (alloc.vec.Vec arena.inductives.positivity.NestFieldKind ×
      alloc.vec.Vec (arena.handle.EIdx × kernel.expr.BinderMeta) × arena.handle.EIdx ×
      arena.inductives.positivity.NestState) →
    (List NestFieldKind × List (EIdx × ConLeche.BinderMeta) × EIdx × NestState) → Prop :=
  fun a b => TeleWF a.2.1 ∧ b = (a.1.val.map absNestFieldKind, absBinderL a.2.1,
    absEIdx a.2.2.1, absNestState a.2.2.2)

/-- `nest_fields` ⊑ `nestFields` at a fuel whose `nest_pos` is related. -/
theorem nest_fields_of {pers} {mode : kernel.env.CheckMode} {rf : arena.env.IFEnv} {lf : IFEnv}
    {ctx : arena.inductives.positivity.NestCtx} {F : Nat}
    (hP : NestPosRel pers mode rf lf ctx F) (n : Nat) :
    ∀ (fuel : Std.U64) (prog : alloc.vec.Vec arena.inductives.positivity.NestHole)
      (base n_f j : Std.U64) (cur : arena.handle.EIdx)
      (ns : arena.inductives.positivity.NestState)
      (ks : alloc.vec.Vec arena.inductives.positivity.NestFieldKind)
      (nds : alloc.vec.Vec (arena.handle.EIdx × kernel.expr.BinderMeta)) st lst,
      fuel.val = F → n_f.val = n → TeleWF nds → AStateRel₀ pers st lst → AStateInv pers st →
      LS pers RFields
        (arena.inductives.positivity.nest_fields pers st mode rf ctx fuel prog base n_f j cur ns
          ks nds) lst
        (nestFields (ConRon.Refine.absMode mode) lf (absNestCtx ctx) F (prog.val.map absNestHole)
          (absU base) n (absU j) (absEIdx cur) (absNestState ns) (ks.val.map absNestFieldKind)
          (absBinderL nds)) := by
  have hP' : ∀ (fuel : Std.U64) (prog : alloc.vec.Vec arena.inductives.positivity.NestHole)
      (dep kb : Std.U64) (e : arena.handle.EIdx) (ns : arena.inductives.positivity.NestState)
      st lst, AStateRel₀ pers st lst → AStateInv pers st → fuel.val = F →
      LS pers RPos (arena.inductives.positivity.nest_pos pers st mode rf ctx fuel prog dep kb e ns)
        lst (nestPos (ConRon.Refine.absMode mode) lf (absNestCtx ctx) F
          (prog.val.map absNestHole) (absU dep) (absU kb) (absEIdx e) (absNestState ns)) :=
    fun fuel prog dep kb e ns st lst hrel hinv hf => hP fuel prog dep kb e ns st lst hf hrel hinv
  clear hP
  induction n with
  | zero =>
    intro fuel prog base n_f j cur ns ks nds st lst hf hn hte hrel hinv
    rw [arena.inductives.positivity.nest_fields, if_pos (by scalar_tac), nestFields]
    lockstep
  | succ n ih =>
    intro fuel prog base n_f j cur ns ks nds st lst hf hn hte hrel hinv
    rw [arena.inductives.positivity.nest_fields, if_neg (by scalar_tac), nestFields]
    lockstep
    rename_i hwf _ _ _ b2 ks1 hks nds1 hnds nf1 hnf1
    refine LS.tail (ih _ _ _ _ _ _ _ _ _ _ _ hf (by scalar_tac) ?_ (by assumption)
      (by assumption)) ?_ (fun _ _ h => h)
    · exact TeleWF.push hnds hte (hwf _ rfl)
    · have e1 : absU a = absU j + 1 := by simp only [absU]; scalar_tac
      simp only [e1, absBinderL, hks, hnds, List.map_append, List.map_cons, List.map_nil]
      rfl

-- The frame-constructor fragments of `nestCtors` (the crest typed, the fields
-- walked at the constructor's fuel, U4 / the result / the record).
attribute [lockstep_inline] arena.inductives.positivity.nest_ctors_typed
  arena.inductives.positivity.nest_ctors_walk arena.inductives.positivity.nest_ctors_done
-- `nest_res_ok` is `nestCtors`' `resOk` block, which the twin's normal form
-- flattens into the `if !resOk` after it: unfolded here, it zips step by step.
attribute [local lockstep_inline] arena.inductives.positivity.nest_res_ok

/-- A walked constructor's `(kinds, closed form)`. -/
def absCtorOut (p : alloc.vec.Vec arena.inductives.positivity.NestFieldKind × arena.handle.EIdx) :
    List NestFieldKind × EIdx :=
  (p.1.val.map absNestFieldKind, absEIdx p.2)

/-- The answer relation of `nest_ctors`. -/
abbrev RCtors : (alloc.vec.Vec (alloc.vec.Vec arena.inductives.positivity.NestFieldKind ×
      arena.handle.EIdx) × arena.inductives.positivity.NestState) →
    (List (List NestFieldKind × EIdx) × NestState) → Prop :=
  fun a b => b = (a.1.val.map absCtorOut, absNestState a.2)

/-- `nest_ctors` ⊑ `nestCtors` from the constructor cursor on, at a `root`
flag and fuel whose fields' walks are related: `hW` is `nest_fields` at the
fuel the constructor's fields are walked at (`fuel` itself in a container
frame; any fuel at the root). -/
theorem nest_ctors_of {pers} {mode : kernel.env.CheckMode} {rf : arena.env.IFEnv} {lf : IFEnv}
    {ctx : arena.inductives.positivity.NestCtx} (hctx : CoreCtx ctx.vis rf lf)
    (root : Bool) (fuel : Std.U64)
    (hW : ∀ (fuel_c : Std.U64), (root = true ∨ fuel_c = fuel) →
      ∀ (prog : alloc.vec.Vec arena.inductives.positivity.NestHole)
      (base n_f : Std.U64) (cur : arena.handle.EIdx)
      (ns : arena.inductives.positivity.NestState) st lst,
      AStateRel₀ pers st lst → AStateInv pers st →
      LS pers RFields
        (arena.inductives.positivity.nest_fields pers st mode rf ctx fuel_c prog base n_f 0#u64 cur
          ns (alloc.vec.Vec.new _) (alloc.vec.Vec.new _)) lst
        (nestFields (ConRon.Refine.absMode mode) lf (absNestCtx ctx) (absU fuel_c)
          (prog.val.map absNestHole) (absU base) (absU n_f) 0 (absEIdx cur) (absNestState ns) [] []))
    (prog : alloc.vec.Vec arena.inductives.positivity.NestHole) (hi : Std.U64)
    (us : arena.handle.LsIdx) (ds : alloc.vec.Vec arena.handle.EIdx)
    (names : alloc.vec.Vec arena.handle.NIdx) (holes : alloc.vec.Vec arena.handle.EIdx)
    (cs : alloc.vec.Vec (arena.env.IConstantVal × Std.U64)) :
    ∀ (i : Std.Usize) (ns : arena.inductives.positivity.NestState)
      (outs : alloc.vec.Vec (alloc.vec.Vec arena.inductives.positivity.NestFieldKind ×
        arena.handle.EIdx)) st lst,
      AStateRel₀ pers st lst → AStateInv pers st →
      LS pers RCtors
        (arena.inductives.positivity.nest_ctors pers st mode rf ctx root fuel prog hi us ds names
          holes cs i ns outs) lst
        (nestCtors (ConRon.Refine.absMode mode) lf (absNestCtx ctx) root (absU fuel)
          (prog.val.map absNestHole) (absU hi) (absLsIdx us) (absEIdxL ds) (absNIdxL names)
          (absEIdxL holes) (absCtorsLFrom cs i) (absNestState ns) (outs.val.map absCtorOut)) := by
  intro i
  refine cursor_induction (fun i : Std.Usize => i.val) cs.val.length
    (fun i (_ : Unit) => ∀ (ns : arena.inductives.positivity.NestState)
      (outs : alloc.vec.Vec (alloc.vec.Vec arena.inductives.positivity.NestFieldKind ×
        arena.handle.EIdx)) st lst,
      AStateRel₀ pers st lst → AStateInv pers st →
      LS pers RCtors
        (arena.inductives.positivity.nest_ctors pers st mode rf ctx root fuel prog hi us ds names
          holes cs i ns outs) lst
        (nestCtors (ConRon.Refine.absMode mode) lf (absNestCtx ctx) root (absU fuel)
          (prog.val.map absNestHole) (absU hi) (absLsIdx us) (absEIdxL ds) (absNIdxL names)
          (absEIdxL holes) (absCtorsLFrom cs i) (absNestState ns) (outs.val.map absCtorOut)))
    ?_ ?_ i ()
  · intro i _ hn ns outs st lst hrel hinv
    rw [arena.inductives.positivity.nest_ctors,
      if_pos (show i ≥ alloc.vec.Vec.len cs by scalar_tac), absCtorsLFrom,
      List.drop_eq_nil_of_le hn, List.map_nil, nestCtors]
    lockstep
  · intro i _ hlt ih ns outs st lst hrel hinv
    have ih' : ∀ j : Std.Usize, j.val = i.val + 1 → ∀ (ns : arena.inductives.positivity.NestState)
        (outs : alloc.vec.Vec (alloc.vec.Vec arena.inductives.positivity.NestFieldKind ×
          arena.handle.EIdx)) st lst,
        AStateRel₀ pers st lst → AStateInv pers st →
        LS pers RCtors
          (arena.inductives.positivity.nest_ctors pers st mode rf ctx root fuel prog hi us ds names
            holes cs j ns outs) lst
          (nestCtors (ConRon.Refine.absMode mode) lf (absNestCtx ctx) root (absU fuel)
            (prog.val.map absNestHole) (absU hi) (absLsIdx us) (absEIdxL ds) (absNIdxL names)
            (absEIdxL holes) (absCtorsLFrom cs j) (absNestState ns) (outs.val.map absCtorOut)) :=
      fun j hj => ih j () hj
    clear ih
    rw [arena.inductives.positivity.nest_ctors,
      if_neg (show ¬ i ≥ alloc.vec.Vec.len cs by scalar_tac), absCtorsLFrom,
      List.drop_eq_getElem_cons hlt, List.map_cons, nestCtors]
    cases root
    · have hW0 := hW fuel (Or.inr rfl)
      clear hW
      lockstep
      rename_i nfv hnfv outs1 houts
      refine LS.tail (ih' _ (by scalar_tac) _ _ _ _ (by assumption) (by assumption)) ?_
        (fun _ _ h => h)
      have ha : a.val = i.val + 1 := by scalar_tac
      simp [absCtorsLFrom, ha, absNestState, hnfv, houts, absCtorOut]
    · have hW1 : ∀ (fuel_c : Std.U64) (prog : alloc.vec.Vec arena.inductives.positivity.NestHole)
          (base n_f : Std.U64) (cur : arena.handle.EIdx)
          (ns : arena.inductives.positivity.NestState) st lst,
          AStateRel₀ pers st lst → AStateInv pers st →
          LS pers RFields
            (arena.inductives.positivity.nest_fields pers st mode rf ctx fuel_c prog base n_f 0#u64
              cur ns (alloc.vec.Vec.new _) (alloc.vec.Vec.new _)) lst
            (nestFields (ConRon.Refine.absMode mode) lf (absNestCtx ctx) (absU fuel_c)
              (prog.val.map absNestHole) (absU base) (absU n_f) 0 (absEIdx cur) (absNestState ns)
              [] []) :=
        fun fuel_c => hW fuel_c (Or.inl rfl)
      clear hW
      lockstep
      rename_i nfv hnfv outs1 houts
      refine LS.tail (ih' _ (by scalar_tac) _ _ _ _ (by assumption) (by assumption)) ?_
        (fun _ _ h => h)
      have ha : a.val = i.val + 1 := by scalar_tac
      simp [absCtorsLFrom, ha, absNestState, hnfv, houts, absCtorOut]

/-- A container frame's constructors (`root = false`, from `0`, no outputs
yet) at a fuel whose `nest_pos` is related. -/
theorem nest_ctors_frame_of {pers} {mode : kernel.env.CheckMode} {rf : arena.env.IFEnv}
    {lf : IFEnv} {ctx : arena.inductives.positivity.NestCtx} (hctx : CoreCtx ctx.vis rf lf)
    {fuel : Std.U64} (hP : NestPosRel pers mode rf lf ctx fuel.val)
    (prog : alloc.vec.Vec arena.inductives.positivity.NestHole) (hi : Std.U64)
    (us : arena.handle.LsIdx) (ds : alloc.vec.Vec arena.handle.EIdx)
    (names : alloc.vec.Vec arena.handle.NIdx) (holes : alloc.vec.Vec arena.handle.EIdx)
    (cs : alloc.vec.Vec (arena.env.IConstantVal × Std.U64))
    (ns : arena.inductives.positivity.NestState) st lst
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) :
    LS pers RCtors
      (arena.inductives.positivity.nest_ctors pers st mode rf ctx false fuel prog hi us ds names
        holes cs 0#usize ns (alloc.vec.Vec.new _)) lst
      (nestCtors (ConRon.Refine.absMode mode) lf (absNestCtx ctx) false (absU fuel)
        (prog.val.map absNestHole) (absU hi) (absLsIdx us) (absEIdxL ds) (absNIdxL names)
        (absEIdxL holes) (absCtorsL cs) (absNestState ns) []) := by
  have h := nest_ctors_of (mode := mode) hctx false fuel ?_ prog hi us ds names holes cs 0#usize ns
    (alloc.vec.Vec.new _) st lst hrel hinv
  · rwa [absCtorsLFrom_zero] at h
  · rintro fuel_c (h | rfl)
    · cases h
    intro prog base n_f cur ns st lst hrel hinv
    exact nest_fields_of hP _ fuel_c prog base n_f 0#u64 cur ns _ _ st lst rfl rfl TeleWF.new
      hrel hinv

-- A container frame's fragments (the instantiation typed; the stack, the
-- group's constructors and the walk).
attribute [lockstep_inline] arena.inductives.positivity.nest_frame_at
  arena.inductives.positivity.nest_frame_walk

/-- `nest_frame` ⊑ `nestFrame` at a fuel whose `nest_pos` is related. -/
theorem nest_frame_of {pers} {mode : kernel.env.CheckMode} {rf : arena.env.IFEnv}
    {lf : IFEnv} {ctx : arena.inductives.positivity.NestCtx} (hctx : CoreCtx ctx.vis rf lf)
    {fuel : Std.U64} (hP : NestPosRel pers mode rf lf ctx fuel.val)
    (prog : alloc.vec.Vec arena.inductives.positivity.NestHole) (hi : Std.U64)
    (us : arena.handle.LsIdx) (ds : alloc.vec.Vec arena.handle.EIdx) (n_pc : Std.U64)
    (grp : alloc.vec.Vec (arena.handle.NIdx × arena.handle.EIdx))
    (ns : arena.inductives.positivity.NestState) st lst
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absNestState a)
      (arena.inductives.positivity.nest_frame pers st mode rf ctx fuel prog hi us ds n_pc grp ns)
      lst
      (nestFrame (ConRon.Refine.absMode mode) lf (absNestCtx ctx) (absU fuel)
        (prog.val.map absNestHole) (absU hi) (absLsIdx us) (absEIdxL ds) (absU n_pc)
        (absGrpL grp) (absNestState ns)) := by
  have hC := nest_ctors_frame_of hctx hP
  rw [arena.inductives.positivity.nest_frame, nestFrame.eq_def]
  lockstep
  · -- the empty group: the twin's `match grp` at `[]`
    split
    · lockstep
    · rename_i heq
      exfalso
      have : grp.val.length = 0 := by scalar_tac
      simp [absGrpL, List.eq_nil_of_length_eq_zero this] at heq
  · -- a group: the twin's `match grp` at its head
    split
    · rename_i heq
      exfalso
      simp [absGrpL] at heq
      scalar_tac
    · rename_i c _ _ heq
      have hc : c = absNIdx (grp.val[0]'(by scalar_tac)).1 := by
        have e : grp.val = grp.val[0]'(by scalar_tac) :: grp.val.drop 1 := by
          rw [← List.drop_eq_getElem_cons (by scalar_tac)]; rfl
        rw [absGrpL, e, List.map_cons, List.cons.injEq, Prod.mk.injEq] at heq
        exact heq.1.1.symm
      subst hc
      lockstep
      rename_i gl hgl
      have e : absU a = absU hi + (absGrpL grp).length := by
        simp only [absU, absGrpL, List.length_map]; scalar_tac
      rw [← e]
      lockstep

/-- `nest_keys_dup` behind a non-empty accumulator: the accumulator, then the
copied keys (`nest_cont_new`'s `group_keys ++ active`). -/
theorem nest_keys_dup_acc (ks : alloc.vec.Vec arena.inductives.positivity.NestKey) :
    ∀ (i : Std.Usize) (out o : alloc.vec.Vec arena.inductives.positivity.NestKey),
      arena.inductives.positivity.nest_keys_dup ks i out = ok o →
      o.val = out.val ++ (ks.val.drop i.val).map id := by
  refine vec_map_loop ks _ (arena.inductives.positivity.nest_keys_dup ks) ?_ ?_
  · intro i out o hn h
    rw [arena.inductives.positivity.nest_keys_dup.eq_def,
      if_pos (show i ≥ alloc.vec.Vec.len ks by scalar_tac), Result.ok.injEq] at h
    exact h.symm
  · intro i x out o hx h
    rw [arena.inductives.positivity.nest_keys_dup.eq_def, if_neg (show ¬ i ≥ alloc.vec.Vec.len ks by
      have := (List.getElem?_eq_some_iff.mp hx).1; scalar_tac)] at h
    obtain ⟨q, hq, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have hqx : q = x := by
      have h1 := vec_index_some hq; rw [hx] at h1; exact (Option.some_inj.mp h1).symm
    subst hqx
    obtain ⟨k1, hk1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨out1, hout1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨i2, hi2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    rw [nest_key_dup_spec _ _ hk1] at hout1
    exact ⟨i2, out1, absSz_add_one hi2, ConRon.Refine.vec_push_val hout1, h⟩

/-- `nest_keys_dup` from `0` behind any accumulator (below `nest_keys_dup_spec`,
the exact copy at `Vec::new()`). -/
@[lockstep low] theorem nest_keys_dup_out_spec
    (ks out : alloc.vec.Vec arena.inductives.positivity.NestKey) :
    LSP (arena.inductives.positivity.nest_keys_dup ks 0#usize out)
      (fun o => o.val = out.val ++ ks.val) := by
  intro o h
  rw [nest_keys_dup_acc ks _ out o h]
  simp

attribute [local lockstep_simp] absGrpL

/-- The Rust's `kb != 0` as the twin's (`NestFieldKind.nested`'s flag). -/
theorem pn_u64_bne_zero (x : Std.U64) : (x != 0#u64) = (x.val != 0) := by
  by_cases h : x = 0#u64
  · subst h; rfl
  · have h' : x.val ≠ 0 := by intro h0; exact h (by scalar_tac)
    rw [Bool.eq_iff_iff, bne_iff_ne, bne_iff_ne]
    exact ⟨fun _ => h', fun _ => h⟩

/-- The answer relation of `nest_cont` / `nest_cont_key` / `nest_cont_new`. -/
abbrev RCont : arena.inductives.positivity.NestFieldKind × arena.inductives.positivity.NestState →
    NestFieldKind × NestState → Prop :=
  fun a b => b = (absNestFieldKind a.1, absNestState a.2)

/-- `nest_cont_new` ⊑ `nestContNew` at a fuel whose `nest_pos` is related. -/
theorem nest_cont_new_of {pers} {mode : kernel.env.CheckMode} {rf : arena.env.IFEnv}
    {lf : IFEnv} {ctx : arena.inductives.positivity.NestCtx} (hctx : CoreCtx ctx.vis rf lf)
    {fuel : Std.U64} (hP : NestPosRel pers mode rf lf ctx fuel.val)
    (prog : alloc.vec.Vec arena.inductives.positivity.NestHole) (kb : Std.U64)
    (n : arena.handle.NIdx) (us : arena.handle.LsIdx) (ds : alloc.vec.Vec arena.handle.EIdx)
    (n_pc : Std.U64) (cty : arena.handle.EIdx) (ns : arena.inductives.positivity.NestState) st lst
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) :
    LS pers RCont
      (arena.inductives.positivity.nest_cont_new pers st mode rf ctx fuel prog kb n us ds n_pc cty
        ns) lst
      (nestContNew (ConRon.Refine.absMode mode) lf (absNestCtx ctx) (absU fuel)
        (prog.val.map absNestHole) (absU kb) (absNIdx n) (absLsIdx us) (absEIdxL ds) (absU n_pc)
        (absEIdx cty) (absNestState ns)) := by
  have hF := nest_frame_of hctx hP
  rw [arena.inductives.positivity.nest_cont_new, nestContNew.eq_def]
  lockstep
  -- the frame, walked with the group in progress: the Rust's `{ ns with active }`
  -- is the twin's rebuilt record
  rename_i wp _ _ _ _ _ _ _ _ wl hwl hw hhw grp v hv
  refine LS.bind (hF _ _ _ _ _ grp { ns with active := a } _ _ hrel hinv) ?_
    (fun _ _ => by lockstep_errarm) ?_
  · have e1 : absU hw = absU ctx.n_p + ctx.names.val.length + (wp.val.map absNestHole).length := by
      simp only [absU, List.length_map]; scalar_tac
    simp only [TwinEq] at hv
    simp only [absNestState, e1, hP, List.map_append, ← hv, vec_new_val', List.map_nil,
      List.nil_append, absGrpL, List.map_map]
    rfl
  · intro r b st2 lst2 hR hrel hinv
    subst hR
    lockstep
    · apply LS.pure _ (by assumption) (by assumption)
      simp only [TwinEq, absNestKeyArr, absGrpL, absEIdxL] at hP
      show _ = _
      simp only [absNestState, absNestFieldKind, hP, pn_u64_bne_zero]
    · apply LS.pure _ (by assumption) (by assumption)
      show _ = _
      simp only [absNestState, absNestFieldKind, hc, pn_u64_bne_zero, if_false]

/-- `nest_keys_contain` of a rebuilt key over a state's in-progress keys (the
twin's `List`) and over its accepted keys (the twin's `Array`), in the forms
`nestContKey` reads them. -/
theorem nest_keys_contain_active_twin (ns : arena.inductives.positivity.NestState)
    (n : arena.handle.NIdx) (l : arena.handle.LsIdx) (d : alloc.vec.Vec arena.handle.EIdx) :
    LSP (arena.inductives.positivity.nest_keys_contain ns.active
        { cname := n, lvls := l, ds := d } 0#usize)
      (fun o => TwinEq ((absNestState ns).active.contains
        { cname := absNIdx n, lvls := absLsIdx l, ds := List.map absEIdx d.val }) o) := by
  intro o h
  have := nest_keys_contain_twin _ _ o h
  simp only [TwinEq, absNestKeyArr, List.contains_toArray] at this ⊢
  exact this

theorem nest_keys_contain_keys_twin (ns : arena.inductives.positivity.NestState)
    (n : arena.handle.NIdx) (l : arena.handle.LsIdx) (d : alloc.vec.Vec arena.handle.EIdx) :
    LSP (arena.inductives.positivity.nest_keys_contain ns.keys
        { cname := n, lvls := l, ds := d } 0#usize)
      (fun o => TwinEq ((absNestState ns).keys.contains
        { cname := absNIdx n, lvls := absLsIdx l, ds := List.map absEIdx d.val }) o) := by
  intro o h
  exact nest_keys_contain_twin _ _ o h

/-- The handle copies are the identity (exact, ahead of the generic specs, so
that a rebuilt key IS the key). -/
theorem pn_nidx_dup2_spec (x : arena.handle.NIdx) :
    LSP (arena.handle.NIdx.Insts.Con_ron_coreRonHashmapDup.dup2 x) (fun o => o = x) :=
  fun _ h => dupId_nidx _ _ h

theorem pn_lsidx_dup2_spec (x : arena.handle.LsIdx) :
    LSP (arena.handle.LsIdx.Insts.Con_ron_coreRonHashmapDup.dup2 x) (fun o => o = x) :=
  fun _ h => dupId_lsidx _ _ h

attribute [local lockstep high] nest_keys_contain_active_twin nest_keys_contain_keys_twin
  pn_nidx_dup2_spec pn_lsidx_dup2_spec

/-- `nest_cont_key` ⊑ `nestContKey` at a fuel whose `nest_pos` is related. -/
theorem nest_cont_key_of {pers} {mode : kernel.env.CheckMode} {rf : arena.env.IFEnv}
    {lf : IFEnv} {ctx : arena.inductives.positivity.NestCtx} (hctx : CoreCtx ctx.vis rf lf)
    {fuel : Std.U64} (hP : NestPosRel pers mode rf lf ctx fuel.val)
    (prog : alloc.vec.Vec arena.inductives.positivity.NestHole) (kb : Std.U64)
    (n : arena.handle.NIdx) (us : arena.handle.LsIdx) (ds : alloc.vec.Vec arena.handle.EIdx)
    (n_pc : Std.U64) (cty : arena.handle.EIdx) (ns : arena.inductives.positivity.NestState) st lst
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) :
    LS pers RCont
      (arena.inductives.positivity.nest_cont_key pers st mode rf ctx fuel prog kb n us ds n_pc cty
        ns) lst
      (nestContKey (ConRon.Refine.absMode mode) lf (absNestCtx ctx) (absU fuel)
        (prog.val.map absNestHole) (absU kb) (absNIdx n) (absLsIdx us) (absEIdxL ds) (absU n_pc)
        (absEIdx cty) (absNestState ns)) := by
  have hN := nest_cont_new_of hctx hP
  rw [arena.inductives.positivity.nest_cont_key, nestContKey.eq_def]
  lockstep
  apply LS.pure _ (by assumption) (by assumption)
  show _ = _
  simp only [absNestFieldKind, pn_u64_bne_zero]

end ConRon.Refine2
