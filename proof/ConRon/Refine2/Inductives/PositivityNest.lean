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

end ConRon.Refine2
