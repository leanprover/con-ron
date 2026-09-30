/-
# `ConRon.Refine2.Inductives.GenRec` — Theorem 2 for `arena::inductives::gen_rec`

**Task #105** (DESIGN.md §8.2, Theorem 2).  `crates/con-ron-core/src/arena/inductives/gen_rec.rs`
against `proof/ConRon/Arena/Inductives/GenRec.lean`: the generator
(`ClassGen`: the prefix, each recursor's type, each rule) and the stage
(`checkBlockClasses`, `genRecCheck`).

## Shapes

* A Rust cursor loop with a pushing accumulator is the twin's `List.mapM` in
  its `mapM.loop` form (the accumulator reversed), so the statement at the
  cursor needs no append lemma; the callers' form (`0`, `Vec::new()`) is the
  twin's `mapM` by definition.
* A Rust telescope pushed into `close_telescope`/`close_lams` carries
  `TeleWF` (the binders' erased `PropWhen` invariant) beside its
  abstraction; the generated datum `g.bm` is canonical (`ClassGenWF`).
-/
import ConRon.Refine2.Inductives.Positivity
import ConRon.Refine2.Inductives.Prims
import ConRon.Refine2.Inductives.StructParts
import ConRon.Arena.Inductives.GenRec

open Aeneas Aeneas.Std Result
open ConRon.Generated

attribute [-grind] U32.bv_eq_imp_eq UScalar.val_eq_imp

namespace ConRon.Refine2

open ConRon.Arena
open Lockstep
open scoped IndSide

attribute [local lockstep_simp] pos_core_walk_fuel_abs pos_core_walk_fuel_val
attribute [local lockstep] pos_zero_level_ls pos_i_constant_val_dup_spec

/-! ## The records' fields -/

@[lockstep_simp] theorem absClassCtor_cv (x : arena.inductives.gen_rec.ClassCtor) :
    (absClassCtor x).cv = absIConstantVal x.cv := rfl
@[lockstep_simp] theorem absClassCtor_nF (x : arena.inductives.gen_rec.ClassCtor) :
    (absClassCtor x).nF = absU x.n_f := rfl
@[lockstep_simp] theorem absClassCtor_kinds (x : arena.inductives.gen_rec.ClassCtor) :
    (absClassCtor x).kinds = x.kinds.val.map absClassField := rfl
@[lockstep_simp] theorem absClassCtor_tyD (x : arena.inductives.gen_rec.ClassCtor) :
    (absClassCtor x).tyD = absEIdx x.ty_d := rfl
@[lockstep_simp] theorem absClassCtor_tyN (x : arena.inductives.gen_rec.ClassCtor) :
    (absClassCtor x).tyN = absEIdx x.ty_n := rfl

@[lockstep_simp] theorem absClassGen_nP (g : arena.inductives.gen_rec.ClassGen) :
    (absClassGen g).nP = absU g.n_p := rfl
@[lockstep_simp] theorem absClassGen_params (g : arena.inductives.gen_rec.ClassGen) :
    (absClassGen g).params = absEIdxL g.params := rfl
@[lockstep_simp] theorem absClassGen_cls (g : arena.inductives.gen_rec.ClassGen) :
    (absClassGen g).cls = g.cls.val.map absTargetMajor := rfl
@[lockstep_simp] theorem absClassGen_formerTys (g : arena.inductives.gen_rec.ClassGen) :
    (absClassGen g).formerTys = absEIdxL g.former_tys := rfl
@[lockstep_simp] theorem absClassGen_slots (g : arena.inductives.gen_rec.ClassGen) :
    (absClassGen g).slots = g.slots.val.map absClassSlot := rfl
@[lockstep_simp] theorem absClassGen_ctors (g : arena.inductives.gen_rec.ClassGen) :
    (absClassGen g).ctors = g.ctors.val.map (fun cs => cs.val.map absClassCtor) := rfl
@[lockstep_simp] theorem absClassGen_elim (g : arena.inductives.gen_rec.ClassGen) :
    (absClassGen g).elim = absLIdx g.elim := rfl
@[lockstep_simp] theorem absClassGen_bm (g : arena.inductives.gen_rec.ClassGen) :
    (absClassGen g).bm = ConRon.Refine.absBinderMeta g.bm := rfl
@[lockstep_simp] theorem absClassGen_pre (g : arena.inductives.gen_rec.ClassGen) :
    (absClassGen g).pre = absBinderL g.pre := rfl

/-- The generator's representation facts: its datum and its prefix are
canonical (`PropWhenWF`, the erased subtype invariant). -/
def ClassGenWF (g : arena.inductives.gen_rec.ClassGen) : Prop :=
  ConRon.Refine.PropWhenWF g.bm.pw ∧ TeleWF g.pre

theorem ClassGenWF.bm {g : arena.inductives.gen_rec.ClassGen} (h : ClassGenWF g) :
    ConRon.Refine.PropWhenWF g.bm.pw := h.1

theorem ClassGenWF.pre {g : arena.inductives.gen_rec.ClassGen} (h : ClassGenWF g) :
    TeleWF g.pre := h.2

/-! ## The copies (identities) -/

@[lockstep] theorem class_field_dup_spec (k : arena.inductives.gen_rec.ClassField) :
    LSP (arena.inductives.gen_rec.class_field_dup k) (fun o => o = k) := by
  intro o h
  cases k <;> simp only [arena.inductives.gen_rec.class_field_dup, Result.ok.injEq] at h <;>
    exact h.symm

/-- A copy loop whose element copy is the identity (`Positivity.lean`'s
private `copy_loop_id`, restated). -/
theorem gr_copy_loop_id {α : Type} (dup : α → Result α) (hd : ∀ x y, dup x = ok y → y = x)
    (xs : alloc.vec.Vec α) (F : Std.Usize → alloc.vec.Vec α → Result (alloc.vec.Vec α))
    (heq : ∀ i out, F i out = (if i ≥ alloc.vec.Vec.len xs then ok out else do
      let x ← alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice α) xs i
      let y ← dup x
      let out1 ← alloc.vec.Vec.push out y
      let i2 ← i + 1#usize
      F i2 out1)) :
    ∀ (o : alloc.vec.Vec α), F 0#usize (alloc.vec.Vec.new α) = ok o → o = xs := by
  refine vec_copy_id xs F ?_ ?_
  · intro i out o hn h
    rw [heq, if_pos (show i ≥ alloc.vec.Vec.len xs by scalar_tac), Result.ok.injEq] at h
    rw [h]
  · intro i x out o hx h
    rw [heq, if_neg (show ¬ i ≥ alloc.vec.Vec.len xs by
      have := (List.getElem?_eq_some_iff.mp hx).1; scalar_tac)] at h
    obtain ⟨q, hq, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have hqx : q = x := by
      have h1 := vec_index_some hq; rw [hx] at h1; exact (Option.some_inj.mp h1).symm
    subst hqx
    obtain ⟨y, hy, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨out1, hout1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨i2, hi2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    rw [hd _ _ hy] at hout1
    exact ⟨i2, out1, absSz_add_one hi2, ConRon.Refine.vec_push_val hout1, h⟩

@[lockstep] theorem class_fields_dup_spec (ks : alloc.vec.Vec arena.inductives.gen_rec.ClassField) :
    LSP (arena.inductives.gen_rec.class_fields_dup ks 0#usize (alloc.vec.Vec.new _))
      (fun o => o = ks) :=
  gr_copy_loop_id _ (fun x y h => class_field_dup_spec x y h) ks
    (arena.inductives.gen_rec.class_fields_dup ks)
    (fun i out => by rw [arena.inductives.gen_rec.class_fields_dup.eq_def])

@[lockstep] theorem class_ctor_dup_spec (x : arena.inductives.gen_rec.ClassCtor) :
    LSP (arena.inductives.gen_rec.class_ctor_dup x) (fun o => o = x) := by
  intro o h
  rw [arena.inductives.gen_rec.class_ctor_dup] at h
  obtain ⟨cv, hcv, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨v, hv, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨e, he, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨e1, he1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  cases Result.ok_injective h
  rw [pos_i_constant_val_dup_spec _ _ hcv, class_fields_dup_spec _ _ hv, dupId_eidx _ _ he,
    dupId_eidx _ _ he1]

@[lockstep] theorem class_ctors_dup_spec (xs : alloc.vec.Vec arena.inductives.gen_rec.ClassCtor) :
    LSP (arena.inductives.gen_rec.class_ctors_dup xs 0#usize (alloc.vec.Vec.new _))
      (fun o => o = xs) :=
  gr_copy_loop_id _ (fun x y h => class_ctor_dup_spec x y h) xs
    (arena.inductives.gen_rec.class_ctors_dup xs)
    (fun i out => by rw [arena.inductives.gen_rec.class_ctors_dup.eq_def])

/-! ## `close_lams` -/

/-- `close_lams` ⊑ `closeLams`, the telescope from the cursor on. -/
@[lockstep] theorem close_lams_ls {pers}
    {bs : alloc.vec.Vec (arena.handle.EIdx × kernel.expr.BinderMeta)}
    {body : arena.handle.EIdx} (hte : TeleWF bs) :
    ∀ (k : Std.Usize) (i : Std.U64) st lst, AStateRel₀ pers st lst → AStateInv pers st →
      LS pers (fun a b => b = absEIdx a)
        (arena.inductives.gen_rec.close_lams pers st bs k i body) lst
        (closeLams (absBinderLFrom bs k) (absU i) (absEIdx body)) := by
  intro k i st lst hrel hinv
  refine ls_cursor_acc bs (fun p => (absEIdx p.1, ConRon.Refine.absBinderMeta p.2))
    (fun (w : Std.U64) l => closeLams l (absU w) (absEIdx body))
    (fun st k w => arena.inductives.gen_rec.close_lams pers st bs k w body)
    ?_ ?_ k st lst i hrel hinv
  · intro st lst k w hn hrel hinv
    rw [arena.inductives.gen_rec.close_lams.eq_def,
      if_pos (show k ≥ alloc.vec.Vec.len bs by scalar_tac), closeLams]
    lockstep
  · intro st lst k w hk hrel hinv ih
    have ih' : ∀ st' lst' (j : Std.Usize) (w' : Std.U64), j.val = k.val + 1 →
        AStateRel₀ pers st' lst' → AStateInv pers st' →
        LS pers (fun a b => b = absEIdx a)
          (arena.inductives.gen_rec.close_lams pers st' bs j w' body) lst'
          (closeLams (absBinderLFrom bs j) (absU w') (absEIdx body)) := ih
    clear ih
    have hpw := TeleWF.get hte k.val hk
    rw [arena.inductives.gen_rec.close_lams.eq_def,
      if_neg (show ¬ k ≥ alloc.vec.Vec.len bs by scalar_tac), closeLams]
    lockstep

/-! ## `expr_get_d` -/

/-- `expr_get_d` ⊑ `exprGetD`. -/
@[lockstep] theorem expr_get_d_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (xs : alloc.vec.Vec arena.handle.EIdx) (i : Std.U64) :
    LS pers (fun a b => b = absEIdx a)
      (arena.inductives.gen_rec.expr_get_d pers st xs i) lst
      (exprGetD (absEIdxL xs) (absU i)) := by
  rw [arena.inductives.gen_rec.expr_get_d, exprGetD]
  lockstep

/-! ## The binders: `class_binders`, `gen_binders` (`List.mapM` in its loop form) -/

theorem absBinderL_push {out o : alloc.vec.Vec (arena.handle.EIdx × kernel.expr.BinderMeta)}
    {x : arena.handle.EIdx × kernel.expr.BinderMeta} (h : o.val = out.val ++ [x]) :
    (absBinderL o).reverse = (absEIdx x.1, ConRon.Refine.absBinderMeta x.2) :: (absBinderL out).reverse := by
  simp [absBinderL, h]

@[lockstep_simp] theorem absBinderL_new :
    absBinderL (alloc.vec.Vec.new (arena.handle.EIdx × kernel.expr.BinderMeta)) = [] := rfl

theorem class_binders_acc {pers st} (xs : alloc.vec.Vec arena.handle.EIdx) :
    ∀ (i : Std.Usize) (out : alloc.vec.Vec (arena.handle.EIdx × kernel.expr.BinderMeta)) lst,
      AStateRel₀ pers st lst → AStateInv pers st → TeleWF out →
      LSR pers (fun a b => b = absBinderL a ∧ TeleWF a)
        (arena.inductives.gen_rec.class_binders pers st xs i out) st lst
        (List.mapM.loop classBinder ((xs.val.drop i.val).map absEIdx) (absBinderL out).reverse) := by
  refine cursor_induction (fun i : Std.Usize => i.val) xs.val.length
    (fun i out => ∀ lst, AStateRel₀ pers st lst → AStateInv pers st → TeleWF out →
      LSR pers (fun a b => b = absBinderL a ∧ TeleWF a)
        (arena.inductives.gen_rec.class_binders pers st xs i out) st lst
        (List.mapM.loop classBinder ((xs.val.drop i.val).map absEIdx)
          (absBinderL out).reverse)) ?_ ?_
  · intro i out hn lst hrel hinv hout
    rw [List.drop_eq_nil_of_le hn, List.map_nil, List.mapM.loop, List.reverse_reverse]
    apply LSR.of_LS
    rw [arena.inductives.gen_rec.class_binders.eq_def,
      if_pos (show i ≥ alloc.vec.Vec.len xs by scalar_tac)]
    lockstep
  · intro i out hi ih lst hrel hinv hout
    rw [List.drop_eq_getElem_cons hi, List.map_cons, List.mapM.loop]
    apply LSR.of_LS
    rw [arena.inductives.gen_rec.class_binders.eq_def,
      if_neg (show ¬ i ≥ alloc.vec.Vec.len xs by scalar_tac), classBinder]
    lockstep

/-- `class_binders` from `0` into `Vec::new()` ⊑ `xs.mapM classBinder`. -/
@[lockstep] theorem class_binders_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (xs : alloc.vec.Vec arena.handle.EIdx) :
    LSR pers (fun a b => b = absBinderL a ∧ TeleWF a)
      (arena.inductives.gen_rec.class_binders pers st xs 0#usize (alloc.vec.Vec.new _)) st lst
      ((absEIdxL xs).mapM classBinder) := by
  have h := class_binders_acc (pers := pers) xs 0#usize (alloc.vec.Vec.new _) lst hrel hinv
    TeleWF.new
  simpa [absEIdxL, absBinderL, alloc.vec.Vec.new, List.mapM] using h

theorem gen_binders_acc {pers st} (g : arena.inductives.gen_rec.ClassGen)
    (hbm : ConRon.Refine.PropWhenWF g.bm.pw) (xs : alloc.vec.Vec arena.handle.EIdx) :
    ∀ (i : Std.Usize) (out : alloc.vec.Vec (arena.handle.EIdx × kernel.expr.BinderMeta)) lst,
      AStateRel₀ pers st lst → AStateInv pers st → TeleWF out →
      LSR pers (fun a b => b = absBinderL a ∧ TeleWF a)
        (arena.inductives.gen_rec.gen_binders pers st g xs i out) st lst
        (List.mapM.loop (absClassGen g).binder ((xs.val.drop i.val).map absEIdx)
          (absBinderL out).reverse) := by
  refine cursor_induction (fun i : Std.Usize => i.val) xs.val.length
    (fun i out => ∀ lst, AStateRel₀ pers st lst → AStateInv pers st → TeleWF out →
      LSR pers (fun a b => b = absBinderL a ∧ TeleWF a)
        (arena.inductives.gen_rec.gen_binders pers st g xs i out) st lst
        (List.mapM.loop (absClassGen g).binder ((xs.val.drop i.val).map absEIdx)
          (absBinderL out).reverse)) ?_ ?_
  · intro i out hn lst hrel hinv hout
    rw [List.drop_eq_nil_of_le hn, List.map_nil, List.mapM.loop, List.reverse_reverse]
    apply LSR.of_LS
    rw [arena.inductives.gen_rec.gen_binders.eq_def,
      if_pos (show i ≥ alloc.vec.Vec.len xs by scalar_tac)]
    lockstep
  · intro i out hi ih lst hrel hinv hout
    rw [List.drop_eq_getElem_cons hi, List.map_cons, List.mapM.loop]
    apply LSR.of_LS
    rw [arena.inductives.gen_rec.gen_binders.eq_def,
      if_neg (show ¬ i ≥ alloc.vec.Vec.len xs by scalar_tac), ClassGen.binder]
    lockstep

/-- `gen_binders` from `0` into `Vec::new()` ⊑ `xs.mapM g.binder`. -/
@[lockstep high] theorem gen_binders_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (g : arena.inductives.gen_rec.ClassGen)
    (hbm : ConRon.Refine.PropWhenWF g.bm.pw) (xs : alloc.vec.Vec arena.handle.EIdx) :
    LSR pers (fun a b => b = absBinderL a ∧ TeleWF a)
      (arena.inductives.gen_rec.gen_binders pers st g xs 0#usize (alloc.vec.Vec.new _)) st lst
      ((absEIdxL xs).mapM (absClassGen g).binder) := by
  have h := gen_binders_acc (pers := pers) g hbm xs 0#usize (alloc.vec.Vec.new _) lst hrel hinv
    TeleWF.new
  simpa [absEIdxL, absBinderL, alloc.vec.Vec.new, List.mapM] using h

/-- `List.mapM.loop` with an accumulator is the `mapM` behind it. -/
theorem mapM_loop_acc {α β : Type} (f : α → AM β) (l : List α) (acc : List β) :
    List.mapM.loop f l acc = (do let r ← List.mapM.loop f l []; pure (acc.reverse ++ r)) := by
  induction l generalizing acc with
  | nil => simp [List.mapM.loop]
  | cons a l ih =>
    simp only [List.mapM.loop, bind_assoc]
    congr 1; funext b
    rw [ih, ih (b :: [])]
    simp

/-- A twin-only `map` on a read's answer, taken off: the relation composed
with it. -/
theorem LSR.of_twin_map {α β γ : Type} {pers : arena.store.PersTier} {R₁ : α → γ → Prop}
    {m : Result (core.result.Result α kernel.core_types.CheckError)}
    {st : arena.monad.AState} {lst : AState} {x : AM β} {f : β → γ}
    (h : LSR pers R₁ m st lst (x >>= fun b => pure (f b))) :
    LSR pers (fun a b => R₁ a (f b)) m st lst x := by
  intro o hm
  have h1 := h o hm
  rw [StateT.run_bind] at h1
  cases hx : x.run lst with
  | error le =>
    rw [hx] at h1
    cases o with
    | Err e =>
      intro k hk
      obtain ⟨le', hle, hk'⟩ := h1 k hk
      have : le' = le := by
        change Except.error le = Except.error le' at hle
        cases hle; rfl
      subst this
      exact ⟨le', rfl, hk'⟩
    | Ok a =>
      obtain ⟨b, lst', hb, -⟩ := h1
      exact absurd hb (by simp [Bind.bind, Except.bind])
  | ok p =>
    rw [hx] at h1
    obtain ⟨b, l1⟩ := p
    cases o with
    | Err e =>
      intro k hk
      obtain ⟨le, hle, -⟩ := h1 k hk
      exact absurd hle (by
        show Except.bind (Except.ok (b, l1)) (fun p => (pure (f p.1) : AM γ).run p.2) ≠ _
        simp [Except.bind, Pure.pure, StateT.pure, StateT.run, Except.pure])
    | Ok a =>
      obtain ⟨c, lst', hc, hR, h2, h3⟩ := h1
      simp only [Bind.bind, Except.bind, Pure.pure, StateT.pure, Except.pure, StateT.run,
        Except.ok.injEq, Prod.mk.injEq] at hc
      obtain ⟨rfl, rfl⟩ := hc
      exact ⟨b, l1, rfl, hR, h2, h3⟩

/-- `gen_binders` seeded with a prefix `out` ⊑ `xs.mapM g.binder`, the prefix
in front of the answer (`classGenRecTy`'s `g.pre ++ ibs`). -/
@[lockstep] theorem gen_binders_pre_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (g : arena.inductives.gen_rec.ClassGen)
    (hbm : ConRon.Refine.PropWhenWF g.bm.pw) (xs : alloc.vec.Vec arena.handle.EIdx)
    (out : alloc.vec.Vec (arena.handle.EIdx × kernel.expr.BinderMeta)) (hout : TeleWF out) :
    LSR pers (fun a b => absBinderL a = absBinderL out ++ b ∧ TeleWF a)
      (arena.inductives.gen_rec.gen_binders pers st g xs 0#usize out) st lst
      ((absEIdxL xs).mapM (absClassGen g).binder) := by
  have h := gen_binders_acc (pers := pers) g hbm xs 0#usize out lst hrel hinv hout
  rw [mapM_loop_acc, List.reverse_reverse] at h
  have h2 := LSR.of_twin_map h
  have e : (List.mapM.loop (absClassGen g).binder
      ((xs.val.drop (0#usize : Std.Usize).val).map absEIdx) []) =
      (absEIdxL xs).mapM (absClassGen g).binder := by
    simp [absEIdxL, List.mapM]
  rw [e] at h2
  intro o ho
  have h3 := h2 o ho
  cases o with
  | Err e => exact h3
  | Ok a =>
    obtain ⟨b, lst', hb, ⟨h4, h5⟩, h6, h7⟩ := h3
    exact ⟨b, lst', hb, ⟨h4.symm, h5⟩, h6, h7⟩

/-- `class_gen_bm` ⊑ `classGenBm`, the datum canonical. -/
@[lockstep] theorem class_gen_bm_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (elim : arena.handle.LIdx) :
    LS pers (fun a b => b = ConRon.Refine.absBinderMeta a ∧ ConRon.Refine.PropWhenWF a.pw)
      (arena.inductives.gen_rec.class_gen_bm pers st elim) lst (classGenBm (absLIdx elim)) := by
  rw [arena.inductives.gen_rec.class_gen_bm, classGenBm]
  lockstep

/-- `slot_var` ⊑ `ClassGen.slotVar`. -/
@[lockstep] theorem slot_var_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (g : arena.inductives.gen_rec.ClassGen) (s : Std.U64) :
    LS pers (fun a b => b = absEIdx a)
      (arena.inductives.gen_rec.slot_var pers st g s) lst ((absClassGen g).slotVar (absU s)) := by
  rw [arena.inductives.gen_rec.slot_var, ClassGen.slotVar]
  lockstep

/-- `eidx_append` is the twin's `++`. -/
@[lockstep] theorem eidx_append_twin (xs ys : alloc.vec.Vec arena.handle.EIdx) :
    LSP (arena.inductives.gen_rec.eidx_append xs ys)
      (fun o => TwinEq (absEIdxL xs ++ absEIdxL ys) (absEIdxL o)) := by
  intro o h
  rw [arena.inductives.gen_rec.eidx_append] at h
  obtain ⟨v, hv, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have := append_eidx_twin v ys o h
  simp only [TwinEq] at this ⊢
  rw [← this]
  simp [absEIdxL, eidx_vec_dup_val hv]

end ConRon.Refine2
