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
import ConRon.Refine2.Inductives.ClassRead
import ConRon.Refine2.Inductives.RecCheck
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

/-! ## The pure scans

Each Rust cursor scan against the twin's `List` expression, stated at the
cursor (`List.range' i (n - i)`, `drop i`) and read at `0` by the `TwinEq`
companion.  The twin's lambdas that carry a `match` are the helpers below
(`grMinorIs`, `isMotiveSlot`, `grRecField`): a restated `match` is a new matcher
constant, so the twin functions that use them are restated once by `rfl`
(`classGenRule_eq`, …) in terms of these. -/

/-- `classGenRule`'s slot test. -/
def grMinorIs (c : Nat) (C : NIdx) : Nat × ClassSlot → Bool
  | (_, .minor c' C' _) => c' == c && C' == C
  | (_, .motive _) => false

/-- `minorTy`'s recursive-field reading. -/
def grRecField (kinds : List ClassField) (i : Nat) : Option (Nat × Nat × Nat) :=
  match kinds.getD i .ordinary with
  | .recursive t tele => some (i, t, tele)
  | .ordinary => none

def absTriple (p : Std.U64 × Std.U64 × Std.U64) : Nat × Nat × Nat :=
  (absU p.1, absU p.2.1, absU p.2.2)

theorem u64_eq_iff_val {a b : Std.U64} : a = b ↔ a.val = b.val :=
  ⟨fun h => h ▸ rfl, fun h => by scalar_tac⟩

/-- `class_rec_of` from the cursor `r`. -/
theorem class_rec_of_abs (rec_cls : alloc.vec.Vec Std.U64)
    (cv_gs : alloc.vec.Vec arena.env.IConstantVal) (t : Std.U64) :
    ∀ (r : Std.Usize) (o : Option arena.handle.NIdx),
      arena.inductives.gen_rec.class_rec_of rec_cls cv_gs t r = ok o →
      o.map absNIdx = ((List.range' r.val (cv_gs.val.length - r.val)).find?
        (fun r => (absNatL rec_cls).getD r 0 == absU t)).map
          (fun r => ((cv_gs.val.map absIConstantVal).getD r default).name) := by
  intro r
  refine cursor_induction (fun i : Std.Usize => i.val) cv_gs.val.length
    (fun r (_ : Unit) => ∀ o, arena.inductives.gen_rec.class_rec_of rec_cls cv_gs t r = ok o →
      o.map absNIdx = ((List.range' r.val (cv_gs.val.length - r.val)).find?
        (fun r => (absNatL rec_cls).getD r 0 == absU t)).map
          (fun r => ((cv_gs.val.map absIConstantVal).getD r default).name)) ?_ ?_ r ()
  · intro r _ hn o h
    rw [arena.inductives.gen_rec.class_rec_of.eq_def,
      if_pos (show r ≥ alloc.vec.Vec.len cv_gs by scalar_tac), Result.ok.injEq] at h
    subst h
    rw [show cv_gs.val.length - r.val = 0 by omega]
    rfl
  · intro r _ hr ih o h
    rw [arena.inductives.gen_rec.class_rec_of.eq_def,
      if_neg (show ¬ r ≥ alloc.vec.Vec.len cv_gs by scalar_tac)] at h
    rw [show cv_gs.val.length - r.val = (cv_gs.val.length - (r.val + 1)) + 1 by omega,
      List.range'_succ, List.find?_cons]
    obtain ⟨c, hc, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have hcv : absU c = (absNatL rec_cls).getD r.val 0 := by
      split at hc
      · have := vec_index_some hc
        simp only [absNatL, List.getD_eq_getElem?_getD, List.getElem?_map, this]
        rfl
      · rw [Result.ok.injEq] at hc
        subst hc
        simp only [absNatL, List.getD_eq_getElem?_getD, List.getElem?_map]
        rw [List.getElem?_eq_none (by simp [alloc.vec.Vec.len] at *; scalar_tac)]
        rfl
    by_cases hct : c = t
    · rw [if_pos hct] at h
      obtain ⟨iv, hiv, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      obtain ⟨n, hn, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      rw [Result.ok.injEq] at h
      subst h
      rw [← hcv, hct]
      simp only [beq_self_eq_true, Option.map_some]
      have hx := vec_index_some hiv
      rw [dupId_nidx _ _ hn, List.getD_eq_getElem?_getD, List.getElem?_map, hx]
      rfl
    · rw [if_neg hct] at h
      obtain ⟨r2, hr2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      have hr2v : r2.val = r.val + 1 := absSz_add_one hr2
      rw [ih r2 () hr2v o h, hr2v, ← hcv]
      have : (absU c == absU t) = false := by
        simp only [beq_eq_false_iff_ne, ne_eq]
        intro he; exact hct (u64_eq_iff_val.mpr he)
      rw [this]

/-- `class_rec_of … 0` is `classRecOf`. -/
@[lockstep] theorem class_rec_of_twin (rec_cls : alloc.vec.Vec Std.U64)
    (cv_gs : alloc.vec.Vec arena.env.IConstantVal) (t : Std.U64) :
    LSP (arena.inductives.gen_rec.class_rec_of rec_cls cv_gs t 0#usize)
      (fun o => TwinEq (classRecOf (absNatL rec_cls) (cv_gs.val.map absIConstantVal) (absU t))
        (o.map absNIdx)) := by
  intro o h
  rw [TwinEq, class_rec_of_abs rec_cls cv_gs t 0#usize o h, classRecOf]
  simp [List.range_eq_range']

/-- `minor_is` is the slot test. -/
@[lockstep] theorem minor_is_twin (sl : arena.inductives.class_read.ClassSlot) (c : Std.U64)
    (cn : arena.handle.NIdx) (k : Nat) :
    LSP (arena.inductives.gen_rec.minor_is sl c cn)
      (fun b => b = grMinorIs (absU c) (absNIdx cn) (k, absClassSlot sl)) := by
  intro b h
  cases sl with
  | Motive _ =>
    simp only [arena.inductives.gen_rec.minor_is, Result.ok.injEq] at h
    subst h; rfl
  | Minor c2 n2 ihs =>
    rw [arena.inductives.gen_rec.minor_is] at h
    simp only [absClassSlot, grMinorIs]
    by_cases hc : c2 = c
    · rw [if_pos hc] at h
      rw [nidx_eq2_abs h, hc]
      simp
    · rw [if_neg hc, Result.ok.injEq] at h
      subst h
      have : (absU c2 == absU c) = false := by
        simp only [beq_eq_false_iff_ne, ne_eq]
        intro he; exact hc (u64_eq_iff_val.mpr he)
      rw [this]; rfl

/-- `find_minor_slot` from the cursor `s`. -/
theorem find_minor_slot_abs (slots : alloc.vec.Vec arena.inductives.class_read.ClassSlot)
    (c : Std.U64) (cn : arena.handle.NIdx) :
    ∀ (s : Std.Usize) (o : Option Std.U64),
      arena.inductives.gen_rec.find_minor_slot slots c cn s = ok o →
      ((List.range' s.val (slots.val.length - s.val)).zip
          ((slots.val.drop s.val).map absClassSlot)).find? (grMinorIs (absU c) (absNIdx cn)) =
        o.map (fun k => (absU k, (slots.val.map absClassSlot).getD (absU k) default)) := by
  intro s
  refine cursor_induction (fun i : Std.Usize => i.val) slots.val.length
    (fun s (_ : Unit) => ∀ o, arena.inductives.gen_rec.find_minor_slot slots c cn s = ok o →
      ((List.range' s.val (slots.val.length - s.val)).zip
          ((slots.val.drop s.val).map absClassSlot)).find? (grMinorIs (absU c) (absNIdx cn)) =
        o.map (fun k => (absU k, (slots.val.map absClassSlot).getD (absU k) default))) ?_ ?_ s ()
  · intro s _ hn o h
    rw [arena.inductives.gen_rec.find_minor_slot.eq_def,
      if_pos (show s ≥ alloc.vec.Vec.len slots by scalar_tac), Result.ok.injEq] at h
    subst h
    rw [show slots.val.length - s.val = 0 by omega]
    rfl
  · intro s _ hs ih o h
    rw [arena.inductives.gen_rec.find_minor_slot.eq_def,
      if_neg (show ¬ s ≥ alloc.vec.Vec.len slots by scalar_tac)] at h
    rw [show slots.val.length - s.val = (slots.val.length - (s.val + 1)) + 1 by omega,
      List.range'_succ, List.drop_eq_getElem_cons hs, List.map_cons, List.zip_cons_cons,
      List.find?_cons]
    obtain ⟨cs, hcs, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have hx := vec_index_some hcs
    obtain ⟨hxb, hxv⟩ := List.getElem?_eq_some_iff.mp hx
    obtain ⟨b, hb, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have hbv := minor_is_twin cs c cn s.val b hb
    rw [hxv, ← hbv]
    cases b
    · rw [if_neg (by simp)] at h
      obtain ⟨s2, hs2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      have hs2v : s2.val = s.val + 1 := absSz_add_one hs2
      rw [← ih s2 () hs2v o h, hs2v]
    · rw [if_pos rfl] at h
      obtain ⟨k, hk, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      rw [Result.ok.injEq] at h
      subst h
      have hkv : k.val = s.val := by
        simp only [lift, Result.ok.injEq] at hk; subst hk
        exact ConRon.Refine.ExprOps.usize_cast_u64_val s
      simp only [Option.map_some, absU, hkv]
      rw [List.getD_eq_getElem?_getD, List.getElem?_map, hx]
      rfl

/-- `find_minor_slot … 0` is `classGenRule`'s `hit`. -/
@[lockstep] theorem find_minor_slot_twin (slots : alloc.vec.Vec arena.inductives.class_read.ClassSlot)
    (c : Std.U64) (cn : arena.handle.NIdx) :
    LSP (arena.inductives.gen_rec.find_minor_slot slots c cn 0#usize)
      (fun o => TwinEq (((List.range (slots.val.map absClassSlot).length).zip
          (slots.val.map absClassSlot)).find? (grMinorIs (absU c) (absNIdx cn)))
        (o.map (fun k => (absU k, (slots.val.map absClassSlot).getD (absU k) default)))) := by
  intro o h
  rw [TwinEq, ← find_minor_slot_abs slots c cn 0#usize o h]
  simp [List.range_eq_range']

/-- `motives_before` from the cursor `i`. -/
theorem motives_before_abs (slots : alloc.vec.Vec arena.inductives.class_read.ClassSlot)
    (s : Std.Usize) :
    ∀ (i : Std.Usize) (acc o : Std.U64),
      arena.inductives.gen_rec.motives_before slots s i acc = ok o →
      o.val = acc.val + ((((slots.val.map absClassSlot).take s.val).drop i.val).filter
        isMotiveSlot).length := by
  intro i
  refine cursor_induction (fun i : Std.Usize => i.val) (min s.val slots.val.length)
    (fun i (_ : Unit) => ∀ acc o, arena.inductives.gen_rec.motives_before slots s i acc = ok o →
      o.val = acc.val + ((((slots.val.map absClassSlot).take s.val).drop i.val).filter
        isMotiveSlot).length) ?_ ?_ i ()
  · intro i _ hn acc o h
    rw [List.drop_eq_nil_of_le (by simp; omega)]
    rw [arena.inductives.gen_rec.motives_before.eq_def] at h
    by_cases h1 : i ≥ s
    · rw [if_pos h1, Result.ok.injEq] at h; subst h; simp
    · rw [if_neg h1, if_pos (show i ≥ alloc.vec.Vec.len slots by scalar_tac),
        Result.ok.injEq] at h
      subst h; simp
  · intro i _ hi ih acc o h
    have his : i.val < s.val := by omega
    have hil : i.val < slots.val.length := by omega
    rw [arena.inductives.gen_rec.motives_before.eq_def, if_neg (by scalar_tac),
      if_neg (show ¬ i ≥ alloc.vec.Vec.len slots by scalar_tac)] at h
    rw [List.drop_eq_getElem_cons (by simp; omega)]
    obtain ⟨cs, hcs, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have hx := vec_index_some hcs
    obtain ⟨hxb, hxv⟩ := List.getElem?_eq_some_iff.mp hx
    obtain ⟨b, hb, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have hbv : b = isMotiveSlot (absClassSlot cs) := is_motive_twin cs b hb
    simp only [List.getElem_take, List.getElem_map, hxv, List.filter_cons]
    rw [← hbv]
    cases b
    · rw [if_neg (by simp)] at h
      obtain ⟨i2, hi2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      have hi2v : i2.val = i.val + 1 := absSz_add_one hi2
      rw [ih i2 () hi2v acc o h, hi2v]
      simp
    · rw [if_pos rfl] at h
      obtain ⟨i2, hi2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      obtain ⟨a2, ha2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      have hi2v : i2.val = i.val + 1 := absSz_add_one hi2
      have ha2v : a2.val = acc.val + 1 := ConRon.Refine.Nat.uadd_val ha2
      rw [ih i2 () hi2v a2 o h, hi2v, ha2v]
      simp; omega

/-- `motives_before … s 0 0` is the twin's count of the motives before slot `s`. -/
@[lockstep] theorem motives_before_twin (slots : alloc.vec.Vec arena.inductives.class_read.ClassSlot)
    (s : Std.Usize) :
    LSP (arena.inductives.gen_rec.motives_before slots s 0#usize 0#u64)
      (fun o => TwinEq ((((slots.val.map absClassSlot).take s.val).filter isMotiveSlot).length)
        (absU o)) := by
  intro o h
  rw [TwinEq, absU, motives_before_abs slots s 0#usize 0#u64 o h]
  simp

/-- `find_class_ctor_in` from the cursor `i`. -/
theorem find_class_ctor_in_abs (xs : alloc.vec.Vec arena.inductives.gen_rec.ClassCtor)
    (cn : arena.handle.NIdx) :
    ∀ (i : Std.Usize) (o : Option arena.inductives.gen_rec.ClassCtor),
      arena.inductives.gen_rec.find_class_ctor_in xs cn i = ok o →
      o.map absClassCtor = ((xs.val.drop i.val).map absClassCtor).find?
        (·.cv.name == absNIdx cn) := by
  intro i
  refine cursor_induction (fun i : Std.Usize => i.val) xs.val.length
    (fun i (_ : Unit) => ∀ o, arena.inductives.gen_rec.find_class_ctor_in xs cn i = ok o →
      o.map absClassCtor = ((xs.val.drop i.val).map absClassCtor).find?
        (·.cv.name == absNIdx cn)) ?_ ?_ i ()
  · intro i _ hn o h
    rw [arena.inductives.gen_rec.find_class_ctor_in.eq_def,
      if_pos (show i ≥ alloc.vec.Vec.len xs by scalar_tac), Result.ok.injEq] at h
    subst h
    rw [List.drop_eq_nil_of_le hn]; rfl
  · intro i _ hi ih o h
    rw [arena.inductives.gen_rec.find_class_ctor_in.eq_def,
      if_neg (show ¬ i ≥ alloc.vec.Vec.len xs by scalar_tac)] at h
    rw [List.drop_eq_getElem_cons hi, List.map_cons, List.find?_cons]
    obtain ⟨cc, hcc, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have hx := vec_index_some hcc
    obtain ⟨hxb, hxv⟩ := List.getElem?_eq_some_iff.mp hx
    obtain ⟨b, hb, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have hbv := nidx_eq2_abs hb
    rw [hxv]
    change _ = match (absNIdx cc.cv.name == absNIdx cn) with
      | true => some (absClassCtor cc) | false => _
    rw [← hbv]
    cases b
    · rw [if_neg (by simp)] at h
      obtain ⟨i2, hi2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      have hi2v : i2.val = i.val + 1 := absSz_add_one hi2
      rw [ih i2 () hi2v o h, hi2v]
    · rw [if_pos rfl] at h
      obtain ⟨cc1, hcc1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      rw [Result.ok.injEq] at h
      subst h
      rw [class_ctor_dup_spec _ _ hcc1]
      rfl

/-- `find_class_ctor` is `prefixBinders`' constructor lookup. -/
@[lockstep] theorem find_class_ctor_twin (g : arena.inductives.gen_rec.ClassGen) (c : Std.U64)
    (cn : arena.handle.NIdx) :
    LSP (arena.inductives.gen_rec.find_class_ctor g c cn)
      (fun o => TwinEq (((g.ctors.val.map (fun cs => cs.val.map absClassCtor)).getD (absU c)
          []).find? (·.cv.name == absNIdx cn)) (o.map absClassCtor)) := by
  intro o h
  rw [arena.inductives.gen_rec.find_class_ctor] at h
  obtain ⟨n, hn, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have hnv : n.val = g.ctors.val.length := by
    simp only [lift, Result.ok.injEq] at hn; subst hn
    simp
  rw [TwinEq]
  split at h
  · rename_i hcn
    obtain ⟨k, hk, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨v, hv, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have hkv : k.val = c.val := by
      simp only [lift, Result.ok.injEq] at hk
      subst hk
      exact ConRon.Refine.ExprOps.u64_cast_usize_val (by
        have := g.ctors.property
        scalar_tac)
    have hx := vec_index_some hv
    rw [find_class_ctor_in_abs v cn 0#usize o h]
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, show absU c = k.val from hkv.symm, hx]
    simp
  · rw [Result.ok.injEq] at h
    subst h
    rw [List.getD_eq_default _ _ (by simp; scalar_tac)]
    rfl

/-! ## The generator's small steps -/

/-- `binder_copy_from … 0 Vec::new()` is a copy. -/
theorem binder_copy_from_new_spec
    (xs : alloc.vec.Vec (arena.handle.EIdx × kernel.expr.BinderMeta)) :
    LSP (arena.expr_ops.binder_copy_from xs 0#usize (alloc.vec.Vec.new _)) (fun r => r = xs) := by
  refine vec_copy_id xs (arena.expr_ops.binder_copy_from xs) ?_ ?_
  · intro i out o hn h
    rw [arena.expr_ops.binder_copy_from.eq_def,
      if_pos (show i ≥ alloc.vec.Vec.len xs by scalar_tac), Result.ok.injEq] at h
    rw [h]
  · intro i x out o hx h
    rw [arena.expr_ops.binder_copy_from.eq_def, if_neg (show ¬ i ≥ alloc.vec.Vec.len xs by
      have := (List.getElem?_eq_some_iff.mp hx).1; scalar_tac)] at h
    obtain ⟨q, hq, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have hqx : q = x := by
      have h1 := vec_index_some hq; rw [hx] at h1; exact (Option.some_inj.mp h1).symm
    subst hqx
    obtain ⟨e1, he1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨bm1, hbm1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨out1, hout1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨i2, hi2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    rw [dupId_eidx _ _ he1, ConRon.Refine.Expr.binder_meta_dup_eq hbm1] at hout1
    exact ⟨i2, out1, absSz_add_one hi2, ConRon.Refine.vec_push_val hout1, h⟩

attribute [local lockstep high] binder_copy_from_new_spec

/-- `mot_var` ⊑ `ClassGen.motVar`. -/
@[lockstep] theorem mot_var_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (g : arena.inductives.gen_rec.ClassGen) (c : Std.U64) :
    LS pers (fun a b => b = absEIdx a)
      (arena.inductives.gen_rec.mot_var pers st g c) lst ((absClassGen g).motVar (absU c)) := by
  rw [arena.inductives.gen_rec.mot_var, ClassGen.motVar]
  lockstep

/-- `ih_parts` ⊑ `ClassGen.ihParts`. -/
@[lockstep] theorem ih_parts_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (g : arena.inductives.gen_rec.ClassGen) (t tele : Std.U64)
    (w : arena.handle.EIdx) (d : Std.U64) :
    LS pers (fun a b => b = a.map (fun p => (absEIdxL p.1, absEIdxL p.2)))
      (arena.inductives.gen_rec.ih_parts pers st g t tele w d) lst
      ((absClassGen g).ihParts (absU t) (absU tele) (absEIdx w) (absU d)) := by
  rw [arena.inductives.gen_rec.ih_parts, ClassGen.ihParts]
  rcases hcls : (g.cls.val)[(absU t)]? with _ | m <;>
    simp only [absClassGen_cls, List.getElem?_map, hcls, Option.map_none, Option.map_some]
  · lockstep
    all_goals (exfalso; rw [List.getElem?_eq_none_iff] at hcls; simp only [absU] at hcls; scalar_tac)
  · obtain ⟨hb, rfl⟩ := List.getElem?_eq_some_iff.mp hcls
    lockstep
    rename_i n hn k hk hkb args
    refine LS.pure ?_ ‹_› ‹_›
    rcases hk with hk | hk
    · have e : (g.cls.val)[k.val]'hkb = (g.cls.val)[absU t]'hb := by simp only [absU, hk]
      simp only [TwinEq] at hP
      simp only [absEIdxL, Option.map_some] at hP ⊢
      rw [← hP, e]
      try rfl
    · exfalso
      have := g.cls.property
      simp only [absU] at hb
      scalar_tac

/-- `rec_fields` from the cursor `i`. -/
theorem rec_fields_abs (ks : alloc.vec.Vec arena.inductives.gen_rec.ClassField) (n_f : Std.U64) :
    ∀ (m : Nat) (i : Std.U64) (out o : alloc.vec.Vec (Std.U64 × Std.U64 × Std.U64)),
      n_f.val - i.val = m → arena.inductives.gen_rec.rec_fields ks n_f i out = ok o →
      o.val.map absTriple = out.val.map absTriple ++
        (List.range' i.val m).filterMap (grRecField (ks.val.map absClassField)) := by
  intro m
  induction m with
  | zero =>
    intro i out o hm h
    rw [arena.inductives.gen_rec.rec_fields.eq_def, if_pos (by scalar_tac), Result.ok.injEq] at h
    subst h; simp
  | succ m ih =>
    intro i out o hm h
    rw [arena.inductives.gen_rec.rec_fields.eq_def, if_neg (by scalar_tac)] at h
    rw [List.range'_succ, List.filterMap_cons]
    obtain ⟨n, hn, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have hnv : n.val = ks.val.length := by
      simp only [lift, Result.ok.injEq] at hn; subst hn
      simp
    split at h
    · rename_i hlt
      obtain ⟨k, hk, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      have hkv : k.val = i.val := by
        simp only [lift, Result.ok.injEq] at hk
        subst hk
        exact ConRon.Refine.ExprOps.u64_cast_usize_val (by have := ks.property; scalar_tac)
      obtain ⟨cf, hcf, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      have hx := vec_index_some hcf
      have hg : grRecField (ks.val.map absClassField) i.val =
          (match absClassField cf with
           | .recursive t tele => some (i.val, t, tele)
           | .ordinary => none) := by
        simp only [grRecField, List.getD_eq_getElem?_getD, List.getElem?_map, ← hkv, hx]
        rfl
      rw [hg]
      cases cf with
      | Ordinary =>
        obtain ⟨i4, hi4, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
        have hi4v : i4.val = i.val + 1 := ConRon.Refine.Nat.uadd_val hi4
        rw [ih i4 out o (by omega) h, hi4v]
        rfl
      | Recursive t tele =>
        obtain ⟨out1, hout1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
        obtain ⟨i4, hi4, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
        have hi4v : i4.val = i.val + 1 := ConRon.Refine.Nat.uadd_val hi4
        rw [ih i4 out1 o (by omega) h, hi4v, ConRon.Refine.vec_push_val hout1]
        simp [absTriple, absClassField, absU]
    · rename_i hge
      obtain ⟨i3, hi3, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      have hi3v : i3.val = i.val + 1 := ConRon.Refine.Nat.uadd_val hi3
      have hg : grRecField (ks.val.map absClassField) i.val = none := by
        simp only [grRecField, List.getD_eq_getElem?_getD, List.getElem?_map]
        rw [List.getElem?_eq_none (by scalar_tac)]
        rfl
      rw [hg, ih i3 out o (by omega) h, hi3v]

/-- `rec_fields … 0 Vec::new()` is `minorTy`'s `recs`. -/
@[lockstep] theorem rec_fields_twin (ks : alloc.vec.Vec arena.inductives.gen_rec.ClassField)
    (n_f : Std.U64) :
    LSP (arena.inductives.gen_rec.rec_fields ks n_f 0#u64 (alloc.vec.Vec.new _))
      (fun o => TwinEq ((List.range (absU n_f)).filterMap (grRecField (ks.val.map absClassField)))
        (o.val.map absTriple)) := by
  intro o h
  rw [TwinEq, rec_fields_abs ks n_f _ 0#u64 _ o rfl h]
  simp [List.range_eq_range', absU]

/-! ## `minor_ihs` ⊑ `minorTy.ihsGo`

The Rust pushes each hypothesis onto `out` and tail-calls; the twin recurses
and conses on the way out.  The statement carries `out` in front of the
twin's answer (`OptBinders out`), and the step closes the twin's
`match ← ihsGo … with | some ihs => pure (some (ih :: ihs))` by
`ls_tail_opt_cons`. -/

/-- An optional telescope's binders are canonical. -/
def OptTeleWF (a : Option (alloc.vec.Vec (arena.handle.EIdx × kernel.expr.BinderMeta))) : Prop :=
  ∀ v, a = some v → TeleWF v

theorem OptTeleWF.none : OptTeleWF none := fun _ h => by cases h

theorem OptTeleWF.some {v} (h : TeleWF v) : OptTeleWF (Option.some v) := fun _ h' => by
  cases h'; exact h

theorem OptTeleWF.get {v} (h : OptTeleWF (Option.some v)) : TeleWF v := h v rfl

/-- The answer relation of an optional telescope built onto `out`. -/
def OptBinders (out : alloc.vec.Vec (arena.handle.EIdx × kernel.expr.BinderMeta))
    (a : Option (alloc.vec.Vec (arena.handle.EIdx × kernel.expr.BinderMeta)))
    (b : Option (List (EIdx × ConLeche.BinderMeta))) : Prop :=
  a.map absBinderL = b.map (absBinderL out ++ ·) ∧ OptTeleWF a

theorem ls_tail_opt_cons {pers : arena.store.PersTier}
    {m : Result (core.result.Result (Option (alloc.vec.Vec (arena.handle.EIdx ×
      kernel.expr.BinderMeta))) kernel.core_types.CheckError × arena.monad.AState)}
    {lst : AState} {x : AM (Option (List (EIdx × ConLeche.BinderMeta)))}
    {y : EIdx × ConLeche.BinderMeta}
    {out out1 : alloc.vec.Vec (arena.handle.EIdx × kernel.expr.BinderMeta)}
    (h : LS pers (OptBinders out1) m lst x) (hout : absBinderL out1 = absBinderL out ++ [y]) :
    LS pers (OptBinders out) m lst (do
      match ← x with
      | none => pure none
      | some ihs => pure (some (y :: ihs))) := by
  have h2 := LS.twin_map (R := OptBinders out) (f := Option.map (y :: ·)) h (by
    intro a b ⟨h1, h2⟩
    refine ⟨?_, h2⟩
    rw [h1, hout]
    cases b <;> simp)
  refine LS.twin_eq h2 ?_
  congr 1
  funext r
  cases r <;> rfl

theorem minor_ihs_acc {pers} (g : arena.inductives.gen_rec.ClassGen) (hbm : ConRon.Refine.PropWhenWF g.bm.pw)
    (x : arena.inductives.gen_rec.ClassCtor) (d : Std.U64)
    (fvs ws : alloc.vec.Vec arena.handle.EIdx)
    (recs : alloc.vec.Vec (Std.U64 × Std.U64 × Std.U64)) :
    ∀ (l : Std.Usize) (out : alloc.vec.Vec (arena.handle.EIdx × kernel.expr.BinderMeta)) st lst,
      AStateRel₀ pers st lst → AStateInv pers st → TeleWF out →
      LS pers (OptBinders out)
        (arena.inductives.gen_rec.minor_ihs pers st g x d fvs ws recs l out) lst
        (ClassGen.minorTy.ihsGo (absClassGen g) (absClassCtor x) (absU d) (absEIdxL fvs)
          (absEIdxL ws) l.val ((recs.val.drop l.val).map absTriple)) := by
  intro l
  refine cursor_induction (fun i : Std.Usize => i.val) recs.val.length
    (fun l out => ∀ st lst, AStateRel₀ pers st lst → AStateInv pers st → TeleWF out →
      LS pers (OptBinders out)
        (arena.inductives.gen_rec.minor_ihs pers st g x d fvs ws recs l out) lst
        (ClassGen.minorTy.ihsGo (absClassGen g) (absClassCtor x) (absU d) (absEIdxL fvs)
          (absEIdxL ws) l.val ((recs.val.drop l.val).map absTriple))) ?_ ?_ l
  · intro l out hn st lst hrel hinv hout
    rw [List.drop_eq_nil_of_le hn, List.map_nil, ClassGen.minorTy.ihsGo,
      arena.inductives.gen_rec.minor_ihs.eq_def,
      if_pos (show l ≥ alloc.vec.Vec.len recs by scalar_tac)]
    exact LS.pure ⟨by simp, OptTeleWF.some hout⟩ hrel hinv
  · intro l out hl ih st lst hrel hinv hout
    rw [List.drop_eq_getElem_cons hl, List.map_cons, absTriple, ClassGen.minorTy.ihsGo,
      arena.inductives.gen_rec.minor_ihs.eq_def,
      if_neg (show ¬ l ≥ alloc.vec.Vec.len recs by scalar_tac)]
    lockstep
    · exact LS.pure ⟨rfl, OptTeleWF.none⟩ ‹_› ‹_›
    · rename_i ihd out1 hout1
      have hjv : a.val = l.val + 1 := by simpa using hP
      have h1 := ih a out1 hjv _ _ ‹_› ‹_› (TeleWF.push hout1 hout hbm)
      rw [hjv] at h1
      refine ls_tail_opt_cons h1 ?_
      simp [absBinderL, hout1]

/-- `minor_ihs` from `0` into `Vec::new()` ⊑ `minorTy.ihsGo … 0`. -/
@[lockstep] theorem minor_ihs_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (g : arena.inductives.gen_rec.ClassGen)
    (hbm : ConRon.Refine.PropWhenWF g.bm.pw)
    (x : arena.inductives.gen_rec.ClassCtor) (d : Std.U64)
    (fvs ws : alloc.vec.Vec arena.handle.EIdx)
    (recs : alloc.vec.Vec (Std.U64 × Std.U64 × Std.U64)) :
    LS pers (fun a b => b = a.map absBinderL ∧ OptTeleWF a)
      (arena.inductives.gen_rec.minor_ihs pers st g x d fvs ws recs 0#usize (alloc.vec.Vec.new _))
      lst
      (ClassGen.minorTy.ihsGo (absClassGen g) (absClassCtor x) (absU d) (absEIdxL fvs)
        (absEIdxL ws) 0 (recs.val.map absTriple)) := by
  have h := minor_ihs_acc g hbm x d fvs ws recs 0#usize (alloc.vec.Vec.new _) st lst hrel hinv
    TeleWF.new
  refine LS.tail h (by simp) ?_
  intro a b ⟨h1, h2⟩
  refine ⟨?_, h2⟩
  rw [h1]
  cases b <;> simp [absBinderL, alloc.vec.Vec.new]

/-! ## `classGenRule`'s parts: `prefix_vars`, `rule_calls`/`rule_call`, `class_gen_rule_close` -/

theorem gr_absIConstantVal_name (cv : arena.env.IConstantVal) :
    (absIConstantVal cv).name = absNIdx cv.name := rfl
theorem gr_absIConstantVal_levelParams (cv : arena.env.IConstantVal) :
    (absIConstantVal cv).levelParams = absNIdxL cv.level_params := rfl
theorem gr_absIConstantVal_type (cv : arena.env.IConstantVal) :
    (absIConstantVal cv).type = absEIdx cv.ty := rfl
attribute [local lockstep_simp] gr_absIConstantVal_name gr_absIConstantVal_levelParams
  gr_absIConstantVal_type

/-- `classGenRule`'s prefix variable `i`. -/
def grPVar (g : ClassGen) (i : Nat) : AM EIdx :=
  if i < g.nP then exprGetD g.params i else g.slotVar (i - g.nP)

/-- `classGenRule`'s closing tail: the minor premise applied, closed over the
prefix and the fields (the Rust's `class_gen_rule_close`). -/
def grRuleClose (g : ClassGen) (s : Nat) (fvs ihs : List EIdx) : AM (Option EIdx) := do
  let sv ← g.slotVar s
  let body ← mkAppN sv (fvs ++ ihs)
  let fbs ← fvs.mapM g.binder
  let r ← closeLams (g.pre ++ fbs) 0 body
  pure (some r)

theorem prefix_vars_acc {pers} (g : arena.inductives.gen_rec.ClassGen) (r_p : Std.U64) :
    ∀ (i : Std.U64) st lst (out : alloc.vec.Vec arena.handle.EIdx),
      AStateRel₀ pers st lst → AStateInv pers st →
      LS pers (fun a b => b = absEIdxL a)
        (arena.inductives.gen_rec.prefix_vars pers st g r_p i out) lst
        (List.mapM.loop (grPVar (absClassGen g)) (List.range' i.val (r_p.val - i.val))
          (absEIdxL out).reverse) := by
  refine ls_counted r_p
    (fun (w : alloc.vec.Vec arena.handle.EIdx) m i =>
      List.mapM.loop (grPVar (absClassGen g)) (List.range' i m) (absEIdxL w).reverse)
    (fun st i w => arena.inductives.gen_rec.prefix_vars pers st g r_p i w) ?_ ?_
  · intro st lst i w hn hrel hinv
    rw [arena.inductives.gen_rec.prefix_vars.eq_def, if_pos (by scalar_tac)]
    simp only [List.range'_zero, List.mapM.loop, List.reverse_reverse]
    lockstep
  · intro st lst i w m hi hm hrel hinv ih
    rw [arena.inductives.gen_rec.prefix_vars.eq_def, if_neg (by scalar_tac)]
    simp only [List.range'_succ, List.mapM.loop, grPVar]
    lockstep

/-- `prefix_vars … 0 Vec::new()` ⊑ `(List.range rP).mapM (grPVar g)`. -/
@[lockstep] theorem prefix_vars_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (g : arena.inductives.gen_rec.ClassGen) (r_p : Std.U64) :
    LS pers (fun a b => b = absEIdxL a)
      (arena.inductives.gen_rec.prefix_vars pers st g r_p 0#u64 (alloc.vec.Vec.new _)) lst
      ((List.range (absU r_p)).mapM (grPVar (absClassGen g))) := by
  have h := prefix_vars_acc (pers := pers) g r_p 0#u64 st lst (alloc.vec.Vec.new _) hrel hinv
  simpa [List.range_eq_range', absEIdxL, alloc.vec.Vec.new, List.mapM, absU] using h

/-- The answer relation of an optional term list built onto `out`. -/
def OptEIdxs (out : alloc.vec.Vec arena.handle.EIdx)
    (a : Option (alloc.vec.Vec arena.handle.EIdx)) (b : Option (List EIdx)) : Prop :=
  a.map absEIdxL = b.map (absEIdxL out ++ ·)

theorem ls_tail_opt_cons_e {pers : arena.store.PersTier}
    {m : Result (core.result.Result (Option (alloc.vec.Vec arena.handle.EIdx))
      kernel.core_types.CheckError × arena.monad.AState)}
    {lst : AState} {x : AM (Option (List EIdx))} {y : EIdx}
    {out out1 : alloc.vec.Vec arena.handle.EIdx}
    (h : LS pers (OptEIdxs out1) m lst x) (hout : absEIdxL out1 = absEIdxL out ++ [y]) :
    LS pers (OptEIdxs out) m lst (do
      match ← x with
      | none => pure none
      | some rest => pure (some (y :: rest))) := by
  have h2 := LS.twin_map (R := OptEIdxs out) (f := Option.map (y :: ·)) h (by
    intro a b h1
    simp only [OptEIdxs] at h1 ⊢
    rw [h1, hout]
    cases b <;> simp)
  refine LS.twin_eq h2 ?_
  congr 1
  funext r
  cases r <;> rfl

attribute [local lockstep_inline] arena.inductives.gen_rec.rule_call

/-- The port's guarded kind read `if i < len then ks[i] else Ordinary`, as one
value. -/
theorem gr_kind_read {γ : Type} (ks : alloc.vec.Vec arena.inductives.gen_rec.ClassField)
    (i : Std.U64) (M : arena.inductives.gen_rec.ClassField → Result γ) :
    (do
      let i2 ← lift (UScalar.cast .U64 (alloc.vec.Vec.len ks))
      let k ← if i < i2 then do
          let i3 ← lift (UScalar.cast .Usize i)
          let cf ← alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice
            arena.inductives.gen_rec.ClassField) ks i3
          arena.inductives.gen_rec.class_field_dup cf
        else ok arena.inductives.gen_rec.ClassField.Ordinary
      M k) =
    M (if h : i.val < ks.val.length then ks.val[i.val] else .Ordinary) := by
  have hl : (UScalar.cast .U64 (alloc.vec.Vec.len ks)).val = ks.val.length := by
    rw [ConRon.Refine.ExprOps.usize_cast_u64_val]; rfl
  simp only [lift, bind_tc_ok]
  by_cases h : i.val < ks.val.length
  · rw [if_pos (by scalar_tac), dif_pos h]
    have hc : (UScalar.cast .Usize i).val = i.val :=
      ConRon.Refine.ExprOps.u64_cast_usize_val (by have := ks.property; scalar_tac)
    have hidx : alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice
        arena.inductives.gen_rec.ClassField) ks (UScalar.cast .Usize i) = ok ks.val[i.val] := by
      rw [alloc.vec.Vec.index_slice_index, alloc.vec.Vec.index_usize]
      rw [show ks[(UScalar.cast .Usize i).val]? = ks.val[(UScalar.cast .Usize i).val]? from rfl,
        hc, List.getElem?_eq_getElem h]
    rw [hidx, bind_tc_ok]
    cases hk : ks.val[i.val] <;> simp [arena.inductives.gen_rec.class_field_dup]
  · rw [if_neg (by scalar_tac), dif_neg h, bind_tc_ok]

theorem rule_calls_acc {pers} (g : arena.inductives.gen_rec.ClassGen) (hbm : ConRon.Refine.PropWhenWF g.bm.pw)
    (rec_cls : alloc.vec.Vec Std.U64) (cv_gs : alloc.vec.Vec arena.env.IConstantVal)
    (rlvls : arena.handle.LsIdx) (x : arena.inductives.gen_rec.ClassCtor) (r_p : Std.U64)
    (fvs ws pvars : alloc.vec.Vec arena.handle.EIdx) :
    ∀ (m : Nat) (i : Std.U64) (out : alloc.vec.Vec arena.handle.EIdx) st lst,
      x.n_f.val - i.val = m → AStateRel₀ pers st lst → AStateInv pers st →
      LS pers (OptEIdxs out)
        (arena.inductives.gen_rec.rule_calls pers st g rec_cls cv_gs rlvls x r_p fvs ws pvars i out)
        lst
        (classGenRule.callsGo (absClassGen g) (absNatL rec_cls) (cv_gs.val.map absIConstantVal)
          (absLsIdx rlvls) (absClassCtor x) (absU r_p) (absEIdxL fvs) (absEIdxL ws)
          (absEIdxL pvars) m i.val) := by
  intro m
  induction m with
  | zero =>
    intro i out st lst hm hrel hinv
    rw [arena.inductives.gen_rec.rule_calls.eq_def, if_pos (by scalar_tac), classGenRule.callsGo]
    exact LS.pure (by simp [OptEIdxs]) hrel hinv
  | succ m ih =>
    intro i out st lst hm hrel hinv
    rw [arena.inductives.gen_rec.rule_calls.eq_def, if_neg (by scalar_tac), classGenRule.callsGo]
    rw [gr_kind_read]
    by_cases hik : i.val < x.kinds.val.length
    · have htw : (List.map absClassField x.kinds.val).getD i.val .ordinary =
          absClassField (x.kinds.val[i.val]'hik) := by
        simp [List.getD_eq_getElem?_getD, hik]
      simp only [absClassCtor_kinds, htw, dif_pos hik]
      generalize x.kinds.val[i.val]'hik = k
      cases k <;> simp only [absClassField]
      all_goals lockstep
      rename_i call out1 hout1
      have hjv : a.val = i.val + 1 := by simpa using hP
      have h1 := ih a out1 _ _ (by omega) ‹_› ‹_›
      rw [hjv] at h1
      refine ls_tail_opt_cons_e h1 ?_
      simp [absEIdxL, hout1]
    · have htw : (List.map absClassField x.kinds.val).getD i.val .ordinary = .ordinary := by
        simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (Nat.le_of_not_lt hik)]
      simp only [absClassCtor_kinds, htw, dif_neg hik]
      lockstep

/-- `rule_calls` from field `0` into `Vec::new()` ⊑ `classGenRule.callsGo … nF 0`. -/
@[lockstep] theorem rule_calls_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (g : arena.inductives.gen_rec.ClassGen)
    (hbm : ConRon.Refine.PropWhenWF g.bm.pw)
    (rec_cls : alloc.vec.Vec Std.U64) (cv_gs : alloc.vec.Vec arena.env.IConstantVal)
    (rlvls : arena.handle.LsIdx) (x : arena.inductives.gen_rec.ClassCtor) (r_p : Std.U64)
    (fvs ws pvars : alloc.vec.Vec arena.handle.EIdx) :
    LS pers (fun a b => b = a.map absEIdxL)
      (arena.inductives.gen_rec.rule_calls pers st g rec_cls cv_gs rlvls x r_p fvs ws pvars 0#u64
        (alloc.vec.Vec.new _)) lst
      (classGenRule.callsGo (absClassGen g) (absNatL rec_cls) (cv_gs.val.map absIConstantVal)
        (absLsIdx rlvls) (absClassCtor x) (absU r_p) (absEIdxL fvs) (absEIdxL ws)
        (absEIdxL pvars) (absU x.n_f) 0) := by
  have h := rule_calls_acc g hbm rec_cls cv_gs rlvls x r_p fvs ws pvars _ 0#u64
    (alloc.vec.Vec.new _) st lst rfl hrel hinv
  refine LS.tail h (by simp [absU]) ?_
  intro a b h1
  simp only [OptEIdxs] at h1
  rw [h1]
  cases b <;> simp [absEIdxL, alloc.vec.Vec.new]

/-- `class_gen_rule_close` ⊑ `grRuleClose` (`classGenRule`'s tail). -/
@[lockstep] theorem class_gen_rule_close_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (g : arena.inductives.gen_rec.ClassGen) (hg : ClassGenWF g)
    (s : Std.U64) (fvs ihs : alloc.vec.Vec arena.handle.EIdx) :
    LS pers (fun a b => b = a.map absEIdx)
      (arena.inductives.gen_rec.class_gen_rule_close pers st g s fvs ihs) lst
      (grRuleClose (absClassGen g) (absU s) (absEIdxL fvs) (absEIdxL ihs)) := by
  have hbm := hg.bm
  have hpre := hg.pre
  rw [arena.inductives.gen_rec.class_gen_rule_close, grRuleClose]
  lockstep

/-! ## `class_gen_rule` ⊑ `classGenRule`

The twin's slot test is a `match`-lambda; `classGenRule'` is the same `def`
with it named (`grMinorIs`), the prefix variable named (`grPVar`) and the tail
named (`grRuleClose`) — equal by `rfl`. -/

def classGenRule' (g : ClassGen) (recCls : List Nat) (cvGs : List IConstantVal)
    (rlvls : LsIdx) (c : Nat) (x : ClassCtor) : AM (Option EIdx) := do
  let rP := g.pre.length
  let hit := ((List.range g.slots.length).zip g.slots).find? (grMinorIs c x.cv.name)
  match hit with
  | none => pure none
  | some (s, _) =>
    match ← openPisAtFvarsF x.nF x.tyD rP with
    | none => pure none
    | some (fvs, _) =>
      match ← targetPiDomsWith fvs x.tyN with
      | none => pure none
      | some ws => do
        let pvars ← (List.range rP).mapM (grPVar g)
        match ← classGenRule.callsGo g recCls cvGs rlvls x rP fvs ws pvars x.nF 0 with
        | none => pure none
        | some ihs => grRuleClose g s fvs ihs

theorem classGenRule_eq : classGenRule = classGenRule' := by
  funext g recCls cvGs rlvls c x
  simp only [classGenRule, classGenRule', grRuleClose]
  congr 1
  · congr 1; funext p; rcases p with ⟨_, _ | _⟩ <;> rfl

@[lockstep] theorem class_gen_rule_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (g : arena.inductives.gen_rec.ClassGen) (hg : ClassGenWF g)
    (rec_cls : alloc.vec.Vec Std.U64) (cv_gs : alloc.vec.Vec arena.env.IConstantVal)
    (rlvls : arena.handle.LsIdx) (c : Std.U64) (x : arena.inductives.gen_rec.ClassCtor) :
    LS pers (fun a b => b = a.map absEIdx)
      (arena.inductives.gen_rec.class_gen_rule pers st g rec_cls cv_gs rlvls c x) lst
      (classGenRule (absClassGen g) (absNatL rec_cls) (cv_gs.val.map absIConstantVal)
        (absLsIdx rlvls) (absU c) (absClassCtor x)) := by
  have hbm := hg.bm
  rw [arena.inductives.gen_rec.class_gen_rule, classGenRule_eq, classGenRule']
  lockstep

end ConRon.Refine2
