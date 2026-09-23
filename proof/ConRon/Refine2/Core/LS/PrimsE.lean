/-
# `ConRon.Refine2.Core.LS.PrimsE` — region E's primitive pairs (the inference bodies)

Task #97-P5-Core round 5, region E.  The `@[lockstep]` pairs the inference
bodies (`infer_body`, `infer_body_io`) and their loops (`infer_lams`,
`infer_pis`, `infer_spine`, `infer_spine_io`) step through that no earlier
file provides: the two binder stacks' abstractions, the level-list length and
the `const` projection, the memoised readbacks, the Rust-only value steps on
binder data, the two pins, and the pending intern prims.
-/
import ConRon.Refine2.Core.LS.Prims

open Aeneas Aeneas.Std Result
open ConRon.Generated

attribute [-grind] U32.bv_eq_imp_eq UScalar.val_eq_imp

namespace ConRon.Refine2.Lockstep.PE

open ConRon.Arena ConRon.Refine2 ConRon.Refine2.Lockstep

/-! ## Abstractions -/

/-- The λ loop's binder stack (`Vec<(EIdx, BinderMeta)>`, pushed outermost
first) as the twin's `Array (EIdx × BinderMeta)`. -/
def absLamStk (v : alloc.vec.Vec (arena.handle.EIdx × kernel.expr.BinderMeta)) :
    Array (EIdx × ConLeche.BinderMeta) :=
  (v.val.map fun p => (absEIdx p.1, ConRon.Refine.absBinderMeta p.2)).toArray

/-- The ∀ loop's sort stack (`Vec<(LIdx, PropWhen)>`) as the twin's
`Array (LIdx × PropWhen)`. -/
def absPiStk (v : alloc.vec.Vec (arena.handle.LIdx × kernel.prop_when.PropWhen)) :
    Array (LIdx × ConLeche.PropWhen) :=
  (v.val.map fun p => (absLIdx p.1, ConRon.Refine.absPropWhen p.2)).toArray

@[lockstep_simp] theorem absLamStk_size
    (v : alloc.vec.Vec (arena.handle.EIdx × kernel.expr.BinderMeta)) :
    (absLamStk v).size = v.val.length := by
  simp [absLamStk]

@[lockstep_simp] theorem absPiStk_size
    (v : alloc.vec.Vec (arena.handle.LIdx × kernel.prop_when.PropWhen)) :
    (absPiStk v).size = v.val.length := by
  simp [absPiStk]

theorem absLamStk_push (v w : alloc.vec.Vec (arena.handle.EIdx × kernel.expr.BinderMeta)) (x)
    (h : w.val = v.val ++ [x]) :
    absLamStk w = (absLamStk v).push (absEIdx x.1, ConRon.Refine.absBinderMeta x.2) := by
  simp [absLamStk, h]

theorem absPiStk_push (v w : alloc.vec.Vec (arena.handle.LIdx × kernel.prop_when.PropWhen)) (x)
    (h : w.val = v.val ++ [x]) :
    absPiStk w = (absPiStk v).push (absLIdx x.1, ConRon.Refine.absPropWhen x.2) := by
  simp [absPiStk, h]

theorem absEIdxArr_push (v w : alloc.vec.Vec arena.handle.EIdx) (x)
    (h : w.val = v.val ++ [x]) :
    absEIdxArr w = (absEIdxArr v).push (absEIdx x) := by
  simp [absEIdxArr, h]

@[lockstep_simp] theorem vec_len_abs {α : Type} (v : alloc.vec.Vec α) :
    absSz (alloc.vec.Vec.len v) = v.val.length := by
  simp [absSz]

@[lockstep_simp] theorem absEIdxArr_new :
    absEIdxArr (alloc.vec.Vec.new arena.handle.EIdx) = #[] := rfl

@[lockstep_simp] theorem absLamStk_new :
    absLamStk (alloc.vec.Vec.new (arena.handle.EIdx × kernel.expr.BinderMeta)) = #[] := rfl

@[lockstep_simp] theorem absPiStk_new :
    absPiStk (alloc.vec.Vec.new (arena.handle.LIdx × kernel.prop_when.PropWhen)) = #[] := rfl

attribute [lockstep_simp] ConRon.Refine.absBinderMeta absConstT
attribute [simp] absLamStk absPiStk


@[lockstep_simp] theorem peel_fuel_abs : absU arena.core.PEEL_FUEL = peelFuel := by
  rw [arena.core.PEEL_FUEL, Arena.peelFuel]
  rfl

/-! ## The io view of the lane knot

`laneKnotAt … io f` is `laneKnot … f` with (under `io`) its `infer` slot
rebound to `inferIO`; every other slot is the lane knot's own, by iota. -/

@[lockstep_simp] theorem laneKnotAt_whnf (m fe l io f) :
    (laneKnotAt m fe l io f).whnf = (laneKnot m fe l f).whnf := by cases io <;> rfl
@[lockstep_simp] theorem laneKnotAt_whnfCore (m fe l io f) :
    (laneKnotAt m fe l io f).whnfCore = (laneKnot m fe l f).whnfCore := by cases io <;> rfl
@[lockstep_simp] theorem laneKnotAt_defeq (m fe l io f) :
    (laneKnotAt m fe l io f).defeq = (laneKnot m fe l f).defeq := by cases io <;> rfl
@[lockstep_simp] theorem laneKnotAt_inferIO (m fe l io f) :
    (laneKnotAt m fe l io f).inferIO = (laneKnot m fe l f).inferIO := by cases io <;> rfl
@[lockstep_simp] theorem laneKnotAt_annotate (m fe l io f) :
    (laneKnotAt m fe l io f).annotate = (laneKnot m fe l f).annotate := by cases io <;> rfl

/-- `ensureSort` reads its record's `whnf` slot alone. -/
@[lockstep_simp] theorem ensureSort_laneKnotAt (m fe l io f lfe d e) :
    ensureSort (laneKnotAt m fe l io f) lfe d e = ensureSort (laneKnot m fe l f) lfe d e := by
  cases io <;> rfl

/-- `!=` is `!(==)`, so the tag tests `t.tag != ETag.lam` reduce with the
`absU32_beq_*` equations. -/
@[lockstep_simp] theorem bne_eq_not_beq' {α : Type} [BEq α] (a b : α) : (a != b) = !(a == b) := rfl

attribute [lockstep_simp] Bool.not_eq_true' decide_eq_false_iff_not not_not

/-- The port's `if t != ETAG_LAM` as a proposition, both polarities. -/
@[lockstep_simp] theorem u32_bne_true (a b : Std.U32) : ((a != b) = true) = ¬ a = b := by
  by_cases h : a = b <;> simp [h]
@[lockstep_simp] theorem u32_not_bne_true (a b : Std.U32) : (¬ (a != b) = true) = (a = b) := by
  by_cases h : a = b <;> simp [h]

/-- The port's `u32` `==` is `decide`, the shape the `absU32_beq_*` equations
leave on the twin side. -/
@[lockstep_simp] theorem u32_beq_decide (a b : Std.U32) : (a == b) = decide (a = b) := by
  by_cases h : a = b <;> simp [h]

/-! ## Rust-only value steps -/

@[lockstep] theorem verified_checks_ls (m : kernel.env.CheckMode) :
    LSP (kernel.env.verified_checks m)
      (fun b => b = (ConRon.Refine.absMode m).verifiedChecks) :=
  by
  intro b h
  cases m <;> (simp only [kernel.env.verified_checks, Result.ok.injEq] at h; rw [← h]; rfl)

@[lockstep] theorem io_skip_ls (m : kernel.env.CheckMode) (pw : kernel.prop_when.PropWhen) :
    LSP (kernel.env.io_skip m pw)
      (fun b => b = (ConRon.Refine.absMode m).ioSkip (ConRon.Refine.absPropWhen pw)) :=
  by
  intro b h
  cases m
  · simp only [kernel.env.io_skip, kernel.env.certs, bind_tc_ok, reduceIte] at h
    rw [ConRon.Refine.PropWhen.is_never_refines h]; rfl
  · simp only [kernel.env.io_skip, kernel.env.certs, bind_tc_ok, Bool.false_eq_true, if_false,
      Result.ok.injEq] at h
    rw [← h]; rfl

/-- The twin's `(if c then a else b) >>= g`, pushed into the branches so that
the twin test sits at the head where `lockstep` decides it. -/
theorem twin_ite_bind {α β : Type} {c : Prop} [Decidable c] (a b : AM α) (g : α → AM β) :
    ((if c then a else b) >>= g) = (if c then a >>= g else b >>= g) := by
  split <;> rfl


/-! ## Well-formedness carried by a read

`prop_when::beq` is the twin's `==` on the abstraction only at two
canonical-form data (`PropWhenWF`; `One p` and `Two (p, p)` abstract alike and
compare unequal).  Every datum the inference loops compare comes out of the
Rust store (`bms`' `TblInv`, part of `AStateInv`) or out of `zeroness_of`, so
the reads below carry that representation fact beside the abstraction.  They
are used as LOCAL hypotheses (`have := …`), which `specCore` tries before the
registered `view_bind_ls` / `view_ls` / `lam_pw_ls`. -/

/-- The binder datum of a `view_bind` answer is well formed. -/
def optBindWF : Option (arena.handle.EIdx × arena.handle.EIdx × kernel.expr.BinderMeta) → Prop
  | some (_, _, m) => ConRon.Refine.PropWhenWF m.pw
  | none => True

/-- The binder datum of a `view` answer is well formed. -/
def viewWF : arena.store.ENodeView → Prop
  | .Lam _ _ m => ConRon.Refine.PropWhenWF m.pw
  | .ForallE _ _ m => ConRon.Refine.PropWhenWF m.pw
  | _ => True

/-- A `lam_pw` answer is well formed. -/
def optPwWF : Option kernel.prop_when.PropWhen → Prop
  | some p => ConRon.Refine.PropWhenWF p
  | none => True

attribute [lockstep_simp] optBindWF viewWF optPwWF ExprOps.absPwOpt

theorem view_bind_wf_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (h : arena.handle.EIdx)
    (hbind : ETag.isBind (absEIdx h).tag = true) :
    LSV pers (fun a b => optBindWF a ∧ b = Option.map absBindM a)
      (arena.monad.view_bind pers st h) st lst (Arena.viewBind (absEIdx h)) := by
  sorry

theorem view_wf_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (h : arena.handle.EIdx) :
    LSR pers (fun a b => viewWF a ∧ b = absENodeView a) (arena.monad.view pers st h) st lst
      (Arena.view (absEIdx h)) := by
  sorry

theorem lam_pw_wf_ls {pers} (hx : ExprOpsHyp pers) {st lst}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) (h) :
    LSR pers (fun a b => optPwWF a ∧ b = ExprOps.absPwOpt a) (arena.expr_ops.lam_pw pers st h)
      st lst (lamPw (absEIdx h)) := by
  sorry

theorem lam_stk_push_wf {stk stk1 : alloc.vec.Vec (arena.handle.EIdx × kernel.expr.BinderMeta)}
    {x : arena.handle.EIdx × kernel.expr.BinderMeta} (h : stk1.val = stk.val ++ [x])
    (hs : ∀ p ∈ stk.val, ConRon.Refine.PropWhenWF p.2.pw) (hx : ConRon.Refine.PropWhenWF x.2.pw) :
    ∀ p ∈ stk1.val, ConRon.Refine.PropWhenWF p.2.pw := by
  intro p hp
  rw [h, List.mem_append, List.mem_singleton] at hp
  rcases hp with hp | rfl
  · exact hs p hp
  · exact hx

theorem pi_stk_push_wf {stk stk1 : alloc.vec.Vec (arena.handle.LIdx × kernel.prop_when.PropWhen)}
    {x : arena.handle.LIdx × kernel.prop_when.PropWhen} (h : stk1.val = stk.val ++ [x])
    (hs : ∀ p ∈ stk.val, ConRon.Refine.PropWhenWF p.2) (hx : ConRon.Refine.PropWhenWF x.2) :
    ∀ p ∈ stk1.val, ConRon.Refine.PropWhenWF p.2 := by
  intro p hp
  rw [h, List.mem_append, List.mem_singleton] at hp
  rcases hp with hp | rfl
  · exact hs p hp
  · exact hx

/-! ## Reads -/

@[lockstep] theorem view_ls_len_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (h : arena.handle.LsIdx) :
    LSV pers (fun a b => b = Option.map absSz a) (arena.monad.view_ls_len pers st h) st lst
      (Arena.viewLsLen (absLsIdx h)) := by
  intro o hrun
  exact ⟨_, lst, view_ls_len_run₀ hrel hrun, rfl, hrel, hinv⟩

@[lockstep] theorem view_const_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (h : arena.handle.EIdx) :
    LSV pers (fun a b => b = Option.map absConstT a) (arena.monad.view_const pers st h) st lst
      (Arena.viewConst (absEIdx h)) := by
  intro o hrun
  exact ⟨_, lst, view_const_run₀ hrel hrun, rfl, hrel, hinv⟩

/-- The memoised level readback; the tree it answers is well formed. -/
@[lockstep] theorem read_level_m_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (h : arena.handle.LIdx) :
    LS pers (fun a b => ConRon.Refine.LevelWF a ∧ b = ConRon.Refine.absLevel a)
      (arena.monad.read_level_m pers st h) lst (Arena.readLevelM (absLIdx h)) := by
  sorry

@[lockstep] theorem read_levels_m_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (h : arena.handle.LsIdx) :
    LS pers (fun a b => ConRon.Refine.LevelsWF a ∧ b = ConRon.Refine.absLevels a)
      (arena.monad.read_levels_m pers st h) lst (Arena.readLevelsM (absLsIdx h)) := by
  sorry

@[lockstep] theorem read_names_m_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (ks : alloc.vec.Vec arena.handle.NIdx) :
    LS pers (fun a b => ConRon.Refine.NamesWF a ∧ b = ConRon.Refine.absNames a)
      (arena.monad.read_names_m pers st ks) lst (Arena.readNamesM (ks.val.map absNIdx)) := by
  sorry

/-! ## Rust-only steps on levels and data -/

@[lockstep] theorem zeroness_of_ls {l : kernel.level.Level} (hl : ConRon.Refine.LevelWF l) :
    LSP (kernel.level.zeroness_of l) (fun pw => ConRon.Refine.PropWhenWF pw ∧
      ConRon.Refine.absPropWhen pw = ConLeche.Level.zeronessOf (ConRon.Refine.absLevel l)) := by
  intro pw h
  have := ConRon.Refine.ExprOps.zeroness_of_refines hl pw h
  exact ⟨this.2, this.1⟩

theorem absLamStk_getElem! (v : alloc.vec.Vec (arena.handle.EIdx × kernel.expr.BinderMeta))
    (i : Nat) (h : i < v.val.length) :
    (absLamStk v)[i]! = (absEIdx (v.val[i]).1, ConRon.Refine.absBinderMeta (v.val[i]).2) := by
  rw [getElem!_pos (absLamStk v) i (by simpa [absLamStk] using h)]
  simp [absLamStk]

/-- `prop_when::beq` against a λ-stack entry: the answer in the twin's own
spelling, `(absLamStk stk)[i]!`.  Filed before the general pair, which it
specialises. -/
@[lockstep] theorem prop_when_beq_stk_ls
    {stk : alloc.vec.Vec (arena.handle.EIdx × kernel.expr.BinderMeta)}
    (hstk : ∀ p ∈ stk.val, ConRon.Refine.PropWhenWF p.2.pw)
    {a : kernel.prop_when.PropWhen} (ha : ConRon.Refine.PropWhenWF a) (i : Nat)
    (hi : i < stk.val.length) :
    LSP (kernel.prop_when.beq a (stk.val[i]).2.pw)
      (fun c => c = (ConRon.Refine.absPropWhen a == ((absLamStk stk)[i]!).2.pw)) := by
  intro c h
  have := ConRon.Refine.PropWhen.beq_iff (ConRon.Refine.PropWhen.wf_shape ha)
    (ConRon.Refine.PropWhen.wf_shape (hstk _ (List.getElem_mem hi))) h
  rw [absLamStk_getElem! stk i hi]
  cases c <;> simp_all [ConRon.Refine.absBinderMeta]

/-- The same, with the stack entry on the left. -/
@[lockstep] theorem prop_when_beq_stk_left_ls
    {stk : alloc.vec.Vec (arena.handle.EIdx × kernel.expr.BinderMeta)}
    (hstk : ∀ p ∈ stk.val, ConRon.Refine.PropWhenWF p.2.pw)
    {b : kernel.prop_when.PropWhen} (hb : ConRon.Refine.PropWhenWF b) (i : Nat)
    (hi : i < stk.val.length) :
    LSP (kernel.prop_when.beq (stk.val[i]).2.pw b)
      (fun c => c = (((absLamStk stk)[i]!).2.pw == ConRon.Refine.absPropWhen b)) := by
  intro c h
  have := ConRon.Refine.PropWhen.beq_iff
    (ConRon.Refine.PropWhen.wf_shape (hstk _ (List.getElem_mem hi)))
    (ConRon.Refine.PropWhen.wf_shape hb) h
  rw [absLamStk_getElem! stk i hi]
  cases c <;> simp_all [ConRon.Refine.absBinderMeta]

@[lockstep] theorem prop_when_beq_ls {a b : kernel.prop_when.PropWhen}
    (ha : ConRon.Refine.PropWhenWF a) (hb : ConRon.Refine.PropWhenWF b) :
    LSP (kernel.prop_when.beq a b)
      (fun c => c = (ConRon.Refine.absPropWhen a == ConRon.Refine.absPropWhen b)) := by
  intro c h
  have := ConRon.Refine.PropWhen.beq_iff (ConRon.Refine.PropWhen.wf_shape ha)
    (ConRon.Refine.PropWhen.wf_shape hb) h
  cases c <;> simp_all

@[lockstep] theorem prop_when_never_ls :
    LSP kernel.prop_when.never (fun pw => ConRon.Refine.PropWhenWF pw ∧
      ConRon.Refine.absPropWhen pw = ConLeche.PropWhen.never) :=
  fun _ h => ⟨ConRon.Refine.PropWhen.never_wf h, ConRon.Refine.PropWhen.never_refines h⟩

/-- The λ loop's `let (_, bm) = stk[j]; bm.pw.dup()`, with the `dup` (the
identity) dropped, so that the index step's answer feeds a plain projection. -/
theorem stk_index_pw_eq (stk : alloc.vec.Vec (arena.handle.EIdx × kernel.expr.BinderMeta))
    (j : Std.Usize) :
    (do
      let (_, bm) ← alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice
        (arena.handle.EIdx × kernel.expr.BinderMeta)) stk j
      kernel.prop_when.dup bm.pw) =
    (do
      let e ← alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice
        (arena.handle.EIdx × kernel.expr.BinderMeta)) stk j
      ok e.2.pw) := by
  congr 1
  funext e
  obtain ⟨_, bm⟩ := e
  exact ConRon.Refine.PropWhen.dup_eq' _

theorem absLamStk_last_pw (v : alloc.vec.Vec (arena.handle.EIdx × kernel.expr.BinderMeta))
    (i : Nat) (h : i < v.val.length) (hi : i = v.val.length - 1) :
    ((absLamStk v)[v.val.length - 1]!).2.pw = ConRon.Refine.absPropWhen (v.val[i]).2.pw := by
  subst hi; rw [absLamStk_getElem! v _ h]; rfl

@[lockstep] theorem prop_when_dup_ls (pw : kernel.prop_when.PropWhen) :
    LSP (kernel.prop_when.dup pw) (fun r => r = pw) :=
  fun _ h => ConRon.Refine.PropWhen.dup_eq h

@[lockstep] theorem binder_meta_dup_ls (m : kernel.expr.BinderMeta) :
    LSP (kernel.expr.binder_meta_dup m) (fun r => r = m) :=
  fun _ h => ConRon.Refine.Expr.binder_meta_dup_eq h

@[lockstep] theorem lidx_dup2_ls (h : arena.handle.LIdx) :
    LSP (arena.handle.LIdx.Insts.Con_ron_coreRonHashmapDup.dup2 h) (fun e => e = h) :=
  fun e he => dupId_lidx _ _ he

/-! ## The environment -/

/-- A projection-table entry, field for field (regions A2 and G spell the
same function). -/
def absIProjEntry (e : arena.env.IProjEntry) : IProjEntry :=
  ⟨absNIdx e.struct_name, absU e.idx, e.level_params.val.map absNIdx, absU e.num_params,
    absNIdx e.ctor, absU e.num_fields, absEIdx e.body, absLIdx e.field_sort,
    absLIdx e.struct_sort, absU e.off⟩

@[lockstep] theorem i_constant_info_is_tower_entry_ls (ci : arena.env.IConstantInfo) :
    LSP (arena.env.i_constant_info_is_tower_entry ci)
      (fun b => b = (absIConstantInfo ci).isTowerEntry) := by
  intro b h
  cases ci <;> simp only [arena.env.i_constant_info_is_tower_entry, Result.ok.injEq] at h <;>
    subst h <;> rfl

/-- `i_constant_info_to_constant_val` against `IConstantInfo.toConstantVal`, a
store-level step.  The `ProjInfo` arm interns `Sort 1`. -/
@[lockstep] theorem i_constant_info_to_constant_val_ls {pers st lst}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) (ci : arena.env.IConstantInfo) :
    LSS pers (fun a b => b = absIConstantVal a)
      (arena.env.i_constant_info_to_constant_val pers st.store ci) st lst
      (absIConstantInfo ci).toConstantVal := by
  -- PENDING foundation intern slice (T2-LOCKSTEP slice 3)
  sorry

/-- `ifenv_find_proj` against `IFEnv.findProj?`, a store-level step: it
interns the reserved table name. -/
@[lockstep] theorem ifenv_find_proj_ls {pers vis st lst fe lfe}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) (hctx : CoreCtx vis fe lfe)
    (t : arena.handle.NIdx) (i : Std.U64) :
    LSS pers (fun a b => b = Option.map absIProjEntry a)
      (arena.env.ifenv_find_proj pers vis st.store fe t i) st lst
      (lfe.findProj? (absNIdx t) (absU i)) := by
  -- PENDING foundation intern slice (T2-LOCKSTEP slice 3)
  sorry

/-! ## The two pins -/

@[lockstep] theorem pin_nat_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LSR pers (fun a b => b = absNIdx a) (arena.pins.pin_nat st) st lst pinNat := by
  sorry

@[lockstep] theorem pin_string_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LSR pers (fun a b => b = absNIdx a) (arena.pins.pin_string st) st lst pinString := by
  sorry

/-! ## Levels (the propositional-structure check of the `.proj` clause) -/

@[lockstep] theorem level_zero_ls :
    LSP kernel.level.zero (fun u => ConRon.Refine.LevelWF u ∧
      ConRon.Refine.absLevel u = ConLeche.Level.zero) :=
  fun _ h => ⟨ConRon.Refine.Level.zero_wf h, ConRon.Refine.Level.zero_refines h⟩

@[lockstep] theorem level_subst_ls {ks : alloc.vec.Vec kernel.name.Name}
    {vs : alloc.vec.Vec kernel.level.Level} {u : kernel.level.Level}
    (hks : ConRon.Refine.NamesWF ks) (hvs : ConRon.Refine.LevelsWF vs)
    (hu : ConRon.Refine.LevelWF u) :
    LSP (kernel.level.subst ks vs u) (fun u' => ConRon.Refine.LevelWF u' ∧
      ConRon.Refine.absLevel u' = ConLeche.Level.subst (ConRon.Refine.absNames ks)
        (ConRon.Refine.absLevels vs) (ConRon.Refine.absLevel u)) := by
  intro u' h
  have := ConRon.Refine.Level.subst_refines hu hks hvs h
  exact ⟨this.2, this.1⟩

@[lockstep] theorem level_is_equiv_ls {l r : kernel.level.Level}
    (hl : ConRon.Refine.LevelWF l) (hr : ConRon.Refine.LevelWF r) :
    LSP (kernel.level.is_equiv l r) (fun o =>
      ConLeche.Level.isEquiv (ConRon.Refine.absLevel l) (ConRon.Refine.absLevel r) = o) :=
  fun _ h => ConRon.Refine.Level.is_equiv_refines hl hr h

/-! ## Handles and scalars -/

@[lockstep] theorem nidx_eq2_ls (a b : arena.handle.NIdx) :
    LSP (arena.handle.NIdx.Insts.Con_ron_coreRonHashmapEq2.eq2 a b)
      (fun c => c = decide (absNIdx a = absNIdx b)) := by
  intro c h
  rw [arena.handle.NIdx.Insts.Con_ron_coreRonHashmapEq2.eq2] at h
  cases Result.ok_injective h
  by_cases hab : a.word = b.word
  · have : absNIdx a = absNIdx b := by simp [absNIdx, hab]
    simp [hab, this]
  · have : absNIdx a ≠ absNIdx b := fun he => hab (by
      have := absNIdx_inj he; rw [this])
    simp [hab, this]

@[lockstep] theorem usize_cast_u64_ls (x : Std.Usize) :
    LSP (lift (Std.UScalar.cast .U64 x)) (fun r : Std.U64 => r.val = x.val) := by
  intro r h
  cases Result.ok_injective h
  exact usize_cast_u64_val' x

@[lockstep] theorem fail_dangling_ls_ls (T : Type) :
    LSP (arena.monad.fail_dangling_ls T) (fun r => ∃ v, r = .Err (.Internal v)) := by
  intro r h
  rw [arena.monad.fail_dangling_ls] at h
  obtain ⟨s, _, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨v, _, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  exact ⟨v, fail_run h⟩

@[lockstep_simp] theorem failDanglingLs_eq {α : Type} :
    (failDanglingLs : AM α) = Arena.fail (.internal "arena: dangling level-list handle") := rfl

@[lockstep_simp] theorem usize_bne_true (a b : Std.Usize) : ((a != b) = true) = ¬ a.val = b.val := by
  by_cases h : a = b
  · simp [h]
  · have : a.val ≠ b.val := fun hv => h (Std.UScalar.eq_of_val_eq hv)
    simp [h, this]
@[lockstep_simp] theorem usize_not_bne_true (a b : Std.Usize) :
    (¬ (a != b) = true) = (a.val = b.val) := by
  rw [usize_bne_true]; simp

attribute [lockstep_simp] absIProjEntry absIConstantVal List.length_map ExprOps.absEIdxList

@[lockstep_simp] theorem vec_len_val' {α : Type} (v : alloc.vec.Vec α) :
    (alloc.vec.Vec.len v).val = v.val.length := by
  simp [alloc.vec.Vec.len_val]

@[lockstep_simp] theorem opt_beq_some_true (o : Option Bool) :
    ((o == some true) = true) = (o = some true) := by
  cases o with
  | none => simp
  | some b => cases b <;> simp
@[lockstep_simp] theorem opt_beq_some_false (o : Option Bool) :
    ((o == some true) = false) = ¬ (o = some true) := by
  cases o with
  | none => simp
  | some b => cases b <;> simp

attribute [lockstep_simp] Option.some.injEq reduceCtorEq

@[lockstep_simp] theorem nat_beq_false (a b : Nat) : ((a == b) = false) = ¬ a = b := by
  by_cases h : a = b <;> simp [h]

/-- `viewLs` read only for its length is the length projection (the twin's
`inferBody` `.const` clause reads the whole list, the port and `inferBodyIO`
read `view_ls_len`; `Core/Arms/Delta.lean`'s `LsStore_viewLen_eq`). -/
def danglingLsOr {δ : Type} (k : Nat → AM δ) : Option Nat → AM δ
  | none => failDanglingLs
  | some n => k n

@[lockstep_simp] theorem danglingLsOr_none {δ : Type} (k : Nat → AM δ) :
    danglingLsOr k none = failDanglingLs := rfl
@[lockstep_simp] theorem danglingLsOr_some {δ : Type} (k : Nat → AM δ) (n : Nat) :
    danglingLsOr k (some n) = k n := rfl

@[lockstep_simp] theorem viewLs_length_bind {δ : Type} (h : LsIdx) (L : Nat) (A B : AM δ) :
    (viewLs h >>= fun usl => if ¬ List.length usl = L then A else B) =
      (viewLsLen h >>= danglingLsOr fun n => if ¬ n = L then A else B) := by
  funext lst
  show (viewLs h >>= _).run lst = (viewLsLen h >>= _).run lst
  rw [StateT.run_bind, StateT.run_bind]
  show (match lst.store.lss.view h with
      | some v => (pure v : AM LsNodeView)
      | none => Arena.fail (.internal "arena: dangling level-list handle")).run lst >>= _ =
    (pure (lst.store.lss.viewLen h) : AM (Option Nat)).run lst >>= _
  rw [LsStore_viewLen_eq]
  cases lst.store.lss.view h <;> rfl

/-! ## Interns — PENDING foundation intern slice (T2-LOCKSTEP slice 3) -/

@[lockstep] theorem intern_e_fvar_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (i : Std.U64) (ty : arena.handle.EIdx) :
    LS pers (fun a b => b = absEIdx a) (arena.monad.intern_e_fvar pers st i ty) lst
      (Arena.internFVarE (absU i) (absEIdx ty)) := by
  -- PENDING foundation intern slice (T2-LOCKSTEP slice 3)
  sorry

@[lockstep] theorem intern_e_sort_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (u : arena.handle.LIdx) :
    LS pers (fun a b => b = absEIdx a) (arena.monad.intern_e_sort pers st u) lst
      (Arena.internSortE (absLIdx u)) := by
  -- PENDING foundation intern slice (T2-LOCKSTEP slice 3)
  sorry

@[lockstep] theorem intern_l_node_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (v : arena.store.LNodeView) :
    LS pers (fun a b => b = absLIdx a) (arena.monad.intern_l_node pers st v) lst
      (Arena.internLNode (absLNodeView v)) := by
  -- PENDING foundation intern slice (T2-LOCKSTEP slice 3)
  sorry

/-! ## Local tactic moves (reported to the coordinator)

1. **`ok v >>= k` is NOT definitionally `k v`** for Aeneas's `Result` (an
   `ITree`; `bind_tc_ok` is proved by `simp`, not `rfl`).  `lockstep_core`'s
   `coreMove` feeds an `ok` to the continuation with `replaceTargetDefEq`,
   which does not check, and the kernel then rejects the proof ("application
   type mismatch").  `LS.rust_ok_bind` is the propositional step.
2. **An error arm through a pair-returning inner block**
   (`let (st1, cert) ← (match r with … | Err e1 => ok (st2, Err e1)); match
   cert with … | Err e1 => ok (Err e1, st1)`): `errArm` head-normalises only
   and cannot see through the inner `ok … >>= k'`.  `ls_state_bind` is
   `LS.bind` with the error arm closed by `simp`. -/

theorem LS.rust_ok_bind {γ α β : Type} {pers : arena.store.PersTier} {R : α → β → Prop}
    {v : γ} {k : γ → Result (core.result.Result α kernel.core_types.CheckError × arena.monad.AState)}
    {lst : AState} {x : AM β} (h : LS pers R (k v) lst x) :
    LS pers R (ok v >>= k) lst x := by
  rw [bind_tc_ok]; exact h

theorem LSP.rust_ok_bind {γ α : Type} {v : γ} {k : γ → Result α} {Q : α → Prop}
    (h : LSP (k v) Q) : LSP (ok v >>= k) Q := by
  rw [bind_tc_ok]; exact h

open Lean Meta Elab Tactic in
/-- Feed an `ok v` to the Rust continuation, propositionally. -/
elab "ls_ok_bind" : tactic => withMainContext do
  let g ← getMainGoal
  let others := (← getGoals).tail
  let ty ← instantiateMVars (← g.getType)
  let some rp := rustPos ty | throwError "ls_ok_bind: not a judgement"
  let m := (ty.getArg! rp).headBeta
  unless m.isAppOfArity ``Bind.bind 6 do throwError "ls_ok_bind: not a bind"
  let f ← headNorm (m.getArg! 4)
  unless f.isAppOfArity ``Result.ok 2 do throwError "ls_ok_bind: not an ok"
  let m' := mkAppN m.getAppFn (m.getAppArgs.set! 4 f)
  let g ← g.replaceTargetDefEq (mkAppN ty.getAppFn (ty.getAppArgs.set! rp m'))
  let gs ← applyRule g (if rp == 4 then ``LS.rust_ok_bind else ``LSP.rust_ok_bind)
  let g' ← pick gs `h
  setGoals ((← normAll [g']) ++ others)

open Lean Meta Elab Tactic in
/-- `LS.bind` with the error arm closed by `simp`. -/
elab "ls_state_bind" : tactic => withMainContext do
  let g ← getMainGoal
  let others := (← getGoals).tail
  let gs ← applyRule g ``LS.bind
  specCore (← pick gs `hf)
  runClosed (← pick gs `hx) (evalT `(tactic| lockstep_congr))
  runClosed (← pick gs `he) (evalT `(tactic| (
    intro e st1 o st' h
    simp at h
    first | exact h.1.symm | exact h.symm | (obtain ⟨rfl, -⟩ := h; rfl))))
  let rest ← cont (← pick gs `hk) [`a, `b, `st1, `lst1, `hR, `hrel, `hinv] (some `hR)
  setGoals ((← normAll rest) ++ others)

/-- `lockstep_core` with the two local moves. -/
macro "lockstep_e" : tactic =>
  `(tactic| repeat' (first
      | ls_ok_bind
      | lockstep_core_step
      | ls_state_bind
      | (apply LS.err; exact errSim_fail (by assumption))
      | (apply LS.err; exact errSim_throw (by assumption))))

end ConRon.Refine2.Lockstep.PE
