/-
# `kernel::inductives::sum_install` refined (task #57)

`CORE_PLAN.md` step 7.  The direct route's **shared former- and
constructor-stages** (`crates/con-ron-core/src/kernel/inductives/sum_install.rs`,
23 functions plus the `CapsOf` trait) against
`ConLeche/Kernel/Inductives/SumInstall.lean` and its index twin
`SumInstallF.lean`.  Task #25's deviation 1 is that the port has *one*
function per `Env`/index pair carrying both citations, so every statement whose
Lean has a `*F` twin is against that twin — the spelling the executable runs
and the one `Cached/CheckerC.lean`'s drivers call.  The five definitions with
no twin (`whnfTelescope`, `closeTelescope`, `normPosDom`, `normFieldDoms`,
`sumRules`) read the environment as an `Env` or as a `find?`, and are stated at
`absEnv fe.env` / `lfe.find?` respectively — which is exactly what the port
passes.

| group | items |
|---|---|
| the dictionary | `CapsOf` (`CapsOfRefines`, a hypothesis: `checkSumInd`'s `capsOf` argument is a one-method trait in the port) |
| the former's telescope | `whnf_telescope`, `close_telescope`, `check_sum_tele`, `check_sum_tele_whnf`, `check_sum_ind` |
| the fields' sorts | `exprs_contains`, `exprs_contains_from`, `check_struct_field_sorts_i` |
| the positivity walk as a normalisation | `norm_pos_dom`, `norm_field_doms`, `norm_ctor_val`, `zip_param_binders`(`_from`), `append_binders`(`_from`) |
| the constructors' stage | `opened_resid_ok`, `field_doms_resolve_from`, `index_args_resolve_from`, `check_sum_ctor`, `check_sum_ctors`, `cons_sum_ctors` |
| the stored rules | `sum_rules`, `sum_rules_from` |

## The deviations the statements had to absorb

* **`capsOf` is a dictionary, not a closure.**  `checkSumInd` takes
  `capsOf : InductiveShape → IndCaps`; §3.4 forbids closures, so the port has
  the one-method trait `sum_install::CapsOf` (task #9's pattern 1), whose one
  implementation is `native_install::NativeCapsAt`.  The parametricity is what
  con-leche's verification tier uses, so `check_sum_ind_refines` is
  **parametric in the dictionary**: it takes the dictionary's own refinement
  (`CapsOfRefines`) as a hypothesis and concludes against
  `checkSumIndF … capsOf` at the abstract function that hypothesis names.  The
  instance's discharge belongs to `Refine/IndNativeInstall.lean`.
* **Three accumulators are pushed on the way in** (task #13's pattern 3) where
  Lean conses on the way out: `whnf_telescope`, `norm_field_doms` and
  `check_sum_ctors`.  Each general statement therefore carries the accumulator
  in front (`absBinders out ++ lbs`), and the entry points are its empty
  reading.
* **`check_sum_tele_whnf` is a port-only split** of `checkSumTele`'s
  `| _ => do …` arm (task #18's pattern 3), so its statement is that cited
  `do` block spelled out.
* **`checkStructFieldSortsI`/`IF`/`IFA` are one function** in the port (one
  list type), so `check_struct_field_sorts_i_refines` is stated against the
  list spelling `checkStructFieldSortsIF`; con-leche's own
  `checkStructFieldSortsIFA_eq` is what carries it to the `Array` twin that
  `checkSumCtorF` calls.
* **`sumRules`' `find?` argument is the index itself** (`fe`), as everywhere
  in the port, and its two-list recursion is an index recursion whose "one
  list ran out" arm is the cited `| _, _ => []`.
* **One `u64 → usize` narrowing.** `opened_resid_ok` compares
  `getAppArgs.take nP` through `expr_ops::take_exprs`, which indexes by
  `usize`, so the port writes `n_p as usize` where con-leche's `List.take`
  takes a `Nat`.  `opened_resid_ok_refines` carries that as its one extra
  hypothesis `hnp : n_p.val ≤ Std.Usize.max` — vacuous wherever
  `Usize.numBits = 64`, which is the only platform the crate is built for,
  and the model cannot prove it because Aeneas's `Usize` is
  `System.Platform`-dependent.  It is the only place in this file where the
  port's word sizes are visible in a statement.

## What this file does not own

The knot is assumed (task #55 proves its arms): every state-touching lemma
takes `hw : Core.Wrappers mode IndAbs.checkFuelU` and reaches the operations
only through `IndAbs.ops_*`.  Eight facts belong to files this task may not
import, and travel as named `Prop` ingredients in the exact-result shape —
nothing is weakened:

| ingredient | owner |
|---|---|
| `CheckConstantValRefines`, `OpenPisAtFvarsFRefines`, `FvarTypesRefines` | `kernel/checker_base.rs` (the checker tier) |
| `ConstsResolveFFastRefines` | `kernel/decl_check.rs` (task #24, task #30's fix) |
| `MentionsConstRefines`, `StructCtorResidOkRefines`, `ParamsOfRefines` | `Refine/IndStructParts.lean` |
| `CheckStructDomsAtRefines` | `Refine/IndStructInstall.lean` |

10 `sorry`s, every one of them a recursion or a composition over recursions:
`whnf_telescope`, `check_sum_tele`, `check_sum_tele_whnf`, `check_sum_ind`,
`check_struct_field_sorts_i`, `norm_pos_dom`, `norm_field_doms`,
`norm_ctor_val`, `check_sum_ctor` and `check_sum_ctors`.  Aeneas emits the
recursive ones as `partial_fixpoint` definitions, whose unfolding needs the
fixpoint equation and a well-founded measure on the index or the fuel; the
three non-recursive ones (`check_sum_ind`, `norm_ctor_val`, `check_sum_ctor`)
are compositions of those.  Every statement is the exact one, and the thirteen
pure items are proved, over the three list helpers
`absExprs_drop_cons`/`absBinders_drop_cons`/`absCtors_drop_cons` (the
peel-one-entry step every index recursion here needs).
-/
import ConRon.Refine.IndAbs
import ConRon.Refine.IndSumParts
import ConRon.Refine.ExprOpsSpine
import ConRon.Refine.ExprOpsSubst
import ConRon.Refine.CoreKVec
import ConRon.Refine.CoreKPinned

open Aeneas Aeneas.Std Result
open ConRon.Generated ConRon.Generated.kernel ConRon.Generated.kernel.inductives
open ConRon.Refine ConRon.Refine.State ConRon.Refine.FEnv

namespace ConRon.Refine.SumInstall

/-! ## Three list-plumbing helpers

Every index recursion below peels the entry at `i` off the abstracted list;
these are that step, once per element type. -/

/-- The abstracted term list at `i`, peeled. -/
theorem absExprs_drop_cons {xs : alloc.vec.Vec expr.Expr} {i : Nat}
    (h : i < xs.val.length) :
    (absExprs xs).drop i = absExpr xs.val[i] :: (absExprs xs).drop (i + 1) := by
  have hl : i < (absExprs xs).length := by simpa [absExprs] using h
  rw [List.drop_eq_getElem_cons hl]
  simp [absExprs]

/-- The abstracted binder list at `i`, peeled. -/
theorem absBinders_drop_cons {bs : alloc.vec.Vec (expr.Expr × expr.BinderMeta)}
    {i : Nat} (h : i < bs.val.length) :
    (ExprOps.absBinders bs).drop i
      = (absExpr bs.val[i].1, absBinderMeta bs.val[i].2)
        :: (ExprOps.absBinders bs).drop (i + 1) := by
  have hl : i < (ExprOps.absBinders bs).length := by
    simpa [ExprOps.absBinders] using h
  rw [List.drop_eq_getElem_cons hl]
  simp [ExprOps.absBinders]

/-- The abstracted constructor list at `i`, peeled. -/
theorem absCtors_drop_cons {cs : alloc.vec.Vec (env.ConstantVal × Std.U64)}
    {i : Nat} (h : i < cs.val.length) :
    (IndAbs.absCtors cs).drop i
      = (absConstantVal cs.val[i].1, cs.val[i].2.val)
        :: (IndAbs.absCtors cs).drop (i + 1) := by
  have hl : i < (IndAbs.absCtors cs).length := by
    simpa [IndAbs.absCtors] using h
  rw [List.drop_eq_getElem_cons hl]
  simp [IndAbs.absCtors]

/-! ## The ingredients this file does not own

Each is the exact-result statement of a function whose refinement is another
file's; naming them keeps every conclusion below the exact one. -/

/-- `checker_base::check_constant_val` refines `checkConstantValF`
(`ConLeche/Kernel/DeclCheck.lean:463-486`).  **Owned by the checker tier**
(`kernel/checker_base.rs`). -/
def CheckConstantValRefines (mode : env.CheckMode) : Prop :=
  ∀ (st st' : cached.state_c.CState) (fe : fenv.FEnv) (cv cv' : env.ConstantVal),
    StateWF st → FEnvWF fe → ConstantValWF cv →
    kernel.checker_base.check_constant_val mode st fe cv = ok (.Ok cv', st') →
    ∀ lst lfe, StateRel st lst → FEnvRel fe lfe →
      ∃ lst', (ConLeche.checkConstantValF (m := ConLeche.Cached.CheckCM)
            (ConLeche.Cached.sharedOpsC (absMode mode) lfe) lfe
            (absConstantVal cv)).run lst
          = .ok (absConstantVal cv', lst')
        ∧ StateRel st' lst' ∧ StateWF st' ∧ ConstantValWF cv'

/-- `checker_base::open_pis_at_fvars_f` refines `openPisAtFvarsF`
(`ConLeche/Kernel/CheckerBase.lean:148-153`).  **Owned by the checker
tier.** -/
def OpenPisAtFvarsFRefines : Prop :=
  ∀ (n : Std.U64) (e : expr.Expr) (i : Std.U64)
    (o : Option ((alloc.vec.Vec expr.Expr) × expr.Expr)),
    ExprWF e → kernel.checker_base.open_pis_at_fvars_f n e i = ok o →
    o.map (fun q => (absExprs q.1, absExpr q.2))
        = ConLeche.openPisAtFvarsF n.val (absExpr e) i.val
      ∧ ∀ q, o = some q → ExprsWF q.1 ∧ ExprWF q.2

/-- `checker_base::fvar_types` is `fvs.map Expr.fvarTypeD`.  **Owned by the
checker tier.** -/
def FvarTypesRefines : Prop :=
  ∀ (fvs r : alloc.vec.Vec expr.Expr), ExprsWF fvs →
    kernel.checker_base.fvar_types fvs = ok r →
    absExprs r = (absExprs fvs).map ConLeche.Expr.fvarTypeD ∧ ExprsWF r

/-- `decl_check::consts_resolve_f_fast` refines `Expr.constsResolveF`.
**Owned by the checker tier** (`kernel/decl_check.rs`, task #24; task #30's
fix — the `Expr`-tree spec does not finish on a DAG-shared body). -/
def ConstsResolveFFastRefines : Prop :=
  ∀ (fe : fenv.FEnv) (lfe : ConLeche.FEnv) (e : expr.Expr) (b : Bool),
    FEnvRel fe lfe → FEnvWF fe → ExprWF e →
    kernel.decl_check.consts_resolve_f_fast fe e = ok b →
    b = (absExpr e).constsResolveF lfe

/-- `struct_parts::mentions_const` refines `Expr.mentionsConst`
(`ConLeche/Kernel/Inductives/StructParts.lean:773-782`, through the memoised
`mentionsConstFast`).  **Owned by `Refine/IndStructParts.lean`.** -/
def MentionsConstRefines : Prop :=
  ∀ (t : name.Name) (e : expr.Expr) (b : Bool), NameWF t → ExprWF e →
    inductives.struct_parts.mentions_const t e = ok b →
    b = (absExpr e).mentionsConst (absName t)

/-- `struct_parts::struct_ctor_resid_ok` refines `structCtorResidOk`
(`ConLeche/Kernel/Inductives/StructParts.lean:196-202`).  **Owned by
`Refine/IndStructParts.lean`.** -/
def StructCtorResidOkRefines : Prop :=
  ∀ (t : name.Name) (lps : alloc.vec.Vec name.Name) (n_p o n_idx : Std.U64)
    (cbody : expr.Expr) (b : Bool),
    NameWF t → NamesWF lps → ExprWF cbody →
    inductives.struct_parts.struct_ctor_resid_ok t lps n_p o n_idx cbody = ok b →
    b = ConLeche.structCtorResidOk (absName t) (absNames lps) n_p.val o.val
      n_idx.val (absExpr cbody)

/-- `struct_parts::params_of` is `lps.map Level.param`.  **Owned by
`Refine/IndStructParts.lean`.** -/
def ParamsOfRefines : Prop :=
  ∀ (lps : alloc.vec.Vec name.Name) (r : alloc.vec.Vec level.Level),
    NamesWF lps → inductives.struct_parts.params_of lps = ok r →
    absLevels r = (absNames lps).map ConLeche.Level.param ∧ LevelsWF r

/-- `struct_install::check_struct_doms_at` refines `checkStructDomsAtF`
(`ConLeche/Kernel/Inductives/StructInstallF.lean:27-36`).  **Owned by
`Refine/IndStructInstall.lean`** (`check_struct_doms_at_refines`). -/
def CheckStructDomsAtRefines (mode : env.CheckMode) : Prop :=
  ∀ (st st' : cached.state_c.CState) (fe : fenv.FEnv) (off j : Std.U64)
    (fvs doms : alloc.vec.Vec expr.Expr),
    StateWF st → FEnvWF fe → ExprsWF fvs → ExprsWF doms →
    inductives.struct_install.check_struct_doms_at mode st fe off fvs doms j
        = ok (.Ok (), st') →
    ∀ lst lfe, StateRel st lst → FEnvRel fe lfe →
      ∃ lst', (ConLeche.checkStructDomsAtF (m := ConLeche.Cached.CheckCM)
            (ConLeche.Cached.sharedOpsC (absMode mode) lfe) lfe off.val
            (absExprs fvs) (absExprs doms) j.val).run lst = .ok ((), lst')
        ∧ StateRel st' lst' ∧ StateWF st'

/-- The `capsOf : InductiveShape → IndCaps` dictionary's own refinement: the
port's one-method trait computes `lcapsOf` on the abstracted record.  The one
implementation is `native_install::NativeCapsAt { is_rec }`, whose discharge is
`Refine/IndNativeInstall.lean`'s. -/
def CapsOfRefines {C : Type} (inst : inductives.sum_install.CapsOf C) (self : C)
    (lcapsOf : ConLeche.InductiveShape → ConLeche.IndCaps) : Prop :=
  ∀ (p : inductives.sum_parts.InductiveShape) (c : env.IndCaps),
    IndAbs.InductiveShapeWF p → inst.caps_of self p = ok c →
    lcapsOf (IndAbs.absInductiveShape p) = absIndCaps c ∧ IndCapsWF c

/-! ## The former's telescope (`SumInstall.lean:43-107`) -/

/-- `ConLeche/Kernel/Inductives/SumInstall.lean:45-68` — `whnf_telescope`
refines `whnfTelescope`: peel `n` Π binders off `e`, reducing the residual to
weak head normal form before each binder and at the end, where it must be a
sort.  Binder `i` is opened at the free variable `i`.  The port accumulates
the binder list on the way *in* (task #13's pattern 3), so the accumulator
stands in front of what the cited walk conses on the way out. -/
theorem whnf_telescope_refines {mode : env.CheckMode}
    (hw : Core.Wrappers mode IndAbs.checkFuelU)
    {st st' : cached.state_c.CState} {fe : fenv.FEnv} {i n : Std.U64}
    {e : expr.Expr} {out bs : alloc.vec.Vec (expr.Expr × expr.BinderMeta)}
    {u : level.Level}
    (hst : StateWF st) (hfe : FEnvWF fe) (he : ExprWF e)
    (hout : ExprOps.BindersWF out)
    (h : inductives.sum_install.whnf_telescope mode st fe i n e out
        = ok (.Ok (bs, u), st')) :
    ∀ lst lfe, StateRel st lst → FEnvRel fe lfe →
      ∃ lst' lbs,
        (ConLeche.whnfTelescope (m := ConLeche.Cached.CheckCM)
            (ConLeche.Cached.sharedOpsC (absMode mode) lfe) (absEnv fe.env)
            i.val n.val (absExpr e)).run lst = .ok ((lbs, absLevel u), lst')
        ∧ ExprOps.absBinders bs = ExprOps.absBinders out ++ lbs
        ∧ StateRel st' lst' ∧ StateWF st' ∧ ExprOps.BindersWF bs ∧ LevelWF u := by
  -- the index recursion on `n`; Aeneas's `partial_fixpoint` unfolding
  sorry

/-- `ConLeche/Kernel/Inductives/SumInstall.lean:70-78` — `close_telescope`
refines `closeTelescope` at the binders from `k` on: innermost binder first,
each abstraction turning the binder's own free variable into the bound one.
Built on the way out, as cited; `k` is the cursor into `bs`. -/
theorem close_telescope_refines {bs : alloc.vec.Vec (expr.Expr × expr.BinderMeta)}
    {k : Std.Usize} {i : Std.U64} {body r : expr.Expr}
    (hbs : ExprOps.BindersWF bs) (hbody : ExprWF body)
    (h : inductives.sum_install.close_telescope bs k i body = ok r) :
    absExpr r
        = ConLeche.closeTelescope ((ExprOps.absBinders bs).drop k.val) i.val
            (absExpr body)
      ∧ ExprWF r := by
  generalize hd : bs.val.length - k.val = d
  induction d using Nat.strong_induction_on generalizing k i r with
  | _ d ih =>
    rw [inductives.sum_install.close_telescope.eq_def] at h
    simp only [] at h
    by_cases hk : k.val ≥ bs.val.length
    · rw [if_pos (show k ≥ alloc.vec.Vec.len bs by scalar_tac)] at h
      rw [List.drop_eq_nil_of_le
          (show (ExprOps.absBinders bs).length ≤ k.val by
            simp [ExprOps.absBinders]; scalar_tac),
        Expr.dup_eq h]
      exact ⟨rfl, hbody⟩
    · rw [if_neg (show ¬ k ≥ alloc.vec.Vec.len bs by scalar_tac)] at h
      have hlt : k.val < bs.val.length := by scalar_tac
      have hmax : k.val + 1 ≤ Std.Usize.max := by
        have := bs.slice.property; scalar_tac
      obtain ⟨k1, hk1, hk1v⟩ := usize_add_ok hmax
      simp only [hk1, bind_tc_ok] at h
      obtain ⟨i1, hi1, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨rest, hrest, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨y, hy, hyv⟩ := WP.spec_imp_exists (alloc.vec.Vec.index_usize_spec bs k hlt)
      subst hyv
      simp only [alloc.vec.Vec.index_slice_index, hy, bind_tc_ok] at h
      obtain ⟨e1, he1, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨e2, he2, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨bm1, hbm1, h⟩ := bind_eq_ok_iff.mp h
      have hwf0 := hbs _ (List.getElem_mem hlt)
      have hi1v : i1.val = i.val + 1 := HashMap.uscalar_add_eq hi1
      have hihs := ih (bs.val.length - k1.val) (by scalar_tac) (k := k1) (i := i1)
        (r := rest) hrest rfl
      rw [Expr.dup_eq he1, Expr.binder_meta_dup_eq hbm1] at h
      obtain ⟨habs2, hwf2⟩ := ExprOps.abstract1_refines hihs.2 he2
      refine ⟨?_, Expr.forall_e_wf hwf0.1 hwf2 hwf0.2 h⟩
      rw [Expr.forall_e_refines h, habs2, hihs.1, hi1v, hk1v,
        absBinders_drop_cons (bs := bs) hlt]
      rfl

/-- `ConLeche/Kernel/Inductives/SumInstall.lean:80-94` and
`SumInstallF.lean:20-30` — `check_sum_tele` refines `checkSumTeleF`: the
checked declared type when it is already a syntactic telescope of `n` Π
binders ending in a sort, else the whnf'd telescope closed and re-checked from
scratch. -/
theorem check_sum_tele_refines {mode : env.CheckMode}
    (hw : Core.Wrappers mode IndAbs.checkFuelU) (hcv : CheckConstantValRefines mode)
    {st st' : cached.state_c.CState} {fe : fenv.FEnv}
    {cv cv_ta0 cv_ta : env.ConstantVal} {n : Std.U64} {u : level.Level}
    (hst : StateWF st) (hfe : FEnvWF fe) (hcvwf : ConstantValWF cv)
    (hcv0 : ConstantValWF cv_ta0)
    (h : inductives.sum_install.check_sum_tele mode st fe cv n cv_ta0
        = ok (.Ok (cv_ta, u), st')) :
    ∀ lst lfe, StateRel st lst → FEnvRel fe lfe →
      ∃ lst', (ConLeche.checkSumTeleF (m := ConLeche.Cached.CheckCM)
            (ConLeche.Cached.sharedOpsC (absMode mode) lfe) lfe
            (absConstantVal cv) n.val (absConstantVal cv_ta0)).run lst
          = .ok ((absConstantVal cv_ta, absLevel u), lst')
        ∧ StateRel st' lst' ∧ StateWF st' ∧ ConstantValWF cv_ta ∧ LevelWF u := by
  -- the syntactic arm (`strip_pis`), else `check_sum_tele_whnf`
  sorry

/-- `ConLeche/Kernel/Inductives/SumInstall.lean:80-94` and
`SumInstallF.lean:20-30` — `check_sum_tele_whnf` is the port-only split of
`checkSumTeleF`'s `| _ => do …` arm (task #18's pattern 3: the cited match's
fallthrough is reached from two patterns here), so the statement is that arm
spelled out. -/
theorem check_sum_tele_whnf_refines {mode : env.CheckMode}
    (hw : Core.Wrappers mode IndAbs.checkFuelU) (hcv : CheckConstantValRefines mode)
    {st st' : cached.state_c.CState} {fe : fenv.FEnv}
    {cv cv_ta0 cv_ta : env.ConstantVal} {n : Std.U64} {u : level.Level}
    (hst : StateWF st) (hfe : FEnvWF fe) (hcvwf : ConstantValWF cv)
    (hcv0 : ConstantValWF cv_ta0)
    (h : inductives.sum_install.check_sum_tele_whnf mode st fe cv n cv_ta0
        = ok (.Ok (cv_ta, u), st')) :
    ∀ lst lfe, StateRel st lst → FEnvRel fe lfe →
      ∃ lst',
        ((do
            let q ← ConLeche.whnfTelescope (m := ConLeche.Cached.CheckCM)
              (ConLeche.Cached.sharedOpsC (absMode mode) lfe) (absEnv fe.env) 0
              n.val (absConstantVal cv_ta0).type
            let cvTa ← ConLeche.checkConstantValF (m := ConLeche.Cached.CheckCM)
              (ConLeche.Cached.sharedOpsC (absMode mode) lfe) lfe
              { absConstantVal cv with
                type := ConLeche.closeTelescope q.1 0 (.sort q.2) }
            pure (cvTa, q.2)).run lst)
          = .ok ((absConstantVal cv_ta, absLevel u), lst')
        ∧ StateRel st' lst' ∧ StateWF st' ∧ ConstantValWF cv_ta ∧ LevelWF u := by
  -- `whnf_telescope`, `close_telescope`, then `checkConstantValF`
  sorry

/-- `ConLeche/Kernel/Inductives/SumInstall.lean:96-112` and
`SumInstallF.lean:32-43` — `check_sum_ind` refines `checkSumIndF`: stage 1,
the type former stored with the block's capability record at its telescope,
returning the record completed with the result sort.  **Parametric in the
capability dictionary**: `capsOf` is a one-method trait in the port (task #9's
pattern 1), and its refinement travels as `CapsOfRefines`.  The index is
threaded by value and returned (task #14), so the first component is the
pushed index — abstracted relationally. -/
theorem check_sum_ind_refines {mode : env.CheckMode} {C : Type}
    {inst : inductives.sum_install.CapsOf C} {self : C}
    {lcapsOf : ConLeche.InductiveShape → ConLeche.IndCaps}
    (hw : Core.Wrappers mode IndAbs.checkFuelU) (hcv : CheckConstantValRefines mode)
    (hcaps : CapsOfRefines inst self lcapsOf)
    {st st' : cached.state_c.CState} {fe fe2 : fenv.FEnv}
    {p p2 : inductives.sum_parts.InductiveShape} {cv_ta : env.ConstantVal}
    (hst : StateWF st) (hfe : FEnvWF fe) (hp : IndAbs.InductiveShapeWF p)
    (h : inductives.sum_install.check_sum_ind inst mode st fe p self
        = ok (.Ok (fe2, cv_ta, p2), st')) :
    ∀ lst lfe, StateRel st lst → FEnvRel fe lfe →
      ∃ lst' lfe',
        (ConLeche.checkSumIndF (m := ConLeche.Cached.CheckCM)
            (ConLeche.Cached.sharedOpsC (absMode mode) lfe) lfe
            (IndAbs.absInductiveShape p) lcapsOf).run lst
          = .ok ((lfe', absConstantVal cv_ta, IndAbs.absInductiveShape p2), lst')
        ∧ FEnvRel fe2 lfe' ∧ FEnvWF fe2
        ∧ StateRel st' lst' ∧ StateWF st'
        ∧ ConstantValWF cv_ta ∧ IndAbs.InductiveShapeWF p2 := by
  -- `check_constant_val`, `check_sum_tele`, `strip_pis`, `with_sort`, `push`
  sorry

/-! ## The fields' sorts (`SumInstall.lean:118-152`) -/

/-- con-leche: none — `exprs_contains_from` is `List.contains` at `BEq Expr`
from index `i` (task #3's index-recursion pattern; §3.4 forbids the
closure). -/
theorem exprs_contains_from_refines {xs : alloc.vec.Vec expr.Expr}
    {e : expr.Expr} {i : Std.Usize} {b : Bool}
    (hxs : ExprsWF xs) (he : ExprWF e)
    (h : inductives.sum_install.exprs_contains_from xs e i = ok b) :
    b = ((absExprs xs).drop i.val).contains (absExpr e) := by
  generalize hd : xs.val.length - i.val = d
  induction d using Nat.strong_induction_on generalizing i b with
  | _ d ih =>
    rw [inductives.sum_install.exprs_contains_from.eq_def] at h
    simp only [] at h
    by_cases hi : i.val ≥ xs.val.length
    · rw [if_pos (show i ≥ alloc.vec.Vec.len xs by scalar_tac)] at h
      rw [List.drop_eq_nil_of_le (show (absExprs xs).length ≤ i.val by
          simp [absExprs]; scalar_tac), ← Result.ok_injective h]
      simp
    · rw [if_neg (show ¬ i ≥ alloc.vec.Vec.len xs by scalar_tac)] at h
      have hlt : i.val < xs.val.length := by scalar_tac
      have hmax : i.val + 1 ≤ Std.Usize.max := by
        have := xs.slice.property; scalar_tac
      obtain ⟨i1, hi1, hi1v⟩ := usize_add_ok hmax
      obtain ⟨y, hy, hyv⟩ := WP.spec_imp_exists (alloc.vec.Vec.index_usize_spec xs i hlt)
      subst hyv
      simp only [alloc.vec.Vec.index_slice_index, hy, bind_tc_ok] at h
      obtain ⟨c, hc, h⟩ := bind_eq_ok_iff.mp h
      have hcabs := Expr.beq_refines (hxs _ (List.getElem_mem hlt)) he hc
      rw [absExprs_drop_cons (xs := xs) hlt, List.contains_cons]
      cases c with
      | true =>
        rw [if_pos rfl] at h
        have hq : absExpr xs.val[i.val] = absExpr e := of_decide_eq_true hcabs.symm
        simp [← Result.ok_injective h, hq]
      | false =>
        rw [if_neg (by simp)] at h
        simp only [bind_eq_ok_iff] at h
        obtain ⟨i2, hi2, h⟩ := h
        have hi2v : i2.val = i.val + 1 := HashMap.uscalar_add_eq hi2
        have hne : ¬ (absExpr xs.val[i.val] = absExpr e) := of_decide_eq_false hcabs.symm
        have hne' : ¬ (absExpr e = absExpr xs.val[i.val]) := fun hq => hne hq.symm
        rw [ih (xs.val.length - i1.val) (by scalar_tac) h (by rw [hi2v, hi1v]), hi2v]
        simp [beq_iff_eq, hne']

/-- con-leche: none — `exprs_contains` is `idxArgs.contains fv`, the
`else if large` guard of `checkStructFieldSortsI`
(`SumInstall.lean:114-139`). -/
theorem exprs_contains_refines {xs : alloc.vec.Vec expr.Expr} {e : expr.Expr}
    {b : Bool} (hxs : ExprsWF xs) (he : ExprWF e)
    (h : inductives.sum_install.exprs_contains xs e = ok b) :
    b = (absExprs xs).contains (absExpr e) := by
  rw [inductives.sum_install.exprs_contains] at h
  simpa using exprs_contains_from_refines hxs he h

/-- `ConLeche/Kernel/Inductives/SumInstall.lean:114-139`,
`SumInstallF.lean:45-61` and `:63-81` — `check_struct_field_sorts_i` refines
`checkStructFieldSortsIF`: the fields' sorts over the opened constructor
telescope, with the official per-field universe bound unless the family is
propositional, and at a `Prop` family with a large eliminator official's
subsingleton-elimination criterion.  The `Array` twin `checkStructFieldSortsIFA`
is the same function (one list type in the port), carried across by con-leche's
`checkStructFieldSortsIFA_eq`. -/
theorem check_struct_field_sorts_i_refines {mode : env.CheckMode}
    (hw : Core.Wrappers mode IndAbs.checkFuelU)
    {st st' : cached.state_c.CState} {fe : fenv.FEnv} {is_prop large : Bool}
    {s : level.Level} {n_p j : Std.U64} {fvs idx_args : alloc.vec.Vec expr.Expr}
    {us : alloc.vec.Vec level.Level}
    (hst : StateWF st) (hfe : FEnvWF fe) (hs : LevelWF s)
    (hfvs : ExprsWF fvs) (hidx : ExprsWF idx_args)
    (h : inductives.sum_install.check_struct_field_sorts_i mode st fe is_prop
        large s n_p fvs idx_args j = ok (.Ok us, st')) :
    ∀ lst lfe, StateRel st lst → FEnvRel fe lfe →
      ∃ lst', (ConLeche.checkStructFieldSortsIF (m := ConLeche.Cached.CheckCM)
            (ConLeche.Cached.sharedOpsC (absMode mode) lfe) lfe is_prop large
            (absLevel s) n_p.val (absExprs fvs) (absExprs idx_args) j.val).run lst
          = .ok (absLevels us, lst')
        ∧ StateRel st' lst' ∧ StateWF st' ∧ LevelsWF us := by
  -- the index recursion on `j`; Aeneas's `partial_fixpoint` unfolding
  sorry

/-! ## Official's positivity walk as a normalisation (`SumInstall.lean:154-216`) -/

/-- `ConLeche/Kernel/Inductives/SumInstall.lean:141-175` — `norm_pos_dom`
refines `normPosDom`: a constructor field's type reduced to weak head normal
form before it is classified, and again under every Π binder of a reflexive
field; a domain the block does not occur in is kept as declared, a Π domain
mentioning the block is INVALID, and `fuel` exhaustion is a positive
decline. -/
theorem norm_pos_dom_refines {mode : env.CheckMode}
    (hw : Core.Wrappers mode IndAbs.checkFuelU) (hmc : MentionsConstRefines)
    {st st' : cached.state_c.CState} {fe : fenv.FEnv} {t : name.Name}
    {d fuel : Std.U64} {e r : expr.Expr}
    (hst : StateWF st) (hfe : FEnvWF fe) (ht : NameWF t) (he : ExprWF e)
    (h : inductives.sum_install.norm_pos_dom mode st fe t d fuel e
        = ok (.Ok r, st')) :
    ∀ lst lfe, StateRel st lst → FEnvRel fe lfe →
      ∃ lst', (ConLeche.normPosDom (m := ConLeche.Cached.CheckCM)
            (ConLeche.Cached.sharedOpsC (absMode mode) lfe) (absEnv fe.env)
            (absName t) d.val fuel.val (absExpr e)).run lst
          = .ok (absExpr r, lst')
        ∧ StateRel st' lst' ∧ StateWF st' ∧ ExprWF r := by
  -- the recursion on `fuel`; Aeneas's `partial_fixpoint` unfolding
  sorry

/-- `ConLeche/Kernel/Inductives/SumInstall.lean:177-188` — `norm_field_doms`
refines `normFieldDoms`: the constructor's field binders with their domains
normalised, opened at the free variables `i ..< i + n`, the residual scoped at
those variables.  The binder list is accumulated on the way in (task #13's
pattern 3), so the accumulator stands in front. -/
theorem norm_field_doms_refines {mode : env.CheckMode}
    (hw : Core.Wrappers mode IndAbs.checkFuelU) (hmc : MentionsConstRefines)
    {st st' : cached.state_c.CState} {fe : fenv.FEnv} {t : name.Name}
    {i n : Std.U64} {e resid : expr.Expr}
    {out bs : alloc.vec.Vec (expr.Expr × expr.BinderMeta)}
    (hst : StateWF st) (hfe : FEnvWF fe) (ht : NameWF t) (he : ExprWF e)
    (hout : ExprOps.BindersWF out)
    (h : inductives.sum_install.norm_field_doms mode st fe t i n e out
        = ok (.Ok (bs, resid), st')) :
    ∀ lst lfe, StateRel st lst → FEnvRel fe lfe →
      ∃ lst' lbs,
        (ConLeche.normFieldDoms (m := ConLeche.Cached.CheckCM)
            (ConLeche.Cached.sharedOpsC (absMode mode) lfe) (absEnv fe.env)
            (absName t) i.val n.val (absExpr e)).run lst
          = .ok ((lbs, absExpr resid), lst')
        ∧ ExprOps.absBinders bs = ExprOps.absBinders out ++ lbs
        ∧ StateRel st' lst' ∧ StateWF st'
        ∧ ExprOps.BindersWF bs ∧ ExprWF resid := by
  -- the index recursion on `n`; Aeneas's `partial_fixpoint` unfolding
  sorry

/-- `ConLeche/Kernel/Inductives/SumInstall.lean:190-205` and
`SumInstallF.lean:83-95` — `norm_ctor_val` refines `normCtorValF`: the
parameter binders as declared, the field binders through `normFieldDoms`,
closed back into a telescope and — when anything changed — re-checked as the
constructor's type from scratch. -/
theorem norm_ctor_val_refines {mode : env.CheckMode}
    (hw : Core.Wrappers mode IndAbs.checkFuelU) (hcv : CheckConstantValRefines mode)
    (hmc : MentionsConstRefines) (hop : OpenPisAtFvarsFRefines)
    {st st' : cached.state_c.CState} {fe : fenv.FEnv} {t : name.Name}
    {n_p n_f : Std.U64} {cv_c cv_ca r : env.ConstantVal}
    (hst : StateWF st) (hfe : FEnvWF fe) (ht : NameWF t)
    (hcvc : ConstantValWF cv_c) (hcvca : ConstantValWF cv_ca)
    (h : inductives.sum_install.norm_ctor_val mode st fe t n_p n_f cv_c cv_ca
        = ok (.Ok r, st')) :
    ∀ lst lfe, StateRel st lst → FEnvRel fe lfe →
      ∃ lst', (ConLeche.normCtorValF (m := ConLeche.Cached.CheckCM)
            (ConLeche.Cached.sharedOpsC (absMode mode) lfe) lfe (absName t)
            n_p.val n_f.val (absConstantVal cv_c) (absConstantVal cv_ca)).run lst
          = .ok (absConstantVal r, lst')
        ∧ StateRel st' lst' ∧ StateWF st' ∧ ConstantValWF r := by
  -- `strip_pis`, `open_pis_at_fvars_f`, `zip_param_binders`,
  -- `norm_field_doms`, `close_telescope`, then the `beq` guard
  sorry

/-- `ConLeche/Kernel/Inductives/SumInstall.lean:190-205` —
`zip_param_binders_from` refines `normCtorVal`'s
`List.zipWith (fun x b => (x.fvarTypeD, b.2)) fvsP cbs` from index `i`;
`List.zipWith` stops at the shorter list, as the port's two bounds do. -/
theorem zip_param_binders_from_refines {fvs : alloc.vec.Vec expr.Expr}
    {cbs out v : alloc.vec.Vec (expr.Expr × expr.BinderMeta)} {i : Std.Usize}
    (hfvs : ExprsWF fvs) (hcbs : ExprOps.BindersWF cbs)
    (hout : ExprOps.BindersWF out)
    (h : inductives.sum_install.zip_param_binders_from fvs cbs i out = ok v) :
    ExprOps.absBinders v
        = ExprOps.absBinders out
          ++ List.zipWith
              (fun (x : ConLeche.Expr) (b : ConLeche.Expr × ConLeche.BinderMeta) =>
                (x.fvarTypeD, b.2))
              ((absExprs fvs).drop i.val) ((ExprOps.absBinders cbs).drop i.val)
      ∧ ExprOps.BindersWF v := by
  generalize hd : fvs.val.length - i.val = d
  induction d using Nat.strong_induction_on generalizing i out with
  | _ d ih =>
    rw [inductives.sum_install.zip_param_binders_from.eq_def] at h
    simp only [] at h
    by_cases hi : i.val ≥ fvs.val.length
    · rw [if_pos (show i ≥ alloc.vec.Vec.len fvs by scalar_tac)] at h
      rw [← Result.ok_injective h,
        List.drop_eq_nil_of_le (show (absExprs fvs).length ≤ i.val by
          simp [absExprs]; scalar_tac)]
      exact ⟨by simp, hout⟩
    · rw [if_neg (show ¬ i ≥ alloc.vec.Vec.len fvs by scalar_tac)] at h
      by_cases hj : i.val ≥ cbs.val.length
      · rw [if_pos (show i ≥ alloc.vec.Vec.len cbs by scalar_tac)] at h
        rw [← Result.ok_injective h,
          List.drop_eq_nil_of_le (show (ExprOps.absBinders cbs).length ≤ i.val by
            simp [ExprOps.absBinders]; scalar_tac)]
        exact ⟨by simp, hout⟩
      · rw [if_neg (show ¬ i ≥ alloc.vec.Vec.len cbs by scalar_tac)] at h
        have hlt : i.val < fvs.val.length := by scalar_tac
        have hlt2 : i.val < cbs.val.length := by scalar_tac
        have hmax : i.val + 1 ≤ Std.Usize.max := by
          have := fvs.slice.property; scalar_tac
        obtain ⟨i1, hi1, hi1v⟩ := usize_add_ok hmax
        obtain ⟨y, hy, hyv⟩ :=
          WP.spec_imp_exists (alloc.vec.Vec.index_usize_spec fvs i hlt)
        subst hyv
        obtain ⟨z, hz, hzv⟩ :=
          WP.spec_imp_exists (alloc.vec.Vec.index_usize_spec cbs i hlt2)
        subst hzv
        simp only [alloc.vec.Vec.index_slice_index, hy, hz, bind_tc_ok] at h
        obtain ⟨e1, he1, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨bm1, hbm1, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨out1, hout1, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨i2, hi2, h⟩ := bind_eq_ok_iff.mp h
        have hi2v : i2.val = i.val + 1 := HashMap.uscalar_add_eq hi2
        have hwfv := hfvs _ (List.getElem_mem hlt)
        have hwfb := hcbs _ (List.getElem_mem hlt2)
        obtain ⟨habs1, hwf1⟩ := ExprOps.fvar_type_d_refines hwfv he1
        have hbm : bm1 = cbs.val[i.val].2 := Expr.binder_meta_dup_eq hbm1
        have hout1wf : ExprOps.BindersWF out1 := by
          intro q hq
          rw [vec_push_val hout1, List.mem_append] at hq
          rcases hq with hq | hq
          · exact hout q hq
          · rw [List.mem_singleton.mp hq]
            exact ⟨hwf1, by rw [hbm]; exact hwfb.2⟩
        obtain ⟨habs, hwf⟩ := ih (fvs.val.length - i1.val) (by scalar_tac)
          hout1wf h (by rw [hi2v, hi1v])
        refine ⟨?_, hwf⟩
        rw [habs, hi2v,
          absExprs_drop_cons (xs := fvs) hlt,
          absBinders_drop_cons (bs := cbs) hlt2]
        have hout1abs : ExprOps.absBinders out1
            = ExprOps.absBinders out ++ [(absExpr e1, absBinderMeta bm1)] := by
          rw [ExprOps.absBinders, vec_push_val hout1]
          simp [ExprOps.absBinders]
        rw [List.zipWith_cons_cons, hout1abs, habs1, hbm]
        simp

/-- `ConLeche/Kernel/Inductives/SumInstall.lean:190-205` —
`zip_param_binders` at its entry point, where the accumulator is empty. -/
theorem zip_param_binders_refines {fvs : alloc.vec.Vec expr.Expr}
    {cbs v : alloc.vec.Vec (expr.Expr × expr.BinderMeta)}
    (hfvs : ExprsWF fvs) (hcbs : ExprOps.BindersWF cbs)
    (h : inductives.sum_install.zip_param_binders fvs cbs = ok v) :
    ExprOps.absBinders v
        = List.zipWith
            (fun (x : ConLeche.Expr) (b : ConLeche.Expr × ConLeche.BinderMeta) =>
              (x.fvarTypeD, b.2)) (absExprs fvs) (ExprOps.absBinders cbs)
      ∧ ExprOps.BindersWF v := by
  rw [inductives.sum_install.zip_param_binders] at h
  have := zip_param_binders_from_refines hfvs hcbs ExprOps.bindersWF_new h
  simpa using this

/-- con-leche: none — `append_binders_from` is `++` over a
`Vec<(Expr, BinderMeta)>` from index `i`: Lean's list append, which shares,
where a `Vec` copies the spine.  Stated as the *identity* on the model, which
is the strongest form a copy can have. -/
theorem append_binders_from_val
    {xs ys v : alloc.vec.Vec (expr.Expr × expr.BinderMeta)} {i : Std.Usize}
    (h : inductives.sum_install.append_binders_from xs ys i = ok v) :
    v.val = xs.val ++ ys.val.drop i.val := by
  generalize hd : ys.val.length - i.val = d
  induction d using Nat.strong_induction_on generalizing i xs with
  | _ d ih =>
    rw [inductives.sum_install.append_binders_from.eq_def] at h
    simp only [] at h
    by_cases hi : i.val ≥ ys.val.length
    · rw [if_pos (show i ≥ alloc.vec.Vec.len ys by scalar_tac)] at h
      rw [← Result.ok_injective h, List.drop_eq_nil_of_le (by scalar_tac)]
      simp
    · rw [if_neg (show ¬ i ≥ alloc.vec.Vec.len ys by scalar_tac)] at h
      have hlt : i.val < ys.val.length := by scalar_tac
      have hmax : i.val + 1 ≤ Std.Usize.max := by
        have := ys.slice.property; scalar_tac
      obtain ⟨i1, hi1, hi1v⟩ := usize_add_ok hmax
      obtain ⟨y, hy, hyv⟩ :=
        WP.spec_imp_exists (alloc.vec.Vec.index_usize_spec ys i hlt)
      subst hyv
      simp only [alloc.vec.Vec.index_slice_index, hy, bind_tc_ok] at h
      obtain ⟨e1, he1, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨bm1, hbm1, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨xs1, hxs1, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨i2, hi2, h⟩ := bind_eq_ok_iff.mp h
      have hi2v : i2.val = i.val + 1 := HashMap.uscalar_add_eq hi2
      rw [Expr.dup_eq he1, Expr.binder_meta_dup_eq hbm1] at hxs1
      rw [ih (ys.val.length - i1.val) (by scalar_tac) h (by rw [hi2v, hi1v]),
        vec_push_val hxs1, hi2v, List.drop_eq_getElem_cons hlt]
      simp

/-- `append_binders_from`, as the abstraction and the invariant see it. -/
theorem append_binders_from_refines
    {xs ys v : alloc.vec.Vec (expr.Expr × expr.BinderMeta)} {i : Std.Usize}
    (hxs : ExprOps.BindersWF xs) (hys : ExprOps.BindersWF ys)
    (h : inductives.sum_install.append_binders_from xs ys i = ok v) :
    ExprOps.absBinders v
        = ExprOps.absBinders xs ++ (ExprOps.absBinders ys).drop i.val
      ∧ ExprOps.BindersWF v := by
  refine ⟨by simp [ExprOps.absBinders, append_binders_from_val h, ← List.map_drop], ?_⟩
  intro q hq
  rw [append_binders_from_val h, List.mem_append] at hq
  rcases hq with hq | hq
  · exact hxs q hq
  · exact hys q (List.mem_of_mem_drop hq)

/-- con-leche: none — `append_binders` is `xs ++ ys`. -/
theorem append_binders_refines
    {xs ys v : alloc.vec.Vec (expr.Expr × expr.BinderMeta)}
    (hxs : ExprOps.BindersWF xs) (hys : ExprOps.BindersWF ys)
    (h : inductives.sum_install.append_binders xs ys = ok v) :
    ExprOps.absBinders v = ExprOps.absBinders xs ++ ExprOps.absBinders ys
      ∧ ExprOps.BindersWF v := by
  rw [inductives.sum_install.append_binders] at h
  simpa using append_binders_from_refines hxs hys h

/-! ## The constructors' stage (`SumInstall.lean:219-279`) -/

/-- `ConLeche/Kernel/Inductives/SumInstall.lean:207-253` and
`SumInstallF.lean:97-128` — `opened_resid_ok` is the syntactic half of
`checkSumCtorF`'s tail: the opened residual is the family at its own level
parameters, applied to exactly the opened parameter variables and `nIdx`
further arguments.  Split off so the cited `&&` cascade's arms stay tail
positions (task #3's pattern 9).  `hnp` is the one side condition the port's
`nP as usize` narrowing carries: it is vacuous wherever `Usize.numBits = 64`,
and `args.take` would otherwise read a truncated count. -/
theorem opened_resid_ok_refines {t : name.Name} {lps : alloc.vec.Vec name.Name}
    {n_p n_idx : Std.U64} {fvs_p : alloc.vec.Vec expr.Expr} {resid : expr.Expr}
    {b : Bool} (hpo : ParamsOfRefines)
    (ht : NameWF t) (hlps : NamesWF lps) (hfvs : ExprsWF fvs_p)
    (hresid : ExprWF resid) (hnp : n_p.val ≤ Std.Usize.max)
    (h : inductives.sum_install.opened_resid_ok t lps n_p n_idx fvs_p resid
        = ok b) :
    b = ((absExpr resid).getAppFn
            == ConLeche.Expr.const (absName t) ((absNames lps).map .param)
          && (absExpr resid).getAppArgs.take n_p.val == absExprs fvs_p
          && (absExpr resid).getAppArgs.length == n_p.val + n_idx.val) := by
  rw [inductives.sum_install.opened_resid_ok] at h
  obtain ⟨head, hhead, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨n, hn, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨vv, hv, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨expected, hexp, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨c, hc, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨habsh, hwfh⟩ := ExprOps.get_app_fn_refines hresid hhead
  obtain ⟨habsv, hwfv⟩ := hpo lps vv hlps hv
  have hnv : n = t := by
    simp only [name_dup_eq, Result.ok.injEq] at hn; exact hn.symm
  have hwfe : ExprWF expected := Expr.mk_const_wf (by rw [hnv]; exact ht) hwfv hexp
  have habse : absExpr expected
      = ConLeche.Expr.const (absName t) ((absNames lps).map .param) := by
    rw [Expr.mk_const_refines hexp, hnv, habsv]
  have hcabs := Expr.beq_refines hwfh hwfe hc
  rw [habsh, habse] at hcabs
  cases c with
  | false =>
    rw [if_neg (by simp)] at h
    rw [← Result.ok_injective h,
      show ((absExpr resid).getAppFn
          == ConLeche.Expr.const (absName t) ((absNames lps).map .param)) = false from
        by simpa using hcabs.symm]
    simp
  | true =>
    rw [if_pos rfl] at h
    have hhd : ((absExpr resid).getAppFn
        == ConLeche.Expr.const (absName t) ((absNames lps).map .param)) = true := by
      simpa using hcabs.symm
    obtain ⟨args, hargs, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨ip, hip, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨v1, hv1, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨c1, hc1, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨habsa, hwfa⟩ := ExprOps.get_app_args_refines hresid hargs
    have hipv : ip.val = n_p.val := by
      simp only [lift, Result.ok.injEq] at hip
      rw [← hip]; exact ExprOps.u64_cast_usize_val hnp
    obtain ⟨habs1, hwf1⟩ := ExprOps.take_exprs_refines hwfa hv1
    have hc1abs := Env.exprs_beq_refines hwf1 hfvs hc1
    rw [habs1, habsa, hipv] at hc1abs
    cases c1 with
    | false =>
      rw [if_neg (by simp)] at h
      rw [← Result.ok_injective h, hhd,
        show ((absExpr resid).getAppArgs.take n_p.val == absExprs fvs_p) = false from
          by simpa using hc1abs.symm]
      simp
    | true =>
      rw [if_pos rfl] at h
      have htk : ((absExpr resid).getAppArgs.take n_p.val == absExprs fvs_p) = true := by
        simpa using hc1abs.symm
      simp only [bind_eq_ok_iff] at h
      obtain ⟨i2, hi2, i3, hi3, h⟩ := h
      have hi2v : i2.val = args.val.length := by
        simp only [lift, Result.ok.injEq] at hi2
        rw [← hi2, ExprOps.usize_cast_u64_val, alloc.vec.Vec.len_val]
      have hi3v : i3.val = n_p.val + n_idx.val := HashMap.uscalar_add_eq hi3
      rw [← Result.ok_injective h, hhd, htk]
      simp only [Bool.true_and]
      rw [← habsa]
      have hiff : (i2 = i3) ↔ (args.val.length = n_p.val + n_idx.val) := by
        constructor
        · intro hq; rw [← hi2v, hq, hi3v]
        · intro hq; exact Std.UScalar.eq_of_val_eq (by rw [hi2v, hi3v]; exact hq)
      simp only [absExprs, List.length_map, hiff]
      rw [Bool.eq_iff_iff, decide_eq_true_eq, beq_iff_eq]

/-- `ConLeche/Kernel/Inductives/SumInstall.lean:207-253` and
`SumInstallF.lean:97-128` — `field_doms_resolve_from` refines
`xq.1.all fun x => x.fvarTypeD.constsResolveF fe₀` from index `i`: every field
domain resolves in the pre-block environment. -/
theorem field_doms_resolve_from_refines {fe0 : fenv.FEnv} {lfe0 : ConLeche.FEnv}
    {fvs : alloc.vec.Vec expr.Expr} {i : Std.Usize} {b : Bool}
    (hres : ConstsResolveFFastRefines)
    (hrel : FEnvRel fe0 lfe0) (hfe : FEnvWF fe0) (hfvs : ExprsWF fvs)
    (h : inductives.sum_install.field_doms_resolve_from fe0 fvs i = ok b) :
    b = ((absExprs fvs).drop i.val).all
      (fun x => x.fvarTypeD.constsResolveF lfe0) := by
  generalize hd : fvs.val.length - i.val = d
  induction d using Nat.strong_induction_on generalizing i b with
  | _ d ih =>
    rw [inductives.sum_install.field_doms_resolve_from.eq_def] at h
    simp only [] at h
    by_cases hi : i.val ≥ fvs.val.length
    · rw [if_pos (show i ≥ alloc.vec.Vec.len fvs by scalar_tac)] at h
      rw [List.drop_eq_nil_of_le (show (absExprs fvs).length ≤ i.val by
          simp [absExprs]; scalar_tac), ← Result.ok_injective h]
      simp
    · rw [if_neg (show ¬ i ≥ alloc.vec.Vec.len fvs by scalar_tac)] at h
      have hlt : i.val < fvs.val.length := by scalar_tac
      have hmax : i.val + 1 ≤ Std.Usize.max := by
        have := fvs.slice.property; scalar_tac
      obtain ⟨i1, hi1, hi1v⟩ := usize_add_ok hmax
      obtain ⟨y, hy, hyv⟩ :=
        WP.spec_imp_exists (alloc.vec.Vec.index_usize_spec fvs i hlt)
      subst hyv
      simp only [alloc.vec.Vec.index_slice_index, hy, bind_tc_ok] at h
      obtain ⟨dom, hdom, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨c, hc, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨habsd, hwfd⟩ :=
        ExprOps.fvar_type_d_refines (hfvs _ (List.getElem_mem hlt)) hdom
      have hcabs := hres fe0 lfe0 dom c hrel hfe hwfd hc
      rw [habsd] at hcabs
      rw [absExprs_drop_cons (xs := fvs) hlt, List.all_cons, ← hcabs]
      cases c with
      | false => rw [if_neg (by simp)] at h; simp [← Result.ok_injective h]
      | true =>
        rw [if_pos rfl] at h
        simp only [bind_eq_ok_iff] at h
        obtain ⟨i2, hi2, h⟩ := h
        have hi2v : i2.val = i.val + 1 := HashMap.uscalar_add_eq hi2
        rw [ih (fvs.val.length - i1.val) (by scalar_tac) h (by rw [hi2v, hi1v]),
          hi2v]
        simp

/-- `ConLeche/Kernel/Inductives/SumInstall.lean:207-253` and
`SumInstallF.lean:97-128` — `index_args_resolve_from` refines
`(xq.2.getAppArgs.drop nP).all fun e => e.constsResolveF fe₀` from index `i`:
the index expressions never mention the block (official
`is_valid_ind_app`). -/
theorem index_args_resolve_from_refines {fe0 : fenv.FEnv} {lfe0 : ConLeche.FEnv}
    {args : alloc.vec.Vec expr.Expr} {i : Std.Usize} {b : Bool}
    (hres : ConstsResolveFFastRefines)
    (hrel : FEnvRel fe0 lfe0) (hfe : FEnvWF fe0) (hargs : ExprsWF args)
    (h : inductives.sum_install.index_args_resolve_from fe0 args i = ok b) :
    b = ((absExprs args).drop i.val).all (fun e => e.constsResolveF lfe0) := by
  generalize hd : args.val.length - i.val = d
  induction d using Nat.strong_induction_on generalizing i b with
  | _ d ih =>
    rw [inductives.sum_install.index_args_resolve_from.eq_def] at h
    simp only [] at h
    by_cases hi : i.val ≥ args.val.length
    · rw [if_pos (show i ≥ alloc.vec.Vec.len args by scalar_tac)] at h
      rw [List.drop_eq_nil_of_le (show (absExprs args).length ≤ i.val by
          simp [absExprs]; scalar_tac), ← Result.ok_injective h]
      simp
    · rw [if_neg (show ¬ i ≥ alloc.vec.Vec.len args by scalar_tac)] at h
      have hlt : i.val < args.val.length := by scalar_tac
      have hmax : i.val + 1 ≤ Std.Usize.max := by
        have := args.slice.property; scalar_tac
      obtain ⟨i1, hi1, hi1v⟩ := usize_add_ok hmax
      obtain ⟨y, hy, hyv⟩ :=
        WP.spec_imp_exists (alloc.vec.Vec.index_usize_spec args i hlt)
      subst hyv
      simp only [alloc.vec.Vec.index_slice_index, hy, bind_tc_ok] at h
      obtain ⟨c, hc, h⟩ := bind_eq_ok_iff.mp h
      have hcabs := hres fe0 lfe0 _ c hrel hfe (hargs _ (List.getElem_mem hlt)) hc
      rw [absExprs_drop_cons (xs := args) hlt, List.all_cons, ← hcabs]
      cases c with
      | false => rw [if_neg (by simp)] at h; simp [← Result.ok_injective h]
      | true =>
        rw [if_pos rfl] at h
        simp only [bind_eq_ok_iff] at h
        obtain ⟨i2, hi2, h⟩ := h
        have hi2v : i2.val = i.val + 1 := HashMap.uscalar_add_eq hi2
        rw [ih (args.val.length - i1.val) (by scalar_tac) h (by rw [hi2v, hi1v]),
          hi2v]
        simp

/-- `ConLeche/Kernel/Inductives/SumInstall.lean:207-253` and
`SumInstallF.lean:97-128` — `check_sum_ctor` refines `checkSumCtorF`: stage 2,
one constructor's type — the ordinary constant check, the normalised
constructor, the annotated result shape, the parameter pins against the type
former's opened telescope, the pre-block resolution of the field domains, and
the per-field universe bound.  Returns the annotated constructor and its
fields' sorts. -/
theorem check_sum_ctor_refines {mode : env.CheckMode}
    (hw : Core.Wrappers mode IndAbs.checkFuelU) (hcv : CheckConstantValRefines mode)
    (hmc : MentionsConstRefines) (hop : OpenPisAtFvarsFRefines)
    (hft : FvarTypesRefines) (hdoms : CheckStructDomsAtRefines mode)
    (hresid : StructCtorResidOkRefines) (hpo : ParamsOfRefines)
    (hres : ConstsResolveFFastRefines)
    {st st' : cached.state_c.CState} {fe0 fe : fenv.FEnv} {lfe0 : ConLeche.FEnv}
    {t : name.Name} {lps : alloc.vec.Vec name.Name} {n_p n_idx n_f : Std.U64}
    {res_sort : level.Level} {is_prop large : Bool}
    {cv_c cv_ta cv_ca : env.ConstantVal} {sorts : alloc.vec.Vec level.Level}
    (hst : StateWF st) (hfe0 : FEnvWF fe0) (hfe : FEnvWF fe)
    (hrel0 : FEnvRel fe0 lfe0) (ht : NameWF t) (hlps : NamesWF lps)
    (hsort : LevelWF res_sort) (hcvc : ConstantValWF cv_c)
    (hcvta : ConstantValWF cv_ta)
    (h : inductives.sum_install.check_sum_ctor mode st fe0 fe t lps n_p n_idx
        res_sort is_prop large cv_c n_f cv_ta = ok (.Ok (cv_ca, sorts), st')) :
    ∀ lst lfe, StateRel st lst → FEnvRel fe lfe →
      ∃ lst', (ConLeche.checkSumCtorF (m := ConLeche.Cached.CheckCM)
            (ConLeche.Cached.sharedOpsC (absMode mode) lfe) lfe0 lfe (absName t)
            (absNames lps) n_p.val n_idx.val (absLevel res_sort) is_prop large
            (absConstantVal cv_c) n_f.val (absConstantVal cv_ta)).run lst
          = .ok ((absConstantVal cv_ca, absLevels sorts), lst')
        ∧ StateRel st' lst' ∧ StateWF st'
        ∧ ConstantValWF cv_ca ∧ LevelsWF sorts := by
  -- the eight stages, in the cited order
  sorry

/-- `ConLeche/Kernel/Inductives/SumInstall.lean:255-267` and
`SumInstallF.lean:130-140` — `check_sum_ctors` refines `checkSumCtorsF`: stage
2 for every constructor, at the environment holding the type former alone.
The two accumulators are pushed on the way in (task #13's pattern 3), so they
stand in front of what the cited walk conses on the way out. -/
theorem check_sum_ctors_refines {mode : env.CheckMode}
    (hw : Core.Wrappers mode IndAbs.checkFuelU) (hcv : CheckConstantValRefines mode)
    (hmc : MentionsConstRefines) (hop : OpenPisAtFvarsFRefines)
    (hft : FvarTypesRefines) (hdoms : CheckStructDomsAtRefines mode)
    (hresid : StructCtorResidOkRefines) (hpo : ParamsOfRefines)
    (hres : ConstsResolveFFastRefines)
    {st st' : cached.state_c.CState} {fe0 fe : fenv.FEnv} {lfe0 : ConLeche.FEnv}
    {t : name.Name} {lps : alloc.vec.Vec name.Name} {n_p n_idx : Std.U64}
    {res_sort : level.Level} {is_prop large : Bool} {cv_ta : env.ConstantVal}
    {cs out r : alloc.vec.Vec (env.ConstantVal × Std.U64)} {i : Std.Usize}
    {souts sr : alloc.vec.Vec (alloc.vec.Vec level.Level)}
    (hst : StateWF st) (hfe0 : FEnvWF fe0) (hfe : FEnvWF fe)
    (hrel0 : FEnvRel fe0 lfe0) (ht : NameWF t) (hlps : NamesWF lps)
    (hsort : LevelWF res_sort) (hcvta : ConstantValWF cv_ta)
    (hcs : ∀ c ∈ cs.val, ConstantValWF c.1)
    (hout : ∀ c ∈ out.val, ConstantValWF c.1)
    (hsouts : ∀ us ∈ souts.val, LevelsWF us)
    (h : inductives.sum_install.check_sum_ctors mode st fe0 fe t lps n_p n_idx
        res_sort is_prop large cv_ta cs i out souts = ok (.Ok (r, sr), st')) :
    ∀ lst lfe, StateRel st lst → FEnvRel fe lfe →
      ∃ lst' lcs lss,
        (ConLeche.checkSumCtorsF (m := ConLeche.Cached.CheckCM)
            (ConLeche.Cached.sharedOpsC (absMode mode) lfe) lfe0 lfe (absName t)
            (absNames lps) n_p.val n_idx.val (absLevel res_sort) is_prop large
            (absConstantVal cv_ta) ((IndAbs.absCtors cs).drop i.val)).run lst
          = .ok ((lcs, lss), lst')
        ∧ IndAbs.absCtors r = IndAbs.absCtors out ++ lcs
        ∧ IndAbs.absLevelss sr = IndAbs.absLevelss souts ++ lss
        ∧ StateRel st' lst' ∧ StateWF st'
        ∧ (∀ c ∈ r.val, ConstantValWF c.1) ∧ (∀ us ∈ sr.val, LevelsWF us) := by
  -- the index recursion on `cs.len() - i`; Aeneas's `partial_fixpoint`
  sorry

/-- `ConLeche/Kernel/Inductives/SumInstall.lean:269-272` and
`SumInstallF.lean:142-145` — `cons_sum_ctors` refines `consSumCtorsF`: the
constructors' pushes, in order (the first constructor deepest).  The index is
threaded by value and returned (task #14), so the result is the pushed index —
abstracted relationally. -/
theorem cons_sum_ctors_refines {n_p : Std.U64}
    {cs : alloc.vec.Vec (env.ConstantVal × Std.U64)} {i : Std.Usize}
    {fe fe' : fenv.FEnv} {lfe : ConLeche.FEnv}
    (hrel : FEnvRel fe lfe) (hfe : FEnvWF fe)
    (hcs : ∀ c ∈ cs.val, ConstantValWF c.1)
    (h : inductives.sum_install.cons_sum_ctors n_p cs i fe = ok fe') :
    FEnvRel fe' (ConLeche.consSumCtorsF n_p.val ((IndAbs.absCtors cs).drop i.val) lfe)
      ∧ FEnvWF fe' := by
  generalize hd : cs.val.length - i.val = d
  induction d using Nat.strong_induction_on generalizing i fe lfe with
  | _ d ih =>
    rw [inductives.sum_install.cons_sum_ctors.eq_def] at h
    simp only [] at h
    by_cases hi : i.val ≥ cs.val.length
    · rw [if_pos (show i ≥ alloc.vec.Vec.len cs by scalar_tac)] at h
      rw [List.drop_eq_nil_of_le (show (IndAbs.absCtors cs).length ≤ i.val by
          simp [IndAbs.absCtors]; scalar_tac), ← Result.ok_injective h]
      exact ⟨hrel, hfe⟩
    · rw [if_neg (show ¬ i ≥ alloc.vec.Vec.len cs by scalar_tac)] at h
      have hlt : i.val < cs.val.length := by scalar_tac
      have hmax : i.val + 1 ≤ Std.Usize.max := by
        have := cs.slice.property; scalar_tac
      obtain ⟨i1, hi1, hi1v⟩ := usize_add_ok hmax
      obtain ⟨y, hy, hyv⟩ :=
        WP.spec_imp_exists (alloc.vec.Vec.index_usize_spec cs i hlt)
      subst hyv
      simp only [alloc.vec.Vec.index_slice_index, hy, bind_tc_ok] at h
      obtain ⟨cv1, hcv1, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨fe2, hfe2, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨i2, hi2, h⟩ := bind_eq_ok_iff.mp h
      have hi2v : i2.val = i.val + 1 := HashMap.uscalar_add_eq hi2
      have hcvw : ConstantValWF cs.val[i.val].1 := hcs _ (List.getElem_mem hlt)
      rw [Env.constant_val_dup_refines hcv1] at hfe2
      obtain ⟨hrel2, hwf2⟩ := FEnv.push_refines hrel hfe (by exact hcvw) hfe2
      have hstep := ih (cs.val.length - i1.val) (by scalar_tac) hrel2 hwf2 h
        (by rw [hi2v, hi1v])
      rw [absCtors_drop_cons (cs := cs) hlt, ConLeche.consSumCtorsF]
      rw [hi2v] at hstep
      exact hstep

/-! ## The stored rules (`SumInstall.lean:274-290`) -/

/-- `ConLeche/Kernel/Inductives/SumInstall.lean:274-290` — `sum_rules_from`
refines `sumRules` at the constructors and right-hand sides from `i` on, with
the port's accumulator in front of what the cited walk conses on the way out.
Deviations: the `find? : Name → Option ConstantInfo` argument is the index
itself (`fe`), and the two-list recursion is an index recursion whose "one list
ran out" arm is the cited `| _, _ => []`. -/
theorem sum_rules_from_refines {fe : fenv.FEnv} {lfe : ConLeche.FEnv}
    {rec_name : name.Name} {n_p m_i r_p : Std.U64} {rec_ty : expr.Expr}
    {cs : alloc.vec.Vec (env.ConstantVal × Std.U64)}
    {rhss : alloc.vec.Vec expr.Expr} {i : Std.Usize}
    {out v : alloc.vec.Vec env.RecRule}
    (hrel : FEnvRel fe lfe) (hfe : FEnvWF fe) (hrec : NameWF rec_name)
    (hty : ExprWF rec_ty) (hcs : ∀ c ∈ cs.val, ConstantValWF c.1)
    (hrhss : ExprsWF rhss) (hout : RecRulesWF out)
    (h : inductives.sum_install.sum_rules_from fe rec_name n_p m_i r_p rec_ty
        cs rhss i out = ok v) :
    absRecRules v
        = absRecRules out
          ++ ConLeche.sumRules lfe.find? (absName rec_name) n_p.val m_i.val
              r_p.val (absExpr rec_ty) ((IndAbs.absCtors cs).drop i.val)
              ((absExprs rhss).drop i.val)
      ∧ RecRulesWF v := by
  have hag : FindAgree fe lfe := FindAgree.of_rel hrel hfe
  have hfw : FindWF fe := FindWF.of_wf hfe
  generalize hd : cs.val.length - i.val = d
  induction d using Nat.strong_induction_on generalizing i out with
  | _ d ih =>
    rw [inductives.sum_install.sum_rules_from.eq_def] at h
    simp only [] at h
    by_cases hi : i.val ≥ cs.val.length
    · rw [if_pos (show i ≥ alloc.vec.Vec.len cs by scalar_tac)] at h
      rw [List.drop_eq_nil_of_le (show (IndAbs.absCtors cs).length ≤ i.val by
          simp [IndAbs.absCtors]; scalar_tac), ← Result.ok_injective h]
      exact ⟨by simp [ConLeche.sumRules], hout⟩
    · rw [if_neg (show ¬ i ≥ alloc.vec.Vec.len cs by scalar_tac)] at h
      by_cases hj : i.val ≥ rhss.val.length
      · rw [if_pos (show i ≥ alloc.vec.Vec.len rhss by scalar_tac)] at h
        rw [List.drop_eq_nil_of_le (show (absExprs rhss).length ≤ i.val by
            simp [absExprs]; scalar_tac), ← Result.ok_injective h]
        refine ⟨?_, hout⟩
        rcases hcsl : (IndAbs.absCtors cs).drop i.val with _ | ⟨c0, cl⟩ <;>
          simp [ConLeche.sumRules]
      · rw [if_neg (show ¬ i ≥ alloc.vec.Vec.len rhss by scalar_tac)] at h
        have hlt : i.val < cs.val.length := by scalar_tac
        have hlt2 : i.val < rhss.val.length := by scalar_tac
        have hmax : i.val + 1 ≤ Std.Usize.max := by
          have := cs.slice.property; scalar_tac
        obtain ⟨i1, hi1, hi1v⟩ := usize_add_ok hmax
        obtain ⟨b, hb, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨fire, hfire, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨y, hy, hyv⟩ :=
          WP.spec_imp_exists (alloc.vec.Vec.index_usize_spec cs i hlt)
        subst hyv
        simp only [alloc.vec.Vec.index_slice_index, hy, bind_tc_ok] at h
        obtain ⟨n, hn, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨z, hz, hzv⟩ :=
          WP.spec_imp_exists (alloc.vec.Vec.index_usize_spec rhss i hlt2)
        subst hzv
        simp only [hz, bind_tc_ok] at h
        obtain ⟨e1, he1, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨rr, hrr, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨out1, hout1, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨i2, hi2, h⟩ := bind_eq_ok_iff.mp h
        have hi2v : i2.val = i.val + 1 := HashMap.uscalar_add_eq hi2
        have hcvw : ConstantValWF cs.val[i.val].1 := hcs _ (List.getElem_mem hlt)
        have hbabs := ExprOps.rec_rule_plain_refines hty hb
        have hnv : n = cs.val[i.val].1.name := by
          simp only [name_dup_eq, Result.ok.injEq] at hn; exact hn.symm
        have he1v : e1 = rhss.val[i.val] := Expr.dup_eq he1
        have hfireabs : absFire fire
            = (if (absExpr rec_ty).recRulePlain m_i.val r_p.val n_p.val then
                ConLeche.RecRuleFire.plain else ConLeche.RecRuleFire.inert) := by
          rw [← hbabs]
          cases b with
          | true => rw [if_pos rfl] at hfire; rw [← Result.ok_injective hfire]; rfl
          | false => rw [if_neg (by simp)] at hfire; rw [← Result.ok_injective hfire]; rfl
        have hfirewf : RecRuleFireWF fire := by
          cases b with
          | true => rw [if_pos rfl] at hfire; rw [← Result.ok_injective hfire]; trivial
          | false => rw [if_neg (by simp)] at hfire; rw [← Result.ok_injective hfire]; trivial
        have hrlwf : RecRuleWF
            { ctor := n, nfields := cs.val[i.val].2, ctor_params := n_p,
              fire := fire, rhs := e1, k := false, eta := false,
              params_blind := true } :=
          ⟨by rw [hnv]; exact hcvw.1, hfirewf,
            by rw [he1v]; exact hrhss _ (List.getElem_mem hlt2)⟩
        obtain ⟨hrrabs, hrrwf⟩ :=
          CoreK.rec_rule_bits_refines CoreK.envFacts hag hfw hrec hrlwf hrr
        have hout1wf : RecRulesWF out1 := by
          intro q hq
          rw [vec_push_val hout1, List.mem_append] at hq
          rcases hq with hq | hq
          · exact hout q hq
          · rw [List.mem_singleton.mp hq]; exact hrrwf
        obtain ⟨habs, hwf⟩ := ih (cs.val.length - i1.val) (by scalar_tac)
          hout1wf h (by rw [hi2v, hi1v])
        refine ⟨?_, hwf⟩
        rw [habs, hi2v,
          absCtors_drop_cons (cs := cs) hlt,
          absExprs_drop_cons (xs := rhss) hlt2]
        have hout1abs : absRecRules out1 = absRecRules out ++ [absRecRule rr] := by
          rw [absRecRules, vec_push_val hout1]
          simp [absRecRules]
        rw [ConLeche.sumRules, hout1abs, hrrabs, List.append_assoc,
          List.singleton_append]
        simp only [absRecRule, hnv, he1v, hfireabs, absConstantVal]

/-- `ConLeche/Kernel/Inductives/SumInstall.lean:274-290` — `sum_rules` refines
`sumRules`: the entry point, where the accumulator is empty. -/
theorem sum_rules_refines {fe : fenv.FEnv} {lfe : ConLeche.FEnv}
    {rec_name : name.Name} {n_p m_i r_p : Std.U64} {rec_ty : expr.Expr}
    {cs : alloc.vec.Vec (env.ConstantVal × Std.U64)}
    {rhss : alloc.vec.Vec expr.Expr} {v : alloc.vec.Vec env.RecRule}
    (hrel : FEnvRel fe lfe) (hfe : FEnvWF fe) (hrec : NameWF rec_name)
    (hty : ExprWF rec_ty) (hcs : ∀ c ∈ cs.val, ConstantValWF c.1)
    (hrhss : ExprsWF rhss)
    (h : inductives.sum_install.sum_rules fe rec_name n_p m_i r_p rec_ty cs rhss
        = ok v) :
    absRecRules v
        = ConLeche.sumRules lfe.find? (absName rec_name) n_p.val m_i.val r_p.val
            (absExpr rec_ty) (IndAbs.absCtors cs) (absExprs rhss)
      ∧ RecRulesWF v := by
  rw [inductives.sum_install.sum_rules] at h
  have hnew : RecRulesWF (alloc.vec.Vec.new env.RecRule) := by
    intro r hr; simp [alloc.vec.Vec.new] at hr
  have := sum_rules_from_refines hrel hfe hrec hty hcs hrhss hnew h
  simpa [absRecRules, alloc.vec.Vec.new] using this

end ConRon.Refine.SumInstall
