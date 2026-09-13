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
| the former's telescope | `whnf_telescope`, `close_telescope`, `check_sum_tele`, `check_sum_tele_whnf`, `check_sum_ind` (with `check_sum_ind_canon`, the index-canonicity half `Refine/IndNativeInstall.lean` asks for as `CheckSumIndCanon`) |
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
* **Two `u64 → usize` narrowings** (`Refine/Scalars.lean`'s subject).
  `opened_resid_ok` compares `getAppArgs.take nP` through
  `expr_ops::take_exprs`, which indexes by `usize`, so the port writes
  `n_p as usize` where con-leche's `List.take` takes a `Nat`; and
  `check_struct_field_sorts_i` reads `fvs[(j - 1) as usize]` against a guard on
  the *cast*, where `checkStructFieldSortsIF` reads `fvs[j]?`.  Each carries
  the bound as its one extra hypothesis — `hnp : n_p.val ≤ Std.Usize.max`
  resp. `hj : j.val ≤ Std.Usize.max`.  Both are vacuous wherever
  `Usize.numBits = 64`, which is the only platform the crate is built for, and
  the model cannot prove them because Aeneas's `Usize` is
  `System.Platform`-dependent; on a 32-bit target the conclusions are
  genuinely false, so the hypotheses are not slack.  They are the only places
  in this file where the port's word sizes are visible in a statement, and
  **`check_sum_ctor_refines` — the one caller of both, and of
  `CheckStructDomsAtRefines`, which carries the same bound — discharges all
  three** from the `Vec`s that `open_pis_at_fvars_f` produced, whose lengths
  are `n_p` resp. `n_f` (`openPisAtFvarsF_length` and
  `Scalars.u64_le_usize_max_of_le_len`).

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

**No `sorry`.**  Task #59 closed all ten: `whnf_telescope`, `check_sum_tele`,
`check_sum_tele_whnf`, `check_sum_ind`, `check_struct_field_sorts_i`,
`norm_pos_dom`, `norm_field_doms`, `norm_ctor_val`, `check_sum_ctor` and
`check_sum_ctors`.  Aeneas emits the recursive ones as `partial_fixpoint`
definitions; each is unfolded with its own equation and a strong induction on
the *measure* the recursion decreases (`n.val`, `fuel.val`, `j.val`,
`cs.len() - i`), with the peel-one-entry step supplied by the three list
helpers `absExprs_drop_cons`/`absBinders_drop_cons`/`absCtors_drop_cons`.  The
three non-recursive ones (`check_sum_ind`, `norm_ctor_val`, `check_sum_ctor`)
are compositions of those.

The `## The cited walks, one step at a time` section below is the other half of
each proof: one `.run lst` equation per clause of the cited con-leche
definition (`ConLeche.Cached.CheckCM` is `StateT CState (Except CheckError)`,
so `.run` of a bind is the bind of the `.run`s — `run_bind`).  Matching the
port's own bind chain against those clauses is what every state-touching proof
here does.  `openPisAtFvars_length` and `checkStructFieldSortsIFA_eq` are
con-leche's own facts (`Model/Inductives/StructBits.lean` resp.
`Verify/CheckerF.lean`), restated locally because those modules are not
imported; `ConLeche.Verify.FastOps` *is* imported, for `openPisAtFvarsF_eq`
(`normCtorValF` and `checkSumCtorF` spell `openPisAtFvars` where the port calls
`open_pis_at_fvars_f`) and `checkStructDomsAtFA_eq`.

Two statements are ordered against the Rust for a dependency: the port-only
split `check_sum_tele_whnf` is proved *before* `check_sum_tele`, which calls
it, and `norm_ctor_val` *after* the binder helpers `zip_param_binders` and
`append_binders` it composes.
-/
import ConRon.Refine.IndAbs
import ConRon.Refine.IndSumParts
import ConRon.Refine.ExprOpsSpine
import ConRon.Refine.ExprOpsSubst
import ConRon.Refine.CoreKVec
import ConRon.Refine.CoreKPinned
import ConLeche.Verify.FastOps

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
`Refine/IndStructInstall.lean`** (`check_struct_doms_at_refines`).

`j.val ≤ Std.Usize.max` is that lemma's one side condition: the port guards on
`(j as usize) >= fvs.len()`, i.e. on the *cast*, so a wrapped counter would
pass a guard `checkStructDomsAtF`'s `fvs[j]?` answers `none` at.  It is vacuous
wherever `Usize.numBits = 64`, and `check_sum_ctor_refines` — the one caller
here — discharges it from the `Vec` of opened parameter variables, whose length
is `n_p`. -/
def CheckStructDomsAtRefines (mode : env.CheckMode) : Prop :=
  ∀ (st st' : cached.state_c.CState) (fe : fenv.FEnv) (off j : Std.U64)
    (fvs doms : alloc.vec.Vec expr.Expr),
    StateWF st → FEnvWF fe → ExprsWF fvs → ExprsWF doms →
    j.val ≤ Std.Usize.max →
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


/-! ## The cited walks, one step at a time -/

section Steps

variable {ops : ConLeche.CheckerOps ConLeche.Cached.CheckCM}

/-- `.run` of a bind, in the state monad the drivers use. -/
theorem run_bind {α β : Type} {x : ConLeche.Cached.CheckCM α}
    {f : α → ConLeche.Cached.CheckCM β} {lst : ConLeche.Cached.CState} :
    (x >>= f).run lst = (x.run lst).bind fun p => (f p.1).run p.2 := rfl

/-- `whnfTelescope` at `n = 0`, when the whnf'd residual is a sort. -/
theorem whnfTelescope_zero {lenv : ConLeche.Env} {i : Nat} {e : ConLeche.Expr}
    {lst lst1 : ConLeche.Cached.CState} {s : ConLeche.Level}
    (h : (ops.whnf lenv i e).run lst = .ok (.sort s, lst1)) :
    (ConLeche.whnfTelescope ops lenv i 0 e).run lst = .ok (([], s), lst1) := by
  rw [ConLeche.whnfTelescope, run_bind, h]
  rfl

/-- `whnfTelescope` at `n + 1`, when the whnf'd residual is a Π. -/
theorem whnfTelescope_succ {lenv : ConLeche.Env} {i n : Nat}
    {e dom body : ConLeche.Expr} {bm : ConLeche.BinderMeta}
    {bs : List (ConLeche.Expr × ConLeche.BinderMeta)} {s : ConLeche.Level}
    {lst lst1 lst2 : ConLeche.Cached.CState}
    (h : (ops.whnf lenv i e).run lst = .ok (.forallE dom body bm, lst1))
    (hr : (ConLeche.whnfTelescope ops lenv (i + 1) n
            (body.instantiate1 (.fvar i dom))).run lst1 = .ok ((bs, s), lst2)) :
    (ConLeche.whnfTelescope ops lenv i (n + 1) e).run lst
      = .ok (((dom, bm) :: bs, s), lst2) := by
  rw [ConLeche.whnfTelescope, run_bind, h]
  simp only [Except.bind]
  rw [run_bind, hr]
  rfl

/-- `checkStructFieldSortsIF` at an exhausted counter. -/
theorem checkStructFieldSortsIF_zero {lfe : ConLeche.FEnv} {isProp large : Bool}
    {s : ConLeche.Level} {nP : Nat} {fvs idxArgs : List ConLeche.Expr}
    {lst : ConLeche.Cached.CState} :
    (ConLeche.checkStructFieldSortsIF ops lfe isProp large s nP fvs idxArgs 0).run lst
      = .ok ([], lst) := rfl

/-- `checkStructFieldSortsIF`'s step, at a field whose guard passed.  The two
guard hypotheses are the cited `unless`es, each under the branch that reaches
it: the universe bound off a propositional family, and the
subsingleton-elimination criterion at a `Prop` family with a large
eliminator. -/
theorem checkStructFieldSortsIF_succ {lfe : ConLeche.FEnv} {isProp large : Bool}
    {s u : ConLeche.Level} {nP j : Nat} {fvs idxArgs : List ConLeche.Expr}
    {fv ty : ConLeche.Expr} {rest : List ConLeche.Level}
    {lst lst1 lst2 lst3 : ConLeche.Cached.CState}
    (hfv : fvs[j]? = some fv)
    (hty : (ops.inferType lfe.env (nP + j) fv.fvarTypeD).run lst = .ok (ty, lst1))
    (hu : (ops.ensureSort lfe.env (nP + j) ty).run lst1 = .ok (u, lst2))
    (hleq : isProp = false → ConLeche.Level.leq u s = some true)
    (helim : isProp = true → large = true →
      (ConLeche.Level.isEquiv u .zero == some true || idxArgs.contains fv) = true)
    (hrest : (ConLeche.checkStructFieldSortsIF ops lfe isProp large s nP fvs
        idxArgs j).run lst2 = .ok (rest, lst3)) :
    (ConLeche.checkStructFieldSortsIF ops lfe isProp large s nP fvs idxArgs
        (j + 1)).run lst = .ok (rest ++ [u], lst3) := by
  rw [ConLeche.checkStructFieldSortsIF]
  simp only [ConLeche.unwrapOr, hfv, StateT.run, Bind.bind, StateT.bind,
    Except.bind, Pure.pure, StateT.pure, Except.pure]
  rw [show (ops.inferType lfe.env (nP + j) fv.fvarTypeD) lst = Except.ok (ty, lst1) from hty]
  simp only []
  rw [show (ops.ensureSort lfe.env (nP + j) ty) lst1 = Except.ok (u, lst2) from hu]
  simp only []
  cases isProp with
  | false =>
    simp [ConLeche.liftFueled, hleq rfl, Bind.bind, StateT.bind, Except.bind, Pure.pure,
      StateT.pure, Except.pure,
      show (ConLeche.checkStructFieldSortsIF ops lfe false large s nP fvs idxArgs j) lst2
        = Except.ok (rest, lst3) from hrest]
  | true =>
    cases large with
    | false =>
      simp [Bind.bind, StateT.bind, Except.bind, Pure.pure, StateT.pure, Except.pure,
        show (ConLeche.checkStructFieldSortsIF ops lfe true false s nP fvs idxArgs j) lst2
          = Except.ok (rest, lst3) from hrest]
    | true =>
      have hh : ConLeche.Level.isEquiv u .zero = some true ∨ fv ∈ idxArgs := by
        simpa using helim rfl rfl
      simp [hh, Bind.bind, StateT.bind, Except.bind, Pure.pure, StateT.pure, Except.pure,
        show (ConLeche.checkStructFieldSortsIF ops lfe true true s nP fvs idxArgs j) lst2
          = Except.ok (rest, lst3) from hrest]

/-- `normPosDom` at a domain the block does not occur in: kept as declared. -/
theorem normPosDom_keep {lenv : ConLeche.Env} {T : ConLeche.Name} {d fuel : Nat}
    {e : ConLeche.Expr} {lst : ConLeche.Cached.CState}
    (he : e.mentionsConst T = false) :
    (ConLeche.normPosDom ops lenv T d (fuel + 1) e).run lst = .ok (e, lst) := by
  rw [ConLeche.normPosDom]
  simp [he, StateT.run, Pure.pure, StateT.pure, Except.pure]

/-- `normPosDom` at a residual the whnf'd form does not mention the block in. -/
theorem normPosDom_whnf {lenv : ConLeche.Env} {T : ConLeche.Name} {d fuel : Nat}
    {e w : ConLeche.Expr} {lst lst1 : ConLeche.Cached.CState}
    (he : e.mentionsConst T = true)
    (hw : (ops.whnf lenv d e).run lst = .ok (w, lst1))
    (hwm : w.mentionsConst T = false) :
    (ConLeche.normPosDom ops lenv T d (fuel + 1) e).run lst = .ok (w, lst1) := by
  rw [ConLeche.normPosDom]
  simp only [he, Bool.not_true, Bool.false_eq_true, if_false, StateT.run,
    Bind.bind, StateT.bind, Except.bind, Pure.pure]
  rw [show (ops.whnf lenv d e) lst = Except.ok (w, lst1) from hw]
  simp only [hwm, Bool.not_false, if_true]
  rfl

/-- `normPosDom` at a whnf'd residual that is not a Π: returned as reduced. -/
theorem normPosDom_nonpi {lenv : ConLeche.Env} {T : ConLeche.Name} {d fuel : Nat}
    {e w : ConLeche.Expr} {lst lst1 : ConLeche.Cached.CState}
    (he : e.mentionsConst T = true)
    (hw : (ops.whnf lenv d e).run lst = .ok (w, lst1))
    (hwm : w.mentionsConst T = true)
    (hnp : ∀ dom body bm, w ≠ .forallE dom body bm) :
    (ConLeche.normPosDom ops lenv T d (fuel + 1) e).run lst = .ok (w, lst1) := by
  rw [ConLeche.normPosDom]
  simp only [he, Bool.not_true, Bool.false_eq_true, if_false, StateT.run,
    Bind.bind, StateT.bind, Except.bind, Pure.pure]
  rw [show (ops.whnf lenv d e) lst = Except.ok (w, lst1) from hw]
  simp only [hwm, Bool.not_true, Bool.false_eq_true, if_false]
  cases w with
  | forallE dom body bm => exact absurd rfl (hnp dom body bm)
  | _ => rfl

/-- `normPosDom` under a Π binder of a reflexive field. -/
theorem normPosDom_pi {lenv : ConLeche.Env} {T : ConLeche.Name} {d fuel : Nat}
    {e dom body body' : ConLeche.Expr} {bm : ConLeche.BinderMeta}
    {lst lst1 lst2 : ConLeche.Cached.CState}
    (he : e.mentionsConst T = true)
    (hw : (ops.whnf lenv d e).run lst = .ok (.forallE dom body bm, lst1))
    (hwm : (ConLeche.Expr.forallE dom body bm).mentionsConst T = true)
    (hdm : dom.mentionsConst T = false)
    (hrec : (ConLeche.normPosDom ops lenv T (d + 1) fuel
        (body.instantiate1 (.fvar d dom))).run lst1 = .ok (body', lst2)) :
    (ConLeche.normPosDom ops lenv T d (fuel + 1) e).run lst
      = .ok (.forallE dom (body'.abstract1 d) bm, lst2) := by
  rw [ConLeche.normPosDom]
  simp only [he, Bool.not_true, Bool.false_eq_true, if_false, StateT.run,
    Bind.bind, StateT.bind, Except.bind, Pure.pure]
  rw [show (ops.whnf lenv d e) lst = Except.ok (ConLeche.Expr.forallE dom body bm, lst1)
    from hw]
  simp only [hwm, Bool.not_true, Bool.false_eq_true, if_false, hdm, StateT.bind,
    Bind.bind, Except.bind]
  rw [show (ConLeche.normPosDom ops lenv T (d + 1) fuel
      (body.instantiate1 (ConLeche.Expr.fvar d dom))) lst1 = Except.ok (body', lst2)
    from hrec]
  rfl

/-- `normFieldDoms` at an exhausted counter. -/
theorem normFieldDoms_zero {lenv : ConLeche.Env} {T : ConLeche.Name} {i : Nat}
    {e : ConLeche.Expr} {lst : ConLeche.Cached.CState} :
    (ConLeche.normFieldDoms ops lenv T i 0 e).run lst = .ok (([], e), lst) := rfl

/-- `normFieldDoms`' step: one field binder, its domain normalised. -/
theorem normFieldDoms_succ {lenv : ConLeche.Env} {T : ConLeche.Name} {i n : Nat}
    {dom body dom' r : ConLeche.Expr} {bm : ConLeche.BinderMeta}
    {bs : List (ConLeche.Expr × ConLeche.BinderMeta)}
    {lst lst1 lst2 : ConLeche.Cached.CState}
    (hd : (ConLeche.normPosDom ops lenv T i 1024 dom).run lst = .ok (dom', lst1))
    (hrec : (ConLeche.normFieldDoms ops lenv T (i + 1) n
        (body.instantiate1 (.fvar i dom))).run lst1 = .ok ((bs, r), lst2)) :
    (ConLeche.normFieldDoms ops lenv T i (n + 1) (.forallE dom body bm)).run lst
      = .ok (((dom', bm) :: bs, r), lst2) := by
  rw [ConLeche.normFieldDoms]
  simp only [StateT.run, Bind.bind, StateT.bind, Except.bind, Pure.pure,
    StateT.pure, Except.pure]
  rw [show (ConLeche.normPosDom ops lenv T i 1024 dom) lst = Except.ok (dom', lst1)
    from hd]
  simp only []
  rw [show (ConLeche.normFieldDoms ops lenv T (i + 1) n
      (body.instantiate1 (ConLeche.Expr.fvar i dom))) lst1 = Except.ok ((bs, r), lst2)
    from hrec]

/-- `checkSumCtorsF` at an exhausted list. -/
theorem checkSumCtorsF_nil {lfe0 lfe : ConLeche.FEnv} {T : ConLeche.Name}
    {lps : List ConLeche.Name} {nP nIdx : Nat} {resSort : ConLeche.Level}
    {isProp large : Bool} {cvTa : ConLeche.ConstantVal}
    {lst : ConLeche.Cached.CState} :
    (ConLeche.checkSumCtorsF ops lfe0 lfe T lps nP nIdx resSort isProp large
        cvTa []).run lst = .ok (([], []), lst) := rfl

/-- `checkSumCtorsF`' step: one constructor, then the rest. -/
theorem checkSumCtorsF_cons {lfe0 lfe : ConLeche.FEnv} {T : ConLeche.Name}
    {lps : List ConLeche.Name} {nP nIdx : Nat} {resSort : ConLeche.Level}
    {isProp large : Bool} {cvTa cvCa : ConLeche.ConstantVal}
    {c : ConLeche.ConstantVal × Nat} {cs rest : List (ConLeche.ConstantVal × Nat)}
    {sorts : List ConLeche.Level} {srest : List (List ConLeche.Level)}
    {lst lst1 lst2 : ConLeche.Cached.CState}
    (h1 : (ConLeche.checkSumCtorF ops lfe0 lfe T lps nP nIdx resSort isProp large
        c.1 c.2 cvTa).run lst = .ok ((cvCa, sorts), lst1))
    (h2 : (ConLeche.checkSumCtorsF ops lfe0 lfe T lps nP nIdx resSort isProp large
        cvTa cs).run lst1 = .ok ((rest, srest), lst2)) :
    (ConLeche.checkSumCtorsF ops lfe0 lfe T lps nP nIdx resSort isProp large
        cvTa (c :: cs)).run lst
      = .ok (((cvCa, c.2) :: rest, sorts :: srest), lst2) := by
  rw [ConLeche.checkSumCtorsF, run_bind, h1]
  simp only [Except.bind]
  rw [run_bind, h2]
  rfl

/-- `openPisAtFvars` returns exactly `n` free variables.  (con-leche's own
`openPisAtFvars_length` lives in `ConLeche/Model/Inductives/StructBits.lean`,
which this file does not import; the induction is three lines.) -/
theorem openPisAtFvars_length :
    ∀ (n : Nat) {e : ConLeche.Expr} {d : Nat} {fvs : List ConLeche.Expr}
      {o : ConLeche.Expr},
      ConLeche.openPisAtFvars n e d = some (fvs, o) → fvs.length = n
  | 0, e, d, fvs, o, h => by
    simp only [ConLeche.openPisAtFvars, Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.1]; rfl
  | n + 1, e, d, fvs, o, h => by
    match e, h with
    | .forallE dom body mb, h =>
      simp only [ConLeche.openPisAtFvars] at h
      split at h
      · next fvs' e' h' =>
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        rw [← h.1, List.length_cons, openPisAtFvars_length n h']
      · exact nomatch h
    | .bvar _, h => simp [ConLeche.openPisAtFvars] at h
    | .fvar _ _, h => simp [ConLeche.openPisAtFvars] at h
    | .sort _, h => simp [ConLeche.openPisAtFvars] at h
    | .const _ _, h => simp [ConLeche.openPisAtFvars] at h
    | .app _ _, h => simp [ConLeche.openPisAtFvars] at h
    | .lam _ _ _, h => simp [ConLeche.openPisAtFvars] at h
    | .letE _ _ _, h => simp [ConLeche.openPisAtFvars] at h
    | .lit _, h => simp [ConLeche.openPisAtFvars] at h
    | .proj _ _ _, h => simp [ConLeche.openPisAtFvars] at h

/-- The same at the one-pass spelling the port calls. -/
theorem openPisAtFvarsF_length {n : Nat} {e : ConLeche.Expr} {d : Nat}
    {fvs : List ConLeche.Expr} {o : ConLeche.Expr}
    (h : ConLeche.openPisAtFvarsF n e d = some (fvs, o)) : fvs.length = n :=
  openPisAtFvars_length n (by rw [← ConLeche.openPisAtFvarsF_eq]; exact h)

/-- `checkStructFieldSortsIFA` at `List.toArray` is `checkStructFieldSortsIF`
(con-leche's `checkStructFieldSortsIFA_eq`, `ConLeche/Verify/CheckerF.lean:285`,
restated here: that module is not imported). -/
theorem checkStructFieldSortsIFA_eq (lfe : ConLeche.FEnv) (isProp large : Bool)
    (s : ConLeche.Level) (nP : Nat) (fvs idxArgs : List ConLeche.Expr) :
    ∀ j, ConLeche.checkStructFieldSortsIFA ops lfe isProp large s nP
        fvs.toArray idxArgs j
      = ConLeche.checkStructFieldSortsIF ops lfe isProp large s nP fvs idxArgs j
  | 0 => rfl
  | j + 1 => by
    simp only [ConLeche.checkStructFieldSortsIFA, ConLeche.checkStructFieldSortsIF,
      List.getElem?_toArray,
      checkStructFieldSortsIFA_eq lfe isProp large s nP fvs idxArgs j]

/-- `checkSumCtorF`'s eight stages, spelled as one `.run` equation: the shape
the port's own bind chain is matched against.  The two `Array` twins are
carried across by con-leche's `checkStructDomsAtFA_eq` and by
`checkStructFieldSortsIFA_eq` above. -/
theorem checkSumCtorF_run {lfe0 lfe : ConLeche.FEnv} {T : ConLeche.Name}
    {lps : List ConLeche.Name} {nP nIdx nF : Nat} {resSort : ConLeche.Level}
    {isProp large : Bool} {cvC cvTa cvCa0 cvCa : ConLeche.ConstantVal}
    {cbs : List (ConLeche.Expr × ConLeche.BinderMeta)} {cbody : ConLeche.Expr}
    {cq1 tq1 xq1 : List ConLeche.Expr} {cq2 tq2 xq2 : ConLeche.Expr}
    {sorts : List ConLeche.Level}
    {lst lst1 lst2 lst3 lst4 : ConLeche.Cached.CState}
    (h0 : (ConLeche.checkConstantValF ops lfe cvC).run lst = .ok (cvCa0, lst1))
    (h1 : (ConLeche.normCtorValF ops lfe T nP nF cvC cvCa0).run lst1
      = .ok (cvCa, lst2))
    (hstrip : cvCa.type.stripPis (nP + nF) = some (cbs, cbody))
    (hresid : ConLeche.structCtorResidOk T lps nP nF nIdx cbody = true)
    (hcq : ConLeche.openPisAtFvarsF nP cvCa.type 0 = some (cq1, cq2))
    (htq : ConLeche.openPisAtFvarsF nP cvTa.type 0 = some (tq1, tq2))
    (hdoms : (ConLeche.checkStructDomsAtF ops lfe 0 cq1
        (tq1.map ConLeche.Expr.fvarTypeD) nP).run lst2 = .ok ((), lst3))
    (hxq : ConLeche.openPisAtFvarsF nF cq2 nP = some (xq1, xq2))
    (hg1 : (xq2.getAppFn == ConLeche.Expr.const T (lps.map .param)
        && xq2.getAppArgs.take nP == cq1
        && xq2.getAppArgs.length == nP + nIdx) = true)
    (hg2 : (xq1.all fun x => x.fvarTypeD.constsResolveF lfe0) = true)
    (hg3 : ((xq2.getAppArgs.drop nP).all fun e => e.constsResolveF lfe0) = true)
    (hs : (ConLeche.checkStructFieldSortsIF ops lfe isProp large resSort nP xq1
        (xq2.getAppArgs.drop nP) nF).run lst3 = .ok (sorts, lst4)) :
    (ConLeche.checkSumCtorF ops lfe0 lfe T lps nP nIdx resSort isProp large cvC
        nF cvTa).run lst = .ok ((cvCa, sorts), lst4) := by
  rw [ConLeche.checkSumCtorF]
  simp only [StateT.run, Bind.bind, StateT.bind, Except.bind, Pure.pure]
  rw [show (ConLeche.checkConstantValF ops lfe cvC) lst = Except.ok (cvCa0, lst1)
    from h0]
  simp only []
  rw [show (ConLeche.normCtorValF ops lfe T nP nF cvC cvCa0) lst1
    = Except.ok (cvCa, lst2) from h1]
  simp only [ConLeche.unwrapOr, hstrip, hcq, htq, Bind.bind,
    StateT.bind, Except.bind, Pure.pure, StateT.pure, Except.pure, hresid,
    if_true, ConLeche.checkStructDomsAtFA_eq]
  rw [show (ConLeche.checkStructDomsAtF ops lfe 0 cq1
      (tq1.map ConLeche.Expr.fvarTypeD) nP) lst2 = Except.ok ((), lst3) from hdoms]
  simp only [hxq, Bind.bind, StateT.bind,
    Except.bind, Pure.pure, StateT.pure, Except.pure, hg1, hg2, hg3, if_true,
    checkStructFieldSortsIFA_eq]
  rw [show (ConLeche.checkStructFieldSortsIF ops lfe isProp large resSort nP xq1
      (xq2.getAppArgs.drop nP) nF) lst3 = Except.ok (sorts, lst4) from hs]

end Steps

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
  generalize hd : n.val = d
  induction d using Nat.strong_induction_on generalizing st st' i n e out bs u with
  | _ d ih =>
  subst hd
  intro lst lfe hrel hfer
  rw [inductives.sum_install.whnf_telescope] at h
  simp only [IndAbs.check_fuel_eq, bind_tc_ok] at h
  obtain ⟨p, hp, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨r, st1⟩ := p
  cases r with
  | Err err => simp at h
  | Ok w =>
    obtain ⟨lst1, hrun, hrel1, hwf1, hwe⟩ :=
      IndAbs.ops_whnf hw hst hfe he hp lst lfe hrel hfer
    obtain ⟨⟨dd, k⟩⟩ := w
    by_cases hn0 : n = 0#u64
    · -- the last residual: a sort, and the accumulator is the answer
      subst hn0
      cases k
      case «Sort» s =>
        simp at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        refine ⟨lst1, [], ?_, by simp, hrel1, hwf1, hout, IndAbs.sort_node_wf hwe⟩
        simpa using whnfTelescope_zero (by simpa using hrun)
      all_goals simp at h
    · -- one more binder: peel it and recurse
      cases k
      case ForallE dom body bm =>
        obtain ⟨hdom, hbody, hbm⟩ := CoreK.ExprWF.forallE_children hwe rfl
        simp only [if_neg hn0] at h
        simp at h
        obtain ⟨fv, hfv, opened, hopened, bm1, hbm1, out1, hout1, i2, hi2, i3, hi3, h⟩ := h
        have hfvwf : ExprWF fv := Expr.fvar_wf hdom hfv
        have hfvabs : absExpr fv = .fvar i.val (absExpr dom) := Expr.fvar_refines hfv
        obtain ⟨hoabs, howf⟩ := ExprOps.instantiate1_refines hbody hfvwf hopened
        have hbm1v : bm1 = bm := Expr.binder_meta_dup_eq hbm1
        have hi2v : i2.val = i.val + 1 := HashMap.uscalar_add_eq hi2
        have hi3v : i3.val = n.val - 1 := HashMap.uscalar_sub_eq hi3
        have hnpos : 1 ≤ n.val := by scalar_tac
        have hout1wf : ExprOps.BindersWF out1 :=
          ExprOps.bindersWF_push hout hdom (by rw [hbm1v]; exact hbm) hout1
        obtain ⟨lst2, lbs, hrun2, habs2, hrel2, hwf2, hbswf, huwf⟩ :=
          ih i3.val (by omega) hwf1 howf hout1wf h rfl lst1 lfe hrel1 hfer
        refine ⟨lst2, (absExpr dom, absBinderMeta bm) :: lbs, ?_, ?_,
          hrel2, hwf2, hbswf, huwf⟩
        · rw [show n.val = i3.val + 1 by omega]
          refine whnfTelescope_succ (by simpa using hrun) ?_
          simpa [hi2v, hoabs, hfvabs] using hrun2
        · rw [habs2, ExprOps.absBinders_push hout1, hbm1v]
          simp
      all_goals simp [hn0] at h

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
  intro lst lfe hrel hfer
  rw [inductives.sum_install.check_sum_tele_whnf] at h
  obtain ⟨p, hp, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨r, st1⟩ := p
  cases r with
  | Err err => simp at h
  | Ok q =>
    obtain ⟨v, l⟩ := q
    simp at h
    obtain ⟨e1, he1, closed, hclosed, lp, hlp, a, b, hccv, h⟩ := h
    obtain ⟨lst1, lbs, hrun1, habs1, hrel1, hwf1, hvwf, hlwf⟩ :=
      whnf_telescope_refines hw hst hfe hcv0.2.2 ExprOps.bindersWF_new hp lst lfe hrel hfer
    have he1wf : ExprWF e1 := Expr.sort_wf hlwf he1
    have he1abs : absExpr e1 = .sort (absLevel l) := Expr.sort_refines he1
    obtain ⟨hclabs, hclwf⟩ := close_telescope_refines hvwf he1wf hclosed
    have hlpv : lp.val = cv.level_params.val := PropWhen.names_copy_val hlp
    have hlpwf : NamesWF lp := by
      intro q hq; rw [hlpv] at hq; exact hcvwf.2.1 q hq
    have habs1' : ExprOps.absBinders v = lbs := by simpa using habs1
    have hcv2wf : ConstantValWF
        { «name» := cv.name, level_params := lp, ty := closed } :=
      ⟨hcvwf.1, hlpwf, hclwf⟩
    have hcv2abs : absConstantVal { «name» := cv.name, level_params := lp, ty := closed }
        = { absConstantVal cv with
            type := ConLeche.closeTelescope lbs 0 (.sort (absLevel l)) } := by
      rw [absConstantVal, absConstantVal, hclabs, he1abs, habs1']
      simp [absNames, hlpv]
    cases a with
    | Err err => simp at h
    | Ok cv_ta1 =>
      simp only [Result.ok.injEq, core.result.Result.Ok.injEq, Prod.mk.injEq] at h
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
      obtain ⟨lst2, hrun2, hrel2, hwf2, hcvtawf⟩ :=
        hcv st1 b fe _ _ hwf1 hfe hcv2wf hccv lst1 lfe hrel1 hfer
      rw [hcv2abs] at hrun2
      have hrun1' : (ConLeche.whnfTelescope (m := ConLeche.Cached.CheckCM)
            (ConLeche.Cached.sharedOpsC (absMode mode) lfe) (absEnv fe.env) 0 n.val
            (absConstantVal cv_ta0).type).run lst = .ok ((lbs, absLevel l), lst1) := by
        simpa [absConstantVal] using hrun1
      refine ⟨lst2, ?_, hrel2, hwf2, hcvtawf, hlwf⟩
      rw [run_bind, hrun1']
      simp only [Except.bind]
      rw [run_bind, hrun2]
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
  intro lst lfe hrel hfer
  rw [inductives.sum_install.check_sum_tele] at h
  obtain ⟨o, ho, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨hoabs, howf⟩ := ExprOps.strip_pis_refines hcv0.2.2 ho
  cases o with
  | none =>
    have hstrip : (absConstantVal cv_ta0).type.stripPis n.val = none := by
      simpa [absConstantVal] using hoabs.symm
    have h' : inductives.sum_install.check_sum_tele_whnf mode st fe cv n cv_ta0
        = ok (.Ok (cv_ta, u), st') := h
    obtain ⟨lst', hrun, hrel', hwf', hcvta, hu⟩ :=
      check_sum_tele_whnf_refines hw hcv hst hfe hcvwf hcv0 h' lst lfe hrel hfer
    refine ⟨lst', ?_, hrel', hwf', hcvta, hu⟩
    rw [ConLeche.checkSumTeleF, hstrip, ← hfer.1]
    exact hrun
  | some q =>
    obtain ⟨bs, e0⟩ := q
    have hstrip : (absConstantVal cv_ta0).type.stripPis n.val
        = some (ExprOps.absBinders bs, absExpr e0) := by
      simpa [absConstantVal] using hoabs.symm
    obtain ⟨hbswf, he0wf⟩ := howf _ rfl
    obtain ⟨⟨dd, k⟩⟩ := e0
    simp at h
    cases k
    case «Sort» s =>
      simp at h
      obtain ⟨hcv1, rfl, rfl⟩ := h
      rw [Env.constant_val_dup_refines hcv1]
      refine ⟨lst, ?_, hrel, hst, hcv0, IndAbs.sort_node_wf he0wf⟩
      rw [ConLeche.checkSumTeleF, show (absConstantVal cv_ta0).type.stripPis n.val
          = some (ExprOps.absBinders bs, ConLeche.Expr.sort (absLevel s)) from
        by simpa using hstrip]
      rfl
    all_goals
      (simp at h
       obtain ⟨lst', hrun, hrel', hwf', hcvta, hu⟩ :=
          check_sum_tele_whnf_refines hw hcv hst hfe hcvwf hcv0 h lst lfe hrel hfer
       refine ⟨lst', ?_, hrel', hwf', hcvta, hu⟩
       rw [ConLeche.checkSumTeleF, hstrip, ← hfer.1]
       exact hrun)

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
  intro lst lfe hrel hfer
  rw [inductives.sum_install.check_sum_ind] at h
  obtain ⟨pp, hp0, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨r0, st1⟩ := pp
  cases r0 with
  | Err err => simp at h
  | Ok cv_ta0 =>
    simp at h
    obtain ⟨i, hi, a, b, htele, h⟩ := h
    cases a with
    | Err err => simp at h
    | Ok q =>
      obtain ⟨cv_ta', s⟩ := q
      simp at h
      obtain ⟨o, ho, h⟩ := h
      cases o with
      | none => simp at h
      | some tq =>
        obtain ⟨tbs, e⟩ := tq
        simp at h
        obtain ⟨e1, he1, hbeq, hws, caps, hcapsok, cvd, hcvd, hpush, rfl, rfl⟩ := h
        obtain ⟨lst1, hrun0, hrel1, hwf1, hcv0wf⟩ :=
          hcv st st1 fe p.cv_t cv_ta0 hst hfe hp.1 hp0 lst lfe hrel hfer
        have hiv : i.val = p.n_p.val + p.n_idx.val := HashMap.uscalar_add_eq hi
        obtain ⟨lst2, hrun1, hrel2, hwf2, hcvtawf, hswf⟩ :=
          check_sum_tele_refines hw hcv hwf1 hfe hp.1 hcv0wf htele lst1 lfe hrel1 hfer
        obtain ⟨hoabs, howf⟩ := ExprOps.strip_pis_refines hcvtawf.2.2 ho
        obtain ⟨htbswf, hewf⟩ := howf _ rfl
        have he1abs : absExpr e1 = .sort (absLevel s) := Expr.sort_refines he1
        have he1wf : ExprWF e1 := Expr.sort_wf hswf he1
        have hbeq' : absExpr e = ConLeche.Expr.sort (absLevel s) := by
          have := Expr.beq_refines hewf he1wf hbeq
          rw [he1abs] at this
          exact of_decide_eq_true this.symm
        have hp2wf : IndAbs.InductiveShapeWF p2 := by
          rw [inductives.sum_parts.with_sort] at hws
          obtain ⟨bb, hbb, hws⟩ := bind_eq_ok_iff.mp hws
          rw [← Result.ok_injective hws]
          exact ⟨hp.1, hp.2.1, hp.2.2.1, hp.2.2.2.1, hswf, hp.2.2.2.2.2⟩
        have hwsabs : IndAbs.absInductiveShape p2
            = (IndAbs.absInductiveShape p).withSort (absLevel s) :=
          SumParts.with_sort_refines hswf hws
        obtain ⟨hcapsabs, hcapswf⟩ := hcaps p2 caps hp2wf hcapsok
        rw [hwsabs] at hcapsabs
        rw [Env.constant_val_dup_refines hcvd] at hpush
        obtain ⟨hrelpush, hwfpush⟩ :=
          FEnv.push_refines hfer hfe (show ConstantInfoWF (.IndInfo cv_ta' caps) from
            ⟨hcvtawf, hcapswf⟩) hpush
        refine ⟨lst2, lfe.push (absConstantInfo (.IndInfo cv_ta' caps)), ?_,
          hrelpush, hwfpush, hrel2, hwf2, hcvtawf, hp2wf⟩
        have hstrip : (absConstantVal cv_ta').type.stripPis i.val
            = some (ExprOps.absBinders tbs, absExpr e) := by
          simpa [absConstantVal] using hoabs.symm
        rw [ConLeche.checkSumIndF,
          show (IndAbs.absInductiveShape p).cvT = absConstantVal p.cv_t from rfl,
          show (IndAbs.absInductiveShape p).nP + (IndAbs.absInductiveShape p).nIdx
            = i.val from by rw [hiv]; rfl,
          run_bind, hrun0]
        simp only [Except.bind]
        rw [run_bind, hrun1]
        simp only [Except.bind]
        simp only [hstrip, ConLeche.unwrapOr, hbeq']
        simp [StateT.run, Bind.bind, StateT.bind, Except.bind, Pure.pure,
          StateT.pure, Except.pure, hwsabs, hcapsabs, absConstantInfo]


/-- `check_sum_ind` keeps the **unrestricted-canonical** pair: its only index
step is the `fenv::push` of the type former onto the index it was handed, and
`FEnv.push_canon` is exactly that step.  This is
`Refine/IndNativeInstall.lean`'s `CheckSumIndCanon` ingredient.

`hfe2` is the one hypothesis beyond the three `FEnv` facts: `FEnv.push_canon`
needs `ConstantInfoWF` of what is pushed, which here is
`.IndInfo cv_ta (capsOf p₂)` — and `IndCapsWF` of the dictionary's record is
*not* a consequence of the port's code, it is what `CapsOfRefines` supplies.
Rather than drag the knot, `CheckConstantValRefines` and `CapsOfRefines` into a
statement that says nothing about abstraction, the well-formedness of the
*result* index is taken as given: every caller already has it, from
`check_sum_ind_refines`' (resp. `NativeInstall.CheckSumIndRefines`') own
`FEnvWF r.1` conjunct, and `EnvWF fe2.env` is where the pushed record's
`ConstantInfoWF` is read back off. -/
theorem check_sum_ind_canon {mode : env.CheckMode} {C : Type}
    {inst : inductives.sum_install.CapsOf C} {self : C}
    {st st' : cached.state_c.CState} {fe fe2 : fenv.FEnv}
    {p p2 : inductives.sum_parts.InductiveShape} {cv_ta : env.ConstantVal}
    (hfe : FEnvWF fe) (hcan : FEnv.FEnvCanon fe) (hfull : FEnv.FEnvFull fe)
    (h : inductives.sum_install.check_sum_ind inst mode st fe p self
        = ok (.Ok (fe2, cv_ta, p2), st'))
    (hfe2 : FEnvWF fe2) :
    FEnv.FEnvCanon fe2 ∧ FEnv.FEnvFull fe2 := by
  rw [inductives.sum_install.check_sum_ind] at h
  obtain ⟨pp, hp0, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨r0, st1⟩ := pp
  cases r0 with
  | Err err => simp at h
  | Ok cv_ta0 =>
    simp at h
    obtain ⟨i, hi, a, b, htele, h⟩ := h
    cases a with
    | Err err => simp at h
    | Ok q =>
      obtain ⟨cvTa, s⟩ := q
      simp at h
      obtain ⟨o, ho, h⟩ := h
      cases o with
      | none => simp at h
      | some tq =>
        obtain ⟨tbs, e⟩ := tq
        simp at h
        obtain ⟨e1, he1, hbeq, hws, caps, hcapsok, cvd, hcvd, hpush, hcveq, hsteq⟩ := h
        have hci : ConstantInfoWF (.IndInfo cvd caps) := by
          refine hfe2.env _ ?_
          rw [FEnv.push_consts hpush]
          simp
        exact FEnv.push_canon hfe hci hcan hfull hpush

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
`checkStructFieldSortsIFA_eq`.

`hj` is the second of this file's two `usize`-width side conditions
(`Refine/Scalars.lean`): the port's bound check is
`(j - 1) as usize >= fvs.len()`, i.e. on the *cast*, so on a target with
`Usize.numBits < 64` a wrapped counter passes a guard `fvs[j - 1]?` answers
`none` at, and the conclusion is then false — the hypothesis is not slack.  It
is vacuous wherever `Usize.numBits = 64`, and `check_sum_ctor_refines`, the one
caller, discharges it from `open_pis_at_fvars_f`'s field-variable `Vec`, whose
length is `n_f`. -/
theorem check_struct_field_sorts_i_refines {mode : env.CheckMode}
    (hw : Core.Wrappers mode IndAbs.checkFuelU)
    {st st' : cached.state_c.CState} {fe : fenv.FEnv} {is_prop large : Bool}
    {s : level.Level} {n_p j : Std.U64} {fvs idx_args : alloc.vec.Vec expr.Expr}
    {us : alloc.vec.Vec level.Level}
    (hst : StateWF st) (hfe : FEnvWF fe) (hs : LevelWF s)
    (hfvs : ExprsWF fvs) (hidx : ExprsWF idx_args) (hj : j.val ≤ Std.Usize.max)
    (h : inductives.sum_install.check_struct_field_sorts_i mode st fe is_prop
        large s n_p fvs idx_args j = ok (.Ok us, st')) :
    ∀ lst lfe, StateRel st lst → FEnvRel fe lfe →
      ∃ lst', (ConLeche.checkStructFieldSortsIF (m := ConLeche.Cached.CheckCM)
            (ConLeche.Cached.sharedOpsC (absMode mode) lfe) lfe is_prop large
            (absLevel s) n_p.val (absExprs fvs) (absExprs idx_args) j.val).run lst
          = .ok (absLevels us, lst')
        ∧ StateRel st' lst' ∧ StateWF st' ∧ LevelsWF us := by
  generalize hd : j.val = d
  induction d using Nat.strong_induction_on generalizing st st' j us with
  | _ d ih =>
  subst hd
  intro lst lfe hrel hfer
  rw [inductives.sum_install.check_struct_field_sorts_i] at h
  by_cases hj0 : j = 0#u64
  · subst hj0
    simp at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨lst, ?_, hrel, hst, ?_⟩
    · exact checkStructFieldSortsIF_zero
    · intro l hl; simp [alloc.vec.Vec.new] at hl
  · rw [if_neg hj0] at h
    simp at h
    obtain ⟨y, hy, h⟩ := h
    have hyv : y.val = j.val - 1 := HashMap.uscalar_sub_eq hy
    have hjpos : 1 ≤ j.val := by scalar_tac
    have hybound : y.val ≤ Std.Usize.max := by omega
    have hmod : y.val % 2 ^ System.Platform.numBits = y.val := by
      refine Nat.mod_eq_of_lt ?_
      have hmax : Std.Usize.max = 2 ^ System.Platform.numBits - 1 := by
        simp only [Std.Usize.max, Std.Usize.numBits, Std.UScalarTy.Usize_numBits_eq]
      have hpos : 0 < 2 ^ System.Platform.numBits := Nat.two_pow_pos _
      omega
    rw [hmod] at h
    by_cases hlt : y.val < fvs.val.length
    · rw [if_neg (by omega)] at h
      have hcast : (Std.UScalar.cast .Usize y : Std.Usize).val = y.val :=
        ExprOps.u64_cast_usize_val hybound
      obtain ⟨fv, hfv, hfvv⟩ := WP.spec_imp_exists
        (alloc.vec.Vec.index_usize_spec fvs (Std.UScalar.cast .Usize y)
          (by rw [hcast]; exact hlt))
      have hfveq : fv = fvs.val[y.val] := by rw [hfvv]; simp [hcast]
      simp only [hfv, bind_tc_ok] at h
      obtain ⟨dom, hdom, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨i5, hi5, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨pp, hinfer, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨r, st1⟩ := pp
      cases r with
      | Err err => simp at h
      | Ok ty =>
        simp at h
        obtain ⟨r1, st2, hens, h⟩ := h
        cases r1 with
        | Err err => simp at h
        | Ok u =>
          have hfvwf : ExprWF fv := by
            rw [hfveq]; exact hfvs _ (List.getElem_mem hlt)
          obtain ⟨hdomabs, hdomwf⟩ := ExprOps.fvar_type_d_refines hfvwf hdom
          have hi5v : i5.val = n_p.val + y.val := HashMap.uscalar_add_eq hi5
          obtain ⟨lst1, hrunty, hrel1, hwf1, htywf⟩ :=
            IndAbs.ops_infer hw hst hfe hdomwf hinfer lst lfe hrel hfer
          obtain ⟨lst2', hrunu, hrel2', hwf2', huwf⟩ :=
            IndAbs.ops_ensure_sort hw hwf1 hfe htywf hens lst1 lfe hrel1 hfer
          have hfvget : (absExprs fvs)[y.val]? = some (absExpr fv) := by
            rw [absExprs, List.getElem?_map,
              List.getElem?_eq_getElem (show y.val < fvs.val.length from hlt), hfveq]
            rfl
          have hrunty' : ((ConLeche.Cached.sharedOpsC (absMode mode) lfe).inferType
              lfe.env (n_p.val + y.val)
              (absExpr fv).fvarTypeD).run lst
              = .ok (absExpr ty, lst1) := by
            rw [← hfer.1, ← hdomabs, ← hi5v]; exact hrunty
          have hrunu' : ((ConLeche.Cached.sharedOpsC (absMode mode) lfe).ensureSort
              lfe.env (n_p.val + y.val) (absExpr ty)).run lst1
              = .ok (absLevel u, lst2') := by
            rw [← hfer.1, ← hi5v]; exact hrunu
          have hjsucc : j.val = y.val + 1 := by omega
          cases is_prop <;> cases large <;> simp at h
          case false.false =>
            obtain ⟨o, hlequ, r2, hlf, a, b, hg, h⟩ := h
            have hleqabs : ConLeche.Level.leq (absLevel u) (absLevel s) = o :=
              Level.leq_refines huwf hs hlequ
            cases b with
            | Err err => simp at h
            | Ok _ =>
              have hbb : r2 = .Ok true ∧ a = st2 := by
                cases r2 with
                | Err err => simp at hg
                | Ok bb =>
                  cases bb with
                  | false => simp at hg
                  | true => simp at hg; exact ⟨rfl, hg.symm⟩
              obtain ⟨hr2, rfl⟩ := hbb
              subst hr2
              have hosome : o = some true := by
                cases o with
                | none => simp [core_k.lift_fueled] at hlf
                | some c => simpa [core_k.lift_fueled] using hlf
              simp at h
              obtain ⟨r3, st4, hrec, hfin⟩ := h
              cases r3 with
              | Err err => simp at hfin
              | Ok rest =>
                simp at hfin
                obtain ⟨hpush, rfl⟩ := hfin
                obtain ⟨lst3, hrun3, hrel3, hwf3, hrestwf⟩ :=
                  ih y.val (by omega) hwf2' (by omega) hrec rfl lst2' lfe hrel2' hfer
                refine ⟨lst3, ?_, hrel3, hwf3, ?_⟩
                · rw [hjsucc, absLevels, vec_push_val hpush, List.map_append]
                  exact checkStructFieldSortsIF_succ hfvget hrunty' hrunu'
                    (fun _ => by rw [hleqabs, hosome]) (by simp) hrun3
                · intro l hl
                  rw [vec_push_val hpush, List.mem_append] at hl
                  rcases hl with hl | hl
                  · exact hrestwf l hl
                  · rw [List.mem_singleton.mp hl]; exact huwf
          case false.true =>
            obtain ⟨o, hlequ, r2, hlf, a, b, hg, h⟩ := h
            have hleqabs : ConLeche.Level.leq (absLevel u) (absLevel s) = o :=
              Level.leq_refines huwf hs hlequ
            cases b with
            | Err err => simp at h
            | Ok _ =>
              have hbb : r2 = .Ok true ∧ a = st2 := by
                cases r2 with
                | Err err => simp at hg
                | Ok bb =>
                  cases bb with
                  | false => simp at hg
                  | true => simp at hg; exact ⟨rfl, hg.symm⟩
              obtain ⟨hr2, rfl⟩ := hbb
              subst hr2
              have hosome : o = some true := by
                cases o with
                | none => simp [core_k.lift_fueled] at hlf
                | some c => simpa [core_k.lift_fueled] using hlf
              simp at h
              obtain ⟨r3, st4, hrec, hfin⟩ := h
              cases r3 with
              | Err err => simp at hfin
              | Ok rest =>
                simp at hfin
                obtain ⟨hpush, rfl⟩ := hfin
                obtain ⟨lst3, hrun3, hrel3, hwf3, hrestwf⟩ :=
                  ih y.val (by omega) hwf2' (by omega) hrec rfl lst2' lfe hrel2' hfer
                refine ⟨lst3, ?_, hrel3, hwf3, ?_⟩
                · rw [hjsucc, absLevels, vec_push_val hpush, List.map_append]
                  exact checkStructFieldSortsIF_succ hfvget hrunty' hrunu'
                    (fun _ => by rw [hleqabs, hosome]) (by simp) hrun3
                · intro l hl
                  rw [vec_push_val hpush, List.mem_append] at hl
                  rcases hl with hl | hl
                  · exact hrestwf l hl
                  · rw [List.mem_singleton.mp hl]; exact huwf

          case true.false =>
            obtain ⟨r2, st4, hrec, hfin⟩ := h
            cases r2 with
            | Err err => simp at hfin
            | Ok rest =>
              simp at hfin
              obtain ⟨hpush, rfl⟩ := hfin
              obtain ⟨lst3, hrun3, hrel3, hwf3, hrestwf⟩ :=
                ih y.val (by omega) hwf2' (by omega) hrec rfl lst2' lfe hrel2' hfer
              refine ⟨lst3, ?_, hrel3, hwf3, ?_⟩
              · rw [hjsucc, absLevels, vec_push_val hpush, List.map_append]
                exact checkStructFieldSortsIF_succ hfvget hrunty' hrunu'
                  (by simp) (by simp) hrun3
              · intro l hl
                rw [vec_push_val hpush, List.mem_append] at hl
                rcases hl with hl | hl
                · exact hrestwf l hl
                · rw [List.mem_singleton.mp hl]; exact huwf
          case true.true =>
            obtain ⟨z, hz, o, hiseq, a, hg, r3, st4, hrec, hfin⟩ := h
            have hzabs : absLevel z = .zero := Level.zero_refines hz
            have hzwf : LevelWF z := Level.zero_wf hz
            have hiseqabs : ConLeche.Level.isEquiv (absLevel u) ConLeche.Level.zero = o := by
              rw [← hzabs]; exact Level.is_equiv_refines huwf hzwf hiseq
            have hgok : a = st2 ∧ (ConLeche.Level.isEquiv (absLevel u) ConLeche.Level.zero
                == some true || (absExprs idx_args).contains (absExpr fv)) = true := by
              cases o with
              | none =>
                simp at hg
                refine ⟨hg.2.symm, ?_⟩
                rw [hiseqabs]
                simpa using (exprs_contains_refines hidx hfvwf hg.1).symm
              | some bb =>
                cases bb with
                | false =>
                  simp at hg
                  refine ⟨hg.2.symm, ?_⟩
                  rw [hiseqabs]
                  simpa using (exprs_contains_refines hidx hfvwf hg.1).symm
                | true =>
                  simp at hg
                  refine ⟨hg.symm, ?_⟩
                  rw [hiseqabs]
                  simp
            obtain ⟨rfl, helimok⟩ := hgok
            cases r3 with
            | Err err => simp at hfin
            | Ok rest =>
              simp at hfin
              obtain ⟨hpush, rfl⟩ := hfin
              obtain ⟨lst3, hrun3, hrel3, hwf3, hrestwf⟩ :=
                ih y.val (by omega) hwf2' (by omega) hrec rfl lst2' lfe hrel2' hfer
              refine ⟨lst3, ?_, hrel3, hwf3, ?_⟩
              · rw [hjsucc, absLevels, vec_push_val hpush, List.map_append]
                exact checkStructFieldSortsIF_succ hfvget hrunty' hrunu'
                  (by simp) (fun _ _ => helimok) hrun3
              · intro l hl
                rw [vec_push_val hpush, List.mem_append] at hl
                rcases hl with hl | hl
                · exact hrestwf l hl
                · rw [List.mem_singleton.mp hl]; exact huwf
    · rw [if_pos (by omega)] at h
      simp at h

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
  generalize hd : fuel.val = d0
  induction d0 using Nat.strong_induction_on generalizing st st' d fuel e r with
  | _ d0 ih =>
  subst hd
  intro lst lfe hrel hfer
  rw [inductives.sum_install.norm_pos_dom] at h
  have hfsucc : ∀ k : Std.U64, ¬ k = 0#u64 → k.val = (k.val - 1) + 1 := by
    intro k hk; have : 1 ≤ k.val := by scalar_tac
    omega
  by_cases hf0 : fuel = 0#u64
  · subst hf0; simp at h
  · rw [if_neg hf0] at h
    have hfpos : 1 ≤ fuel.val := by scalar_tac
    obtain ⟨b, hb, h⟩ := bind_eq_ok_iff.mp h
    have hbabs : b = (absExpr e).mentionsConst (absName t) := hmc t e b ht he hb
    cases b with
    | false =>
      rw [if_neg (by simp)] at h
      simp at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨lst, ?_, hrel, hst, he⟩
      rw [hfsucc fuel hf0]
      exact normPosDom_keep hbabs.symm
    | true =>
      rw [if_pos rfl] at h
      simp only [IndAbs.check_fuel_eq, bind_tc_ok] at h
      obtain ⟨pp, hwhnf, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨r0, st1⟩ := pp
      cases r0 with
      | Err err => simp at h
      | Ok w =>
        obtain ⟨lst1, hrunw, hrel1, hwf1, hwwf⟩ :=
          IndAbs.ops_whnf hw hst hfe he hwhnf lst lfe hrel hfer
        simp at h
        rcases h with ⟨hb1, rfl, rfl⟩ | ⟨hb1, h⟩
        · have hb1abs := hmc t w false ht hwwf hb1
          refine ⟨lst1, ?_, hrel1, hwf1, hwwf⟩
          rw [hfsucc fuel hf0]
          exact normPosDom_whnf hbabs.symm hrunw hb1abs.symm
        · have hb1abs := hmc t w true ht hwwf hb1
          clear hb1 hwhnf
          obtain ⟨⟨dd, k⟩⟩ := w
          simp only [ExprOps.node_kind] at h
          cases k
          case ForallE dom body bm =>
            obtain ⟨hdomwf, hbodywf, hbmwf⟩ := CoreK.ExprWF.forallE_children hwwf rfl
            simp at h
            obtain ⟨hb2, bm2, hbm2, fv, hfv, opened, hopened, i1, hi1, i2, hi2,
              r1, st2, hrec, hfin⟩ := h
            have hb2abs := hmc t dom false ht hdomwf hb2
            have hbm2v : bm2 = bm := Expr.binder_meta_dup_eq hbm2
            have hfvwf : ExprWF fv := Expr.fvar_wf hdomwf hfv
            have hfvabs : absExpr fv = .fvar d.val (absExpr dom) := Expr.fvar_refines hfv
            obtain ⟨hoabs, howf⟩ := ExprOps.instantiate1_refines hbodywf hfvwf hopened
            have hi1v : i1.val = d.val + 1 := HashMap.uscalar_add_eq hi1
            have hi2v : i2.val = fuel.val - 1 := HashMap.uscalar_sub_eq hi2
            cases r1 with
            | Err err => simp at hfin
            | Ok body2 =>
              simp at hfin
              obtain ⟨e1, he1, he2, rfl⟩ := hfin
              obtain ⟨lst2, hrun2, hrel2, hwf2, hbody2wf⟩ :=
                ih i2.val (by omega) hwf1 howf hrec rfl lst1 lfe hrel1 hfer
              obtain ⟨he1abs, he1wf⟩ := ExprOps.abstract1_refines hbody2wf he1
              refine ⟨lst2, ?_, hrel2, hwf2,
                Expr.forall_e_wf hdomwf he1wf (by rw [hbm2v]; exact hbmwf) he2⟩
              rw [Expr.forall_e_refines he2, he1abs, hbm2v, hfsucc fuel hf0]
              refine normPosDom_pi hbabs.symm (by simpa using hrunw)
                (by simpa using hb1abs.symm) hb2abs.symm ?_
              simpa [hi1v, hi2v, hoabs, hfvabs] using hrun2
          all_goals
            (simp at h
             obtain ⟨rfl, rfl⟩ := h
             refine ⟨lst1, ?_, hrel1, hwf1, hwwf⟩
             rw [hfsucc fuel hf0]
             exact normPosDom_nonpi hbabs.symm hrunw hb1abs.symm (by intro a b c; simp))

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
  generalize hd : n.val = d0
  induction d0 using Nat.strong_induction_on generalizing st st' i n e out bs resid with
  | _ d0 ih =>
  subst hd
  intro lst lfe hrel hfer
  rw [inductives.sum_install.norm_field_doms] at h
  by_cases hn0 : n = 0#u64
  · subst hn0
    simp at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact ⟨lst, [], by simpa using normFieldDoms_zero, by simp, hrel, hst, hout, he⟩
  · rw [if_neg hn0] at h
    have hnpos : 1 ≤ n.val := by scalar_tac
    obtain ⟨⟨dd, k⟩⟩ := e
    simp only [arc_deref_eq, bind_tc_ok, ExprOps.node_kind] at h
    cases k
    case ForallE dom body bm =>
      obtain ⟨hdomwf, hbodywf, hbmwf⟩ := CoreK.ExprWF.forallE_children he rfl
      obtain ⟨pp, hnpd, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨r0, st1⟩ := pp
      cases r0 with
      | Err err => simp at h
      | Ok dom2 =>
        obtain ⟨lst1, hrund, hrel1, hwf1, hdom2wf⟩ :=
          norm_pos_dom_refines hw hmc hst hfe ht hdomwf hnpd lst lfe hrel hfer
        simp at h
        obtain ⟨fv, hfv, opened, hopened, bm1, hbm1, out1, hout1, i1, hi1, i2, hi2, h⟩ := h
        have hfvwf : ExprWF fv := Expr.fvar_wf hdomwf hfv
        have hfvabs : absExpr fv = .fvar i.val (absExpr dom) := Expr.fvar_refines hfv
        obtain ⟨hoabs, howf⟩ := ExprOps.instantiate1_refines hbodywf hfvwf hopened
        have hbm1v : bm1 = bm := Expr.binder_meta_dup_eq hbm1
        have hi1v : i1.val = i.val + 1 := HashMap.uscalar_add_eq hi1
        have hi2v : i2.val = n.val - 1 := HashMap.uscalar_sub_eq hi2
        have hout1wf : ExprOps.BindersWF out1 :=
          ExprOps.bindersWF_push hout hdom2wf (by rw [hbm1v]; exact hbmwf) hout1
        obtain ⟨lst2, lbs, hrun2, habs2, hrel2, hwf2, hbswf, hrwf⟩ :=
          ih i2.val (by omega) hwf1 howf hout1wf h rfl lst1 lfe hrel1 hfer
        refine ⟨lst2, (absExpr dom2, absBinderMeta bm) :: lbs, ?_, ?_,
          hrel2, hwf2, hbswf, hrwf⟩
        · rw [show n.val = i2.val + 1 by omega]
          refine normFieldDoms_succ (by simpa using hrund) ?_
          simpa [hi1v, hoabs, hfvabs] using hrun2
        · rw [habs2, ExprOps.absBinders_push hout1, hbm1v]
          simp
    all_goals simp at h

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
  intro lst lfe hrel hfer
  rw [inductives.sum_install.norm_ctor_val] at h
  obtain ⟨o, ho, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨hoabs, howf⟩ := ExprOps.strip_pis_refines hcvca.2.2 ho
  cases o with
  | none => simp at h
  | some cq =>
    obtain ⟨cbs, crest0⟩ := cq
    obtain ⟨hcbswf, -⟩ := howf _ rfl
    simp at h
    obtain ⟨o1, ho1, h⟩ := h
    obtain ⟨ho1abs, ho1wf⟩ := hop n_p cv_ca.ty 0#u64 o1 hcvca.2.2 ho1
    cases o1 with
    | none => simp at h
    | some oq =>
      obtain ⟨fvsP, crest⟩ := oq
      obtain ⟨hfvsPwf, hcrestwf⟩ := ho1wf _ rfl
      simp at h
      obtain ⟨pbs, hzip, r0, st1, hnfd, h⟩ := h
      cases r0 with
      | Err err => simp at h
      | Ok fq =>
        obtain ⟨fbs, resid⟩ := fq
        obtain ⟨hpbsabs, hpbswf⟩ := zip_param_binders_refines hfvsPwf hcbswf hzip
        obtain ⟨lst1, lfbs, hrunfd, hfbsabs, hrel1, hwf1, hfbswf, hresidwf⟩ :=
          norm_field_doms_refines hw hmc hst hfe ht hcrestwf ExprOps.bindersWF_new
            hnfd lst lfe hrel hfer
        simp at h
        obtain ⟨all, hall, ty2, hclose, hcase⟩ := h
        obtain ⟨hallabs, hallwf⟩ := append_binders_refines hpbswf hfbswf hall
        obtain ⟨hty2abs, hty2wf⟩ := close_telescope_refines hallwf hresidwf hclose
        have hfbsabs' : ExprOps.absBinders fbs = lfbs := by simpa using hfbsabs
        have hstrip : (absConstantVal cv_ca).type.stripPis n_p.val
            = some (ExprOps.absBinders cbs, absExpr crest0) := by
          simpa [absConstantVal] using hoabs.symm
        have hopen : ConLeche.openPisAtFvars n_p.val (absConstantVal cv_ca).type 0
            = some (absExprs fvsP, absExpr crest) := by
          rw [← ConLeche.openPisAtFvarsF_eq]
          simpa [absConstantVal] using ho1abs.symm
        set lty : ConLeche.Expr :=
          ConLeche.closeTelescope
            (List.zipWith
                (fun (x : ConLeche.Expr) (bq : ConLeche.Expr × ConLeche.BinderMeta) =>
                  (x.fvarTypeD, bq.2)) (absExprs fvsP) (ExprOps.absBinders cbs)
              ++ lfbs) 0 (absExpr resid) with hlty
        have hty2abs' : absExpr ty2 = lty := by
          rw [hty2abs, hlty]
          simp [hallabs, hpbsabs, hfbsabs']
        have hrunhead : (ConLeche.normCtorValF (m := ConLeche.Cached.CheckCM)
              (ConLeche.Cached.sharedOpsC (absMode mode) lfe) lfe (absName t) n_p.val
              n_f.val (absConstantVal cv_c) (absConstantVal cv_ca)).run lst
            = ((if lty == (absConstantVal cv_ca).type then
                  (pure (absConstantVal cv_ca) : ConLeche.Cached.CheckCM _)
                else ConLeche.checkConstantValF
                  (ConLeche.Cached.sharedOpsC (absMode mode) lfe) lfe
                  { absConstantVal cv_c with type := lty }).run lst1) := by
          rw [ConLeche.normCtorValF, ← hfer.1]
          simp only [ConLeche.unwrapOr, hstrip, hopen, StateT.run, Bind.bind,
            StateT.bind, Except.bind, Pure.pure, StateT.pure, Except.pure]
          rw [show (ConLeche.normFieldDoms (m := ConLeche.Cached.CheckCM)
              (ConLeche.Cached.sharedOpsC (absMode mode) lfe) (absEnv fe.env)
              (absName t) n_p.val n_f.val (absExpr crest)) lst
              = Except.ok ((lfbs, absExpr resid), lst1) from hrunfd]
        rcases hcase with ⟨hbeq, lp, hlp, hccv⟩ | ⟨hbeq, hdup, rfl⟩
        · have hbeqabs := Expr.beq_refines hty2wf hcvca.2.2 hbeq
          rw [hty2abs'] at hbeqabs
          have hne : (lty == (absConstantVal cv_ca).type) = false := by
            simpa [absConstantVal] using hbeqabs.symm
          have hlpv : lp.val = cv_c.level_params.val := PropWhen.names_copy_val hlp
          have hlpwf : NamesWF lp := by
            intro q hq; rw [hlpv] at hq; exact hcvc.2.1 q hq
          have hcv2abs : absConstantVal
              { «name» := cv_c.name, level_params := lp, ty := ty2 }
              = { absConstantVal cv_c with type := lty } := by
            rw [absConstantVal, absConstantVal, hty2abs']
            simp [absNames, hlpv]
          obtain ⟨lst2, hrun2, hrel2, hwf2, hrwf⟩ :=
            hcv st1 st' fe { «name» := cv_c.name, level_params := lp, ty := ty2 } r
              hwf1 hfe ⟨hcvc.1, hlpwf, hty2wf⟩ hccv lst1 lfe hrel1 hfer
          rw [hcv2abs] at hrun2
          refine ⟨lst2, ?_, hrel2, hwf2, hrwf⟩
          rw [hrunhead, hne]
          simpa using hrun2
        · have hbeqabs := Expr.beq_refines hty2wf hcvca.2.2 hbeq
          rw [hty2abs'] at hbeqabs
          have heq : (lty == (absConstantVal cv_ca).type) = true := by
            simpa [absConstantVal] using hbeqabs.symm
          rw [Env.constant_val_dup_refines hdup]
          refine ⟨lst1, ?_, hrel1, hwf1, hcvca⟩
          rw [hrunhead, heq]
          rfl

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
  intro lst lfe hrel hfer
  rw [inductives.sum_install.check_sum_ctor] at h
  obtain ⟨pp, hccv0, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨r0, st1⟩ := pp
  cases r0 with
  | Err err => simp at h
  | Ok cv_ca0 =>
    obtain ⟨lst1, hrun0, hrel1, hwf1, hcvca0wf⟩ :=
      hcv st st1 fe cv_c cv_ca0 hst hfe hcvc hccv0 lst lfe hrel hfer
    simp at h
    obtain ⟨r1, st2, hnorm, h⟩ := h
    cases r1 with
    | Err err => simp at h
    | Ok cvCa =>
      obtain ⟨lst2, hrun1, hrel2, hwf2, hcvcawf⟩ :=
        norm_ctor_val_refines hw hcv hmc hop hwf1 hfe ht hcvc hcvca0wf hnorm
          lst1 lfe hrel1 hfer
      simp at h
      obtain ⟨i, hi, o, ho, h⟩ := h
      cases o with
      | none => simp at h
      | some bq =>
        obtain ⟨bbs, cbody⟩ := bq
        simp at h
        obtain ⟨hb, o1, ho1, h⟩ := h
        cases o1 with
        | none => simp at h
        | some cq =>
          obtain ⟨cq1, cq2⟩ := cq
          simp at h
          obtain ⟨o2, ho2, h⟩ := h
          cases o2 with
          | none => simp at h
          | some tq =>
            obtain ⟨tq1, tq2⟩ := tq
            simp at h
            obtain ⟨doms, hfvt, r2, st3, hdomsat, h⟩ := h
            cases r2 with
            | Err err => simp at h
            | Ok _ =>
              simp at h
              obtain ⟨o3, ho3, h⟩ := h
              cases o3 with
              | none => simp at h
              | some xq =>
                obtain ⟨xq1, xq2⟩ := xq
                simp at h
                obtain ⟨v3, hargs, idxs, hdrop, hb1, hb2, hb3, r3, st4,
                  hsortsstep, hfin⟩ := h
                cases r3 with
                | Err err => simp at hfin
                | Ok sorts0 =>
                  simp at hfin
                  obtain ⟨rfl, rfl, rfl⟩ := hfin
                  -- the abstractions of the eight stages
                  obtain ⟨hstripabs, hstripwf⟩ :=
                    ExprOps.strip_pis_refines hcvcawf.2.2 ho
                  obtain ⟨hbbswf, hcbodywf⟩ := hstripwf _ rfl
                  have hiv : i.val = n_p.val + n_f.val := HashMap.uscalar_add_eq hi
                  have hstrip : (absConstantVal cvCa).type.stripPis (n_p.val + n_f.val)
                      = some (ExprOps.absBinders bbs, absExpr cbody) := by
                    rw [← hiv]; simpa [absConstantVal] using hstripabs.symm
                  have hresidok := hresid t lps n_p n_f n_idx cbody true ht hlps
                    hcbodywf hb
                  obtain ⟨ho1abs, ho1wf⟩ := hop n_p cvCa.ty 0#u64 _ hcvcawf.2.2 ho1
                  obtain ⟨hcq1wf, hcq2wf⟩ := ho1wf _ rfl
                  obtain ⟨ho2abs, ho2wf⟩ := hop n_p cv_ta.ty 0#u64 _ hcvta.2.2 ho2
                  obtain ⟨htq1wf, htq2wf⟩ := ho2wf _ rfl
                  have hcq : ConLeche.openPisAtFvarsF n_p.val
                      (absConstantVal cvCa).type 0 = some (absExprs cq1, absExpr cq2) := by
                    simpa [absConstantVal] using ho1abs.symm
                  have htq : ConLeche.openPisAtFvarsF n_p.val
                      (absConstantVal cv_ta).type 0 = some (absExprs tq1, absExpr tq2) := by
                    simpa [absConstantVal] using ho2abs.symm
                  have hcq1len : cq1.val.length = n_p.val := by
                    have := openPisAtFvarsF_length hcq
                    simpa [absExprs] using this
                  have hnpmax : n_p.val ≤ Std.Usize.max :=
                    Scalars.u64_le_usize_max_of_le_len (v := cq1) (le_of_eq hcq1len.symm)
                  obtain ⟨hdomsabs, hdomswf⟩ := hft tq1 doms htq1wf hfvt
                  obtain ⟨lst3, hrundoms, hrel3, hwf3⟩ :=
                    hdoms st2 st3 fe 0#u64 n_p cq1 doms hwf2 hfe hcq1wf hdomswf
                      hnpmax hdomsat lst2 lfe hrel2 hfer
                  obtain ⟨ho3abs, ho3wf⟩ := hop n_f cq2 n_p _ hcq2wf ho3
                  obtain ⟨hxq1wf, hxq2wf⟩ := ho3wf _ rfl
                  have hxq : ConLeche.openPisAtFvarsF n_f.val (absExpr cq2) n_p.val
                      = some (absExprs xq1, absExpr xq2) := by
                    simpa using ho3abs.symm
                  have hxq1len : xq1.val.length = n_f.val := by
                    have := openPisAtFvarsF_length hxq
                    simpa [absExprs] using this
                  have hnfmax : n_f.val ≤ Std.Usize.max :=
                    Scalars.u64_le_usize_max_of_le_len (v := xq1) (le_of_eq hxq1len.symm)
                  obtain ⟨hargsabs, hargswf⟩ := ExprOps.get_app_args_refines hxq2wf hargs
                  obtain ⟨hdropabs, hdropwf⟩ := CoreK.drop_exprs_refines hargswf hdrop
                  have hcastnp : (Std.UScalar.cast .Usize n_p : Std.Usize).val = n_p.val :=
                    ExprOps.u64_cast_usize_val hnpmax
                  have hidxabs : absExprs idxs = (absExpr xq2).getAppArgs.drop n_p.val := by
                    rw [hdropabs, hcastnp, hargsabs]
                  have hb1abs := opened_resid_ok_refines hpo ht hlps hcq1wf hxq2wf
                    hnpmax hb1
                  have hb2abs := field_doms_resolve_from_refines hres hrel0 hfe0
                    hxq1wf hb2
                  have hb3abs := index_args_resolve_from_refines hres hrel0 hfe0
                    hdropwf hb3
                  obtain ⟨lst4, hrunsorts, hrel4, hwf4, hsortswf⟩ :=
                    check_struct_field_sorts_i_refines hw hwf3 hfe hsort hxq1wf
                      hdropwf hnfmax hsortsstep lst3 lfe hrel3 hfer
                  have hrundoms' : (ConLeche.checkStructDomsAtF
                      (m := ConLeche.Cached.CheckCM)
                      (ConLeche.Cached.sharedOpsC (absMode mode) lfe) lfe 0
                      (absExprs cq1) ((absExprs tq1).map ConLeche.Expr.fvarTypeD)
                      n_p.val).run lst2 = .ok ((), lst3) := by
                    rw [← hdomsabs]; simpa using hrundoms
                  have hrunsorts' : (ConLeche.checkStructFieldSortsIF
                      (m := ConLeche.Cached.CheckCM)
                      (ConLeche.Cached.sharedOpsC (absMode mode) lfe) lfe is_prop
                      large (absLevel res_sort) n_p.val (absExprs xq1)
                      ((absExpr xq2).getAppArgs.drop n_p.val) n_f.val).run lst3
                      = .ok (absLevels sorts0, lst4) := by
                    rw [← hidxabs]; exact hrunsorts
                  refine ⟨lst4, ?_, hrel4, hwf4, hcvcawf, hsortswf⟩
                  exact checkSumCtorF_run hrun0 hrun1 hstrip hresidok.symm hcq htq
                    hrundoms' hxq hb1abs.symm (by simpa using hb2abs.symm)
                    (by rw [← hidxabs]; simpa using hb3abs.symm) hrunsorts'

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
  generalize hd : cs.val.length - i.val = d
  induction d using Nat.strong_induction_on generalizing st st' i out souts r sr with
  | _ d ih =>
  intro lst lfe hrel hfer
  rw [inductives.sum_install.check_sum_ctors] at h
  by_cases hi : i.val ≥ cs.val.length
  · rw [if_pos (show i ≥ alloc.vec.Vec.len cs by scalar_tac)] at h
    simp at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    refine ⟨lst, [], [], ?_, by simp, by simp, hrel, hst, hout, hsouts⟩
    rw [List.drop_eq_nil_of_le (show (IndAbs.absCtors cs).length ≤ i.val by
      simp [IndAbs.absCtors]; scalar_tac)]
    exact checkSumCtorsF_nil
  · rw [if_neg (show ¬ i ≥ alloc.vec.Vec.len cs by scalar_tac)] at h
    have hlt : i.val < cs.val.length := by scalar_tac
    have hmax : i.val + 1 ≤ Std.Usize.max := by
      have := cs.slice.property; scalar_tac
    obtain ⟨i1, hi1, hi1v⟩ := usize_add_ok hmax
    obtain ⟨y, hy, hyv⟩ :=
      WP.spec_imp_exists (alloc.vec.Vec.index_usize_spec cs i hlt)
    subst hyv
    simp only [alloc.vec.Vec.index_slice_index, hy, bind_tc_ok] at h
    obtain ⟨pp, hstep, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨r0, st1⟩ := pp
    cases r0 with
    | Err err => simp at h
    | Ok q =>
      obtain ⟨cv1, sorts⟩ := q
      obtain ⟨lst1, hrun1, hrel1, hwf1, hcv1wf, hsortswf⟩ :=
        check_sum_ctor_refines hw hcv hmc hop hft hdoms hresid hpo hres hst hfe0 hfe
          hrel0 ht hlps hsort (hcs _ (List.getElem_mem hlt)) hcvta hstep lst lfe
          hrel hfer
      simp at h
      obtain ⟨out1, hout1, souts1, hsouts1, i2, hi2, h⟩ := h
      have hi2v : i2.val = i.val + 1 := HashMap.uscalar_add_eq hi2
      have hout1wf : ∀ c ∈ out1.val, ConstantValWF c.1 := by
        intro c hc
        rw [vec_push_val hout1, List.mem_append] at hc
        rcases hc with hc | hc
        · exact hout c hc
        · rw [List.mem_singleton.mp hc]; exact hcv1wf
      have hsouts1wf : ∀ us ∈ souts1.val, LevelsWF us := by
        intro us hu
        rw [vec_push_val hsouts1, List.mem_append] at hu
        rcases hu with hu | hu
        · exact hsouts us hu
        · rw [List.mem_singleton.mp hu]; exact hsortswf
      obtain ⟨lst2, lcs, lss, hrun2, habsr, habssr, hrel2, hwf2, hrwf, hsrwf⟩ :=
        ih (cs.val.length - i1.val) (by scalar_tac) hwf1 hout1wf hsouts1wf h
          (by rw [hi2v, hi1v]) lst1 lfe hrel1 hfer
      refine ⟨lst2, (absConstantVal cv1, cs.val[i.val].2.val) :: lcs,
        absLevels sorts :: lss, ?_, ?_, ?_, hrel2, hwf2, hrwf, hsrwf⟩
      · rw [absCtors_drop_cons (cs := cs) hlt]
        rw [hi2v] at hrun2
        exact checkSumCtorsF_cons hrun1 hrun2
      · rw [habsr, IndAbs.absCtors, vec_push_val hout1]
        simp [IndAbs.absCtors]
      · rw [habssr, IndAbs.absLevelss, vec_push_val hsouts1]
        simp [IndAbs.absLevelss]

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
