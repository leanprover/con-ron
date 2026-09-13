/-
# `kernel::inductives::struct_install` refined (task #57)

`CORE_PLAN.md` step 7.  The direct route's **structure** stages
(`crates/con-ron-core/src/kernel/inductives/struct_install.rs`, four items)
against `ConLeche/Kernel/Inductives/StructInstall.lean` and its index twin
`StructInstallF.lean`.  Task #25's deviation 1 is that the port has *one*
function per `Env`/index pair carrying both citations, so every statement here
is against the `*F` spelling — the one the executable runs, and the one the
cached drivers of `Cached/CheckerC.lean` call.

| group | items |
|---|---|
| the binder-domain comparison | `check_struct_doms_at` (`checkStructDomsAtF`; the `Array` twin `checkStructDomsAtFA` is the same function at `List.toArray`) |
| the projection table's guards | `proj_bodies_scoped_from` (the `bodies.all` conjunct), `proj_fn_family_free_from` (the `(List.range nF).all` name-family freshness, shared with `Modeled.lean`'s two sites) |
| the table itself | `check_struct_proj_table` (`checkStructProjTableF` at `StructWalkers.plain`) |

**The walkers record is dissolved** (task #25's deviation 3):
`checkStructProjTableF` takes a `StructWalkers` record of two closures and the
cached driver supplies memoised twins, but con-leche's own
`structWalkersC_eq_plain` says `StructWalkers.plain` is the specification, so
the port calls the two walkers by name.  The statement below is therefore
against `StructWalkers.plain` and the two walkers' own refinements are
*ingredients*: `struct_parts::struct_proj_bodies` is the sibling
`IndStructParts.lean`'s and `decl_check::consts_resolve_f_fast` is task #24's
tier's, so both travel as explicit named hypotheses
(`StructProjBodiesRefines`, `ConstsResolveFFastRefines`) in the exact-result
shape — nothing is weakened, the conclusion is the exact one under a named
ingredient, exactly as `Refine/StateC.lean` carries `InstantiateListRefines`.

**The knot is assumed** (task #55 proves its arms): `check_struct_doms_at`
reaches `ops.isDefEq` and so takes
`hw : Core.Wrappers mode IndAbs.checkFuelU`.

3 `sorry`s: the three recursions (`check_struct_doms_at`,
`proj_bodies_scoped_from`, `check_struct_proj_table`).  Aeneas emits the first
two as `partial_fixpoint` definitions, whose unfolding needs the fixpoint
equation and a well-founded measure on the index; the statements are the exact
ones and the recursion is the only thing missing.
-/
import ConRon.Refine.IndAbs
import ConRon.Refine.ExprOpsFields
import ConRon.Refine.ExprOpsMeta
import ConRon.Refine.CoreKBase
import ConRon.Refine.CoreKSupport

open Aeneas Aeneas.Std Result
open ConRon.Generated ConRon.Generated.kernel ConRon.Generated.kernel.inductives
open ConRon.Refine ConRon.Refine.State ConRon.Refine.FEnv

namespace ConRon.Refine.StructInstall

/-! ## The two ingredients this file does not own -/

/-- `struct_parts::struct_proj_bodies` refines `structProjBodies`
(`StructParts.lean`), the second of `StructWalkers.plain`'s two walkers.
**Owned by `Refine/IndStructParts.lean`**; named here so that
`check_struct_proj_table_refines` keeps its exact conclusion under an explicit
ingredient. -/
def StructProjBodiesRefines : Prop :=
  ∀ (t : name.Name) (n_p n_f : Std.U64) (cty : expr.Expr)
    (o : Option (alloc.vec.Vec expr.Expr)),
    NameWF t → ExprWF cty →
    inductives.struct_parts.struct_proj_bodies t n_p n_f cty = ok o →
    o.map (fun bs => (absExprs bs).toArray)
      = ConLeche.structProjBodies (absName t) n_p.val n_f.val (absExpr cty)
    ∧ ∀ bs, o = some bs → ExprsWF bs

/-- `decl_check::consts_resolve_f_fast` refines `Expr.constsResolveF`, the
first of `StructWalkers.plain`'s two walkers.  **Owned by the checker tier**
(`kernel/decl_check.rs`, task #24; task #30's fix — the `Expr`-tree spec
`core_k::consts_resolve` does not finish on a DAG-shared body, so the port
runs the memoised `*_fast` member). -/
def ConstsResolveFFastRefines : Prop :=
  ∀ (fe : fenv.FEnv) (lfe : ConLeche.FEnv) (e : expr.Expr) (b : Bool),
    FEnvRel fe lfe → FEnvWF fe → ExprWF e →
    kernel.decl_check.consts_resolve_f_fast fe e = ok b →
    b = (absExpr e).constsResolveF lfe

/-! ## The binder-domain comparison -/

/-- `ConLeche/Kernel/Inductives/StructInstallF.lean:27-36` —
`check_struct_doms_at` refines `checkStructDomsAtF`: the `j`-th opened
variable's annotation against the `j`-th expected domain, at frame `off + j`,
from the last binder to the first. -/
theorem check_struct_doms_at_refines {mode : env.CheckMode}
    (hw : Core.Wrappers mode IndAbs.checkFuelU)
    {st st' : cached.state_c.CState} {fe : fenv.FEnv} {off j : Std.U64}
    {fvs doms : alloc.vec.Vec expr.Expr}
    (hst : StateWF st) (hfe : FEnvWF fe) (hfvs : ExprsWF fvs)
    (hdoms : ExprsWF doms)
    (h : inductives.struct_install.check_struct_doms_at mode st fe off fvs doms j
        = ok (.Ok (), st')) :
    ∀ lst lfe, StateRel st lst → FEnvRel fe lfe →
      ∃ lst',
        (ConLeche.checkStructDomsAtF (m := ConLeche.Cached.CheckCM)
            (ConLeche.Cached.sharedOpsC (absMode mode) lfe) lfe off.val
            (absExprs fvs) (absExprs doms) j.val).run lst = .ok ((), lst')
        ∧ StateRel st' lst' ∧ StateWF st' := by
  -- the index recursion on `j`; Aeneas's `partial_fixpoint` unfolding
  sorry

/-! ## The projection table's two guards -/

/-- `ConLeche/Kernel/Inductives/StructInstallF.lean:73-95` —
`proj_bodies_scoped_from` refines `checkStructProjTableF`'s `bodies.all`
conjunct from index `i`: fvar-free, level parameters within the structure's,
resolving, and scoped at the parameters and the subject. -/
theorem proj_bodies_scoped_from_refines {fe : fenv.FEnv} {lfe : ConLeche.FEnv}
    {lps : alloc.vec.Vec name.Name} {n_p : Std.U64}
    {bodies : alloc.vec.Vec expr.Expr} {i : Std.Usize} {b : Bool}
    (hres : ConstsResolveFFastRefines)
    (hrel : FEnvRel fe lfe) (hfe : FEnvWF fe) (hlps : NamesWF lps)
    (hbodies : ExprsWF bodies)
    (h : inductives.struct_install.proj_bodies_scoped_from fe lps n_p bodies i
        = ok b) :
    b = ((absExprs bodies).drop i.val).all (fun e =>
      !e.hasFvar && e.allLevelParamsDefined (absNames lps) && e.constsResolveF lfe
        && e.looseBVarsBounded (n_p.val + 1)) := by
  -- the index recursion on `bodies.len() - i`; Aeneas's `partial_fixpoint`
  sorry

/-- `ConLeche/Kernel/Inductives/StructInstallF.lean:73-95` —
`proj_fn_family_free_from` refines the projection-function name family's
freshness test `(List.range nF).all (fun j => (fe.find? (projFnName T j)).isNone)`
from index `j`.  `Modeled.lean`'s two sites spell the same `all`, and
`IndC.lean`'s modeled driver reads this lemma at `j = 0`. -/
theorem proj_fn_family_free_from_refines {fe : fenv.FEnv} {lfe : ConLeche.FEnv}
    {t : name.Name} {n_f j : Std.U64} {b : Bool}
    (hrel : FEnvRel fe lfe) (hfe : FEnvWF fe) (ht : NameWF t)
    (h : inductives.struct_install.proj_fn_family_free_from fe t n_f j = ok b) :
    b = (List.range' j.val (n_f.val - j.val)).all
      (fun k => (lfe.find? (ConLeche.projFnName (absName t) k)).isNone) := by
  have hag : FindAgree fe lfe := FindAgree.of_rel hrel hfe
  generalize hd : n_f.val - j.val = d
  induction d using Nat.strong_induction_on generalizing j b with
  | _ d ih =>
    rw [inductives.struct_install.proj_fn_family_free_from] at h
    split at h
    · rename_i hge
      have hz : d = 0 := by rw [← hd]; scalar_tac
      subst hz
      simpa using (Result.ok_injective h).symm
    · rename_i hlt
      have hlt' : j.val < n_f.val := by scalar_tac
      simp only [bind_eq_ok_iff] at h
      obtain ⟨n, hn, o, ho, h⟩ := h
      have hnw : NameWF n := Env.proj_fn_name_wf ht hn
      have habs : absName n = ConLeche.projFnName (absName t) j.val :=
        Env.proj_fn_name_refines hn
      have hs : core.option.Option.is_some o
          = (lfe.find? (ConLeche.projFnName (absName t) j.val)).isSome := by
        rw [CoreK.find_isSome hag hnw ho, habs]
      have hsplit : d = (n_f.val - (j.val + 1)) + 1 := by rw [← hd]; omega
      subst hsplit
      rw [List.range'_succ, List.all_cons]
      split at h
      · rename_i hsome
        rw [hs] at hsome
        rw [← Result.ok_injective h]
        rcases hf : lfe.find? (ConLeche.projFnName (absName t) j.val) with _ | ci
        · rw [hf] at hsome; simp at hsome
        · simp
      · rename_i hnone
        rw [hs] at hnone
        simp only [Bool.not_eq_true] at hnone
        simp only [bind_eq_ok_iff] at h
        obtain ⟨i, hi, h⟩ := h
        have hiv : i.val = j.val + 1 := HashMap.uscalar_add_eq hi
        have hrec := ih (n_f.val - (j.val + 1)) (by omega) (j := i) (b := b) h
          (by rw [hiv])
        rcases hf : lfe.find? (ConLeche.projFnName (absName t) j.val) with _ | ci
        · simp only [Option.isNone_none, Bool.true_and]
          rw [hrec, hiv]
        · rw [hf] at hnone; simp at hnone

/-- The `j = 0` reading, which is what both routes' drivers call: the cited
`(List.range nF).all`. -/
theorem proj_fn_family_free_refines {fe : fenv.FEnv} {lfe : ConLeche.FEnv}
    {t : name.Name} {n_f : Std.U64} {b : Bool}
    (hrel : FEnvRel fe lfe) (hfe : FEnvWF fe) (ht : NameWF t)
    (h : inductives.struct_install.proj_fn_family_free_from fe t n_f 0#u64
        = ok b) :
    b = (List.range n_f.val).all
      (fun k => (lfe.find? (ConLeche.projFnName (absName t) k)).isNone) := by
  have := proj_fn_family_free_from_refines hrel hfe ht h
  simpa [List.range_eq_range'] using this

/-! ## The table -/

/-- `ConLeche/Kernel/Inductives/StructInstallF.lean:73-95` —
`check_struct_proj_table` refines `checkStructProjTableF StructWalkers.plain`:
the fields' result-type bodies read off the *annotated* constructor type by
substitution alone, the per-field guard levels, the constructor and the
counts, pushed as one `projInfo` constant.  Nothing is annotated, inferred or
pinned here, so no knot hypothesis is needed — only the two walkers. -/
theorem check_struct_proj_table_refines
    {t c : name.Name} {lps : alloc.vec.Vec name.Name} {n_p n_f off : Std.U64}
    {res_sort : level.Level} {guards : alloc.vec.Vec level.Level}
    {cv_ca : env.ConstantVal} {fe fe' : fenv.FEnv} {lfe : ConLeche.FEnv}
    (hbodies : StructProjBodiesRefines) (hres : ConstsResolveFFastRefines)
    (hrel : FEnvRel fe lfe) (hfe : FEnvWF fe)
    (ht : NameWF t) (hc : NameWF c) (hlps : NamesWF lps)
    (hsort : LevelWF res_sort) (hguards : LevelsWF guards)
    (hcv : ConstantValWF cv_ca)
    (h : inductives.struct_install.check_struct_proj_table t c lps n_p n_f
        res_sort guards off cv_ca fe = ok (.Ok fe')) :
    ∃ lfe',
      (∀ lst, (ConLeche.checkStructProjTableF (m := ConLeche.Cached.CheckCM)
          ConLeche.StructWalkers.plain (absName t) (absName c) (absNames lps)
          n_p.val n_f.val (absLevel res_sort) (absLevels guards) off.val
          (absConstantVal cv_ca) lfe).run lst = .ok (lfe', lst))
      ∧ FEnvRel fe' lfe' ∧ FEnvWF fe' := by
  -- the two guards, then `fenv::push` of the `projInfo` record
  sorry

end ConRon.Refine.StructInstall
