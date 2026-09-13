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

0 `sorry`s (task #59).  All four items are proved: the two guards and
`check_struct_doms_at` by strong induction on the remaining index over Aeneas's
`partial_fixpoint` unfolding, the table by composing them with `fenv::push`;
the `j = 0` reading of the name-family freshness that both routes' drivers call
follows from the general one.

**One hypothesis is added, at `check_struct_doms_at_refines`**: `hjmax`, the
`usize`-width side condition of `Refine/Scalars.lean`.  The conclusion is false
without it (the port indexes with `i as usize` on a `u64` counter and guards on
the *cast*, so a 32-bit target admits a wrapped index con-leche's `fvs[i]?`
answers `none` at); its own doc-comment says how the single caller discharges
it.  `Refine/IndSumInstall.lean`'s named ingredient `CheckStructDomsAtRefines`
therefore wants the same conjunct.
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

open ConLeche.Cached in
/-- `checkStructDomsAtF` at an exhausted counter. -/
theorem checkStructDomsAtF_zero {ops : ConLeche.CheckerOps CheckCM}
    {lfe : ConLeche.FEnv} {off : Nat} {fvs doms : List ConLeche.Expr}
    {lst : CState} :
    (ConLeche.checkStructDomsAtF ops lfe off fvs doms 0).run lst
      = .ok ((), lst) := rfl

open ConLeche.Cached in
/-- `checkStructDomsAtF`'s step, at a comparison that succeeded. -/
theorem checkStructDomsAtF_succ {ops : ConLeche.CheckerOps CheckCM}
    {lfe : ConLeche.FEnv} {off j : Nat} {fvs doms : List ConLeche.Expr}
    {a b : ConLeche.Expr} {lst lst1 : CState}
    (ha : fvs[j]? = some a) (hb : doms[j]? = some b)
    (hstep : (ops.isDefEq lfe.env (off + j) a.fvarTypeD b).run lst
      = .ok (true, lst1)) :
    (ConLeche.checkStructDomsAtF ops lfe off fvs doms (j + 1)).run lst
      = (ConLeche.checkStructDomsAtF ops lfe off fvs doms j).run lst1 := by
  rw [ConLeche.checkStructDomsAtF]
  simp only [ConLeche.unwrapOr, ha, hb, StateT.run, Bind.bind, StateT.bind,
    Except.bind, Pure.pure, StateT.pure, Except.pure]
  rw [show (ops.isDefEq lfe.env (off + j) a.fvarTypeD b) lst
      = Except.ok (true, lst1) from hstep]
  rfl

/-- The abstracted `Vec`, read at an index the port read. -/
theorem absExprs_getElem? {v : alloc.vec.Vec expr.Expr} {i : Nat}
    {x : expr.Expr} (h : v.val[i]? = some x) :
    (absExprs v)[i]? = some (absExpr x) := by
  rw [absExprs, List.getElem?_map, h]; rfl

/-- The binder-domain recursion, with the measure the induction runs on made
explicit.  `hjmax` is the `usize`-width side condition `Refine/Scalars.lean`
owns: see `check_struct_doms_at_refines` below. -/
theorem check_struct_doms_at_refines_aux {mode : env.CheckMode}
    (hw : Core.Wrappers mode IndAbs.checkFuelU)
    {fe : fenv.FEnv} {off : Std.U64} {fvs doms : alloc.vec.Vec expr.Expr}
    {lfe : ConLeche.FEnv}
    (hfe : FEnvWF fe) (hfvs : ExprsWF fvs) (hdoms : ExprsWF doms)
    (hfr : FEnvRel fe lfe) :
    ∀ (N : Nat) (j : Std.U64) (st st' : cached.state_c.CState),
      j.val ≤ N → j.val ≤ Std.Usize.max → StateWF st →
      inductives.struct_install.check_struct_doms_at mode st fe off fvs doms j
          = ok (.Ok (), st') →
      ∀ lst, StateRel st lst →
        ∃ lst', (ConLeche.checkStructDomsAtF (m := ConLeche.Cached.CheckCM)
              (ConLeche.Cached.sharedOpsC (absMode mode) lfe) lfe off.val
              (absExprs fvs) (absExprs doms) j.val).run lst = .ok ((), lst')
          ∧ StateRel st' lst' ∧ StateWF st' := by
  intro N
  induction N with
  | zero =>
    intro j st st' hN hjmax hst h lst hsr
    have hj0 : j = 0#u64 := by scalar_tac
    subst hj0
    rw [inductives.struct_install.check_struct_doms_at] at h
    simp only [reduceIte, Result.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    exact ⟨lst, by simpa using checkStructDomsAtF_zero, hsr, hst⟩
  | succ N ih =>
    intro j st st' hN hjmax hst h lst hsr
    rw [inductives.struct_install.check_struct_doms_at] at h
    by_cases hj0 : j = 0#u64
    · subst hj0
      simp only [reduceIte, Result.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h
      exact ⟨lst, by simpa using checkStructDomsAtF_zero, hsr, hst⟩
    · rw [if_neg hj0] at h
      obtain ⟨i, hi, h⟩ := bind_eq_ok_iff.mp h
      have hiv : i.val = j.val - 1 := HashMap.uscalar_sub_eq hi
      have hjne : j.val ≠ 0 := by
        intro hc
        exact hj0 (Std.UScalar.eq_of_val_eq (by simpa using hc))
      have hjv : j.val = i.val + 1 := by omega
      have himax : i.val ≤ Std.Usize.max := by omega
      have hcast : (Std.UScalar.cast .Usize i : Std.Usize).val = i.val :=
        Scalars.u64_cast_usize_val himax
      simp only [lift_eq, bind_tc_ok] at h
      split at h
      · simp [bind_eq_ok_iff] at h
      · rename_i hgef
        split at h
        · simp [bind_eq_ok_iff] at h
        · rename_i hged
          obtain ⟨e, he, h⟩ := bind_eq_ok_iff.mp h
          obtain ⟨a, ha, h⟩ := bind_eq_ok_iff.mp h
          obtain ⟨i6, hi6, h⟩ := bind_eq_ok_iff.mp h
          have hi6v : i6 = IndAbs.checkFuelU := by
            rw [IndAbs.check_fuel_eq] at hi6; exact (Result.ok_injective hi6).symm
          subst hi6v
          obtain ⟨i7, hi7, h⟩ := bind_eq_ok_iff.mp h
          have hi7v : i7.val = off.val + i.val := HashMap.uscalar_add_eq hi7
          obtain ⟨e1, he1, h⟩ := bind_eq_ok_iff.mp h
          obtain ⟨p, hp, h⟩ := bind_eq_ok_iff.mp h
          obtain ⟨r, st1⟩ := p
          cases r with
          | Err err => simp at h
          | Ok b =>
            cases b with
            | false => simp [bind_eq_ok_iff] at h
            | true =>
              have hew : ExprWF e := (ExprOps.vec_index_expr hfvs he).2.1
              have he1w : ExprWF e1 := (ExprOps.vec_index_expr hdoms he1).2.1
              obtain ⟨haabs, haw⟩ := ExprOps.fvar_type_d_refines hew ha
              obtain ⟨lst1, hrun, hsr1, hst1⟩ :=
                IndAbs.ops_defeq hw hst hfe haw he1w hp lst lfe hsr hfr
              obtain ⟨lst2, hrun2, hsr2, hst2⟩ :=
                ih i st1 st' (by omega) (by omega) hst1 h lst1 hsr1
              refine ⟨lst2, ?_, hsr2, hst2⟩
              have hfvsget : (absExprs fvs)[i.val]? = some (absExpr e) := by
                have hg := ExprOps.vec_index_expr_getElem? he
                rw [hcast] at hg
                exact absExprs_getElem? hg
              have hdomsget : (absExprs doms)[i.val]? = some (absExpr e1) := by
                have hg := ExprOps.vec_index_expr_getElem? he1
                rw [hcast] at hg
                exact absExprs_getElem? hg
              have hstep :
                  ((ConLeche.Cached.sharedOpsC (absMode mode) lfe).isDefEq
                      lfe.env (off.val + i.val) (absExpr e).fvarTypeD
                      (absExpr e1)).run lst = .ok (true, lst1) := by
                rw [← hfr.1, ← hi7v, ← haabs]; exact hrun
              rw [hjv, checkStructDomsAtF_succ hfvsget hdomsget hstep]
              exact hrun2

/-- `ConLeche/Kernel/Inductives/StructInstallF.lean:27-36` —
`check_struct_doms_at` refines `checkStructDomsAtF`: the `j`-th opened
variable's annotation against the `j`-th expected domain, at frame `off + j`,
from the last binder to the first.

**`hjmax` is the one added hypothesis of this file** and it cannot be dropped:
the port indexes `fvs`/`doms` with `i as usize` on the `u64` counter, which
Aeneas models as `UScalar.cast .Usize i`, of value `i.val % 2 ^ Usize.numBits`,
while con-leche reads `fvs[i]?` at `i` itself.  The loop's own guard compares
the *cast* (`(i as usize) >= fvs.len()`, `struct_install.rs:61-64`), so it
admits a wrapped index, and on a 32-bit target the port then succeeds where
`checkStructDomsAtF` throws `.internal` — the conclusion is false there.
`Refine/Scalars.lean` owns the fact and the discharges; the one caller
(`sum_install.rs:742`) passes `n_p`, the length of a `Vec` returned by
`open_pis_at_fvars_f`, so `Scalars.u64_le_usize_max_of_le_len` discharges it. -/
theorem check_struct_doms_at_refines {mode : env.CheckMode}
    (hw : Core.Wrappers mode IndAbs.checkFuelU)
    {st st' : cached.state_c.CState} {fe : fenv.FEnv} {off j : Std.U64}
    {fvs doms : alloc.vec.Vec expr.Expr}
    (hst : StateWF st) (hfe : FEnvWF fe) (hfvs : ExprsWF fvs)
    (hdoms : ExprsWF doms) (hjmax : j.val ≤ Std.Usize.max)
    (h : inductives.struct_install.check_struct_doms_at mode st fe off fvs doms j
        = ok (.Ok (), st')) :
    ∀ lst lfe, StateRel st lst → FEnvRel fe lfe →
      ∃ lst',
        (ConLeche.checkStructDomsAtF (m := ConLeche.Cached.CheckCM)
            (ConLeche.Cached.sharedOpsC (absMode mode) lfe) lfe off.val
            (absExprs fvs) (absExprs doms) j.val).run lst = .ok ((), lst')
        ∧ StateRel st' lst' ∧ StateWF st' := by
  intro lst lfe hsr hfr
  exact check_struct_doms_at_refines_aux hw hfe hfvs hdoms hfr j.val j st st'
    le_rfl hjmax hst h lst hsr

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
  generalize hd : bodies.length - i.val = d
  induction d using Nat.strong_induction_on generalizing i b with
  | _ d ih =>
    rw [inductives.struct_install.proj_bodies_scoped_from] at h
    split at h
    · rename_i hge
      have hnil : (absExprs bodies).drop i.val = [] := by
        apply List.drop_eq_nil_of_le
        simp only [absExprs, List.length_map]
        scalar_tac
      rw [hnil]
      simpa using (Result.ok_injective h).symm
    · rename_i hlt
      have hlt' : i.val < bodies.val.length := by
        have := alloc.vec.Vec.len_val bodies; scalar_tac
      obtain ⟨y, hy, hyv⟩ :=
        WP.spec_imp_exists (alloc.vec.Vec.index_usize_spec bodies i hlt')
      subst hyv
      have hew : ExprWF bodies.val[i.val] := hbodies _ (List.getElem_mem hlt')
      have hlt2 : i.val < (absExprs bodies).length := by
        simpa [absExprs] using hlt'
      have hcons : (absExprs bodies).drop i.val
          = absExpr bodies.val[i.val] :: (absExprs bodies).drop (i.val + 1) := by
        rw [List.drop_eq_getElem_cons hlt2]; simp [absExprs]
      rw [hcons, List.all_cons]
      simp only [alloc.vec.Vec.index_slice_index, hy, bind_tc_ok] at h
      obtain ⟨b0, hb0, h⟩ := bind_eq_ok_iff.mp h
      have hb0v : b0 = (absExpr bodies.val[i.val]).hasFvar :=
        ExprOps.has_fvar_refines hew hb0
      split at h
      · rename_i hfv
        rw [hb0v] at hfv
        rw [← Result.ok_injective h, hfv]
        simp
      · rename_i hfv
        simp only [Bool.not_eq_true] at hfv
        rw [hb0v] at hfv
        obtain ⟨b1, hb1, h⟩ := bind_eq_ok_iff.mp h
        have hb1v : b1 = (absExpr bodies.val[i.val]).allLevelParamsDefined
            (absNames lps) :=
          ExprOps.all_level_params_defined_fast_refines hlps hew hb1
        split at h
        · rename_i hlp
          obtain ⟨b2, hb2, h⟩ := bind_eq_ok_iff.mp h
          have hb2v : b2 = (absExpr bodies.val[i.val]).constsResolveF lfe :=
            hres _ _ _ _ hrel hfe hew hb2
          split at h
          · rename_i hcr
            obtain ⟨i2, hi2, h⟩ := bind_eq_ok_iff.mp h
            have hi2v : i2.val = n_p.val + 1 := HashMap.uscalar_add_eq hi2
            obtain ⟨b3, hb3, h⟩ := bind_eq_ok_iff.mp h
            have hb3v : b3 = (absExpr bodies.val[i.val]).looseBVarsBounded i2.val :=
              ExprOps.loose_bvars_bounded_refines hew hb3
            rw [hi2v] at hb3v
            split at h
            · rename_i hlb
              obtain ⟨i3, hi3, h⟩ := bind_eq_ok_iff.mp h
              have hi3v : i3.val = i.val + 1 := HashMap.uscalar_add_eq hi3
              have hrec := ih (bodies.length - i3.val) (by scalar_tac) h rfl
              rw [hi3v] at hrec
              rw [hrec, hfv, ← hb1v, hlp, ← hb2v, hcr, ← hb3v, hlb]
              simp
            · rename_i hlb
              simp only [Bool.not_eq_true] at hlb
              rw [← Result.ok_injective h, hfv, ← hb1v, hlp, ← hb2v, hcr, ← hb3v,
                hlb]
              simp
          · rename_i hcr
            simp only [Bool.not_eq_true] at hcr
            rw [← Result.ok_injective h, hfv, ← hb1v, hlp, ← hb2v, hcr]
            simp
        · rename_i hlp
          simp only [Bool.not_eq_true] at hlp
          rw [← Result.ok_injective h, hfv, ← hb1v, hlp]
          simp

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

open ConLeche.Cached in
/-- `checkStructProjTableF` on the path where all three guards hold: nothing
here touches the state, so the run is the pushed index at the same state. -/
theorem checkStructProjTableF_ok {w : ConLeche.StructWalkers}
    {T C : ConLeche.Name} {lps : List ConLeche.Name} {nP nF : Nat}
    {resSort : ConLeche.Level} {guards : List ConLeche.Level} {off : Nat}
    {cvCa : ConLeche.ConstantVal} {lfe : ConLeche.FEnv}
    {bodies : Array ConLeche.Expr} {lst : CState}
    (hb : w.projBodies T nP nF cvCa.type = some bodies)
    (hsize : bodies.size = nF)
    (hall : (bodies.all fun b =>
        !b.hasFvar && ConLeche.Expr.allLevelParamsDefined lps b && w.resolve lfe b
          && ConLeche.Expr.looseBVarsBounded (nP + 1) b) = true)
    (hfam : ((List.range nF).all fun j =>
        (lfe.find? (ConLeche.projFnName T j)).isNone) = true)
    (htbl : (lfe.find? (ConLeche.projTableName T)).isNone = true) :
    (ConLeche.checkStructProjTableF (m := CheckCM) w T C lps nP nF resSort guards
        off cvCa lfe).run lst
      = .ok (lfe.push (ConLeche.ConstantInfo.projInfo
          { structName := T, levelParams := lps, numParams := nP, ctor := C,
            numFields := nF, structSort := resSort, bodies := bodies,
            guards := guards, off := off }), lst) := by
  rw [ConLeche.checkStructProjTableF]
  simp only [ConLeche.unwrapOr, hb, pure_bind]
  rw [if_pos (show _ ∧ _ from ⟨hsize, hall⟩), if_pos hfam, if_pos htbl]
  rfl

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
  rw [inductives.struct_install.check_struct_proj_table] at h
  obtain ⟨o, ho, h⟩ := bind_eq_ok_iff.mp h
  have habs := hbodies t n_p n_f cv_ca.ty o ht hcv.2.2 ho
  cases o with
  | none => simp [bind_eq_ok_iff] at h
  | some bodies =>
    obtain ⟨habs1, hwf1⟩ := habs
    have hbw : ExprsWF bodies := hwf1 bodies rfl
    simp only [Option.map_some] at habs1
    simp only [lift_eq, bind_tc_ok] at h
    obtain ⟨sc, hsc, h⟩ := bind_eq_ok_iff.mp h
    split at h
    · rename_i hsct
      subst hsct
      split at hsc
      · rename_i hlen
        have hlenv : bodies.val.length = n_f.val := by
          have hl := alloc.vec.Vec.len_val bodies
          have hc := Scalars.usize_cast_u64_val (alloc.vec.Vec.len bodies)
          rw [hlen] at hc
          scalar_tac
        have hscoped := proj_bodies_scoped_from_refines hres hrel hfe hlps hbw hsc
        obtain ⟨b, hb, h⟩ := bind_eq_ok_iff.mp h
        have hbv := proj_fn_family_free_refines hrel hfe ht hb
        split at h
        · rename_i hbt
          subst hbt
          obtain ⟨n, hn, h⟩ := bind_eq_ok_iff.mp h
          obtain ⟨o1, ho1, h⟩ := bind_eq_ok_iff.mp h
          have hnabs : absName n = ConLeche.projTableName (absName t) :=
            Env.proj_table_name_refines hn
          have hnwf : NameWF n := Env.proj_table_name_wf ht hn
          have hag : FindAgree fe lfe := FindAgree.of_rel hrel hfe
          have hiss : core.option.Option.is_some o1
              = (lfe.find? (absName n)).isSome := CoreK.find_isSome hag hnwf ho1
          split at h
          · simp [bind_eq_ok_iff] at h
          · rename_i hns
            simp only [Bool.not_eq_true] at hns
            rw [hns, hnabs] at hiss
            simp only [name_dup_eq, level_dup_eq, bind_tc_ok] at h
            obtain ⟨v, hv, h⟩ := bind_eq_ok_iff.mp h
            have hvv : v.val = lps.val := PropWhen.names_copy_val hv
            obtain ⟨f, hf, h⟩ := bind_eq_ok_iff.mp h
            have hfeq : f = fe' := by
              simpa using Result.ok_injective h
            subst hfeq
            have hciwf : ConstantInfoWF (.ProjInfo
                { struct_name := t, level_params := v, num_params := n_p,
                  ctor := c, num_fields := n_f, struct_sort := res_sort,
                  bodies := bodies, guards := guards, off := off }) := by
              refine ⟨ht, ?_, hc, hsort, hbw, hguards⟩
              intro x hx; exact hlps x (by rw [← hvv]; exact hx)
            obtain ⟨hrel', hfe'⟩ := FEnv.push_refines hrel hfe hciwf hf
            have hcia : absConstantInfo (.ProjInfo
                { struct_name := t, level_params := v, num_params := n_p,
                  ctor := c, num_fields := n_f, struct_sort := res_sort,
                  bodies := bodies, guards := guards, off := off })
                = ConLeche.ConstantInfo.projInfo
                  { structName := absName t, levelParams := absNames lps,
                    numParams := n_p.val, ctor := absName c,
                    numFields := n_f.val, structSort := absLevel res_sort,
                    bodies := (absExprs bodies).toArray,
                    guards := absLevels guards, off := off.val } := by
              simp only [absConstantInfo, absProjTable, absNames, hvv]
            refine ⟨_, ?_, hcia ▸ hrel', hfe'⟩
            intro lst
            refine checkStructProjTableF_ok (bodies := (absExprs bodies).toArray)
              habs1.symm ?_ ?_ ?_ ?_
            · simpa [absExprs] using hlenv
            · rw [List.all_toArray]
              simpa [ConLeche.StructWalkers.plain] using hscoped.symm
            · simpa using hbv.symm
            · simpa using hiss
        · simp [bind_eq_ok_iff] at h
      · exact absurd (Result.ok_injective hsc) (by simp)
    · simp [bind_eq_ok_iff] at h

end ConRon.Refine.StructInstall
