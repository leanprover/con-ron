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

**The full outcome** (task #67, DESIGN.md §3's ruling of 2026-09-13): the two
`*_refines` lemmas are stated over the Rust computation's whole outcome, with
the pre-#67 statement left beside each as `*_refines_ok` for the call sites
that already know the port succeeded.  All seven of the module's error sites
are mirrored: `check_struct_doms_at`'s two `(i as usize) >= len` guards are
con-leche's own `unwrapOr fvs[j]?`/`doms[j]?` (`StructInstallF.lean:31-32`),
its `defeq` failure travels through con-leche's bind, its domain mismatch is
the cited `notImplemented`, and `check_struct_proj_table`'s four guards are the
cited `throw`s one for one.

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

/-- **`throw` in `CheckCM`**: the plumbing `simp` set carries no
`MonadExcept` instance, so `simp` would leave con-leche's `throw` arms
un-run (task #67; `Refine/IndAbs.lean` re-declares the same lemma —
`attribute [local simp]` does not travel across files). -/
private theorem checkCM_throw_apply {b : Type} (le : ConLeche.CheckError)
    (lst : ConLeche.Cached.CState) :
    (throw le : ConLeche.Cached.CheckCM b) lst = .error le := rfl

attribute [local simp] checkCM_throw_apply

/-- The port's `Err` value at a mirrored `throw` arm: `core_types::internal`
*is* the `Internal` constructor (task #67). -/
private theorem internal_err {v : alloc.vec.Vec Std.U32}
    {ce : core_types.CheckError} (h : core_types.internal v = ok ce) :
    ce = .Internal v :=
  (Result.ok_injective (by rw [core_types.internal] at h; exact h)).symm

/-- The same for `core_types::invalid`. -/
private theorem invalid_err {v : alloc.vec.Vec Std.U32}
    {ce : core_types.CheckError} (h : core_types.invalid v = ok ce) :
    ce = .Invalid v :=
  (Result.ok_injective (by rw [core_types.invalid] at h; exact h)).symm

/-- The same for `core_types::not_implemented`. -/
private theorem not_implemented_err {v : alloc.vec.Vec Std.U32}
    {ce : core_types.CheckError} (h : core_types.not_implemented v = ok ce) :
    ce = .NotImplemented v :=
  (Result.ok_injective (by rw [core_types.not_implemented] at h; exact h)).symm

open ConLeche.Cached in
/-- `checkStructDomsAtF`'s step, with the comparison's *whole* outcome left
standing (task #67): the two `unwrapOr`s succeeded, so what remains is
`ops.isDefEq` and the `unless`.  The three corollaries below read off its
three cases. -/
theorem checkStructDomsAtF_succ_run {ops : ConLeche.CheckerOps CheckCM}
    {lfe : ConLeche.FEnv} {off j : Nat} {fvs doms : List ConLeche.Expr}
    {a b : ConLeche.Expr} {lst : CState}
    (ha : fvs[j]? = some a) (hb : doms[j]? = some b) :
    (ConLeche.checkStructDomsAtF ops lfe off fvs doms (j + 1)).run lst
      = (ops.isDefEq lfe.env (off + j) a.fvarTypeD b).run lst >>= fun p =>
          if p.1 then (ConLeche.checkStructDomsAtF ops lfe off fvs doms j).run p.2
          else .error (.notImplemented
            "direct structure: binder domain mismatch") := by
  rw [ConLeche.checkStructDomsAtF]
  simp only [ConLeche.unwrapOr, ha, hb, StateT.run, Bind.bind, StateT.bind,
    Except.bind, Pure.pure, StateT.pure, Except.pure]
  cases hd : (ops.isDefEq lfe.env (off + j) a.fvarTypeD b) lst with
  | error e => rfl
  | ok p => cases hp : p.1 <;> simp [hp, StateT.bind, Bind.bind, Except.bind]

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
  rw [checkStructDomsAtF_succ_run ha hb, hstep]; rfl

open ConLeche.Cached in
/-- `checkStructDomsAtF`'s step, at a comparison that *failed*: both sides
throw `notImplemented` — the port at `check_struct_doms_at::M_MIS`
(`struct_install.rs:78`), con-leche at `StructInstallF.lean:35`. -/
theorem checkStructDomsAtF_succ_false {ops : ConLeche.CheckerOps CheckCM}
    {lfe : ConLeche.FEnv} {off j : Nat} {fvs doms : List ConLeche.Expr}
    {a b : ConLeche.Expr} {lst lst1 : CState}
    (ha : fvs[j]? = some a) (hb : doms[j]? = some b)
    (hstep : (ops.isDefEq lfe.env (off + j) a.fvarTypeD b).run lst
      = .ok (false, lst1)) :
    (ConLeche.checkStructDomsAtF ops lfe off fvs doms (j + 1)).run lst
      = .error (.notImplemented "direct structure: binder domain mismatch") := by
  rw [checkStructDomsAtF_succ_run ha hb, hstep]; rfl

open ConLeche.Cached in
/-- `checkStructDomsAtF` at an index **con-leche itself** finds out of range:
`unwrapOr fvs[j]?` throws `.internal` (`StructInstallF.lean:31`), which is
what the port's `(i as usize) >= fvs.len()` guard mirrors
(`struct_install.rs:62`). -/
theorem checkStructDomsAtF_fvs_none {ops : ConLeche.CheckerOps CheckCM}
    {lfe : ConLeche.FEnv} {off j : Nat} {fvs doms : List ConLeche.Expr}
    {lst : CState} (ha : fvs[j]? = none) :
    (ConLeche.checkStructDomsAtF ops lfe off fvs doms (j + 1)).run lst
      = .error (.internal "direct structure: domain index") := by
  rw [ConLeche.checkStructDomsAtF]
  simp [ConLeche.unwrapOr, ha, StateT.run, Bind.bind, StateT.bind, Except.bind]

open ConLeche.Cached in
/-- The same at `doms` (`StructInstallF.lean:32`, `struct_install.rs:64`). -/
theorem checkStructDomsAtF_doms_none {ops : ConLeche.CheckerOps CheckCM}
    {lfe : ConLeche.FEnv} {off j : Nat} {fvs doms : List ConLeche.Expr}
    {a : ConLeche.Expr} {lst : CState}
    (ha : fvs[j]? = some a) (hb : doms[j]? = none) :
    (ConLeche.checkStructDomsAtF ops lfe off fvs doms (j + 1)).run lst
      = .error (.internal "direct structure: domain index") := by
  rw [ConLeche.checkStructDomsAtF]
  simp [ConLeche.unwrapOr, ha, hb, StateT.run, Bind.bind, StateT.bind,
    Except.bind, Pure.pure, StateT.pure, Except.pure]

/-- The abstracted `Vec`, read at an index the port read. -/
theorem absExprs_getElem? {v : alloc.vec.Vec expr.Expr} {i : Nat}
    {x : expr.Expr} (h : v.val[i]? = some x) :
    (absExprs v)[i]? = some (absExpr x) := by
  rw [absExprs, List.getElem?_map, h]; rfl

/-- The binder-domain recursion, with the measure the induction runs on made
explicit, over the **whole outcome** (task #67).  `hjmax` is the `usize`-width
side condition `Refine/Scalars.lean` owns: see `check_struct_doms_at_refines`
below. -/
theorem check_struct_doms_at_refines_aux {mode : env.CheckMode}
    (hw : Core.Wrappers mode IndAbs.checkFuelU)
    {fe : fenv.FEnv} {off : Std.U64} {fvs doms : alloc.vec.Vec expr.Expr}
    {lfe : ConLeche.FEnv}
    (hfe : FEnvWF fe) (hfvs : ExprsWF fvs) (hdoms : ExprsWF doms)
    (hfr : FEnvRel fe lfe) :
    ∀ (N : Nat) (j : Std.U64) (st st' : cached.state_c.CState)
      (o : core.result.Result Unit core_types.CheckError),
      j.val ≤ N → j.val ≤ Std.Usize.max → StateWF st →
      inductives.struct_install.check_struct_doms_at mode st fe off fvs doms j
          = ok (o, st') →
      ∀ lst, StateRel st lst →
        match o with
        | .Ok _ =>
          ∃ lst', (ConLeche.checkStructDomsAtF
                (ConLeche.Cached.sharedOpsC (absMode mode) lfe) lfe off.val
                (absExprs fvs) (absExprs doms) j.val).run lst = .ok ((), lst')
            ∧ StateRel st' lst' ∧ StateWF st'
        | .Err e =>
          ErrSim e ((ConLeche.checkStructDomsAtF
              (ConLeche.Cached.sharedOpsC (absMode mode) lfe) lfe off.val
              (absExprs fvs) (absExprs doms) j.val).run lst) := by
  intro N
  induction N with
  | zero =>
    intro j st st' o hN hjmax hst h lst hsr
    have hj0 : j = 0#u64 := by scalar_tac
    subst hj0
    rw [inductives.struct_install.check_struct_doms_at] at h
    simp only [reduceIte, Result.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨lst, by simpa using checkStructDomsAtF_zero, hsr, hst⟩
  | succ N ih =>
    intro j st st' o hN hjmax hst h lst hsr
    rw [inductives.struct_install.check_struct_doms_at] at h
    by_cases hj0 : j = 0#u64
    · subst hj0
      simp only [reduceIte, Result.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
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
      · -- `(i as usize) >= fvs.len()` (`struct_install.rs:62`): con-leche's
        -- own `unwrapOr fvs[j]?` throws the same `.internal`
        rename_i hgef
        have hge : (absExprs fvs).length ≤ i.val := by
          have h1 : (alloc.vec.Vec.len fvs).val
              ≤ (Std.UScalar.cast .Usize i : Std.Usize).val := hgef
          rw [alloc.vec.Vec.len_val, hcast] at h1
          simpa [absExprs] using h1
        have hnone : (absExprs fvs)[i.val]? = none := List.getElem?_eq_none hge
        simp only [bind_eq_ok_iff] at h
        obtain ⟨v, hv, ce, hce, h⟩ := h
        simp at h
        obtain ⟨rfl, rfl⟩ := h
        refine ErrSim.of_eq (x := Except.error
          (.internal "direct structure: domain index")) ?_ ?_
        · rw [internal_err hce]; exact ErrSim.internal rfl
        · rw [hjv]; exact checkStructDomsAtF_fvs_none hnone
      · rename_i hgef
        have hltf : i.val < (absExprs fvs).length := by
          have h1 : ¬ (alloc.vec.Vec.len fvs).val
              ≤ (Std.UScalar.cast .Usize i : Std.Usize).val := hgef
          rw [alloc.vec.Vec.len_val, hcast] at h1
          simpa [absExprs] using h1
        obtain ⟨af, hfvsget⟩ : ∃ af, (absExprs fvs)[i.val]? = some af :=
          ⟨_, List.getElem?_eq_getElem hltf⟩
        split at h
        · -- `(i as usize) >= doms.len()` (`struct_install.rs:64`)
          rename_i hged
          have hge : (absExprs doms).length ≤ i.val := by
            have h1 : (alloc.vec.Vec.len doms).val
                ≤ (Std.UScalar.cast .Usize i : Std.Usize).val := hged
            rw [alloc.vec.Vec.len_val, hcast] at h1
            simpa [absExprs] using h1
          have hnone : (absExprs doms)[i.val]? = none := List.getElem?_eq_none hge
          simp only [bind_eq_ok_iff] at h
          obtain ⟨v, hv, ce, hce, h⟩ := h
          simp at h
          obtain ⟨rfl, rfl⟩ := h
          refine ErrSim.of_eq (x := Except.error
            (.internal "direct structure: domain index")) ?_ ?_
          · rw [internal_err hce]; exact ErrSim.internal rfl
          · rw [hjv]; exact checkStructDomsAtF_doms_none hfvsget hnone
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
          have hew : ExprWF e := (ExprOps.vec_index_expr hfvs he).2.1
          have he1w : ExprWF e1 := (ExprOps.vec_index_expr hdoms he1).2.1
          obtain ⟨haabs, haw⟩ := ExprOps.fvar_type_d_refines hew ha
          have hfvsget : (absExprs fvs)[i.val]? = some (absExpr e) := by
            have hg := ExprOps.vec_index_expr_getElem? he
            rw [hcast] at hg
            exact absExprs_getElem? hg
          have hdomsget : (absExprs doms)[i.val]? = some (absExpr e1) := by
            have hg := ExprOps.vec_index_expr_getElem? he1
            rw [hcast] at hg
            exact absExprs_getElem? hg
          have hdefeq :
              ((ConLeche.Cached.sharedOpsC (absMode mode) lfe).isDefEq
                  lfe.env (off.val + i.val) (absExpr e).fvarTypeD
                  (absExpr e1)).run lst
                = ((ConLeche.Cached.sharedOpsC (absMode mode) lfe).isDefEq
                  (absEnv fe.env) i7.val (absExpr a) (absExpr e1)).run lst := by
            rw [← hfr.1, ← hi7v, ← haabs]
          cases r with
          | Err err =>
            -- `core_c::defeq` threw (`struct_install.rs:78`): con-leche's own
            -- bind at `ops.isDefEq` carries it
            simp at h
            obtain ⟨rfl, rfl⟩ := h
            have hkey : ErrSim err
                ((ConLeche.checkStructDomsAtF (m := ConLeche.Cached.CheckCM)
                    (ConLeche.Cached.sharedOpsC (absMode mode) lfe) lfe off.val
                    (absExprs fvs) (absExprs doms) j.val).run lst) := by
              rw [hjv, checkStructDomsAtF_succ_run hfvsget hdomsget]
              refine ErrSim.bind ?_ _
              rw [hdefeq]
              exact IndAbs.ops_defeq_err hw hst hfe haw he1w hp lst lfe hsr hfr
            exact hkey
          | Ok b =>
            obtain ⟨lst1, hrun, hsr1, hst1⟩ :=
              IndAbs.ops_defeq hw hst hfe haw he1w hp lst lfe hsr hfr
            have hstep :
                ((ConLeche.Cached.sharedOpsC (absMode mode) lfe).isDefEq
                    lfe.env (off.val + i.val) (absExpr e).fvarTypeD
                    (absExpr e1)).run lst = .ok (b, lst1) := by
              rw [hdefeq]; exact hrun
            cases b with
            | false =>
              -- the domains disagree: both sides throw `notImplemented`
              simp at h
              obtain ⟨v, hv, ce, hce, rfl, rfl⟩ := h
              refine ErrSim.of_eq (x := Except.error (.notImplemented
                "direct structure: binder domain mismatch")) ?_ ?_
              · rw [not_implemented_err hce]; exact ErrSim.notImplemented rfl
              · rw [hjv]
                exact checkStructDomsAtF_succ_false hfvsget hdomsget hstep
            | true =>
              have hrec := ih i st1 st' o (by omega) (by omega) hst1 h lst1 hsr1
              rw [hjv, checkStructDomsAtF_succ hfvsget hdomsget hstep]
              exact hrec

/-- `ConLeche/Kernel/Inductives/StructInstallF.lean:27-36` —
`check_struct_doms_at` refines `checkStructDomsAtF`: the `j`-th opened
variable's annotation against the `j`-th expected domain, at frame `off + j`,
from the last binder to the first.

At the **full outcome** (task #67) the four failures are all mirrored: the
two `(i as usize) >= len` guards (`struct_install.rs:62`, `:64`) are
con-leche's own `unwrapOr fvs[j]?` / `doms[j]?`
(`StructInstallF.lean:31-32`), which throw `.internal` too; `core_c::defeq`
threw and con-leche's bind carries it; or the domains disagreed and both
sides throw `.notImplemented`.

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
    {o : core.result.Result Unit core_types.CheckError}
    (hst : StateWF st) (hfe : FEnvWF fe) (hfvs : ExprsWF fvs)
    (hdoms : ExprsWF doms) (hjmax : j.val ≤ Std.Usize.max)
    (h : inductives.struct_install.check_struct_doms_at mode st fe off fvs doms j
        = ok (o, st')) :
    ∀ lst lfe, StateRel st lst → FEnvRel fe lfe →
      match o with
      | .Ok _ =>
        ∃ lst',
          (ConLeche.checkStructDomsAtF
              (ConLeche.Cached.sharedOpsC (absMode mode) lfe) lfe off.val
              (absExprs fvs) (absExprs doms) j.val).run lst = .ok ((), lst')
          ∧ StateRel st' lst' ∧ StateWF st'
      | .Err e =>
        ErrSim e ((ConLeche.checkStructDomsAtF
            (ConLeche.Cached.sharedOpsC (absMode mode) lfe) lfe off.val
            (absExprs fvs) (absExprs doms) j.val).run lst) := by
  intro lst lfe hsr hfr
  have hkey := check_struct_doms_at_refines_aux hw hfe hfvs hdoms hfr j.val j
    st st' o le_rfl hjmax hst h lst hsr
  cases o with
  | Ok u => exact hkey
  | Err e => exact hkey

/-- The **accept direction** of `check_struct_doms_at_refines`, the pre-#67
statement: the `.Ok` branch of the full-outcome one, for the call sites that
already know the port succeeded. -/
theorem check_struct_doms_at_refines_ok {mode : env.CheckMode}
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
        ∧ StateRel st' lst' ∧ StateWF st' :=
  fun lst lfe hsr hfr =>
    check_struct_doms_at_refines hw hst hfe hfvs hdoms hjmax h lst lfe hsr hfr

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

open ConLeche.Cached in
/-- `checkStructProjTableF` where the bodies do not exist: `unwrapOr` throws
`.internal` (`StructInstallF.lean:78`), which `struct_install.rs:179`
mirrors. -/
theorem checkStructProjTableF_bodies {w : ConLeche.StructWalkers}
    {T C : ConLeche.Name} {lps : List ConLeche.Name} {nP nF : Nat}
    {resSort : ConLeche.Level} {guards : List ConLeche.Level} {off : Nat}
    {cvCa : ConLeche.ConstantVal} {lfe : ConLeche.FEnv} {lst : CState}
    (hb : w.projBodies T nP nF cvCa.type = none) :
    (ConLeche.checkStructProjTableF (m := CheckCM) w T C lps nP nF resSort guards
        off cvCa lfe).run lst
      = .error (.internal "direct structure: projection bodies") := by
  rw [ConLeche.checkStructProjTableF]
  simp [ConLeche.unwrapOr, hb, StateT.run, Bind.bind, StateT.bind, Except.bind]

open ConLeche.Cached in
/-- `checkStructProjTableF` at its scoping guard (`StructInstallF.lean:86`,
mirrored by `struct_install.rs:187`). -/
theorem checkStructProjTableF_scope {w : ConLeche.StructWalkers}
    {T C : ConLeche.Name} {lps : List ConLeche.Name} {nP nF : Nat}
    {resSort : ConLeche.Level} {guards : List ConLeche.Level} {off : Nat}
    {cvCa : ConLeche.ConstantVal} {lfe : ConLeche.FEnv}
    {bodies : Array ConLeche.Expr} {lst : CState}
    (hb : w.projBodies T nP nF cvCa.type = some bodies)
    (hall : ¬ (bodies.size = nF ∧ (bodies.all fun b =>
        !b.hasFvar && ConLeche.Expr.allLevelParamsDefined lps b && w.resolve lfe b
          && ConLeche.Expr.looseBVarsBounded (nP + 1) b) = true)) :
    (ConLeche.checkStructProjTableF (m := CheckCM) w T C lps nP nF resSort guards
        off cvCa lfe).run lst
      = .error (.internal "direct structure: projection body scoping") := by
  rw [ConLeche.checkStructProjTableF]
  simp only [ConLeche.unwrapOr, hb, pure_bind]
  rw [if_neg hall]
  rfl

open ConLeche.Cached in
/-- `checkStructProjTableF` at its name-family guard
(`StructInstallF.lean:92`, mirrored by `struct_install.rs:189`). -/
theorem checkStructProjTableF_fam {w : ConLeche.StructWalkers}
    {T C : ConLeche.Name} {lps : List ConLeche.Name} {nP nF : Nat}
    {resSort : ConLeche.Level} {guards : List ConLeche.Level} {off : Nat}
    {cvCa : ConLeche.ConstantVal} {lfe : ConLeche.FEnv}
    {bodies : Array ConLeche.Expr} {lst : CState}
    (hb : w.projBodies T nP nF cvCa.type = some bodies)
    (hsize : bodies.size = nF)
    (hall : (bodies.all fun b =>
        !b.hasFvar && ConLeche.Expr.allLevelParamsDefined lps b && w.resolve lfe b
          && ConLeche.Expr.looseBVarsBounded (nP + 1) b) = true)
    (hfam : ¬ (((List.range nF).all fun j =>
        (lfe.find? (ConLeche.projFnName T j)).isNone) = true)) :
    (ConLeche.checkStructProjTableF (m := CheckCM) w T C lps nP nF resSort guards
        off cvCa lfe).run lst
      = .error (.invalid "projection name family taken") := by
  rw [ConLeche.checkStructProjTableF]
  simp only [ConLeche.unwrapOr, hb, pure_bind]
  rw [if_pos (show _ ∧ _ from ⟨hsize, hall⟩), if_neg hfam]
  rfl

open ConLeche.Cached in
/-- `checkStructProjTableF` at its table-name guard (`StructInstallF.lean:94`,
mirrored by `struct_install.rs:191`). -/
theorem checkStructProjTableF_tbl {w : ConLeche.StructWalkers}
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
    (htbl : ¬ ((lfe.find? (ConLeche.projTableName T)).isNone = true)) :
    (ConLeche.checkStructProjTableF (m := CheckCM) w T C lps nP nF resSort guards
        off cvCa lfe).run lst
      = .error (.invalid "projection table taken") := by
  rw [ConLeche.checkStructProjTableF]
  simp only [ConLeche.unwrapOr, hb, pure_bind]
  rw [if_pos (show _ ∧ _ from ⟨hsize, hall⟩), if_pos hfam, if_neg htbl]
  rfl

/-- `ConLeche/Kernel/Inductives/StructInstallF.lean:73-95` —
`check_struct_proj_table` refines `checkStructProjTableF StructWalkers.plain`:
the fields' result-type bodies read off the *annotated* constructor type by
substitution alone, the per-field guard levels, the constructor and the
counts, pushed as one `projInfo` constant.  Nothing is annotated, inferred or
pinned here, so no knot hypothesis is needed — only the two walkers.

At the **full outcome** (task #67) all four failures are mirrored, one per
guard of the cited `do` block: the bodies do not exist (`.internal`,
`struct_install.rs:179` against `StructInstallF.lean:78`), the bodies are not
scoped (`.internal`, `:187` against `:86`), the projection-function name
family is taken (`.invalid`, `:189` against `:92`) or the table name is
(`.invalid`, `:191` against `:94`).

The **unrestricted-canonical pair** rides through (task #59): the one success
branch is a single `fenv::push`, so `FEnv.push_canon` carries
`FEnvCanon`/`FEnvFull` from the index handed in to the one handed back.
`Refine/IndSpec.lean`'s header says why the tier needs the pair at all. -/
theorem check_struct_proj_table_refines
    {t c : name.Name} {lps : alloc.vec.Vec name.Name} {n_p n_f off : Std.U64}
    {res_sort : level.Level} {guards : alloc.vec.Vec level.Level}
    {cv_ca : env.ConstantVal} {fe : fenv.FEnv} {lfe : ConLeche.FEnv}
    {o : core.result.Result fenv.FEnv core_types.CheckError}
    (hbodies : StructProjBodiesRefines) (hres : ConstsResolveFFastRefines)
    (hrel : FEnvRel fe lfe) (hfe : FEnvWF fe)
    (hcan : FEnv.FEnvCanon fe) (hfull : FEnv.FEnvFull fe)
    (ht : NameWF t) (hc : NameWF c) (hlps : NamesWF lps)
    (hsort : LevelWF res_sort) (hguards : LevelsWF guards)
    (hcv : ConstantValWF cv_ca)
    (h : inductives.struct_install.check_struct_proj_table t c lps n_p n_f
        res_sort guards off cv_ca fe = ok o) :
    match o with
    | .Ok fe' =>
      ∃ lfe',
        (∀ lst, ((ConLeche.checkStructProjTableF
            ConLeche.StructWalkers.plain (absName t) (absName c) (absNames lps)
            n_p.val n_f.val (absLevel res_sort) (absLevels guards) off.val
            (absConstantVal cv_ca) lfe :
              ConLeche.Cached.CheckCM ConLeche.FEnv).run lst = .ok (lfe', lst)))
        ∧ FEnvRel fe' lfe' ∧ FEnvWF fe'
        ∧ FEnv.FEnvCanon fe' ∧ FEnv.FEnvFull fe'
    | .Err e =>
      ∀ lst, ErrSim e ((ConLeche.checkStructProjTableF
          ConLeche.StructWalkers.plain
          (absName t) (absName c) (absNames lps) n_p.val n_f.val
          (absLevel res_sort) (absLevels guards) off.val
          (absConstantVal cv_ca) lfe :
            ConLeche.Cached.CheckCM ConLeche.FEnv).run lst) := by
  rw [inductives.struct_install.check_struct_proj_table] at h
  obtain ⟨ob, hob, h⟩ := bind_eq_ok_iff.mp h
  have habs := hbodies t n_p n_f cv_ca.ty ob ht hcv.2.2 hob
  cases ob with
  | none =>
    have hbn : ConLeche.StructWalkers.plain.projBodies (absName t) n_p.val
        n_f.val (absConstantVal cv_ca).type = none := by
      simpa [ConLeche.StructWalkers.plain, absConstantVal] using habs.1.symm
    simp at h
    obtain ⟨v, hv, ce, hce, rfl⟩ := h
    intro lst
    rw [internal_err hce]
    exact ErrSim.of_eq
      (ErrSim.internal (s := "direct structure: projection bodies") rfl)
      (checkStructProjTableF_bodies hbn)
  | some bodies =>
    obtain ⟨habs1, hwf1⟩ := habs
    have hbw : ExprsWF bodies := hwf1 bodies rfl
    simp only [Option.map_some] at habs1
    have hbs : ConLeche.StructWalkers.plain.projBodies (absName t) n_p.val
        n_f.val (absConstantVal cv_ca).type = some (absExprs bodies).toArray :=
      habs1.symm
    simp only [lift_eq, bind_tc_ok] at h
    obtain ⟨sc, hsc, h⟩ := bind_eq_ok_iff.mp h
    split at h
    · rename_i hsct
      subst hsct
      split at hsc
      · rename_i hlen
        have hlenv : bodies.val.length = n_f.val := by
          have hl := alloc.vec.Vec.len_val bodies
          have hcc := Scalars.usize_cast_u64_val (alloc.vec.Vec.len bodies)
          rw [hlen] at hcc
          scalar_tac
        have hscoped := proj_bodies_scoped_from_refines hres hrel hfe hlps hbw hsc
        have hsizeA : ((absExprs bodies).toArray).size = n_f.val := by
          simpa [absExprs] using hlenv
        have hallA : (((absExprs bodies).toArray).all fun b =>
            !b.hasFvar && ConLeche.Expr.allLevelParamsDefined (absNames lps) b
              && ConLeche.StructWalkers.plain.resolve lfe b
              && ConLeche.Expr.looseBVarsBounded (n_p.val + 1) b) = true := by
          rw [List.all_toArray]
          simpa [ConLeche.StructWalkers.plain] using hscoped.symm
        obtain ⟨b, hb, h⟩ := bind_eq_ok_iff.mp h
        have hbv := proj_fn_family_free_refines hrel hfe ht hb
        split at h
        · rename_i hbt
          subst hbt
          have hfamA : ((List.range n_f.val).all fun j =>
              (lfe.find? (ConLeche.projFnName (absName t) j)).isNone) = true := by
            simpa using hbv.symm
          obtain ⟨n, hn, h⟩ := bind_eq_ok_iff.mp h
          obtain ⟨o1, ho1, h⟩ := bind_eq_ok_iff.mp h
          have hnabs : absName n = ConLeche.projTableName (absName t) :=
            Env.proj_table_name_refines hn
          have hnwf : NameWF n := Env.proj_table_name_wf ht hn
          have hag : FindAgree fe lfe := FindAgree.of_rel hrel hfe
          have hiss : core.option.Option.is_some o1
              = (lfe.find? (absName n)).isSome := CoreK.find_isSome hag hnwf ho1
          split at h
          · rename_i hss
            have hsome : (lfe.find? (absName n)).isSome = true := by
              rw [← hiss]; exact hss
            have htblA :
                ¬ ((lfe.find? (ConLeche.projTableName (absName t))).isNone
                  = true) := by
              rw [← hnabs]
              rcases hf : lfe.find? (absName n) with _ | ci
              · rw [hf] at hsome; simp at hsome
              · simp
            simp at h
            obtain ⟨v, hv, ce, hce, rfl⟩ := h
            intro lst
            rw [invalid_err hce]
            exact ErrSim.of_eq
              (ErrSim.invalid (s := "projection table taken") rfl)
              (checkStructProjTableF_tbl hbs hsizeA hallA hfamA htblA)
          · rename_i hns
            simp only [Bool.not_eq_true] at hns
            rw [hns, hnabs] at hiss
            simp only [name_dup_eq, level_dup_eq, bind_tc_ok] at h
            obtain ⟨v, hv, h⟩ := bind_eq_ok_iff.mp h
            have hvv : v.val = lps.val := PropWhen.names_copy_val hv
            obtain ⟨f, hf, h⟩ := bind_eq_ok_iff.mp h
            simp at h
            subst h
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
            have hpc := FEnv.push_canon hfe hciwf hcan hfull hf
            refine ⟨_, ?_, hcia ▸ hrel', hfe', hpc.1, hpc.2⟩
            intro lst
            exact checkStructProjTableF_ok (bodies := (absExprs bodies).toArray)
              hbs hsizeA hallA hfamA (by simpa using hiss)
        · rename_i hbf
          simp only [Bool.not_eq_true] at hbf
          subst hbf
          have hfamA : ¬ (((List.range n_f.val).all fun j =>
              (lfe.find? (ConLeche.projFnName (absName t) j)).isNone)
                = true) := by
            rw [← hbv]; simp
          simp at h
          obtain ⟨v, hv, ce, hce, rfl⟩ := h
          intro lst
          rw [invalid_err hce]
          exact ErrSim.of_eq
            (ErrSim.invalid (s := "projection name family taken") rfl)
            (checkStructProjTableF_fam hbs hsizeA hallA hfamA)
      · exact absurd (Result.ok_injective hsc) (by simp)
    · rename_i hsct
      simp only [Bool.not_eq_true] at hsct
      subst hsct
      have hnotA : ¬ (((absExprs bodies).toArray).size = n_f.val
          ∧ (((absExprs bodies).toArray).all fun b =>
              !b.hasFvar && ConLeche.Expr.allLevelParamsDefined (absNames lps) b
                && ConLeche.StructWalkers.plain.resolve lfe b
                && ConLeche.Expr.looseBVarsBounded (n_p.val + 1) b) = true) := by
        rintro ⟨hsz, hal⟩
        split at hsc
        · rename_i hlen
          have hscoped :=
            proj_bodies_scoped_from_refines hres hrel hfe hlps hbw hsc
          have hfalse : (((absExprs bodies).toArray).all fun b =>
              !b.hasFvar && ConLeche.Expr.allLevelParamsDefined (absNames lps) b
                && ConLeche.StructWalkers.plain.resolve lfe b
                && ConLeche.Expr.looseBVarsBounded (n_p.val + 1) b) = false := by
            rw [List.all_toArray]
            simpa [ConLeche.StructWalkers.plain] using hscoped.symm
          rw [hfalse] at hal
          simp at hal
        · rename_i hlen
          refine hlen ?_
          have hl := alloc.vec.Vec.len_val bodies
          have hcc := Scalars.usize_cast_u64_val (alloc.vec.Vec.len bodies)
          exact Std.UScalar.eq_of_val_eq
            (by rw [hcc, hl]; simpa [absExprs] using hsz)
      simp at h
      obtain ⟨v, hv, ce, hce, rfl⟩ := h
      intro lst
      rw [internal_err hce]
      exact ErrSim.of_eq
        (ErrSim.internal (s := "direct structure: projection body scoping") rfl)
        (checkStructProjTableF_scope hbs hnotA)

/-- The **accept direction** of `check_struct_proj_table_refines`, the pre-#67
statement: the `.Ok` branch of the full-outcome one, for the call sites that
already know the port succeeded. -/
theorem check_struct_proj_table_refines_ok
    {t c : name.Name} {lps : alloc.vec.Vec name.Name} {n_p n_f off : Std.U64}
    {res_sort : level.Level} {guards : alloc.vec.Vec level.Level}
    {cv_ca : env.ConstantVal} {fe fe' : fenv.FEnv} {lfe : ConLeche.FEnv}
    (hbodies : StructProjBodiesRefines) (hres : ConstsResolveFFastRefines)
    (hrel : FEnvRel fe lfe) (hfe : FEnvWF fe)
    (hcan : FEnv.FEnvCanon fe) (hfull : FEnv.FEnvFull fe)
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
      ∧ FEnvRel fe' lfe' ∧ FEnvWF fe'
      ∧ FEnv.FEnvCanon fe' ∧ FEnv.FEnvFull fe' :=
  check_struct_proj_table_refines hbodies hres hrel hfe hcan hfull ht hc hlps
    hsort hguards hcv h

end ConRon.Refine.StructInstall
