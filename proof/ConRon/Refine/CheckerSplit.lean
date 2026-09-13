import ConRon.Refine.TypeChecker
import ConRon.Refine.CheckerBase
import ConRon.Refine.CoreKSupport
import ConRon.Refine.CoreKShapes
import ConRon.Refine.CoreKVec
import ConRon.Refine.CoreKPinned
import ConRon.Refine.BasisNames
import ConRon.Refine.ExprOpsMeta
import ConLeche.Kernel.CheckerSplit

/-! # `kernel::checker_split` — the install/check seam (task #56)

`ConLeche/Kernel/CheckerSplit.lean` (con-leche task #253) re-cuts the
declaration checker at the seam the *installed* driver needs: for a `defn`,
`thm` or `opaque` the **install half** runs the syntactic guards and the
annotation and pushes the constant, and the **check half** runs the inferences
and the conversion at the environment the constant was installed at.  Every
other declaration kind is not separable and its install half *is* `checkDecl`.

Three cited definitions, five Rust functions:

| Rust | con-leche |
|---|---|
| `install_constant_val` | `installConstantVal` (`:64-85`) |
| `install_value` | `installValue` (`:87-100`) |
| `is_thm` | `ValueKind`'s `DecidableEq` at `.thm` (`:36-42`) |
| `check_value_group` + `check_value_group_tail` | `checkValueGroup` (`:102-119`) |

`check_value_group` is split at the `let jv ← if …` join so both branches are
tail calls (task #24 point 7); the pair refines the one cited definition, and
`check_value_group_tail_refines` is stated at an arbitrary post-join `jv` so
that the two compose.

`ValueKind`/`ValueGroup` live in `cached::parsed_c` (task #14 took the three
seam records); `absValueKind`/`absValueGroup` are written here, **to be
unified into `Abs.lean`**.  `ValueKind.word` (`:44-48`) is not ported — it
renders the kind into a type-mismatch message, and DESIGN.md §3.1 says message
strings need not match; nothing below reads it, which is what makes the
omission free.

Two hypotheses recur and are not this file's to discharge:

* the knot (`core_k.check_fuel = ok fuel`, `Core.Wrappers mode fuel`), task
  #55's — every one of these functions calls a core entry point;
* `lenv`, the `Env` the cited Lean reads: `installConstantVal`/`installValue`
  call `Expr.constsResolve env` and `FEnv.lean` has no `constsResolveF` twin
  (`Refine/CoreKSupport.lean`'s `consts_resolve_refines` already carries that
  `henv` hypothesis), so the statements take the `Env` argument and the
  agreement `∀ n, lfe.find? n = lenv.find? n`.

**`check_value_group_refines` gained that agreement as a hypothesis** (task
#58), at `lenv = lfe.env`: the task-#56 note guessed it was `FEnvRel`'s own
first clause, and it is not.  `FEnvRel` relates `fe.env` to `lfe.env` and
`fe.idx` to `lfe.idx`, and `FEnvWF` constrains the index only as a hash map —
neither ties a `ConLeche.FEnv`'s index to its own `Env`, which is what
`FEnv.find? = Env.find?` says (con-leche proves it for `mkFEnv` only,
`mkFEnv_find?`).  Without the hypothesis the statement is false: an `fe` whose
index holds a name its `env` does not makes `core_k::consts_resolve` accept a
value whose `Expr.constsResolve lfe.env` rejects, so the Rust succeeds where
the cited Lean throws.  The two install lemmas already carried it, and at
every real call site the `FEnv` is a `mkFEnv`/`push` chain, where it holds.

`sorry` count in this file: 0.
-/
open Aeneas Aeneas.Std Result
open ConRon.Generated ConRon.Generated.kernel ConRon.Generated.cached
open ConRon.Refine ConRon.Refine.State ConRon.Refine.FEnv

namespace ConRon.Refine.CheckerSplit

/-! ## The seam's datum

`ValueKind` and `ValueGroup` (`ConLeche/Kernel/CheckerSplit.lean:36-42`,
`:51-56`).  **To be unified into `Abs.lean`.** -/

/-- A separable declaration kind of the model as `ConLeche.ValueKind`. -/
def absValueKind : parsed_c.ValueKind → ConLeche.ValueKind
  | .Defn => .defn
  | .Thm => .thm
  | .Opaque => .opaque

/-- What the install half hands the check half, as `ConLeche.ValueGroup`: the
kind, the header with its type annotated, and the value — annotated for a
definition or an opaque, **raw** for a theorem. -/
def absValueGroup (g : parsed_c.ValueGroup) : ConLeche.ValueGroup where
  kind := absValueKind g.kind
  cvA := absConstantVal g.cv_a
  jv := absExpr g.jv

/-- The hereditary invariant of the seam's datum. -/
def ValueGroupWF (g : parsed_c.ValueGroup) : Prop :=
  ConstantValWF g.cv_a ∧ ExprWF g.jv

/-- `expr::dup` is the identity in the model (DESIGN.md §3.2: `Arc::clone`);
`Refine/CheckerBase.lean` and `Refine/State.lean` keep the same local copy. -/
@[local simp] theorem expr_dup_eq (e : expr.Expr) : expr.dup e = ok e := by
  obtain ⟨r⟩ := e; simp [expr.dup]

/-! ## The kind test -/

/-- **`checker_split::is_thm` is `g.kind = .thm`** — the cited `DecidableEq`
instance at the one value the check half branches on
(`CheckerSplit.lean:36-42`). -/
theorem is_thm_refines {k : parsed_c.ValueKind} {b : Bool}
    (h : checker_split.is_thm k = ok b) :
    b = decide (absValueKind k = ConLeche.ValueKind.thm) := by
  cases k <;> (rw [checker_split.is_thm] at h; rw [← Result.ok_injective h]) <;> rfl

/-! ## The cited `do` blocks, run once

`Refine/CheckerBase.lean`'s `checkTypedList_cons` style: the cited body is
unfolded once against a run that is already known to have succeeded, so that
each refinement proof below only has to *supply* the steps.  `ops` and `lenv`
are arbitrary here — a slot is opaque to this file — and `checkValueGroup`,
whose `do` has a join in the middle, gets one lemma per branch of the join
plus `tail_run` for what follows it. -/

open ConLeche.Cached in
/-- `installConstantVal`, at a run all of whose guards passed. -/
theorem install_constant_val_run {ops : ConLeche.CheckerOps CheckCM} {lenv : ConLeche.Env}
    {cv : ConLeche.ConstantVal} {ty : ConLeche.Expr} {lst lst1 : CState}
    (h1 : (lenv.find? cv.name).isSome = false)
    (h2 : ConLeche.reservedBasisNames.contains cv.name = false)
    (h3 : cv.name.isProjFnShape = false)
    (h4 : ConLeche.Name.nodup cv.levelParams = true)
    (h5 : cv.type.looseBVarsBounded 0 = true) (h6 : cv.type.hasFvar = false)
    (hann : (ops.annotate lenv 0 cv.type).run lst = .ok (ty, lst1))
    (h7 : ty.allLevelParamsDefined cv.levelParams = true)
    (h8 : ty.constsResolve lenv = true) :
    (ConLeche.installConstantVal ops lenv cv).run lst
      = .ok ({ cv with type := ty }, lst1) := by
  rw [ConLeche.installConstantVal]
  simp only [h1, h2, h3, h4, h5, h6, if_true, Bool.false_eq_true, if_false]
  simp only [StateT.run, Bind.bind, StateT.bind]
  rw [show (ops.annotate lenv 0 cv.type) lst = Except.ok (ty, lst1) from hann]
  simp only [Except.bind, h7, h8, reduceIte]
  rfl

open ConLeche.Cached in
/-- `installValue`, at a run all of whose guards passed. -/
theorem install_value_run {ops : ConLeche.CheckerOps CheckCM} {lenv : ConLeche.Env}
    {cv : ConLeche.ConstantVal} {value va : ConLeche.Expr} {lst lst1 : CState}
    (h1 : value.looseBVarsBounded 0 = true) (h2 : value.hasFvar = false)
    (hann : (ops.annotate lenv 0 value).run lst = .ok (va, lst1))
    (h3 : va.allLevelParamsDefined cv.levelParams = true)
    (h4 : va.constsResolve lenv = true) :
    (ConLeche.installValue ops lenv cv value).run lst = .ok (va, lst1) := by
  rw [ConLeche.installValue]
  simp only [h1, h2, if_true, Bool.false_eq_true, if_false]
  simp only [StateT.run, Bind.bind, StateT.bind]
  rw [show (ops.annotate lenv 0 value) lst = Except.ok (va, lst1) from hann]
  simp only [Except.bind, h3, h4, reduceIte]
  rfl

open ConLeche.Cached in
/-- `checkValueGroup` down to the join, on the **non-theorem** branch: the
sort ran and the join was `pure g.jv`, so what is left is the cited tail. -/
theorem check_value_group_head_plain {ops : ConLeche.CheckerOps CheckCM}
    {lenv : ConLeche.Env} {g : ConLeche.ValueGroup} {stype : ConLeche.Expr}
    {u : ConLeche.Level} {lst lst1 lst2 : CState}
    (hkind : ¬ g.kind = ConLeche.ValueKind.thm)
    (hinf : (ops.inferType lenv 0 g.cvA.type).run lst = .ok (stype, lst1))
    (hsort : (ops.ensureSort lenv 0 stype).run lst1 = .ok (u, lst2)) :
    (ConLeche.checkValueGroup ops lenv g).run lst
      = (do let vtype ← ops.inferType lenv 0 g.jv
            let okv ← ops.isDefEq lenv 0 vtype g.cvA.type
            if okv then pure () else
              throw (ConLeche.CheckError.invalid
                s!"type mismatch in {g.kind.word} {g.cvA.name}")).run lst2 := by
  rw [ConLeche.checkValueGroup]
  simp only [StateT.run, Bind.bind, StateT.bind]
  rw [show (ops.inferType lenv 0 g.cvA.type) lst = Except.ok (stype, lst1) from hinf]
  simp only [Except.bind]
  rw [show (ops.ensureSort lenv 0 stype) lst1 = Except.ok (u, lst2) from hsort]
  simp only [if_neg hkind]
  rfl

open ConLeche.Cached in
/-- `checkValueGroup` down to the join, on the **theorem** branch: the sort
ran, the level comparison said the statement is a proposition and the value's
install produced `jv`, so what is left is the cited tail at `jv`. -/
theorem check_value_group_head_thm {ops : ConLeche.CheckerOps CheckCM}
    {lenv : ConLeche.Env} {g : ConLeche.ValueGroup} {stype jv : ConLeche.Expr}
    {u : ConLeche.Level} {lst lst1 lst2 lst3 : CState}
    (hkind : g.kind = ConLeche.ValueKind.thm)
    (hinf : (ops.inferType lenv 0 g.cvA.type).run lst = .ok (stype, lst1))
    (hsort : (ops.ensureSort lenv 0 stype).run lst1 = .ok (u, lst2))
    (hprop : ConLeche.Level.isEquiv u ConLeche.Level.zero = some true)
    (hiv : (ConLeche.installValue ops lenv g.cvA g.jv).run lst2 = .ok (jv, lst3)) :
    (ConLeche.checkValueGroup ops lenv g).run lst
      = (do let vtype ← ops.inferType lenv 0 jv
            let okv ← ops.isDefEq lenv 0 vtype g.cvA.type
            if okv then pure () else
              throw (ConLeche.CheckError.invalid
                s!"type mismatch in {g.kind.word} {g.cvA.name}")).run lst3 := by
  rw [ConLeche.checkValueGroup]
  simp only [if_pos hkind]
  simp only [StateT.run, Bind.bind, StateT.bind]
  rw [show (ops.inferType lenv 0 g.cvA.type) lst = Except.ok (stype, lst1) from hinf]
  simp only [Except.bind]
  rw [show (ops.ensureSort lenv 0 stype) lst1 = Except.ok (u, lst2) from hsort]
  simp only [hprop, ConLeche.liftFueled, StateT.bind, StateT.pure,
    Pure.pure, Except.pure, reduceIte]
  rw [show (ConLeche.installValue ops lenv g.cvA g.jv) lst2 = Except.ok (jv, lst3) from hiv]
  rfl

open ConLeche.Cached in
/-- `checkValueGroup`'s tail past the join, at an inference and a conversion
that succeeded. -/
theorem tail_run {ops : ConLeche.CheckerOps CheckCM} {lenv : ConLeche.Env}
    {jv vt ty : ConLeche.Expr} {msg : String} {lst lst1 lst2 : CState}
    (hinf : (ops.inferType lenv 0 jv).run lst = .ok (vt, lst1))
    (hdef : (ops.isDefEq lenv 0 vt ty).run lst1 = .ok (true, lst2)) :
    (do let vtype ← ops.inferType lenv 0 jv
        let okv ← ops.isDefEq lenv 0 vtype ty
        if okv then pure () else throw (ConLeche.CheckError.invalid msg)).run lst
      = .ok ((), lst2) := by
  simp only [StateT.run, Bind.bind, StateT.bind]
  rw [show (ops.inferType lenv 0 jv) lst = Except.ok (vt, lst1) from hinf]
  simp only [Except.bind]
  rw [show (ops.isDefEq lenv 0 vt ty) lst1 = Except.ok (true, lst2) from hdef]
  rfl

/-! ## The install half -/

/-- **`checker_split::install_constant_val` refines `installConstantVal`**
(`CheckerSplit.lean:64-85`): `checkConstantVal` minus its inference — the six
syntactic guards, the annotation of the type, and the two post-annotation
guards.  The result is the header with its type replaced by the annotated one.

The six guards are each already refined (`Refine/FEnv.lean`'s `find_refines`,
`Refine/BasisNames.lean`'s `reserved_basis_names_refines`, `Refine/Name.lean`'s
`contains_refines`, `Refine/CoreKShapes.lean`'s
`name_is_proj_fn_shape_refines`, `Refine/CheckerBase.lean`'s
`name_nodup_refines`, `Refine/ExprOpsFields.lean`'s
`loose_bvars_bounded_refines`/`has_fvar_refines`), the annotation is
`Refine/TypeChecker.lean`'s `annotate_core_refines`, and the two after it are
`Refine/ExprOpsMeta.lean`'s `all_level_params_defined_fast_refines` and
`Refine/CoreKSupport.lean`'s `consts_resolve_refines`; the nine-level `if`
cascade is walked with `install_constant_val_run` as the cited side. -/
theorem install_constant_val_refines {mode : env.CheckMode} {fuel : Std.U64}
    (hfuel : core_k.check_fuel = ok fuel) (hk : Core.Wrappers mode fuel)
    (hp : CoreK.PinnedBasisNames)
    {st st' : cached.state_c.CState} {fe : fenv.FEnv}
    {cv cv' : env.ConstantVal}
    (hsw : StateWF st) (hfw : FEnvWF fe) (hcv : ConstantValWF cv)
    (h : checker_split.install_constant_val mode st fe cv = ok (.Ok cv', st')) :
    ∀ lst lfe (lenv : ConLeche.Env), StateRel st lst → FEnvRel fe lfe →
      (∀ n : ConLeche.Name, lfe.find? n = lenv.find? n) →
      ∃ lst',
        (ConLeche.installConstantVal (TypeChecker.lops mode lfe) lenv
            (absConstantVal cv)).run lst = .ok (absConstantVal cv', lst')
        ∧ StateRel st' lst' ∧ StateWF st' ∧ ConstantValWF cv' := by
  intro lst lfe lenv hsr hfr henv
  obtain ⟨hnwf, hlpwf, htywf⟩ := hcv
  rw [checker_split.install_constant_val] at h
  obtain ⟨o, ho, h⟩ := bind_eq_ok_iff.mp h
  have hfind := FEnv.find_refines hfr hfw hnwf ho
  cases o with
  | some ci => simp [core.option.Option.is_some, bind_eq_ok_iff] at h
  | none =>
    simp only [core.option.Option.is_some] at h
    have h1 : ((lenv.find? (absName cv.name)).isSome) = false := by
      rw [← henv, ← hfind]; simp
    obtain ⟨rv, hrv, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨b1, hb1, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨hrvabs, hrvwf⟩ := BasisNames.reserved_basis_names_refines hrv
    have hb1abs := Name.contains_refines hrvwf hnwf hb1
    rw [hrvabs] at hb1abs
    split at h
    · simp [bind_eq_ok_iff] at h
    · rename_i hb1f
      have h2 : ConLeche.reservedBasisNames.contains (absName cv.name) = false := by
        rw [← hb1abs]; simpa using hb1f
      obtain ⟨b2, hb2, h⟩ := bind_eq_ok_iff.mp h
      have hb2abs := CoreK.name_is_proj_fn_shape_refines hnwf hb2
      split at h
      · simp [bind_eq_ok_iff] at h
      · rename_i hb2f
        have h3 : (absName cv.name).isProjFnShape = false := by
          rw [← hb2abs]; simpa using hb2f
        obtain ⟨b3, hb3, h⟩ := bind_eq_ok_iff.mp h
        have hb3abs := CheckerBase.name_nodup_refines hlpwf hb3
        split at h
        · rename_i hb3t
          obtain ⟨b4, hb4, h⟩ := bind_eq_ok_iff.mp h
          have hb4abs := ExprOps.loose_bvars_bounded_refines htywf hb4
          rw [show ((0#u64 : Std.U64)).val = 0 from rfl] at hb4abs
          split at h
          · rename_i hb4t
            obtain ⟨b5, hb5, h⟩ := bind_eq_ok_iff.mp h
            have hb5abs := ExprOps.has_fvar_refines htywf hb5
            split at h
            · simp [bind_eq_ok_iff] at h
            · rename_i hb5f
              obtain ⟨q, hq, h⟩ := bind_eq_ok_iff.mp h
              obtain ⟨r1, st1⟩ := q
              cases r1 with
              | Err er => simp at h
              | Ok ty =>
                obtain ⟨lst1, hrun1, hsr1, hsw1, htyawf⟩ :=
                  (TypeChecker.annotate_core_refines hfuel hk).ok st fe 0#u64 cv.ty ty st1
                    hsw hfw htywf hq lst lfe hsr hfr
                obtain ⟨b6, hb6, h⟩ := bind_eq_ok_iff.mp h
                have hb6abs :=
                  ExprOps.all_level_params_defined_fast_refines hlpwf htyawf hb6
                split at h
                · rename_i hb6t
                  obtain ⟨b7, hb7, h⟩ := bind_eq_ok_iff.mp h
                  have hb7abs :=
                    CoreK.consts_resolve_refines hp (FindAgree.of_rel hfr hfw) henv htyawf _ hb7
                  split at h
                  · rename_i hb7t
                    obtain ⟨n, hn, h⟩ := bind_eq_ok_iff.mp h
                    obtain ⟨v1, hv1, h⟩ := bind_eq_ok_iff.mp h
                    have hnn : n = cv.name := by simpa using hn.symm
                    have hvv : v1.val = cv.level_params.val := PropWhen.names_copy_val hv1
                    obtain ⟨hcv'', hst⟩ :
                        ({ «name» := n, level_params := v1, ty } : env.ConstantVal) = cv'
                          ∧ st1 = st' := by simpa using h
                    subst hst
                    have hcvabs : absConstantVal cv'
                        = { absConstantVal cv with type := absExpr ty } := by
                      rw [← hcv'']
                      simp only [absConstantVal, hnn, absNames, hvv]
                    refine ⟨lst1, ?_, hsr1, hsw1, ?_⟩
                    · rw [hcvabs]
                      refine install_constant_val_run h1 h2 h3 ?_ ?_ ?_
                        (by rw [TypeChecker.sharedOpsC_annotate]; exact hrun1) ?_ ?_
                      · simp only [absConstantVal]; rw [← hb3abs]; exact hb3t
                      · simp only [absConstantVal]; rw [← hb4abs]; exact hb4t
                      · simp only [absConstantVal]; rw [← hb5abs]; simpa using hb5f
                      · simp only [absConstantVal]; rw [← hb6abs]; exact hb6t
                      · rw [← hb7abs]; exact hb7t
                    · rw [← hcv'']
                      exact ⟨hnn ▸ hnwf, fun m hm => hlpwf m (hvv ▸ hm), htyawf⟩
                  · simp [bind_eq_ok_iff] at h
                · simp [bind_eq_ok_iff] at h
          · simp [bind_eq_ok_iff] at h
        · simp [bind_eq_ok_iff] at h

/-- **`checker_split::install_value` refines `installValue`**
(`CheckerSplit.lean:87-100`): the value half of `check{Defn,Thm,Opaque}Val`
minus its inference — the two scope guards, the annotation, and the two
post-annotation guards.

The same five pieces as `install_constant_val_refines`, one `if` cascade
shorter; `install_value_run` is the cited side. -/
theorem install_value_refines {mode : env.CheckMode} {fuel : Std.U64}
    (hfuel : core_k.check_fuel = ok fuel) (hk : Core.Wrappers mode fuel)
    (hp : CoreK.PinnedBasisNames)
    {st st' : cached.state_c.CState} {fe : fenv.FEnv}
    {cv : env.ConstantVal} {value r : expr.Expr}
    (hsw : StateWF st) (hfw : FEnvWF fe) (hcv : ConstantValWF cv) (hv : ExprWF value)
    (h : checker_split.install_value mode st fe cv value = ok (.Ok r, st')) :
    ∀ lst lfe (lenv : ConLeche.Env), StateRel st lst → FEnvRel fe lfe →
      (∀ n : ConLeche.Name, lfe.find? n = lenv.find? n) →
      ∃ lst',
        (ConLeche.installValue (TypeChecker.lops mode lfe) lenv (absConstantVal cv)
            (absExpr value)).run lst = .ok (absExpr r, lst')
        ∧ StateRel st' lst' ∧ StateWF st' ∧ ExprWF r := by
  intro lst lfe lenv hsr hfr henv
  rw [checker_split.install_value] at h
  obtain ⟨b, hb, h⟩ := bind_eq_ok_iff.mp h
  have hbv := ExprOps.loose_bvars_bounded_refines hv hb
  cases b with
  | false => simp [bind_eq_ok_iff] at h
  | true =>
    obtain ⟨b1, hb1, h⟩ := bind_eq_ok_iff.mp h
    have hb1v := ExprOps.has_fvar_refines hv hb1
    cases b1 with
    | true => simp [bind_eq_ok_iff] at h
    | false =>
      obtain ⟨p, hq, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨r0, st1⟩ := p
      cases r0 with
      | Err er => simp at h
      | Ok va =>
        obtain ⟨lst1, hrun, hsr1, hsw1, hvaw⟩ :=
          (TypeChecker.annotate_core_refines hfuel hk).ok st fe 0#u64 value va st1
            hsw hfw hv hq lst lfe hsr hfr
        obtain ⟨b2, hb2, h⟩ := bind_eq_ok_iff.mp h
        have hb2v := ExprOps.all_level_params_defined_fast_refines hcv.2.1 hvaw hb2
        cases b2 with
        | false => simp [bind_eq_ok_iff] at h
        | true =>
          obtain ⟨b3, hb3, h⟩ := bind_eq_ok_iff.mp h
          have hb3v := CoreK.consts_resolve_refines hp (FindAgree.of_rel hfr hfw) henv hvaw _ hb3
          cases b3 with
          | false => simp [bind_eq_ok_iff] at h
          | true =>
            obtain ⟨hva, hst⟩ : va = r ∧ st1 = st' := by simpa using h
            subst hva; subst hst
            exact ⟨lst1, install_value_run hbv.symm hb1v.symm
              (by rw [TypeChecker.sharedOpsC_annotate]; exact hrun) hb2v.symm hb3v.symm,
              hsr1, hsw1, hvaw⟩

/-! ## The check half

`checkValueGroup` is one `do` block with a join in the middle (`let jv ← if
g.kind = .thm then … else pure g.jv`); the port splits it there so that both
branches are tail calls.  The pair of lemmas below is that split: the head
runs the sort and the theorem gate and hands the tail the post-join `jv`, and
the tail is stated at an arbitrary `jv`, which is what lets them compose. -/

/-- **`checker_split::check_value_group_tail` refines `checkValueGroup`'s tail**
(`CheckerSplit.lean:102-119`, past the join): the value's inferred type against
the declared one.  Stated at an arbitrary post-join `jv`.

`Refine/TypeChecker.lean`'s `infer_type_core_refines` and
`is_def_eq_core_refines`, then one `if`; `tail_run` is the cited side. -/
theorem check_value_group_tail_refines {mode : env.CheckMode} {fuel : Std.U64}
    (hfuel : core_k.check_fuel = ok fuel) (hk : Core.Wrappers mode fuel)
    {st st' : cached.state_c.CState} {fe : fenv.FEnv}
    {g : parsed_c.ValueGroup} {jv : expr.Expr}
    (hsw : StateWF st) (hfw : FEnvWF fe) (hg : ValueGroupWF g) (hjv : ExprWF jv)
    (h : checker_split.check_value_group_tail mode st fe g jv = ok (.Ok (), st')) :
    ∀ lst lfe, StateRel st lst → FEnvRel fe lfe →
      ∃ lst',
        (do let vtype ← (TypeChecker.lops mode lfe).inferType lfe.env 0 (absExpr jv)
            let ok ← (TypeChecker.lops mode lfe).isDefEq lfe.env 0 vtype
              (absValueGroup g).cvA.type
            if ok then pure () else
              throw (ConLeche.CheckError.invalid
                s!"type mismatch in {(absValueGroup g).kind.word} {(absValueGroup g).cvA.name}")).run lst
          = .ok ((), lst')
        ∧ StateRel st' lst' ∧ StateWF st' := by
  intro lst lfe hsr hfr
  rw [checker_split.check_value_group_tail] at h
  obtain ⟨p, hq, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨r, st1⟩ := p
  cases r with
  | Err er => simp at h
  | Ok vtype =>
    obtain ⟨lst1, hrun1, hsr1, hsw1, hvw⟩ :=
      (TypeChecker.infer_type_core_refines hfuel hk).ok st fe 0#u64 jv vtype st1
        hsw hfw hjv hq lst lfe hsr hfr
    obtain ⟨p2, hq2, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨r1, st2⟩ := p2
    cases r1 with
    | Err er => simp at h
    | Ok b =>
      cases b with
      | false => simp [bind_eq_ok_iff] at h
      | true =>
        have hst : st2 = st' := by simpa using h
        subst hst
        obtain ⟨lst2, hrun2, hsr2, hsw2⟩ :=
          (TypeChecker.is_def_eq_core_refines hfuel hk).ok st1 fe 0#u64 vtype g.cv_a.ty true st2
            hsw1 hfw hvw hg.1.2.2 hq2 lst1 lfe hsr1 hfr
        exact ⟨lst2, tail_run hrun1 hrun2, hsr2, hsw2⟩

/-- **`checker_split::check_value_group` refines `checkValueGroup`**
(`CheckerSplit.lean:102-119`): at the environment the constant was installed
at — the type's sort, the theorem's is-a-proposition test, for a theorem the
value's guards and annotation (a theorem's value reaches the check half raw),
and then the tail.

`infer_type_core_refines` and `ensure_sort_core_refines`, then
`Refine/CoreKVec.lean`'s `lift_fueled_refines` over `Refine/Level.lean`'s
`is_equiv_refines`, then `install_value_refines` and
`check_value_group_tail_refines` above; the cited side is
`check_value_group_head_{plain,thm}` down to the join and `tail_run` past it.

**The `FEnv.find? = Env.find?` agreement is a hypothesis here** — see the
module note: it is not derivable from `FEnvRel`/`FEnvWF`, and the statement is
false without it. -/
theorem check_value_group_refines {mode : env.CheckMode} {fuel : Std.U64}
    (hfuel : core_k.check_fuel = ok fuel) (hk : Core.Wrappers mode fuel)
    (hp : CoreK.PinnedBasisNames)
    {st st' : cached.state_c.CState} {fe : fenv.FEnv} {g : parsed_c.ValueGroup}
    (hsw : StateWF st) (hfw : FEnvWF fe) (hg : ValueGroupWF g)
    (h : checker_split.check_value_group mode st fe g = ok (.Ok (), st')) :
    ∀ lst lfe, StateRel st lst → FEnvRel fe lfe →
      (∀ n : ConLeche.Name, lfe.find? n = lfe.env.find? n) →
      ∃ lst',
        (ConLeche.checkValueGroup (TypeChecker.lops mode lfe) lfe.env
            (absValueGroup g)).run lst = .ok ((), lst')
        ∧ StateRel st' lst' ∧ StateWF st' := by
  intro lst lfe hsr hfr henv
  rw [checker_split.check_value_group] at h
  obtain ⟨q, hq, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨r0, st1⟩ := q
  cases r0 with
  | Err er => simp at h
  | Ok stype =>
    obtain ⟨lst1, hrun1, hsr1, hsw1, hstw⟩ :=
      (TypeChecker.infer_type_core_refines hfuel hk).ok st fe 0#u64 g.cv_a.ty stype st1
        hsw hfw hg.1.2.2 hq lst lfe hsr hfr
    obtain ⟨q2, hq2, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨r1, st2⟩ := q2
    cases r1 with
    | Err er => simp at h
    | Ok u =>
      obtain ⟨lst2, hrun2, hsr2, hsw2, huw⟩ :=
        (TypeChecker.ensure_sort_core_refines hfuel hk).ok st1 fe 0#u64 stype u st2
          hsw1 hfw hstw hq2 lst1 lfe hsr1 hfr
      have hinf : ((TypeChecker.lops mode lfe).inferType lfe.env 0
          (absValueGroup g).cvA.type).run lst = .ok (absExpr stype, lst1) := by
        rw [TypeChecker.sharedOpsC_inferType]; exact hrun1
      have hsort : ((TypeChecker.lops mode lfe).ensureSort lfe.env 0
          (absExpr stype)).run lst1 = .ok (absLevel u, lst2) := by
        rw [TypeChecker.sharedOpsC_ensureSort]; exact hrun2
      obtain ⟨b, hb, h⟩ := bind_eq_ok_iff.mp h
      have hbabs := is_thm_refines hb
      cases b with
      | false =>
        obtain ⟨e, he, h⟩ := bind_eq_ok_iff.mp h
        have hee : g.jv = e := by simpa using he
        subst hee
        obtain ⟨lst', hrunt, hsrt, hswt⟩ :=
          check_value_group_tail_refines hfuel hk hsw2 hfw hg hg.2 h lst2 lfe hsr2 hfr
        refine ⟨lst', ?_, hsrt, hswt⟩
        rw [check_value_group_head_plain (by simpa [absValueGroup] using hbabs.symm) hinf hsort]
        exact hrunt
      | true =>
        obtain ⟨l, hl, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨o, ho, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨r2, hr2, h⟩ := bind_eq_ok_iff.mp h
        have hlz : absLevel l = ConLeche.Level.zero := by rw [level_zero_inv hl]; rfl
        have hoabs := Level.is_equiv_refines huw (LevelWF.zero hl) ho
        cases r2 with
        | Err er => simp at h
        | Ok is_prop =>
          have hlf := CoreK.lift_fueled_refines hr2
          have hoq : o = some is_prop := by
            cases o with
            | none => simp [ConLeche.liftFueled] at hlf
            | some a => simpa [ConLeche.liftFueled, Pure.pure, Except.pure] using hlf
          cases is_prop with
          | false => simp [bind_eq_ok_iff] at h
          | true =>
            have hprop : ConLeche.Level.isEquiv (absLevel u) ConLeche.Level.zero = some true := by
              rw [← hlz, hoabs, hoq]
            obtain ⟨q3, hq3, h⟩ := bind_eq_ok_iff.mp h
            obtain ⟨r3, st3⟩ := q3
            cases r3 with
            | Err er => simp at h
            | Ok jv =>
              obtain ⟨lst3, hrun3, hsr3, hsw3, hjvw⟩ :=
                install_value_refines hfuel hk hp hsw2 hfw hg.1 hg.2 hq3 lst2 lfe lfe.env
                  hsr2 hfr henv
              obtain ⟨lst', hrunt, hsrt, hswt⟩ :=
                check_value_group_tail_refines hfuel hk hsw3 hfw hg hjvw h lst3 lfe hsr3 hfr
              refine ⟨lst', ?_, hsrt, hswt⟩
              rw [check_value_group_head_thm (by simpa [absValueGroup] using hbabs.symm) hinf hsort hprop hrun3]
              exact hrunt

/-! ## Axiom census (DESIGN.md §5, the P3 gate)

The two composite lemmas: `install_constant_val_refines` is the file's widest
chain (six guard refinements, the annotation and two post-annotation guards),
and `check_value_group_refines` is its deepest (the two core entry points, the
level comparison and both halves of the join). -/

/--
info: 'ConRon.Refine.CheckerSplit.install_constant_val_refines' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms install_constant_val_refines

/--
info: 'ConRon.Refine.CheckerSplit.check_value_group_refines' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms check_value_group_refines

end ConRon.Refine.CheckerSplit
