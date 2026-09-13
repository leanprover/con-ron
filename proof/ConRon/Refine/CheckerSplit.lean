import ConRon.Refine.TypeChecker
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
  agreement `∀ n, lfe.find? n = lenv.find? n` — which at the *call sites*
  (`lenv = lfe.env`) is `FEnvRel`'s own first clause.

`sorry` count in this file: 4.
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

/-! ## The kind test -/

/-- **`checker_split::is_thm` is `g.kind = .thm`** — the cited `DecidableEq`
instance at the one value the check half branches on
(`CheckerSplit.lean:36-42`). -/
theorem is_thm_refines {k : parsed_c.ValueKind} {b : Bool}
    (h : checker_split.is_thm k = ok b) :
    b = decide (absValueKind k = ConLeche.ValueKind.thm) := by
  cases k <;> (rw [checker_split.is_thm] at h; rw [← Result.ok_injective h]) <;> rfl

/-! ## The install half -/

/-- **`checker_split::install_constant_val` refines `installConstantVal`**
(`CheckerSplit.lean:64-85`): `checkConstantVal` minus its inference — the six
syntactic guards, the annotation of the type, and the two post-annotation
guards.  The result is the header with its type replaced by the annotated one.

`sorry`: the six guards are each already refined
(`Refine/FEnv.lean`'s `find_refines`, `Refine/BasisNames.lean`'s
`reserved_basis_names_refines`, `Refine/Name.lean`'s `contains_refines`,
`Refine/CoreKShapes.lean`'s `name_is_proj_fn_shape_refines`,
`Refine/Level.lean`'s `name_nodup`, `Refine/ExprOpsFields.lean`'s
`loose_bvars_bounded_refines`/`has_fvar_refines`), the annotation is
`Refine/TypeChecker.lean`'s `annotate_core_refines`, and the two after it are
`Refine/ExprOpsMeta.lean`'s `all_level_params_defined_fast_refines` and
`Refine/CoreKSupport.lean`'s `consts_resolve_refines`; what is left is the
nine-level `if` cascade, which is bulk, not idea. -/
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
  sorry

/-- **`checker_split::install_value` refines `installValue`**
(`CheckerSplit.lean:87-100`): the value half of `check{Defn,Thm,Opaque}Val`
minus its inference — the two scope guards, the annotation, and the two
post-annotation guards.

`sorry`: the same five pieces as `install_constant_val_refines`, one `if`
cascade shorter. -/
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
  sorry

/-! ## The check half

`checkValueGroup` is one `do` block with a join in the middle (`let jv ← if
g.kind = .thm then … else pure g.jv`); the port splits it there so that both
branches are tail calls.  The pair of lemmas below is that split: the head
runs the sort and the theorem gate and hands the tail the post-join `jv`, and
the tail is stated at an arbitrary `jv`, which is what lets them compose. -/

/-- **`checker_split::check_value_group_tail` refines `checkValueGroup`'s tail**
(`CheckerSplit.lean:102-119`, past the join): the value's inferred type against
the declared one.  Stated at an arbitrary post-join `jv`.

`sorry`: `Refine/TypeChecker.lean`'s `infer_type_core_refines` and
`is_def_eq_core_refines`, then one `if`. -/
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
  sorry

/-- **`checker_split::check_value_group` refines `checkValueGroup`**
(`CheckerSplit.lean:102-119`): at the environment the constant was installed
at — the type's sort, the theorem's is-a-proposition test, for a theorem the
value's guards and annotation (a theorem's value reaches the check half raw),
and then the tail.

`sorry`: `infer_type_core_refines` and `ensure_sort_core_refines`, then
`Refine/CoreKVec.lean`'s `lift_fueled_refines` over `Refine/Level.lean`'s
`is_equiv_refines`, then `install_value_refines` and
`check_value_group_tail_refines` above. -/
theorem check_value_group_refines {mode : env.CheckMode} {fuel : Std.U64}
    (hfuel : core_k.check_fuel = ok fuel) (hk : Core.Wrappers mode fuel)
    (hp : CoreK.PinnedBasisNames)
    {st st' : cached.state_c.CState} {fe : fenv.FEnv} {g : parsed_c.ValueGroup}
    (hsw : StateWF st) (hfw : FEnvWF fe) (hg : ValueGroupWF g)
    (h : checker_split.check_value_group mode st fe g = ok (.Ok (), st')) :
    ∀ lst lfe, StateRel st lst → FEnvRel fe lfe →
      ∃ lst',
        (ConLeche.checkValueGroup (TypeChecker.lops mode lfe) lfe.env
            (absValueGroup g)).run lst = .ok ((), lst')
        ∧ StateRel st' lst' ∧ StateWF st' := by
  sorry

end ConRon.Refine.CheckerSplit
