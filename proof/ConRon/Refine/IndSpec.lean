/-
# `IndRoutesSpec` — what the checker tier consumes from the inductive routes

`CORE_PLAN.md` step 7 splits in two: the checker tier (task #56) and the two
inductive routes (task #57, this file's siblings `Ind*.lean`).  The seam
between them is this one `Prop`: the two entry points `checker.rs`'s
`.indDecl` arm reaches, refined against the cached drivers of
`ConLeche/Cached/CheckerC.lean`.

* `kernel::inductives::inductives_c::check_native_s` against `checkNativeS`
  (`CheckerC.lean:217-231`) — the **direct (fixpoint) route**: a recognised
  block is checked against the reference kernels' own inductive-declaration
  checks and its recursor is *generated*.
* `kernel::inductives::inductives_c::check_ind_decl_s` against
  `checkIndDeclSF` (`CheckerC.lean:233-268`) — the **modeled route**: every
  member is checked against its `_model` artifact.

Both are in the standard exact-result shape of DESIGN.md §3.5: on a Rust
`.Ok` the con-leche driver run at a related state and index returns exactly
the abstracted result, the states stay related and the well-formedness
invariants are preserved; nothing is claimed on failure.  The returned value
is an `FEnv`, which `Refine/FEnv.lean` abstracts *relationally*, so the
conclusion is `∃ lfe'` — the con-leche index the driver returns — rather than
an equation.

Both take the knot as a hypothesis: the routes reach the core only through
`sharedOpsC`, i.e. through `Core.KnotSpec mode IndAbs.checkFuelU` (task #55
proves its arms).  `IndC.lean` discharges this `Prop` from the two entry
lemmas it proves.
-/
import ConRon.Refine.IndAbs

open Aeneas Aeneas.Std Result
open ConRon.Generated ConRon.Generated.kernel ConRon.Generated.cached
open ConRon.Refine ConRon.Refine.State ConRon.Refine.FEnv

namespace ConRon.Refine

/-- The two inductive routes, refined: what task #56's checker tier consumes
from task #57.  Indexed by the `CheckMode`, and stated under the knot at
`core_k::check_fuel()` — the fuel `sharedOpsC` ties it at. -/
structure IndRoutesSpec (mode : env.CheckMode) : Prop where
  /-- The direct (fixpoint) route: `check_native_s` against `checkNativeS`. -/
  checkNative :
    ∀ st fe p0 fe' st',
      StateWF st → FEnvWF fe → IndAbs.NativePartsWF p0 →
      kernel.inductives.inductives_c.check_native_s mode st fe p0
          = ok (.Ok fe', st') →
      ∀ lst lfe, StateRel st lst → FEnvRel fe lfe →
        ∃ lst' lfe',
          (ConLeche.Cached.checkNativeS (absMode mode) lfe
              (IndAbs.absNativeParts p0)).run lst = .ok (lfe', lst')
          ∧ StateRel st' lst' ∧ FEnvRel fe' lfe'
          ∧ StateWF st' ∧ FEnvWF fe'
  /-- The modeled route: `check_ind_decl_s` against `checkIndDeclSF`. -/
  checkIndDecl :
    ∀ st fe block fe' st',
      StateWF st → FEnvWF fe → ConstantInfosWF block →
      kernel.inductives.inductives_c.check_ind_decl_s mode st fe block
          = ok (.Ok fe', st') →
      ∀ lst lfe, StateRel st lst → FEnvRel fe lfe →
        ∃ lst' lfe',
          (ConLeche.Cached.checkIndDeclSF (absMode mode) lfe
              (absConstantInfos block)).run lst = .ok (lfe', lst')
          ∧ StateRel st' lst' ∧ FEnvRel fe' lfe'
          ∧ StateWF st' ∧ FEnvWF fe'

end ConRon.Refine
