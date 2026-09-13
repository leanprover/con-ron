import ConRon.Refine.State
import ConRon.Refine.FEnv
import ConLeche.Cached.CheckerC
import ConRon.Refine.IndAbs

/-! # `IndRoutesSpec` — the seam between task #56 and task #57

`checkDeclC`'s `.indDecl` arm (`ConLeche/Cached/ParsedC.lean:238-241`) is a
two-way dispatch on the *recogniser*: a recognised block takes the fixpoint
route (`checkNativeS`), every other one the modeled route (`checkIndDeclSF`).
Both routes are `ConLeche/Kernel/Inductives/*` plus
`ConLeche/Cached/CheckerC.lean`'s phase drivers — **task #57's** subject, not
this one's.  So this file names what task #56 needs of task #57, and nothing
more: two clauses, one per route, each already carrying the recogniser's
verdict, so that

* task #56 can state and prove `check_decl_c`'s `.indDecl` arm exactly, with
  `IndRoutesSpec mode` as a named hypothesis, and
* task #57 can prove `IndRoutesSpec mode` without reading task #56 at all.

## Why the recogniser's verdict is inside each clause

The alternative — a third clause "`native_parts` refines `nativeParts?`" —
would need an abstraction function `absNativeParts` for the port's
`NativeParts` record, which is task #57's to write (it has fourteen fields and
three nested shape records).  Folding the verdict into each route's clause
keeps this file free of it: the native clause says "when the port recognises
the block and the route succeeds, *there is* a Lean `NativeParts` the Lean
recogniser produces and `checkNativeS` at it agrees", and the modeled clause
says "when the port declines, so does the Lean recogniser".  That is exactly
the strength the `.indDecl` arm consumes, and it is minimal: nothing here
mentions a single field of either route's internals.

Both clauses are DESIGN.md §3.5's standard shape (`CORE_PLAN.md` step 7):
exact result on success, nothing on failure, `StateRel`/`FEnvRel` in and out,
`StateWF`/`FEnvWF` preserved — the `FEnv` the routes return is an *output*, so
it is existentially quantified and related by `FEnvRel`.

## The index the routes are handed must be its environment's rebuild (task #59)

Both clauses carry `FEnvCanon fe` and `FEnvFull fe` (`Refine/FEnv.lean`) as
well as `FEnvWF fe`.  That is **not** slack and not a weakening of convenience:
`native_install::check_native_pass_former` and `inductives_c::check_ind_recs_s`
both open by copying the index with `fenv::dup`, which *rebuilds* it from the
environment (`ron::hashmap` has no iteration API), and `FEnvRel` pins `lfe.idx`
only on the image of the well-formed names.  So for an `fe` whose index is not
its own environment's rebuild the copy is a *different* index from `fe`, the
port's later lookups differ from con-leche's at the `lfe` the caller keeps
across the copy, and **the conclusion is false**.  `FEnvFull` ("nothing is
hidden") is what `FEnv.push_canon` needs, because `FEnv.push` stamps the new
entry with `visibleBelow` while the rebuild stamps it with the constant count.

The consumer discharges both: every index the checker builds is `mk_fenv` or
`dup` followed by pushes (`FEnv.mk_fenv_canon`, `FEnv.dup_canon`,
`FEnv.push_canon`), and `restrict_to` — the only thing that hides — is never
called between a copy and its pushes.

## …and both clauses hand it back (task #59)

Each clause also *concludes* `FEnvCanon fe'` and `FEnvFull fe'` of the index
the route returns.  That is not decoration: `cached::installed`'s phase A folds
`check_decl_step_c` over the whole stream, so the index an `.indDecl` step
hands back is the next step's input, and without the pair coming back out the
fold could discharge the hypothesis only at position 0.  It is true for the
same reason it is assumed — both routes build their answer out of the index
they are given by `dup`s and `push`es — and `Refine/IndC.lean` proves it
alongside each route's refinement.

`sorry` count in this file: 0 (it declares a `Prop`; nothing is proved here).
-/
open Aeneas Aeneas.Std Result
open ConRon.Generated ConRon.Generated.kernel ConRon.Generated.cached
open ConRon.Refine ConRon.Refine.State ConRon.Refine.FEnv

namespace ConRon.Refine

/-- **What task #57 owes task #56**: the two inductive install routes of
`cached::parsed_c::check_ind_decl_c`, each at the recogniser verdict that
selects it. -/
structure IndRoutesSpec (mode : env.CheckMode) : Prop where
  /-- **Route A, the fixpoint install** (`inductives_c::check_native_s`
  against `ConLeche.Cached.checkNativeS`, `Cached/CheckerC.lean:213-226`):
  when `native_parts::native_parts` recognises the block, con-leche's
  `nativeParts?` recognises it too, and the route agrees on the recognised
  parts. -/
  native : ∀ (st : cached.state_c.CState) (fe : fenv.FEnv)
      (n_p : Std.U64) (block : alloc.vec.Vec env.ConstantInfo)
      (p : inductives.native_parts.NativeParts) (fe' : fenv.FEnv)
      (st' : cached.state_c.CState),
    StateWF st → FEnvWF fe → FEnvCanon fe → FEnvFull fe →
    ConstantInfosWF block →
    inductives.native_parts.native_parts n_p block = ok (some p) →
    inductives.inductives_c.check_native_s mode st fe p = ok (.Ok fe', st') →
    ∀ lst lfe, StateRel st lst → FEnvRel fe lfe →
      ∃ lst' lfe' lp,
        ConLeche.nativeParts? n_p.val (absConstantInfos block) = some lp
        ∧ (ConLeche.Cached.checkNativeS (absMode mode) lfe lp).run lst = .ok (lfe', lst')
        ∧ StateRel st' lst' ∧ StateWF st' ∧ FEnvRel fe' lfe' ∧ FEnvWF fe'
        ∧ FEnvCanon fe' ∧ FEnvFull fe'
  /-- **Route B, the modeled install** (`inductives_c::check_ind_decl_s`
  against `ConLeche.Cached.checkIndDeclSF`, `Cached/CheckerC.lean:228-269`):
  when `native_parts::native_parts` declines, so does `nativeParts?`, and the
  modeled route agrees. -/
  modeled : ∀ (st : cached.state_c.CState) (fe : fenv.FEnv)
      (n_p : Std.U64) (block : alloc.vec.Vec env.ConstantInfo)
      (fe' : fenv.FEnv) (st' : cached.state_c.CState),
    StateWF st → FEnvWF fe → FEnvCanon fe → FEnvFull fe →
    ConstantInfosWF block →
    inductives.native_parts.native_parts n_p block = ok none →
    inductives.inductives_c.check_ind_decl_s mode st fe block = ok (.Ok fe', st') →
    ∀ lst lfe, StateRel st lst → FEnvRel fe lfe →
      ∃ lst' lfe',
        ConLeche.nativeParts? n_p.val (absConstantInfos block) = none
        ∧ (ConLeche.Cached.checkIndDeclSF (absMode mode) lfe
              (absConstantInfos block)).run lst = .ok (lfe', lst')
        ∧ StateRel st' lst' ∧ StateWF st' ∧ FEnvRel fe' lfe' ∧ FEnvWF fe'
        ∧ FEnvCanon fe' ∧ FEnvFull fe'

/-- **The producer's form** (task #57): the two routes on already-recognised
parts, without the recogniser clause.  `IndRoutesSpec` (the consumer's form,
task #56) follows from it together with the recogniser's refinement
(`native_parts_refines`) — task #59 proves that bridge. -/
structure IndRoutesSpecP (mode : env.CheckMode) : Prop where
  /-- The direct (fixpoint) route: `check_native_s` against `checkNativeS`. -/
  checkNative :
    ∀ st fe p0 fe' st',
      StateWF st → FEnvWF fe → FEnvCanon fe → FEnvFull fe →
      IndAbs.NativePartsWF p0 →
      kernel.inductives.inductives_c.check_native_s mode st fe p0
          = ok (.Ok fe', st') →
      ∀ lst lfe, StateRel st lst → FEnvRel fe lfe →
        ∃ lst' lfe',
          (ConLeche.Cached.checkNativeS (absMode mode) lfe
              (IndAbs.absNativeParts p0)).run lst = .ok (lfe', lst')
          ∧ StateRel st' lst' ∧ FEnvRel fe' lfe'
          ∧ StateWF st' ∧ FEnvWF fe'
          ∧ FEnvCanon fe' ∧ FEnvFull fe'
  /-- The modeled route: `check_ind_decl_s` against `checkIndDeclSF`. -/
  checkIndDecl :
    ∀ st fe block fe' st',
      StateWF st → FEnvWF fe → FEnvCanon fe → FEnvFull fe →
      ConstantInfosWF block →
      kernel.inductives.inductives_c.check_ind_decl_s mode st fe block
          = ok (.Ok fe', st') →
      ∀ lst lfe, StateRel st lst → FEnvRel fe lfe →
        ∃ lst' lfe',
          (ConLeche.Cached.checkIndDeclSF (absMode mode) lfe
              (absConstantInfos block)).run lst = .ok (lfe', lst')
          ∧ StateRel st' lst' ∧ FEnvRel fe' lfe'
          ∧ StateWF st' ∧ FEnvWF fe'
          ∧ FEnvCanon fe' ∧ FEnvFull fe'


end ConRon.Refine
