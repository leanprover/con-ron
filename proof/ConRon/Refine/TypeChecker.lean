import ConRon.Refine.Core.Statements
import ConRon.Refine.CoreKGuards
import ConRon.Refine.CoreKVec
import ConLeche.Cached.CheckerC

/-! # `kernel::type_checker` — the checker's front door (task #56)

`CORE_PLAN.md` step 7, first file.  `kernel/type_checker.rs` is the **one
place the knot is named** (task #24's note 1): seven six-line functions over
`cached::core_c` at `core_k::check_fuel()`, which are simultaneously

* `ConLeche/Kernel/TypeChecker.lean`'s seven pure-lane entry points,
* `ConLeche/Kernel/CheckerBase.lean`'s `fueledOps mode checkFuel` = `pureOps`,
  in its five core slots, and
* `ConLeche/Cached/CheckerC.lean`'s `opE`/`opB`/`opS`, i.e. `sharedOpsC`'s five
  core slots — the record the *executed* declaration checker runs on.

DESIGN.md §3.1 gives the port **one** knot, the cached one, so a refinement
lemma about any of these is stated against `coreKnotI` (`CORE_PLAN.md`'s
step-6 statements), never against `coreKnot`: `pureFns`/`fueledOps` are cited
here and the lemmas below *are* their refinement too, because the Rust
functions are literally the same seven.

## The knot is assumed (task #55 discharges it)

Every lemma takes `Core.Wrappers mode fuel` — the six memoising wrappers'
refinement at `fuel` from `Refine/Core/Statements.lean` — as a hypothesis,
together with `core_k.check_fuel = ok fuel`.  `Refine/Core/Knot.lean`'s
`knot_induction` plus task #55's arms supply it at every fuel; until then it
travels as a hypothesis, and *no lemma in the declaration-checker tier proves
anything about the core*.  `CoreK.check_fuel_refines` turns the `U64` into
con-leche's `checkFuel`, which is what makes `knot mode lfe fuel.val` the
`coreKnotI mode lfe checkFuel` that `opE` builds.

## What the statements are stated against

`opE`/`opB`/`opS`, not `sharedOpsC`, because those are what the Rust cites and
because `opE` is higher-order in the slot selector (§3.4 forbids the closure,
so the port has it four times over).  The five `sharedOpsC` slot equalities
(`sharedOpsC_*`) are `rfl` and are what a downstream lemma about a Lean
function taking `ops : CheckerOps CheckCM` rewrites with: the slots ignore
their `Env` argument, which is exactly why the port can pass the index alone
(task #24's note 3).

`sorry` count in this file: 0.
-/
open Aeneas Aeneas.Std Result
open ConRon.Generated ConRon.Generated.kernel ConRon.Generated.cached
open ConRon.Refine ConRon.Refine.State ConRon.Refine.FEnv

namespace ConRon.Refine.TypeChecker

/-! ## The `Level`-valued refinement shape

`Refine/Core/Statements.lean` has `RefinesE` (`Expr`-valued) and `RefinesB`
(`Bool`-valued); `ensureSortCore` is the third shape.  **To be unified** with
those two once tasks #55/#56/#57 land (it belongs beside them). -/

/-- A `Level`-valued knot operation refines a Lean one: exact result on
success, `StateRel` in and out, `LevelWF` on the result. -/
def RefinesL
    (f : cached.state_c.CState → fenv.FEnv → Std.U64 → expr.Expr →
      Result ((core.result.Result level.Level core_types.CheckError) × cached.state_c.CState))
    (g : ConLeche.FEnv → Nat → ConLeche.Expr → ConLeche.Cached.CheckCM ConLeche.Level) : Prop :=
  ∀ st fe d e r st',
    StateWF st → FEnvWF fe → ExprWF e →
    f st fe d e = ok (.Ok r, st') →
    ∀ lst lfe, StateRel st lst → FEnvRel fe lfe →
      ∃ lst', (g lfe d.val (absExpr e)).run lst = .ok (absLevel r, lst')
        ∧ StateRel st' lst' ∧ StateWF st' ∧ LevelWF r

/-! ## `check_fuel` is `checkFuel`, inside the knot

The one rewriting step every lemma below starts with: the Rust reads the fuel
constant and hands it to the wrapper, and `CoreK.check_fuel_refines`
(`Refine/CoreKVec.lean`) says the constant is con-leche's. -/

/-- The fuel read, discharged: every entry point is `do let i ← check_fuel;
<wrapper> mode i …`. -/
theorem at_check_fuel {α : Type} {g : Std.U64 → Result α} {fuel : Std.U64} {v : α}
    (hfuel : core_k.check_fuel = ok fuel)
    (h : (do let i ← core_k.check_fuel; g i) = ok v) : g fuel = ok v := by
  rw [hfuel] at h; simpa using h

/-- `knot mode lfe fuel.val` is the record `opE` builds, once the fuel is the
checker's. -/
theorem knot_at_check_fuel {fuel : Std.U64} (hfuel : core_k.check_fuel = ok fuel)
    (mode : env.CheckMode) (lfe : ConLeche.FEnv) :
    Core.knot mode lfe fuel.val
      = ConLeche.Cached.coreKnotI (absMode mode) lfe ConLeche.checkFuel := by
  rw [Core.knot, ConRon.Refine.CoreK.check_fuel_refines hfuel]

/-! ## The seven entry points

Each is `do let i ← check_fuel; <wrapper> mode i st fe d e`, so each is the
matching `Core.Wrappers` field after one rewrite. -/

/-- `type_checker::whnf_core` refines `opE mode fe (·.whnfCore)`
(`TypeChecker.lean:27-29 whnfCore`, `CheckerC.lean:68-71 opE`). -/
theorem whnf_core_refines {mode : env.CheckMode} {fuel : Std.U64}
    (hfuel : core_k.check_fuel = ok fuel) (hk : Core.Wrappers mode fuel) :
    Core.RefinesE (type_checker.whnf_core mode)
      (fun lfe => ConLeche.Cached.opE (absMode mode) lfe (·.whnfCore)) := by
  intro st fe d e r st' hsw hfw hew h lst lfe hsr hfr
  rw [type_checker.whnf_core] at h
  replace h := at_check_fuel hfuel h
  obtain ⟨lst', hrun, rest⟩ := hk.whnfCore st fe d e r st' hsw hfw hew h lst lfe hsr hfr
  refine ⟨lst', ?_, rest⟩
  simp only [ConLeche.Cached.opE, ← knot_at_check_fuel hfuel]
  exact hrun

/-- `type_checker::whnf` refines `opE mode fe (·.whnf)` — `CheckerOps.whnf`
(`TypeChecker.lean:31-33 whnf`). -/
theorem whnf_refines {mode : env.CheckMode} {fuel : Std.U64}
    (hfuel : core_k.check_fuel = ok fuel) (hk : Core.Wrappers mode fuel) :
    Core.RefinesE (type_checker.whnf mode)
      (fun lfe => ConLeche.Cached.opE (absMode mode) lfe (·.whnf)) := by
  intro st fe d e r st' hsw hfw hew h lst lfe hsr hfr
  rw [type_checker.whnf] at h
  replace h := at_check_fuel hfuel h
  obtain ⟨lst', hrun, rest⟩ := hk.whnf st fe d e r st' hsw hfw hew h lst lfe hsr hfr
  refine ⟨lst', ?_, rest⟩
  simp only [ConLeche.Cached.opE, ← knot_at_check_fuel hfuel]
  exact hrun

/-- `type_checker::infer_type_core` refines `opE mode fe (·.infer)` —
`CheckerOps.inferType` (`TypeChecker.lean:35-38 inferTypeCore`). -/
theorem infer_type_core_refines {mode : env.CheckMode} {fuel : Std.U64}
    (hfuel : core_k.check_fuel = ok fuel) (hk : Core.Wrappers mode fuel) :
    Core.RefinesE (type_checker.infer_type_core mode)
      (fun lfe => ConLeche.Cached.opE (absMode mode) lfe (·.infer)) := by
  intro st fe d e r st' hsw hfw hew h lst lfe hsr hfr
  rw [type_checker.infer_type_core] at h
  replace h := at_check_fuel hfuel h
  obtain ⟨lst', hrun, rest⟩ := hk.infer st fe d e r st' hsw hfw hew h lst lfe hsr hfr
  refine ⟨lst', ?_, rest⟩
  simp only [ConLeche.Cached.opE, ← knot_at_check_fuel hfuel]
  exact hrun

/-- `type_checker::infer_type_io` refines the knot's `inferIO` slot
(`TypeChecker.lean:40-46 inferTypeIO`).  No declaration-level function calls
it — `CheckerOps` has no io slot — and it is refined here so the family stays
whole, exactly as the port keeps it. -/
theorem infer_type_io_refines {mode : env.CheckMode} {fuel : Std.U64}
    (hfuel : core_k.check_fuel = ok fuel) (hk : Core.Wrappers mode fuel) :
    Core.RefinesE (type_checker.infer_type_io mode)
      (fun lfe => ConLeche.Cached.opE (absMode mode) lfe (·.inferIO)) := by
  intro st fe d e r st' hsw hfw hew h lst lfe hsr hfr
  rw [type_checker.infer_type_io] at h
  replace h := at_check_fuel hfuel h
  obtain ⟨lst', hrun, rest⟩ := hk.inferIO st fe d e r st' hsw hfw hew h lst lfe hsr hfr
  refine ⟨lst', ?_, rest⟩
  simp only [ConLeche.Cached.opE, ← knot_at_check_fuel hfuel]
  exact hrun

/-- `type_checker::annotate_core` refines `opE mode fe (·.annotate)` —
`CheckerOps.annotate` (`TypeChecker.lean:52-54 annotateCore`). -/
theorem annotate_core_refines {mode : env.CheckMode} {fuel : Std.U64}
    (hfuel : core_k.check_fuel = ok fuel) (hk : Core.Wrappers mode fuel) :
    Core.RefinesE (type_checker.annotate_core mode)
      (fun lfe => ConLeche.Cached.opE (absMode mode) lfe (·.annotate)) := by
  intro st fe d e r st' hsw hfw hew h lst lfe hsr hfr
  rw [type_checker.annotate_core] at h
  replace h := at_check_fuel hfuel h
  obtain ⟨lst', hrun, rest⟩ := hk.annotate st fe d e r st' hsw hfw hew h lst lfe hsr hfr
  refine ⟨lst', ?_, rest⟩
  simp only [ConLeche.Cached.opE, ← knot_at_check_fuel hfuel]
  exact hrun

/-- `type_checker::is_def_eq_core` refines `opB` — `CheckerOps.isDefEq`
(`TypeChecker.lean:48-50 isDefEqCore`, `CheckerC.lean:73-75 opB`). -/
theorem is_def_eq_core_refines {mode : env.CheckMode} {fuel : Std.U64}
    (hfuel : core_k.check_fuel = ok fuel) (hk : Core.Wrappers mode fuel) :
    Core.RefinesB (type_checker.is_def_eq_core mode)
      (fun lfe => ConLeche.Cached.opB (absMode mode) lfe) := by
  intro st fe d a b r st' hsw hfw haw hbw h lst lfe hsr hfr
  rw [type_checker.is_def_eq_core] at h
  replace h := at_check_fuel hfuel h
  obtain ⟨lst', hrun, rest⟩ := hk.defeq st fe d a b r st' hsw hfw haw hbw h lst lfe hsr hfr
  refine ⟨lst', ?_, rest⟩
  simp only [ConLeche.Cached.opB, ← knot_at_check_fuel hfuel]
  exact hrun

/-! ## `ensureSort`, the one derived slot

`opS mode fe d e = ensureSortI (coreKnotI mode fe checkFuel) d e`, and
`ensureSortI` is `r.whnf` followed by a match on `.sort`; the Rust
(`core_c::ensure_sort_i`) is the same two steps with `level::dup` — the
identity in the model — on the result.  So this is `whnf_refines` plus
`ConRon.Refine.CoreK.wf_sort_inv`. -/

/-- `type_checker::ensure_sort_core` refines `opS` — `CheckerOps.ensureSort`
(`TypeChecker.lean:56-58 ensureSortCore`, `CheckerC.lean:77-79 opS`,
`CoreC.lean:1114-1119 ensureSortI`). -/
theorem ensure_sort_core_refines {mode : env.CheckMode} {fuel : Std.U64}
    (hfuel : core_k.check_fuel = ok fuel) (hk : Core.Wrappers mode fuel) :
    RefinesL (type_checker.ensure_sort_core mode)
      (fun lfe => ConLeche.Cached.opS (absMode mode) lfe) := by
  intro st fe d e r st' hsw hfw hew h lst lfe hsr hfr
  rw [type_checker.ensure_sort_core] at h
  replace h := at_check_fuel hfuel h
  rw [cached.core_c.ensure_sort_i] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨p, hw, h⟩ := h
  obtain ⟨res, stw⟩ := p
  cases res with
  | Err er => simp at h
  | Ok w =>
    obtain ⟨lstw, hrunw, hsrw, hsww, heww⟩ :=
      hk.whnf st fe d e w stw hsw hfw hew hw lst lfe hsr hfr
    obtain ⟨nd⟩ := w
    obtain ⟨dw, kw⟩ := nd
    cases kw
    case «Sort» u =>
      simp at h
      obtain ⟨rfl, rfl⟩ := h
      have hk2 : ((ConLeche.Cached.coreKnotI (absMode mode) lfe
              ConLeche.checkFuel).whnf d.val (absExpr e)).run lst
          = .ok (.sort (absLevel u), lstw) := by
        rw [← knot_at_check_fuel hfuel]; simpa using hrunw
      refine ⟨lstw, ?_, hsrw, hsww, ConRon.Refine.CoreK.wf_sort_inv heww rfl⟩
      simp [ConLeche.Cached.opS, ConLeche.Cached.ensureSortI, hk2]
      rfl
    all_goals simp at h


/-! ## `sharedOpsC`'s five slots

`rfl`, each: the slots *are* `opE`/`opB`/`opS`, and they ignore their `Env`
argument — which is why the port passes the index alone (task #24's note 3).
These are what a downstream lemma about a Lean function taking
`ops : CheckerOps CheckCM` rewrites with before applying the seven above. -/

/-- The Lean side's operation record at the cached knot. -/
abbrev lops (mode : env.CheckMode) (lfe : ConLeche.FEnv) :
    ConLeche.CheckerOps ConLeche.Cached.CheckCM :=
  ConLeche.Cached.sharedOpsC (absMode mode) lfe

@[simp] theorem sharedOpsC_whnf (mode : env.CheckMode) (lfe : ConLeche.FEnv)
    (lenv : ConLeche.Env) (d : Nat) (e : ConLeche.Expr) :
    (lops mode lfe).whnf lenv d e
      = ConLeche.Cached.opE (absMode mode) lfe (·.whnf) d e := rfl

@[simp] theorem sharedOpsC_inferType (mode : env.CheckMode) (lfe : ConLeche.FEnv)
    (lenv : ConLeche.Env) (d : Nat) (e : ConLeche.Expr) :
    (lops mode lfe).inferType lenv d e
      = ConLeche.Cached.opE (absMode mode) lfe (·.infer) d e := rfl

@[simp] theorem sharedOpsC_annotate (mode : env.CheckMode) (lfe : ConLeche.FEnv)
    (lenv : ConLeche.Env) (d : Nat) (e : ConLeche.Expr) :
    (lops mode lfe).annotate lenv d e
      = ConLeche.Cached.opE (absMode mode) lfe (·.annotate) d e := rfl

@[simp] theorem sharedOpsC_isDefEq (mode : env.CheckMode) (lfe : ConLeche.FEnv)
    (lenv : ConLeche.Env) (d : Nat) (a b : ConLeche.Expr) :
    (lops mode lfe).isDefEq lenv d a b
      = ConLeche.Cached.opB (absMode mode) lfe d a b := rfl

@[simp] theorem sharedOpsC_ensureSort (mode : env.CheckMode) (lfe : ConLeche.FEnv)
    (lenv : ConLeche.Env) (d : Nat) (e : ConLeche.Expr) :
    (lops mode lfe).ensureSort lenv d e
      = ConLeche.Cached.opS (absMode mode) lfe d e := rfl

end ConRon.Refine.TypeChecker
