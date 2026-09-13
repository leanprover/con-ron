/-
# The arms every cluster shares (task #55, `CORE_PLAN.md` step 6)

Two helpers of `crates/con-ron-core/src/cached/core_c.rs`'s
`partial_fixpoint` block are called from *otherwise disjoint* clusters, so
they live here rather than in any one cluster's file:

* `ensure_sort_i` (`core_c.rs:2604`) — con-leche's `ensureSortI`
  (`ConLeche/Cached/CoreC.lean:1115`), the binder-telescope loops' "this type
  is a sort, and here is its level";
* `infer_io_whnf_i` (`core_c.rs:1445`) — the two-line `r.whnf depth (←
  r.inferIO depth major)` that con-leche writes *inline* in `majorToCtorI`
  (`ConLeche/Cached/CoreC.lean:557-558`), which all three ι-rescue branches
  open with.

Neither calls anything outside the six wrappers, so neither needs a `Deps`
structure: `Wrappers mode fuel` is the whole of their hypothesis, and this
file is the one every other arms file may lean on.

The `.M`-suffixed `Array Std.U32` constants of the block (here
`cached.core_c.ensure_sort_i.M`) are error-message code points, reached only
on the `.Err` path; nothing is claimed on failure (DESIGN.md §3.5), so they
carry no theorem.
-/
import ConRon.Refine.Core.Arms.Shape
import ConRon.Refine.CoreKGuards

open Aeneas Aeneas.Std Result
open ConRon.Generated ConRon.Generated.kernel ConRon.Generated.cached
open ConRon.Refine ConRon.Refine.State ConRon.Refine.FEnv

namespace ConRon.Refine.Core

/-! `attribute [local simp]` does not travel across files, so `Shape.lean`'s
monad-plumbing set (`CheckCM = StateT CState (Except CheckError)`) is
re-declared here verbatim. -/
attribute [local simp] except_pure' StateT.run modifyGet MonadStateOf.modifyGet
  StateT.modifyGet Bind.bind StateT.bind Pure.pure StateT.pure Except.bind
  Except.pure

/-- `bind_eq_ok_iff` in the form `simp` leaves a `Result` bind in once
`Bind.bind` has been unfolded (the set above unfolds it for the `Except`
side, which stops `bind_eq_ok_iff` from matching). -/
theorem std_bind_eq_ok {α β : Type} {e : Result α} {f : α → Result β} {v : β}
    (h : Std.bind e f = ok v) : ∃ y, e = ok y ∧ f y = ok v :=
  bind_eq_ok_iff.mp h

section
variable {mode : env.CheckMode} {fuel : Std.U64}

/-- `ConLeche/Cached/CoreC.lean:1115` — **`ensure_sort_i` refines
`ensureSortI`**: `r.whnf depth e` and then a `Sort` node, whose level is the
result (`core_c.rs:2604`).  con-leche's twin takes no `FEnv` — the record
`knot mode lfe fuel.val` is where `lfe` enters — but the Rust threads `fe`,
so this is a `Sim` whose Lean side reads `lfe` only through the knot; a
caller holding `FEnvRel fe lfe` applies it unchanged.  The value abstraction
is `absLevel`, and the level handed back is well formed (it is a sub-level of
a well-formed node), which is what the callers in the binder-telescope loops
need. -/
theorem ensure_sort_i_refines (hw : Wrappers mode fuel) (d : Std.U64)
    {e : expr.Expr} (he : ExprWF e) :
    Sim absLevel LevelWF
      (fun st fe => cached.core_c.ensure_sort_i mode fuel st fe d e)
      (fun lfe => ConLeche.Cached.ensureSortI (knot mode lfe fuel.val) d.val
        (absExpr e)) := by
  intro fe lfe hfe hfrel st r st' hwf hok lst hrel
  unfold cached.core_c.ensure_sort_i at hok
  simp only [bind_eq_ok_iff] at hok
  obtain ⟨⟨r0, st1⟩, h1, hok⟩ := hok
  cases r0 with
  | Err err => simp at hok
  | Ok w =>
    obtain ⟨lst1, hrun1, hrel1, hwf1, hwWF⟩ :=
      (hw.whnfSim d he).apply hwf hfe h1 hrel hfrel
    obtain ⟨⟨dw, k⟩⟩ := w
    cases k with
    | «Sort» u =>
      simp at hok
      obtain ⟨rfl, rfl⟩ := hok
      refine ⟨lst1, ?_, hrel1, hwf1, CoreK.wf_sort_inv hwWF rfl⟩
      simp only [absExpr_mk, absExprKind, StateT.run] at hrun1
      simp [ConLeche.Cached.ensureSortI, hrun1]
    | _ =>
      simp at hok
      obtain ⟨v, -, hok⟩ := std_bind_eq_ok hok
      obtain ⟨ce, -, hok⟩ := std_bind_eq_ok hok
      simp at hok

/-- `ConLeche/Cached/CoreC.lean:557-558` — **`infer_io_whnf_i` refines
`majorToCtorI`'s opening two lines**: `let tmaj₀ ← r.inferIO depth major;
r.whnf depth tmaj₀` (`core_c.rs:1445`).  con-leche writes the pair inline in
each of `majorToCtorI`'s three rescue branches, so the Lean side here is that
`do` block, not a named definition. -/
theorem infer_io_whnf_i_refines (hw : Wrappers mode fuel) (d : Std.U64)
    {e : expr.Expr} (he : ExprWF e) :
    Sim absExpr ExprWF
      (fun st fe => cached.core_c.infer_io_whnf_i mode fuel st fe d e)
      (fun lfe => do
        let t ← (knot mode lfe fuel.val).inferIO d.val (absExpr e)
        (knot mode lfe fuel.val).whnf d.val t) := by
  intro fe lfe hfe hfrel st r st' hwf hok lst hrel
  unfold cached.core_c.infer_io_whnf_i at hok
  simp only [bind_eq_ok_iff] at hok
  obtain ⟨⟨r0, st1⟩, h1, hok⟩ := hok
  cases r0 with
  | Err err => simp at hok
  | Ok t =>
    obtain ⟨lst1, hrun1, hrel1, hwf1, htWF⟩ :=
      (hw.inferIOSim d he).apply hwf hfe h1 hrel hfrel
    obtain ⟨lst2, hrun2, hrel2, hwf2, hrWF⟩ :=
      (hw.whnfSim d htWF).apply hwf1 hfe hok hrel1 hfrel
    simp only [StateT.run] at hrun1 hrun2
    exact ⟨lst2, by simp [hrun1, hrun2], hrel2, hwf2, hrWF⟩

end

end ConRon.Refine.Core
