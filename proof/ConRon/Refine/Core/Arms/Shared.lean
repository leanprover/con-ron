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

Both lemmas are stated at the **full outcome** (task #67, DESIGN.md §3's
ruling of 2026-09-13): the accept direction as before, and on a failure
con-leche's own `throw` at the same kind.  Every error either comes from one
of the two wrappers — carried through con-leche's `do` block by
`ErrSim.bindCM` when the *first* step threw and by `ErrSim.trans` when a
later one did — or is `ensure_sort_i`'s single explicit `throw`, which the
`.M`-suffixed `Array Std.U32` constant of the block (here
`cached.core_c.ensure_sort_i.M`) spells as code points.  Messages are never
compared (DESIGN.md §3.1), so that constant still carries no theorem of its
own: `ErrSim.invalid` only has to name the string con-leche throws.
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

/-- **`throw` in `CheckCM`**: `Shape.lean`'s plumbing set does not carry the
`MonadExcept` instance, so `simp` leaves a `throw` arm of con-leche's un-run.
This is the one extra rewrite an explicit `throw` arm needs (task #67). -/
@[local simp] theorem checkCM_throw_apply {β : Type} (le : ConLeche.CheckError)
    (lst : ConLeche.Cached.CState) :
    (throw le : ConLeche.Cached.CheckCM β) lst = .error le := rfl

/-- The port's `Err` value at a mirrored `throw` arm: `core_types::invalid`
is the `Invalid` constructor, so an `Err` built from it is `Err (.Invalid v)`
(task #67).  `Refine/CoreKInfer.lean` does the same bookkeeping for
`core_k.rs`'s arms; this is the one `core_c.rs` arm this file meets. -/
private theorem invalid_err {v : alloc.vec.Vec Std.U32}
    {ce : core_types.CheckError} (h : core_types.invalid v = ok ce) :
    ce = .Invalid v :=
  (Result.ok_injective (by rw [core_types.invalid] at h; exact h)).symm

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
need.

At the full outcome there are two failures, and both are mirrored: `r.whnf`
threw (`ErrSim.bindCM` through con-leche's bind), or the reduced type was not
a `Sort` and both sides throw `invalid` — the port at `ensure_sort_i.M`, the
Lean at `"expected a sort"`. -/
theorem ensure_sort_i_refines (hw : Wrappers mode fuel) (d : Std.U64)
    {e : expr.Expr} (he : ExprWF e) :
    Sim absLevel LevelWF
      (fun st fe => cached.core_c.ensure_sort_i mode fuel st fe d e)
      (fun lfe => ConLeche.Cached.ensureSortI (knot mode lfe fuel.val) d.val
        (absExpr e)) := by
  intro fe lfe hfe hfrel st o st' hwf hok lst hrel
  unfold cached.core_c.ensure_sort_i at hok
  simp only [bind_eq_ok_iff] at hok
  obtain ⟨⟨r0, st1⟩, h1, hok⟩ := hok
  cases r0 with
  | Err err =>
    simp at hok
    obtain ⟨rfl, rfl⟩ := hok
    refine Out.err ?_
    unfold ConLeche.Cached.ensureSortI
    exact ErrSim.bindCM ((hw.whnfSim d he).apply_err hwf hfe h1 hrel hfrel)
  | Ok w =>
    obtain ⟨lst1, hrun1, hrel1, hwf1, hwWF⟩ :=
      (hw.whnfSim d he).apply hwf hfe h1 hrel hfrel
    obtain ⟨⟨dw, k⟩⟩ := w
    simp only [absExpr_mk, StateT.run] at hrun1
    cases k with
    | «Sort» u =>
      simp [ron.node.ExprView.ofKind] at hok
      obtain ⟨rfl, rfl⟩ := hok
      refine Out.ok (lst' := lst1) ?_ hrel1 hwf1 (CoreK.wf_sort_inv hwWF rfl)
      simp [ConLeche.Cached.ensureSortI, hrun1]
    | _ =>
      simp at hok
      obtain ⟨v, -, hok⟩ := std_bind_eq_ok hok
      obtain ⟨ce, hce, hok⟩ := std_bind_eq_ok hok
      simp only [Result.ok.injEq, Prod.mk.injEq] at hok
      obtain ⟨rfl, rfl⟩ := hok
      rw [invalid_err hce]
      refine Out.err (ErrSim.invalid (s := "expected a sort") ?_)
      simp [ConLeche.Cached.ensureSortI, hrun1]

/-- `ConLeche/Cached/CoreC.lean:557-558` — **`infer_io_whnf_i` refines
`majorToCtorI`'s opening two lines**: `let tmaj₀ ← r.inferIO depth major;
r.whnf depth tmaj₀` (`core_c.rs:1445`).  con-leche writes the pair inline in
each of `majorToCtorI`'s three rescue branches, so the Lean side here is that
`do` block, not a named definition.

It throws nothing of its own: at the full outcome (task #67) either
`r.inferIO` threw, and con-leche's bind carries it, or `r.whnf` threw, and it
is the whole block's error on both sides. -/
theorem infer_io_whnf_i_refines (hw : Wrappers mode fuel) (d : Std.U64)
    {e : expr.Expr} (he : ExprWF e) :
    Sim absExpr ExprWF
      (fun st fe => cached.core_c.infer_io_whnf_i mode fuel st fe d e)
      (fun lfe => do
        let t ← (knot mode lfe fuel.val).inferIO d.val (absExpr e)
        (knot mode lfe fuel.val).whnf d.val t) := by
  intro fe lfe hfe hfrel st o st' hwf hok lst hrel
  unfold cached.core_c.infer_io_whnf_i at hok
  simp only [bind_eq_ok_iff] at hok
  obtain ⟨⟨r0, st1⟩, h1, hok⟩ := hok
  cases r0 with
  | Err err =>
    simp at hok
    obtain ⟨rfl, rfl⟩ := hok
    exact Out.err (ErrSim.bindCM ((hw.inferIOSim d he).apply_err hwf hfe h1 hrel hfrel))
  | Ok t =>
    obtain ⟨lst1, hrun1, hrel1, hwf1, htWF⟩ :=
      (hw.inferIOSim d he).apply hwf hfe h1 hrel hfrel
    simp only [StateT.run] at hrun1
    cases o with
    | Ok r =>
      obtain ⟨lst2, hrun2, hrel2, hwf2, hrWF⟩ :=
        (hw.whnfSim d htWF).apply hwf1 hfe hok hrel1 hfrel
      simp only [StateT.run] at hrun2
      exact Out.ok (lst' := lst2) (by simp [hrun1, hrun2]) hrel2 hwf2 hrWF
    | Err ce =>
      refine Out.err (ErrSim.trans
        ((hw.whnfSim d htWF).apply_err hwf1 hfe hok hrel1 hfrel) ?_)
      intro le hle
      simp only [StateT.run] at hle
      simp [hrun1, hle]

end

end ConRon.Refine.Core
