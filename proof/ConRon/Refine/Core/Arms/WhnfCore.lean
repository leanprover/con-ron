/-
# The `whnf_core` body: the step, the loop, the body (task #55)

`crates/con-ron-core/src/cached/core_c.rs:2369-2527` against
`ConLeche/Cached/CoreC.lean:942-1009`.  Three functions:

* `whnf_core_step_i` — one head-normalization step (`whnfCoreStepI`), the ten
  `ExprKind` arms.  Six are the identity (`expr::dup` where the Lean hands
  back the node), two are the cited throws, and two delegate: `.app` to
  `whnf_app_i` after the spine head's `whnf_core`, `.proj` to
  `whnf_core_proj_i` after `whnf` and `proj_lit_to_ctor_i`.
* `whnf_core_loop_i` — the step at its own `U64` budget (`whnfCoreLoopI`,
  which recurses structurally on a `Nat`).  **No induction here**: the Rust
  loop at `n` calls the step at `n - 1`, con-leche's loop at `n + 1` calls the
  step with the loop at `n` as its continuation `k`, and the step's statement
  is parametric in that budget — as are the two `Deps` fields it delegates to.
  Task #61 made `WhnfCoreDeps` *indexed* by that budget, which is what breaks
  the packaging cycle with `Arms/App.lean` (see the record's doc comment); the
  one induction on the budget lives in `Arms/Arms.lean`, where both files are
  in scope.
* `whnf_core_body_i` — the loop at `core_k::whnf_core_loop_fuel`
  (`whnfCoreLoopFuel`, task #49's `Refine/CoreKVec.lean`).  This is the
  `Bodies.whnfCore` arm.

The `.M`-suffixed code-point arrays are error messages on the `.Err` path, so
they carry no obligation: the `Sim` shape claims nothing on failure
(DESIGN.md §3.5).
-/
import ConRon.Refine.Core.Arms.Shape
import ConRon.Refine.ExprOpsC
import ConRon.Refine.CoreKVec
import ConRon.Refine.Nat

open Aeneas Aeneas.Std Result
open ConRon.Generated ConRon.Generated.kernel ConRon.Generated.cached
open ConRon.Refine ConRon.Refine.State ConRon.Refine.FEnv

namespace ConRon.Refine.Core

/-! ## One `CheckCM` bind, run

`Refine/StateC.lean`'s note applies: `simp` will not push a state argument
through a `match`, so the arms are composed one bind at a time.  It and the
named `.proj` arm below live in a private namespace, so that the sibling arm
files may carry their own copy without a clash. -/

namespace WhnfCore

/-- `(x >>= f).run lst` at a known `x.run lst`. -/
theorem run_bind {α β : Type} {x : ConLeche.Cached.CheckCM α}
    {f : α → ConLeche.Cached.CheckCM β} {lst lst' : ConLeche.Cached.CState} {a : α}
    (h : x.run lst = .ok (a, lst')) :
    (x >>= f).run lst = (f a).run lst' := by
  simp only [StateT.run, Bind.bind, StateT.bind] at h ⊢
  rw [h]
  rfl

/-! ## The `.proj` arm as a named action

`whnf_core_proj_i` (`core_c.rs:2429`) is the continuation of
`whnfCoreStepI`'s `.proj` arm on the already-reduced scrutinee, and con-leche
keeps that continuation *inline* (`CoreC.lean:967-989`): there is no
`whnfCoreProjI` to cite.  So the arm is named here, as a `rfl`-identity
against the cited definition (`whnfCoreStepI_proj` below), and it is that name
the `WhnfCoreDeps.whnfCoreProj` field is stated against.  `Arms/App.lean`,
which owns `whnf_core_proj_i` itself, names the same action `whnfCoreProjI`;
the two are the same subterm of `whnfCoreStepI`, so each is the other by
`rfl` and the coordinator discharges the field with App's lemma. -/

/-- `ConLeche/Cached/CoreC.lean:967-989` — the `.proj` arm of `whnfCoreStepI`
below its two leading reductions: the structural rule
`proj_i (ctor p⃗ x⃗) ↦ x_i`, behind the projection table's counts, its
`fireOk` level guard and `projCertAtI`. -/
def whnfCoreProjArmI (mode : ConLeche.CheckMode) (r : ConLeche.Cached.CoreFnsI)
    (fe : ConLeche.FEnv) (depth : Nat)
    (k : ConLeche.Cached.ExprC → ConLeche.Cached.CheckCM ConLeche.Cached.ExprC)
    (sn : ConLeche.Name) (i : Nat) (e' : ConLeche.Cached.ExprC) :
    ConLeche.Cached.CheckCM ConLeche.Cached.ExprC :=
  match fe.findProj? sn i with
  | some entry =>
    match ConLeche.Cached.ExprC.getAppFn e' with
    | .const c us => do
      let args ← pure (ConLeche.Cached.ExprC.getAppArgs e')
      if (← pure (c == entry.ctor)) ∧ i < entry.numFields ∧
          args.length = entry.numParams + entry.numFields ∧
          us.length = entry.levelParams.length ∧
          entry.fireOk us = true then do
        let bvar0 ← pure (ConLeche.Expr.mkBvar 0)
        let arg := args.getD (entry.numParams + i) bvar0
        if ← ConLeche.Cached.projCertAtI r fe depth mode.verifiedChecks mode.betaGate
            c us args then
          k arg
        else pure (ConLeche.Expr.proj sn i e')
      else pure (ConLeche.Expr.proj sn i e')
    | _ => pure (ConLeche.Expr.proj sn i e')
  | none => pure (ConLeche.Expr.proj sn i e')

/-- `whnfCoreProjArmI` is literally `whnfCoreStepI`'s `.proj` arm. -/
theorem whnfCoreStepI_proj (mode : ConLeche.CheckMode) (r : ConLeche.Cached.CoreFnsI)
    (fe : ConLeche.FEnv) (depth : Nat)
    (k : ConLeche.Cached.ExprC → ConLeche.Cached.CheckCM ConLeche.Cached.ExprC)
    (sn : ConLeche.Name) (i : Nat) (pe : ConLeche.Cached.ExprC) :
    ConLeche.Cached.whnfCoreStepI mode r fe depth k (.proj sn i pe)
      = (do
          let e' ← r.whnf depth pe
          let e' ← ConLeche.Cached.projLitToCtorI r fe depth e'
          whnfCoreProjArmI mode r fe depth k sn i e') := rfl

end WhnfCore

open WhnfCore

/-- `CoreC.lean:1000-1004` — one unrolling of `whnfCoreLoopI`: the step at the
decremented budget, with the loop itself as the continuation `k`. -/
theorem whnfCoreLoopI_succ (mode : ConLeche.CheckMode) (r : ConLeche.Cached.CoreFnsI)
    (fe : ConLeche.FEnv) (depth m : Nat) (e : ConLeche.Cached.ExprC) :
    ConLeche.Cached.whnfCoreLoopI mode r fe depth (m + 1) e
      = ConLeche.Cached.whnfCoreStepI mode r fe depth
          (ConLeche.Cached.whnfCoreLoopI mode r fe depth m) e := by
  rw [ConLeche.Cached.whnfCoreLoopI]

/-! ## What lives in another arm's file -/

/-- The three helpers of the `whnf_core` body that live in another arm file:
`whnf_app_i` and `whnf_core_proj_i` (`Arms/App.lean`) and `proj_lit_to_ctor_i`
(`Arms/Major.lean`).  Each field is the statement that helper's own
`*_refines` has; the coordinator discharges the structure.

**Indexed by the budget `n`** (task #61).  `whnf_core_loop_i`,
`whnf_core_step_i`, `whnf_app_i` and `beta_peel_i` are one strongly connected
component of the Rust block, and task #55's partition put it in two files with
`∀ n`-quantified `Deps` fields, so neither `WhnfCoreDeps` nor `Arms/App.lean`'s
`AppDeps` could be built without the other.  The recursion is well founded in
the budget — loop(n+1) is step(n), step(n) calls whnfApp(n) and
whnfCoreProj(n), and both of those call loop(n) — so fixing `n` in this record
breaks the packaging cycle without weakening anything: `whnf_core_step_i` at
`n` needs its two callees only at `n`, and `whnf_core_loop_i` at `n` needs the
record only at budgets **below** `n`. -/
structure WhnfCoreDeps (mode : env.CheckMode) (fuel n : Std.U64) : Prop where
  /-- `core_c.rs:2218` — the spine loop of the `.app` arm, at the loop's own
  continuation budget `n`; the Rust index `i` is the suffix
  `(absExprs args).drop i.val`. -/
  whnfApp : ∀ (d : Std.U64) (f : expr.Expr) (args : alloc.vec.Vec expr.Expr)
      (i : Std.Usize), ExprWF f → ExprsWF args →
    Sim absExpr ExprWF
      (fun st fe => cached.core_c.whnf_app_i mode fuel st fe d n f args i)
      (fun lfe => ConLeche.Cached.whnfAppI (absMode mode) (knot mode lfe fuel.val) lfe
        d.val
        (ConLeche.Cached.whnfCoreLoopI (absMode mode) (knot mode lfe fuel.val) lfe
          d.val n.val)
        (absExpr f) ((absExprs args).drop i.val))
  /-- `core_c.rs:2429` — the `.proj` arm's continuation on the reduced
  scrutinee (`whnfCoreProjArmI` above, con-leche's inline arm). -/
  whnfCoreProj : ∀ (d : Std.U64) (sn : name.Name) (i : Std.U64) (e2 : expr.Expr),
      NameWF sn → ExprWF e2 →
    Sim absExpr ExprWF
      (fun st fe => cached.core_c.whnf_core_proj_i mode fuel st fe d n sn i e2)
      (fun lfe => whnfCoreProjArmI (absMode mode) (knot mode lfe fuel.val) lfe d.val
        (ConLeche.Cached.whnfCoreLoopI (absMode mode) (knot mode lfe fuel.val) lfe
          d.val n.val)
        (absName sn) i.val (absExpr e2))
  /-- `core_c.rs:1665` — the string-literal expansion of a projection's
  scrutinee (`CoreC.lean:684 projLitToCtorI`).  Budget-free: `projLitToCtorI`
  reaches the knot, not the loop. -/
  projLitToCtor : ∀ (d : Std.U64) (e : expr.Expr), ExprWF e →
    Sim absExpr ExprWF
      (fun st fe => cached.core_c.proj_lit_to_ctor_i mode fuel st fe d e)
      (fun lfe => ConLeche.Cached.projLitToCtorI (knot mode lfe fuel.val) lfe d.val
        (absExpr e))

/-! ## The step -/

/-- `ConLeche/Cached/CoreC.lean:950` — **`whnf_core_step_i` refines
`whnfCoreStepI`** at the continuation `whnfCoreLoopI … n` (`core_c.rs:2369`). -/
theorem whnf_core_step_i_refines {mode : env.CheckMode} {fuel : Std.U64}
    (hw : Wrappers mode fuel) (d n : Std.U64) (hd : WhnfCoreDeps mode fuel n)
    {e : expr.Expr} (he : ExprWF e) :
    Sim absExpr ExprWF
      (fun st fe => cached.core_c.whnf_core_step_i mode fuel st fe d n e)
      (fun lfe => ConLeche.Cached.whnfCoreStepI (absMode mode) (knot mode lfe fuel.val)
        lfe d.val
        (ConLeche.Cached.whnfCoreLoopI (absMode mode) (knot mode lfe fuel.val) lfe
          d.val n.val)
        (absExpr e)) := by
  intro fe lfe hfe hfrel st res st' hwf hok lst hrel
  cases he with
  | @bvar i e h1 =>
    -- `whnf beyond the supported fragment`: the Rust throws, nothing to show
    obtain ⟨dw, rfl, -, -, -⟩ := Expr.bvar_inv h1
    unfold cached.core_c.whnf_core_step_i at hok
    simp at hok
  | @let_e ty v bo e hty hv hbo h1 =>
    -- `whnfCore: `let` in an annotated expression`: likewise
    obtain ⟨dw, rfl, -, -, -⟩ := Expr.let_e_inv h1
    unfold cached.core_c.whnf_core_step_i at hok
    simp at hok
  | @fvar idx ty e hty h1 =>
    obtain ⟨dw, rfl, -, -, -⟩ := Expr.fvar_inv h1
    unfold cached.core_c.whnf_core_step_i at hok
    simp only [arc_deref_eq, bind_tc_ok, ExprOps.node_kind, State.expr_dup_eq,
      Result.ok.injEq, Prod.mk.injEq] at hok
    obtain ⟨heq, rfl⟩ := hok
    obtain rfl : res = _ := by simpa using heq.symm
    exact ⟨lst, by simp only [absExpr_mk, absExprKind, ConLeche.Cached.whnfCoreStepI]; rfl, hrel, hwf, ExprWF.fvar hty h1⟩
  | @sort u e hu h1 =>
    obtain ⟨dw, b, -, rfl, -, -, -⟩ := Expr.sort_inv h1
    unfold cached.core_c.whnf_core_step_i at hok
    simp only [arc_deref_eq, bind_tc_ok, ExprOps.node_kind, State.expr_dup_eq,
      Result.ok.injEq, Prod.mk.injEq] at hok
    obtain ⟨heq, rfl⟩ := hok
    obtain rfl : res = _ := by simpa using heq.symm
    exact ⟨lst, by simp only [absExpr_mk, absExprKind, ConLeche.Cached.whnfCoreStepI]; rfl, hrel, hwf, ExprWF.sort hu h1⟩
  | @mk_const nm us e hn hus h1 =>
    obtain ⟨dw, b, -, rfl, -, -, -⟩ := Expr.mk_const_inv h1
    unfold cached.core_c.whnf_core_step_i at hok
    simp only [arc_deref_eq, bind_tc_ok, ExprOps.node_kind, State.expr_dup_eq,
      Result.ok.injEq, Prod.mk.injEq] at hok
    obtain ⟨heq, rfl⟩ := hok
    obtain rfl : res = _ := by simpa using heq.symm
    exact ⟨lst, by simp only [absExpr_mk, absExprKind, ConLeche.Cached.whnfCoreStepI]; rfl, hrel, hwf, ExprWF.mk_const hn hus h1⟩
  | @lam ty bo m e hty hbo hm h1 =>
    obtain ⟨dw, rfl, -, -, -⟩ := Expr.lam_inv h1
    unfold cached.core_c.whnf_core_step_i at hok
    simp only [arc_deref_eq, bind_tc_ok, ExprOps.node_kind, State.expr_dup_eq,
      Result.ok.injEq, Prod.mk.injEq] at hok
    obtain ⟨heq, rfl⟩ := hok
    obtain rfl : res = _ := by simpa using heq.symm
    exact ⟨lst, by simp only [absExpr_mk, absExprKind, ConLeche.Cached.whnfCoreStepI]; rfl, hrel, hwf, ExprWF.lam hty hbo hm h1⟩
  | @forall_e ty bo m e hty hbo hm h1 =>
    obtain ⟨dw, rfl, -, -, -⟩ := Expr.forall_e_inv h1
    unfold cached.core_c.whnf_core_step_i at hok
    simp only [arc_deref_eq, bind_tc_ok, ExprOps.node_kind, State.expr_dup_eq,
      Result.ok.injEq, Prod.mk.injEq] at hok
    obtain ⟨heq, rfl⟩ := hok
    obtain rfl : res = _ := by simpa using heq.symm
    exact ⟨lst, by simp only [absExpr_mk, absExprKind, ConLeche.Cached.whnfCoreStepI]; rfl, hrel, hwf,
      ExprWF.forall_e hty hbo hm h1⟩
  | @lit l e hl h1 =>
    obtain ⟨dw, rfl, -, -, -⟩ := Expr.lit_inv h1
    unfold cached.core_c.whnf_core_step_i at hok
    simp only [arc_deref_eq, bind_tc_ok, ExprOps.node_kind, State.expr_dup_eq,
      Result.ok.injEq, Prod.mk.injEq] at hok
    obtain ⟨heq, rfl⟩ := hok
    obtain rfl : res = _ := by simpa using heq.symm
    exact ⟨lst, by simp only [absExpr_mk, absExprKind, ConLeche.Cached.whnfCoreStepI]; rfl, hrel, hwf, ExprWF.lit hl h1⟩
  | @app f a e hf ha h1 =>
    -- Bulk beta: the spine head through the knot, the whole spine to `whnf_app_i`.
    have he : ExprWF e := ExprWF.app hf ha h1
    obtain ⟨dw, rfl, -, -, -⟩ := Expr.app_inv h1
    unfold cached.core_c.whnf_core_step_i at hok
    simp only [arc_deref_eq, bind_tc_ok, ExprOps.node_kind] at hok
    obtain ⟨h', hh, hok⟩ := bind_eq_ok_iff.mp hok
    obtain ⟨args, hargs, hok⟩ := bind_eq_ok_iff.mp hok
    obtain ⟨⟨rc, st1⟩, hc, hok⟩ := bind_eq_ok_iff.mp hok
    obtain ⟨hhabs, hhwf⟩ := ExprOps.get_app_fn_refines he hh
    obtain ⟨haabs, hawf⟩ := ExprOps.get_app_args_refines he hargs
    cases rc with
    | Err err => simp at hok
    | Ok v =>
      obtain ⟨lst1, hrun1, hrel1, hwf1, hvwf⟩ :=
        (hw.whnfCoreSim d hhwf).apply hwf hfe hc hrel hfrel
      obtain ⟨lst2, hrun2, hrel2, hwf2, hrwf⟩ :=
        (hd.whnfApp d v args 0#usize hvwf hawf).apply hwf1 hfe hok hrel1 hfrel
      refine ⟨lst2, ?_, hrel2, hwf2, hrwf⟩
      simp only [absExpr_mk, absExprKind] at hhabs haabs
      rw [hhabs] at hrun1
      simp only [absExpr_mk, absExprKind, ConLeche.Cached.whnfCoreStepI, pure_bind,
        ConLeche.Cached.ExprC.getAppFn_spec, ConLeche.Cached.ExprC.getAppArgs_spec]
      rw [run_bind hrun1]
      simpa [haabs] using hrun2
  | @proj sn i pe e hsn hpe h1 =>
    obtain ⟨dw, rfl, -, -, -⟩ := Expr.proj_inv h1
    unfold cached.core_c.whnf_core_step_i at hok
    simp only [arc_deref_eq, bind_tc_ok, ExprOps.node_kind, name_dup_eq] at hok
    obtain ⟨⟨rw1, st1⟩, hw1, hok⟩ := bind_eq_ok_iff.mp hok
    cases rw1 with
    | Err err => simp at hok
    | Ok w =>
      obtain ⟨lst1, hrun1, hrel1, hwf1, hwwf⟩ :=
        (hw.whnfSim d hpe).apply hwf hfe hw1 hrel hfrel
      obtain ⟨⟨rl, st2⟩, hl, hok⟩ := bind_eq_ok_iff.mp hok
      cases rl with
      | Err err => simp at hok
      | Ok e2 =>
        obtain ⟨lst2, hrun2, hrel2, hwf2, he2wf⟩ :=
          (hd.projLitToCtor d w hwwf).apply hwf1 hfe hl hrel1 hfrel
        obtain ⟨lst3, hrun3, hrel3, hwf3, hrwf⟩ :=
          (hd.whnfCoreProj d sn i e2 hsn he2wf).apply hwf2 hfe hok hrel2 hfrel
        refine ⟨lst3, ?_, hrel3, hwf3, hrwf⟩
        simp only [absExpr_mk, absExprKind, whnfCoreStepI_proj]
        rw [run_bind hrun1, run_bind hrun2]
        exact hrun3

/-! ## The loop and the body -/

/-- `ConLeche/Cached/CoreC.lean:1000` — **`whnf_core_loop_i` refines
`whnfCoreLoopI`** (`core_c.rs:2483`). -/
theorem whnf_core_loop_i_refines {mode : env.CheckMode} {fuel : Std.U64}
    (hw : Wrappers mode fuel) (d n : Std.U64)
    (hd : ∀ m : Std.U64, m.val < n.val → WhnfCoreDeps mode fuel m)
    {e : expr.Expr} (he : ExprWF e) :
    Sim absExpr ExprWF
      (fun st fe => cached.core_c.whnf_core_loop_i mode fuel st fe d n e)
      (fun lfe => ConLeche.Cached.whnfCoreLoopI (absMode mode) (knot mode lfe fuel.val)
        lfe d.val n.val (absExpr e)) := by
  intro fe lfe hfe hfrel st res st' hwf hok lst hrel
  dsimp only at hok
  unfold cached.core_c.whnf_core_loop_i at hok
  by_cases hz : n = 0#u64
  · -- the budget is spent: the Rust answers `.Err`, so there is nothing to show
    rw [hz] at hok; simp [bind_eq_ok_iff] at hok
  · rw [if_neg hz] at hok
    obtain ⟨m, hm, hok⟩ := bind_eq_ok_iff.mp hok
    -- `n.val = m.val + 1`, so con-leche's loop is the step at the budget `m`.
    have hnz : n.val ≠ 0 := fun h => hz (Std.UScalar.eq_of_val_eq (by simp [h]))
    have hmv : n.val = m.val + 1 := by
      have h1 := ConRon.Refine.Nat.usub_val hm
      have h2 : ((1#u64 : Std.U64)).val = 1 := rfl
      omega
    simp only [hmv, whnfCoreLoopI_succ]
    exact (whnf_core_step_i_refines hw d m (hd m (by omega)) he).apply hwf hfe hok hrel hfrel

/-- `ConLeche/Cached/CoreC.lean:1008` — **`whnf_core_body_i` refines
`whnfCoreBodyI`** (`core_c.rs:2510`): the loop at `whnfCoreLoopFuel`. -/
theorem whnf_core_body_i_refines {mode : env.CheckMode} {fuel : Std.U64}
    (hw : Wrappers mode fuel) (hd : ∀ m : Std.U64, WhnfCoreDeps mode fuel m)
    (d : Std.U64) {e : expr.Expr} (he : ExprWF e) :
    Sim absExpr ExprWF
      (fun st fe => cached.core_c.whnf_core_body_i mode fuel st fe d e)
      (fun lfe => ConLeche.Cached.whnfCoreBodyI (absMode mode) (knot mode lfe fuel.val) lfe
        d.val (absExpr e)) := by
  intro fe lfe hfe hfrel st res st' hwf hok lst hrel
  unfold cached.core_c.whnf_core_body_i at hok
  obtain ⟨i, hi, hok⟩ := bind_eq_ok_iff.mp hok
  have hiv : i.val = ConLeche.whnfCoreLoopFuel := CoreK.whnf_core_loop_fuel_refines hi
  have := (whnf_core_loop_i_refines hw d i (fun m _ => hd m) he).apply hwf hfe hok hrel hfrel
  rw [hiv] at this
  simpa [ConLeche.Cached.whnfCoreBodyI] using this

end ConRon.Refine.Core
