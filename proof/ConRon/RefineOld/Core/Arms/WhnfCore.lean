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

The `.M`-suffixed code-point arrays are the messages of the three **mirrored**
throws this file owns (task #67's census: every `cached/core_c.rs` error site
is one-to-one with a `throw` in `Cached/CoreC.lean`).  Under the full-outcome
statement each one carries a real obligation — con-leche throws too, at the
same kind — and all three are discharged by `rfl` equations below:

* `whnf_core_step_i`'s `M_LET` (`core_c.rs:2432`) is `CoreC.lean:994`'s
  `throw (.internal "whnfCore: `let` in an annotated expression")`;
* its `M_BVAR` (`:2434`) is `:996`'s
  `throw (.notImplemented "whnf beyond the supported fragment")`;
* `whnf_core_loop_i`'s `M` (`:2515`) is `:1002`'s
  `throw (.internal "fuel exhausted: whnfCore loop")`, the `0` arm of the
  budget recursion.

Messages are never compared, so only the constructor matters.
-/
import ConRon.RefineOld.Core.Arms.Shape
import ConRon.RefineOld.ExprOpsC
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
    (k : ConLeche.Expr → ConLeche.Cached.CheckCM ConLeche.Expr)
    (sn : ConLeche.Name) (i : Nat) (e' : ConLeche.Expr) :
    ConLeche.Cached.CheckCM ConLeche.Expr :=
  match fe.findProj? sn i with
  | some entry =>
    match ConLeche.Expr.getAppFn e' with
    | .const c us => do
      let args ← pure (ConLeche.Expr.getAppArgsC e')
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
    (k : ConLeche.Expr → ConLeche.Cached.CheckCM ConLeche.Expr)
    (sn : ConLeche.Name) (i : Nat) (pe : ConLeche.Expr) :
    ConLeche.Cached.whnfCoreStepI mode r fe depth k (.proj sn i pe)
      = (do
          let e' ← r.whnf depth pe
          let e' ← ConLeche.Cached.projLitToCtorI r fe depth e'
          whnfCoreProjArmI mode r fe depth k sn i e') := rfl

/-! ## The two cited throws

`whnfCoreStepI`'s last two arms are `throw`s, and `whnf_core_step_i` mirrors
both (task #67).  Each is a `rfl` equation on the `run`: `throw` in
`CheckCM = StateT CState (Except CheckError)` discards the state. -/

/-- `ConLeche/Cached/CoreC.lean:996` — the `.bvar` arm, `core_c.rs:2434`'s
`M_BVAR`. -/
theorem whnfCoreStepI_bvar (mode : ConLeche.CheckMode) (r : ConLeche.Cached.CoreFnsI)
    (fe : ConLeche.FEnv) (depth : Nat)
    (k : ConLeche.Expr → ConLeche.Cached.CheckCM ConLeche.Expr)
    (i : Nat) (lst : ConLeche.Cached.CState) :
    (ConLeche.Cached.whnfCoreStepI mode r fe depth k (.bvar i)).run lst
      = .error (.notImplemented "whnf beyond the supported fragment") := rfl

/-- `ConLeche/Cached/CoreC.lean:994` — the `.letE` arm, `core_c.rs:2432`'s
`M_LET`. -/
theorem whnfCoreStepI_letE (mode : ConLeche.CheckMode) (r : ConLeche.Cached.CoreFnsI)
    (fe : ConLeche.FEnv) (depth : Nat)
    (k : ConLeche.Expr → ConLeche.Cached.CheckCM ConLeche.Expr)
    (ty v bo : ConLeche.Expr) (lst : ConLeche.Cached.CState) :
    (ConLeche.Cached.whnfCoreStepI mode r fe depth k (.letE ty v bo)).run lst
      = .error (.internal "whnfCore: `let` in an annotated expression") := rfl

end WhnfCore

open WhnfCore

/-- `CoreC.lean:1000-1004` — one unrolling of `whnfCoreLoopI`: the step at the
decremented budget, with the loop itself as the continuation `k`. -/
theorem whnfCoreLoopI_succ (mode : ConLeche.CheckMode) (r : ConLeche.Cached.CoreFnsI)
    (fe : ConLeche.FEnv) (depth m : Nat) (e : ConLeche.Expr) :
    ConLeche.Cached.whnfCoreLoopI mode r fe depth (m + 1) e
      = ConLeche.Cached.whnfCoreStepI mode r fe depth
          (ConLeche.Cached.whnfCoreLoopI mode r fe depth m) e := by
  rw [ConLeche.Cached.whnfCoreLoopI]

/-- `CoreC.lean:1002` — the spent budget: `whnfCoreLoopI` at `0` throws
`internal "fuel exhausted: whnfCore loop"`, which `core_c.rs:2515`'s `M`
mirrors (task #67). -/
theorem whnfCoreLoopI_zero (mode : ConLeche.CheckMode) (r : ConLeche.Cached.CoreFnsI)
    (fe : ConLeche.FEnv) (depth : Nat) (e : ConLeche.Expr)
    (lst : ConLeche.Cached.CState) :
    (ConLeche.Cached.whnfCoreLoopI mode r fe depth 0 e).run lst
      = .error (.internal "fuel exhausted: whnfCore loop") := rfl

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
`whnfCoreStepI`** at the continuation `whnfCoreLoopI … n` (`core_c.rs:2369`),
**at every outcome** (task #67).  The two halves are split by `Sim.mk''`: the
accept half is §3.5's proof unchanged, and the failure half is the six
identity arms (where `.Err` is absurd), the two cited throws (`rfl` against
`whnfCoreStepI_bvar`/`_letE`) and the two delegating arms, where a callee's
error is this step's error and `ErrSim.bindCM` carries it through the rest of
con-leche's `do` block. -/
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
  refine Sim.mk'' ?_ ?_
  -- **The accept half**: §3.5's statement, the proof unchanged.
  · intro fe lfe hfe hfrel st res st' hwf hok lst hrel
    cases he with
    | @bvar i e h1 =>
      -- `whnf beyond the supported fragment`: the Rust throws, so `.Ok` is absurd
      obtain ⟨dw, rfl, -, -, -⟩ := Expr.bvar_inv h1
      unfold cached.core_c.whnf_core_step_i at hok
      simp [ron.node.ExprView.ofKind] at hok
    | @let_e ty v bo e hty hv hbo h1 =>
      -- `whnfCore: `let` in an annotated expression`: likewise
      obtain ⟨dw, rfl, -, -, -⟩ := Expr.let_e_inv h1
      unfold cached.core_c.whnf_core_step_i at hok
      simp [ron.node.ExprView.ofKind] at hok
    | @fvar idx ty e hty h1 =>
      obtain ⟨dw, rfl, -, -, -⟩ := Expr.fvar_inv h1
      unfold cached.core_c.whnf_core_step_i at hok
      simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, ExprOps.node_kind, ron.node.ExprView.ofKind, State.expr_dup_eq,
        Result.ok.injEq, Prod.mk.injEq] at hok
      obtain ⟨heq, rfl⟩ := hok
      obtain rfl : res = _ := by simpa using heq.symm
      exact ⟨lst, by simp only [absExpr_mk, absExprKind, ConLeche.Cached.whnfCoreStepI]; rfl, hrel, hwf, ExprWF.fvar hty h1⟩
    | @sort u e hu h1 =>
      obtain ⟨dw, b, -, rfl, -, -, -⟩ := Expr.sort_inv h1
      unfold cached.core_c.whnf_core_step_i at hok
      simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, ExprOps.node_kind, ron.node.ExprView.ofKind, State.expr_dup_eq,
        Result.ok.injEq, Prod.mk.injEq] at hok
      obtain ⟨heq, rfl⟩ := hok
      obtain rfl : res = _ := by simpa using heq.symm
      exact ⟨lst, by simp only [absExpr_mk, absExprKind, ConLeche.Cached.whnfCoreStepI]; rfl, hrel, hwf, ExprWF.sort hu h1⟩
    | @mk_const nm us e hn hus h1 =>
      obtain ⟨dw, b, -, rfl, -, -, -⟩ := Expr.mk_const_inv h1
      unfold cached.core_c.whnf_core_step_i at hok
      simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, ExprOps.node_kind, ron.node.ExprView.ofKind, State.expr_dup_eq,
        Result.ok.injEq, Prod.mk.injEq] at hok
      obtain ⟨heq, rfl⟩ := hok
      obtain rfl : res = _ := by simpa using heq.symm
      exact ⟨lst, by simp only [absExpr_mk, absExprKind, ConLeche.Cached.whnfCoreStepI]; rfl, hrel, hwf, ExprWF.mk_const hn hus h1⟩
    | @lam ty bo m e hty hbo hm h1 =>
      obtain ⟨dw, rfl, -, -, -⟩ := Expr.lam_inv h1
      unfold cached.core_c.whnf_core_step_i at hok
      simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, ExprOps.node_kind, ron.node.ExprView.ofKind, State.expr_dup_eq,
        Result.ok.injEq, Prod.mk.injEq] at hok
      obtain ⟨heq, rfl⟩ := hok
      obtain rfl : res = _ := by simpa using heq.symm
      exact ⟨lst, by simp only [absExpr_mk, absExprKind, ConLeche.Cached.whnfCoreStepI]; rfl, hrel, hwf, ExprWF.lam hty hbo hm h1⟩
    | @forall_e ty bo m e hty hbo hm h1 =>
      obtain ⟨dw, rfl, -, -, -⟩ := Expr.forall_e_inv h1
      unfold cached.core_c.whnf_core_step_i at hok
      simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, ExprOps.node_kind, ron.node.ExprView.ofKind, State.expr_dup_eq,
        Result.ok.injEq, Prod.mk.injEq] at hok
      obtain ⟨heq, rfl⟩ := hok
      obtain rfl : res = _ := by simpa using heq.symm
      exact ⟨lst, by simp only [absExpr_mk, absExprKind, ConLeche.Cached.whnfCoreStepI]; rfl, hrel, hwf,
        ExprWF.forall_e hty hbo hm h1⟩
    | @lit l e hl h1 =>
      obtain ⟨dw, rfl, -, -, -⟩ := Expr.lit_inv h1
      unfold cached.core_c.whnf_core_step_i at hok
      simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, ExprOps.node_kind, ron.node.ExprView.ofKind, State.expr_dup_eq,
        Result.ok.injEq, Prod.mk.injEq] at hok
      obtain ⟨heq, rfl⟩ := hok
      obtain rfl : res = _ := by simpa using heq.symm
      exact ⟨lst, by simp only [absExpr_mk, absExprKind, ConLeche.Cached.whnfCoreStepI]; rfl, hrel, hwf, ExprWF.lit hl h1⟩
    | @app f a e hf ha h1 =>
      -- Bulk beta: the spine head through the knot, the whole spine to `whnf_app_i`.
      have he : ExprWF e := ExprWF.app hf ha h1
      obtain ⟨dw, rfl, -, -, -⟩ := Expr.app_inv h1
      unfold cached.core_c.whnf_core_step_i at hok
      simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, ExprOps.node_kind, ron.node.ExprView.ofKind] at hok
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
        simp only [absExpr_mk, absExprKind, ConLeche.Cached.whnfCoreStepI, pure_bind, ConLeche.Expr.getAppArgsC_spec]
        rw [run_bind hrun1]
        simpa [haabs] using hrun2
    | @proj sn i pe e hsn hpe h1 =>
      obtain ⟨dw, rfl, -, -, -⟩ := Expr.proj_inv h1
      unfold cached.core_c.whnf_core_step_i at hok
      simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, ExprOps.node_kind, ron.node.ExprView.ofKind, name_dup_eq] at hok
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
  -- **The failure half** (task #67): the two cited throws, and the two
  -- delegating arms, where a callee's error is this step's error.
  · intro fe lfe hfe hfrel st ce st' hwf hok lst hrel
    cases he with
    | @bvar i e h1 =>
      -- `core_c.rs:2434` mirrors `CoreC.lean:996`'s `notImplemented` throw.
      obtain ⟨dw, rfl, -, -, -⟩ := Expr.bvar_inv h1
      unfold cached.core_c.whnf_core_step_i at hok
      simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, ExprOps.node_kind, ron.node.ExprView.ofKind, bind_eq_ok_iff,
        Result.ok.injEq, Prod.mk.injEq, core.result.Result.Err.injEq] at hok
      obtain ⟨s, -, v, -, c1, hc1, rfl, -⟩ := hok
      rw [core_types.not_implemented] at hc1
      obtain rfl : c1 = .NotImplemented v := (Result.ok_injective hc1).symm
      simp only [absExpr_mk, absExprKind]
      exact ErrSim.notImplemented (whnfCoreStepI_bvar _ _ _ _ _ _ lst)
    | @let_e ty v bo e hty hv hbo h1 =>
      -- `core_c.rs:2432` mirrors `CoreC.lean:994`'s `internal` throw.
      obtain ⟨dw, rfl, -, -, -⟩ := Expr.let_e_inv h1
      unfold cached.core_c.whnf_core_step_i at hok
      simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, ExprOps.node_kind, ron.node.ExprView.ofKind, bind_eq_ok_iff,
        Result.ok.injEq, Prod.mk.injEq, core.result.Result.Err.injEq] at hok
      obtain ⟨s, -, v, -, c1, hc1, rfl, -⟩ := hok
      rw [core_types.internal] at hc1
      obtain rfl : c1 = .Internal v := (Result.ok_injective hc1).symm
      simp only [absExpr_mk, absExprKind]
      exact ErrSim.internal (whnfCoreStepI_letE _ _ _ _ _ _ _ _ lst)
    | @fvar idx ty e hty h1 =>
      obtain ⟨dw, rfl, -, -, -⟩ := Expr.fvar_inv h1
      unfold cached.core_c.whnf_core_step_i at hok
      simp [ron.node.ExprView.ofKind] at hok
    | @sort u e hu h1 =>
      obtain ⟨dw, b, -, rfl, -, -, -⟩ := Expr.sort_inv h1
      unfold cached.core_c.whnf_core_step_i at hok
      simp [ron.node.ExprView.ofKind] at hok
    | @mk_const nm us e hn hus h1 =>
      obtain ⟨dw, b, -, rfl, -, -, -⟩ := Expr.mk_const_inv h1
      unfold cached.core_c.whnf_core_step_i at hok
      simp [ron.node.ExprView.ofKind] at hok
    | @lam ty bo m e hty hbo hm h1 =>
      obtain ⟨dw, rfl, -, -, -⟩ := Expr.lam_inv h1
      unfold cached.core_c.whnf_core_step_i at hok
      simp [ron.node.ExprView.ofKind] at hok
    | @forall_e ty bo m e hty hbo hm h1 =>
      obtain ⟨dw, rfl, -, -, -⟩ := Expr.forall_e_inv h1
      unfold cached.core_c.whnf_core_step_i at hok
      simp [ron.node.ExprView.ofKind] at hok
    | @lit l e hl h1 =>
      obtain ⟨dw, rfl, -, -, -⟩ := Expr.lit_inv h1
      unfold cached.core_c.whnf_core_step_i at hok
      simp [ron.node.ExprView.ofKind] at hok
    | @app f a e hf ha h1 =>
      -- either the spine head's `whnf_core` threw, or `whnf_app_i` did.
      have he : ExprWF e := ExprWF.app hf ha h1
      obtain ⟨dw, rfl, -, -, -⟩ := Expr.app_inv h1
      unfold cached.core_c.whnf_core_step_i at hok
      simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, ExprOps.node_kind, ron.node.ExprView.ofKind] at hok
      obtain ⟨h', hh, hok⟩ := bind_eq_ok_iff.mp hok
      obtain ⟨args, hargs, hok⟩ := bind_eq_ok_iff.mp hok
      obtain ⟨⟨rc, st1⟩, hc, hok⟩ := bind_eq_ok_iff.mp hok
      obtain ⟨hhabs, hhwf⟩ := ExprOps.get_app_fn_refines he hh
      obtain ⟨haabs, hawf⟩ := ExprOps.get_app_args_refines he hargs
      simp only [absExpr_mk, absExprKind] at hhabs haabs
      simp only [absExpr_mk, absExprKind, ConLeche.Cached.whnfCoreStepI, pure_bind, ConLeche.Expr.getAppArgsC_spec]
      cases rc with
      | Err err =>
        simp at hok
        obtain ⟨rfl, -⟩ := hok
        have herr := (hw.whnfCoreSim d hhwf).apply_err hwf hfe hc hrel hfrel
        rw [hhabs] at herr
        exact ErrSim.bindCM herr
      | Ok v =>
        obtain ⟨lst1, hrun1, hrel1, hwf1, hvwf⟩ :=
          (hw.whnfCoreSim d hhwf).apply hwf hfe hc hrel hfrel
        have herr := (hd.whnfApp d v args 0#usize hvwf hawf).apply_err hwf1 hfe hok hrel1 hfrel
        rw [hhabs] at hrun1
        rw [run_bind hrun1]
        simpa [haabs] using herr
    | @proj sn i pe e hsn hpe h1 =>
      -- `whnf`, then `proj_lit_to_ctor_i`, then the `.proj` continuation.
      obtain ⟨dw, rfl, -, -, -⟩ := Expr.proj_inv h1
      unfold cached.core_c.whnf_core_step_i at hok
      simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, ExprOps.node_kind, ron.node.ExprView.ofKind, name_dup_eq] at hok
      obtain ⟨⟨rw1, st1⟩, hw1, hok⟩ := bind_eq_ok_iff.mp hok
      simp only [absExpr_mk, absExprKind, whnfCoreStepI_proj]
      cases rw1 with
      | Err err =>
        simp at hok
        obtain ⟨rfl, -⟩ := hok
        exact ErrSim.bindCM ((hw.whnfSim d hpe).apply_err hwf hfe hw1 hrel hfrel)
      | Ok w =>
        obtain ⟨lst1, hrun1, hrel1, hwf1, hwwf⟩ :=
          (hw.whnfSim d hpe).apply hwf hfe hw1 hrel hfrel
        obtain ⟨⟨rl, st2⟩, hl, hok⟩ := bind_eq_ok_iff.mp hok
        rw [run_bind hrun1]
        cases rl with
        | Err err =>
          simp at hok
          obtain ⟨rfl, -⟩ := hok
          exact ErrSim.bindCM ((hd.projLitToCtor d w hwwf).apply_err hwf1 hfe hl hrel1 hfrel)
        | Ok e2 =>
          obtain ⟨lst2, hrun2, hrel2, hwf2, he2wf⟩ :=
            (hd.projLitToCtor d w hwwf).apply hwf1 hfe hl hrel1 hfrel
          rw [run_bind hrun2]
          exact (hd.whnfCoreProj d sn i e2 hsn he2wf).apply_err hwf2 hfe hok hrel2 hfrel

/-! ## The loop and the body -/

/-- `ConLeche/Cached/CoreC.lean:1000` — **`whnf_core_loop_i` refines
`whnfCoreLoopI`** (`core_c.rs:2483`), at every outcome.  Only the spent budget
needs a case of its own: **fuel exhaustion is mirrored** (`whnfCoreLoopI_zero`),
where §3.5's accept-direction proof had nothing to show.  Above zero the step's
own statement already covers both halves, so one application does it. -/
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
  · -- The budget is spent, and **both sides throw**: `core_c.rs:2515`'s
    -- `internal "fuel exhausted: whnfCore loop"` is `CoreC.lean:1002`'s
    -- (task #67).  The `.Ok` outcome is absurd, so the case is the throw.
    subst hz
    rw [if_pos rfl] at hok
    simp only [bind_eq_ok_iff, Result.ok.injEq, Prod.mk.injEq] at hok
    obtain ⟨s, -, v, -, c1, hc1, rfl, -⟩ := hok
    rw [core_types.internal] at hc1
    obtain rfl : c1 = .Internal v := (Result.ok_injective hc1).symm
    exact ErrSim.internal (whnfCoreLoopI_zero _ _ _ _ _ lst)
  · rw [if_neg hz] at hok
    obtain ⟨m, hm, hok⟩ := bind_eq_ok_iff.mp hok
    -- `n.val = m.val + 1`, so con-leche's loop is the step at the budget `m`.
    have hnz : n.val ≠ 0 := fun h => hz (Std.UScalar.eq_of_val_eq (by simp [h]))
    have hmv : n.val = m.val + 1 := by
      have h1 := ConRon.Refine.Nat.usub_val hm
      have h2 : ((1#u64 : Std.U64)).val = 1 := rfl
      omega
    simp only [hmv, whnfCoreLoopI_succ]
    -- The step's statement is the full outcome, so one application covers both
    -- halves: whatever the step answers, the loop answers.
    exact whnf_core_step_i_refines hw d m (hd m (by omega)) he
      fe lfe hfe hfrel st res st' hwf hok lst hrel

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
  have := whnf_core_loop_i_refines hw d i (fun m _ => hd m) he
    fe lfe hfe hfrel st res st' hwf hok lst hrel
  rw [hiv] at this
  exact this

end ConRon.Refine.Core
