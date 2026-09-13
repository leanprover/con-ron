/-
# The knot's app arm (task #55): bulk beta, the peel loop and the structural
projection rule

`crates/con-ron-core/src/cached/core_c.rs`'s spine machinery, against
`ConLeche/Cached/CoreC.lean`:

| Rust | con-leche |
|---|---|
| `pi_residual_m` (`:483`) | `piResidualM` (`Cached/StateC.lean:219-221`) |
| `fab_scope_ok_i` (`:1266`) | the cached scope guard of `majorToCtorI` |
| `proj_cert_i` (`:2152`) | `projCertI` (`CoreC.lean:841`) |
| `proj_cert_at_i` (`:2179`) | `projCertAtI` (`CoreC.lean:851`) |
| `whnf_core_proj_i` (`:2429`) | the `.proj` continuation of `whnfCoreStepI` |
| `whnf_app_i` (`:2218`) | `whnfAppI` (`CoreC.lean:867`) |
| `beta_peel_i` (`:2296`) | `betaPeelI` (`CoreC.lean:907`) |

Three things are worth saying before the proofs.

**The continuation is a parameter.**  con-leche abstracts the
head-normalization loop's continuation as `k : Expr → CheckCM Expr`; the
Rust defunctionalizes it into the loop's step budget `n` and a call to
`whnf_core_loop_i … n` (task #18's pattern 2).  The two big lemmas below are
therefore proved with `k` *abstract*, under one hypothesis — `KSim`, a `Sim`
between `whnf_core_loop_i … n` and `k` — and the canonical corollaries take
that hypothesis at `k := whnfCoreLoopI … n`.  The general form is what
`Arms/WhnfCore.lean` wants at its call site, since `whnfCoreStepI` passes
exactly that `k`.

**The two big lemmas are one induction.**  `whnfAppI`/`betaPeelI` are one
con-leche `mutual` block at `termination_by _ args => (args.length, 0)` /
`(args.length, 1)`, so `whnf_app_beta_peel_aux` proves both by one strong
induction on the *remaining* argument count, `whnfApp` before `betaPeel` at
each count: `whnfAppI` at `L` calls `betaPeelI`/`whnfAppI` at `L - 1`, and
`betaPeelI` at `L` calls `whnfAppI` at `L`.  `whnf_app_i_refines` and
`beta_peel_i_refines` are its two corollaries.

**No `sorry`.**  `beta_peel_i` ends each peeled group with
`state_c::inst_list_m`, whose refinement needs the `instC` entry-count clause;
task #55 could not derive it from `StateRel` (a lookup agreement does not bound
the Lean map's size) and left `App.instCSize_of_rel` a `sorry`.  Task #61
folded the clause into `Refine/State.lean`'s `StateRel` (`StateRel.instCSize`,
with `State.insert_size_step` as its insert lemma), so `instCSize_of_rel` is a
projection and this file is closed.

**The continuation is a hypothesis, not a `Deps` field.**  `whnf_core_loop_i`,
`whnf_core_step_i`, `whnf_app_i` and `beta_peel_i` are **one** strongly
connected component of the Rust block — loop(n) → step(n−1) → whnfApp(n−1) →
loop(n−1) — and task #55's partition put it in two files with `∀`-quantified
`Deps` fields, so neither `AppDeps` nor `WhnfCoreDeps` could be built without
the other.  Task #61's repair: `AppDeps` keeps only the acyclic callees
(`Arms/Iota.lean`, `Arms/Certs.lean`), the continuation travels as the explicit
`KSim mode fuel d n k` hypothesis the `*_of_loop` lemmas already took, and
`Arms/Arms.lean` runs the one induction on the budget that ties the component
together.

**The remaining arguments are a suffix.**  The Rust walks `args : Vec Expr`
by an index `i`; con-leche recurses on a `List`.  The correspondence is
`(absExprs args).drop i.val`, peeled one element at a time by
`ExprOps.vec_index_expr`.

**The full outcome (task #67, DESIGN.md §3's ruling of 2026-09-13).**  Every
lemma here is stated over the Rust computation's whole outcome (`Sim`, through
`Refine/State.lean`'s `Out`): exact result on success, *and* con-leche's own
throw at the same kind on a failure.  None of this file's five Rust functions
throws on its own — `proj_cert_i`, `proj_cert_at_i`, `whnf_core_proj_i`,
`whnf_app_i` and `beta_peel_i` have no `Err(core_types::…)` arm between them —
so every error half is move 1 of the README's three: the callee's
`Sim.apply_err` carried through the rest of con-leche's `do` block by
`ErrSim.bindCM`, one line per bind.  The six callees that can throw are
`state_c::const_ty_at_m`, `iota_certs_i`, `proj_cert_at_i` itself, `infer_io`,
`defeq` and the continuation `k`; `inst_list_m`, `fab_scope_ok_i` and
`pi_residual_m` cannot, and the five stuck-`proj` arms rebuild a node
(`App.proj_stuck` now reads the outcome off the arm rather than assuming it).
-/
import ConRon.Refine.Core.Arms.Shape
import ConRon.Refine.CoreKVec
import ConRon.Refine.CoreKShapes
import ConRon.Refine.CoreKSupport
import ConRon.Refine.CoreKGuards
import ConRon.Refine.ExprOpsSpine
import ConRon.Refine.ExprOpsC
import ConRon.Refine.ExprOpsCGuards
import ConRon.Refine.Core.Arms.Bridge

open Aeneas Aeneas.Std Result
open ConRon.Generated ConRon.Generated.kernel ConRon.Generated.cached
open ConRon.Refine ConRon.Refine.State ConRon.Refine.FEnv

namespace ConRon.Refine.Core

/-! ## The foreign helpers

Four callees of this file live in another arm file (`Arms/Iota.lean`,
`Arms/Certs.lean`).  Each is a field here, at the exact statement its own
`<fn>_refines` has; the coordinator discharges the structure in
`Arms/Arms.lean`.  The fifth, `Arms/WhnfCore.lean`'s `whnf_core_loop_i`, is
**not** a field: it is the other half of this file's strongly connected
component, and travels as the `KSim` hypothesis below (task #61). -/

/-- The arms this file calls but does not own. -/
structure AppDeps (mode : env.CheckMode) (fuel : Std.U64) : Prop where
  /-- `Arms/Iota.lean` — `iota_arity_ok` (`core_c.rs:1043`) refines
  `iotaArityOk` (`CoreC.lean:734-742`): state-free and environment-only. -/
  iotaArityOk : ∀ (fe : fenv.FEnv) (lfe : ConLeche.FEnv) (e : expr.Expr)
    (b : Bool), FEnvWF fe → FEnvRel fe lfe → ExprWF e →
    cached.core_c.iota_arity_ok fe e = ok b →
    b = ConLeche.Cached.iotaArityOk lfe (absExpr e)
  /-- `Arms/Iota.lean` — `iota_rec_i` (`core_c.rs:1793`) refines `iotaRecI`
  (`CoreC.lean:744`). -/
  iotaRec : ∀ (d : Std.U64) (e : expr.Expr), ExprWF e →
    Sim (Option.map absExpr) (fun o => ∀ x ∈ o, ExprWF x)
      (fun st fe => cached.core_c.iota_rec_i mode fuel st fe d e)
      (fun lfe => ConLeche.Cached.iotaRecI (absMode mode)
        (knot mode lfe fuel.val) lfe d.val (absExpr e))
  /-- `Arms/Iota.lean` — `is_ctor_stored_i` (`core_c.rs:1266`) refines the
  cited `some (.ctorInfo _ _ _)` test of `projCertI` (`CoreC.lean:843`). -/
  isCtorStored : ∀ (fe : fenv.FEnv) (lfe : ConLeche.FEnv) (c : name.Name)
    (b : Bool), FEnvWF fe → FEnvRel fe lfe → NameWF c →
    cached.core_c.is_ctor_stored_i fe c = ok b →
    b = (match lfe.find? (absName c) with
         | some (.ctorInfo _ _ _) => true
         | _ => false)
  /-- `Arms/Certs.lean` — `iota_certs_i` (`core_c.rs:1368`) refines
  `iotaCertsI` (`CoreC.lean:197-205`). -/
  iotaCerts : ∀ (d : Std.U64) (lic : Bool) (ty : expr.Expr)
    (args : alloc.vec.Vec expr.Expr), ExprWF ty → ExprsWF args →
    Sim id (fun _ => True)
      (fun st fe => cached.core_c.iota_certs_i mode fuel st fe d lic ty args)
      (fun lfe => ConLeche.Cached.iotaCertsI (knot mode lfe fuel.val) lfe d.val
        lic (absExpr ty) (absExprs args))

/-! ## One `CheckCM` bind, run

`Refine/StateC.lean`'s note applies: `simp` will not push a state argument
through a `match`, so the arms are composed one bind at a time.  The two
lemmas live in a private namespace so that the sibling arm files may carry
their own copy without a clash. -/

namespace App

/-- `(x >>= f).run lst` at a known `x.run lst`. -/
theorem run_bind {α β : Type} {x : ConLeche.Cached.CheckCM α}
    {f : α → ConLeche.Cached.CheckCM β} {lst lst' : ConLeche.Cached.CState} {a : α}
    (h : x.run lst = .ok (a, lst')) :
    (x >>= f).run lst = (f a).run lst' := by
  simp only [StateT.run, Bind.bind, StateT.bind] at h ⊢
  rw [h]
  rfl

/-- `pure`'s `run`. -/
@[simp] theorem run_pure {α : Type} (a : α) (lst : ConLeche.Cached.CState) :
    (pure a : ConLeche.Cached.CheckCM α).run lst = .ok (a, lst) := rfl

/-- **A `Sim` in tail position** (task #67): where the Rust arm *is* a call,
the callee's whole outcome is the caller's, so neither `Sim.apply` nor
`Sim.apply_err` alone applies — this is `Sim` unfolded at the undivided
outcome, in the argument order `Sim.apply` has. -/
theorem sim_tail {α β : Type} {A : α → β} {WF : α → Prop} {f g}
    (h : Sim A WF f g) {st fe o st' lst lfe} (hwf : StateWF st) (hfe : FEnvWF fe)
    (hok : f st fe = Aeneas.Std.Result.ok (o, st')) (hrel : StateRel st lst)
    (hfrel : FEnvRel fe lfe) : Out A WF o st' ((g lfe).run lst) :=
  h fe lfe hfe hfrel st o st' hwf hok lst hrel

end App

/-! ## `pi_residual_m` — the tenth `*M` wrapper (`core_c.rs:483`)

`ConLeche/Cached/StateC.lean:219-221`: `piResidualM` is `pure (Expr.piResidual
e args)`, so the wrapper is state-free and the refinement is the pure shape
against the value the `pure` carries. -/

/-- `piResidualM`'s `run`: the `pure` of `Expr.piResidual`. -/
@[simp] theorem piResidualM_run {lst : ConLeche.Cached.CState}
    (e : ConLeche.Expr) (args : List ConLeche.Expr) :
    (ConLeche.Cached.piResidualM e args).run lst
      = .ok (ConLeche.Expr.piResidual e args, lst) := rfl

/-- `ConLeche/Cached/StateC.lean:219-221` — **`pi_residual_m` refines
`piResidualM`**: `pure (Expr.piResidual e args)`, the bulk form of the
`∀`-telescope residual (`core_c.rs:483`). -/
theorem pi_residual_m_refines {e : expr.Expr} {args : alloc.vec.Vec expr.Expr}
    (he : ExprWF e) (hargs : ExprsWF args) :
    SimP (Option.map absExpr) (fun o => ∀ x ∈ o, ExprWF x)
      (cached.core_c.pi_residual_m e args)
      (ConLeche.Expr.piResidual (absExpr e) (absExprs args)) := by
  intro o h
  rw [cached.core_c.pi_residual_m] at h
  exact ExprOpsC.pi_residual_refines he hargs (by simpa using h)

/-! ## `fab_scope_ok_i` — the cached scope guard (`core_c.rs:1266`)

`ConLeche/Cached/CoreC.lean:543-670 majorToCtorI` runs the cited
`Expr.wscopedBC depth fab && Expr.looseBVarsBounded 0 fab &&
Expr.leafGuard fab major` on every rescue fabrication; the port lifts it into
its own function (task #32's memo policy note) and short-circuits it exactly
as `&&` does. -/

/-- `ConLeche/Cached/CoreC.lean:543-670` — **`fab_scope_ok_i` refines the
cached tier's scope guard** of `majorToCtorI`'s three rescue branches:
`wscopedB depth fab && looseBVarsBounded 0 fab && leafGuard fab major`
(`core_c.rs:1266`). -/
theorem fab_scope_ok_i_refines {fab major : expr.Expr} {depth : Std.U64}
    (hfab : ExprWF fab) (hmajor : ExprWF major) :
    SimP id (fun _ => True) (cached.core_c.fab_scope_ok_i fab major depth)
      (ConLeche.Expr.wscopedBC depth.val (absExpr fab) &&
        ((absExpr fab).looseBVarsBounded 0 &&
          ConLeche.Expr.leafGuard (absExpr fab) (absExpr major))) := by
  intro b h
  refine ⟨?_, trivial⟩
  rw [cached.core_c.fab_scope_ok_i] at h
  obtain ⟨b0, hb0, h⟩ := bind_eq_ok_iff.mp h
  rw [← ExprOpsC.wscoped_b_refines hfab hb0]
  cases b0 with
  | false =>
    simp only [Bool.false_eq_true, if_false, Result.ok.injEq] at h
    subst h; simp
  | true =>
    simp only [if_true] at h
    obtain ⟨b1, hb1, h⟩ := bind_eq_ok_iff.mp h
    have h2 : b1 = (absExpr fab).looseBVarsBounded 0 := by
      simpa using ExprOps.loose_bvars_bounded_refines hfab hb1
    rw [← h2]
    cases b1 with
    | false =>
      simp only [Bool.false_eq_true, if_false, Result.ok.injEq] at h
      subst h; simp
    | true =>
      simp only [if_true] at h
      rw [← ExprOpsC.leaf_guard_refines hfab hmajor h]
      simp

/-! ## The structural projection's certificate (`core_c.rs:2152`, `:2179`)

`ConLeche/Cached/CoreC.lean:841-853`: `projCertI` certifies the constructor
spine of a firing `proj` redex against the constructor's *stored* type (read
through `constTyAtM` at the redex's own levels), and `projCertAtI` is that
under the mode's `verifiedChecks` gate. -/

section
variable {mode : env.CheckMode} {fuel : Std.U64}

/-- `ConLeche/Cached/CoreC.lean:841-848` — **`proj_cert_i` refines
`projCertI`** (`core_c.rs:2152`): the stored-constructor test, the
level-instantiated constructor type, and the spine certificate. -/
theorem proj_cert_i_refines (hd : AppDeps mode fuel) (d : Std.U64) (lic : Bool)
    {c : name.Name} {us : alloc.vec.Vec level.Level}
    {args : alloc.vec.Vec expr.Expr} (hc : NameWF c) (hus : LevelsWF us)
    (hargs : ExprsWF args) :
    Sim id (fun _ => True)
      (fun st fe => cached.core_c.proj_cert_i mode fuel st fe d lic c us args)
      (fun lfe => ConLeche.Cached.projCertI (knot mode lfe fuel.val) lfe d.val lic
        (absName c) (absLevels us) (absExprs args)) := by
  intro fe lfe hfe hfrel st o st' hwf hok lst hrel
  unfold cached.core_c.proj_cert_i at hok
  obtain ⟨b, hb, hok⟩ := bind_eq_ok_iff.mp hok
  have hbv := hd.isCtorStored fe lfe c b hfe hfrel hc hb
  simp only [ConLeche.Cached.projCertI, pure_bind]
  -- the two sides branch on the same `fe.find? c`
  cases hfind : lfe.find? (absName c) with
  | none =>
    rw [hfind] at hbv
    simp only at hbv
    subst hbv
    simp only [Bool.false_eq_true, if_false, Result.ok.injEq, Prod.mk.injEq] at hok
    obtain ⟨rfl, rfl⟩ := hok
    exact ⟨lst, rfl, hrel, hwf, trivial⟩
  | some ci =>
    cases ci with
    | ctorInfo cv np nf =>
      rw [hfind] at hbv
      simp only at hbv
      subst hbv
      simp only [if_true] at hok
      obtain ⟨⟨rc, st1⟩, hcty, hok⟩ := bind_eq_ok_iff.mp hok
      cases rc with
      | Err err =>
        -- `constTyAtM` threw: con-leche's `do` block throws the same (move 1)
        simp at hok
        obtain ⟨rfl, rfl⟩ := hok
        exact ErrSim.bindCM
          (StateC.const_ty_at_m_err hwf hfe hc hus hcty lst lfe hrel hfrel (absName c))
      | Ok cty =>
        obtain ⟨lst1, hrun1, hrel1, hwf1, hctyWF⟩ :=
          StateC.const_ty_at_m_refines StateC.instLevelParamsRefines hwf hfe hc hus
            hcty lst lfe hrel hfrel (absName c)
        rw [App.run_bind hrun1]
        exact (hd.iotaCerts d lic cty args hctyWF hargs) fe lfe hfe hfrel st1 o st'
          hwf1 hok lst1 hrel1
    | axiomInfo cv | defnInfo cv v h | thmInfo cv v | indInfo cv caps
    | recInfo cv mi rp rules | projInfo tbl =>
      all_goals (
        rw [hfind] at hbv
        simp only at hbv
        subst hbv
        simp only [Bool.false_eq_true, if_false, Result.ok.injEq, Prod.mk.injEq] at hok
        obtain ⟨rfl, rfl⟩ := hok
        exact ⟨lst, rfl, hrel, hwf, trivial⟩)

/-- `ConLeche/Cached/CoreC.lean:850-853` — **`proj_cert_at_i` refines
`projCertAtI`** (`core_c.rs:2179`): the certificate at the verified mode, and
an unconditional `true` at the trusted one (the official kernel's
`reduce_proj`). -/
theorem proj_cert_at_i_refines (hd : AppDeps mode fuel) (d : Std.U64)
    (verified lic : Bool) {c : name.Name} {us : alloc.vec.Vec level.Level}
    {args : alloc.vec.Vec expr.Expr} (hc : NameWF c) (hus : LevelsWF us)
    (hargs : ExprsWF args) :
    Sim id (fun _ => True)
      (fun st fe =>
        cached.core_c.proj_cert_at_i mode fuel st fe d verified lic c us args)
      (fun lfe => ConLeche.Cached.projCertAtI (knot mode lfe fuel.val) lfe d.val
        verified lic (absName c) (absLevels us) (absExprs args)) := by
  intro fe lfe hfe hfrel st o st' hwf hok lst hrel
  unfold cached.core_c.proj_cert_at_i at hok
  cases verified with
  | true =>
    simp only [ConLeche.Cached.projCertAtI, if_true] at hok ⊢
    exact proj_cert_i_refines hd d lic hc hus hargs fe lfe hfe hfrel st o st'
      hwf hok lst hrel
  | false =>
    simp only [ConLeche.Cached.projCertAtI, Bool.false_eq_true, if_false,
      Result.ok.injEq, Prod.mk.injEq] at hok ⊢
    obtain ⟨rfl, rfl⟩ := hok
    exact ⟨lst, rfl, hrel, hwf, trivial⟩

end

/-! ## The abstract continuation

con-leche threads the head-normalization loop's continuation as a function
argument `k : Expr → CheckCM Expr`; the Rust carries the loop's step budget
`n` instead and calls `whnf_core_loop_i … n` where con-leche writes `k x`
(task #18's pattern 2).  `KSim` is the one hypothesis that crosses that call,
and `AppDeps.whnfCoreLoop` is what discharges it at
`k := whnfCoreLoopI … n.val`. -/

/-- The Rust loop at budget `n` refines the con-leche continuation `k`. -/
def KSim (mode : env.CheckMode) (fuel d n : Std.U64)
    (k : ConLeche.FEnv → ConLeche.Expr →
      ConLeche.Cached.CheckCM ConLeche.Expr) : Prop :=
  ∀ e : expr.Expr, ExprWF e →
    Sim absExpr ExprWF
      (fun st fe => cached.core_c.whnf_core_loop_i mode fuel st fe d n e)
      (fun lfe => k lfe (absExpr e))

/-! ## `whnf_core_proj_i` — the `.proj` continuation (`core_c.rs:2429`)

`ConLeche/Cached/CoreC.lean:963-988` writes this arm *inline* inside
`whnfCoreStepI`; the port lifts it into its own function.  Following
`Refine/StateC.lean`'s `eqvStep`, the con-leche side is therefore *named*
here — and `whnfCoreStepI_proj` below is the `rfl`-identity that says the
name is the cited subterm and nothing else, so nothing is assumed. -/

/-- `ConLeche/Cached/CoreC.lean:967-988` — the `.proj` arm of `whnfCoreStepI`
past its two knot calls, verbatim.  The structural rule
`proj_i (C p⃗ x⃗) ↦ x_i`, behind the projection table's counts, its
possibly-`Prop` level guard and `projCertAtI`; the fired field goes to the
loop's continuation `k`, not back through the knot. -/
def whnfCoreProjI (mode : ConLeche.CheckMode) (r : ConLeche.Cached.CoreFnsI)
    (fe : ConLeche.FEnv) (depth : Nat)
    (k : ConLeche.Expr → ConLeche.Cached.CheckCM ConLeche.Expr)
    (sn : ConLeche.Name) (i : Nat) (e' : ConLeche.Expr) :
    ConLeche.Cached.CheckCM ConLeche.Expr := do
  let snn ← pure sn
  match fe.findProj? snn i with
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
        if ← ConLeche.Cached.projCertAtI r fe depth mode.verifiedChecks
            mode.betaGate c us args then
          k arg
        else pure (ConLeche.Expr.proj sn i e')
      else pure (ConLeche.Expr.proj sn i e')
    | _ => pure (ConLeche.Expr.proj sn i e')
  | none => pure (ConLeche.Expr.proj sn i e')

/-- `whnfCoreProjI` **is** `whnfCoreStepI`'s `.proj` arm: the whole arm is
`r.whnf`, `projLitToCtorI`, and then this.  `rfl`, so the name assumes
nothing. -/
theorem whnfCoreStepI_proj (mode : ConLeche.CheckMode)
    (r : ConLeche.Cached.CoreFnsI) (fe : ConLeche.FEnv) (depth : Nat)
    (k : ConLeche.Expr → ConLeche.Cached.CheckCM ConLeche.Expr)
    (sn : ConLeche.Name) (i : Nat) (pe : ConLeche.Expr) :
    ConLeche.Cached.whnfCoreStepI mode r fe depth k (.proj sn i pe)
      = (do
          let e' ← r.whnf depth pe
          let e' ← ConLeche.Cached.projLitToCtorI r fe depth e'
          whnfCoreProjI mode r fe depth k sn i e') := rfl

namespace App

/-- The five `else` arms of `whnf_core_proj_i`: the redex stays stuck, and the
node the port rebuilds is con-leche's `Expr.proj sn i e'`.  The arm cannot
throw, so the outcome it reaches is an `.Ok` (task #67). -/
theorem proj_stuck {sn : name.Name} {i : Std.U64} {x : expr.Expr}
    {oc : core.result.Result expr.Expr core_types.CheckError}
    {st st' : cached.state_c.CState} (hsn : NameWF sn) (hx : ExprWF x)
    (h : (do
          let n1 ← name.dup sn
          let e ← expr.dup x
          let e1 ← expr.proj n1 i e
          ok ((core.result.Result.Ok e1, st) :
            (core.result.Result expr.Expr core_types.CheckError) ×
              cached.state_c.CState))
        = ok (oc, st')) :
    ∃ res, oc = .Ok res ∧ absExpr res = .proj (absName sn) i.val (absExpr x)
      ∧ ExprWF res ∧ st' = st := by
  obtain ⟨n1, hn1, h1⟩ := bind_eq_ok_iff.mp h
  obtain ⟨x1, hx1, h2⟩ := bind_eq_ok_iff.mp h1
  obtain ⟨e1, hp, h3⟩ := bind_eq_ok_iff.mp h2
  have hn : n1 = sn := by
    rw [name_dup_eq] at hn1; exact (Result.ok_injective hn1).symm
  have hex : x1 = x := Expr.dup_eq hx1
  rw [hn, hex] at hp
  have h4 := Result.ok_injective h3
  have hst : st = st' := congrArg Prod.snd h4
  exact ⟨e1, (congrArg Prod.fst h4).symm, Expr.proj_refines hp,
    Expr.proj_wf hsn hx hp, hst.symm⟩

end App

section
variable {mode : env.CheckMode} {fuel : Std.U64}

/-- `ConLeche/Cached/CoreC.lean:967-988` — **`whnf_core_proj_i` refines
`whnfCoreProjI`** (`core_c.rs:2429`), at an abstract continuation. -/
theorem whnf_core_proj_of_loop (hd : AppDeps mode fuel) (d n : Std.U64)
    {k : ConLeche.FEnv → ConLeche.Expr →
      ConLeche.Cached.CheckCM ConLeche.Expr} (hk : KSim mode fuel d n k)
    {sn : name.Name} {i : Std.U64} {e2 : expr.Expr} (hsn : NameWF sn)
    (he2 : ExprWF e2) :
    Sim absExpr ExprWF
      (fun st fe => cached.core_c.whnf_core_proj_i mode fuel st fe d n sn i e2)
      (fun lfe => whnfCoreProjI (absMode mode) (knot mode lfe fuel.val) lfe d.val
        (k lfe) (absName sn) i.val (absExpr e2)) := by
  intro fe lfe hfe hfrel st oc st' hwf hok lst hrel
  unfold cached.core_c.whnf_core_proj_i at hok
  obtain ⟨o, ho, hok⟩ := bind_eq_ok_iff.mp hok
  obtain ⟨habs, hpwf⟩ := ConRon.Refine.find_proj_refines
    (FindAgree.of_rel hfrel hfe) (FindWF.of_wf hfe) hsn ho
  simp only [whnfCoreProjI, pure_bind, ConLeche.Expr.getAppFn_spec,
    ConLeche.Expr.getAppArgsC_spec]
  rw [← habs]
  cases o with
  | none =>
    simp only [Option.map_none]
    obtain ⟨res, rfl, hr, hrwf, rfl⟩ := App.proj_stuck hsn he2 hok
    exact ⟨lst, by rw [App.run_pure, hr], hrel, hwf, hrwf⟩
  | some entry =>
    simp only [Option.map_some]
    have hpe : ProjEntryWF entry := hpwf entry rfl
    obtain ⟨f, hf, hok⟩ := bind_eq_ok_iff.mp hok
    obtain ⟨habsf, hfwf⟩ := ExprOps.get_app_fn_refines he2 hf
    rw [← habsf]
    obtain ⟨⟨dw, kd⟩⟩ := f
    simp only [arc_deref_eq, bind_tc_ok] at hok
    cases kd with
    | Const c us =>
      simp only [absExpr_mk, absExprKind]
      have hcwf : NameWF c := (CoreK.wf_const_inv hfwf rfl).1
      have huswf : LevelsWF us := (CoreK.wf_const_inv hfwf rfl).2
      obtain ⟨args, hargs, hok⟩ := bind_eq_ok_iff.mp hok
      obtain ⟨habsargs, hargswf⟩ := ExprOps.get_app_args_refines he2 hargs
      obtain ⟨b, hb, hok⟩ := bind_eq_ok_iff.mp hok
      have hsh := CoreK.proj_fire_shape_ok_refines hpe hcwf huswf hb
      rw [habsargs] at hsh
      -- the port's `decide`d five-conjunct guard is the cited `if` condition,
      -- the head test spelled `==` there and `=` here
      cases b with
      | false =>
        have hnc := of_decide_eq_false hsh.symm
        have hncond : ¬ ((absName c == (absProjEntry entry).ctor) = true ∧
            i.val < (absProjEntry entry).numFields ∧
            (ConLeche.Expr.getAppArgs (absExpr e2)).length
              = (absProjEntry entry).numParams + (absProjEntry entry).numFields ∧
            (absLevels us).length = (absProjEntry entry).levelParams.length ∧
            (absProjEntry entry).fireOk (absLevels us) = true) := by
          intro hcc
          exact hnc ⟨by simpa using hcc.1, hcc.2⟩
        rw [if_neg hncond]
        simp only [Bool.false_eq_true, if_false] at hok
        obtain ⟨res, rfl, hr, hrwf, rfl⟩ := App.proj_stuck hsn he2 hok
        exact ⟨lst, by rw [App.run_pure, hr], hrel, hwf, hrwf⟩
      | true =>
        have hc := of_decide_eq_true hsh.symm
        have hcond : ((absName c == (absProjEntry entry).ctor) = true ∧
            i.val < (absProjEntry entry).numFields ∧
            (ConLeche.Expr.getAppArgs (absExpr e2)).length
              = (absProjEntry entry).numParams + (absProjEntry entry).numFields ∧
            (absLevels us).length = (absProjEntry entry).levelParams.length ∧
            (absProjEntry entry).fireOk (absLevels us) = true) :=
          ⟨by simpa using hc.1, hc.2⟩
        rw [if_pos hcond]
        simp only [if_true] at hok
        obtain ⟨i1, hi1, hok⟩ := bind_eq_ok_iff.mp hok
        have hi1v : i1.val = entry.num_params.val + i.val :=
          HashMap.uscalar_add_eq hi1
        obtain ⟨arg, harg, hok⟩ := bind_eq_ok_iff.mp hok
        obtain ⟨habsarg, hargwf⟩ := CoreK.get_d_expr_refines hargswf harg
        obtain ⟨b1, hb1, hok⟩ := bind_eq_ok_iff.mp hok
        obtain ⟨b2, hb2, hok⟩ := bind_eq_ok_iff.mp hok
        rw [Env.verified_checks_refines hb1] at hok
        rw [Env.beta_gate_refines hb2] at hok
        obtain ⟨⟨rc, st1⟩, hcert, hok⟩ := bind_eq_ok_iff.mp hok
        cases rc with
        | Err err =>
          -- `projCertAtI` threw: so does con-leche's `if ← …` (move 1)
          simp at hok
          obtain ⟨rfl, rfl⟩ := hok
          rw [← habsargs]
          exact ErrSim.bindCM
            ((proj_cert_at_i_refines hd d (absMode mode).verifiedChecks
              (absMode mode).betaGate hcwf huswf hargswf).apply_err
                hwf hfe hcert hrel hfrel)
        | Ok b3 =>
          obtain ⟨lst1, hrun1, hrel1, hwf1, -⟩ :=
            (proj_cert_at_i_refines hd d (absMode mode).verifiedChecks
              (absMode mode).betaGate hcwf huswf hargswf).apply hwf hfe hcert hrel hfrel
          simp only [id_eq] at hrun1
          rw [← habsargs, App.run_bind hrun1]
          cases b3 with
          | false =>
            simp only [Bool.false_eq_true, if_false] at hok ⊢
            obtain ⟨res, rfl, hr, hrwf, rfl⟩ := App.proj_stuck hsn he2 hok
            exact ⟨lst1, by rw [App.run_pure, hr], hrel1, hwf1, hrwf⟩
          | true =>
            simp only [if_true] at hok ⊢
            rw [show (absExprs args).getD ((absProjEntry entry).numParams + i.val)
                  (ConLeche.Expr.mkBvar 0) = absExpr arg by
                rw [habsarg, hi1v, ConLeche.Expr.mkBvar_eq]
                rfl]
            exact hk arg hargwf fe lfe hfe hfrel st1 oc st' hwf1 hok lst1 hrel1
    | _ =>
      simp only [absExpr_mk, absExprKind]
      obtain ⟨res, rfl, hr, hrwf, rfl⟩ := App.proj_stuck hsn he2 hok
      exact ⟨lst, by rw [App.run_pure, hr], hrel, hwf, hrwf⟩

/-- `ConLeche/Cached/CoreC.lean:967-988` — **`whnf_core_proj_i` refines the
`.proj` continuation of `whnfCoreStepI`** (`core_c.rs:2429`), the continuation
being the head-normalization loop at the budget the Rust carries. -/
theorem whnf_core_proj_i_refines (hd : AppDeps mode fuel) (d n : Std.U64)
    (hk : KSim mode fuel d n (fun lfe => ConLeche.Cached.whnfCoreLoopI (absMode mode)
      (knot mode lfe fuel.val) lfe d.val n.val))
    {sn : name.Name} {i : Std.U64} {e2 : expr.Expr} (hsn : NameWF sn)
    (he2 : ExprWF e2) :
    Sim absExpr ExprWF
      (fun st fe => cached.core_c.whnf_core_proj_i mode fuel st fe d n sn i e2)
      (fun lfe => whnfCoreProjI (absMode mode) (knot mode lfe fuel.val) lfe d.val
        (ConLeche.Cached.whnfCoreLoopI (absMode mode) (knot mode lfe fuel.val) lfe
          d.val n.val) (absName sn) i.val (absExpr e2)) :=
  whnf_core_proj_of_loop hd d n hk hsn he2

end


/-! ## Bulk beta and the peel loop (`core_c.rs:2218`, `:2296`)

`ConLeche/Cached/CoreC.lean:855-940` is one `mutual` block at
`termination_by _ args => (args.length, 0)` / `(args.length, 1)`, so the two
lemmas are one lexicographic induction: on the remaining argument count, and
`whnfApp` before `betaPeel` at each count.  `whnfAppI` at `L` calls
`betaPeelI`/`whnfAppI` at `L - 1`; `betaPeelI` at `L` calls `whnfAppI` at `L`
and `betaPeelI` at `L - 1`. -/

namespace App

/-- `mkAppNM`'s `run`: the `pure` of `Expr.mkAppN`
(`ConLeche/Cached/StateC.lean:212-213`). -/
@[simp] theorem run_mkAppNM {lst : ConLeche.Cached.CState}
    (f : ConLeche.Expr) (xs : List ConLeche.Expr) :
    (ConLeche.Cached.mkAppNM f xs).run lst
      = .ok (ConLeche.Expr.mkAppN f xs, lst) := rfl

/-- The `instC` table's entry count on the two sides.  `StateRel` is a *lookup*
agreement, and a lookup agreement does not bound the Lean map's size, so this
used to be underivable (task #55's finding); task #61 folded it into
`Refine/State.lean`'s `StateRel` as the field `StateRel.instCSize`, with
`State.insert_size_step` as its insert lemma, so it is now just a projection. -/
theorem instCSize_of_rel {st : cached.state_c.CState}
    {lst : ConLeche.Cached.CState} (hwf : StateWF st) (hrel : StateRel st lst) :
    StateC.InstCSize st lst := hrel.instCSize

/-- `ConLeche/Cached/StateC.lean:186-199` — `inst_list_m` refines `instListM`
at the cursor `0`, in the shape the peel loop consumes.  This is
`Refine/StateC.lean`'s `inst_list_m_refines` with its two ingredients
supplied: `Arms/Bridge.lean`'s `instantiateListRefines` and `instCSize_of_rel`
above. -/
theorem inst_list_run {st st' : cached.state_c.CState} {t r : expr.Expr}
    {acc : alloc.vec.Vec expr.Expr} (hwf : StateWF st) (ht : ExprWF t)
    (hacc : ExprsWF acc)
    (h : cached.state_c.inst_list_m st t acc 0#u64 = ok (r, st')) :
    ∀ lst, StateRel st lst → ∃ lst',
      (ConLeche.Cached.instListM (absExpr t) (absExprs acc) 0).run lst
          = .ok (absExpr r, lst')
        ∧ StateRel st' lst' ∧ StateWF st' ∧ ExprWF r := by
  intro lst hrel
  obtain ⟨lst', hrun, hrel', hwf', -, hrwf⟩ :=
    StateC.inst_list_m_refines instantiateListRefines hwf ht hacc h lst hrel
      (instCSize_of_rel hwf hrel)
  exact ⟨lst', by simpa using hrun, hrel', hwf', hrwf⟩

end App

section
variable {mode : env.CheckMode} {fuel : Std.U64}

/-- **The joint induction.**  At a remaining argument count `N` — the suffix
`args[i..]` — `whnf_app_i` refines `whnfAppI` and `beta_peel_i` refines
`betaPeelI`, the first proved before the second at each `N`, exactly as
con-leche's `(args.length, tag)` order requires. -/
theorem whnf_app_beta_peel_aux (hw : Wrappers mode fuel) (hd : AppDeps mode fuel)
    (d n : Std.U64)
    {k : ConLeche.FEnv → ConLeche.Expr →
      ConLeche.Cached.CheckCM ConLeche.Expr} (hk : KSim mode fuel d n k) :
    ∀ (N : Nat) (args : alloc.vec.Vec expr.Expr) (i : Std.Usize),
      args.val.length - i.val = N → ExprsWF args →
      (∀ v : expr.Expr, ExprWF v →
        Sim absExpr ExprWF
          (fun st fe => cached.core_c.whnf_app_i mode fuel st fe d n v args i)
          (fun lfe => ConLeche.Cached.whnfAppI (absMode mode)
            (knot mode lfe fuel.val) lfe d.val (k lfe) (absExpr v)
            ((absExprs args).drop i.val))) ∧
      (∀ (t : expr.Expr) (acc : alloc.vec.Vec expr.Expr), ExprWF t → ExprsWF acc →
        Sim absExpr ExprWF
          (fun st fe => cached.core_c.beta_peel_i mode fuel st fe d n t acc args i)
          (fun lfe => ConLeche.Cached.betaPeelI (absMode mode)
            (knot mode lfe fuel.val) lfe d.val (k lfe) (absExpr t) (absExprs acc)
            ((absExprs args).drop i.val))) := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro args i hN hargs
  by_cases hlt : i.val < args.val.length
  case neg =>
    -- the spine is exhausted on both sides
    have hlen : args.val.length ≤ i.val := by omega
    have hnil : (absExprs args).drop i.val = [] :=
      List.drop_eq_nil_of_le (by simpa [absExprs] using hlen)
    have hge : i ≥ alloc.vec.Vec.len args := by
      have := alloc.vec.Vec.len_val args; scalar_tac
    constructor
    · intro v hv fe lfe hfe hfrel st oc st' hwf hok lst hrel
      unfold cached.core_c.whnf_app_i at hok
      dsimp only at hok
      rw [if_pos hge] at hok
      rw [hnil]
      obtain ⟨c, hdup, hres⟩ := bind_eq_ok_iff.mp hok
      rw [Expr.dup_eq hdup] at hres
      have h4 := Result.ok_injective hres
      -- the arm cannot throw: the outcome it reaches is `.Ok v`
      have hre : oc = .Ok v := (congrArg Prod.fst h4).symm
      have hst : st = st' := congrArg Prod.snd h4
      subst hre; subst hst
      exact ⟨lst, by simp only [ConLeche.Cached.whnfAppI, App.run_pure], hrel, hwf, hv⟩
    · intro t acc ht hacc fe lfe hfe hfrel st oc st' hwf hok lst hrel
      unfold cached.core_c.beta_peel_i at hok
      dsimp only at hok
      rw [if_pos hge] at hok
      rw [hnil]
      obtain ⟨⟨e2, st1⟩, hinst, hok⟩ := bind_eq_ok_iff.mp hok
      obtain ⟨lst1, hrun1, hrel1, hwf1, he2wf⟩ :=
        App.inst_list_run hwf ht hacc hinst lst hrel
      simp only [ConLeche.Cached.betaPeelI]
      rw [App.run_bind hrun1]
      exact App.sim_tail (hk e2 he2wf) hwf1 hfe hok hrel1 hfrel
  case pos =>
  -- one more argument to consume: `args[i]`, and the tail at `i + 1`
  obtain ⟨j, hj, hjv⟩ := usize_add_ok (i := i)
    (by have := alloc.vec.Vec.len_val args; scalar_tac)
  have hge : ¬ (i ≥ alloc.vec.Vec.len args) := by
    have := alloc.vec.Vec.len_val args; scalar_tac
  have hihApp : ∀ w : expr.Expr, ExprWF w →
      Sim absExpr ExprWF
        (fun st fe => cached.core_c.whnf_app_i mode fuel st fe d n w args j)
        (fun lfe => ConLeche.Cached.whnfAppI (absMode mode)
          (knot mode lfe fuel.val) lfe d.val (k lfe) (absExpr w)
          ((absExprs args).drop (i.val + 1))) := by
    intro w hwv
    have h := (ih (args.val.length - j.val) (by omega) args j rfl hargs).1 w hwv
    rw [hjv] at h; exact h
  have hihPeel : ∀ (t acc : _), ExprWF t → ExprsWF acc →
      Sim absExpr ExprWF
        (fun st fe => cached.core_c.beta_peel_i mode fuel st fe d n t acc args j)
        (fun lfe => ConLeche.Cached.betaPeelI (absMode mode)
          (knot mode lfe fuel.val) lfe d.val (k lfe) (absExpr t) (absExprs acc)
          ((absExprs args).drop (i.val + 1))) := by
    intro t acc ht hacc
    have h := (ih (args.val.length - j.val) (by omega) args j rfl hargs).2 t acc ht hacc
    rw [hjv] at h; exact h
  -- `args[i]` itself, and the suffix it peels off
  obtain ⟨x, hxe0, -⟩ := WP.spec_imp_exists
    (alloc.vec.Vec.index_usize_spec args i (by scalar_tac))
  have hxe : alloc.vec.Vec.index
      (core.slice.index.SliceIndexUsizeSlice expr.Expr) args i = ok x := by
    rw [alloc.vec.Vec.index_slice_index]; exact hxe0
  obtain ⟨-, hxwf, hdrop⟩ := ExprOps.vec_index_expr hargs hxe
  -- the `whnfApp` half
  have happ : ∀ v : expr.Expr, ExprWF v →
      Sim absExpr ExprWF
        (fun st fe => cached.core_c.whnf_app_i mode fuel st fe d n v args i)
        (fun lfe => ConLeche.Cached.whnfAppI (absMode mode)
          (knot mode lfe fuel.val) lfe d.val (k lfe) (absExpr v)
          ((absExprs args).drop i.val)) := by
    intro v hv fe lfe hfe hfrel st oc st' hwf hok lst hrel
    unfold cached.core_c.whnf_app_i at hok
    dsimp only at hok
    rw [if_neg hge] at hok
    have hvc := CoreK.ExprWF.children hv
    obtain ⟨⟨dv, kv⟩⟩ := v
    simp only [arc_deref_eq, bind_tc_ok] at hok
    rw [hdrop]
    cases kv with
    | Lam ty body mb =>
      obtain ⟨htywf, hbodywf, -⟩ := hvc
      obtain ⟨ty1, hty1, hok⟩ := bind_eq_ok_iff.mp hok
      obtain ⟨body1, hbody1, hok⟩ := bind_eq_ok_iff.mp hok
      rw [Expr.dup_eq hty1, Expr.dup_eq hbody1] at hok
      obtain ⟨bs, hbs, hok⟩ := bind_eq_ok_iff.mp hok
      have hbsv : bs = (absMode mode).betaSkip (absPropWhen mb.pw) :=
        Env.beta_skip_refines hbs
      simp only [absExpr_mk, absExprKind, ConLeche.Cached.whnfAppI, absBinderMeta,
        ← hbsv]
      cases bs with
      | true =>
        simp only [if_true]
        rw [hxe] at hok
        simp only [bind_tc_ok, if_true] at hok
        obtain ⟨acc, hacc, hok⟩ := bind_eq_ok_iff.mp hok
        obtain ⟨habsacc, haccwf⟩ := CoreK.expr_singleton_refines hxwf hacc
        obtain ⟨i2, hi2, hok⟩ := bind_eq_ok_iff.mp hok
        have hij : i2 = j := Result.ok_injective (hi2.symm.trans hj)
        subst hij
        rw [← habsacc]
        exact App.sim_tail (hihPeel _ acc hbodywf haccwf) hwf hfe hok hrel hfrel
      | false =>
        rw [if_neg (by simp)]
        rw [hxe] at hok
        simp only [bind_tc_ok, Bool.false_eq_true, if_false] at hok
        obtain ⟨⟨r0, st1⟩, hio, hok⟩ := bind_eq_ok_iff.mp hok
        cases r0 with
        | Err err =>
          -- the argument's io-grade inference threw (move 1)
          simp at hok
          obtain ⟨rfl, rfl⟩ := hok
          exact ErrSim.bindCM ((hw.inferIOSim d hxwf).apply_err hwf hfe hio hrel hfrel)
        | Ok ta =>
          obtain ⟨lst1, hrun1, hrel1, hwf1, htawf⟩ :=
            (hw.inferIOSim d hxwf).apply hwf hfe hio hrel hfrel
          rw [App.run_bind hrun1]
          obtain ⟨⟨r1, st2⟩, hdq, hok⟩ := bind_eq_ok_iff.mp hok
          cases r1 with
          | Err err =>
            -- the β certificate's `defeq` threw (move 1)
            simp at hok
            obtain ⟨rfl, rfl⟩ := hok
            exact ErrSim.bindCM
              ((hw.defeqSim d htawf htywf).apply_err hwf1 hfe hdq hrel1 hfrel)
          | Ok b1 =>
            obtain ⟨lst2, hrun2, hrel2, hwf2, -⟩ :=
              (hw.defeqSim d htawf htywf).apply hwf1 hfe hdq hrel1 hfrel
            simp only [id_eq] at hrun2
            rw [App.run_bind hrun2]
            cases b1 with
            | true =>
              simp only [if_true] at hok ⊢
              obtain ⟨acc, hacc, hok⟩ := bind_eq_ok_iff.mp hok
              obtain ⟨habsacc, haccwf⟩ := CoreK.expr_singleton_refines hxwf hacc
              obtain ⟨i2, hi2, hok⟩ := bind_eq_ok_iff.mp hok
              have hij : i2 = j := Result.ok_injective (hi2.symm.trans hj)
              subst hij
              rw [← habsacc]
              exact App.sim_tail (hihPeel _ acc hbodywf haccwf) hwf2 hfe hok hrel2 hfrel
            | false =>
              simp only [Bool.false_eq_true, if_false] at hok ⊢
              obtain ⟨c1, hc1, hok⟩ := bind_eq_ok_iff.mp hok
              obtain ⟨c2, hc2, hok⟩ := bind_eq_ok_iff.mp hok
              obtain ⟨fa, hfa, hok⟩ := bind_eq_ok_iff.mp hok
              obtain ⟨i2, hi2, hok⟩ := bind_eq_ok_iff.mp hok
              obtain ⟨rest, hrest, hok⟩ := bind_eq_ok_iff.mp hok
              have hi2v : i2.val = i.val + 1 := HashMap.uscalar_add_eq hi2
              obtain ⟨habsrest, hrestwf⟩ := CoreK.drop_exprs_refines hargs hrest
              rw [Expr.dup_eq hc1, Expr.dup_eq hc2] at hfa
              have hfawf := Expr.app_wf hv hxwf hfa
              rw [StateC.mk_app_n_m_eq] at hok
              obtain ⟨e3, he3, hok⟩ := bind_eq_ok_iff.mp hok
              obtain ⟨habse3, he3wf⟩ := ExprOpsC.mk_app_n_refines hfawf hrestwf he3
              have h4 := Result.ok_injective hok
              have hre : oc = .Ok e3 := (congrArg Prod.fst h4).symm
              have hst : st2 = st' := congrArg Prod.snd h4
              subst hre; subst hst
              refine ⟨lst2, ?_, hrel2, hwf2, he3wf⟩
              simp only [pure_bind, App.run_mkAppNM, Except.ok.injEq,
                Prod.mk.injEq, and_true]
              rw [habse3, Expr.app_refines hfa, habsrest, hi2v]
              simp only [absExpr_mk, absExprKind, absBinderMeta]
    | _ =>
      all_goals (
        obtain ⟨c, hdupv, hok⟩ := bind_eq_ok_iff.mp hok
        rw [hxe] at hok
        simp only [bind_tc_ok] at hok
        obtain ⟨x2, hdupx, hok⟩ := bind_eq_ok_iff.mp hok
        obtain ⟨fa, hfa, hok⟩ := bind_eq_ok_iff.mp hok
        obtain ⟨b, hb, hok⟩ := bind_eq_ok_iff.mp hok
        rw [Expr.dup_eq hdupv, Expr.dup_eq hdupx] at hfa
        have hfawf := Expr.app_wf hv hxwf hfa
        have hbv := hd.iotaArityOk fe lfe fa b hfe hfrel hfawf hb
        have hfabs := Expr.app_refines hfa
        simp only [absExpr_mk, absExprKind] at hfabs ⊢
        obtain ⟨⟨st1, step⟩, hstep, hok⟩ := bind_eq_ok_iff.mp hok
        simp only [ConLeche.Cached.whnfAppI, pure_bind, ← hfabs, ← hbv]
        cases b with
        | false =>
          simp only [Bool.false_eq_true, if_false, pure_bind] at hok ⊢
          have hs := Result.ok_injective hstep
          simp only [Prod.mk.injEq] at hs
          obtain ⟨rfl, rfl⟩ := hs
          obtain ⟨i2, hi2, hok⟩ := bind_eq_ok_iff.mp hok
          have hij : i2 = j := Result.ok_injective (hi2.symm.trans hj)
          subst hij
          exact App.sim_tail (hihApp fa hfawf) hwf hfe hok hrel hfrel
        | true =>
          simp only [if_true] at hok ⊢
          obtain ⟨⟨step1, st2⟩, hiota, hs⟩ := bind_eq_ok_iff.mp hstep
          have hs2 := Result.ok_injective hs
          simp only [Prod.mk.injEq] at hs2
          obtain ⟨rfl, rfl⟩ := hs2
          cases step1 with
          | Err err =>
            -- the ι step threw (move 1)
            simp at hok
            obtain ⟨rfl, rfl⟩ := hok
            exact ErrSim.bindCM ((hd.iotaRec d fa hfawf).apply_err hwf hfe hiota hrel hfrel)
          | Ok o =>
            obtain ⟨lst1, hrun1, hrel1, hwf1, howf⟩ :=
              (hd.iotaRec d fa hfawf).apply hwf hfe hiota hrel hfrel
            rw [App.run_bind hrun1]
            cases o with
            | none =>
              simp only [Option.map_none] at hrun1 ⊢
              obtain ⟨i2, hi2, hok⟩ := bind_eq_ok_iff.mp hok
              have hij : i2 = j := Result.ok_injective (hi2.symm.trans hj)
              subst hij
              exact App.sim_tail (hihApp fa hfawf) hwf1 hfe hok hrel1 hfrel
            | some e21 =>
              simp only [Option.map_some] at hrun1 ⊢
              have he21wf : ExprWF e21 := howf e21 rfl
              obtain ⟨⟨r2, st3⟩, hloop, hok⟩ := bind_eq_ok_iff.mp hok
              cases r2 with
              | Err err =>
                -- the continuation threw on the ι reduct (move 1)
                simp at hok
                obtain ⟨rfl, rfl⟩ := hok
                exact ErrSim.bindCM ((hk e21 he21wf).apply_err hwf1 hfe hloop hrel1 hfrel)
              | Ok v2 =>
                obtain ⟨lst2, hrun2, hrel2, hwf2, hv2wf⟩ :=
                  (hk e21 he21wf).apply hwf1 hfe hloop hrel1 hfrel
                rw [App.run_bind hrun2]
                obtain ⟨i2, hi2, hok⟩ := bind_eq_ok_iff.mp hok
                have hij : i2 = j := Result.ok_injective (hi2.symm.trans hj)
                subst hij
                exact App.sim_tail (hihApp v2 hv2wf) hwf2 hfe hok hrel2 hfrel)
  refine ⟨happ, ?_⟩
  -- the `betaPeel` half, at the same count: it may call `whnfApp` at this `N`
  intro t acc ht hacc fe lfe hfe hfrel st oc st' hwf hok lst hrel
  unfold cached.core_c.beta_peel_i at hok
  dsimp only at hok
  rw [if_neg hge] at hok
  have htc := CoreK.ExprWF.children ht
  obtain ⟨⟨dt, kt⟩⟩ := t
  simp only [arc_deref_eq, bind_tc_ok] at hok
  rw [hdrop]
  cases kt with
  | Lam ty body mb =>
    obtain ⟨htywf, hbodywf, -⟩ := htc
    obtain ⟨ty1, hty1, hok⟩ := bind_eq_ok_iff.mp hok
    obtain ⟨body1, hbody1, hok⟩ := bind_eq_ok_iff.mp hok
    rw [Expr.dup_eq hty1, Expr.dup_eq hbody1] at hok
    obtain ⟨bs, hbs, hok⟩ := bind_eq_ok_iff.mp hok
    have hbsv : bs = (absMode mode).betaSkip (absPropWhen mb.pw) :=
      Env.beta_skip_refines hbs
    simp only [absExpr_mk, absExprKind, ConLeche.Cached.betaPeelI, absBinderMeta,
      ← hbsv]
    cases bs with
    | true =>
      simp only [if_true]
      rw [hxe] at hok
      simp only [bind_tc_ok, if_true] at hok
      obtain ⟨acc2, hacc2, hok⟩ := bind_eq_ok_iff.mp hok
      obtain ⟨habsacc2, hacc2wf⟩ := ExprOps.cons_expr_refines hxwf hacc hacc2
      obtain ⟨i2, hi2, hok⟩ := bind_eq_ok_iff.mp hok
      have hij : i2 = j := Result.ok_injective (hi2.symm.trans hj)
      subst hij
      rw [← habsacc2]
      exact App.sim_tail (hihPeel _ acc2 hbodywf hacc2wf) hwf hfe hok hrel hfrel
    | false =>
      rw [if_neg (by simp)] at hok ⊢
      obtain ⟨⟨ty2, st1⟩, hinst, hok⟩ := bind_eq_ok_iff.mp hok
      obtain ⟨lst1, hrun1, hrel1, hwf1, hty2wf⟩ :=
        App.inst_list_run hwf htywf hacc hinst lst hrel
      rw [App.run_bind hrun1]
      rw [hxe] at hok
      simp only [bind_tc_ok] at hok
      obtain ⟨⟨r0, st2⟩, hio, hok⟩ := bind_eq_ok_iff.mp hok
      cases r0 with
      | Err err =>
        -- the argument's io-grade inference threw (move 1)
        simp at hok
        obtain ⟨rfl, rfl⟩ := hok
        exact ErrSim.bindCM ((hw.inferIOSim d hxwf).apply_err hwf1 hfe hio hrel1 hfrel)
      | Ok ta =>
        obtain ⟨lst2, hrun2, hrel2, hwf2, htawf⟩ :=
          (hw.inferIOSim d hxwf).apply hwf1 hfe hio hrel1 hfrel
        rw [App.run_bind hrun2]
        obtain ⟨⟨r1, st3⟩, hdq, hok⟩ := bind_eq_ok_iff.mp hok
        cases r1 with
        | Err err =>
          -- the binder's certificate `defeq` threw (move 1)
          simp at hok
          obtain ⟨rfl, rfl⟩ := hok
          exact ErrSim.bindCM
            ((hw.defeqSim d htawf hty2wf).apply_err hwf2 hfe hdq hrel2 hfrel)
        | Ok b1 =>
          obtain ⟨lst3, hrun3, hrel3, hwf3, -⟩ :=
            (hw.defeqSim d htawf hty2wf).apply hwf2 hfe hdq hrel2 hfrel
          simp only [id_eq] at hrun3
          rw [App.run_bind hrun3]
          cases b1 with
          | true =>
            simp only [if_true] at hok ⊢
            obtain ⟨acc2, hacc2, hok⟩ := bind_eq_ok_iff.mp hok
            obtain ⟨habsacc2, hacc2wf⟩ := ExprOps.cons_expr_refines hxwf hacc hacc2
            obtain ⟨i2, hi2, hok⟩ := bind_eq_ok_iff.mp hok
            have hij : i2 = j := Result.ok_injective (hi2.symm.trans hj)
            subst hij
            rw [← habsacc2]
            exact App.sim_tail (hihPeel _ acc2 hbodywf hacc2wf) hwf3 hfe hok hrel3 hfrel
          | false =>
            simp only [Bool.false_eq_true, if_false] at hok ⊢
            obtain ⟨⟨f2, st4⟩, hinst2, hok⟩ := bind_eq_ok_iff.mp hok
            obtain ⟨lst4, hrun4, hrel4, hwf4, hf2wf⟩ :=
              App.inst_list_run hwf3 ht hacc hinst2 lst3 hrel3
            simp only [absExpr_mk, absExprKind, absBinderMeta] at hrun4
            rw [App.run_bind hrun4]
            obtain ⟨c2, hc2, hok⟩ := bind_eq_ok_iff.mp hok
            obtain ⟨fa, hfa, hok⟩ := bind_eq_ok_iff.mp hok
            obtain ⟨i2, hi2, hok⟩ := bind_eq_ok_iff.mp hok
            obtain ⟨rest, hrest, hok⟩ := bind_eq_ok_iff.mp hok
            have hi2v : i2.val = i.val + 1 := HashMap.uscalar_add_eq hi2
            obtain ⟨habsrest, hrestwf⟩ := CoreK.drop_exprs_refines hargs hrest
            rw [Expr.dup_eq hc2] at hfa
            have hfawf := Expr.app_wf hf2wf hxwf hfa
            rw [StateC.mk_app_n_m_eq] at hok
            obtain ⟨e3, he3, hok⟩ := bind_eq_ok_iff.mp hok
            obtain ⟨habse3, he3wf⟩ := ExprOpsC.mk_app_n_refines hfawf hrestwf he3
            have h4 := Result.ok_injective hok
            have hre : oc = .Ok e3 := (congrArg Prod.fst h4).symm
            have hst : st4 = st' := congrArg Prod.snd h4
            subst hre; subst hst
            refine ⟨lst4, ?_, hrel4, hwf4, he3wf⟩
            simp only [pure_bind, App.run_mkAppNM, Except.ok.injEq,
              Prod.mk.injEq, and_true]
            rw [habse3, Expr.app_refines hfa, habsrest, hi2v]
  | _ =>
    all_goals (
      obtain ⟨⟨e2, st1⟩, hinst, hok⟩ := bind_eq_ok_iff.mp hok
      obtain ⟨lst1, hrun1, hrel1, hwf1, he2wf⟩ :=
        App.inst_list_run hwf ht hacc hinst lst hrel
      simp only [absExpr_mk, absExprKind] at hrun1 ⊢
      simp only [ConLeche.Cached.betaPeelI]
      rw [App.run_bind hrun1]
      obtain ⟨⟨r0, st2⟩, hloop, hok⟩ := bind_eq_ok_iff.mp hok
      cases r0 with
      | Err err =>
        -- the continuation threw on the substituted body (move 1)
        simp at hok
        obtain ⟨rfl, rfl⟩ := hok
        exact ErrSim.bindCM ((hk e2 he2wf).apply_err hwf1 hfe hloop hrel1 hfrel)
      | Ok v =>
        obtain ⟨lst2, hrun2, hrel2, hwf2, hvwf⟩ :=
          (hk e2 he2wf).apply hwf1 hfe hloop hrel1 hfrel
        rw [App.run_bind hrun2, ← hdrop]
        exact App.sim_tail (happ v hvwf) hwf2 hfe hok hrel2 hfrel)

/-- `ConLeche/Cached/CoreC.lean:867-900` — **`whnf_app_i` refines `whnfAppI`**
at an abstract continuation (`core_c.rs:2218`). -/
theorem whnf_app_of_loop (hw : Wrappers mode fuel) (hd : AppDeps mode fuel)
    (d n : Std.U64)
    {k : ConLeche.FEnv → ConLeche.Expr →
      ConLeche.Cached.CheckCM ConLeche.Expr} (hk : KSim mode fuel d n k)
    {v : expr.Expr} {args : alloc.vec.Vec expr.Expr} {i : Std.Usize}
    (hv : ExprWF v) (hargs : ExprsWF args) :
    Sim absExpr ExprWF
      (fun st fe => cached.core_c.whnf_app_i mode fuel st fe d n v args i)
      (fun lfe => ConLeche.Cached.whnfAppI (absMode mode) (knot mode lfe fuel.val)
        lfe d.val (k lfe) (absExpr v) ((absExprs args).drop i.val)) :=
  (whnf_app_beta_peel_aux hw hd d n hk _ args i rfl hargs).1 v hv

/-- `ConLeche/Cached/CoreC.lean:907-935` — **`beta_peel_i` refines
`betaPeelI`** at an abstract continuation (`core_c.rs:2296`). -/
theorem beta_peel_of_loop (hw : Wrappers mode fuel) (hd : AppDeps mode fuel)
    (d n : Std.U64)
    {k : ConLeche.FEnv → ConLeche.Expr →
      ConLeche.Cached.CheckCM ConLeche.Expr} (hk : KSim mode fuel d n k)
    {t : expr.Expr} {acc args : alloc.vec.Vec expr.Expr} {i : Std.Usize}
    (ht : ExprWF t) (hacc : ExprsWF acc) (hargs : ExprsWF args) :
    Sim absExpr ExprWF
      (fun st fe => cached.core_c.beta_peel_i mode fuel st fe d n t acc args i)
      (fun lfe => ConLeche.Cached.betaPeelI (absMode mode) (knot mode lfe fuel.val)
        lfe d.val (k lfe) (absExpr t) (absExprs acc)
        ((absExprs args).drop i.val)) :=
  (whnf_app_beta_peel_aux hw hd d n hk _ args i rfl hargs).2 t acc ht hacc

/-- `ConLeche/Cached/CoreC.lean:867-900` — **`whnf_app_i` refines `whnfAppI`**
(`core_c.rs:2218`), the continuation being the head-normalization loop at the
budget the Rust carries. -/
theorem whnf_app_i_refines (hw : Wrappers mode fuel) (hd : AppDeps mode fuel)
    (d n : Std.U64)
    (hk : KSim mode fuel d n (fun lfe => ConLeche.Cached.whnfCoreLoopI (absMode mode)
      (knot mode lfe fuel.val) lfe d.val n.val))
    {v : expr.Expr} {args : alloc.vec.Vec expr.Expr}
    {i : Std.Usize} (hv : ExprWF v) (hargs : ExprsWF args) :
    Sim absExpr ExprWF
      (fun st fe => cached.core_c.whnf_app_i mode fuel st fe d n v args i)
      (fun lfe => ConLeche.Cached.whnfAppI (absMode mode) (knot mode lfe fuel.val)
        lfe d.val
        (ConLeche.Cached.whnfCoreLoopI (absMode mode) (knot mode lfe fuel.val) lfe
          d.val n.val)
        (absExpr v) ((absExprs args).drop i.val)) :=
  whnf_app_of_loop hw hd d n hk hv hargs

/-- `ConLeche/Cached/CoreC.lean:907-935` — **`beta_peel_i` refines
`betaPeelI`** (`core_c.rs:2296`), the continuation being the
head-normalization loop at the budget the Rust carries. -/
theorem beta_peel_i_refines (hw : Wrappers mode fuel) (hd : AppDeps mode fuel)
    (d n : Std.U64)
    (hk : KSim mode fuel d n (fun lfe => ConLeche.Cached.whnfCoreLoopI (absMode mode)
      (knot mode lfe fuel.val) lfe d.val n.val))
    {t : expr.Expr} {acc args : alloc.vec.Vec expr.Expr}
    {i : Std.Usize} (ht : ExprWF t) (hacc : ExprsWF acc) (hargs : ExprsWF args) :
    Sim absExpr ExprWF
      (fun st fe => cached.core_c.beta_peel_i mode fuel st fe d n t acc args i)
      (fun lfe => ConLeche.Cached.betaPeelI (absMode mode) (knot mode lfe fuel.val)
        lfe d.val
        (ConLeche.Cached.whnfCoreLoopI (absMode mode) (knot mode lfe fuel.val) lfe
          d.val n.val)
        (absExpr t) (absExprs acc) ((absExprs args).drop i.val)) :=
  beta_peel_of_loop hw hd d n hk ht hacc hargs

end

/-! ## Axiom census (DESIGN.md §5, the P3 gate)

All seven are Lean's own three and nothing else: task #61 closed
`App.instCSize_of_rel` by folding the `instC` entry-count clause into
`Refine/State.lean`'s `StateRel`. -/

/-- info: 'ConRon.Refine.Core.pi_residual_m_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms pi_residual_m_refines

/-- info: 'ConRon.Refine.Core.fab_scope_ok_i_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms fab_scope_ok_i_refines

/-- info: 'ConRon.Refine.Core.proj_cert_i_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms proj_cert_i_refines

/-- info: 'ConRon.Refine.Core.proj_cert_at_i_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms proj_cert_at_i_refines

/-- info: 'ConRon.Refine.Core.whnf_core_proj_i_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms whnf_core_proj_i_refines

/-- info: 'ConRon.Refine.Core.whnf_app_i_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms whnf_app_i_refines

/-- info: 'ConRon.Refine.Core.beta_peel_i_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms beta_peel_i_refines

end ConRon.Refine.Core
