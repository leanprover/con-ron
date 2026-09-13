/-
# `kernel::inductives::inductives_c` refined — the two routes' drivers (task #57)

`CORE_PLAN.md` step 7, the top of the inductive tier.
`crates/con-ron-core/src/kernel/inductives/inductives_c.rs` is the *cached*
driver of each route — the stages of `ConLeche/Cached/CheckerC.lean` that the
shipped binary runs on an inductive block — and the two entry points it ends
in, `check_native_s` and `check_ind_decl_s`, are what `checker.rs`'s `.indDecl`
arm calls.  `Refine/IndSpec.lean`'s `IndRoutesSpec` is the `Prop` the checker
tier (task #56) consumes; `ind_routes_spec` at the bottom of this file produces
it.

| group | items |
|---|---|
| the modeled route | `check_ind_member_s`, `check_ind_members_s`, `provision_recs_s`, `check_ind_recs_s`, `install_proj_fn_step_s`, `install_proj_fns_s`, `check_ind_decl_struct_s`, **`check_ind_decl_s`** |
| the direct route | `check_native_pass_s`, `check_native_tail_s`, **`check_native_s`** |

## What this file is *about*: the flush policy

The cited stages "mirror their `ConLeche/Kernel/Checker.lean` counterparts
clause by clause; the differences are exactly: `flushC` at environment
transitions, `FEnv.push` maintaining the index, and *every* environment lookup
routed through the index".  The port has one spelling of the index already
(task #25's deviation 1), so what `inductives_c.rs` adds is the **flush
policy** — the one thing DESIGN.md §3.1 insists must be mirrored, because a
flush changes the memo hit/miss pattern.  Three stages were *split* in
`native_install`/`modeled` so that the flush lands exactly where the cited
`flushC` does, with one body serving both the pure and the cached spelling;
composing those halves around `Refine/StateC.lean`'s `flush_c_refines` is this
file's work, and it is why the statements below are against the `*S` drivers
rather than against the stages.

`checkIndDeclStructS` transcribes `checkIndDeclSF`'s single-type-former,
single-constructor arm, which con-leche writes inline inside a `match`; it is
an internal helper of this file only — the **entry-point** lemmas
`check_ind_decl_s_refines` and `check_native_s_refines` are stated against
con-leche's own `checkIndDeclSF`/`checkNativeS`, unmodified.

## The knot

Every lemma takes `hw : Core.Wrappers mode IndAbs.checkFuelU` — the routes
reach the core only through `sharedOpsC`, which ties `coreKnotI` at exactly
`core_k::check_fuel()` (`Refine/IndAbs.lean`).  Task #55 proves the knot's
arms; this file assumes them.

## `sorry` count

**0** (task #59 closed all nine drivers; task #62 closed the last bound).
Task #59 left one `sorry` here, and it was never a missing proof: a
`≤ Std.Usize.max` bound inside `check_ind_decl_s_refines`' structured arm that
`Modeled.ind_block_caps_refines` asked for because
`modeled::check_eta_thm_shape` / `check_unit_thm_shape` compared
`n_p as usize` against `sbinders.len()` (`Refine/Scalars.lean`'s deviation),
where `n_p` is a count `single_ind_ctor` read off a `.CtorInfo` inside the
block that nothing bounds.  The fix was in the Rust, as recorded: task #62
made those two read the subject binder with `expr_ops::dom_at_n`, a counting
recursion over the `u64`, and the bound left every statement in the chain —
`ind_block_caps`, `check_eta_thm`, `check_unit_thm`, their two shapes and
`check_ind_decl_struct_s_refines` here.

## The index-canonicity seam

Three stages of the two routes copy the index they are handed —
`native_install::check_native_pass_former` and the two `fenv::dup`s of
`inductives_c::check_ind_recs_s` — and a copy is a *rebuild*:
`Refine/FEnv.lean`'s `dup_refines` relates it to the canonical Lean `FEnv` of
the copied environment, so carrying the caller's own persistent `lfe` across it
is `FEnv.dup_rel`, which needs `FEnv.FEnvCanon` of the index being copied (and
`FEnv.FEnvFull` where a `push` has to keep the pair).  `FEnvWF` says nothing
tying `fe.idx` to `fe.env`, so it cannot supply either, and the clause really
is false without them — `Refine/IndSpec.lean`'s header is where that argument
is written down.  So the pair rides through this file: `FEnv.push_canon` at a
`push`, `check_ind_member_canon` / `check_ind_members_s_canon` through the
members' fold, and `cons_sum_ctors_canon` through `consSumCtorsF`.
`IndRoutesSpecP` carries it, and the consumer discharges it from
`FEnv.mk_fenv_canon` / `FEnv.dup_canon` / `FEnv.push_canon`.

## The matcher seam

The cited code's `match`es and this file's spelling of the same ones elaborate
to *different* auxiliary matchers, so no `rw` of a refinement ever lands on a
cited term.  Every composition against the cited code is therefore closed with
`exact` — which bridges the gap by `whnf`, matchers and `η` being definitional
— and `runBind_compose` is the one helper that makes that possible for a
two-stage `do` block, by taking the stages from the goal.

The statements are the exact-result ones and nothing below is weakened.  The
two `#print axioms` censuses at the bottom are machine-checked with
`#guard_msgs`: `sorryAx` leaving them is the gate that says the inductive tier
is closed, and as of task #62 **both are clean**.
-/
import ConRon.Refine.IndSpec
import ConRon.Refine.IndStructParts
import ConRon.Refine.IndNativeParts
import ConRon.Refine.IndStructInstall
import ConRon.Refine.IndSumParts
import ConRon.Refine.StateC
import ConRon.Refine.IndIngredients

open Aeneas Aeneas.Std Result
open ConRon.Generated ConRon.Generated.kernel ConRon.Generated.kernel.inductives
open ConRon.Refine ConRon.Refine.State ConRon.Refine.FEnv

namespace ConRon.Refine.InductivesC

/-! ## Two abstractions this file needs (**to be unified into
`Refine/Abs.lean`**) -/

/-- `provisionRecsS`' output list: the provisional recursors, each with its two
argument sums and the stream's rules. -/
def absCheckedRecs
    (cs : alloc.vec.Vec (env.ConstantVal × Std.U64 × Std.U64
      × alloc.vec.Vec env.RecRule)) :
    List (ConLeche.ConstantVal × Nat × Nat × List ConLeche.RecRule) :=
  cs.val.map (fun c =>
    (absConstantVal c.1, c.2.1.val, c.2.2.1.val, absRecRules c.2.2.2))

/-- `CheckerC.lean:233-268` — the single-type-former, single-constructor arm of
`checkIndDeclSF`, transcribed (con-leche writes it inline inside the `match`).
An internal helper: the entry-point lemma is against `checkIndDeclSF` itself. -/
def checkIndDeclStructS (mode : ConLeche.CheckMode) (lfe : ConLeche.FEnv)
    (blockNames : List ConLeche.Name)
    (nonrecs recs : List ConLeche.ConstantInfo)
    (cvT cvC : ConLeche.ConstantVal) (nP nF : Nat) :
    ConLeche.Cached.CheckCM ConLeche.FEnv := do
  let caps ← pure (ConLeche.indBlockCapsF mode lfe cvT cvC nP nF)
  let fe₂ ← nonrecs.foldlM (ConLeche.Cached.checkIndMemberS mode blockNames caps) lfe
  let fe₃ ← ConLeche.Cached.checkIndRecsS mode blockNames fe₂ recs
  unless ConLeche.ctorResidualOkF mode fe₃ cvT.name cvC.name cvT.levelParams nP nF
      caps.eta do
    throw (.notImplemented "modeled structure: eta constructor residual")
  unless (List.range nF).all (fun j => (fe₃.find? (ConLeche.projFnName cvT.name j)).isNone) do
    throw (.invalid "projection name family taken")
  if ConLeche.ctorTargetsFam cvC.type cvT.name cvT.levelParams nP nF then
    (List.range nF).foldlM
      (ConLeche.Cached.installProjFnStepS mode cvT.name cvC.name cvT.levelParams nP nF)
      fe₃
  else pure fe₃

/-! ## Two shims the compositions below need -/

/-- A `throw` swallows the rest of its `do` block: in `StateT CState (Except …)`
`throw` discards the state, which is why `checkIndRecsS`' guard arm may be read
without the phase's flush. -/
private theorem throwC_bind {α β : Type} (e : ConLeche.CheckError)
    (g : α → ConLeche.Cached.CheckCM β) : (throw e >>= g) = throw e := rfl

/-- Two stages' runs composed, **without naming either stage**.  The cited code
and this file spell the same `match` with different auxiliary matchers, so a
`rw` of a stage's refinement into the cited term never fires; applying this with
`_`s takes the stages from the *goal* and accepts the two refinements up to
`whnf`, which is where the matchers meet. -/
private theorem runBind_compose {α : Type}
    {A : ConLeche.Cached.CheckCM ConLeche.FEnv}
    {B : ConLeche.FEnv → ConLeche.Cached.CheckCM α}
    {lst lst1 lst' : ConLeche.Cached.CState} {x : ConLeche.FEnv} {y : α}
    (hA : A.run lst = .ok (x, lst1)) (hB : (B x).run lst1 = .ok (y, lst')) :
    (A >>= B).run lst = .ok (y, lst') := by
  simp only [StateT.run_bind, hA, NativeInstall.exceptOk_bind]
  exact hB


/-- **The cited member stage is the flush and the body.**  `checkIndMemberS`
opens with `flushC`; `Refine/IndModeled.lean`'s `checkIndMemberN` is the rest,
which is what `modeled::check_ind_member` refines. -/
private theorem checkIndMemberS_eq (lmode : ConLeche.CheckMode)
    (blockNames : List ConLeche.Name) (caps : ConLeche.IndCaps)
    (lfe : ConLeche.FEnv) (ci : ConLeche.ConstantInfo) :
    ConLeche.Cached.checkIndMemberS lmode blockNames caps lfe ci
      = (do
          ConLeche.Cached.flushC
          Modeled.checkIndMemberN lmode blockNames caps lfe ci) := by
  rfl

/-- `provisionRecsS` at a cons: **the flush**, the step, then the tail, with the
checked recursor consed on the way out.  `Refine/IndModeled.lean`'s
`provisionRecsStepN` is the cited arm minus that flush. -/
private theorem provisionRecsS_cons {lmode : ConLeche.CheckMode}
    {blockNames : List ConLeche.Name} {feAcc fe1 fe2 : ConLeche.FEnv}
    {ci : ConLeche.ConstantInfo} {rest : List ConLeche.ConstantInfo}
    {cv : ConLeche.ConstantVal} {mI rP : Nat} {rules : List ConLeche.RecRule}
    {tail : List (ConLeche.ConstantVal × Nat × Nat × List ConLeche.RecRule)}
    {lst lst1 lst2 : ConLeche.Cached.CState}
    (h1 : (Modeled.provisionRecsStepN lmode blockNames feAcc ci).run lst.flushed
      = .ok ((fe1, cv, mI, rP, rules), lst1))
    (h2 : (ConLeche.Cached.provisionRecsS lmode blockNames fe1 rest).run lst1
      = .ok ((fe2, tail), lst2)) :
    (ConLeche.Cached.provisionRecsS lmode blockNames feAcc (ci :: rest)).run lst
      = .ok ((fe2, (cv, mI, rP, rules) :: tail), lst2) := by
  cases ci
  case recInfo cv0 mI0 rP0 rules0 =>
    rw [Modeled.provisionRecsStepN] at h1
    rw [ConLeche.Cached.provisionRecsS]
    rw [StateT.run_bind, StateC.flushC_run, NativeInstall.exceptOk_bind]
    simp only [StateT.run, Bind.bind, StateT.bind, Except.bind, Pure.pure,
      StateT.pure, Except.pure] at h1 h2 ⊢
    split at h1
    · simp at h1
    · rename_i v heq
      simp only [Except.ok.injEq, Prod.mk.injEq] at h1
      obtain ⟨⟨rfl, rfl, rfl, rfl, rfl⟩, rfl⟩ := h1
      rw [h2]
  all_goals
    simp [Modeled.provisionRecsStepN, StateT.run, throw, throwThe,
      MonadExceptOf.throw, StateT.lift, Bind.bind, Except.bind] at h1

/-- `provisionRecsS_cons`' failure halves (task #67).  The cons arm throws
exactly what its step threw, and — the step having succeeded — exactly what its
tail threw; the per-recursor `flushC` in front cannot throw, so the two are the
whole of the arm's failure behaviour. -/
private theorem provisionRecsS_cons_err {lmode : ConLeche.CheckMode}
    {blockNames : List ConLeche.Name} {feAcc : ConLeche.FEnv}
    {ci : ConLeche.ConstantInfo} {rest : List ConLeche.ConstantInfo}
    {lst : ConLeche.Cached.CState} {le : ConLeche.CheckError}
    (h1 : (Modeled.provisionRecsStepN lmode blockNames feAcc ci).run lst.flushed
      = .error le) :
    (ConLeche.Cached.provisionRecsS lmode blockNames feAcc (ci :: rest)).run lst
      = .error le := by
  cases ci
  case recInfo cv0 mI0 rP0 rules0 =>
    rw [Modeled.provisionRecsStepN] at h1
    rw [ConLeche.Cached.provisionRecsS]
    rw [StateT.run_bind, StateC.flushC_run, NativeInstall.exceptOk_bind]
    simp only [StateT.run, Bind.bind, StateT.bind, Except.bind, Pure.pure,
      StateT.pure, Except.pure] at h1 ⊢
    split at h1
    · simp only [Except.error.injEq] at h1 ⊢
      exact h1
    · simp at h1
  all_goals
    simp_all [Modeled.provisionRecsStepN, ConLeche.Cached.provisionRecsS,
      StateT.run, throw, throwThe, MonadExceptOf.throw, StateT.lift, Bind.bind,
      Except.bind]

/-- The same at a step that succeeded and a tail that threw. -/
private theorem provisionRecsS_cons_tail_err {lmode : ConLeche.CheckMode}
    {blockNames : List ConLeche.Name} {feAcc fe1 : ConLeche.FEnv}
    {ci : ConLeche.ConstantInfo} {rest : List ConLeche.ConstantInfo}
    {cv : ConLeche.ConstantVal} {mI rP : Nat} {rules : List ConLeche.RecRule}
    {lst lst1 : ConLeche.Cached.CState} {le : ConLeche.CheckError}
    (h1 : (Modeled.provisionRecsStepN lmode blockNames feAcc ci).run lst.flushed
      = .ok ((fe1, cv, mI, rP, rules), lst1))
    (h2 : (ConLeche.Cached.provisionRecsS lmode blockNames fe1 rest).run lst1
      = .error le) :
    (ConLeche.Cached.provisionRecsS lmode blockNames feAcc (ci :: rest)).run lst
      = .error le := by
  cases ci
  case recInfo cv0 mI0 rP0 rules0 =>
    rw [Modeled.provisionRecsStepN] at h1
    rw [ConLeche.Cached.provisionRecsS]
    rw [StateT.run_bind, StateC.flushC_run, NativeInstall.exceptOk_bind]
    simp only [StateT.run, Bind.bind, StateT.bind, Except.bind, Pure.pure,
      StateT.pure, Except.pure] at h1 h2 ⊢
    split at h1
    · simp at h1
    · rename_i v heq
      simp only [Except.ok.injEq, Prod.mk.injEq] at h1
      obtain ⟨⟨rfl, rfl, rfl, rfl, rfl⟩, rfl⟩ := h1
      rw [h2]
  all_goals
    simp [Modeled.provisionRecsStepN, StateT.run, throw, throwThe,
      MonadExceptOf.throw, StateT.lift, Bind.bind, Except.bind] at h1

set_option linter.unusedSimpArgs false in
/-- **The cited recursor group is the guards, the phase and the fold around one
`flushC`.**  `Refine/IndModeled.lean`'s `checkIndRecsFoldN` is the fold and its
`blockRename` the rename closure `checkIndRecsS` writes inline; the per-recursor
flushes are `provisionRecsS`'s and the phase's is the one spelled here. -/
private theorem checkIndRecsS_eq (lmode : ConLeche.CheckMode)
    (blockNames : List ConLeche.Name) (fe2 : ConLeche.FEnv)
    (recs : List ConLeche.ConstantInfo) :
    ConLeche.Cached.checkIndRecsS lmode blockNames fe2 recs
      = (if recs.isEmpty then pure fe2
         else if fe2.find? ConLeche.eqName = some ConLeche.eqA then
           (do
             let (feSelf, checked) ←
               ConLeche.Cached.provisionRecsS lmode blockNames fe2 recs
             ConLeche.Cached.flushC
             Modeled.checkIndRecsFoldN lmode fe2 feSelf
               (Modeled.blockRename blockNames) checked fe2)
         else throw (.notImplemented
           "modeled recursor requires the pinned Eq basis")) := by
  simp only [ConLeche.Cached.checkIndRecsS, Modeled.checkIndRecsFoldN,
    throwC_bind, bind_assoc, pure_bind]
  try rfl

/-- `modeled::check_ind_member` keeps the **unrestricted-canonical** pair: on
success it is one `fenv::push` onto the index it is handed, and
`FEnv.push_canon` is exactly that step.  The `FEnvWF fe'` premise is how the
`ConstantInfoWF` of the pushed record is reached (off `EnvWF` of the *result*,
through `FEnv.push_consts`) without dragging the knot into a statement that
mentions no abstraction — every caller has it from
`Modeled.check_ind_member_refines`.  This is the modeled route's counterpart of
`SumInstall.check_sum_ind_canon`. -/
private theorem check_ind_member_canon {mode : env.CheckMode}
    {st st' : cached.state_c.CState} {block_names : alloc.vec.Vec name.Name}
    {caps : env.IndCaps} {fe fe' : fenv.FEnv} {ci : env.ConstantInfo}
    (hfe : FEnvWF fe) (hcan : FEnv.FEnvCanon fe) (hfull : FEnv.FEnvFull fe)
    (hwf' : FEnvWF fe')
    (h : inductives.modeled.check_ind_member mode st block_names caps fe ci
        = ok (.Ok fe', st')) :
    FEnv.FEnvCanon fe' ∧ FEnv.FEnvFull fe' := by
  rw [inductives.modeled.check_ind_member] at h
  obtain ⟨cv, hcv, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨p, hp, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨r, st1⟩ := p
  cases r with
  | Err err => simp at h
  | Ok cv_a =>
    cases ci
    case IndInfo =>
      obtain ⟨ic, hic, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨f, hpush, h⟩ := bind_eq_ok_iff.mp h
      simp only [Result.ok.injEq, Prod.mk.injEq, core.result.Result.Ok.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      refine FEnv.push_canon hfe ?_ hcan hfull hpush
      refine hwf'.env _ ?_
      rw [FEnv.push_consts hpush]; simp
    case CtorInfo =>
      obtain ⟨f, hpush, h⟩ := bind_eq_ok_iff.mp h
      simp only [Result.ok.injEq, Prod.mk.injEq, core.result.Result.Ok.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      refine FEnv.push_canon hfe ?_ hcan hfull hpush
      refine hwf'.env _ ?_
      rw [FEnv.push_consts hpush]; simp
    all_goals simp at h

/-- `inductives_c::check_ind_member_s` keeps the canonical pair: it is the
flush and `modeled::check_ind_member`, and a flush does not touch the index. -/
private theorem check_ind_member_s_canon {mode : env.CheckMode}
    {st st' : cached.state_c.CState} {block_names : alloc.vec.Vec name.Name}
    {caps : env.IndCaps} {fe fe' : fenv.FEnv} {ci : env.ConstantInfo}
    (hfe : FEnvWF fe) (hcan : FEnv.FEnvCanon fe) (hfull : FEnv.FEnvFull fe)
    (hwf' : FEnvWF fe')
    (h : inductives.inductives_c.check_ind_member_s mode st block_names caps fe ci
        = ok (.Ok fe', st')) :
    FEnv.FEnvCanon fe' ∧ FEnv.FEnvFull fe' := by
  rw [inductives.inductives_c.check_ind_member_s] at h
  obtain ⟨st1, _, h⟩ := bind_eq_ok_iff.mp h
  exact check_ind_member_canon hfe hcan hfull hwf' h

/-- `@decide _ (blockRecSuffixDec block)` **is** `recsFormSuffix block`: the
instance is `decidable_of_iff _ recsFormSuffix_iff`, so the two Bools agree on
`= true` and a Bool is determined by that. -/
private theorem blockRecSuffix_decide (block : List ConLeche.ConstantInfo) :
    @decide _ (ConLeche.blockRecSuffixDec block) = ConLeche.recsFormSuffix block := by
  rw [Bool.eq_iff_iff, decide_eq_true_iff]
  exact (ConLeche.recsFormSuffix_iff block).symm

/-- `modeled::single_ind_ctor` hands back constants it read **out of the
block**, so they are well formed.  `Refine/IndModeled.lean`'s
`single_ind_ctor_refines` states only the abstraction, and
`check_ind_decl_struct_s_refines` needs the two `ConstantValWF`s; this is that
missing half, as the accumulating index recursion the port writes.  (**To be
moved next to `single_ind_ctor_refines`** when the tier is merged.) -/
private theorem single_ind_ctor_from_wf {block : alloc.vec.Vec env.ConstantInfo}
    (hblock : ConstantInfosWF block) :
    ∀ (k : Nat) (i : Std.Usize) (t : Option env.ConstantVal)
      (c : Option (env.ConstantVal × Std.U64 × Std.U64)) (n_ind n_ctor : Std.U64)
      (q : (Option env.ConstantVal) × (Option (env.ConstantVal × Std.U64
        × Std.U64)) × Std.U64 × Std.U64),
      block.length - i.val ≤ k →
      (∀ cv, t = some cv → ConstantValWF cv) →
      (∀ p, c = some p → ConstantValWF p.1) →
      inductives.modeled.single_ind_ctor_from block i t c n_ind n_ctor = ok q →
      (∀ cv, q.1 = some cv → ConstantValWF cv)
        ∧ (∀ p, q.2.1 = some p → ConstantValWF p.1) := by
  intro k
  induction k with
  | zero =>
    intro i t c n_ind n_ctor q hk ht hc h
    have hlv := alloc.vec.Vec.len_val block
    rw [inductives.modeled.single_ind_ctor_from] at h
    rw [if_pos (show i ≥ alloc.vec.Vec.len block by scalar_tac),
      Result.ok.injEq] at h
    rw [← h]; exact ⟨ht, hc⟩
  | succ k ih =>
    intro i t c n_ind n_ctor q hk ht hc h
    have hlv := alloc.vec.Vec.len_val block
    rw [inductives.modeled.single_ind_ctor_from] at h
    by_cases hi : block.val.length ≤ i.val
    · rw [if_pos (show i ≥ alloc.vec.Vec.len block by scalar_tac),
        Result.ok.injEq] at h
      rw [← h]; exact ⟨ht, hc⟩
    · rw [if_neg (show ¬ i ≥ alloc.vec.Vec.len block by scalar_tac)] at h
      have hlt : i.val < block.val.length := by omega
      obtain ⟨y, hy, hyv⟩ :=
        WP.spec_imp_exists (alloc.vec.Vec.index_usize_spec block i hlt)
      subst hyv
      simp only [alloc.vec.Vec.index_slice_index, hy, bind_tc_ok] at h
      have hciwf : ConstantInfoWF block.val[i.val] := hblock _ (List.getElem_mem hlt)
      revert hciwf h
      cases block.val[i.val]
      case IndInfo =>
        intro h hciwf
        obtain ⟨cv1, hcv1, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨i2, hi2, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨i3, hi3, h⟩ := bind_eq_ok_iff.mp h
        have hi2v : i2.val = i.val + 1 := HashMap.uscalar_add_eq hi2
        refine ih i2 (some cv1) c i3 n_ctor q (by omega) ?_ hc h
        intro cv hcv
        rw [Option.some.injEq] at hcv
        subst hcv
        revert hcv1
        cases t with
        | none =>
          intro hcv1
          simp only [] at hcv1
          rw [Env.constant_val_dup_refines hcv1]
          exact hciwf.1
        | some old =>
          intro hcv1
          simp only [Result.ok.injEq] at hcv1
          rw [← hcv1]
          exact ht old rfl
      case CtorInfo =>
        intro h hciwf
        obtain ⟨t1, ht1, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨i2, hi2, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨i3, hi3, h⟩ := bind_eq_ok_iff.mp h
        have hi2v : i2.val = i.val + 1 := HashMap.uscalar_add_eq hi2
        refine ih i2 t (some t1) n_ind i3 q (by omega) ht ?_ h
        intro p hp
        rw [Option.some.injEq] at hp
        subst hp
        revert ht1
        cases c with
        | none =>
          intro ht1
          simp only [bind_eq_ok_iff, Result.ok.injEq] at ht1
          obtain ⟨cv1, hcv1, ht1⟩ := ht1
          rw [← ht1]
          simp only []
          rw [Env.constant_val_dup_refines hcv1]
          exact hciwf
        | some old =>
          intro ht1
          simp only [Result.ok.injEq] at ht1
          rw [← ht1]
          exact hc old rfl
      all_goals
        (intro h hciwf
         obtain ⟨i2, hi2, h⟩ := bind_eq_ok_iff.mp h
         have hi2v : i2.val = i.val + 1 := HashMap.uscalar_add_eq hi2
         exact ih i2 t c n_ind n_ctor q (by omega) ht hc h)

/-- `modeled::single_ind_ctor`'s two constants are well formed. -/
private theorem single_ind_ctor_wf {block : alloc.vec.Vec env.ConstantInfo}
    {o : Option (env.ConstantVal × env.ConstantVal × Std.U64 × Std.U64)}
    (hblock : ConstantInfosWF block)
    (h : inductives.modeled.single_ind_ctor block = ok o) :
    ∀ q, o = some q → ConstantValWF q.1 ∧ ConstantValWF q.2.1 := by
  intro q hq
  subst hq
  rw [inductives.modeled.single_ind_ctor] at h
  obtain ⟨p, hp, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨o0, o1, nI, nC⟩ := p
  obtain ⟨hwf0, hwf1⟩ :=
    single_ind_ctor_from_wf hblock block.length 0#usize none none 0#u64 0#u64 _
      (by scalar_tac) (by simp) (by simp) hp
  simp only [] at hwf0 hwf1
  -- the tuple `let` Aeneas emits does not reduce under `split` (task #16's
  -- hard spot 1), so the shape goes by ascription
  replace h : (if nI = 1#u64 then
      (if nC = 1#u64 then
        (match o0 with
         | none => ok none
         | some cv_t =>
           match o1 with
           | none => ok none
           | some cq => ok (some (cv_t, cq.1, cq.2.1, cq.2.2)))
       else ok none)
    else ok none) = ok (some q) := h
  by_cases hnI : nI = 1#u64
  · rw [if_pos hnI] at h
    by_cases hnC : nC = 1#u64
    · rw [if_pos hnC] at h
      cases o0 with
      | none => simp at h
      | some cv_t =>
        cases o1 with
        | none => simp at h
        | some cq =>
          simp only [Result.ok.injEq, Option.some.injEq] at h
          subst h
          exact ⟨hwf0 cv_t rfl, hwf1 cq rfl⟩
    · rw [if_neg hnC] at h; simp at h
  · rw [if_neg hnI] at h; simp at h

section Drivers

variable {mode : env.CheckMode} (hw : Core.Wrappers mode IndAbs.checkFuelU)

include hw

/-! ## The modeled route -/

/-- `ConLeche/Cached/CheckerC.lean:105-113` — `check_ind_member_s` refines
`checkIndMemberS`: **one flush entering the member's environment**, then
`checkIndMember`'s body. -/
theorem check_ind_member_s_refines
    {st st' : cached.state_c.CState} {block_names : alloc.vec.Vec name.Name}
    {caps : env.IndCaps} {fe : fenv.FEnv} {ci : env.ConstantInfo}
    {out : core.result.Result fenv.FEnv core_types.CheckError}
    (hst : StateWF st) (hfe : FEnvWF fe) (hbn : NamesWF block_names)
    (hcaps : IndCapsWF caps) (hci : ConstantInfoWF ci)
    (h : inductives.inductives_c.check_ind_member_s mode st block_names caps fe ci
        = ok (out, st')) :
    ∀ lst lfe, StateRel st lst → FEnvRel fe lfe →
      match out with
      | .Ok fe' =>
        ∃ lst' lfe',
          (ConLeche.Cached.checkIndMemberS (absMode mode) (absNames block_names)
              (absIndCaps caps) lfe (absConstantInfo ci)).run lst = .ok (lfe', lst')
          ∧ StateRel st' lst' ∧ FEnvRel fe' lfe' ∧ StateWF st' ∧ FEnvWF fe'
      | .Err e =>
        ErrSim e ((ConLeche.Cached.checkIndMemberS (absMode mode)
          (absNames block_names) (absIndCaps caps) lfe
          (absConstantInfo ci)).run lst) := by
  -- `StateC.flush_c_refines` then `IndModeled`'s `check_ind_member` stage; the
  -- flush cannot throw, so *both* halves are the stage's, past the flush
  intro lst lfe hrel hfer
  rw [inductives.inductives_c.check_ind_member_s] at h
  obtain ⟨st1, hflush, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨hfrun, hrel1, hwf1, _⟩ := StateC.flush_c_refines hrel hst hflush
  have hbody :=
    Modeled.check_ind_member_refines hw (IndIngredients.checkerBaseSpec hw) hwf1
      hfe hbn hcaps hci h lst.flushed lfe hrel1 hfer
  cases out with
  | Ok fe' =>
    obtain ⟨lst', lfe', hrun, hrel2, hfrel2, hwf2, hfwf2⟩ := hbody
    refine ⟨lst', lfe', ?_, hrel2, hfrel2, hwf2, hfwf2⟩
    rw [checkIndMemberS_eq]
    simp only [StateT.run_bind, StateC.flushC_run, NativeInstall.exceptOk_bind]
    exact hrun
  | Err e =>
    rw [checkIndMemberS_eq]
    simp only [StateT.run_bind, StateC.flushC_run, NativeInstall.exceptOk_bind]
    exact hbody

/-- `ConLeche/Cached/CheckerC.lean:233-268` — `check_ind_members_s` refines
`nonrecs.foldlM (checkIndMemberS mode blockNames caps) fe`, as an index
recursion over the filtered members. -/
theorem check_ind_members_s_refines
    {st st' : cached.state_c.CState} {block_names : alloc.vec.Vec name.Name}
    {caps : env.IndCaps} {fe : fenv.FEnv}
    {nonrecs : alloc.vec.Vec env.ConstantInfo} {i : Std.Usize}
    {out : core.result.Result fenv.FEnv core_types.CheckError}
    (hst : StateWF st) (hfe : FEnvWF fe) (hbn : NamesWF block_names)
    (hcaps : IndCapsWF caps) (hnr : ConstantInfosWF nonrecs)
    (h : inductives.inductives_c.check_ind_members_s mode st block_names caps fe
        nonrecs i = ok (out, st')) :
    ∀ lst lfe, StateRel st lst → FEnvRel fe lfe →
      match out with
      | .Ok fe' =>
        ∃ lst' lfe',
          (((absConstantInfos nonrecs).drop i.val).foldlM
              (ConLeche.Cached.checkIndMemberS (absMode mode) (absNames block_names)
                (absIndCaps caps)) lfe).run lst = .ok (lfe', lst')
          ∧ StateRel st' lst' ∧ FEnvRel fe' lfe' ∧ StateWF st' ∧ FEnvWF fe'
      | .Err e =>
        ErrSim e ((((absConstantInfos nonrecs).drop i.val).foldlM
          (ConLeche.Cached.checkIndMemberS (absMode mode) (absNames block_names)
            (absIndCaps caps)) lfe).run lst) := by
  generalize hd : nonrecs.length - i.val = d
  induction d using Nat.strong_induction_on generalizing st fe i with
  | _ d ih =>
    intro lst lfe hrel hfer
    rw [inductives.inductives_c.check_ind_members_s] at h
    split at h
    · -- the index is past the end: the fold is over the empty list
      rename_i hge
      have hnil : (absConstantInfos nonrecs).drop i.val = [] := by
        apply List.drop_eq_nil_of_le
        simp only [absConstantInfos, List.length_map]
        scalar_tac
      simp only [Result.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨lst, lfe, by
        simp only [hnil, List.foldlM_nil, StateT.run, Pure.pure, StateT.pure]
        rfl, hrel, hfer, hst, hfe⟩
    · rename_i hlt
      have hlt' : i.val < nonrecs.val.length := by
        have := alloc.vec.Vec.len_val nonrecs; scalar_tac
      obtain ⟨y, hy, hyv⟩ :=
        WP.spec_imp_exists (alloc.vec.Vec.index_usize_spec nonrecs i hlt')
      subst hyv
      simp only [alloc.vec.Vec.index_slice_index, hy, bind_tc_ok] at h
      obtain ⟨p, hstep, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨r, st1⟩ := p
      have hlt2 : i.val < (absConstantInfos nonrecs).length := by
        simpa [absConstantInfos] using hlt'
      have hciwf : ConstantInfoWF nonrecs.val[i.val] := hnr _ (List.getElem_mem hlt')
      cases r with
      | Err e =>
        -- the member threw: the fold's head threw, and the rest never runs
        simp at h
        obtain ⟨rfl, rfl⟩ := h
        have hmem :=
          check_ind_member_s_refines hw hst hfe hbn hcaps hciwf hstep lst lfe hrel hfer
        have hcons : (absConstantInfos nonrecs).drop i.val
            = absConstantInfo nonrecs.val[i.val]
              :: (absConstantInfos nonrecs).drop (i.val + 1) := by
          rw [List.drop_eq_getElem_cons hlt2]
          simp [absConstantInfos]
        rw [hcons, List.foldlM_cons]
        exact ErrSim.bindCM hmem
      | Ok fe2 =>
        obtain ⟨i2, hi2, h⟩ := by simpa using bind_eq_ok_iff.mp (by simpa using h)
        have hi2v : i2.val = i.val + 1 := HashMap.uscalar_add_eq hi2
        obtain ⟨lst1, lfe1, hrun1, hrel1, hfer1, hwf1, hfew1⟩ :=
          check_ind_member_s_refines hw hst hfe hbn hcaps hciwf hstep lst lfe hrel hfer
        have htail :=
          ih (nonrecs.length - i2.val) (by scalar_tac) hwf1 hfew1 h rfl lst1 lfe1
            hrel1 hfer1
        have hcons : (absConstantInfos nonrecs).drop i.val
            = absConstantInfo nonrecs.val[i.val]
              :: (absConstantInfos nonrecs).drop i2.val := by
          rw [List.drop_eq_getElem_cons hlt2, hi2v]
          simp [absConstantInfos]
        cases out with
        | Ok fe' =>
          obtain ⟨lst', lfe', hrunr, hrelr, hferr, hwfr, hfewr⟩ := htail
          refine ⟨lst', lfe', ?_, hrelr, hferr, hwfr, hfewr⟩
          rw [hcons, List.foldlM_cons]
          simp only [StateT.run, Bind.bind, StateT.bind, Except.bind] at hrun1 hrunr ⊢
          rw [hrun1]
          exact hrunr
        | Err e =>
          rw [hcons, List.foldlM_cons]
          simp only [StateT.run, Bind.bind, StateT.bind, Except.bind] at hrun1 htail ⊢
          rw [hrun1]
          exact htail

/-- The members' fold keeps the **unrestricted-canonical** pair: every step is
one `fenv::push` (`check_ind_member_s_canon`).  `check_ind_decl_struct_s` needs
it because `check_ind_recs_s` copies the index it is handed.  The `StateRel` /
`FEnvRel` arguments are only how the step's `FEnvWF` is reached; every caller
of this lemma is already inside them. -/
private theorem check_ind_members_s_canon
    {st st' : cached.state_c.CState} {block_names : alloc.vec.Vec name.Name}
    {caps : env.IndCaps} {fe fe' : fenv.FEnv}
    {nonrecs : alloc.vec.Vec env.ConstantInfo} {i : Std.Usize}
    (hst : StateWF st) (hfe : FEnvWF fe) (hbn : NamesWF block_names)
    (hcaps : IndCapsWF caps) (hnr : ConstantInfosWF nonrecs)
    (hcan : FEnv.FEnvCanon fe) (hfull : FEnv.FEnvFull fe)
    (h : inductives.inductives_c.check_ind_members_s mode st block_names caps fe
        nonrecs i = ok (.Ok fe', st')) :
    ∀ lst lfe, StateRel st lst → FEnvRel fe lfe →
      FEnv.FEnvCanon fe' ∧ FEnv.FEnvFull fe' := by
  generalize hd : nonrecs.length - i.val = d
  induction d using Nat.strong_induction_on generalizing st fe i with
  | _ d ih =>
    intro lst lfe hrel hfer
    rw [inductives.inductives_c.check_ind_members_s] at h
    split at h
    · simp only [Result.ok.injEq, Prod.mk.injEq, core.result.Result.Ok.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨hcan, hfull⟩
    · rename_i hlt
      have hlt' : i.val < nonrecs.val.length := by
        have := alloc.vec.Vec.len_val nonrecs; scalar_tac
      obtain ⟨y, hy, hyv⟩ :=
        WP.spec_imp_exists (alloc.vec.Vec.index_usize_spec nonrecs i hlt')
      subst hyv
      simp only [alloc.vec.Vec.index_slice_index, hy, bind_tc_ok] at h
      obtain ⟨p, hstep, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨r, st1⟩ := p
      cases r with
      | Err e => simp at h
      | Ok fe2 =>
        obtain ⟨i2, hi2, h⟩ := by simpa using bind_eq_ok_iff.mp (by simpa using h)
        have hi2v : i2.val = i.val + 1 := HashMap.uscalar_add_eq hi2
        have hciwf : ConstantInfoWF nonrecs.val[i.val] := hnr _ (List.getElem_mem hlt')
        obtain ⟨lst1, lfe1, hrun1, hrel1, hfer1, hwf1, hfew1⟩ :=
          check_ind_member_s_refines hw hst hfe hbn hcaps hciwf hstep lst lfe hrel
            hfer
        obtain ⟨hcan2, hfull2⟩ := check_ind_member_s_canon hfe hcan hfull hfew1 hstep
        exact ih (nonrecs.length - i2.val) (by scalar_tac) hwf1 hfew1 hcan2 hfull2 h
          rfl lst1 lfe1 hrel1 hfer1

/-- `ConLeche/Cached/CheckerC.lean:115-129` — the index recursion behind
`provision_recs_s_refines`, carrying one extra conclusion the driver above it
needs and the statement below cannot hold: **the checked recursors are well
formed**, which `check_ind_recs_s` has to hand to
`Modeled.check_ind_recs_fold_refines`.  It is an *implication* in the
conclusion rather than a hypothesis so that the exact-result statement below is
a plain projection of this one. -/
private theorem provision_recs_s_val
    {st st' : cached.state_c.CState} {block_names : alloc.vec.Vec name.Name}
    {fe_acc : fenv.FEnv} {recs : alloc.vec.Vec env.ConstantInfo} {i : Std.Usize}
    {out : alloc.vec.Vec (env.ConstantVal × Std.U64 × Std.U64
      × alloc.vec.Vec env.RecRule)}
    {oq : core.result.Result (fenv.FEnv × alloc.vec.Vec (env.ConstantVal × Std.U64
      × Std.U64 × alloc.vec.Vec env.RecRule)) core_types.CheckError}
    (hst : StateWF st) (hfe : FEnvWF fe_acc) (hbn : NamesWF block_names)
    (hrecs : ConstantInfosWF recs)
    (h : inductives.inductives_c.provision_recs_s mode st block_names fe_acc recs
        i out = ok (oq, st')) :
    ∀ lst lfe, StateRel st lst → FEnvRel fe_acc lfe →
      match oq with
      | .Ok q =>
        ∃ lst' lfe',
          (ConLeche.Cached.provisionRecsS (absMode mode) (absNames block_names) lfe
              ((absConstantInfos recs).drop i.val)).run lst
            = .ok ((lfe', absCheckedRecs q.2 |>.drop (absCheckedRecs out).length),
                lst')
          ∧ absCheckedRecs q.2 = absCheckedRecs out
              ++ (absCheckedRecs q.2).drop (absCheckedRecs out).length
          ∧ StateRel st' lst' ∧ FEnvRel q.1 lfe' ∧ StateWF st' ∧ FEnvWF q.1
          ∧ ((∀ c ∈ out.val, ConstantValWF c.1 ∧ RecRulesWF c.2.2.2) →
              ∀ c ∈ q.2.val, ConstantValWF c.1 ∧ RecRulesWF c.2.2.2)
      | .Err e =>
        ErrSim e ((ConLeche.Cached.provisionRecsS (absMode mode)
          (absNames block_names) lfe ((absConstantInfos recs).drop i.val)).run lst) := by
  generalize hd : recs.length - i.val = d
  induction d using Nat.strong_induction_on generalizing st fe_acc i out oq with
  | _ d ih =>
    intro lst lfe hrel hfer
    rw [inductives.inductives_c.provision_recs_s] at h
    split at h
    · rename_i hge
      simp only [Result.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have hnil : (absConstantInfos recs).drop i.val = [] := by
        apply List.drop_eq_nil_of_le
        simp only [absConstantInfos, List.length_map]
        have := alloc.vec.Vec.len_val recs; scalar_tac
      refine ⟨lst, lfe, ?_, by simp, hrel, hfer, hst, hfe, fun hout => hout⟩
      rw [hnil, ConLeche.Cached.provisionRecsS]
      simp [StateT.run, Pure.pure, StateT.pure, Except.pure]
    · rename_i hge
      obtain ⟨st1, hflush, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨hfrun, hrelf, hwff, _⟩ := StateC.flush_c_refines hrel hst hflush
      have hlt : i.val < recs.val.length := by
        have := alloc.vec.Vec.len_val recs; scalar_tac
      obtain ⟨y, hy, hyv⟩ :=
        WP.spec_imp_exists (alloc.vec.Vec.index_usize_spec recs i hlt)
      subst hyv
      simp only [alloc.vec.Vec.index_slice_index, hy, bind_tc_ok] at h
      have hciwf : ConstantInfoWF recs.val[i.val] := hrecs _ (List.getElem_mem hlt)
      have hlt2 : i.val < (absConstantInfos recs).length := by
        simpa [absConstantInfos] using hlt
      have hcons : (absConstantInfos recs).drop i.val
          = absConstantInfo recs.val[i.val]
            :: (absConstantInfos recs).drop (i.val + 1) := by
        rw [List.drop_eq_getElem_cons hlt2]; simp [absConstantInfos]
      obtain ⟨p, hp, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨r, st2⟩ := p
      cases r with
      | Err err =>
        -- the step threw: the cons arm throws it, past its own flush
        simp at h
        obtain ⟨rfl, rfl⟩ := h
        have hstep :=
          Modeled.provision_recs_step_refines hw (IndIngredients.checkerBaseSpec hw)
            hwff hfe hbn hciwf hp lst.flushed lfe hrelf hfer
        rw [hcons]
        exact hstep.trans fun le hle => provisionRecsS_cons_err hle
      | Ok q0 =>
        obtain ⟨fe1, cv, mi, rp, rules⟩ := q0
        obtain ⟨lst1, lfe1, hrun1, hrel1, hprel1, hwf1, hpwf1, hcvwf, hruleswf⟩ :=
          Modeled.provision_recs_step_refines hw (IndIngredients.checkerBaseSpec hw)
            hwff hfe hbn hciwf hp lst.flushed lfe hrelf hfer
        simp at h
        obtain ⟨out1, hout1, i4, hi4, h⟩ := h
        have hi4v : i4.val = i.val + 1 := HashMap.uscalar_add_eq hi4
        have hout1wf : (∀ c ∈ out.val, ConstantValWF c.1 ∧ RecRulesWF c.2.2.2) →
            ∀ c ∈ out1.val, ConstantValWF c.1 ∧ RecRulesWF c.2.2.2 := by
          intro hout c hc
          rw [vec_push_val hout1, List.mem_append] at hc
          rcases hc with hc | hc
          · exact hout c hc
          · simp only [List.mem_singleton] at hc
            subst hc
            exact ⟨hcvwf, hruleswf⟩
        have htail :=
          ih (recs.length - i4.val) (by scalar_tac) hwf1 hpwf1 h rfl lst1 lfe1
            hrel1 hprel1
        have hout1v : absCheckedRecs out1
            = absCheckedRecs out
              ++ [(absConstantVal cv, mi.val, rp.val, absRecRules rules)] := by
          rw [absCheckedRecs, vec_push_val hout1, List.map_append]
          rfl
        cases oq with
        | Err e =>
          -- the tail threw, and the step's success carries it to the whole arm
          rw [hi4v] at htail
          rw [hcons]
          exact htail.trans fun le hle => provisionRecsS_cons_tail_err hrun1 hle
        | Ok q =>
          obtain ⟨lst', lfe', hrunT, hdrop, hrel', hprel', hwf', hpwf', hqwf⟩ := htail
          rw [hi4v] at hrunT
          rw [hout1v] at hdrop hrunT
          simp only [List.length_append, List.length_cons, List.length_nil,
            Nat.zero_add] at hdrop hrunT
          have hkey : (absCheckedRecs q.2).drop (absCheckedRecs out).length
              = (absConstantVal cv, mi.val, rp.val, absRecRules rules)
                :: (absCheckedRecs q.2).drop ((absCheckedRecs out).length + 1) := by
            conv_lhs => rw [hdrop]
            rw [show (absCheckedRecs out).length
                = (absCheckedRecs out
                  ++ [(absConstantVal cv, mi.val, rp.val,
                      absRecRules rules)]).length - 1 by simp]
            simp
          refine ⟨lst', lfe', ?_, ?_, hrel', hprel', hwf', hpwf',
            fun hout => hqwf (hout1wf hout)⟩
          · rw [hcons, hkey]
            exact provisionRecsS_cons hrun1 hrunT
          · rw [hkey]
            conv_lhs => rw [hdrop]
            simp

/-- `ConLeche/Cached/CheckerC.lean:115-129` — `provision_recs_s` refines
`provisionRecsS`: **one flush per recursor** before its constant is checked,
then `provisionRecs`' step.  The port accumulates the checked recursors on the
way *in* where con-leche conses them on the way *out*, so the statement carries
the accumulator in front. -/
theorem provision_recs_s_refines
    {st st' : cached.state_c.CState} {block_names : alloc.vec.Vec name.Name}
    {fe_acc : fenv.FEnv} {recs : alloc.vec.Vec env.ConstantInfo} {i : Std.Usize}
    {out : alloc.vec.Vec (env.ConstantVal × Std.U64 × Std.U64
      × alloc.vec.Vec env.RecRule)}
    {oq : core.result.Result (fenv.FEnv × alloc.vec.Vec (env.ConstantVal × Std.U64
      × Std.U64 × alloc.vec.Vec env.RecRule)) core_types.CheckError}
    (hst : StateWF st) (hfe : FEnvWF fe_acc) (hbn : NamesWF block_names)
    (hrecs : ConstantInfosWF recs)
    (h : inductives.inductives_c.provision_recs_s mode st block_names fe_acc recs
        i out = ok (oq, st')) :
    ∀ lst lfe, StateRel st lst → FEnvRel fe_acc lfe →
      match oq with
      | .Ok q =>
        ∃ lst' lfe',
          (ConLeche.Cached.provisionRecsS (absMode mode) (absNames block_names) lfe
              ((absConstantInfos recs).drop i.val)).run lst
            = .ok ((lfe', absCheckedRecs q.2 |>.drop (absCheckedRecs out).length),
                lst')
          ∧ absCheckedRecs q.2 = absCheckedRecs out
              ++ (absCheckedRecs q.2).drop (absCheckedRecs out).length
          ∧ StateRel st' lst' ∧ FEnvRel q.1 lfe' ∧ StateWF st' ∧ FEnvWF q.1
      | .Err e =>
        ErrSim e ((ConLeche.Cached.provisionRecsS (absMode mode)
          (absNames block_names) lfe ((absConstantInfos recs).drop i.val)).run lst) := by
  -- the index recursion over `recs`, one flush plus `provision_recs_step` a step
  intro lst lfe hrel hfer
  have hv := provision_recs_s_val hw hst hfe hbn hrecs h lst lfe hrel hfer
  cases oq with
  | Err e => exact hv
  | Ok q =>
    obtain ⟨lst', lfe', a, b, c, d, e, f, _⟩ := hv
    exact ⟨lst', lfe', a, b, c, d, e, f⟩

/-- `ConLeche/Cached/CheckerC.lean:131-151` — `check_ind_recs_s` refines
`checkIndRecsS`: **all iota-rule checks run at `envSelf`** — one flush entering
the phase, none inside the fold — and the ruled recursors are installed on the
`env₂` snapshot of the index.  The two `fenv::dup`s are `FEnv.dup_refines`.

**`hcan` is not a weakening** (task #59): the phase copies the index
(`fenv::dup(fe2)`) and hands the copy to the recursors' operations, where
con-leche keeps passing its own persistent `fe₂`; carrying the caller's `lfe`
across that rebuild is `FEnv.dup_rel`, which asks for `FEnv.FEnvCanon fe2`, and
`Refine/FEnv.lean`'s note explains why `FEnvWF` cannot supply it.  Callers
discharge it from `FEnv.mk_fenv_canon`/`FEnv.dup_canon`/`FEnv.push_canon`. -/
theorem check_ind_recs_s_refines
    {st st' : cached.state_c.CState} {block_names : alloc.vec.Vec name.Name}
    {fe2 fe' : fenv.FEnv} {recs : alloc.vec.Vec env.ConstantInfo}
    (hst : StateWF st) (hfe : FEnvWF fe2) (hcan : FEnv.FEnvCanon fe2)
    (hfull : FEnv.FEnvFull fe2)
    (hbn : NamesWF block_names) (hrecs : ConstantInfosWF recs)
    (h : inductives.inductives_c.check_ind_recs_s mode st block_names fe2 recs
        = ok (.Ok fe', st')) :
    ∀ lst lfe, StateRel st lst → FEnvRel fe2 lfe →
      ∃ lst' lfe',
        (ConLeche.Cached.checkIndRecsS (absMode mode) (absNames block_names) lfe
            (absConstantInfos recs)).run lst = .ok (lfe', lst')
        ∧ StateRel st' lst' ∧ FEnvRel fe' lfe' ∧ StateWF st' ∧ FEnvWF fe'
        ∧ FEnv.FEnvCanon fe' ∧ FEnv.FEnvFull fe' := by
  -- the `eqA` pin guard, the two dups, `provision_recs_s`, the flush, the fold
  intro lst lfe hrel hfer
  rw [inductives.inductives_c.check_ind_recs_s] at h
  rw [checkIndRecsS_eq]
  have hlv := alloc.vec.Vec.len_val recs
  split at h
  · rename_i hz
    have hrv : recs.val = [] := by
      have : recs.val.length = 0 := by scalar_tac
      exact List.eq_nil_of_length_eq_zero this
    simp only [Result.ok.injEq, Prod.mk.injEq, core.result.Result.Ok.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rw [if_pos (by simp [absConstantInfos, hrv])]
    exact ⟨lst, lfe, by simp [StateT.run, Pure.pure, StateT.pure, Except.pure],
      hrel, hfer, hst, hfe, hcan, hfull⟩
  · rename_i hnz
    have hne : ¬ ((absConstantInfos recs).isEmpty = true) := by
      simp only [absConstantInfos, List.isEmpty_iff, List.map_eq_nil_iff]
      intro hrv
      apply hnz
      have : recs.val.length = 0 := by rw [hrv]; rfl
      scalar_tac
    rw [if_neg hne]
    obtain ⟨b, hb, h⟩ := bind_eq_ok_iff.mp h
    have hbv := BasisPins.eq_basis_pinned_refines hfer hfe hb
    split at h
    · rename_i hbt
      have hpin : lfe.find? ConLeche.eqName = some ConLeche.eqA := by
        rw [hbt] at hbv
        exact of_decide_eq_true hbv.symm
      obtain ⟨fe_env, hdup, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨hrele, hwfe, hcane⟩ := FEnv.dup_rel hfe hcan hfer hdup
      obtain ⟨pq, hprov, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨r, st1⟩ := pq
      cases r with
      | Err err => simp at h
      | Ok pq0 =>
        obtain ⟨fq, vq⟩ := pq0
        obtain ⟨lst1, lfe1, hrun1, hdropv, hrel1, hprel1, hwf1, hpwf1, hvqwf⟩ :=
          provision_recs_s_val hw hst hwfe hbn hrecs hprov lst lfe hrel hrele
        obtain ⟨st2, hflush, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨hfrun, hrel2, hwf2, _⟩ := StateC.flush_c_refines hrel1 hwf1 hflush
        have hchecked : ∀ c ∈ vq.val, ConstantValWF c.1 ∧ RecRulesWF c.2.2.2 :=
          hvqwf (by intro c hc; simp [alloc.vec.Vec.new] at hc)
        obtain ⟨lst', lfe', hrunT, hrel3, hfrel3, hwf3, hfwf3, hfcan3, hffull3⟩ :=
          Modeled.check_ind_recs_fold_refines hw (IndIngredients.checkerBaseSpec hw)
            IndIngredients.structInstallConstsResolveFFast
            IndIngredients.structSpinesRefine
            (Modeled.block_rename_rename_refines hbn) hwf2 hwfe hpwf1 hfe hcan hfull
            hchecked h lst1.flushed lfe lfe1 lfe hrel2 hrele hprel1 hfer
        refine ⟨lst', lfe', ?_, hrel3, hfrel3, hwf3, hfwf3, hfcan3, hffull3⟩
        rw [if_pos hpin]
        simp only [alloc.vec.Vec.new, show ((0#usize : Std.Usize).val) = 0 from rfl,
          List.drop_zero, absCheckedRecs, Modeled.absCheckedRecs] at hrun1 hrunT
        simp only [StateT.run_bind, hrun1, NativeInstall.exceptOk_bind, StateC.flushC_run]
        exact hrunT
    · rename_i hbf
      obtain ⟨s, hs, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨v0, hv0, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨ce, hce, h⟩ := bind_eq_ok_iff.mp h
      simp at h

/-- `ConLeche/Cached/CheckerC.lean:168-175` — `install_proj_fn_step_s` refines
`installProjFnStepS`: **one flush** before the projection's own checks, and
nothing at all where the model's projection artifact is absent. -/
theorem install_proj_fn_step_s_refines
    {st st' : cached.state_c.CState} {t ctor_name : name.Name}
    {lps : alloc.vec.Vec name.Name} {n_p n_f i : Std.U64} {fe fe' : fenv.FEnv}
    (hst : StateWF st) (hfe : FEnvWF fe) (hcan : FEnv.FEnvCanon fe)
    (hfull : FEnv.FEnvFull fe) (ht : NameWF t) (hc : NameWF ctor_name)
    (hlps : NamesWF lps)
    (h : inductives.inductives_c.install_proj_fn_step_s mode st t ctor_name lps
        n_p n_f fe i = ok (.Ok fe', st')) :
    ∀ lst lfe, StateRel st lst → FEnvRel fe lfe →
      ∃ lst' lfe',
        (ConLeche.Cached.installProjFnStepS (absMode mode) (absName t)
            (absName ctor_name) (absNames lps) n_p.val n_f.val lfe i.val).run lst
          = .ok (lfe', lst')
        ∧ StateRel st' lst' ∧ FEnvRel fe' lfe' ∧ StateWF st' ∧ FEnvWF fe'
        ∧ FEnv.FEnvCanon fe' ∧ FEnv.FEnvFull fe' := by
  -- `CoreK.proj_model_name_refines` and `FEnv.find_refines` for the artifact
  -- probe, then the flush and `IndModeled`'s `check_proj_fn` stage
  intro lst lfe hrel hfer
  rw [inductives.inductives_c.install_proj_fn_step_s] at h
  obtain ⟨n, hn, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨hnabs, hnwf⟩ := CoreK.proj_model_name_refines ht hn
  obtain ⟨o, ho, h⟩ := bind_eq_ok_iff.mp h
  have hoabs : o.map absConstantInfo
      = lfe.find? (ConLeche.projModelName (absName t) i.val) := by
    rw [← hnabs]; exact FEnv.find_refines hfer hfe hnwf ho
  have hsome : (core.option.Option.is_some o)
      = (lfe.find? (ConLeche.projModelName (absName t) i.val)).isSome := by
    rw [← hoabs]; cases o <;> rfl
  rw [ConLeche.Cached.installProjFnStepS]
  -- the `let b := …` Aeneas emits for the `is_some` test is not a monadic bind,
  -- so it goes by ascription (task #16's hard spot 1) before `split` can fire
  replace h : (if (core.option.Option.is_some o) = true then
        (do
          let st1 ← cached.state_c.flush_c st
          inductives.modeled.check_proj_fn mode st1 fe t ctor_name lps n_p n_f i)
      else ok (.Ok fe, st))
      = (ok (.Ok fe', st') : Result ((core.result.Result _ core_types.CheckError)
          × cached.state_c.CState)) := h
  split at h
  · rename_i hb
    rw [if_pos (by rw [← hsome]; exact hb)]
    obtain ⟨st1, hflush, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨hfrun, hrel1, hwf1, _⟩ := StateC.flush_c_refines hrel hst hflush
    obtain ⟨lst', lfe', hrun, hrel2, hfrel2, hwf2, hfwf2, hfcan2, hffull2⟩ :=
      Modeled.check_proj_fn_refines hw (IndIngredients.checkerBaseSpec hw)
        IndIngredients.structInstallConstsResolveFFast
        IndIngredients.structSpinesRefine hwf1 hfe hcan hfull ht hc hlps h
        lst.flushed lfe hrel1 hfer
    refine ⟨lst', lfe', ?_, hrel2, hfrel2, hwf2, hfwf2, hfcan2, hffull2⟩
    simp only [StateT.run_bind, StateC.flushC_run, NativeInstall.exceptOk_bind]
    exact hrun
  · rename_i hb
    rw [if_neg (by rw [← hsome]; exact hb)]
    simp only [Result.ok.injEq, Prod.mk.injEq, core.result.Result.Ok.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨lst, lfe, rfl, hrel, hfer, hst, hfe, hcan, hfull⟩

/-- `ConLeche/Cached/CheckerC.lean:233-268` — `install_proj_fns_s` refines
`(List.range nF).foldlM (installProjFnStepS …) fe₃`, as an index recursion. -/
theorem install_proj_fns_s_refines
    {st st' : cached.state_c.CState} {t ctor_name : name.Name}
    {lps : alloc.vec.Vec name.Name} {n_p n_f i : Std.U64} {fe fe' : fenv.FEnv}
    (hst : StateWF st) (hfe : FEnvWF fe) (hcan : FEnv.FEnvCanon fe)
    (hfull : FEnv.FEnvFull fe) (ht : NameWF t) (hc : NameWF ctor_name)
    (hlps : NamesWF lps)
    (h : inductives.inductives_c.install_proj_fns_s mode st t ctor_name lps n_p
        n_f fe i = ok (.Ok fe', st')) :
    ∀ lst lfe, StateRel st lst → FEnvRel fe lfe →
      ∃ lst' lfe',
        ((List.range' i.val (n_f.val - i.val)).foldlM
            (ConLeche.Cached.installProjFnStepS (absMode mode) (absName t)
              (absName ctor_name) (absNames lps) n_p.val n_f.val) lfe).run lst
          = .ok (lfe', lst')
        ∧ StateRel st' lst' ∧ FEnvRel fe' lfe' ∧ StateWF st' ∧ FEnvWF fe'
        ∧ FEnv.FEnvCanon fe' ∧ FEnv.FEnvFull fe' := by
  generalize hd : n_f.val - i.val = d
  induction d using Nat.strong_induction_on generalizing st fe i with
  | _ d ih =>
    intro lst lfe hrel hfer
    rw [inductives.inductives_c.install_proj_fns_s] at h
    split at h
    · rename_i hge
      have hz : d = 0 := by rw [← hd]; scalar_tac
      subst hz
      simp only [Result.ok.injEq, Prod.mk.injEq, core.result.Result.Ok.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨lst, lfe, by
        simp only [List.range'_zero, List.foldlM_nil, StateT.run, Pure.pure,
          StateT.pure]
        rfl, hrel, hfer, hst, hfe, hcan, hfull⟩
    · rename_i hlt
      obtain ⟨p, hstep, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨r, st1⟩ := p
      cases r with
      | Err e => simp at h
      | Ok fe2 =>
        obtain ⟨i1, hi1, h⟩ := by simpa using bind_eq_ok_iff.mp (by simpa using h)
        have hi1v : i1.val = i.val + 1 := HashMap.uscalar_add_eq hi1
        obtain ⟨lst1, lfe1, hrun1, hrel1, hfer1, hwf1, hfew1, hfcan1, hffull1⟩ :=
          install_proj_fn_step_s_refines hw hst hfe hcan hfull ht hc hlps hstep lst
            lfe hrel hfer
        have hsplit : d = (n_f.val - i1.val) + 1 := by rw [← hd]; scalar_tac
        subst hsplit
        obtain ⟨lst', lfe', hrunr, hrelr, hferr, hwfr, hfewr, hfcanr, hffullr⟩ :=
          ih (n_f.val - i1.val) (by omega) hwf1 hfew1 hfcan1 hffull1 h rfl lst1 lfe1
            hrel1 hfer1
        refine ⟨lst', lfe', ?_, hrelr, hferr, hwfr, hfewr, hfcanr, hffullr⟩
        rw [List.range'_succ, List.foldlM_cons, ← hi1v]
        simp only [StateT.run, Bind.bind, StateT.bind, Except.bind] at hrun1 hrunr ⊢
        rw [hrun1]
        exact hrunr

/-- `ConLeche/Cached/CheckerC.lean:233-268` — `check_ind_decl_struct_s` refines
the single-type-former, single-constructor arm of `checkIndDeclSF`: the
capability record, the members, the recursors, the eta constructor residual,
the projection name family's freshness and — at a structure-like block — the
projection functions.

`hcan`/`hfull` reach `check_ind_recs_s_refines` through the members' fold
(`check_ind_members_s_canon`): the recursor phase copies the index it is
handed, so the canonical pair has to travel with it.  See
`check_ind_recs_s_refines`' note.

Task #59 carried an `hnp : n_p.val ≤ Std.Usize.max` here, arriving through
`Modeled.ind_block_caps_refines` from `check_eta_thm_shape` /
`check_unit_thm_shape`'s `n_p as usize`.  Task #62's sweep replaced those
casts with `expr_ops::dom_at_n`, which counts the `u64` down a `usize`
cursor, so the bound is gone from every statement in the chain — and with it
the one `sorry` `check_ind_decl_s_refines` could not discharge. -/
theorem check_ind_decl_struct_s_refines
    {st st' : cached.state_c.CState} {fe fe' : fenv.FEnv}
    {block_names : alloc.vec.Vec name.Name}
    {nonrecs recs : alloc.vec.Vec env.ConstantInfo}
    {cv_t cv_c : env.ConstantVal} {n_p n_f : Std.U64}
    (hst : StateWF st) (hfe : FEnvWF fe) (hcan : FEnv.FEnvCanon fe)
    (hfull : FEnv.FEnvFull fe) (hbn : NamesWF block_names)
    (hnr : ConstantInfosWF nonrecs) (hrecs : ConstantInfosWF recs)
    (hct : ConstantValWF cv_t) (hcc : ConstantValWF cv_c)
    (h : inductives.inductives_c.check_ind_decl_struct_s mode st fe block_names
        nonrecs recs cv_t cv_c n_p n_f = ok (.Ok fe', st')) :
    ∀ lst lfe, StateRel st lst → FEnvRel fe lfe →
      ∃ lst' lfe',
        (checkIndDeclStructS (absMode mode) lfe (absNames block_names)
            (absConstantInfos nonrecs) (absConstantInfos recs)
            (absConstantVal cv_t) (absConstantVal cv_c) n_p.val n_f.val).run lst
          = .ok (lfe', lst')
        ∧ StateRel st' lst' ∧ FEnvRel fe' lfe' ∧ StateWF st' ∧ FEnvWF fe'
        ∧ FEnv.FEnvCanon fe' ∧ FEnv.FEnvFull fe' := by
  -- `ind_block_caps`, the two folds above, `ctor_residual_ok`,
  -- `StructInstall.proj_fn_family_free_refines`, `ctor_targets_fam`
  intro lst lfe hrel hfer
  rw [inductives.inductives_c.check_ind_decl_struct_s] at h
  obtain ⟨caps, hcaps, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨hcapsabs, hcapswf⟩ :=
    Modeled.ind_block_caps_refines (IndIngredients.checkerBaseSpec hw)
      IndIngredients.structSpinesRefine hfer hfe hct hcc hcaps
  obtain ⟨p1, hmem, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨r, st1⟩ := p1
  cases r with
  | Err e => simp at h
  | Ok fe2 =>
    obtain ⟨lst1, lfe2, hrun1, hrel1, hfer1, hwf1, hfew1⟩ :=
      check_ind_members_s_refines hw hst hfe hbn hcapswf hnr hmem lst lfe hrel hfer
    obtain ⟨hcan2, hfull2⟩ :=
      check_ind_members_s_canon hw hst hfe hbn hcapswf hnr hcan hfull hmem lst lfe
        hrel hfer
    obtain ⟨p2, hrecp, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨r1, st2⟩ := p2
    cases r1 with
    | Err e => simp at h
    | Ok fe3 =>
      obtain ⟨lst2, lfe3, hrun2, hrel2, hfer2, hwf2, hfew2, hfcan2, hffull2⟩ :=
        check_ind_recs_s_refines hw hwf1 hfew1 hcan2 hfull2 hbn hrecs hrecp lst1
          lfe2 hrel1 hfer1
      obtain ⟨b, hb, h⟩ := bind_eq_ok_iff.mp h
      have hbv := Modeled.ctor_residual_ok_refines IndIngredients.structFamRefines
        hfer2 hfew2 hct.1 hcc.1 hct.2.1 hb
      simp only [show ((0#usize : Std.Usize).val) = 0 from rfl, List.drop_zero,
        hcapsabs] at hrun1
      have hetav : (ConLeche.indBlockCapsF (absMode mode) lfe
          (absConstantVal cv_t) (absConstantVal cv_c) n_p.val n_f.val).eta
          = caps.eta := by rw [← hcapsabs]; rfl
      rw [checkIndDeclStructS]
      simp only [pure_bind, StateT.run_bind, hrun1, NativeInstall.exceptOk_bind, hrun2, hetav]
      simp only [absConstantVal]
      split at h
      · rename_i hbt
        rw [if_pos (show (ConLeche.ctorResidualOkF (absMode mode) lfe3
            (absName cv_t.name) (absName cv_c.name)
            (absNames cv_t.level_params) n_p.val n_f.val caps.eta) = true from by
          rw [← hbv]; exact hbt)]
        obtain ⟨b1, hb1, h⟩ := bind_eq_ok_iff.mp h
        have hb1v := StructInstall.proj_fn_family_free_from_refines hfer2 hfew2
          hct.1 hb1
        rw [show ((0#u64 : Std.U64)).val = 0 from rfl, Nat.sub_zero,
          ← List.range_eq_range'] at hb1v
        split at h
        · rename_i hb1t
          rw [if_pos (show ((List.range n_f.val).all
              (fun j => (lfe3.find? (ConLeche.projFnName
                (absName cv_t.name) j)).isNone)) = true from by
            rw [← hb1v]; exact hb1t)]
          obtain ⟨b2, hb2, h⟩ := bind_eq_ok_iff.mp h
          have hb2v := Modeled.ctor_targets_fam_refines
            IndIngredients.structFamRefines hcc.2.2 hct.1 hct.2.1 hb2
          split at h
          · rename_i hb2t
            rw [if_pos (show ConLeche.ctorTargetsFam
                (absExpr cv_c.ty) (absName cv_t.name)
                (absNames cv_t.level_params) n_p.val n_f.val = true from by
              rw [← hb2v]; exact hb2t)]
            obtain ⟨lst', lfe', hrun3, hrel3, hfer3, hwf3, hfew3, hfcan3, hffull3⟩ :=
              install_proj_fns_s_refines hw hwf2 hfew2 hfcan2 hffull2 hct.1 hcc.1
                hct.2.1 h lst2 lfe3 hrel2 hfer2
            rw [show ((0#u64 : Std.U64)).val = 0 from rfl, Nat.sub_zero,
              ← List.range_eq_range'] at hrun3
            exact ⟨lst', lfe', hrun3, hrel3, hfer3, hwf3, hfew3, hfcan3, hffull3⟩
          · rename_i hb2f
            simp only [Bool.not_eq_true] at hb2f
            rw [if_neg (show ¬ (ConLeche.ctorTargetsFam
                (absExpr cv_c.ty) (absName cv_t.name)
                (absNames cv_t.level_params) n_p.val n_f.val = true) from by
              rw [← hb2v, hb2f]; simp)]
            simp only [Result.ok.injEq, Prod.mk.injEq,
              core.result.Result.Ok.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            exact ⟨lst2, lfe3, rfl, hrel2, hfer2, hwf2, hfew2, hfcan2, hffull2⟩
        · rename_i hb1f
          obtain ⟨s, hs, h⟩ := bind_eq_ok_iff.mp h
          obtain ⟨v0, hv0, h⟩ := bind_eq_ok_iff.mp h
          obtain ⟨ce, hce, h⟩ := bind_eq_ok_iff.mp h
          simp at h
      · rename_i hbf
        obtain ⟨s, hs, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨v0, hv0, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨ce, hce, h⟩ := bind_eq_ok_iff.mp h
        simp at h

/-- `ConLeche/Cached/CheckerC.lean:233-268` — **`check_ind_decl_s` refines
`checkIndDeclSF`**: the modeled inductive block, returning the extended index.
One of the two entry points `checker.rs`'s `.indDecl` arm calls.

**`hcan`/`hfull` are not a weakening**: both arms this dispatches to — the
struct arm and the pair `check_ind_members_s`/`check_ind_recs_s` — reach a
`fenv::dup`, where `FEnv.dup_rel` is the only bridge that keeps the caller's
own `lfe`.  `Refine/IndSpec.lean`'s header spells out why the clause is false
without the pair, and `IndRoutesSpecP.checkIndDecl` carries it. -/
theorem check_ind_decl_s_refines
    {st st' : cached.state_c.CState} {fe fe' : fenv.FEnv}
    {block : alloc.vec.Vec env.ConstantInfo}
    (hst : StateWF st) (hfe : FEnvWF fe) (hcan : FEnv.FEnvCanon fe)
    (hfull : FEnv.FEnvFull fe) (hblock : ConstantInfosWF block)
    (h : inductives.inductives_c.check_ind_decl_s mode st fe block
        = ok (.Ok fe', st')) :
    ∀ lst lfe, StateRel st lst → FEnvRel fe lfe →
      ∃ lst' lfe',
        (ConLeche.Cached.checkIndDeclSF (absMode mode) lfe
            (absConstantInfos block)).run lst = .ok (lfe', lst')
        ∧ StateRel st' lst' ∧ FEnvRel fe' lfe' ∧ StateWF st' ∧ FEnvWF fe'
        ∧ FEnv.FEnvCanon fe' ∧ FEnv.FEnvFull fe' := by
  -- `filter_recs`, `Env.block_rec_suffix_ok_refines`, `block_names_of`,
  -- `single_ind_ctor`, then the struct arm above or the general one.
  --
  -- The cited code's `match` and this file's spelling of the same filters
  -- elaborate to *different* auxiliary matchers, so nothing below rewrites
  -- across the seam: each arm is finished with `exact`, which closes the gap
  -- by `whnf` (matchers and `η` are definitional).
  intro lst lfe hrel hfer
  rw [inductives.inductives_c.check_ind_decl_s] at h
  obtain ⟨recs, hrecs, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨hrecsabs, hrecswf⟩ := Modeled.filter_recs_refines hblock hrecs
  obtain ⟨nonrecs, hnonrecs, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨hnrabs, hnrwf⟩ := Modeled.filter_recs_refines hblock hnonrecs
  have hpos : (fun ci : ConLeche.ConstantInfo => ci.isRecInfo == true)
      = ConLeche.ConstantInfo.isRecInfo := by funext ci; cases ci <;> rfl
  have hneg : (fun ci : ConLeche.ConstantInfo => ci.isRecInfo == false)
      = (fun ci : ConLeche.ConstantInfo => !ci.isRecInfo) := by
    funext ci; cases ci <;> rfl
  have hrecsabs' : absConstantInfos recs
      = (absConstantInfos block).filter ConLeche.ConstantInfo.isRecInfo := by
    rw [hrecsabs, hpos]
  have hnrabs' : absConstantInfos nonrecs
      = (absConstantInfos block).filter (fun ci : ConLeche.ConstantInfo =>
          !ci.isRecInfo) := by
    rw [hnrabs, hneg]
  -- con-leche writes the two filters as `match`es and the block names with
  -- `(·.name)`; `recsFilterPos`/`recsFilterNeg` are its own bridge to the tag,
  -- and they carry *its* auxiliary matchers, which is what makes the rewrites
  -- below land on the cited term
  rw [← ConLeche.recsFilterPos] at hrecsabs'
  rw [← ConLeche.recsFilterNeg] at hnrabs'
  have hmapeta : ConLeche.ConstantInfo.name
      = (fun x : ConLeche.ConstantInfo => x.name) := rfl
  obtain ⟨bo, hbo, h⟩ := bind_eq_ok_iff.mp h
  have hbov := Env.block_rec_suffix_ok_refines hbo
  rw [ConLeche.Cached.checkIndDeclSF]
  simp only [blockRecSuffix_decide, throwC_bind, pure_bind]
  split at h
  · rename_i hbt
    rw [if_pos (show ConLeche.recsFormSuffix (absConstantInfos block) = true from by
      rw [← hbov]; exact hbt)]
    obtain ⟨bn, hbn, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨hbnabs, hbnwf⟩ := Modeled.block_names_of_refines hblock hbn
    rw [hmapeta] at hbnabs
    obtain ⟨o, ho, h⟩ := bind_eq_ok_iff.mp h
    have hsic := Modeled.single_ind_ctor_refines hblock ho
    have hsicwf := single_ind_ctor_wf hblock ho
    split
    · -- the cited single-type-former, single-constructor arm
      rename_i cvT caps cvC nP nF heq1 heq2
      cases o with
      | none =>
        exfalso
        split at hsic
        · rename_i cvT' caps' cvC' nP' nF' heq1' heq2'
          replace hsic : (none : Option (ConLeche.ConstantVal
              × ConLeche.ConstantVal × Nat × Nat))
              = some (cvT', cvC', nP', nF') := hsic
          simp at hsic
        · rename_i hne'
          exact hne' cvT caps cvC nP nF heq1 heq2
      | some sq =>
        obtain ⟨hct, hcc⟩ := hsicwf sq rfl
        split at hsic
        · rename_i cvT' caps' cvC' nP' nF' heq1' heq2'
          injection heq1.symm.trans heq1' with e1 _
          injection e1 with hcvT _
          injection heq2.symm.trans heq2' with e2 _
          injection e2 with hcvC hnP hnF
          subst hcvT; subst hcvC; subst hnP; subst hnF
          replace hsic : (some (absConstantVal sq.1, absConstantVal sq.2.1,
              sq.2.2.1.val, sq.2.2.2.val) : Option (ConLeche.ConstantVal
                × ConLeche.ConstantVal × Nat × Nat))
              = some (cvT, cvC, nP, nF) := hsic
          simp only [Option.some.injEq, Prod.mk.injEq] at hsic
          obtain ⟨hT, hC, hp, hf⟩ := hsic
          -- Task #59's one open bound, gone at task #62: the arm used to owe
          -- `check_ind_decl_struct_s_refines` an `n_p ≤ Usize.max` it could not
          -- produce -- `n_p` is `sq.2.2.1`, a count `single_ind_ctor` read off
          -- a `.CtorInfo` buried in `block`, and nothing in
          -- `ConstantInfosWF block` bounds a stored count.  The port no longer
          -- asks: `check_eta_thm_shape` / `check_unit_thm_shape` read the
          -- subject binder with `expr_ops::dom_at_n`, a counting recursion, so
          -- the hypothesis is off the whole chain.
          obtain ⟨lst', lfe', hrun, hrel', hfer', hwf', hfew', hfcan', hffull'⟩ :=
            check_ind_decl_struct_s_refines hw hst hfe hcan hfull hbnwf hnrwf
              hrecswf hct hcc h lst lfe hrel hfer
          refine ⟨lst', lfe', ?_, hrel', hfer', hwf', hfew', hfcan', hffull'⟩
          rw [hbnabs, hnrabs', hrecsabs', hT, hC, hp, hf] at hrun
          exact hrun
        · rename_i hne'
          exact (hne' cvT caps cvC nP nF heq1 heq2).elim
    · -- the cited general arm
      rename_i hne
      have ho' : o = none := by
        cases o with
        | none => rfl
        | some sq =>
          exfalso
          split at hsic
          · rename_i cvT' caps' cvC' nP' nF' heq1' heq2'
            exact hne cvT' caps' cvC' nP' nF' heq1' heq2'
          · replace hsic : (some (absConstantVal sq.1, absConstantVal sq.2.1,
                sq.2.2.1.val, sq.2.2.2.val) : Option (ConLeche.ConstantVal
                  × ConLeche.ConstantVal × Nat × Nat)) = none := hsic
            simp at hsic
      subst ho'
      obtain ⟨caps, hcapsd, h⟩ := bind_eq_ok_iff.mp h
      have hcapsabs := Env.ind_caps_default_refines hcapsd
      have hcapswf := Env.ind_caps_default_wf hcapsd
      obtain ⟨p1, hmem, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨r, st1⟩ := p1
      cases r with
      | Err e => simp at h
      | Ok fe2 =>
        obtain ⟨lst1, lfe2, hrun1, hrel1, hfer1, hwf1, hfew1⟩ :=
          check_ind_members_s_refines hw hst hfe hbnwf hcapswf hnrwf hmem lst lfe
            hrel hfer
        obtain ⟨hcan2, hfull2⟩ :=
          check_ind_members_s_canon hw hst hfe hbnwf hcapswf hnrwf hcan hfull hmem
            lst lfe hrel hfer
        obtain ⟨lst', lfe', hrun2, hrel2, hfer2, hwf2, hfew2, hfcan2, hffull2⟩ :=
          check_ind_recs_s_refines hw hwf1 hfew1 hcan2 hfull2 hbnwf hrecswf h lst1
            lfe2 hrel1 hfer1
        refine ⟨lst', lfe', ?_, hrel2, hfer2, hwf2, hfew2, hfcan2, hffull2⟩
        rw [show ((0#usize : Std.Usize).val) = 0 from rfl, List.drop_zero,
          hcapsabs, hbnabs, hnrabs'] at hrun1
        rw [hbnabs, hrecsabs'] at hrun2
        exact runBind_compose hrun1 hrun2
  · rename_i hbf
    obtain ⟨s, hs, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨v0, hv0, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨ce, hce, h⟩ := bind_eq_ok_iff.mp h
    simp at h

/-! ## The direct route -/

/-- `ConLeche/Cached/CheckerC.lean:177-190` — `check_native_pass_s` refines
`checkNativePassS`: **one flush per environment transition**, between the
former's stage and the constructors'.  `native_install`'s split into
`check_native_pass_former` and `check_native_pass_ctors` puts it exactly
there, so no memo policy differs from the cited code (DESIGN.md §3.1).

**`hcan`/`hfull` are not a weakening** (task #59).  The pass's own former
stage copies the *caller's* index (`native_install::check_native_pass_former`
opens with `fenv::dup(fe)`), and `FEnv.dup_rel` — the only way to carry the
caller's own `lfe` across a rebuild — asks for `FEnv.FEnvCanon fe`;
`FEnv.FEnvFull fe` is what `FEnv.push_canon` needs to keep the pair through
`check_sum_ind`'s push.  `Refine/FEnv.lean`'s own note explains why the
statement is false without them: `FEnvRel` pins `lfe.idx` only on the image of
the well-formed names, so an `lfe` disagreeing with its own environment is
related to `fe` and not to the rebuild.  Every `FEnv` the checker holds has the
pair (`mk_fenv_canon`/`dup_canon` establish it, `push_canon` preserves it), so
it is discharged at the call site — see `check_native_s_refines`' note. -/
theorem check_native_pass_s_refines
    {st st' : cached.state_c.CState} {fe : fenv.FEnv}
    {p0 : inductives.native_parts.NativeParts} {is_rec : Bool}
    {q : inductives.native_install.NativePass × Bool}
    (hst : StateWF st) (hfe : FEnvWF fe) (hcan : FEnv.FEnvCanon fe)
    (hfull : FEnv.FEnvFull fe) (hp0 : IndAbs.NativePartsWF p0)
    (h : inductives.inductives_c.check_native_pass_s mode st fe p0 is_rec
        = ok (.Ok q, st')) :
    ∀ lst lfe, StateRel st lst → FEnvRel fe lfe →
      ∃ lst' lq,
        (ConLeche.Cached.checkNativePassS (absMode mode) lfe
            (IndAbs.absNativeParts p0) is_rec).run lst = .ok ((lq, q.2), lst')
        ∧ StateRel st' lst' ∧ IndAbs.NativePassRel q.1 lq
        ∧ StateWF st' ∧ IndAbs.NativePassWF q.1
        ∧ FEnv.FEnvCanon q.1.env1 ∧ FEnv.FEnvFull q.1.env1 := by
  -- `check_native_pass_former`, `flush_c_refines`, `check_native_pass_ctors`
  intro lst lfe hrel hfer
  rw [inductives.inductives_c.check_native_pass_s] at h
  obtain ⟨pq, hformer, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨res, st1⟩ := pq
  cases res with
  | Err err => simp at h
  | Ok r =>
    obtain ⟨lst1, lfe1, hrun1, hrel1, hfrel1, hwf1, hfwf1, hcvwf, hiswf, hcwf,
        hrcan, hrfull⟩ :=
      NativeInstall.check_native_pass_former_refines
        (IndIngredients.checkSumIndRefines hw) (IndIngredients.checkSumIndErr hw)
        IndIngredients.checkSumIndCanon
        hst hfe hcan hfull hp0 hformer lst lfe hrel hfer
    obtain ⟨st2, hflush, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨hfrun, hrel2, hwf2, _⟩ := StateC.flush_c_refines hrel1 hwf1 hflush
    obtain ⟨lst', lq, hrun2, hrel3, hqrel, hwf3, hqwf, hqenv⟩ :=
      NativeInstall.check_native_pass_ctors_refines
        (IndIngredients.checkSumCtorsRefines hw) (IndIngredients.checkSumCtorsErr hw)
        IndIngredients.completeRefines
        IndIngredients.withKindsRefines IndIngredients.recCtorKindsRefines
        IndIngredients.recFieldKindBeqRefines hwf2 hfwf1 hcvwf hiswf hp0 hcwf h
        lst1.flushed lfe1 hrel2 hfrel1
    refine ⟨lst', lq, ?_, hrel3, hqrel, hwf3, hqwf, ?_, ?_⟩
    · rw [NativeInstall.checkNativePassS_eq]
      simp only [StateT.run_bind, hrun1, StateC.flushC_run, NativeInstall.exceptOk_bind]
      exact hrun2
    · rw [hqenv]; exact hrcan
    · rw [hqenv]; exact hrfull

/-- `ConLeche/Cached/CheckerC.lean:192-215` — `check_native_tail_s` refines
`checkNativeTailS`: **one flush entering the recursor's environment**, after
`consSumCtorsF` and before `checkNativeRecF`, which is where
`native_install`'s three-way split puts it.

`hcan`/`hfull` are the pass's index's, carried through `consSumCtorsF` by
`cons_sum_ctors_canon` above: the recursor stage copies the consed index with
`fenv::dup`.  `check_native_pass_s_refines` hands them over, so the driver
never asks for more than it can supply. -/
theorem check_native_tail_s_refines
    {st st' : cached.state_c.CState} {fe fe' : fenv.FEnv}
    {q : inductives.native_install.NativePass}
    (hst : StateWF st) (hfe : FEnvWF fe) (hq : IndAbs.NativePassWF q)
    (hcan : FEnv.FEnvCanon q.env1) (hfull : FEnv.FEnvFull q.env1)
    (h : inductives.inductives_c.check_native_tail_s mode st fe q
        = ok (.Ok fe', st')) :
    ∀ lst lfe lq, StateRel st lst → FEnvRel fe lfe →
      IndAbs.NativePassRel q lq →
      ∃ lst' lfe',
        (ConLeche.Cached.checkNativeTailS (absMode mode) lfe lq).run lst
          = .ok (lfe', lst')
        ∧ StateRel st' lst' ∧ FEnvRel fe' lfe' ∧ StateWF st' ∧ FEnvWF fe'
        ∧ FEnv.FEnvCanon fe' ∧ FEnv.FEnvFull fe' := by
  -- `check_native_tail_guards`, `check_native_cons`, `flush_c_refines`,
  -- `check_native_install`
  intro lst lfe lq hrel hfer hqrel
  rw [inductives.inductives_c.check_native_tail_s] at h
  obtain ⟨pq, hguards, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨res, st1⟩ := pq
  cases res with
  | Err err => simp at h
  | Ok u =>
    cases u
    obtain ⟨lst1, hrun1, hrel1, hwf1, hkf⟩ :=
      NativeInstall.check_native_tail_guards_refines hw
        IndIngredients.structInstallConstsResolveFFast
        IndIngredients.nativeInstallParamsOf IndIngredients.piBindersRefines
        IndIngredients.nativeInstallOpenPisAtFvarsF IndIngredients.kindGetDRefines
        IndIngredients.nativeRulesOkRefines
        (IndIngredients.checkStructFieldSortsIRefines hw)
        (IndIngredients.checkStructFieldSortsIErr hw) hst hfe hq hguards lst
        lfe lq hrel hfer hqrel
    obtain ⟨cq, hcq, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨hcrel, hcp, hccv, hcctors, hcss, hcwf, hcpwf, hccvwf, hcawf, hsswf⟩ :=
      NativeInstall.check_native_cons_refines IndIngredients.consSumCtorsRefines hq
        hcq lq hqrel
    -- `check_native_cons` only takes the pass apart, so the consed record's
    -- components are the pass's; that is what carries the guards' `KindsFitCtors`
    -- and `cons_sum_ctors_canon`'s pair to the install stage
    have hcq0 := hcq
    rw [inductives.native_install.check_native_cons] at hcq0
    obtain ⟨fe2, hcs, hcq1⟩ := bind_eq_ok_iff.mp hcq0
    have hcqv : cq = (fe2, q.p, q.cv_ta, q.ctors_a, q.sortss) :=
      (Result.ok_injective hcq1).symm
    have hconscan : FEnv.FEnvCanon cq.1 ∧ FEnv.FEnvFull cq.1 := by
      rw [hcqv]
      exact NativeInstall.cons_sum_ctors_canon hq.2.2.2.1 q.ctors_a.val.length 0#usize q.env1 fe2
        lq.env₁ (by simp) hq.1 hqrel.1 hcan hfull hcs
    have hkf' : NativeInstall.KindsFitCtors cq.2.2.2.1 cq.2.1.kinds := by
      rw [hcqv]; exact hkf
    obtain ⟨st2, hflush, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨hfrun, hrel2, hwf2, _⟩ := StateC.flush_c_refines hrel1 hwf1 hflush
    obtain ⟨lst', lfe2, hrun2, hrel3, hfrel3, hwf3, hfwf3, hfcan3, hffull3⟩ :=
      NativeInstall.check_native_install_refines hw
        IndIngredients.structInstallConstsResolveFFast
        IndIngredients.structRecRhsRRefines IndIngredients.structRecTyRRefines
        IndIngredients.nativeCtors4Refines IndIngredients.nativeRecLpsOkRefines
        (IndIngredients.nativeInstallCheckConstantVal hw)
        (IndIngredients.nativeInstallCheckConstantValErr hw)
        IndIngredients.nativeInstallParamsOf IndIngredients.sumRulesRefines
        IndIngredients.structProjBodiesRefines
        IndIngredients.structProjGuardsRefines hwf2 hcwf hconscan.1 hconscan.2
        hcpwf hccvwf hcawf hkf' hsswf h lst1.flushed
        (ConLeche.consSumCtorsF lq.p.nP lq.ctorsA lq.env₁) hrel2 hcrel
    refine ⟨lst', lfe2, ?_, hrel3, hfrel3, hwf3, hfwf3, hfcan3, hffull3⟩
    rw [NativeInstall.checkNativeTailS_eq]
    rw [hcp, hccv, hcctors, hcss] at hrun2
    simp only [StateT.run_bind, hrun1, StateC.flushC_run, NativeInstall.exceptOk_bind]
    exact hrun2

/-- `ConLeche/Cached/CheckerC.lean:217-231` — **`check_native_s` at a
`checkNativeS`**: the distinct constructor names, one flush, the pass at the
syntactic `is_rec` reading, again at the classified verdict where the reading
overshot, and the install after it.  The other entry point `checker.rs`'s
`.indDecl` arm calls.

**`hcan`/`hfull` are not a weakening.**
`native_install::check_native_pass_former` opens with `fenv::dup(fe)` — a
*rebuild* of the caller's index — so carrying the caller's own `lfe` across it
is `FEnv.dup_rel`, which asks for `FEnv.FEnvCanon fe`, and `FEnv.push_canon`
(through `check_sum_ind`) asks for `FEnv.FEnvFull fe`.  The pair is not
derivable from `FEnvWF`, which says nothing tying the index to the
environment; `Refine/IndSpec.lean`'s header spells out why the clause is false
without it.  It *is* an invariant of every `FEnv` the checker holds
(`FEnv.mk_fenv_canon`/`FEnv.dup_canon` establish it, `FEnv.push_canon`
preserves it), and `IndRoutesSpecP.checkNative` carries it, so the consumer
discharges it. -/
theorem check_native_s_refines
    {st st' : cached.state_c.CState} {fe fe' : fenv.FEnv}
    {p0 : inductives.native_parts.NativeParts}
    (hst : StateWF st) (hfe : FEnvWF fe) (hcan : FEnv.FEnvCanon fe)
    (hfull : FEnv.FEnvFull fe) (hp0 : IndAbs.NativePartsWF p0)
    (h : inductives.inductives_c.check_native_s mode st fe p0
        = ok (.Ok fe', st')) :
    ∀ lst lfe, StateRel st lst → FEnvRel fe lfe →
      ∃ lst' lfe',
        (ConLeche.Cached.checkNativeS (absMode mode) lfe
            (IndAbs.absNativeParts p0)).run lst = .ok (lfe', lst')
        ∧ StateRel st' lst' ∧ FEnvRel fe' lfe' ∧ StateWF st' ∧ FEnvWF fe'
        ∧ FEnv.FEnvCanon fe' ∧ FEnv.FEnvFull fe' := by
  -- `ctor_names`, `level::name_nodup`, the flush, the two passes and the tail
  intro lst lfe hrel hfer
  rw [inductives.inductives_c.check_native_s] at h
  obtain ⟨names, hnames, h⟩ := bind_eq_ok_iff.mp h
  have habsn := NativeInstall.ctor_names_refines hnames
  have hnamesv : names.val = p0.shape.ctors.val.map (fun c => c.1.name) := by
    rw [inductives.native_install.ctor_names] at hnames
    have hv := NativeInstall.ctor_names_from_val p0.shape.ctors
      p0.shape.ctors.length 0#usize _ names (by scalar_tac) hnames
    simpa [alloc.vec.Vec.new] using hv
  have hnwf : NamesWF names := by
    intro n hn
    rw [hnamesv] at hn
    simp only [List.mem_map] at hn
    obtain ⟨c, hc, hce⟩ := hn
    exact hce ▸ (hp0.2.1 c hc).1
  obtain ⟨bnd, hbnd, h⟩ := bind_eq_ok_iff.mp h
  have hbndv := NativeInstall.name_nodup_refines hnwf hbnd
  rw [ConLeche.Cached.checkNativeS]
  split at h
  · rename_i hb
    have hnodup : ((IndAbs.absNativeParts p0).ctors.map (fun c => c.1.name)).Nodup := by
      rw [show (IndAbs.absNativeParts p0).ctors.map (fun c => c.1.name)
        = absNames names from habsn.symm]
      exact of_decide_eq_true (hbndv.symm.trans hb)
    rw [if_pos hnodup]
    obtain ⟨st1, hflush1, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨hfrun1, hrelf1, hwff1, _⟩ := StateC.flush_c_refines hrel hst hflush1
    obtain ⟨b1, hb1, h⟩ := bind_eq_ok_iff.mp h
    have hb1v := NativeInstall.native_raw_rec_refines
      IndIngredients.nativeInstallMentionsConst hp0 hb1
    obtain ⟨pq, hpass, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨res, st2⟩ := pq
    cases res with
    | Err err => simp at h
    | Ok q =>
      obtain ⟨np, b2⟩ := q
      obtain ⟨lst1, lq, hrun1, hrel1, hqrel, hwf1, hqwf, hqcan, hqfull⟩ :=
        check_native_pass_s_refines hw hwff1 hfe hcan hfull hp0 hpass lst.flushed
          lfe hrelf1 hfer
      rw [hb1v] at hrun1
      by_cases hb2 : b2 = true
      · simp only [hb2] at h
        obtain ⟨lst', lfe2, hrun2, hrel2, hfrel2, hwf2, hfwf2, hfcan2, hffull2⟩ :=
          check_native_tail_s_refines hw hwf1 hfe hqwf hqcan hqfull h lst1 lfe lq
            hrel1 hfer hqrel
        refine ⟨lst', lfe2, ?_, hrel2, hfrel2, hwf2, hfwf2, hfcan2, hffull2⟩
        simp only [StateT.run_bind, NativeInstall.exceptOk_bind, StateC.flushC_run, hrun1, hb2,
          if_true]
        exact hrun2
      · simp only [Bool.not_eq_true] at hb2
        simp only [hb2] at h
        obtain ⟨is_rec2, hir, h⟩ := bind_eq_ok_iff.mp h
        have hirv := NativeInstall.native_is_rec_refines
          IndIngredients.recFieldKindBeqRefines hir
        rw [show IndAbs.absKindss np.p.kinds = lq.p.kinds from by
          rw [← hqrel.2.2.1]; rfl] at hirv
        obtain ⟨st3, hflush2, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨hfrun2, hrelf2, hwff2, _⟩ := StateC.flush_c_refines hrel1 hwf1 hflush2
        obtain ⟨pq2, hpass2, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨res2, st4⟩ := pq2
        cases res2 with
        | Err err => simp at h
        | Ok q2 =>
          obtain ⟨np1, b3⟩ := q2
          obtain ⟨lst2, lq2, hrun2, hrel2, hq2rel, hwf2, hq2wf, hq2can, hq2full⟩ :=
            check_native_pass_s_refines hw hwff2 hfe hcan hfull hp0 hpass2
              lst1.flushed lfe hrelf2 hfer
          rw [hirv] at hrun2
          by_cases hb3 : b3 = true
          · simp only [hb3] at h
            obtain ⟨lst', lfe2, hrun3, hrel3, hfrel3, hwf3, hfwf3, hfcan3, hffull3⟩ :=
              check_native_tail_s_refines hw hwf2 hfe hq2wf hq2can hq2full h lst2
                lfe lq2 hrel2 hfer hq2rel
            refine ⟨lst', lfe2, ?_, hrel3, hfrel3, hwf3, hfwf3, hfcan3, hffull3⟩
            simp only [StateT.run_bind, NativeInstall.exceptOk_bind, StateC.flushC_run, hrun1,
              hb2]
            rw [if_neg (by simp)]
            simp only [StateT.run_bind, NativeInstall.exceptOk_bind, StateC.flushC_run, hrun2,
              hb3, if_true]
            exact hrun3
          · simp only [Bool.not_eq_true] at hb3
            simp only [hb3] at h
            obtain ⟨v0, hv0, h⟩ := bind_eq_ok_iff.mp h
            obtain ⟨ce, hce, h⟩ := bind_eq_ok_iff.mp h
            simp at h
  · rename_i hb
    obtain ⟨v0, hv0, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨ce, hce, h⟩ := bind_eq_ok_iff.mp h
    simp at h

end Drivers

/-! ## The seam with the checker tier

`IndRoutesSpec` (`Refine/IndSpec.lean`) is what task #56's checker tier
consumes.  It is exactly the two entry-point lemmas, bundled. -/

/-- **The two inductive routes, refined**, under the knot at
`core_k::check_fuel()` (task #55). -/
theorem ind_routes_spec {mode : env.CheckMode}
    (hk : Core.KnotSpec mode IndAbs.checkFuelU) : IndRoutesSpecP mode where
  checkNative := fun _ _ _ _ _ hst hfe hcan hfull hp0 h lst lfe hrel hfer =>
    check_native_s_refines hk.1 hst hfe hcan hfull hp0 h lst lfe hrel hfer
  checkIndDecl := fun _ _ _ _ _ hst hfe hcan hfull hb h lst lfe hrel hfer =>
    check_ind_decl_s_refines hk.1 hst hfe hcan hfull hb h lst lfe hrel hfer

/-! ### The bridge to the consumer's form (task #59)

`IndRoutesSpecP` (the producer's form, task #57) states the two routes on
*already-recognised* parts; `IndRoutesSpec` (the consumer's form, task #56)
carries the recogniser's verdict inside each clause, because that is the shape
`cached::parsed_c::check_ind_decl_c`'s two-way dispatch consumes.  The step
between them is exactly `native_parts`' own refinement
(`NativeParts.native_parts_refines`): a recognised block gives the Lean
`NativeParts` the native clause existentially quantifies, and a declined one
gives `nativeParts? = none`, which is the modeled clause's first conjunct. -/

/-- **The seam**: the producer's form implies the consumer's, through the
recogniser's refinement. -/
theorem ind_routes_spec_of_p {mode : env.CheckMode} (hp : IndRoutesSpecP mode) :
    IndRoutesSpec mode where
  native := by
    intro st fe n_p block p fe' st' hst hfe hcan hfull hblock hrec h lst lfe hrel hfer
    obtain ⟨habs, hwf⟩ := NativeParts.native_parts_refines IndIngredients.structGens hblock hrec
    obtain ⟨lst', lfe', hrun, hrel', hfer', hst', hfe', hcan', hfull'⟩ :=
      hp.checkNative st fe p fe' st' hst hfe hcan hfull (hwf p rfl) h lst lfe hrel hfer
    exact ⟨lst', lfe', IndAbs.absNativeParts p, habs.symm, hrun, hrel', hst', hfer',
      hfe', hcan', hfull'⟩
  modeled := by
    intro st fe n_p block fe' st' hst hfe hcan hfull hblock hrec h lst lfe hrel hfer
    obtain ⟨habs, _⟩ := NativeParts.native_parts_refines IndIngredients.structGens hblock hrec
    obtain ⟨lst', lfe', hrun, hrel', hfer', hst', hfe', hcan', hfull'⟩ :=
      hp.checkIndDecl st fe block fe' st' hst hfe hcan hfull hblock h lst lfe hrel hfer
    exact ⟨lst', lfe', habs.symm, hrun, hrel', hst', hfer', hfe', hcan', hfull'⟩

/-- **`IndRoutesSpec`, what task #56's checker tier consumes**, from the knot. -/
theorem ind_routes_spec' {mode : env.CheckMode}
    (hk : Core.KnotSpec mode IndAbs.checkFuelU) : IndRoutesSpec mode :=
  ind_routes_spec_of_p (ind_routes_spec hk)

/-! ## The axiom census

DESIGN.md §5's P3 gate on the two entry points, machine-checked: `sorryAx`
leaving these two lines is the gate that says the inductive routes are closed.

**Both lines are closed** (task #62).  `check_native_s_refines` lost its
`sorryAx` at task #68, when task #58's closed checker tier joined task #59's
inductive one.  `check_ind_decl_s_refines` lost its last one here: task #59
left this file a single `sorry` — the `n_p ≤ Usize.max` bound its structured
arm could not produce — and five open stages in `Refine/IndModeled.lean`, and
both were a port bug rather than work.  `modeled.rs` split and indexed `Vec`s
at a `u64 → usize` cast; task #62 swept it onto the counting
`core_k::take_exprs_n` / `drop_exprs_n` / `expr_ops::dom_at_n`, every
`≤ Usize.max` side condition in the tier went away with the casts, and the
five stages are proved. -/

/-- info: 'ConRon.Refine.InductivesC.check_native_s_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms check_native_s_refines

/-- info: 'ConRon.Refine.InductivesC.check_ind_decl_s_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms check_ind_decl_s_refines

-- **The spec bridge is closed** (task #59): `NativeParts.native_parts_refines`,
-- the recogniser, is proved, so the step from the producer's form to the
-- consumer's carries no `sorryAx` at all.
/-- info: 'ConRon.Refine.InductivesC.ind_routes_spec_of_p' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ind_routes_spec_of_p

end ConRon.Refine.InductivesC
