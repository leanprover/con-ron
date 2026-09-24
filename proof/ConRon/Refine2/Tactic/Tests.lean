/-
# `ConRon.Refine2.Tactic.Tests` — regression tests for the shared `lockstep` tactic

Task #97-T2-TACTIC round 2.  Each test is taken from a site where a lane met a
limit of the tactic and worked around it by hand; the test is the site closed
by a plain `lockstep`, so a regression shows up here as a build failure, not as
a hand tail reappearing in some lane.

1. **Twin-only arguments** — a `@[lockstep]` lemma whose TWIN side has an
   argument the Rust does not determine (the message of `liftFueled what` and
   `unresolvedConstsError what`, the div/mod loop's `tried` list).  The
   argument is fixed by unifying the lemma's twin action with the goal's, not
   left as a side goal.
2. **A Rust bind against a twin `if`** — the Rust takes a bind step while the
   twin still tests an `if` (in bind position: `(if c then a else b) >>= k`,
   the `… >>= pure` of a twin `do` block's last line, or undecided by the
   context).  The twin `if` is distributed over its continuation, decided, or
   split, and the zip continues.
3. **No rewrite cycle** — a Rust state step with no twin partner against a
   twin `if` the context cannot decide: `lockstep` must STOP, leaving the goals
   it cannot move (task #97-T2-LOCKSTEP lane ExprOps §7: the `LS.twin_bind_pure`
   fallback once rewrote `x` to `x >>= pure`, the next step normalised it back,
   and `inst_lp_fast_ls` never terminated).  Run under a heartbeat budget, so a
   loop is an error here rather than a hang.
-/
import ConRon.Refine2.Checker.KnotHyp
import ConRon.Refine2.Inductives.Prims
import ConRon.Arena.Inductives.Modeled

open Aeneas Aeneas.Std Result
open ConRon.Generated

attribute [-grind] U32.bv_eq_imp_eq UScalar.val_eq_imp

namespace ConRon.Refine2.Lockstep.Tests

open ConRon.Arena ConRon.Refine2 ConRon.Refine2.Lockstep

/-! ## 1. Twin-only arguments -/

/-- `lift_fueled` ⊑ `liftFueled what`, for EVERY message `what`: the Rust's
message is a constant (`M_FUEL_LEVEL_CMP`), the twin's is its argument, and
the messages are not compared (DESIGN §3.1).  The Checker lane filed this at
the one message its call site uses (`"level comparison"`) because a free
`what` was never picked. -/
@[lockstep] theorem lift_fueled_any_ls {pers st lst} {what : String}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) (o : Option Bool) :
    LSR pers (fun a b => b = a) (arena.core.lift_fueled o) st lst (liftFueled what o) := by
  intro r h
  cases o with
  | some b =>
    simp only [arena.core.lift_fueled, Result.ok.injEq] at h
    subst h
    exact ⟨b, lst, rfl, rfl, hrel, hinv⟩
  | none =>
    simp only [arena.core.lift_fueled] at h
    obtain ⟨s1, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨v, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    rw [fail_run h]
    exact errSim_fail rfl

/-- The lemma above picked at a message it was not stated at. -/
example {pers st lst} (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (o : Option Bool) :
    LS pers (fun a b => b = a) (arena.core.lift_fueled o >>= fun r => ok (r, st)) lst
      (liftFueled "level comparison" o) := by
  lockstep

/-- `unresolved_consts_error` at a fixed subject, through the generic
`unresolved_consts_error_ls` (free `w`). -/
example {pers st lst} {e : arena.handle.EIdx}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) :
    LS pers (fun r v => absAErrKind r = lAErrKind v)
      (arena.checker_base.unresolved_consts_error pers st e) lst
      (unresolvedConstsError "value" (absEIdx e)) := by
  lockstep

/-- A twin-only argument of a LOCAL hypothesis (an induction hypothesis over
the div/mod loop, quantified over the twin's `tried` list), at a list the goal
builds (`tried ++ [msg]`). -/
example {pers st lst} {vis : Std.U64} {rf : arena.env.IFEnv} {lf : IFEnv}
    {mode : kernel.env.CheckMode} {c : arena.handle.NIdx} {value2 : arena.handle.EIdx}
    {variants : alloc.vec.Vec arena.nat_op_pin_set.INatOpPinSet} {i : Std.Usize}
    {tried : alloc.vec.Vec Std.U32} {ltried : List String}
    (hloop : ∀ {st lst} (ltried' : List String), AStateRel₀ pers st lst → AStateInv pers st →
      LS pers (fun a b => b = (fun _ : Unit => ()) a)
        (arena.decl_check.check_div_mod_pin_loop pers vis st mode rf c value2 variants i tried)
        lst
        (checkDivModPinLoop (ConRon.Refine.absMode mode) lf (absNIdx c) (absEIdx value2)
          (absINatOpPinSetLFrom variants i) ltried'))
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) :
    LS pers (fun a b => b = (fun _ : Unit => ()) a)
      (arena.decl_check.check_div_mod_pin_loop pers vis st mode rf c value2 variants i tried) lst
      (checkDivModPinLoop (ConRon.Refine.absMode mode) lf (absNIdx c) (absEIdx value2)
        (absINatOpPinSetLFrom variants i) (ltried ++ ["absent"])) := by
  lockstep

/-! ## 1–2. The reported sites: `install_value_tail`, `install_constant_val_tail`

The Checker lane closed both with `lockstep`, then `rw [bind_pure, if_neg …]`
by hand, then `unresolved_consts_error` at a specialised copy fixed at
`"value"`/`"type"`.  Both are one `lockstep` call now. -/

theorem install_value_tail_refines' {pers st lst} {vis : Std.U64} {rf lf}
    {cv : arena.env.IConstantVal} {value_a : arena.handle.EIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRel rf lf) (hfinv : IFEnvInv rf)
    (hrun : arena.checker_split.install_value_tail pers vis st rf cv value_a = ok o) :
    Sim₀ absEIdx pers lst o
      (installValueTailSpec (lf.restrictTo (absU vis)) (absIConstantVal cv)
        (absEIdx value_a)) := by
  have hfeI : IFEnvRelI rf lf := ⟨hfe, hfinv⟩
  have hctx := IFEnvInv.coreCtxSelf hfe hfinv
  refine LS.toSim₀ ?_ hrun
  rw [arena.checker_split.install_value_tail]
  unfold installValueTailSpec
  lockstep

/-! ## 2. A Rust bind against a twin `if` in bind position -/

/-- The twin's last line is an `if` bound to `pure` (`(if c then a else b) >>=
pure`); the Rust has already decided `c` and steps a bind. -/
example {pers st lst} {e : arena.handle.EIdx} {b : Bool} (hb : b = true)
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) :
    LS pers (fun r v => absAErrKind r = lAErrKind v)
      (arena.checker_base.unresolved_consts_error pers st e >>= fun p => ok p) lst
      ((if b then unresolvedConstsError "value" (absEIdx e)
        else unresolvedConstsError "type" (absEIdx e)) >>= fun r => pure r) := by
  lockstep

/-- The twin's next step is an `if` the last Rust test decided, the Rust's is
a state bind whose partner is inside the branch (the Checker Base/Top lane's
`unresolved_consts_error` and axiom-arm gates): the `if` is decided from the
context, not taken whole as the partner (`twin_bind_pure` skips an `if`). -/
example {pers st lst} {e : arena.handle.EIdx} {b : Bool} (hb : ¬ b = true)
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) :
    LS pers (fun r v => absAErrKind r = lAErrKind v)
      (arena.checker_base.unresolved_consts_error pers st e >>= fun p => ok p) lst
      (if b then (pure (.invalid "a") : AM Arena.CheckError)
        else unresolvedConstsError "type" (absEIdx e)) := by
  lockstep

set_option lockstep.twinSplit true in
/-- The twin tests `c` where the Rust does not test at all (both branches are
the same operation): with `lockstep.twinSplit` the twin `if` is split and each
branch zips (by default the zip stops there, §7). -/
example {pers st lst} {e : arena.handle.EIdx} {b : Bool}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) :
    LS pers (fun r v => absAErrKind r = lAErrKind v)
      (arena.checker_base.unresolved_consts_error pers st e >>= fun p => ok p) lst
      (if b then unresolvedConstsError "value" (absEIdx e)
        else unresolvedConstsError "type" (absEIdx e)) := by
  lockstep

/-! ## 3. No rewrite cycle -/

-- A Rust state step whose twin partner is missing (the twin's branches are
-- `pure`s), against a twin `if` the context does not decide: `lockstep` stops
-- with the goals it cannot move, inside the heartbeat budget.
#guard_msgs (drop warning) in
set_option maxHeartbeats 20000 in
example {pers st lst} {e : arena.handle.EIdx} {b : Bool}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) :
    LS pers (fun r v => absAErrKind r = lAErrKind v)
      (arena.checker_base.unresolved_consts_error pers st e >>= fun p => ok p) lst
      (if b then (pure (.invalid "a") : AM Arena.CheckError) else pure (.invalid "b")) := by
  lockstep
  all_goals sorry

/-! ## 4. A twin `match` on a constructor application (the Inductives Modeled lane)

The fallback that cases a twin `match` on a TERM once cased on `some (!c)`
itself: `cases` rebuilt `some x`, the `match` still did not reduce, and the
move repeated for ever (`check_eta_thm` hit the heartbeat limit; the lane's
`ind_twin_split` in `lockstep_mod` split such matches first).  It now cases on
the first field that is not a constructor application (`!c`); the context
(`hc`) rules the other branch out, so the split is kept (§7). -/
set_option maxHeartbeats 20000 in
example {pers st lst} {c : Bool} (hc : (!c) = true)
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) :
    LS pers (fun a b => b = a) (ok (.Ok (!c), st)) lst
      (match some (!c) with
        | some true => pure true
        | some false => pure false
        | none => pure false) := by
  lockstep

set_option maxHeartbeats 20000 in
/-- The Modeled lane's `check_eta_thm` shape: a twin `match` whose other
discriminant (`none`) rules out every alternative but the catch-all, while
the first is stuck.  The match is `split` (the impossible alternatives
dropped), not cased on a field. -/
example {pers st lst} {c : Bool}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) :
    LS pers (fun a b => b = a) (ok (.Ok false, st)) lst
      (match some (!c), (none : Option Bool) with
        | some true, some _ => pure true
        | _, _ => pure false) := by
  lockstep

/-! ## 5. A failing read reports its own failure

When an `LSR` read step fails (here: the twin reads another handle), the error
is the read's candidates', not the Rust-only fallback's "no @[lockstep] lemma
for `arena.monad.view`". -/

open Lean Elab Tactic in
elab "lockstep_step_fails_with " s:str : tactic => do
  let msg ← try
      evalTactic (← `(tactic| lockstep_step))
      pure none
    catch e => pure (some (← e.toMessageData.toString))
  match msg with
  | none => throwError "lockstep_step succeeded"
  | some m =>
    unless (m.splitOn s.getString).length > 1 do
      throwError "lockstep_step failed with another message:\n{m}"

#guard_msgs (drop warning) in
example {pers st lst} {h h' : arena.handle.EIdx}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absENodeView a)
      (arena.monad.view pers st h >>= fun r => match r with
        | .Ok v => ok (.Ok v, st)
        | .Err e => ok (.Err e, st)) lst
      (Arena.view (absEIdx h') >>= fun v => pure v) := by
  lockstep_step_fails_with "no candidate for `ConRon.Generated.arena.monad.view` closes"
  sorry

/-! ## 6. Memoised walks: `LSM` / `LSRM`

Walks that return their memo beside the `Result` (the Checker tier's
`consts_resolve_f_*` and `all_level_params_defined_*`, the Promote tier's
intern walks) are zipped by `lockstep` through `LSM` (state) and `LSRM`
(reader); the recursive walk is a hypothesis here, as an induction
hypothesis is in a fuel induction. -/

/-- The answer-and-memo relation of the Checker tier's `Bool`-memo walks. -/
abbrev BMemoR (p : Bool × ron.hashmap2.HashMap2 arena.handle.EIdx Bool)
    (b : Bool × Std.HashMap EIdx Bool) : Prop :=
  b.1 = p.1 ∧ ExprOps.LMemoRel p.2 b.2

/-- `consts_resolve_f_two`: two memoised state walks in a row, the memo
threaded, the two answers combined. -/
example {pers st lst} {vis : Std.U64} {rf : arena.env.IFEnv} {lf : IFEnv}
    {rm lm} {fuel : Std.U64} {a b : arena.handle.EIdx}
    (hgo : ∀ {st lst rm lm} (h : arena.handle.EIdx), AStateRel₀ pers st lst →
      AStateInv pers st → ExprOps.LMemoRel rm lm →
      LSM pers BMemoR (arena.checker_base.consts_resolve_f_go pers vis st rf rm fuel h) lst
        (constsResolveFGo lf lm (absU fuel) (absEIdx h)))
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hm : ExprOps.LMemoRel rm lm) :
    LSM pers BMemoR (arena.checker_base.consts_resolve_f_two pers vis st rf rm fuel a b) lst
      (do
        let (b₁, memo) ← constsResolveFGo lf lm (absU fuel) (absEIdx a)
        let (b₂, memo) ← constsResolveFGo lf memo (absU fuel) (absEIdx b)
        pure (b₁ && b₂, memo)) := by
  rw [arena.checker_base.consts_resolve_f_two]
  lockstep

/-- `consts_resolve_f_fast`: a fresh memo, the walk as a callee, the memo
dropped. -/
example {pers st lst} {vis : Std.U64} {rf : arena.env.IFEnv} {lf : IFEnv}
    {e : arena.handle.EIdx}
    (hgo : ∀ {st lst rm lm} (fuel : Std.U64) (h : arena.handle.EIdx),
      AStateRel₀ pers st lst → AStateInv pers st → ExprOps.LMemoRel rm lm →
      LSM pers BMemoR (arena.checker_base.consts_resolve_f_go pers vis st rf rm fuel h) lst
        (constsResolveFGo lf lm (absU fuel) (absEIdx h)))
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) :
    LS pers (fun a b => b = id a) (arena.checker_base.consts_resolve_f_fast pers vis st rf e)
      lst (constsResolveFFast lf (absEIdx e)) := by
  rw [arena.checker_base.consts_resolve_f_fast, constsResolveFFast]
  lockstep

/-- `all_level_params_defined_binder`: a memoised READER walk (`LSRM`), twice,
with the binder's own test between. -/
example {pers st lst} {params : alloc.vec.Vec kernel.name.Name} {rm lm}
    {fuel : Std.U64} {t b : arena.handle.EIdx} {m : kernel.expr.BinderMeta}
    (hgo : ∀ {rm lm lst} (h : arena.handle.EIdx), AStateRel₀ pers st lst →
      AStateInv pers st → ExprOps.LMemoRel rm lm →
      LSRM pers BMemoR (arena.checker_base.all_level_params_defined_go pers st params rm fuel h)
        st lst
        (allLevelParamsDefinedGo (ConRon.Refine.absNames params) lm (absU fuel) (absEIdx h)))
    (hpd : LSP (kernel.prop_when.params_defined params m.pw)
      (fun b3 => TwinEq ((ConRon.Refine.absBinderMeta m).pw.paramsDefined
        (ConRon.Refine.absNames params)) b3))
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hm : ExprOps.LMemoRel rm lm) :
    LSRM pers BMemoR
      (arena.checker_base.all_level_params_defined_binder pers st params rm fuel t b m) st lst
      (do
        let (b₁, memo) ← allLevelParamsDefinedGo (ConRon.Refine.absNames params)
          lm (absU fuel) (absEIdx t)
        if !b₁ then pure (false, memo) else do
          let (b₂, memo) ← allLevelParamsDefinedGo (ConRon.Refine.absNames params)
            memo (absU fuel) (absEIdx b)
          pure (b₂ && (ConRon.Refine.absBinderMeta m).pw.paramsDefined
            (ConRon.Refine.absNames params), memo)) := by
  rw [arena.checker_base.all_level_params_defined_binder]
  lockstep

/-! ## 7. The Frontend lane's two findings

A twin test nothing decides is NOT split by default: the zip stops and hands
the goal back (here the `else` branch is a program the Rust never runs, and
walking it would be wasted work — in the lane's census proofs, until the
heartbeat limit).  And a side goal's `simp [*]`/`simp_all` does not see a
callee spec hypothesis (an induction hypothesis), which it would use as a
conditional rewrite rule; `∀` facts it keeps. -/

set_option linter.unusedTactic false in
set_option maxHeartbeats 20000 in
example {pers st lst} {b : Bool} {n : Nat}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hstuck : LS pers (fun a b => b = a) (ok (.Ok n, st)) lst
      (if b then pure n else do
        let k ← pure (n + 1)
        let j ← pure (k * 2)
        pure (j - n))) :
    LS pers (fun a b => b = a) (ok (.Ok n, st)) lst
      (if b then pure n else do
        let k ← pure (n + 1)
        let j ← pure (k * 2)
        pure (j - n)) := by
  lockstep
  exact hstuck

-- The side tiers' context: a callee spec (an induction hypothesis) is gone, a
-- `∀` fact stays.
example {pers : arena.store.PersTier} {n : Nat}
    (hih : ∀ {st : arena.monad.AState} {lst : AState} (m : Nat), m < n →
      AStateRel₀ pers st lst →
      LS pers (fun a b => b = a) (ok (.Ok m, st)) lst (pure m))
    (hfact : ∀ j, j < n → j < n + 1) : n < n + 2 := by
  lockstep_clear_foralls
  fail_if_success have := @hih
  have := hfact
  omega

/-! ## 8. Round 3: a Rust `have`, a test up to `==`/`decide`, a pair read

Three limits the Inductives lane (round 5) met and worked around per proof. -/

/-- A Rust `have x := …; do …` at the head of a step (the port's `let i1 :=
Vec.len x_fvs` in `native_fields_at`'s step case, which the lane closed with a
`dsimp only` first): zeta-reduced, not taken for a tail call with "no head
constant". -/
example {pers st lst} (x_fvs : alloc.vec.Vec arena.handle.EIdx) (i : Std.U64)
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) :
    LS pers (fun a b => b = a)
      (have i1 := alloc.vec.Vec.len x_fvs
       do
        let i2 ← lift (Std.UScalar.cast .U64 i1)
        if i >= i2 then ok (.Ok false, st) else ok (.Ok true, st)) lst
      (if i.val < x_fvs.val.length then pure true else pure false) := by
  lockstep

/-- A twin `if` stated with `==` against the Rust's list test, whose spec
(`nidx_vec_beq_ls`, Core) answers `decide (absNIdxList a = absNIdxList b)`;
`lockstep_simp` also unfolds `absNIdxList` in the twin but not in the Rust
test's hypothesis.  Both are normalised before the twin test is decided (the
lane restated `structPartsCoreAtSpec`'s tests in the Core form instead). -/
example {pers st lst} (a b : alloc.vec.Vec arena.handle.NIdx)
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) :
    LS pers (fun a b => b = a)
      (do
        let r ← arena.core.nidx_vec_beq a b
        if r then ok (.Ok true, st) else ok (.Ok false, st)) lst
      (if absNIdxList a == absNIdxList b then pure true else pure false) := by
  lockstep

/-- The same at the tier that decides it: `lockstep_side_test`, which runs
before the dear tier (before, only `lockstep_side_ite`'s `simp_all` did, which
in the lane's `struct_parts_core_at` context ran out of heartbeats and the
twin `if` was split). -/
example (a b : alloc.vec.Vec arena.handle.NIdx)
    (hc : decide (absNIdxList a = absNIdxList b) = true) :
    (List.map absNIdx a.val == List.map absNIdx b.val) = true := by
  lockstep_side_test

/-- A count test: the Rust compares machine words, the twin `==` on `Nat`
(`scalar_tac` after the normalisation, in the dear tier). -/
example (m_i n_p i : Std.U64) (hP : i.val = n_p.val + 2) (hc : ¬ m_i = i) :
    ¬ (m_i.val == n_p.val + 2) = true := by
  lockstep_side_ite

/-- The Rust's pair read `let (e, _) ← v[j]; dup2 e` under an `if` the
tactic distributes (`rec_ctor_kinds_from`'s `dom`): stepped through, not kept
as an equation `(let (e, _) := v[j]; dup2 e) = ok a` (the lane's
`let_pair_dup2_eq` finish). -/
example {pers st lst} (cbs : alloc.vec.Vec (arena.handle.EIdx × kernel.expr.BinderMeta))
    (k n : Std.U64) (hk : k.val < cbs.val.length) (hmax : k.val ≤ Std.Usize.max)
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absEIdx a)
      (do
        let dom ←
          if k < n then do
            let i4 ← lift (Std.UScalar.cast .Usize k)
            let (e, _) ← alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice
              (arena.handle.EIdx × kernel.expr.BinderMeta)) cbs i4
            arena.handle.EIdx.Insts.Con_ron_coreRonHashmapDup.dup2 e
          else arena.handle.EIdx.of_word 0#u32
        ok (.Ok dom, st)) lst
      (if k.val < n.val then pure (absEIdx (cbs.val[k.val]'hk).1)
        else pure (absEIdx { word := 0#u32 })) := by
  lockstep

/-! ## 9. An accumulator-versus-`mapM` equation, registered guarded

The Inductives lane's recipe: a callee stated at a transcription (`FSpec l`,
its `…_twin0` companion), a caller's twin `l.mapM F`.  The equation
`l.mapM F = FSpec l` could not be `lockstep_simp` (it rewrote another caller's
twin away from ITS callee's `mapM` statement), so each caller applied it by
`simp only` before `lockstep`.  Registered `@[lockstep_congr_simp]`, it is
used only to match a spec's twin action against the goal's. -/

/-- A transcription of `l.mapM Arena.view` (the stand-in for `structIdxListSpec`). -/
def viewsSpec : List EIdx → AM (List ENodeView)
  | [] => pure []
  | h :: hs => do
    let v ← Arena.view h
    let vs ← viewsSpec hs
    pure (v :: vs)

@[lockstep_congr_simp] theorem mapM_view_eq (l : List EIdx) :
    l.mapM Arena.view = viewsSpec l := by
  induction l with
  | nil => rfl
  | cons h hs ih => rw [List.mapM_cons, ih, viewsSpec]

/-- The callee (a hypothesis here) is stated at the transcription, the goal's
twin is the `mapM`: matched through `mapM_view_eq`. -/
example {pers st lst} {h : arena.handle.EIdx} {l : List EIdx}
    {R : arena.store.ENodeView → List ENodeView → Prop}
    (hf : LSR pers R (arena.monad.view pers st h) st lst (viewsSpec l))
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) :
    LS pers R
      (arena.monad.view pers st h >>= fun r => match r with
        | .Ok v => ok (.Ok v, st)
        | .Err e => ok (.Err e, st)) lst
      (l.mapM Arena.view >>= fun vs => pure vs) := by
  lockstep

/-- A callee stated at the `mapM` form is still matched as it stands: the twin
program is not rewritten. -/
example {pers st lst} {h : arena.handle.EIdx} {l : List EIdx}
    {R : arena.store.ENodeView → List ENodeView → Prop}
    (hf : LSR pers R (arena.monad.view pers st h) st lst (l.mapM Arena.view))
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) :
    LS pers R
      (arena.monad.view pers st h >>= fun r => match r with
        | .Ok v => ok (.Ok v, st)
        | .Err e => ok (.Err e, st)) lst
      (l.mapM Arena.view >>= fun vs => pure vs) := by
  lockstep

/-! ## 10. Two lemmas for one Rust head: priority and erasure

The Inductives Modeled lane met it at `if_all_zero` of the empty list: one
tier's pair answered the value only, another's also its well-formedness.  The
first registered was always tried first (an `LSP` spec's predicate is a
metavariable, so any lemma closes the spec goal), and the lane opened a
namespace of its own to put its copy in front.  Now the stronger lemma says so
itself: `@[lockstep high]`.  Here a Rust step of this file's own with two pairs
that really differ: the weak one (registered FIRST) says nothing. -/

/-- A Rust-only step (the stand-in for `if_all_zero`). -/
def rustEcho (n : Nat) : Result Nat := ok n

/-- The weak pair, registered first at the default priority. -/
@[lockstep] theorem rust_echo_weak (n : Nat) : LSP (rustEcho n) (fun _ => True) :=
  fun _ _ => trivial

/-- The strong pair, registered second: `high` puts it in front. -/
@[lockstep high] theorem rust_echo_strong (n : Nat) : LSP (rustEcho n) (fun a => a = n) :=
  fun _ h => (Result.ok_injective h).symm

/-- The leaf needs the answer: only the `high` lemma gives it. -/
example {pers st lst} (n : Nat) (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) :
    LS pers (fun a b => b = a) (do let a ← rustEcho n; ok (.Ok a, st)) lst (pure n) := by
  lockstep

-- `attribute [-lockstep]` erases it: the weak lemma is taken, and the leaf is
-- left over.
#guard_msgs (drop warning) in
attribute [-lockstep] rust_echo_strong in
example {pers st lst} (n : Nat) (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) :
    LS pers (fun a b => b = a) (do let a ← rustEcho n; ok (.Ok a, st)) lst (pure n) := by
  lockstep
  fail_if_success done
  sorry

/-- After the erasure's scope, the `high` lemma is back. -/
example {pers st lst} (n : Nat) (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) :
    LS pers (fun a b => b = a) (do let a ← rustEcho n; ok (.Ok a, st)) lst (pure n) := by
  lockstep

/-! ## 11. A twin split stops at the list shape

The Inductives Modeled lane's `eq_app3`: the twin's `match ← viewLs us with
| [lv] => … | _ => …` against the port's length test.  The twin-`match`
fallback cased the list, then the head `LIdx` (a structure), then its `U32`,
`BitVec`, `Fin`: a variable of a structure type is no case target now. -/

open Lean Elab Tactic in
/-- No goal has a variable of a machine word's representation types. -/
elab "guard_no_word_split" : tactic => do
  for g in ← getGoals do
    g.withContext do
      for d in ← getLCtx do
        let t ← instantiateMVars d.type
        if t.isConstOf ``UInt32 || t.isAppOf ``BitVec || t.isAppOf ``Fin then
          throwError "a twin split cased a word down to {t}"

#guard_msgs (drop warning) in
example {pers st lst} {h : arena.handle.EIdx}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) :
    LSR pers (fun a b => b = (Option.map fun q => (absNIdx q.1, absLIdx q.2.1, absEIdx q.2.2.1,
        absEIdx q.2.2.2.1, absEIdx q.2.2.2.2)) a)
      (arena.inductives.modeled.eq_app3 pers st h) st lst (eqApp3? (absEIdx h)) := by
  apply LSR.of_LS
  rw [arena.inductives.modeled.eq_app3, eqApp3?]
  lockstep
  guard_no_word_split
  all_goals sorry

/-! ## 12. `lockstep_congr` does not unfold first

Its first alternative was a DEFAULT `rfl`, which between two twin actions that
are not syntactically equal unfolds as far as the definitions go (~4 s per
failing attempt at the Inductives lane's `native_rules_ok_from` callees, which
needed `maxHeartbeats 400000`; `congr 1` closed them in 0.3 s).  Here a default
`rfl` would evaluate a 200-element list; the budget does not allow it. -/

/-- A twin action whose argument is expensive to evaluate. -/
def slowTwin (l : List Nat) : AM Nat := pure l.length

/-- A long list (the stand-in for an abstracted vector). -/
def slowList (n : Nat) : List Nat := (List.range n).map (fun i => i * i % 7)

set_option maxHeartbeats 4000 in
example (a b : Nat) (h : slowList 200 ++ [a] = slowList 200 ++ [b]) :
    slowTwin (slowList 200 ++ [a]) = slowTwin (slowList 200 ++ [b]) := by
  lockstep_congr

-- The Inductives Install lane's case of the same limit: a twin knot entry
-- whose depth the twin spells differently from the port (`absU i4` against
-- `↑off + (↑k - 1)`); the default `rfl` unfolded the knot (`pureFnsA`) and did
-- not come back, and the lane made `isDefEqCore`/`inferTypeCore`/`ensureSortCore`
-- locally irreducible.  (This small instance also passes a default `rfl`; the
-- example above is the one that tells the two apart.)
set_option maxHeartbeats 20000 in
example (mode : ConLeche.CheckMode) (fe : IFEnv) (i4 off k : Std.U64) (e : EIdx)
    (hi : absU i4 = absU off + (absU k - 1)) :
    inferTypeCore mode fe checkFuel (absU i4) e =
      inferTypeCore mode fe checkFuel (absU off + (absU k - 1)) e := by
  lockstep_congr

/-! ## 13. A nested twin `do` block in bind position

The Inductives Install lane's `whnf_telescope`: the twin as stated is
`(do let e' ← whnf …; …) >>= fun q => pure …` once its equation is unfolded.
Every step's RESULT is flattened (`bind_assoc` is `lockstep_simp`), the stated
goal is not, so the first bind rule met the nested block; the lane began each
case with `simp only [bind_assoc]`.  The block is now tried whole (a proof may
group the twin to be one Rust callee's partner: `Checker/Base.lean`'s
`check_proj_rule_wf`) and then flattened (`LS.twin_assoc`). -/
example {pers st lst} {e : arena.handle.EIdx}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) :
    LS pers (fun r v => absAErrKind r = lAErrKind v)
      (arena.checker_base.unresolved_consts_error pers st e >>= fun p => ok p) lst
      ((do let r ← unresolvedConstsError "value" (absEIdx e); pure r) >>= fun q => pure q) := by
  lockstep

/-! ## 14. A twin-only argument the congruence does not fix

A spec whose twin takes a message the twin action then ignores (the Install
lane's `unwrapOr` at a constructor, registered `lockstep_simp`): the
congruence closes without assigning the message.  It went to the side tiers,
and in a dead branch (a contradictory context) `omega` closed the goal of type
`String` by an auxiliary "theorem" the kernel rejected ("type of theorem … is
not a proposition").  Now it is `default`. -/

/-- A twin action that ignores its message (reducibly, so the congruence
closes by unfolding it). -/
@[reducible] def msgTwin {α : Type} (_s : String) (x : AM α) : AM α := x

set_option linter.unusedVariables false in
example {pers st lst} {e : arena.handle.EIdx} (hfalse : False)
    (hf : ∀ (s : String), LS pers (fun r v => absAErrKind r = lAErrKind v)
      (arena.checker_base.unresolved_consts_error pers st e) lst
      (msgTwin s (unresolvedConstsError "value" (absEIdx e))))
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) :
    LS pers (fun r v => absAErrKind r = lAErrKind v)
      (arena.checker_base.unresolved_consts_error pers st e) lst
      (unresolvedConstsError "value" (absEIdx e)) := by
  lockstep

/-! ## 15. A failing alternative fails: no error becomes `sorry`

The Inductives Install lane: a `lockstep_side_ext` rule with a `‹…›` term that
does not elaborate was recovered to `sorry` and so "closed" the goal (the
error logged, the alternative taken).  Every `lockstep` entry point now runs
without error recovery (`strict`). -/

open Lean Elab Tactic in
/-- `tac` must FAIL, run with error recovery on (as in any tactic block;
`fail_if_success` itself turns recovery off, so it cannot tell). -/
elab "fails_with_recovery " tac:tactic : tactic => do
  let s ← saveState
  let ok ← withReader (fun ctx => { ctx with recover := true }) do
    try evalTactic tac; pure true catch _ => pure false
  s.restore
  if ok then throwError "the tactic succeeded (through an error recovered to `sorry`?)"

section
-- a lane extension whose term cannot elaborate here
local macro_rules | `(tactic| lockstep_side_ext) => `(tactic| (have h : False := ‹False›; exact h.elim))

#guard_msgs (drop warning) in
example (n : Nat) : n = n + 1 := by
  fails_with_recovery lockstep_side
  sorry

#guard_msgs (drop warning) in
example (p : Prop) : p := by
  fails_with_recovery lockstep_side_ite
  sorry
end

/-! ## 16. A twin `match` in bind position

The Install lane: the twin-`match` fallback looked at the twin's head only,
not at the callee of its next bind (`(match t with …) >>= k`). -/
set_option maxHeartbeats 20000 in
example {pers st lst} {c : Bool} (hc : (!c) = true)
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) :
    LS pers (fun a b => b = a) (ok (.Ok (!c), st)) lst
      ((match some (!c) with
        | some true => pure true
        | some false => pure false
        | none => pure false) >>= fun b => pure b) := by
  lockstep

/-! ## 17. A memo probe at the key's other spelling

The Inductives Parts lane's `has_loose_bvar_b_go`: the probe's `TwinEq` is
stated at `lm[absEIdxNat k]?`, the twin probes `memo[(h, i)]?`, and the context
has the key equation `absEIdxNat k = (absEIdx h, absU i)`.  A key equation
(a pair on the right) respells the `TwinEq`'s left side, as the scalar facts
do. -/
example {pers st lst} (kf : Nat → Nat × Nat) (k a b v : Nat)
    (lm : Std.HashMap (Nat × Nat) Nat)
    (hkey : kf k = (a, b)) (hprobe : TwinEq lm[kf k]? (some v))
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) :
    LS pers (fun a b => b = a) (do let w ← ok v; ok (.Ok w, st)) lst
      (match lm[(a, b)]? with
        | some x => pure x
        | none => pure 0) := by
  lockstep

/-! ## 18. A `def` relation, split

The Parts lane's `WOutRel`: a relation that is a conjunction was split only
when it unfolds reducibly (an `abbrev`); the lane made it one.  A `def` tagged
`@[lockstep_rel]` is split too. -/

/-- A pair answer both of whose components are the Rust's. -/
@[lockstep_rel] def PairRel (a : Nat) (b : Nat × Nat) : Prop := b.1 = a ∧ b.2 = a

/-- At a leaf. -/
example {pers st lst} (n : Nat)
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) :
    LS pers PairRel (ok (.Ok n, st)) lst (pure (n, n)) := by
  lockstep

/-! ## The axiom census -/

#print axioms lift_fueled_any_ls
#print axioms install_value_tail_refines'

end ConRon.Refine2.Lockstep.Tests
