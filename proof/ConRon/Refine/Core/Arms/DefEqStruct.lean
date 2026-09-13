/-
# The defeq arm's structural cluster (task #55, `CORE_PLAN.md` step 6)

Six helpers of `crates/con-ron-core/src/cached/core_c.rs`'s
`partial_fixpoint` block:

* the three *certificates* the stuck fallback runs — `struct_eta_cert_i`
  (`core_c.rs:1034`, con-leche's `structEtaCertI`,
  `ConLeche/Cached/CoreC.lean:476`), `struct_unit_cert_i` (`:1062`,
  `structUnitCertI`, `CoreC.lean:487`) with its state-touching tail
  `struct_unit_steps_i` (`:1105`), and `eta_cert_i` (`:1148`, `etaCertI`,
  `CoreC.lean:516`) with its tail `eta_cert_body_i` (`:1185`);
* `defeq_struct_i` (`:4061`), the **kind-by-kind case analysis** of
  `defeqStepI` (`CoreC.lean:1456-1616`).

## What `defeq_struct_i` is, exactly

`defeqStepI` is one `do` block.  The port splits it into six functions
(`defeq_step_i`, `defeq_after_whnf_i`, `defeq_lits_i`, `defeq_delta_i`,
`defeq_delta_both_i`, `defeq_unfold_both_i`) plus this one, which is
precisely the **`| false, false =>` arm** of the cited

```
match ← pure (unfoldableHeadC fe a'), ← pure (unfoldableHeadC fe b') with
```

— neither head unfoldable, so `match a', b' with …` decides structurally.
con-leche writes that arm inline, so `defeqStructL` below *names* it, in the
`eqvStep`/`nodeL` way of `Refine/StateC.lean` and `Refine/StateCResolve.lean`:
a local definition that is a verbatim transcription of the cited subterm, tied
to the cited definition by an identity that is `rfl`, so that nothing about the
naming is assumed.  The identity is `defeqStepI_eq`: the *whole* of
`defeqStepI`, restated with its three port-split arms named
(`defeqStructL`, and inside it `defeqAppsL` and `defeqBindersL`, the `.app`
congruence and the two binder congruences, which the port also split out as
`defeq_apps_i`/`defeq_binders_i`), proved by `rfl`.

`defeqAppsL`/`defeqBindersL` are stated here rather than in `Arms/DefEq.lean`
because `defeqStructL` mentions them; `Arms/DefEq.lean`'s own
`defeq_apps_i_refines`/`defeq_binders_i_refines` will name the same two
subterms, and the two namings are `rfl`-equal by construction.

## The two literal arms and their matchers

Four of `defeq_struct_i`'s arms — `.app`/`.lit` and `.lit`/`.app`, each at a
`Nat` and at a `String` literal — read their verdict out of a *guard*
(`core_k::succ_of`, `core_k::str_expansion_fires`), where the cited Lean
writes an inline `match`.  `succ_match_eq` and `str_match_eq` below turn the
cited `match` into the guard's shape, and they do fire on `defeqStructL`:
matchers are shared inside this module.  What is *not* shared is the copy of
the same `match` in the statements of `CoreKLits.lean`'s `succ_of_refines` and
`CoreKGuards.lean`'s `str_expansion_fires_refines` — those modules built their
own matcher constant, so `rw` will not see through it.  Each of the four arms
therefore restates the guard's answer once, `have h : … := h0`, in this
module's matcher; the two matchers are definitionally equal, so the restating
`have` is by `rfl` and assumes nothing.

## The failure half (task #67)

Every lemma below is stated over the Rust computation's **full outcome**
(`Refine/State.lean`'s `Out`, DESIGN.md §3's ruling of 2026-09-13): the exact
result on success, and con-leche's own throw *at the same kind* on a failure.
All the `CheckError` sites these six helpers reach are mirrored (DESIGN.md,
task #67's census for `cached/core_c.rs`: all 49 are), so no arm of this file
is vacuous.

Almost all of it is one move: a sub-call threw, and the error is carried
through the rest of the cited `do` block.  A *tail* call is even shorter than
it was — `out_of_eq` transports the callee's whole `Out` along the one
equation that reduces con-leche's block to the callee's action, and the two
outcomes share that equation.  Two failures are not sub-calls:

* **`eta_cert_body_i`'s annotation check** (`core_c.rs:1201`) is this file's
  one explicit `throw`: the prop-ness annotations disagree at a verified mode,
  the port builds `NotImplemented` out of its code points, and the cited
  `etaCertI` throws `notImplemented` at exactly that step
  (`CoreC.lean:530`).  Messages are not compared, so the two spellings of the
  same sentence never meet.
* **`core_k::lift_fueled`'s `Err` arm**, which `defeq_struct_i` reaches from
  its `.sort`/`.sort` and `.const`/`.const` arms: `internal "fuel exhausted:
  level comparison"` against the cited `liftFueled "level comparison" none`
  (`Kernel/Core.lean:109-111`), `errSim_liftFueled_none` below.  Here the two
  messages *are* the same string, though nothing rests on that.

## What is not here

The `.M`-suffixed `Array Std.U32` constants of these functions
(`eta_cert_body_i.M`) are those messages' code points; since a refinement
lemma compares error *kinds* and never messages, they still carry no theorem.

The file is `sorry`-free: every theorem below closes on
`[propext, Classical.choice, Quot.sound]`.
-/
import ConRon.Refine.Core.Arms.Shape
import ConRon.Refine.CoreKPinned
import ConRon.Refine.ExprOpsCSubst

open Aeneas Aeneas.Std Result
open ConRon.Generated ConRon.Generated.kernel ConRon.Generated.cached
open ConRon.Refine ConRon.Refine.State ConRon.Refine.FEnv

namespace ConRon.Refine.Core

/-! `attribute [local simp]` does not travel across files, so `Shape.lean`'s
monad-plumbing set (`CheckCM = StateT CState (Except CheckError)`) is
re-declared here verbatim. -/
attribute [local simp] except_pure' StateT.run modifyGet MonadStateOf.modifyGet
  StateT.modifyGet Bind.bind StateT.bind Pure.pure StateT.pure Except.bind
  Except.pure Aeneas.Std.uncurry

/-- `bind_eq_ok_iff` in the form `simp` leaves a `Result` bind in once
`Bind.bind` has been unfolded (`Arms/Shared.lean`'s helper, re-declared). -/
theorem std_bind_eq_ok' {α β : Type} {e : Result α} {f : α → Result β} {v : β}
    (h : Std.bind e f = ok v) : ∃ y, e = ok y ∧ f y = ok v :=
  bind_eq_ok_iff.mp h


/-! ## Forward stepping through the generated code

Aeneas compiles `let (r, st) ← f` to `Bind.bind f (Std.uncurry fun r st => …)`,
so `bind_eq_ok_iff` alone leaves the `uncurry` in the way (which is why
`Refine/Core/Knot.lean` retypes each step by hand).  Unfolding `uncurry`
alongside it is the whole of the plumbing: one `res_step` per `let … ←` of the
cited Rust body. -/

/-- `expr::binder_meta_dup` is the identity, in the `simp` shape
`State.lean`'s `expr_dup_eq` has (`Refine/Expr.lean` proves the inference
form). -/
@[local simp] theorem binder_meta_dup_eq' (m : expr.BinderMeta) :
    expr.binder_meta_dup m = ok m := by
  obtain ⟨pw⟩ := m; simp [expr.binder_meta_dup]

/-- Flatten the next `Result` bind of a generated body: `bind_eq_ok_iff`
together with Aeneas's tuple-pattern `uncurry`. -/
local macro "res_step " h:ident : tactic =>
  `(tactic| simp only [bind_eq_ok_iff, Aeneas.Std.uncurry, arc_deref_eq, expr_dup_eq,
      binder_meta_dup_eq', ExprOps.node_kind, Result.ok.injEq,
      exists_eq_left'] at $h:ident)


/-- `core_k::ind_probe`'s answer decides the cited
`match fe.find? Tn with | some (.indInfo cvT caps) => … | _ => …`: the probe's
`Option` and the cited `match` agree arm by arm. -/
theorem ind_find_eq {α : Type} {F : Option ConLeche.ConstantInfo}
    {g : ConLeche.ConstantVal → ConLeche.IndCaps → α} {z : α}
    {o : Option (ConLeche.ConstantVal × ConLeche.IndCaps)}
    (h : o = match F with | some (.indInfo cv c) => some (cv, c) | _ => none) :
    (match F with | some (.indInfo cv c) => g cv c | _ => z)
      = (match o with | some p => g p.1 p.2 | none => z) := by
  subst h
  match F with
  | none => rfl
  | some (.indInfo cv c) => rfl
  | some (.axiomInfo _) | some (.defnInfo _ _ _) | some (.thmInfo _ _)
  | some (.ctorInfo _ _ _) | some (.recInfo _ _ _ _) | some (.projInfo _) => rfl


/-! ## One missing `Expr` inversion

`Refine/CoreKGuards.lean` has `wf_const_inv`/`wf_sort_inv`/`wf_app_inv`; the
kind-by-kind `match` of `defeq_struct_i` needs all ten arms, so here is the
inversion in one piece.  **To be moved to `Refine/Expr.lean`** beside the other
`*_inv` lemmas. -/

/-- What a well-formed node's kind carries: one clause per `ExprWF`
constructor. -/
def KindWF : expr.ExprKind → Prop
  | .Bvar _ => True
  | .Fvar _ ty => ExprWF ty
  | .Sort u => LevelWF u
  | .Const n us => NameWF n ∧ LevelsWF us
  | .App f a => ExprWF f ∧ ExprWF a
  | .Lam ty bo m => ExprWF ty ∧ ExprWF bo ∧ BinderMetaWF m
  | .ForallE ty bo m => ExprWF ty ∧ ExprWF bo ∧ BinderMetaWF m
  | .LetE ty v bo => ExprWF ty ∧ ExprWF v ∧ ExprWF bo
  | .Lit l => LiteralWF l
  | .Proj s _ x => NameWF s ∧ ExprWF x

/-- Casing on `e._0.kind` throws the `ExprWF` derivation away; this hands it
back, arm by arm. -/
theorem wf_kind_inv {e : expr.Expr} (he : ExprWF e) {d : Std.U64}
    {k : expr.ExprKind} (hk : e = .mk (.mk d k)) : KindWF k := by
  cases he with
  | @bvar i _ h1 =>
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.bvar_inv h1
    simp only [expr.Expr.mk.injEq, expr.ExprNode.mk.injEq] at hk
    obtain ⟨-, rfl⟩ := hk; trivial
  | @fvar idx ty _ hty h1 =>
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.fvar_inv h1
    simp only [expr.Expr.mk.injEq, expr.ExprNode.mk.injEq] at hk
    obtain ⟨-, rfl⟩ := hk; exact hty
  | @sort u _ hu h1 =>
    obtain ⟨d1, bb, -, rfl, -, -, -⟩ := Expr.sort_inv h1
    simp only [expr.Expr.mk.injEq, expr.ExprNode.mk.injEq] at hk
    obtain ⟨-, rfl⟩ := hk; exact hu
  | @mk_const n us _ hn hus h1 =>
    obtain ⟨d1, bb, -, rfl, -, -, -⟩ := Expr.mk_const_inv h1
    simp only [expr.Expr.mk.injEq, expr.ExprNode.mk.injEq] at hk
    obtain ⟨-, rfl⟩ := hk; exact ⟨hn, hus⟩
  | @app f aa _ hf ha h1 =>
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.app_inv h1
    simp only [expr.Expr.mk.injEq, expr.ExprNode.mk.injEq] at hk
    obtain ⟨-, rfl⟩ := hk; exact ⟨hf, ha⟩
  | @lam ty bo m _ hty hbo hm h1 =>
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.lam_inv h1
    simp only [expr.Expr.mk.injEq, expr.ExprNode.mk.injEq] at hk
    obtain ⟨-, rfl⟩ := hk; exact ⟨hty, hbo, hm⟩
  | @forall_e ty bo m _ hty hbo hm h1 =>
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.forall_e_inv h1
    simp only [expr.Expr.mk.injEq, expr.ExprNode.mk.injEq] at hk
    obtain ⟨-, rfl⟩ := hk; exact ⟨hty, hbo, hm⟩
  | @let_e ty v bo _ hty hv hbo h1 =>
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.let_e_inv h1
    simp only [expr.Expr.mk.injEq, expr.ExprNode.mk.injEq] at hk
    obtain ⟨-, rfl⟩ := hk; exact ⟨hty, hv, hbo⟩
  | @lit l _ hl h1 =>
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.lit_inv h1
    simp only [expr.Expr.mk.injEq, expr.ExprNode.mk.injEq] at hk
    obtain ⟨-, rfl⟩ := hk; exact hl
  | @proj sn i x _ hs hx h1 =>
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.proj_inv h1
    simp only [expr.Expr.mk.injEq, expr.ExprNode.mk.injEq] at hk
    obtain ⟨-, rfl⟩ := hk; exact ⟨hs, hx⟩

/-! ## The structural case analysis

`defeqStepI` (`ConLeche/Cached/CoreC.lean:1456-1614`) is one `do` block, which
the port splits into seven functions.  `defeq_struct_i` (`core_c.rs:4061`) is
its **`| false, false =>` arm** — neither head unfoldable, so `match a', b'
with …` decides structurally — and `defeq_apps_i`/`defeq_binders_i`
(`core_c.rs:4253`/`:4167`) are two arms inside it.  The three definitions below
are verbatim transcriptions of those three subterms, and `defeqStepI_eq` is the
cited definition with all three named: it is `rfl`, so the naming assumes
nothing. -/

section
open ConLeche ConLeche.Cached

/-- `ConLeche/Cached/CoreC.lean:1590-1602` — `defeqStepI`'s `.app`/`.app` arm,
named (the port's `defeq_apps_i`). -/
def defeqAppsL (mode : CheckMode) (r : CoreFnsI) (fe : FEnv) (depth : Nat)
    (a' b' : Expr) : CheckCM Bool := do
  let as₁ ← pure (Expr.getAppArgsC a')
  let as₂ ← pure (Expr.getAppArgsC b')
  if as₁.length = as₂.length then do
    let h₁ ← pure (Expr.getAppFn a')
    let h₂ ← pure (Expr.getAppFn b')
    if ← r.defeq depth h₁ h₂ then do
      if ← defEqListI r fe depth as₁ as₂ then pure true
      else stuckIrrelI mode r fe depth a' b'
    else stuckIrrelI mode r fe depth a' b'
  else stuckIrrelI mode r fe depth a' b'

/-- `ConLeche/Cached/CoreC.lean:1571-1589` — `defeqStepI`'s two binder arms,
named (the port's `defeq_binders_i`): they are byte-identical apart from the
message tag, which `isForall` selects. -/
def defeqBindersL (mode : CheckMode) (r : CoreFnsI) (fe : FEnv) (depth : Nat)
    (ty₁ body₁ : Expr) (m₁ : BinderMeta) (ty₂ body₂ : Expr) (m₂ : BinderMeta)
    (isForall : Bool) : CheckCM Bool := do
  unless ← r.defeq depth ty₁ ty₂ do return false
  let fv ← pure (Expr.fvar depth ty₂)
  let b₁ ← inst1M body₁ fv
  let b₂ ← inst1M body₂ fv
  unless ← r.defeq (depth + 1) b₁ b₂ do return false
  if mode.verifiedChecks && !(m₁.pw == m₂.pw) then
    throw (.notImplemented
      (if isForall then "sort-annotation mismatch (defeq-forall)"
        else "sort-annotation mismatch (defeq-lam)"))
  pure true

/-- `ConLeche/Cached/CoreC.lean:1520-1614` — `defeqStepI`'s `| false, false =>`
arm, named (the port's `defeq_struct_i`). -/
def defeqStructL (mode : CheckMode) (r : CoreFnsI) (fe : FEnv) (depth : Nat)
    (a' b' : Expr) : CheckCM Bool := do
  match a', b' with
  | .sort u, .sort v => do
    liftFueled "level comparison" (← isEquivLM u v)
  | .lit l₁, .lit l₂ => pure (l₁ == l₂)
  | .lit (.natVal n), .const c us =>
    if (← pure (c == natZeroName)) ∧ us = [] then pure (n == 0)
    else stuckIrrelI mode r fe depth a' b'
  | .const c us, .lit (.natVal n) =>
    if (← pure (c == natZeroName)) ∧ us = [] then pure (n == 0)
    else stuckIrrelI mode r fe depth a' b'
  | .lit (.natVal nn), .app f x => do
    match nn, f with
    | k + 1, .const c [] =>
      if ← pure (c == natSuccName) then do
        let kl ← pure (Expr.lit (.natVal k))
        r.defeq depth kl x
      else stuckIrrelI mode r fe depth a' b'
    | _, _ => stuckIrrelI mode r fe depth a' b'
  | .app f x, .lit (.natVal nn) => do
    match nn, f with
    | k + 1, .const c [] =>
      if ← pure (c == natSuccName) then do
        let kl ← pure (Expr.lit (.natVal k))
        r.defeq depth x kl
      else stuckIrrelI mode r fe depth a' b'
    | _, _ => stuckIrrelI mode r fe depth a' b'
  | .lit (.strVal s), .app fO _x => do
    match fO with
    | .const cO usO =>
      if (← pure (cO == stringOfListName)) ∧ usO = [] ∧ strLitSupportedF fe then do
        let sc ← pure (strLitToConstructor s)
        r.defeq depth sc b'
      else stuckIrrelI mode r fe depth a' b'
    | _ => stuckIrrelI mode r fe depth a' b'
  | .app fO _x, .lit (.strVal s) => do
    match fO with
    | .const cO usO =>
      if (← pure (cO == stringOfListName)) ∧ usO = [] ∧ strLitSupportedF fe then do
        let sc ← pure (strLitToConstructor s)
        r.defeq depth a' sc
      else stuckIrrelI mode r fe depth a' b'
    | _ => stuckIrrelI mode r fe depth a' b'
  | .fvar i _, .fvar j _ =>
    if i == j then pure true
    else stuckIrrelI mode r fe depth a' b'
  | .const n us, .const n' us' =>
    if n = n' then do
      if ← liftFueled "level comparison" (← isEquivListLM us us') then
        pure true
      else stuckIrrelI mode r fe depth a' b'
    else stuckIrrelI mode r fe depth a' b'
  | .forallE ty₁ body₁ m₁, .forallE ty₂ body₂ m₂ =>
    defeqBindersL mode r fe depth ty₁ body₁ m₁ ty₂ body₂ m₂ true
  | .lam ty₁ body₁ m₁, .lam ty₂ body₂ m₂ =>
    defeqBindersL mode r fe depth ty₁ body₁ m₁ ty₂ body₂ m₂ false
  | .app _f₁ _a₁, .app _f₂ _a₂ => defeqAppsL mode r fe depth a' b'
  | .proj s₁ i₁ e₁, .proj s₂ i₂ e₂ => do
    if s₁ == s₂ && i₁ == i₂ then do
      if ← r.defeq depth e₁ e₂ then pure true
      else stuckIrrelI mode r fe depth a' b'
    else stuckIrrelI mode r fe depth a' b'
  | .lam ty₁ body₁ m₁, _ => do
    if ← etaCertI mode r fe depth ty₁ body₁ m₁ b' then pure true
    else stuckIrrelI mode r fe depth a' b'
  | _, .lam ty₂ body₂ m₂ => do
    if ← etaCertI mode r fe depth ty₂ body₂ m₂ a' then pure true
    else stuckIrrelI mode r fe depth a' b'
  | _, _ => stuckIrrelI mode r fe depth a' b'

/-- `ConLeche/Cached/CoreC.lean:1456-1614` — the cited definition with its
three port-split arms named.  `rfl`. -/
theorem defeqStepI_eq (mode : CheckMode) (r : CoreFnsI) (fe : FEnv) (depth : Nat)
    (k : Bool → Expr → Expr → CheckCM Bool) (pi : Bool) (a b : Expr) :
    defeqStepI mode r fe depth k pi a b = (do
  if a == b then pure true else
  -- the eq-true shortcut (E2), as in the spec
  let bt ← pure (Expr.isBoolTrue b)
  let af ← pure (Expr.hasFvar a)
  if ← (if pi && bt && !af then boolTrueShortcutI r depth a
      else pure false) then pure true else
  let a' ← r.whnfCore depth a
  let b' ← r.whnfCore depth b
  if a' == b' then pure true else
  -- proof irrelevance hoisted before lazy delta, as in the spec
  -- (and the official kernel); the `Prop` branch with the fast arms
  -- (task #168, Option U) — once per entry (`pi`; the spec's D3 note)
  let qp ← pure (Expr.quickPair a' b')
  if ← (if pi && !qp then propIrrelI r fe depth a' b' else pure false) then
    pure true else
  -- Literal folding only when both sides are fvar-free, mirroring
  -- the official kernel (`type_checker.cpp`, `lazy_delta_reduction`)
  -- and lean4lean (`TypeChecker.lean:782`); see `defeqBody` for the
  -- full rationale.  `hasFvarI` is an `O(1)` read of the eager
  -- per-node fvar-range array.
  let fold ← pure (!Expr.hasFvar a' && !Expr.hasFvar b')
  match ← (if fold then reduceNatI r fe depth a' else pure none) with
  | some a₂ => k true a₂ b'
  | none =>
  match ← (if fold then reduceNatI r fe depth b' else pure none) with
  | some b₂ => k true a' b₂
  | none =>
  -- lazy delta, decision before materialization; see `defeqBody`
  match ← pure (unfoldableHeadC fe a'),
      ← pure (unfoldableHeadC fe b') with
  | true, false =>
    match ← unfoldDefinitionI fe a' with
    | some a₂ => k false a₂ b'
    | none => pure false
  | false, true =>
    match ← unfoldDefinitionI fe b' with
    | some b₂ => k false a' b₂
    | none => pure false
  | true, true => do
    let ha ← pure (headHintC fe a')
    let hb ← pure (headHintC fe b')
    if ReducibilityHint.lt hb ha then
      match ← unfoldDefinitionI fe a' with
      | some a₂ => k false a₂ b'
      | none => pure false
    else if ReducibilityHint.lt ha hb then
      match ← unfoldDefinitionI fe b' with
      | some b₂ => k false a' b₂
      | none => pure false
    else if ReducibilityHint.sameRegular ha hb &&
        (← pure (sameConstHeadsC a' b')) then do
      if ← defeqSpineI r fe depth a' b' then pure true
      else
        match ← unfoldDefinitionI fe a', ← unfoldDefinitionI fe b' with
        | some a₂, some b₂ => k false a₂ b₂
        | _, _ => pure false
    else
      match ← unfoldDefinitionI fe a', ← unfoldDefinitionI fe b' with
      | some a₂, some b₂ => k false a₂ b₂
      | _, _ => pure false
  | false, false => defeqStructL mode r fe depth a' b') := rfl

end


/-- `core_k::lift_fueled` on the success constructor: the fuelled `Option` was
`some`.  (`Refine/CoreKVec.lean`'s `lift_fueled_refines` says the same at
`CheckM`; the arms below need it at `CheckCM`, where `liftFueled … (some b)` is
`pure b` by `rfl`.) -/
theorem lift_fueled_some {o : Option Bool} {bb : Bool}
    (h : core_k.lift_fueled o = ok (.Ok bb)) : o = some bb := by
  cases o with
  | none =>
    simp only [core_k.lift_fueled, bind_eq_ok_iff] at h
    obtain ⟨s, -, v, -, ce, -, hr⟩ := h
    simp at hr
  | some x =>
    simp only [core_k.lift_fueled, Result.ok.injEq] at h
    injection h with hx
    rw [hx]

/-! ## The failure half: transport, the error constructors, and `throw`

Task #67 states each lemma over the Rust computation's whole outcome
(`Refine/State.lean`'s `Out`), so the arms below each carry a failure half
beside the accept one.  A handful of small facts carry all of them:

* `out_of_eq` — the con-leche side of an arm is the callee's action after the
  `do` block has been reduced to it, so an `Out` transports along that
  equation.  This is the tail-call move, and the reason a tail-call arm is
  *shorter* than it was: the equation is proved once, for both outcomes.
* `internal_inv`/`not_implemented_inv` — `core_types::internal v` is the
  `Internal` constructor, so a Rust `throw` site names the kind the
  full-outcome statement compares.  (**To be hoisted into `Refine/Abs.lean`**
  with the other files' copies at the end of the campaign.)
* `checkCM_throw_apply` — `Shape.lean`'s plumbing `simp` set has no
  `MonadExcept` instance, so a con-leche `throw` has to be told what it is.
  Stated on the *applied* form, since `StateT.run` is already in the set and
  fires first.
* `lift_fueled_err`/`errSim_liftFueled_none` — the fuel-exhaustion pair of the
  two level-comparison arms, read off `core_k::lift_fueled` and the cited
  `liftFueled`. -/

/-- `Out` transported along an equation on the con-leche side. -/
private theorem out_of_eq {α β : Type} {A : α → β} {WF : α → Prop}
    {o : core.result.Result α core_types.CheckError} {st' : cached.state_c.CState}
    {x y : Except ConLeche.CheckError (β × ConLeche.Cached.CState)}
    (h : Out A WF o st' x) (hxy : y = x) : Out A WF o st' y := hxy ▸ h

/-- `core_types::internal` builds the `Internal` constructor. -/
private theorem internal_inv {v : alloc.vec.Vec Std.U32} {ce : core_types.CheckError}
    (h : core_types.internal v = ok ce) : ce = .Internal v := by
  rw [core_types.internal] at h
  exact (Result.ok_injective h).symm

/-- `core_types::not_implemented` builds the `NotImplemented` constructor. -/
private theorem not_implemented_inv {v : alloc.vec.Vec Std.U32}
    {ce : core_types.CheckError} (h : core_types.not_implemented v = ok ce) :
    ce = .NotImplemented v := by
  rw [core_types.not_implemented] at h
  exact (Result.ok_injective h).symm

/-- A con-leche `throw`, applied to the state. -/
@[local simp] private theorem checkCM_throw_apply {β : Type} (le : ConLeche.CheckError)
    (lst : ConLeche.Cached.CState) :
    (throw le : ConLeche.Cached.CheckCM β) lst = Except.error le := rfl

/-- `core_k::lift_fueled` on the failure constructor: the fuelled `Option` was
`none`, and the error is the `internal` kind con-leche's `liftFueled` throws
at (`ConLeche/Kernel/Core.lean:109-111`). -/
private theorem lift_fueled_err {o : Option Bool} {ce : core_types.CheckError}
    (h : core_k.lift_fueled o = ok (.Err ce)) :
    o = none ∧ absErrKind ce = some .internal := by
  cases o with
  | some x => simp [core_k.lift_fueled] at h
  | none =>
    refine ⟨rfl, ?_⟩
    simp only [core_k.lift_fueled, bind_eq_ok_iff] at h
    obtain ⟨s, -, v, -, ce', hce, hr⟩ := h
    simp only [Result.ok.injEq, core.result.Result.Err.injEq] at hr
    subst hr
    rw [internal_inv hce]
    rfl

/-- **`liftFueled` at `none` throws**, at the `internal` kind
(`ConLeche/Kernel/Core.lean:109-111`), which is exactly what
`core_k::lift_fueled`'s `Err` arm builds — so a fuel-exhausted level
comparison is mirrored, message and all. -/
private theorem errSim_liftFueled_none {e : core_types.CheckError}
    (hk : absErrKind e = some .internal) (what : String)
    (lst : ConLeche.Cached.CState) :
    ErrSim e ((ConLeche.liftFueled what (none : Option Bool) :
      ConLeche.Cached.CheckCM Bool).run lst) :=
  ErrSim.mk (le := .internal s!"fuel exhausted: {what}") rfl hk

/-- `expr::literal_nat` builds the `NatVal` literal (`ron::ptr` is the
identity in the model). -/
@[local simp] theorem literal_nat_eq' (n : ron.nat.Nat) :
    expr.literal_nat n = ok (.NatVal n) := by
  simp [expr.literal_nat]

/-- `core_k::succ_of`'s answer decides the cited `match nn, f with | k + 1,
.const c [] => … | _, _ => …` of the `Nat`-literal-against-`Nat.succ` arms.
Stated in *this* module's matcher, the one `defeqStructL` uses; see the module
note on why `succ_of_refines`'s own copy has to be restated before use. -/
theorem succ_match_eq {α : Type} {n : Nat} {f : ConLeche.Expr}
    {g : Nat → α} {z : α} :
    (match n, f with
      | k + 1, .const c [] => if (c == ConLeche.natSuccName) = true then g k else z
      | _, _ => z)
      = (match n, f with
        | k + 1, .const c [] => if c = ConLeche.natSuccName then some k else none
        | _, _ => (none : Option Nat)).elim z g := by
  have key : ∀ (c : ConLeche.Name) (k : Nat),
      (if (c == ConLeche.natSuccName) = true then g k else z)
        = Option.elim (if c = ConLeche.natSuccName then some k else none) z g := by
    intro c k
    have hb : (c == ConLeche.natSuccName) = true ↔ c = ConLeche.natSuccName := by simp
    by_cases hc : c = ConLeche.natSuccName
    · rw [if_pos (hb.mpr hc), if_pos hc]; rfl
    · rw [if_neg (fun hx => hc (hb.mp hx)), if_neg hc]; rfl
  match n, f with
  | 0, _ => rfl
  | _ + 1, .bvar _ | _ + 1, .fvar _ _ | _ + 1, .sort _ | _ + 1, .app _ _
  | _ + 1, .lam _ _ _ | _ + 1, .forallE _ _ _ | _ + 1, .letE _ _ _
  | _ + 1, .lit _ | _ + 1, .proj _ _ _ => rfl
  | _ + 1, .const _ (_ :: _) => rfl
  | k + 1, .const c [] => exact key c k

/-- `core_k::str_expansion_fires`'s answer decides the cited
`match fO with | .const cO usO => if … then … else … | _ => …` of the
string-literal expansion arms.  As with `succ_match_eq`, the `match` here is
this module's matcher, so `str_expansion_fires_refines`'s answer is restated
in it at each use site. -/
theorem str_match_eq {α : Type} {f : ConLeche.Expr} {lfe : ConLeche.FEnv} {g z : α} :
    (match f with
      | .const cO usO =>
        if (cO == ConLeche.stringOfListName) = true ∧ usO = [] ∧
            ConLeche.strLitSupportedF lfe = true then g else z
      | _ => z)
      = (if (match f with
          | .const cO usO => decide (cO = ConLeche.stringOfListName) && decide (usO = []) &&
              ConLeche.strLitSupportedF lfe
          | _ => false) = true then g else z) := by
  cases f with
  | const cO usO =>
    by_cases hc : cO = ConLeche.stringOfListName
    · subst hc; simp
    · simp [hc]
  | _ => simp

/-! ## The foreign callees

Five helpers of *other* arms files, each field verbatim the statement that
file's own `<fn>_refines` has. -/

/-- The two `Arms/Certs.lean` helpers this file calls — everything
`struct_eta_cert_i` and `struct_unit_cert_i` need, and nothing that comes back
from `Arms/DefEq.lean`.

**Task #61 split the record here.**  `Arms/DefEq.lean`'s
`stuck_irrel_i` reaches `struct_eta_cert_i`/`struct_unit_cert_i`, and
`defeq_struct_i` reaches `stuck_irrel_i`, so asking *both* files' theorems for
the whole other file's `Deps` record made the two mutually unconstructible even
though the call graph is acyclic (DESIGN.md, task #55's second packaging
cycle).  Splitting along that order — this record for the certificates,
`DefEqStructDeps` below for `defeq_struct_i` — closes it, with no statement
changed. -/
structure DefEqStructDepsA (mode : env.CheckMode) (fuel : Std.U64) : Prop where
  /-- `core_c.rs:839` — `structEtaCertWithI` (`CoreC.lean:387`). -/
  structEtaCertWith : ∀ (d : Std.U64) {a b wtb : expr.Expr},
    ExprWF a → ExprWF b → ExprWF wtb →
    Sim id (fun _ => True)
      (fun st fe => cached.core_c.struct_eta_cert_with_i mode fuel st fe d a b wtb)
      (fun lfe => ConLeche.Cached.structEtaCertWithI (absMode mode)
        (knot mode lfe fuel.val) lfe d.val (absExpr a) (absExpr b) (absExpr wtb))
  /-- `core_c.rs:415` — `iotaCertsI` (`CoreC.lean:337`). -/
  iotaCerts : ∀ (d : Std.U64) (lic : Bool) {ty : expr.Expr}
    {args : alloc.vec.Vec expr.Expr}, ExprWF ty → ExprsWF args →
    Sim id (fun _ => True)
      (fun st fe => cached.core_c.iota_certs_i mode fuel st fe d lic ty args)
      (fun lfe => ConLeche.Cached.iotaCertsI (knot mode lfe fuel.val) lfe d.val lic
        (absExpr ty) (absExprs args))
/-- The cross-file helpers `defeq_struct_i` calls, in full: the two of
`DefEqStructDepsA` and the three of `Arms/DefEq.lean` that do not themselves
go through `defeq_struct_i`. -/
structure DefEqStructDeps (mode : env.CheckMode) (fuel : Std.U64) : Prop
    extends DefEqStructDepsA mode fuel where
  /-- `core_c.rs:4253` — `defeqStepI`'s `.app`/`.app` arm, `defeqAppsL`. -/
  defeqApps : ∀ (d : Std.U64) {a b : expr.Expr}, ExprWF a → ExprWF b →
    Sim id (fun _ => True)
      (fun st fe => cached.core_c.defeq_apps_i mode fuel st fe d a b)
      (fun lfe => defeqAppsL (absMode mode) (knot mode lfe fuel.val) lfe d.val
        (absExpr a) (absExpr b))
  /-- `core_c.rs:4195` — `defeqStepI`'s two binder arms, `defeqBindersL`. -/
  defeqBinders : ∀ (d : Std.U64) (isForall : Bool) {t1 b1 t2 b2 : expr.Expr}
    {m1 m2 : expr.BinderMeta}, ExprWF t1 → ExprWF b1 → BinderMetaWF m1 →
    ExprWF t2 → ExprWF b2 → BinderMetaWF m2 →
    Sim id (fun _ => True)
      (fun st fe =>
        cached.core_c.defeq_binders_i mode fuel st fe d t1 b1 m1 t2 b2 m2 isForall)
      (fun lfe => defeqBindersL (absMode mode) (knot mode lfe fuel.val) lfe d.val
        (absExpr t1) (absExpr b1) (absBinderMeta m1) (absExpr t2) (absExpr b2)
        (absBinderMeta m2) isForall)
  /-- `core_c.rs:1221` — `stuckIrrelI` (`CoreC.lean:536`). -/
  stuckIrrel : ∀ (d : Std.U64) {a b : expr.Expr}, ExprWF a → ExprWF b →
    Sim id (fun _ => True)
      (fun st fe => cached.core_c.stuck_irrel_i mode fuel st fe d a b)
      (fun lfe => ConLeche.Cached.stuckIrrelI (absMode mode) (knot mode lfe fuel.val)
        lfe d.val (absExpr a) (absExpr b))

section
variable {mode : env.CheckMode} {fuel : Std.U64}

/-! ## The structure-η certificate -/

/-- `ConLeche/Cached/CoreC.lean:476-484` — **`struct_eta_cert_i` refines
`structEtaCertI`** (`core_c.rs:1034`): the constructor-shape gate first (the
divergence audit's D13), and only then `b`'s type, whnf'd, handed to
`structEtaCertWithI`. -/
theorem struct_eta_cert_i_refines (hw : Wrappers mode fuel)
    (hd : DefEqStructDepsA mode fuel) (d : Std.U64) {a b : expr.Expr}
    (ha : ExprWF a) (hb : ExprWF b) :
    Sim id (fun _ => True)
      (fun st fe => cached.core_c.struct_eta_cert_i mode fuel st fe d a b)
      (fun lfe => ConLeche.Cached.structEtaCertI (absMode mode)
        (knot mode lfe fuel.val) lfe d.val (absExpr a) (absExpr b)) := by
  intro fe lfe hfe hfrel st o st' hwf hok lst hrel
  unfold cached.core_c.struct_eta_cert_i at hok
  res_step hok
  obtain ⟨sh, hsh, hok⟩ := hok
  have hshabs : sh = ConLeche.Cached.etaCtorShapeC lfe (absExpr a) :=
    CoreK.eta_ctor_shape_refines CoreK.envFacts (FindAgree.of_rel hfrel hfe) ha hsh
  cases sh with
  | false =>
    simp only [Bool.false_eq_true, if_false, Result.ok.injEq, Prod.mk.injEq] at hok
    obtain ⟨rfl, rfl⟩ := hok
    exact ⟨lst, by simp [ConLeche.Cached.structEtaCertI, ← hshabs], hrel, hwf, trivial⟩
  | true =>
    simp only [if_true] at hok
    res_step hok
    obtain ⟨⟨r0, st1⟩, h1, hok⟩ := hok
    cases r0 with
    | Err err =>
      simp at hok
      obtain ⟨rfl, rfl⟩ := hok
      refine Out.err (ErrSim.trans
        ((hw.inferIOSim d hb).apply_err hwf hfe h1 hrel hfrel) ?_)
      intro le hle
      simp only [StateT.run] at hle
      simp [ConLeche.Cached.structEtaCertI, ← hshabs, hle]
    | Ok tb =>
      obtain ⟨lst1, hrun1, hrel1, hwf1, htbWF⟩ :=
        (hw.inferIOSim d hb).apply hwf hfe h1 hrel hfrel
      simp only [StateT.run] at hrun1
      res_step hok
      obtain ⟨⟨r1, st2⟩, h2, hok⟩ := hok
      cases r1 with
      | Err err =>
        simp at hok
        obtain ⟨rfl, rfl⟩ := hok
        refine Out.err (ErrSim.trans
          ((hw.whnfSim d htbWF).apply_err hwf1 hfe h2 hrel1 hfrel) ?_)
        intro le hle
        simp only [StateT.run] at hle
        simp [ConLeche.Cached.structEtaCertI, ← hshabs, hrun1, hle]
      | Ok wtb =>
        obtain ⟨lst2, hrun2, hrel2, hwf2, hwtbWF⟩ :=
          (hw.whnfSim d htbWF).apply hwf1 hfe h2 hrel1 hfrel
        simp only [StateT.run] at hrun2
        refine out_of_eq ((hd.structEtaCertWith d ha hb hwtbWF)
          fe lfe hfe hfrel st2 o st' hwf2 hok lst2 hrel2) ?_
        simp [ConLeche.Cached.structEtaCertI, ← hshabs, hrun1, hrun2]

/-! ## The unit-likeness certificate

`structUnitCertI` (`ConLeche/Cached/CoreC.lean:487-512`) is one `do` block; the
port splits its state-touching tail into `struct_unit_steps_i`
(`core_c.rs:1105`).  `structUnitStepsL` names that tail and
`structUnitCertI_eq` — `rfl` — is the cited definition with it named. -/

/-- `ConLeche/Cached/CoreC.lean:501-510` — `structUnitCertI`'s tail, named:
`b`'s reduced type against `a`'s, then the type-former telescope certificate
under `certAtI`. -/
def structUnitStepsL (mode : ConLeche.CheckMode) (r : ConLeche.Cached.CoreFnsI)
    (fe : ConLeche.FEnv) (depth : Nat) (wta b : ConLeche.Expr)
    (T Tn : ConLeche.Name) (us' : List ConLeche.Level)
    (targs : List ConLeche.Expr) : ConLeche.Cached.CheckCM Bool := do
  let tb ← r.inferIO depth b
  let wtb ← r.whnf depth tb
  if ← r.defeq depth wta wtb then do
    let tyT ← ConLeche.Cached.constTyAtM fe T Tn us'
    ConLeche.Cached.certAtI mode (ConLeche.Cached.iotaCertsI r fe depth false tyT targs)
  else pure false

/-- `ConLeche/Cached/CoreC.lean:487-512` — the cited definition is its shape
gate around `structUnitStepsL`.  `rfl`. -/
theorem structUnitCertI_eq (mode : ConLeche.CheckMode) (r : ConLeche.Cached.CoreFnsI)
    (fe : ConLeche.FEnv) (depth : Nat) (a b : ConLeche.Expr) :
    ConLeche.Cached.structUnitCertI mode r fe depth a b = (do
      let ta ← r.inferIO depth a
      let wta ← r.whnf depth ta
      match ConLeche.Expr.getAppFn wta with
      | .const T us' => do
        let Tn ← pure T
        match fe.find? Tn with
        | some (.indInfo cvT caps) => do
          let targs ← pure (ConLeche.Expr.getAppArgsC wta)
          if caps.unitlike = true ∧
              ConLeche.reservedBasisNames.contains Tn = false ∧
              targs.length = caps.unitParams ∧
              us'.length = cvT.levelParams.length then
            structUnitStepsL mode r fe depth wta b T Tn us' targs
          else pure false
        | _ => pure false
      | _ => pure false) := rfl


/-- `ConLeche/Cached/CoreC.lean:501-510` — **`struct_unit_steps_i` refines
`structUnitStepsL`** (`core_c.rs:1105`), `structUnitCertI`'s state-touching
tail.

The cited tail runs `constTyAtM` *before* `certAtI mode`, so at every mode it
reads (and memoises, and may `throw` on) the type-former's type; task #61 made
the port's read ungated too, so `StateC.const_ty_at_m_refines` applies once,
above the mode split, and both branches of `certAtI` continue from the state it
leaves. -/
theorem struct_unit_steps_i_refines (hw : Wrappers mode fuel)
    (hd : DefEqStructDepsA mode fuel) (d : Std.U64) {wta b : expr.Expr}
    {t : name.Name} {us2 : alloc.vec.Vec level.Level}
    {targs : alloc.vec.Vec expr.Expr} (hwta : ExprWF wta) (hb : ExprWF b)
    (ht : NameWF t) (hus : LevelsWF us2) (htargs : ExprsWF targs) :
    Sim id (fun _ => True)
      (fun st fe => cached.core_c.struct_unit_steps_i mode fuel st fe d wta b t us2 targs)
      (fun lfe => structUnitStepsL (absMode mode) (knot mode lfe fuel.val) lfe d.val
        (absExpr wta) (absExpr b) (absName t) (absName t) (absLevels us2)
        (absExprs targs)) := by
  intro fe lfe hfe hfrel st o st' hwf hok lst hrel
  unfold cached.core_c.struct_unit_steps_i at hok
  res_step hok
  obtain ⟨⟨r0, st1⟩, h1, hok⟩ := hok
  cases r0 with
  | Err err =>
    simp at hok
    obtain ⟨rfl, rfl⟩ := hok
    refine Out.err (ErrSim.trans
      ((hw.inferIOSim d hb).apply_err hwf hfe h1 hrel hfrel) ?_)
    intro le hle
    simp only [StateT.run] at hle
    simp [structUnitStepsL, hle]
  | Ok tb =>
    obtain ⟨lst1, hrun1, hrel1, hwf1, htbWF⟩ :=
      (hw.inferIOSim d hb).apply hwf hfe h1 hrel hfrel
    simp only [StateT.run] at hrun1
    res_step hok
    obtain ⟨⟨r1, st2⟩, h2, hok⟩ := hok
    cases r1 with
    | Err err =>
      simp at hok
      obtain ⟨rfl, rfl⟩ := hok
      refine Out.err (ErrSim.trans
        ((hw.whnfSim d htbWF).apply_err hwf1 hfe h2 hrel1 hfrel) ?_)
      intro le hle
      simp only [StateT.run] at hle
      simp [structUnitStepsL, hrun1, hle]
    | Ok wtb =>
      obtain ⟨lst2, hrun2, hrel2, hwf2, hwtbWF⟩ :=
        (hw.whnfSim d htbWF).apply hwf1 hfe h2 hrel1 hfrel
      simp only [StateT.run] at hrun2
      res_step hok
      obtain ⟨⟨r2, st3⟩, h3, hok⟩ := hok
      cases r2 with
      | Err err =>
        simp at hok
        obtain ⟨rfl, rfl⟩ := hok
        refine Out.err (ErrSim.trans
          ((hw.defeqSim d hwta hwtbWF).apply_err hwf2 hfe h3 hrel2 hfrel) ?_)
        intro le hle
        simp only [StateT.run] at hle
        simp [structUnitStepsL, hrun1, hrun2, hle]
      | Ok bd =>
        obtain ⟨lst3, hrun3, hrel3, hwf3, -⟩ :=
          (hw.defeqSim d hwta hwtbWF).apply hwf2 hfe h3 hrel2 hfrel
        simp only [StateT.run, id_eq] at hrun3
        cases bd with
        | false =>
          simp only [Bool.false_eq_true, if_false, Result.ok.injEq, Prod.mk.injEq] at hok
          obtain ⟨rfl, rfl⟩ := hok
          exact ⟨lst3, by simp [structUnitStepsL, hrun1, hrun2, hrun3], hrel3, hwf3, trivial⟩
        | true =>
          simp only [if_true] at hok
          res_step hok
          obtain ⟨⟨r3, st4⟩, h4, hok⟩ := hok
          cases r3 with
          | Err err =>
            simp at hok
            obtain ⟨rfl, rfl⟩ := hok
            refine Out.err (ErrSim.trans
              (StateC.const_ty_at_m_err hwf3 hfe ht hus h4 lst3 lfe hrel3 hfrel
                (absName t)) ?_)
            intro le hle
            simp only [StateT.run] at hle
            simp [structUnitStepsL, hrun1, hrun2, hrun3, hle]
          | Ok tty =>
            obtain ⟨lst4, hrun4, hrel4, hwf4, httyWF⟩ :=
              StateC.const_ty_at_m_refines StateC.instLevelParamsRefines hwf3 hfe ht
                hus h4 lst3 lfe hrel3 hfrel (absName t)
            simp only [StateT.run] at hrun4
            res_step hok
            obtain ⟨cb, hcb, hok⟩ := hok
            have hcbabs : cb = (absMode mode).certs := Env.certs_refines hcb
            cases cb with
            | false =>
              simp only [Bool.false_eq_true, if_false, Result.ok.injEq, Prod.mk.injEq] at hok
              obtain ⟨rfl, rfl⟩ := hok
              refine ⟨lst4, ?_, hrel4, hwf4, trivial⟩
              simp only [structUnitStepsL, ConLeche.Cached.certAtI]
              simp [hrun1, hrun2, hrun3, hrun4, ← hcbabs]
            | true =>
              simp only [if_true] at hok
              refine out_of_eq ((hd.iotaCerts d false httyWF htargs)
                fe lfe hfe hfrel st4 o st' hwf4 hok lst4 hrel4) ?_
              simp only [structUnitStepsL, ConLeche.Cached.certAtI]
              simp [hrun1, hrun2, hrun3, hrun4, ← hcbabs]

/-- `ConLeche/Cached/CoreC.lean:487-512` — **`struct_unit_cert_i` refines
`structUnitCertI`** (`core_c.rs:1062`): `a`'s reduced type must be a stored
unit-like family applied to its parameters, and then `structUnitStepsL`. -/
theorem struct_unit_cert_i_refines (hw : Wrappers mode fuel)
    (hd : DefEqStructDepsA mode fuel) (d : Std.U64) {a b : expr.Expr}
    (ha : ExprWF a) (hb : ExprWF b) :
    Sim id (fun _ => True)
      (fun st fe => cached.core_c.struct_unit_cert_i mode fuel st fe d a b)
      (fun lfe => ConLeche.Cached.structUnitCertI (absMode mode)
        (knot mode lfe fuel.val) lfe d.val (absExpr a) (absExpr b)) := by
  intro fe lfe hfe hfrel st o st' hwf hok lst hrel
  unfold cached.core_c.struct_unit_cert_i at hok
  res_step hok
  obtain ⟨⟨r0, st1⟩, h1, hok⟩ := hok
  cases r0 with
  | Err err =>
    simp at hok
    obtain ⟨rfl, rfl⟩ := hok
    refine Out.err (ErrSim.trans
      ((hw.inferIOSim d ha).apply_err hwf hfe h1 hrel hfrel) ?_)
    intro le hle
    simp only [StateT.run] at hle
    simp [structUnitCertI_eq, hle]
  | Ok ta =>
    obtain ⟨lst1, hrun1, hrel1, hwf1, htaWF⟩ :=
      (hw.inferIOSim d ha).apply hwf hfe h1 hrel hfrel
    simp only [StateT.run] at hrun1
    res_step hok
    obtain ⟨⟨r1, st2⟩, h2, hok⟩ := hok
    cases r1 with
    | Err err =>
      simp at hok
      obtain ⟨rfl, rfl⟩ := hok
      refine Out.err (ErrSim.trans
        ((hw.whnfSim d htaWF).apply_err hwf1 hfe h2 hrel1 hfrel) ?_)
      intro le hle
      simp only [StateT.run] at hle
      simp [structUnitCertI_eq, hrun1, hle]
    | Ok wta =>
      obtain ⟨lst2, hrun2, hrel2, hwf2, hwtaWF⟩ :=
        (hw.whnfSim d htaWF).apply hwf1 hfe h2 hrel1 hfrel
      simp only [StateT.run] at hrun2
      res_step hok
      obtain ⟨f, hf, hok⟩ := hok
      obtain ⟨hfabs, hfwf⟩ := ExprOps.get_app_fn_refines hwtaWF hf
      obtain ⟨⟨dn, kn⟩⟩ := f
      simp only [absExpr_mk] at hfabs
      simp only [ExprOps.node_kind] at hok
      cases kn with
      | Const t us2 =>
        obtain ⟨ht, hus2⟩ := CoreK.envFacts.constWF hfwf rfl
        res_step hok
        obtain ⟨op, hprobe, hok⟩ := hok
        obtain ⟨hpabs, hpwf⟩ := CoreK.envFacts.indProbe (FindAgree.of_rel hfrel hfe)
          (FindWF.of_wf hfe) ht hprobe
        cases op with
        | none =>
          simp only [Option.map_none] at hpabs
          simp only [Result.ok.injEq, Prod.mk.injEq] at hok
          obtain ⟨rfl, rfl⟩ := hok
          refine ⟨lst2, ?_, hrel2, hwf2, trivial⟩
          simp [structUnitCertI_eq, ConLeche.Expr.getAppFn_spec,
              ConLeche.Expr.getAppArgsC_spec, hrun1, hrun2, ← hfabs, ind_find_eq hpabs]
        | some p =>
          obtain ⟨cvt, caps⟩ := p
          simp only [Option.map_some] at hpabs
          res_step hok
          obtain ⟨tg, htg, hok⟩ := hok
          obtain ⟨htgabs, htgwf⟩ := ExprOps.get_app_args_refines hwtaWF htg
          obtain ⟨sb, hsb, hok⟩ := hok
          have hsbabs := CoreK.unit_shape_ok_refines CoreK.pinned_reserved_basis_names ht hsb
          have hargs : (absExpr wta).getAppArgs = absExprs tg := htgabs.symm
          cases sb with
          | false =>
            simp only [Bool.false_eq_true, if_false, Result.ok.injEq, Prod.mk.injEq] at hok
            obtain ⟨rfl, rfl⟩ := hok
            refine ⟨lst2, ?_, hrel2, hwf2, trivial⟩
            replace hsbabs := hsbabs.symm
            simp only [decide_eq_false_iff_not] at hsbabs
            simp [structUnitCertI_eq, ConLeche.Expr.getAppFn_spec,
              ConLeche.Expr.getAppArgsC_spec, hrun1, hrun2, ← hfabs, ind_find_eq hpabs,
              hargs]
            rw [if_neg (by simpa using hsbabs)]
            rfl
          | true =>
            simp only [if_true] at hok
            refine out_of_eq ((struct_unit_steps_i_refines hw hd d hwtaWF hb ht hus2 htgwf)
              fe lfe hfe hfrel st2 o st' hwf2 hok lst2 hrel2) ?_
            replace hsbabs := hsbabs.symm
            simp only [decide_eq_true_eq] at hsbabs
            simp [structUnitCertI_eq, ConLeche.Expr.getAppFn_spec,
              ConLeche.Expr.getAppArgsC_spec, hrun1, hrun2, ← hfabs, ind_find_eq hpabs,
              hargs]
            rw [if_pos (by simpa using hsbabs)]
      | _ =>
        simp only [Result.ok.injEq, Prod.mk.injEq] at hok
        obtain ⟨rfl, rfl⟩ := hok
        refine ⟨lst2, ?_, hrel2, hwf2, trivial⟩
        simp [structUnitCertI_eq, ConLeche.Expr.getAppFn_spec,
              hrun1, hrun2, ← hfabs]

/-! ## The η certificate

`etaCertI` (`ConLeche/Cached/CoreC.lean:516-533`) is one `do` block; the port
splits the part after the domain comparison into `eta_cert_body_i`
(`core_c.rs:1185`).  `etaCertBodyL` names it and `etaCertI_eq` — `rfl` — is the
cited definition with it named.  The port carries `m₂.pw` (the `∀`'s own
prop-ness annotation) across the split as `pw2`, which is why the named tail
takes it as an argument. -/

/-- `ConLeche/Cached/CoreC.lean:521-531` — `etaCertI`'s tail, named: the λ's
body opened at a fresh variable against `b` applied to it, and **last** the
prop-ness annotations at the verified modes. -/
def etaCertBodyL (mode : ConLeche.CheckMode) (r : ConLeche.Cached.CoreFnsI) (depth : Nat)
    (ty₁ body₁ : ConLeche.Expr) (m₁ : ConLeche.BinderMeta)
    (b : ConLeche.Expr) (pw₂ : ConLeche.PropWhen) :
    ConLeche.Cached.CheckCM Bool := do
  let fv ← pure (ConLeche.Expr.fvar depth ty₁)
  let b₁ ← ConLeche.Cached.inst1M body₁ fv
  let ba ← pure (ConLeche.Expr.app b fv)
  unless ← r.defeq (depth + 1) b₁ ba do return false
  if mode.verifiedChecks && !(m₁.pw == pw₂) then
    throw (.notImplemented "sort-annotation mismatch (eta)")
  pure true

/-- `ConLeche/Cached/CoreC.lean:516-533` — the cited definition is its `∀`
gate and domain comparison around `etaCertBodyL`.  `rfl`. -/
theorem etaCertI_eq (mode : ConLeche.CheckMode) (r : ConLeche.Cached.CoreFnsI)
    (fe : ConLeche.FEnv) (depth : Nat) (ty₁ body₁ : ConLeche.Expr)
    (m₁ : ConLeche.BinderMeta) (b : ConLeche.Expr) :
    ConLeche.Cached.etaCertI mode r fe depth ty₁ body₁ m₁ b = (do
      let tb ← r.inferIO depth b
      let wtb ← r.whnf depth tb
      match wtb with
      | .forallE ty₂ _ m₂ => do
        if ← r.defeq depth ty₂ ty₁ then
          etaCertBodyL mode r depth ty₁ body₁ m₁ b m₂.pw
        else pure false
      | _ => pure false) := rfl


/-- `ConLeche/Cached/CoreC.lean:521-531` — **`eta_cert_body_i` refines
`etaCertBodyL`** (`core_c.rs:1185`), `etaCertI`'s tail once the domains have
matched.  Its last arm is this file's one explicit `throw` (task #67): a
prop-ness mismatch at a verified mode declines on both sides, at the
`notImplemented` kind. -/
theorem eta_cert_body_i_refines (hw : Wrappers mode fuel) (d : Std.U64)
    {ty1 body1 b : expr.Expr} {m1 : expr.BinderMeta} {pw2 : prop_when.PropWhen}
    (hty : ExprWF ty1) (hbody : ExprWF body1) (hb : ExprWF b)
    (hm1 : BinderMetaWF m1) (hpw2 : PropWhenWF pw2) :
    Sim id (fun _ => True)
      (fun st fe => cached.core_c.eta_cert_body_i mode fuel st fe d ty1 body1 m1 b pw2)
      (fun lfe => etaCertBodyL (absMode mode) (knot mode lfe fuel.val) d.val
        (absExpr ty1) (absExpr body1) (absBinderMeta m1) (absExpr b)
        (absPropWhen pw2)) := by
  intro fe lfe hfe hfrel st o st' hwf hok lst hrel
  unfold cached.core_c.eta_cert_body_i at hok
  res_step hok
  obtain ⟨v, hv, lhs, hlhs, rhs, hrhs, i, hi, hok⟩ := hok
  have hvabs : absExpr v = ConLeche.Expr.fvar d.val (absExpr ty1) := Expr.fvar_refines hv
  have hvwf : ExprWF v := Expr.fvar_wf hty hv
  obtain ⟨hlabs, hlwf⟩ :=
    ExprOpsC.instantiate1_refines hbody hvwf (by rw [← StateC.inst1_m_eq]; exact hlhs)
  rw [show ((0#u64 : Std.U64).val) = 0 from rfl] at hlabs
  have hrabs : absExpr rhs = ConLeche.Expr.app (absExpr b) (absExpr v) := Expr.app_refines hrhs
  have hrwf : ExprWF rhs := ExprWF.app hb hvwf hrhs
  have hival : i.val = d.val + 1 := HashMap.uscalar_add_eq hi
  obtain ⟨⟨r0, st1⟩, h0, hok⟩ := hok
  cases r0 with
  | Err err =>
    simp at hok
    obtain ⟨rfl, rfl⟩ := hok
    refine Out.err (ErrSim.trans
      ((hw.defeqSim i hlwf hrwf).apply_err hwf hfe h0 hrel hfrel) ?_)
    intro le hle
    simp only [StateT.run] at hle
    rw [hival, hlabs, hrabs, hvabs] at hle
    simp [etaCertBodyL, ConLeche.Cached.inst1M, hle]
  | Ok bd =>
    obtain ⟨lst1, hrun1, hrel1, hwf1, -⟩ :=
      (hw.defeqSim i hlwf hrwf).apply hwf hfe h0 hrel hfrel
    simp only [StateT.run, id_eq] at hrun1
    rw [hival, hlabs, hrabs, hvabs] at hrun1
    cases bd with
    | false =>
      simp only [Bool.false_eq_true, if_false, Result.ok.injEq, Prod.mk.injEq] at hok
      obtain ⟨rfl, rfl⟩ := hok
      exact ⟨lst1, by simp [etaCertBodyL, ConLeche.Cached.inst1M, hrun1], hrel1, hwf1, trivial⟩
    | true =>
      simp only [if_true] at hok
      res_step hok
      obtain ⟨vc, hvc, hok⟩ := hok
      have hvcabs : vc = (absMode mode).verifiedChecks := Env.verified_checks_refines hvc
      cases vc with
      | false =>
        simp only [Bool.false_eq_true, if_false, Result.ok.injEq, Prod.mk.injEq] at hok
        obtain ⟨rfl, rfl⟩ := hok
        refine ⟨lst1, ?_, hrel1, hwf1, trivial⟩
        simp [etaCertBodyL, ConLeche.Cached.inst1M, hrun1, ← hvcabs]
      | true =>
        simp only [if_true] at hok
        res_step hok
        obtain ⟨pb, hpb, hok⟩ := hok
        have hpbiff := PropWhen.beq_iff (PropWhen.wf_shape hm1) (PropWhen.wf_shape hpw2) hpb
        cases pb with
        | false =>
          -- **The one explicit `throw` of this file** (`core_c.rs:1201`): the
          -- annotations disagree at a verified mode, and the cited `etaCertI`
          -- throws `notImplemented` at exactly this step (`CoreC.lean:530`).
          simp only [Bool.false_eq_true, if_false] at hok
          res_step hok
          obtain ⟨cps, -, cv, -, ce, hce, rfl, rfl⟩ := hok
          have hcee := not_implemented_inv hce
          subst hcee
          have hpwne : ¬ (absPropWhen m1.pw = absPropWhen pw2) := fun hx => by
            simpa using hpbiff.mpr hx
          refine Out.err (ErrSim.notImplemented
            (s := "sort-annotation mismatch (eta)") ?_)
          simp [etaCertBodyL, ConLeche.Cached.inst1M, hrun1, ← hvcabs, absBinderMeta,
            hpwne]
        | true =>
          simp only [if_true, Result.ok.injEq, Prod.mk.injEq] at hok
          obtain ⟨rfl, rfl⟩ := hok
          refine ⟨lst1, ?_, hrel1, hwf1, trivial⟩
          have hpweq : absPropWhen m1.pw = absPropWhen pw2 := hpbiff.mp rfl
          simp [etaCertBodyL, ConLeche.Cached.inst1M, hrun1, ← hvcabs, absBinderMeta, hpweq]

/-- `ConLeche/Cached/CoreC.lean:516-533` — **`eta_cert_i` refines `etaCertI`**
(`core_c.rs:1148`): `b`'s type whnfs to a `∀` whose domain is definitionally
equal to the λ's, and then `etaCertBodyL`. -/
theorem eta_cert_i_refines (hw : Wrappers mode fuel) (d : Std.U64)
    {ty1 body1 b : expr.Expr} {m1 : expr.BinderMeta}
    (hty : ExprWF ty1) (hbody : ExprWF body1) (hm1 : BinderMetaWF m1)
    (hb : ExprWF b) :
    Sim id (fun _ => True)
      (fun st fe => cached.core_c.eta_cert_i mode fuel st fe d ty1 body1 m1 b)
      (fun lfe => ConLeche.Cached.etaCertI (absMode mode) (knot mode lfe fuel.val)
        lfe d.val (absExpr ty1) (absExpr body1) (absBinderMeta m1) (absExpr b)) := by
  intro fe lfe hfe hfrel st o st' hwf hok lst hrel
  unfold cached.core_c.eta_cert_i at hok
  res_step hok
  obtain ⟨⟨r0, st1⟩, h1, hok⟩ := hok
  cases r0 with
  | Err err =>
    simp at hok
    obtain ⟨rfl, rfl⟩ := hok
    refine Out.err (ErrSim.trans
      ((hw.inferIOSim d hb).apply_err hwf hfe h1 hrel hfrel) ?_)
    intro le hle
    simp only [StateT.run] at hle
    simp [etaCertI_eq, hle]
  | Ok tb =>
    obtain ⟨lst1, hrun1, hrel1, hwf1, htbWF⟩ :=
      (hw.inferIOSim d hb).apply hwf hfe h1 hrel hfrel
    simp only [StateT.run] at hrun1
    res_step hok
    obtain ⟨⟨r1, st2⟩, h2, hok⟩ := hok
    cases r1 with
    | Err err =>
      simp at hok
      obtain ⟨rfl, rfl⟩ := hok
      refine Out.err (ErrSim.trans
        ((hw.whnfSim d htbWF).apply_err hwf1 hfe h2 hrel1 hfrel) ?_)
      intro le hle
      simp only [StateT.run] at hle
      simp [etaCertI_eq, hrun1, hle]
    | Ok wtb =>
      obtain ⟨lst2, hrun2, hrel2, hwf2, hwtbWF⟩ :=
        (hw.whnfSim d htbWF).apply hwf1 hfe h2 hrel1 hfrel
      simp only [StateT.run] at hrun2
      obtain ⟨⟨dw, kw⟩⟩ := wtb
      res_step hok
      cases kw with
      | ForallE ty2 bo2 m2 =>
        obtain ⟨hty2, -, hm2⟩ := wf_kind_inv hwtbWF rfl
        res_step hok
        obtain ⟨pw2, hdup, ⟨r2, st3⟩, h3, hok⟩ := hok
        have hpweq : pw2 = m2.pw := PropWhen.dup_eq hdup
        subst hpweq
        cases r2 with
        | Err err =>
          simp at hok
          obtain ⟨rfl, rfl⟩ := hok
          refine Out.err (ErrSim.trans
            ((hw.defeqSim d hty2 hty).apply_err hwf2 hfe h3 hrel2 hfrel) ?_)
          intro le hle
          simp only [StateT.run] at hle
          simp [etaCertI_eq, hrun1, hrun2, hle]
        | Ok bd =>
          obtain ⟨lst3, hrun3, hrel3, hwf3, -⟩ :=
            (hw.defeqSim d hty2 hty).apply hwf2 hfe h3 hrel2 hfrel
          simp only [StateT.run, id_eq] at hrun3
          cases bd with
          | false =>
            simp only [Bool.false_eq_true, if_false, Result.ok.injEq, Prod.mk.injEq] at hok
            obtain ⟨rfl, rfl⟩ := hok
            refine ⟨lst3, ?_, hrel3, hwf3, trivial⟩
            simp [etaCertI_eq, hrun1, hrun2, hrun3]
          | true =>
            simp only [if_true] at hok
            refine out_of_eq ((eta_cert_body_i_refines hw d hty hbody hb hm1 hm2)
              fe lfe hfe hfrel st3 o st' hwf3 hok lst3 hrel3) ?_
            simp only [etaCertI_eq]
            simp [hrun1, hrun2, hrun3]
      | _ =>
        simp only [Result.ok.injEq, Prod.mk.injEq] at hok
        obtain ⟨rfl, rfl⟩ := hok
        refine ⟨lst2, ?_, hrel2, hwf2, trivial⟩
        simp [etaCertI_eq, hrun1, hrun2]

/-- `ConLeche/Cached/CoreC.lean:1520-1614` — **`defeq_struct_i` refines
`defeqStructL`** (`core_c.rs:4061`), the `| false, false =>` arm of
`defeqStepI`: neither head unfolds, so the pair of kinds decides. -/
theorem defeq_struct_i_refines (hw : Wrappers mode fuel)
    (hd : DefEqStructDeps mode fuel) (d : Std.U64) {a b : expr.Expr}
    (ha : ExprWF a) (hb : ExprWF b) :
    Sim id (fun _ => True)
      (fun st fe => cached.core_c.defeq_struct_i mode fuel st fe d a b)
      (fun lfe => defeqStructL (absMode mode) (knot mode lfe fuel.val) lfe d.val
        (absExpr a) (absExpr b)) := by
  intro fe lfe hfe hfrel st oc st' hwf hok lst hrel
  unfold cached.core_c.defeq_struct_i at hok
  res_step hok
  obtain ⟨⟨da, ka⟩⟩ := a
  obtain ⟨⟨db, kb⟩⟩ := b
  res_step hok
  have Hstuck : ∀ {stX : cached.state_c.CState} {lstX : ConLeche.Cached.CState},
      StateWF stX → StateRel stX lstX →
      cached.core_c.stuck_irrel_i mode fuel stX fe d
          (expr.Expr.mk (expr.ExprNode.mk da ka)) (expr.Expr.mk (expr.ExprNode.mk db kb))
        = ok (oc, st') →
      Out id (fun _ => True) oc st'
        ((ConLeche.Cached.stuckIrrelI (absMode mode) (knot mode lfe fuel.val) lfe d.val
          (absExprKind ka) (absExprKind kb)).run lstX) := by
    intro stX lstX hwfX hrelX hokX
    have h := (hd.stuckIrrel d ha hb) fe lfe hfe hfrel stX oc st' hwfX hokX lstX hrelX
    simpa only [absExpr_mk] using h
  have Heta : ∀ (t2 b2 : expr.Expr) (m2 : expr.BinderMeta) (x : expr.Expr),
      ExprWF t2 → ExprWF b2 → BinderMetaWF m2 → ExprWF x →
      ∀ {stX : cached.state_c.CState} {lstX : ConLeche.Cached.CState}
        {oo : core.result.Result Bool core_types.CheckError} {st1 : cached.state_c.CState},
      StateWF stX → StateRel stX lstX →
      cached.core_c.eta_cert_i mode fuel stX fe d t2 b2 m2 x = ok (oo, st1) →
      Out id (fun _ => True) oo st1
        ((ConLeche.Cached.etaCertI (absMode mode) (knot mode lfe fuel.val) lfe d.val
          (absExpr t2) (absExpr b2) (absBinderMeta m2) (absExpr x)).run lstX) := by
    intro t2 b2 m2 x h1 h2 h3 h4 stX lstX oo st1 hwfX hrelX hokX
    exact (eta_cert_i_refines hw d h1 h2 h3 h4) fe lfe hfe hfrel stX oo st1 hwfX hokX
      lstX hrelX
  have Hdq : ∀ {x y : expr.Expr}, ExprWF x → ExprWF y →
      ∀ {stX : cached.state_c.CState} {lstX : ConLeche.Cached.CState}
        {oo : core.result.Result Bool core_types.CheckError} {st1 : cached.state_c.CState},
      StateWF stX → StateRel stX lstX →
      cached.core_c.defeq mode fuel stX fe d x y = ok (oo, st1) →
      Out id (fun _ => True) oo st1
        (((knot mode lfe fuel.val).defeq d.val (absExpr x) (absExpr y)).run lstX) := by
    intro x y h1 h2 stX lstX oo st1 hwfX hrelX hokX
    exact (hw.defeqSim d h1 h2) fe lfe hfe hfrel stX oo st1 hwfX hokX lstX hrelX
  cases ka with
  | Bvar i =>
    cases kb with
    | Lam t2 b2 m2 =>
      obtain ⟨ht2, hb2, hm2⟩ := wf_kind_inv hb rfl
      res_step hok
      obtain ⟨⟨rr, st1⟩, h1, hok⟩ := hok
      cases rr with
      | Err e =>
        simp at hok
        obtain ⟨rfl, rfl⟩ := hok
        refine Out.err (ErrSim.trans
          (Out.destErr (Heta _ _ _ _ ht2 hb2 hm2 ha hwf hrel h1)) ?_)
        intro le hle
        simp only [absExpr_mk, absExprKind, absBinderMeta, StateT.run] at hle
        simp [defeqStructL, hle]
      | Ok bd =>
        obtain ⟨l1, hr1, hre1, hwe1, -⟩ :=
          Out.dest (Heta _ _ _ _ ht2 hb2 hm2 ha hwf hrel h1)
        simp only [absExpr_mk, absExprKind, absBinderMeta, StateT.run,
          id_eq] at hr1
        cases bd with
        | true =>
          simp only [if_true, Result.ok.injEq, Prod.mk.injEq] at hok
          obtain ⟨rfl, rfl⟩ := hok
          refine ⟨l1, ?_, hre1, hwe1, trivial⟩
          simp [defeqStructL, hr1]
        | false =>
          simp only [Bool.false_eq_true, if_false] at hok
          refine out_of_eq (Hstuck hwe1 hre1 hok) ?_
          simp [defeqStructL, hr1]
    | _ =>
      exact out_of_eq (Hstuck hwf hrel hok) (by simp [defeqStructL])
  | Fvar i ty1 =>
    cases kb with
    | Fvar j ty2 =>
      res_step hok
      split at hok
      · rename_i hij
        subst hij
        simp only [Result.ok.injEq, Prod.mk.injEq] at hok
        obtain ⟨rfl, rfl⟩ := hok
        refine ⟨lst, ?_, hrel, hwf, trivial⟩
        simp [defeqStructL]
      · rename_i hij
        have hijv : ¬ ((i : Std.U64).val = (j : Std.U64).val) := fun hx => hij (u64_val_inj hx)
        refine out_of_eq (Hstuck hwf hrel hok) ?_
        simp [defeqStructL, hijv]
    | Lam t2 b2 m2 =>
      obtain ⟨ht2, hb2, hm2⟩ := wf_kind_inv hb rfl
      res_step hok
      obtain ⟨⟨rr, st1⟩, h1, hok⟩ := hok
      cases rr with
      | Err e =>
        simp at hok
        obtain ⟨rfl, rfl⟩ := hok
        refine Out.err (ErrSim.trans
          (Out.destErr (Heta _ _ _ _ ht2 hb2 hm2 ha hwf hrel h1)) ?_)
        intro le hle
        simp only [absExpr_mk, absExprKind, absBinderMeta, StateT.run] at hle
        simp [defeqStructL, hle]
      | Ok bd =>
        obtain ⟨l1, hr1, hre1, hwe1, -⟩ :=
          Out.dest (Heta _ _ _ _ ht2 hb2 hm2 ha hwf hrel h1)
        simp only [absExpr_mk, absExprKind, absBinderMeta, StateT.run,
          id_eq] at hr1
        cases bd with
        | true =>
          simp only [if_true, Result.ok.injEq, Prod.mk.injEq] at hok
          obtain ⟨rfl, rfl⟩ := hok
          refine ⟨l1, ?_, hre1, hwe1, trivial⟩
          simp [defeqStructL, hr1]
        | false =>
          simp only [Bool.false_eq_true, if_false] at hok
          refine out_of_eq (Hstuck hwe1 hre1 hok) ?_
          simp [defeqStructL, hr1]
    | _ =>
      exact out_of_eq (Hstuck hwf hrel hok) (by simp [defeqStructL])
  | «Sort» u =>
    cases kb with
    | «Sort» v =>
      res_step hok
      have hu : LevelWF u := wf_kind_inv ha rfl
      have hv : LevelWF v := wf_kind_inv hb rfl
      obtain ⟨⟨eqo, st1⟩, h1, rr0, h2, hok⟩ := hok
      obtain ⟨lst1, hr1, hre1, hwe1⟩ := StateC.is_equiv_l_m_refines hwf hu hv h1 lst hrel
      simp only [StateT.run] at hr1
      cases rr0 with
      | Ok bb =>
        simp only [Prod.mk.injEq] at hok
        obtain ⟨rfl, rfl⟩ := hok
        have heq : eqo = some bb := lift_fueled_some h2
        refine ⟨lst1, ?_, hre1, hwe1, trivial⟩
        simp [defeqStructL, hr1, heq, ConLeche.liftFueled]
      | Err e =>
        simp only [Prod.mk.injEq] at hok
        obtain ⟨rfl, rfl⟩ := hok
        obtain ⟨rfl, hkind⟩ := lift_fueled_err h2
        refine Out.err (ErrSim.trans
          (errSim_liftFueled_none hkind "level comparison" lst1) ?_)
        intro le hle
        simp only [StateT.run] at hle
        simp [defeqStructL, hr1, hle]
    | Lam t2 b2 m2 =>
      obtain ⟨ht2, hb2, hm2⟩ := wf_kind_inv hb rfl
      res_step hok
      obtain ⟨⟨rr, st1⟩, h1, hok⟩ := hok
      cases rr with
      | Err e =>
        simp at hok
        obtain ⟨rfl, rfl⟩ := hok
        refine Out.err (ErrSim.trans
          (Out.destErr (Heta _ _ _ _ ht2 hb2 hm2 ha hwf hrel h1)) ?_)
        intro le hle
        simp only [absExpr_mk, absExprKind, absBinderMeta, StateT.run] at hle
        simp [defeqStructL, hle]
      | Ok bd =>
        obtain ⟨l1, hr1, hre1, hwe1, -⟩ :=
          Out.dest (Heta _ _ _ _ ht2 hb2 hm2 ha hwf hrel h1)
        simp only [absExpr_mk, absExprKind, absBinderMeta, StateT.run,
          id_eq] at hr1
        cases bd with
        | true =>
          simp only [if_true, Result.ok.injEq, Prod.mk.injEq] at hok
          obtain ⟨rfl, rfl⟩ := hok
          refine ⟨l1, ?_, hre1, hwe1, trivial⟩
          simp [defeqStructL, hr1]
        | false =>
          simp only [Bool.false_eq_true, if_false] at hok
          refine out_of_eq (Hstuck hwe1 hre1 hok) ?_
          simp [defeqStructL, hr1]
    | _ =>
      exact out_of_eq (Hstuck hwf hrel hok) (by simp [defeqStructL])
  | Const n1 us1 =>
    cases kb with
    | Const n2 us2 =>
      res_step hok
      obtain ⟨hn1, hus1⟩ := wf_kind_inv ha rfl
      obtain ⟨hn2, hus2⟩ := wf_kind_inv hb rfl
      obtain ⟨nb, hnb, hok⟩ := hok
      have hnbabs : nb = decide (absName n1 = absName n2) := Name.beq_refines hn1 hn2 hnb
      cases nb with
      | false =>
        simp only [Bool.false_eq_true, if_false] at hok
        refine out_of_eq (Hstuck hwf hrel hok) ?_
        have hne : ¬ (absName n1 = absName n2) := by simpa using hnbabs.symm
        simp [defeqStructL, hne]
      | true =>
        have heqn : absName n1 = absName n2 := by simpa using hnbabs.symm
        simp only [if_true] at hok
        res_step hok
        obtain ⟨⟨eqo, st1⟩, h1, rr0, h2, hok⟩ := hok
        obtain ⟨lst1, hr1, hre1, hwe1⟩ :=
          StateC.is_equiv_list_l_m_refines hwf hus1 hus2 h1 lst hrel
        simp only [StateT.run] at hr1
        cases rr0 with
        | Err e =>
          simp at hok
          obtain ⟨rfl, rfl⟩ := hok
          obtain ⟨rfl, hkind⟩ := lift_fueled_err h2
          refine Out.err (ErrSim.trans
            (errSim_liftFueled_none hkind "level comparison" lst1) ?_)
          intro le hle
          simp only [StateT.run] at hle
          simp [defeqStructL, hr1, heqn, hle]
        | Ok b2 =>
          have heqo : eqo = some b2 := lift_fueled_some h2
          cases b2 with
          | true =>
            simp only [if_true, Result.ok.injEq, Prod.mk.injEq] at hok
            obtain ⟨rfl, rfl⟩ := hok
            refine ⟨lst1, ?_, hre1, hwe1, trivial⟩
            simp [defeqStructL, hr1, heqo, heqn, ConLeche.liftFueled]
          | false =>
            simp only [Bool.false_eq_true, if_false] at hok
            refine out_of_eq (Hstuck hwe1 hre1 hok) ?_
            simp [defeqStructL, hr1, heqo, heqn, ConLeche.liftFueled]
    | Lit l =>
      cases l with
      | NatVal nn =>
        res_step hok
        obtain ⟨hn1, hus1⟩ := wf_kind_inv ha rfl
        have hnnwf : Nat.NatWF nn := wf_kind_inv hb rfl
        split at hok
        · rename_i hlen
          have hnil : absLevels us1 = [] := by
            have hl : us1.val.length = 0 := by
              have h0 := congrArg Std.UScalar.val hlen
              simpa [alloc.vec.Vec.len_val] using h0
            simp [absLevels, List.eq_nil_of_length_eq_zero hl]
          res_step hok
          obtain ⟨zn, hzn, nb, hnb, hok⟩ := hok
          obtain ⟨hznabs, hznwf⟩ := CoreK.pinned_nat_zero_name zn hzn
          have hnbabs : nb = decide (absName n1 = absName zn) := Name.beq_refines hn1 hznwf hnb
          split at hok
          · rename_i hnbv
            have heqz : absName n1 = ConLeche.natZeroName := by
              rw [← hznabs]; rw [hnbv] at hnbabs; simpa using hnbabs.symm
            res_step hok
            obtain ⟨bz, hbz, hok⟩ := hok
            simp only [Prod.mk.injEq] at hok
            obtain ⟨rfl, rfl⟩ := hok
            have hbzabs : bz = decide (Nat.toNat nn = 0) := Nat.is_zero_refines hnnwf hbz
            refine ⟨lst, ?_, hrel, hwf, trivial⟩
            simp [defeqStructL, hnil, heqz, hbzabs]
            cases hz : Nat.toNat nn <;> simp
          · rename_i hnbv
            have hne : ¬ (absName n1 = ConLeche.natZeroName) := by
              rw [← hznabs]
              simp only [Bool.not_eq_true] at hnbv
              rw [hnbv] at hnbabs; simpa using hnbabs.symm
            refine out_of_eq (Hstuck hwf hrel hok) ?_
            simp [defeqStructL, hne]
        · rename_i hlen
          have hnn : ¬ (absLevels us1 = []) := by
            intro hcc
            apply hlen
            have hv : us1.val = [] := by simpa [absLevels] using hcc
            have hl0 : (alloc.vec.Vec.len us1).val = 0 := by
              simp [hv]
            scalar_tac
          refine out_of_eq (Hstuck hwf hrel hok) ?_
          simp [defeqStructL, hnn]
      | StrVal ss =>
        exact out_of_eq (Hstuck hwf hrel hok) (by simp [defeqStructL])
    | Lam t2 b2 m2 =>
      obtain ⟨ht2, hb2, hm2⟩ := wf_kind_inv hb rfl
      res_step hok
      obtain ⟨⟨rr, st1⟩, h1, hok⟩ := hok
      cases rr with
      | Err e =>
        simp at hok
        obtain ⟨rfl, rfl⟩ := hok
        refine Out.err (ErrSim.trans
          (Out.destErr (Heta _ _ _ _ ht2 hb2 hm2 ha hwf hrel h1)) ?_)
        intro le hle
        simp only [absExpr_mk, absExprKind, absBinderMeta, StateT.run] at hle
        simp [defeqStructL, hle]
      | Ok bd =>
        obtain ⟨l1, hr1, hre1, hwe1, -⟩ :=
          Out.dest (Heta _ _ _ _ ht2 hb2 hm2 ha hwf hrel h1)
        simp only [absExpr_mk, absExprKind, absBinderMeta, StateT.run,
          id_eq] at hr1
        cases bd with
        | true =>
          simp only [if_true, Result.ok.injEq, Prod.mk.injEq] at hok
          obtain ⟨rfl, rfl⟩ := hok
          refine ⟨l1, ?_, hre1, hwe1, trivial⟩
          simp [defeqStructL, hr1]
        | false =>
          simp only [Bool.false_eq_true, if_false] at hok
          refine out_of_eq (Hstuck hwe1 hre1 hok) ?_
          simp [defeqStructL, hr1]
    | _ =>
      exact out_of_eq (Hstuck hwf hrel hok) (by simp [defeqStructL])
  | App f1 x1 =>
    cases kb with
    | App f2 x2 =>
      refine out_of_eq
        ((hd.defeqApps d ha hb) fe lfe hfe hfrel st oc st' hwf hok lst hrel) ?_
      simp [defeqStructL]
    | Lit l =>
      obtain ⟨hf1, hx1⟩ := wf_kind_inv ha rfl
      cases l with
      | NatVal nn =>
        have hnnwf : Nat.NatWF nn := wf_kind_inv hb rfl
        res_step hok
        obtain ⟨o, ho, hok⟩ := hok
        obtain ⟨hoabs0, howf⟩ :=
          CoreK.succ_of_refines hnnwf hf1 CoreK.pinned_nat_succ_name ho
        have hoabs : Option.map Nat.toNat o =
            (match Nat.toNat nn, absExpr f1 with
              | k + 1, .const c [] => if c = ConLeche.natSuccName then some k else none
              | _, _ => none) := hoabs0
        cases o with
        | none =>
          refine out_of_eq (Hstuck hwf hrel hok) ?_
          simp only [defeqStructL, absExpr_mk, absExprKind, absLiteral, pure_bind,
            succ_match_eq]
          rw [← hoabs]
          simp
        | some k =>
          have hkwf : Nat.NatWF k := howf k rfl
          simp only [literal_nat_eq', bind_tc_ok] at hok
          res_step hok
          obtain ⟨lke, hlke, hok⟩ := hok
          refine out_of_eq
            (Hdq hx1 (Expr.lit_wf (l := expr.Literal.NatVal k) hkwf hlke) hwf hrel hok) ?_
          simp only [defeqStructL, absExpr_mk, absExprKind, absLiteral, pure_bind,
            succ_match_eq]
          rw [← hoabs]
          simp [Expr.lit_refines hlke, absLiteral]
      | StrVal ss =>
        have hsswf : StrWF ss := wf_kind_inv hb rfl
        res_step hok
        obtain ⟨bf, hbf, hok⟩ := hok
        have hfabs0 := CoreK.str_expansion_fires_refines CoreK.pinned_string_of_list_name
          (CoreK.strLitSupportedSpec (FindAgree.of_rel hfrel hfe)
            (FindWF.of_wf hfe)) hf1 hbf
        have hfabs : bf =
            (match absExpr f1 with
              | .const cO usO =>
                decide (cO = ConLeche.stringOfListName) && decide (usO = []) &&
                  ConLeche.strLitSupportedF lfe
              | _ => false) := hfabs0
        cases bf with
        | false =>
          simp only [Bool.false_eq_true, if_false] at hok
          refine out_of_eq (Hstuck hwf hrel hok) ?_
          simp only [defeqStructL, absExpr_mk, absExprKind, absLiteral, pure_bind,
            str_match_eq]
          rw [← hfabs]
          simp
        | true =>
          simp only [if_true] at hok
          res_step hok
          obtain ⟨sc, hsc, hok⟩ := hok
          obtain ⟨hscabs, hscwf⟩ := CoreK.str_lit_to_constructor_refines hsswf
            CoreK.pinned_char_name CoreK.pinned_char_of_nat_name
            CoreK.pinned_list_nil_name CoreK.pinned_list_cons_name
            CoreK.pinned_string_of_list_name hsc
          refine out_of_eq (Hdq ha hscwf hwf hrel hok) ?_
          simp only [defeqStructL, absExpr_mk, absExprKind, absLiteral, pure_bind,
            str_match_eq]
          rw [← hfabs]
          simp [hscabs]
    | Lam t2 b2 m2 =>
      obtain ⟨ht2, hb2, hm2⟩ := wf_kind_inv hb rfl
      res_step hok
      obtain ⟨⟨rr, st1⟩, h1, hok⟩ := hok
      cases rr with
      | Err e =>
        simp at hok
        obtain ⟨rfl, rfl⟩ := hok
        refine Out.err (ErrSim.trans
          (Out.destErr (Heta _ _ _ _ ht2 hb2 hm2 ha hwf hrel h1)) ?_)
        intro le hle
        simp only [absExpr_mk, absExprKind, absBinderMeta, StateT.run] at hle
        simp [defeqStructL, hle]
      | Ok bd =>
        obtain ⟨l1, hr1, hre1, hwe1, -⟩ :=
          Out.dest (Heta _ _ _ _ ht2 hb2 hm2 ha hwf hrel h1)
        simp only [absExpr_mk, absExprKind, absBinderMeta, StateT.run,
          id_eq] at hr1
        cases bd with
        | true =>
          simp only [if_true, Result.ok.injEq, Prod.mk.injEq] at hok
          obtain ⟨rfl, rfl⟩ := hok
          refine ⟨l1, ?_, hre1, hwe1, trivial⟩
          simp [defeqStructL, hr1]
        | false =>
          simp only [Bool.false_eq_true, if_false] at hok
          refine out_of_eq (Hstuck hwe1 hre1 hok) ?_
          simp [defeqStructL, hr1]
    | _ =>
      exact out_of_eq (Hstuck hwf hrel hok) (by simp [defeqStructL])
  | Lam t1 b1 m1 =>
    cases kb with
    | Lam t2 b2 m2 =>
      obtain ⟨ht1, hbo1, hm1⟩ := wf_kind_inv ha rfl
      obtain ⟨ht2, hbo2, hm2⟩ := wf_kind_inv hb rfl
      refine out_of_eq ((hd.defeqBinders d false ht1 hbo1 hm1 ht2 hbo2 hm2)
        fe lfe hfe hfrel st oc st' hwf hok lst hrel) ?_
      simp [defeqStructL]
    | _ =>
      obtain ⟨ht2, hb2, hm2⟩ := wf_kind_inv ha rfl
      res_step hok
      obtain ⟨⟨rr, st1⟩, h1, hok⟩ := hok
      cases rr with
      | Err e =>
        simp at hok
        obtain ⟨rfl, rfl⟩ := hok
        refine Out.err (ErrSim.trans
          (Out.destErr (Heta _ _ _ _ ht2 hb2 hm2 hb hwf hrel h1)) ?_)
        intro le hle
        simp only [absExpr_mk, absExprKind, absBinderMeta, absLiteral, StateT.run] at hle
        simp [defeqStructL, hle]
      | Ok bd =>
        obtain ⟨l1, hr1, hre1, hwe1, -⟩ :=
          Out.dest (Heta _ _ _ _ ht2 hb2 hm2 hb hwf hrel h1)
        simp only [absExpr_mk, absExprKind, absBinderMeta, absLiteral, StateT.run,
          id_eq] at hr1
        cases bd with
        | true =>
          simp only [if_true, Result.ok.injEq, Prod.mk.injEq] at hok
          obtain ⟨rfl, rfl⟩ := hok
          refine ⟨l1, ?_, hre1, hwe1, trivial⟩
          simp [defeqStructL, hr1]
        | false =>
          simp only [Bool.false_eq_true, if_false] at hok
          refine out_of_eq (Hstuck hwe1 hre1 hok) ?_
          simp [defeqStructL, hr1]
  | ForallE t1 b1 m1 =>
    cases kb with
    | ForallE t2 b2 m2 =>
      obtain ⟨ht1, hbo1, hm1⟩ := wf_kind_inv ha rfl
      obtain ⟨ht2, hbo2, hm2⟩ := wf_kind_inv hb rfl
      refine out_of_eq ((hd.defeqBinders d true ht1 hbo1 hm1 ht2 hbo2 hm2)
        fe lfe hfe hfrel st oc st' hwf hok lst hrel) ?_
      simp [defeqStructL]
    | Lam t2 b2 m2 =>
      obtain ⟨ht2, hb2, hm2⟩ := wf_kind_inv hb rfl
      res_step hok
      obtain ⟨⟨rr, st1⟩, h1, hok⟩ := hok
      cases rr with
      | Err e =>
        simp at hok
        obtain ⟨rfl, rfl⟩ := hok
        refine Out.err (ErrSim.trans
          (Out.destErr (Heta _ _ _ _ ht2 hb2 hm2 ha hwf hrel h1)) ?_)
        intro le hle
        simp only [absExpr_mk, absExprKind, absBinderMeta, StateT.run] at hle
        simp [defeqStructL, hle]
      | Ok bd =>
        obtain ⟨l1, hr1, hre1, hwe1, -⟩ :=
          Out.dest (Heta _ _ _ _ ht2 hb2 hm2 ha hwf hrel h1)
        simp only [absExpr_mk, absExprKind, absBinderMeta, StateT.run,
          id_eq] at hr1
        cases bd with
        | true =>
          simp only [if_true, Result.ok.injEq, Prod.mk.injEq] at hok
          obtain ⟨rfl, rfl⟩ := hok
          refine ⟨l1, ?_, hre1, hwe1, trivial⟩
          simp [defeqStructL, hr1]
        | false =>
          simp only [Bool.false_eq_true, if_false] at hok
          refine out_of_eq (Hstuck hwe1 hre1 hok) ?_
          simp [defeqStructL, hr1]
    | _ =>
      exact out_of_eq (Hstuck hwf hrel hok) (by simp [defeqStructL])
  | LetE ty1 v1 bo1 =>
    cases kb with
    | Lam t2 b2 m2 =>
      obtain ⟨ht2, hb2, hm2⟩ := wf_kind_inv hb rfl
      res_step hok
      obtain ⟨⟨rr, st1⟩, h1, hok⟩ := hok
      cases rr with
      | Err e =>
        simp at hok
        obtain ⟨rfl, rfl⟩ := hok
        refine Out.err (ErrSim.trans
          (Out.destErr (Heta _ _ _ _ ht2 hb2 hm2 ha hwf hrel h1)) ?_)
        intro le hle
        simp only [absExpr_mk, absExprKind, absBinderMeta, StateT.run] at hle
        simp [defeqStructL, hle]
      | Ok bd =>
        obtain ⟨l1, hr1, hre1, hwe1, -⟩ :=
          Out.dest (Heta _ _ _ _ ht2 hb2 hm2 ha hwf hrel h1)
        simp only [absExpr_mk, absExprKind, absBinderMeta, StateT.run,
          id_eq] at hr1
        cases bd with
        | true =>
          simp only [if_true, Result.ok.injEq, Prod.mk.injEq] at hok
          obtain ⟨rfl, rfl⟩ := hok
          refine ⟨l1, ?_, hre1, hwe1, trivial⟩
          simp [defeqStructL, hr1]
        | false =>
          simp only [Bool.false_eq_true, if_false] at hok
          refine out_of_eq (Hstuck hwe1 hre1 hok) ?_
          simp [defeqStructL, hr1]
    | _ =>
      exact out_of_eq (Hstuck hwf hrel hok) (by simp [defeqStructL])
  | Lit l1 =>
    cases kb with
    | Const c us =>
      cases l1 with
      | NatVal nn =>
        res_step hok
        have hnnwf : Nat.NatWF nn := wf_kind_inv ha rfl
        obtain ⟨hc, hus⟩ := wf_kind_inv hb rfl
        split at hok
        · rename_i hlen
          have hnil : absLevels us = [] := by
            have hl : us.val.length = 0 := by
              have h0 := congrArg Std.UScalar.val hlen
              simpa [alloc.vec.Vec.len_val] using h0
            simp [absLevels, List.eq_nil_of_length_eq_zero hl]
          res_step hok
          obtain ⟨zn, hzn, nb, hnb, hok⟩ := hok
          obtain ⟨hznabs, hznwf⟩ := CoreK.pinned_nat_zero_name zn hzn
          have hnbabs : nb = decide (absName c = absName zn) := Name.beq_refines hc hznwf hnb
          split at hok
          · rename_i hnbv
            have heqz : absName c = ConLeche.natZeroName := by
              rw [← hznabs]; rw [hnbv] at hnbabs; simpa using hnbabs.symm
            res_step hok
            obtain ⟨bz, hbz, hok⟩ := hok
            simp only [Prod.mk.injEq] at hok
            obtain ⟨rfl, rfl⟩ := hok
            have hbzabs : bz = decide (Nat.toNat nn = 0) := Nat.is_zero_refines hnnwf hbz
            refine ⟨lst, ?_, hrel, hwf, trivial⟩
            simp [defeqStructL, hnil, heqz, hbzabs]
            cases hz : Nat.toNat nn <;> simp
          · rename_i hnbv
            have hne : ¬ (absName c = ConLeche.natZeroName) := by
              rw [← hznabs]
              simp only [Bool.not_eq_true] at hnbv
              rw [hnbv] at hnbabs; simpa using hnbabs.symm
            refine out_of_eq (Hstuck hwf hrel hok) ?_
            simp [defeqStructL, hne]
        · rename_i hlen
          have hnn : ¬ (absLevels us = []) := by
            intro hcc
            apply hlen
            have hv : us.val = [] := by simpa [absLevels] using hcc
            have hl0 : (alloc.vec.Vec.len us).val = 0 := by
              simp [hv]
            scalar_tac
          refine out_of_eq (Hstuck hwf hrel hok) ?_
          simp [defeqStructL, hnn]
      | StrVal ss =>
        exact out_of_eq (Hstuck hwf hrel hok) (by simp [defeqStructL])
    | App f2 x2 =>
      obtain ⟨hf2, hx2⟩ := wf_kind_inv hb rfl
      cases l1 with
      | NatVal nn =>
        have hnnwf : Nat.NatWF nn := wf_kind_inv ha rfl
        res_step hok
        obtain ⟨o, ho, hok⟩ := hok
        obtain ⟨hoabs0, howf⟩ :=
          CoreK.succ_of_refines hnnwf hf2 CoreK.pinned_nat_succ_name ho
        have hoabs : Option.map Nat.toNat o =
            (match Nat.toNat nn, absExpr f2 with
              | k + 1, .const c [] => if c = ConLeche.natSuccName then some k else none
              | _, _ => none) := hoabs0
        cases o with
        | none =>
          refine out_of_eq (Hstuck hwf hrel hok) ?_
          simp only [defeqStructL, absExpr_mk, absExprKind, absLiteral, pure_bind,
            succ_match_eq]
          rw [← hoabs]
          simp
        | some k =>
          have hkwf : Nat.NatWF k := howf k rfl
          simp only [literal_nat_eq', bind_tc_ok] at hok
          res_step hok
          obtain ⟨lke, hlke, hok⟩ := hok
          refine out_of_eq
            (Hdq (Expr.lit_wf (l := expr.Literal.NatVal k) hkwf hlke) hx2 hwf hrel hok) ?_
          simp only [defeqStructL, absExpr_mk, absExprKind, absLiteral, pure_bind,
            succ_match_eq]
          rw [← hoabs]
          simp [Expr.lit_refines hlke, absLiteral]
      | StrVal ss =>
        have hsswf : StrWF ss := wf_kind_inv ha rfl
        res_step hok
        obtain ⟨bf, hbf, hok⟩ := hok
        have hfabs0 := CoreK.str_expansion_fires_refines CoreK.pinned_string_of_list_name
          (CoreK.strLitSupportedSpec (FindAgree.of_rel hfrel hfe)
            (FindWF.of_wf hfe)) hf2 hbf
        have hfabs : bf =
            (match absExpr f2 with
              | .const cO usO =>
                decide (cO = ConLeche.stringOfListName) && decide (usO = []) &&
                  ConLeche.strLitSupportedF lfe
              | _ => false) := hfabs0
        cases bf with
        | false =>
          simp only [Bool.false_eq_true, if_false] at hok
          refine out_of_eq (Hstuck hwf hrel hok) ?_
          simp only [defeqStructL, absExpr_mk, absExprKind, absLiteral, pure_bind,
            str_match_eq]
          rw [← hfabs]
          simp
        | true =>
          simp only [if_true] at hok
          res_step hok
          obtain ⟨sc, hsc, hok⟩ := hok
          obtain ⟨hscabs, hscwf⟩ := CoreK.str_lit_to_constructor_refines hsswf
            CoreK.pinned_char_name CoreK.pinned_char_of_nat_name
            CoreK.pinned_list_nil_name CoreK.pinned_list_cons_name
            CoreK.pinned_string_of_list_name hsc
          refine out_of_eq (Hdq hscwf hb hwf hrel hok) ?_
          simp only [defeqStructL, absExpr_mk, absExprKind, absLiteral, pure_bind,
            str_match_eq]
          rw [← hfabs]
          simp [hscabs]
    | Lit l2 =>
      res_step hok
      have hl1 : LiteralWF l1 := wf_kind_inv ha rfl
      have hl2 : LiteralWF l2 := wf_kind_inv hb rfl
      obtain ⟨bq, hbq, hok⟩ := hok
      have hbqabs : bq = (absLiteral l1 == absLiteral l2) := by
        rw [Expr.literal_beq_refines hl1 hl2 hbq]
        cases hx : (absLiteral l1 == absLiteral l2) <;> simp_all
      simp only [Prod.mk.injEq] at hok
      obtain ⟨rfl, rfl⟩ := hok
      refine ⟨lst, ?_, hrel, hwf, trivial⟩
      simp [defeqStructL, hbqabs]
    | Lam t2 b2 m2 =>
      obtain ⟨ht2, hb2, hm2⟩ := wf_kind_inv hb rfl
      res_step hok
      obtain ⟨⟨rr, st1⟩, h1, hok⟩ := hok
      cases rr with
      | Err e =>
        simp at hok
        obtain ⟨rfl, rfl⟩ := hok
        refine Out.err (ErrSim.trans
          (Out.destErr (Heta _ _ _ _ ht2 hb2 hm2 ha hwf hrel h1)) ?_)
        intro le hle
        simp only [absExpr_mk, absExprKind, absBinderMeta, absLiteral, StateT.run] at hle
        simp [defeqStructL, hle]
      | Ok bd =>
        obtain ⟨l1, hr1, hre1, hwe1, -⟩ :=
          Out.dest (Heta _ _ _ _ ht2 hb2 hm2 ha hwf hrel h1)
        simp only [absExpr_mk, absExprKind, absBinderMeta, absLiteral, StateT.run,
          id_eq] at hr1
        cases bd with
        | true =>
          simp only [if_true, Result.ok.injEq, Prod.mk.injEq] at hok
          obtain ⟨rfl, rfl⟩ := hok
          refine ⟨l1, ?_, hre1, hwe1, trivial⟩
          simp [defeqStructL, hr1]
        | false =>
          simp only [Bool.false_eq_true, if_false] at hok
          refine out_of_eq (Hstuck hwe1 hre1 hok) ?_
          simp [defeqStructL, hr1]
    | _ =>
      exact out_of_eq (Hstuck hwf hrel hok) (by simp [defeqStructL])
  | Proj s1 i1 e1 =>
    cases kb with
    | Proj s2 i2 e2 =>
      res_step hok
      obtain ⟨hs1, he1⟩ := wf_kind_inv ha rfl
      obtain ⟨hs2, he2⟩ := wf_kind_inv hb rfl
      obtain ⟨nb, hnb, hok⟩ := hok
      have hnbabs : nb = decide (absName s1 = absName s2) := Name.beq_refines hs1 hs2 hnb
      cases nb with
      | false =>
        simp only [Bool.false_eq_true, if_false] at hok
        refine out_of_eq (Hstuck hwf hrel hok) ?_
        have hne : ¬ (absName s1 = absName s2) := by
          simpa using hnbabs.symm
        simp [defeqStructL, hne]
      | true =>
        have heqn : absName s1 = absName s2 := by simpa using hnbabs.symm
        simp only [if_true] at hok
        split at hok
        · rename_i hii
          subst hii
          res_step hok
          obtain ⟨⟨rr, st1⟩, h1, hok⟩ := hok
          cases rr with
          | Err e =>
            simp at hok
            obtain ⟨rfl, rfl⟩ := hok
            refine Out.err (ErrSim.trans (Out.destErr (Hdq he1 he2 hwf hrel h1)) ?_)
            intro le hle
            simp only [StateT.run] at hle
            simp [defeqStructL, heqn, hle]
          | Ok bd =>
            obtain ⟨l1, hr1, hre1, hwe1, -⟩ := Out.dest (Hdq he1 he2 hwf hrel h1)
            simp only [StateT.run, id_eq] at hr1
            cases bd with
            | true =>
              simp only [if_true, Result.ok.injEq, Prod.mk.injEq] at hok
              obtain ⟨rfl, rfl⟩ := hok
              refine ⟨l1, ?_, hre1, hwe1, trivial⟩
              simp [defeqStructL, hr1, heqn]
            | false =>
              simp only [Bool.false_eq_true, if_false] at hok
              refine out_of_eq (Hstuck hwe1 hre1 hok) ?_
              simp [defeqStructL, hr1, heqn]
        · rename_i hii
          have hiiv : ¬ ((i1 : Std.U64).val = (i2 : Std.U64).val) := fun hx => hii (u64_val_inj hx)
          refine out_of_eq (Hstuck hwf hrel hok) ?_
          simp [defeqStructL, hiiv]
    | Lam t2 b2 m2 =>
      obtain ⟨ht2, hb2, hm2⟩ := wf_kind_inv hb rfl
      res_step hok
      obtain ⟨⟨rr, st1⟩, h1, hok⟩ := hok
      cases rr with
      | Err e =>
        simp at hok
        obtain ⟨rfl, rfl⟩ := hok
        refine Out.err (ErrSim.trans
          (Out.destErr (Heta _ _ _ _ ht2 hb2 hm2 ha hwf hrel h1)) ?_)
        intro le hle
        simp only [absExpr_mk, absExprKind, absBinderMeta, StateT.run] at hle
        simp [defeqStructL, hle]
      | Ok bd =>
        obtain ⟨l1, hr1, hre1, hwe1, -⟩ :=
          Out.dest (Heta _ _ _ _ ht2 hb2 hm2 ha hwf hrel h1)
        simp only [absExpr_mk, absExprKind, absBinderMeta, StateT.run,
          id_eq] at hr1
        cases bd with
        | true =>
          simp only [if_true, Result.ok.injEq, Prod.mk.injEq] at hok
          obtain ⟨rfl, rfl⟩ := hok
          refine ⟨l1, ?_, hre1, hwe1, trivial⟩
          simp [defeqStructL, hr1]
        | false =>
          simp only [Bool.false_eq_true, if_false] at hok
          refine out_of_eq (Hstuck hwe1 hre1 hok) ?_
          simp [defeqStructL, hr1]
    | _ =>
      exact out_of_eq (Hstuck hwf hrel hok) (by simp [defeqStructL])

end

/-! ## Axiom census (DESIGN.md §5, the P3 gate)

Every refinement in this file is axiom-clean since task #61 ungated
`const_ty_at_m` in `struct_unit_steps_i` and the four literal arms of
`defeq_struct_i` were proved (the module note). -/

/--
info: 'ConRon.Refine.Core.struct_eta_cert_i_refines' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms struct_eta_cert_i_refines

/--
info: 'ConRon.Refine.Core.struct_unit_steps_i_refines' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms struct_unit_steps_i_refines

/--
info: 'ConRon.Refine.Core.struct_unit_cert_i_refines' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms struct_unit_cert_i_refines

/--
info: 'ConRon.Refine.Core.eta_cert_body_i_refines' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms eta_cert_body_i_refines

/--
info: 'ConRon.Refine.Core.eta_cert_i_refines' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms eta_cert_i_refines

/--
info: 'ConRon.Refine.Core.defeq_struct_i_refines' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms defeq_struct_i_refines

end ConRon.Refine.Core
