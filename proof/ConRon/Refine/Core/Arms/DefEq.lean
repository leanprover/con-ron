/-
# The `defeq` body (task #55, `CORE_PLAN.md` step 6)

`crates/con-ron-core/src/cached/core_c.rs`'s definitional-equality block
against `ConLeche/Cached/CoreC.lean`: `boolTrueShortcutI` (`:1451`),
`propIrrelI` (`:331`), `stuckIrrelI` (`:536`), `defeqSpineI` (`:224`),
`defeqStepI` (`:1456-1614`), `defeqLoopI` (`:1617`) and `defeqBodyI`
(`:1624`).

Two structural facts shape the file.

**The loop.**  `defeqLoopI` recurses structurally on a `Nat` budget and
`defeqStepI` takes the continuation `k` it hands on; the Rust threads the
budget as a `U64` and six helpers call `defeq_loop_i` where con-leche calls
`k`.  So the whole group is one induction on the budget, in `Arms/Whnf.lean`'s
pattern: each `*_of_loop` helper below is stated parametric in `k` together
with its refinement (`LoopRef`), the chain `step → after_whnf → lits → delta
→ delta_both → unfold_both` is therefore acyclic, and the single induction
`defeq_loop_aux` on the budget's `val` supplies `k := defeqLoopI … m`.  Each
public `<fn>_refines` is then a corollary at
`k := defeqLoopI … n.val`.

**The split of `defeqStepI`.**  The Rust cut the cited hundred-and-sixty-line
`defeqStepI` into nine functions so that every `else` arm stays a tail
position.  Only `defeq_struct_i` (the `| false, false` structural analysis)
went to another file; the other eight are here.  A split function's con-leche
side is therefore not a named definition but a *fragment* of `defeqStepI`,
and the fragments are transcribed below as `DefEq.*Frag` — one `def` per
Rust function, verbatim from the cited lines, with the tail replaced by the
next fragment.  `defeqStepI_eq` is the (definitional) equation that says the
transcription is the cited body.

**The two `Deps` records.**  DESIGN.md task #55 found that one `DefEqDeps`
made this file and `Arms/DefEqStruct.lean` mutually unbuildable: each asked
for the whole of the other's record.  The cycle is in the packaging only —
at the function level the call order is acyclic,

    struct_eta_cert_i, struct_unit_cert_i  →  stuck_irrel_i
    stuck_irrel_i, def_eq_list_i           →  defeq_apps_i, defeq_binders_i
    defeq_apps_i, defeq_binders_i          →  defeq_struct_i
    defeq_struct_i                         →  the budget loop

so task #61 splits the record along it.  `DefEqDepsA` is everything
`defeq_struct_i` does not depend on; `DefEqDeps` is `DefEqDepsA` plus
`defeqStruct`.  `prop_irrel_i_refines`, `stuck_irrel_i_refines`,
`defeq_spine_i_refines` and `defeq_apps_i_refines` ask only for
`DefEqDepsA`, so the coordinator builds `DefEqDepsA` first, discharges
`Arms/DefEqStruct.lean`'s `DefEqStructDeps` with them, and only then
assembles `DefEqDeps` for the loop.  `extends` keeps `hd.structEtaCert` and
friends working unchanged on a `DefEqDeps`.

**The failure half (task #67).**  Every lemma is stated over the Rust's
*whole* outcome (`Refine/State.lean`'s `Out`), so each `.Err` arm is proved
rather than contradicted.  Three of the block's error sites are its own; all
three are **mirrored**, one-to-one with a `throw` in `Cached/CoreC.lean`:

| Rust | con-leche |
|---|---|
| `core_c.rs:4231` `notImplemented(M_PI)` | `CoreC.lean:1579` `throw (.notImplemented "sort-annotation mismatch (defeq-forall)")` |
| `core_c.rs:4235` `notImplemented(M_LAM)` | `CoreC.lean:1588` `… (defeq-lam)` |
| `core_c.rs:4300` `internal(defeq_loop_i.M)` | `CoreC.lean:1619` `throw (.internal "fuel exhausted: defeq loop")` |

The first two are `defeq_binders_i`'s prop-ness guard, which both sides take
at the same step under the same condition; the third is the exhausted budget,
`DefEq.defeqLoopI_zero_run`, exactly as `Core/Knot.lean`'s `wrappers_zero`
mirrors the wrappers'.  So the `.M`-suffixed `Array Std.U32` constants of the
block (`defeq_loop_i.M`, `defeq_binders_i.M_PI`, `defeq_binders_i.M_LAM`) are
message code points only — messages are never compared — and still carry no
theorem.  Every other failure here is a callee's, carried through con-leche's
`do` block by `ErrSim.bindCM`.
-/
import ConRon.Refine.Core.Arms.Shape
import ConRon.Refine.CoreKPinned
import ConRon.Refine.PropRead
import ConRon.Refine.ExprOpsC
import ConRon.Refine.Nat

open Aeneas Aeneas.Std Result
open ConRon.Generated ConRon.Generated.kernel ConRon.Generated.cached
open ConRon.Refine ConRon.Refine.State ConRon.Refine.FEnv

namespace ConRon.Refine.Core

attribute [local simp] except_pure' StateT.run modifyGet MonadStateOf.modifyGet
  StateT.modifyGet Bind.bind StateT.bind Pure.pure StateT.pure Except.bind
  Except.pure

/-- `(x >>= f).run lst` at a known `x.run lst`: the whole of the monad
plumbing the arms need (`simp` will not push a state argument through a
`match`).  `Arms/Whnf.lean`'s `run_bind`, kept private here so that the two
files do not clash. -/
private theorem run_bind' {α β : Type} {x : ConLeche.Cached.CheckCM α}
    {f : α → ConLeche.Cached.CheckCM β} {lst lst' : ConLeche.Cached.CState} {a : α}
    (h : x.run lst = .ok (a, lst')) :
    (x >>= f).run lst = (f a).run lst' := by
  simp only [StateT.run, Bind.bind, StateT.bind] at h ⊢
  rw [h]
  rfl

/-! ### Task #67's plumbing

The full-outcome statement (DESIGN.md §3's ruling of 2026-09-13) adds a
failure half to every lemma below.  Four one-liners carry it: the Rust's
`| Err err => ok (r, st1)` arm (`err_arm`), the transport of the con-leche
side along an equation (`out_of_eq`), the two `core_types` inversions, and
the applied form of a con-leche `throw` — which `simp` will not otherwise
reduce, `StateT.run` being in the plumbing set already. -/

/-- The Rust's `Err` arm of a `match` on a callee's outcome: it hands the
error straight on, which pins both the outcome and the state. -/
private theorem err_arm {α : Type} {err : kernel.core_types.CheckError}
    {o : core.result.Result α kernel.core_types.CheckError}
    {st1 st' : cached.state_c.CState}
    (h : Aeneas.Std.Result.ok (core.result.Result.Err err, st1)
      = Aeneas.Std.Result.ok (o, st')) :
    o = .Err err ∧ st' = st1 := by
  have h2 := Result.ok_injective h
  simp only [Prod.mk.injEq] at h2
  exact ⟨h2.1.symm, h2.2.symm⟩

/-- `Out` transported along an equation on the con-leche side: the tail-call
arms, where the block reduces to the callee's own run. -/
private theorem out_of_eq {α β : Type} {A : α → β} {WF : α → Prop}
    {o : core.result.Result α kernel.core_types.CheckError}
    {st' : cached.state_c.CState}
    {x y : Except ConLeche.CheckError (β × ConLeche.Cached.CState)}
    (h : Out A WF o st' y) (hxy : x = y) : Out A WF o st' x := hxy ▸ h

/-- `core_types::internal`, inverted. -/
private theorem internal_inv {v : alloc.vec.Vec Std.U32}
    {ce : kernel.core_types.CheckError} (h : core_types.internal v = ok ce) :
    ce = .Internal v := by
  rw [core_types.internal] at h; exact (Result.ok_injective h).symm

/-- `core_types::not_implemented`, inverted. -/
private theorem not_implemented_inv {v : alloc.vec.Vec Std.U32}
    {ce : kernel.core_types.CheckError} (h : core_types.not_implemented v = ok ce) :
    ce = .NotImplemented v := by
  rw [core_types.not_implemented] at h; exact (Result.ok_injective h).symm

/-- A con-leche `throw`, **applied** to the state: the plumbing set has
`StateT.run` but no `MonadExcept` instance, so this is where an explicit
`throw` arm ends. -/
@[local simp] private theorem checkCM_throw_apply {β : Type}
    (le : ConLeche.CheckError) (lst : ConLeche.Cached.CState) :
    (throw le : ConLeche.Cached.CheckCM β) lst = .error le := rfl

/-! ## The fragments of `defeqStepI`

Each `def` here is one contiguous piece of `ConLeche/Cached/CoreC.lean`'s
`defeqStepI` (`:1456-1614`), transcribed verbatim, with the piece the next
Rust function owns abstracted into a call.  `defeqStepI_eq` below checks the
transcription against the cited body. -/

namespace DefEq

open ConLeche ConLeche.Cached

/-- `CoreC.lean:253-266` / `:344-354` — the two `Prop` legs both irrelevance
twins end in: the tail of `propIrrelI` (and of `proofIrrelI`) from its
`let tta ← r.inferIO depth ta` on, at the type `ta` the caller already
inferred.  The Rust hoisted it into `prop_legs_i` (`core_c.rs:620`). -/
def propLegsFrag (r : CoreFnsI) (depth : Nat) (ta b : Expr) : CheckCM Bool := do
  let tta ← r.inferIO depth ta
  let wtta ← r.whnf depth tta
  match wtta with
  | .sort uT => do
    let z ← pure .zero
    let okA ← liftFueled "level comparison" (← isEquivLM uT z)
    let tb ← r.inferIO depth b
    let ttb ← r.inferIO depth tb
    let wttb ← r.whnf depth ttb
    match wttb with
    | .sort vT => do
      let z ← pure .zero
      let okB ← liftFueled "level comparison" (← isEquivLM vT z)
      pure (okA && okB)
    | _ => pure false
  | _ => pure false

/-- `CoreC.lean:1571-1590` — the ∀ and λ congruence arms of `defeqStepI`,
which are byte-identical apart from the message tag: the domains, the bodies
at a fresh variable of the *right* side's domain, and **last** the two
prop-ness annotations at the verified modes.  `defeq_binders_i`
(`core_c.rs:4167`) is the pair, with `msg` the tag its `is_forall` flag
picks. -/
def defeqBindersFrag (mode : CheckMode) (r : CoreFnsI) (depth : Nat) (msg : String)
    (ty₁ body₁ : Expr) (m₁ : BinderMeta) (ty₂ body₂ : Expr) (m₂ : BinderMeta) :
    CheckCM Bool := do
  unless ← r.defeq depth ty₁ ty₂ do return false
  let fv ← pure (Expr.fvar depth ty₂)
  let b₁ ← inst1M body₁ fv
  let b₂ ← inst1M body₂ fv
  unless ← r.defeq (depth + 1) b₁ b₂ do return false
  if mode.verifiedChecks && !(m₁.pw == m₂.pw) then
    throw (.notImplemented msg)
  pure true

/-- `CoreC.lean:1591-1603` — the `.app`/`.app` arm of `defeqStepI`:
spine-wise congruence with the stuck fallbacks (`defeq_apps_i`,
`core_c.rs:4225`). -/
def defeqAppsFrag (mode : CheckMode) (r : CoreFnsI) (fe : FEnv) (depth : Nat)
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

/-- `CoreC.lean:1519-1614` — the `| false, false` arm of `defeqStepI`:
structural congruence with the stuck fallbacks.  `defeq_struct_i`
(`core_c.rs:4033`) is this fragment; it mentions the continuation `k`
nowhere, which is why it needs no budget. -/
def defeqStructFrag (mode : CheckMode) (r : CoreFnsI) (fe : FEnv) (depth : Nat)
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
    defeqBindersFrag mode r depth "sort-annotation mismatch (defeq-forall)"
      ty₁ body₁ m₁ ty₂ body₂ m₂
  | .lam ty₁ body₁ m₁, .lam ty₂ body₂ m₂ =>
    defeqBindersFrag mode r depth "sort-annotation mismatch (defeq-lam)"
      ty₁ body₁ m₁ ty₂ body₂ m₂
  | .app _f₁ _a₁, .app _f₂ _a₂ => defeqAppsFrag mode r fe depth a' b'
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

/-- `CoreC.lean:1512-1514` — the tail both equal-hint arms share: unfold both
sides or answer `false` (`defeq_unfold_both_i`, `core_c.rs:4004`). -/
def defeqUnfoldBothFrag (fe : FEnv) (k : Bool → Expr → Expr → CheckCM Bool)
    (a' b' : Expr) : CheckCM Bool := do
  match ← unfoldDefinitionI fe a', ← unfoldDefinitionI fe b' with
  | some a₂, some b₂ => k false a₂ b₂
  | _, _ => pure false

/-- `CoreC.lean:1497-1517` — the `| true, true` arm: unfold the side with the
greater hint, or short-circuit the same-head spine, or unfold both
(`defeq_delta_both_i`, `core_c.rs:3963`). -/
def defeqDeltaBothFrag (r : CoreFnsI) (fe : FEnv) (depth : Nat)
    (k : Bool → Expr → Expr → CheckCM Bool) (a' b' : Expr) : CheckCM Bool := do
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
    else defeqUnfoldBothFrag fe k a' b'
  else defeqUnfoldBothFrag fe k a' b'

/-- `CoreC.lean:1488-1614` — lazy delta, decision before materialization
(`defeq_delta_i`, `core_c.rs:3927`). -/
def defeqDeltaFrag (mode : CheckMode) (r : CoreFnsI) (fe : FEnv) (depth : Nat)
    (k : Bool → Expr → Expr → CheckCM Bool) (a' b' : Expr) : CheckCM Bool := do
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
  | true, true => defeqDeltaBothFrag r fe depth k a' b'
  | false, false => defeqStructFrag mode r fe depth a' b'

/-- `CoreC.lean:1479-1614` — literal acceleration, both sides fvar-free
(`defeq_lits_i`, `core_c.rs:3881`). -/
def defeqLitsFrag (mode : CheckMode) (r : CoreFnsI) (fe : FEnv) (depth : Nat)
    (k : Bool → Expr → Expr → CheckCM Bool) (a' b' : Expr) : CheckCM Bool := do
  let fold ← pure (!Expr.hasFvar a' && !Expr.hasFvar b')
  match ← (if fold then reduceNatI r fe depth a' else pure none) with
  | some a₂ => k true a₂ b'
  | none =>
  match ← (if fold then reduceNatI r fe depth b' else pure none) with
  | some b₂ => k true a' b₂
  | none => defeqDeltaFrag mode r fe depth k a' b'

/-- `CoreC.lean:1472-1614` — the hoisted proof-irrelevance probe and
everything after it (`defeq_after_whnf_i`, `core_c.rs:3849`). -/
def defeqAfterWhnfFrag (mode : CheckMode) (r : CoreFnsI) (fe : FEnv) (depth : Nat)
    (k : Bool → Expr → Expr → CheckCM Bool) (pi : Bool) (a' b' : Expr) :
    CheckCM Bool := do
  let qp ← pure (Expr.quickPair a' b')
  if ← (if pi && !qp then propIrrelI r fe depth a' b' else pure false) then
    pure true else
  defeqLitsFrag mode r fe depth k a' b'

/-- The transcription is the cited body: `defeqStepI` is its syntactic
prefix (`CoreC.lean:1459-1471`) followed by `defeqAfterWhnfFrag`. -/
theorem defeqStepI_eq (mode : CheckMode) (r : CoreFnsI) (fe : FEnv) (depth : Nat)
    (k : Bool → Expr → Expr → CheckCM Bool) (pi : Bool) (a b : Expr) :
    defeqStepI mode r fe depth k pi a b =
      (do
        if a == b then pure true else
        let bt ← pure (Expr.isBoolTrue b)
        let af ← pure (Expr.hasFvar a)
        if ← (if pi && bt && !af then boolTrueShortcutI r depth a
            else pure false) then pure true else
        let a' ← r.whnfCore depth a
        let b' ← r.whnfCore depth b
        if a' == b' then pure true else
        defeqAfterWhnfFrag mode r fe depth k pi a' b') := by
  rw [defeqStepI]
  rfl

/-- `CoreC.lean:1617-1621` — one unrolling of `defeqLoopI`: the step at the
decremented budget. -/
theorem defeqLoopI_succ (mode : CheckMode) (r : CoreFnsI) (fe : FEnv) (depth m : Nat)
    (pi : Bool) (a b : Expr) :
    defeqLoopI mode r fe depth (m + 1) pi a b
      = defeqStepI mode r fe depth (defeqLoopI mode r fe depth m) pi a b := by
  rw [defeqLoopI]

/-- `CoreC.lean:1619` — **the exhausted budget, mirrored**: `defeqLoopI … 0`
throws `.internal`, where `defeq_loop_i`'s `n == 0` arm builds
`core_types::internal` from its `.M` table (`core_c.rs:4300`).  Same step,
same kind — which is what makes the `zero` case of `defeq_loop_aux` a real
proof under task #67, where the accept-direction statement made it
vacuous. -/
theorem defeqLoopI_zero_run (mode : CheckMode) (r : CoreFnsI) (fe : FEnv)
    (depth : Nat) (pi : Bool) (a b : Expr) (lst : CState) :
    (defeqLoopI mode r fe depth 0 pi a b).run lst
      = .error (.internal "fuel exhausted: defeq loop") := rfl

end DefEq

/-! ## The foreign callees

Eight helpers of the block live in other agents' files; here each is a field
of a structure, stated exactly as that file's `<fn>_refines` is.  The
coordinator discharges the structures, in the order the module note gives:
`DefEqDepsA` first, `DefEqDeps` — which adds `defeq_struct_i` — after. -/

/-- What `Arms/DefEq.lean` borrows *before* `defeq_struct_i` is available:
`Arms/Certs.lean`'s three, `Arms/Lits.lean`'s two and `Arms/Whnf.lean`'s
two.  The arms this file owes `Arms/DefEqStruct.lean` need only this much
— see the module note. -/
structure DefEqDepsA (mode : env.CheckMode) (fuel : Std.U64) : Prop where
  /-- `CoreC.lean:476` — `struct_eta_cert_i` refines `structEtaCertI`
  (`core_c.rs:1141`). -/
  structEtaCert : ∀ (d : Std.U64) {a b : expr.Expr}, ExprWF a → ExprWF b →
    Sim id (fun _ => True)
      (fun st fe => cached.core_c.struct_eta_cert_i mode fuel st fe d a b)
      (fun lfe => ConLeche.Cached.structEtaCertI (absMode mode)
        (knot mode lfe fuel.val) lfe d.val (absExpr a) (absExpr b))
  /-- `CoreC.lean:487` — `struct_unit_cert_i` refines `structUnitCertI`
  (`core_c.rs:1163`). -/
  structUnitCert : ∀ (d : Std.U64) {a b : expr.Expr}, ExprWF a → ExprWF b →
    Sim id (fun _ => True)
      (fun st fe => cached.core_c.struct_unit_cert_i mode fuel st fe d a b)
      (fun lfe => ConLeche.Cached.structUnitCertI (absMode mode)
        (knot mode lfe fuel.val) lfe d.val (absExpr a) (absExpr b))
  /-- `CoreC.lean:202` — `def_eq_list_i` refines `defEqListI`
  (`core_c.rs:448`). -/
  defEqList : ∀ (d : Std.U64) {xs ys : alloc.vec.Vec expr.Expr},
    ExprsWF xs → ExprsWF ys →
    Sim id (fun _ => True)
      (fun st fe => cached.core_c.def_eq_list_i mode fuel st fe d xs ys)
      (fun lfe => ConLeche.Cached.defEqListI (knot mode lfe fuel.val) lfe d.val
        (absExprs xs) (absExprs ys))
  /-- `CoreC.lean:253-266` — `prop_legs_i` refines the two `Prop` legs
  (`core_c.rs:620`), `DefEq.propLegsFrag`. -/
  propLegs : ∀ (d : Std.U64) {ta b : expr.Expr}, ExprWF ta → ExprWF b →
    Sim id (fun _ => True)
      (fun st fe => cached.core_c.prop_legs_i mode fuel st fe d ta b)
      (fun lfe => DefEq.propLegsFrag (knot mode lfe fuel.val) d.val
        (absExpr ta) (absExpr b))
  /-- `CoreC.lean:241` — `proof_irrel_i` refines `proofIrrelI`
  (`core_c.rs:568`). -/
  proofIrrel : ∀ (d : Std.U64) {a b : expr.Expr}, ExprWF a → ExprWF b →
    Sim id (fun _ => True)
      (fun st fe => cached.core_c.proof_irrel_i mode fuel st fe d a b)
      (fun lfe => ConLeche.Cached.proofIrrelI (knot mode lfe fuel.val) lfe d.val
        (absExpr a) (absExpr b))
  /-- `CoreC.lean:93` — `reduce_nat_i` refines `reduceNatI`
  (`core_c.rs:1104`).  `Arms/Whnf.lean`'s `WhnfDeps.reduceNat` verbatim. -/
  reduceNat : ∀ (d : Std.U64) {e : expr.Expr}, ExprWF e →
    Sim (Option.map absExpr) (fun o => ∀ e', o = some e' → ExprWF e')
      (fun st fe => cached.core_c.reduce_nat_i mode fuel st fe d e)
      (fun lfe => ConLeche.Cached.reduceNatI (knot mode lfe fuel.val) lfe d.val
        (absExpr e))
  /-- `CoreC.lean:69` — `unfold_definition_i` refines `unfoldDefinitionI`
  (`core_c.rs:180`).  `Arms/Whnf.lean`'s `WhnfDeps.unfoldDefinition`
  verbatim. -/
  unfoldDefinition : ∀ {e : expr.Expr}, ExprWF e →
    Sim (Option.map absExpr) (fun o => ∀ e', o = some e' → ExprWF e')
      (fun st fe => cached.core_c.unfold_definition_i st fe e)
      (fun lfe => ConLeche.Cached.unfoldDefinitionI lfe (absExpr e))

/-- All of it: `DefEqDepsA` plus `Arms/DefEqStruct.lean`'s `defeq_struct_i`,
which only the budget-loop chain below needs. -/
structure DefEqDeps (mode : env.CheckMode) (fuel : Std.U64) : Prop
    extends DefEqDepsA mode fuel where
  /-- `CoreC.lean:1519-1614` — `defeq_struct_i` refines the `| false, false`
  arm of `defeqStepI` (`core_c.rs:4033`).  The arm mentions `defeqStepI`'s
  continuation nowhere, so the statement carries no budget. -/
  defeqStruct : ∀ (d : Std.U64) {a b : expr.Expr}, ExprWF a → ExprWF b →
    Sim id (fun _ => True)
      (fun st fe => cached.core_c.defeq_struct_i mode fuel st fe d a b)
      (fun lfe => DefEq.defeqStructFrag (absMode mode) (knot mode lfe fuel.val) lfe
        d.val (absExpr a) (absExpr b))

/-! ## Four `Cached` guards against their `Kernel` twins

Task #49's lemmas conclude in the `Kernel` spelling (`Expr.hasFvar`,
`unfoldableHead`, `headHint`, `sameConstHeads`); `defeqStepI` reads the
`Cached` ones, which are the same functions on `Expr = Expr`.  These four
one-liners are the bridge. -/

private theorem hasFvarC_eq (e : ConLeche.Expr) :
    ConLeche.Expr.hasFvar e = e.hasFvar := by
  rw [ConLeche.Expr.hasFvar_eq_hasFvarFast]; rfl

private theorem unfoldableHeadC_eq {fe : fenv.FEnv} {lfe : ConLeche.FEnv}
    {e : expr.Expr} {b : Bool} (hfe : FindAgree fe lfe) (he : ExprWF e)
    (h : core_k.unfoldable_head fe e = ok b) :
    b = ConLeche.Cached.unfoldableHeadC lfe (absExpr e) := by
  rw [CoreK.unfoldable_head_refines hfe he h, ConLeche.Cached.unfoldableHeadC,
    ConLeche.Expr.getAppFn_spec]
  rfl

private theorem headHintC_eq {fe : fenv.FEnv} {lfe : ConLeche.FEnv} {e : expr.Expr}
    {r : env.ReducibilityHint} (hfe : FindAgree fe lfe) (hwf : FindWF fe)
    (he : ExprWF e) (h : core_k.head_hint fe e = ok r) :
    absHint r = ConLeche.Cached.headHintC lfe (absExpr e) := by
  rw [CoreK.head_hint_refines hfe hwf he h, ConLeche.Cached.headHintC,
    ConLeche.Expr.getAppFn_spec]
  generalize ConLeche.Expr.getAppFn (absExpr e) = f
  cases f with
  | const n us =>
    simp only []
    rcases hci : lfe.find? n with _ | ci
    · rfl
    · cases ci <;> rfl
  | _ => rfl

private theorem sameConstHeadsC_eq (a b : ConLeche.Expr) :
    ConLeche.Cached.sameConstHeadsC a b = ConLeche.sameConstHeads a b := by
  cases a <;> cases b <;>
    simp [ConLeche.Cached.sameConstHeadsC, ConLeche.sameConstHeads,
      ConLeche.Expr.getAppFn_spec]
  rfl

/-- `(pure a >>= f).run lst` is `(f a).run lst`: the cited `let x ← pure e`
bindings of `defeqStepI`, which the Rust spells as plain `let`s. -/
private theorem run_pure' {α β : Type} {a : α}
    {f : α → ConLeche.Cached.CheckCM β} {lst : ConLeche.Cached.CState} :
    ((pure a : ConLeche.Cached.CheckCM α) >>= f).run lst = (f a).run lst := rfl

/-- Under the lazy-delta guard the cited `unfoldDefinitionI` takes its
`some` branch: the `| _, _ => pure false` tail of `defeqStepI`'s equal-hint
arms is unreachable, which is what the Rust's short-circuit needs. -/
private theorem unfoldDefinitionI_not_none {lfe : ConLeche.FEnv}
    {e : ConLeche.Expr} (h : ConLeche.Cached.unfoldableHeadC lfe e = true)
    {lst lst' : ConLeche.Cached.CState} :
    (ConLeche.Cached.unfoldDefinitionI lfe e).run lst ≠ .ok (none, lst') := by
  rw [ConLeche.Cached.unfoldableHeadC] at h
  simp only [ConLeche.Cached.unfoldDefinitionI]
  cases hfn : ConLeche.Expr.getAppFn e with
  | const n us =>
    rw [hfn] at h
    dsimp only at h
    cases hf : lfe.find? n with
    | none => rw [hf] at h; simp at h
    | some ci =>
      rw [hf] at h
      cases ci with
      | defnInfo cv val hint =>
        simp only at h
        have hlen : us.length = cv.levelParams.length := by simpa using h
        simp only [hf, hlen, if_pos, run_pure']
        intro hc
        simp only [StateT.run, Bind.bind, StateT.bind, Pure.pure, StateT.pure,
          Except.bind] at hc
        repeat' split at hc
        all_goals simp at hc
      | _ => simp at h
  | _ => rw [hfn] at h; simp at h

/-- The continuation hypothesis the split helpers carry: `k` is `defeq_loop_i`
at the budget the Rust threads, which is what `defeqLoopI` passes to
`defeqStepI` as its `k`. -/
private def LoopRef (mode : env.CheckMode) (fuel : Std.U64) (d n : Std.U64)
    (k : ConLeche.FEnv → Bool → ConLeche.Expr → ConLeche.Expr →
      ConLeche.Cached.CheckCM Bool) : Prop :=
  ∀ (pi : Bool) (x y : expr.Expr), ExprWF x → ExprWF y →
    Sim id (fun _ => True)
      (fun st fe => cached.core_c.defeq_loop_i mode fuel st fe d n pi x y)
      (fun lfe => k lfe pi (absExpr x) (absExpr y))

/-! ## The arms -/

section
variable {mode : env.CheckMode} {fuel : Std.U64}

/-- `ConLeche/Cached/CoreC.lean:1451` — **`bool_true_shortcut_i` refines
`boolTrueShortcutI`** (`core_c.rs:3780`): the eq-true shortcut's reduction,
`r.whnf depth a` and then the `Bool.true` test. -/
theorem bool_true_shortcut_i_refines (hw : Wrappers mode fuel) (d : Std.U64)
    {a : expr.Expr} (ha : ExprWF a) :
    Sim id (fun _ => True)
      (fun st fe => cached.core_c.bool_true_shortcut_i mode fuel st fe d a)
      (fun lfe => ConLeche.Cached.boolTrueShortcutI (knot mode lfe fuel.val) d.val
        (absExpr a)) := by
  intro fe lfe hfe hfrel st res st' hwf hok lst hrel
  unfold cached.core_c.bool_true_shortcut_i at hok
  obtain ⟨⟨rc, st1⟩, hc, hok⟩ := bind_eq_ok_iff.mp hok
  cases rc with
  | Err err =>
    -- `whnf` threw: con-leche's `do` throws the same, at its first bind
    obtain ⟨rfl, rfl⟩ := err_arm hok
    unfold ConLeche.Cached.boolTrueShortcutI
    exact ErrSim.bindCM ((hw.whnfSim d ha).apply_err hwf hfe hc hrel hfrel)
  | Ok w =>
    obtain ⟨lst1, hrun1, hrel1, hwf1, hww⟩ :=
      (hw.whnfSim d ha).apply hwf hfe hc hrel hfrel
    obtain ⟨bb, hbb, hok⟩ := bind_eq_ok_iff.mp hok
    obtain ⟨rfl, rfl⟩ : core.result.Result.Ok bb = res ∧ st1 = st' := by
      simpa using Result.ok_injective hok
    refine ⟨lst1, ?_, hrel1, hwf1, trivial⟩
    unfold ConLeche.Cached.boolTrueShortcutI
    rw [run_bind' hrun1]
    simp [CoreK.is_bool_true_refines hww CoreK.pinned_bool_true_name hbb]

/-- `ConLeche/Cached/CoreC.lean:331` — **`prop_irrel_i` refines `propIrrelI`**
(`core_c.rs:664`): the hoisted proof-irrelevance test, the two head-symbol
fast arms in front of the `Prop` legs.  Charon duplicates the cited `else`
tail (the two `isProofFast` arms share it), so the tail is one `SimS` here and
used twice. -/
theorem prop_irrel_i_refines (hw : Wrappers mode fuel) (hd : DefEqDepsA mode fuel)
    (d : Std.U64) {a b : expr.Expr} (ha : ExprWF a) (hb : ExprWF b) :
    Sim id (fun _ => True)
      (fun st fe => cached.core_c.prop_irrel_i mode fuel st fe d a b)
      (fun lfe => ConLeche.Cached.propIrrelI (knot mode lfe fuel.val) lfe d.val
        (absExpr a) (absExpr b)) := by
  intro fe lfe hfe hfrel st res st' hwf hok lst hrel
  have hfa : FindAgree fe lfe := FindAgree.of_rel hfrel hfe
  have hfw : FindWF fe := FindWF.of_wf hfe
  have tail : SimS id (fun _ => True)
      (fun st0 => do
        let (r, st1) ← cached.core_c.infer_io mode fuel st0 fe d a
        match r with
        | .Ok ta => cached.core_c.prop_legs_i mode fuel st1 fe d ta b
        | .Err err => ok (.Err err, st1))
      (do
        let ta ← (knot mode lfe fuel.val).inferIO d.val (absExpr a)
        DefEq.propLegsFrag (knot mode lfe fuel.val) d.val ta (absExpr b)) := by
    intro st0 r0 st0' hwf0 hok0 lst0 hrel0
    obtain ⟨⟨rc, st1⟩, hc, hok0⟩ := bind_eq_ok_iff.mp hok0
    cases rc with
    | Err err =>
      obtain ⟨rfl, rfl⟩ := err_arm hok0
      exact ErrSim.bindCM ((hw.inferIOSim d ha).apply_err hwf0 hfe hc hrel0 hfrel)
    | Ok ta =>
      obtain ⟨lst1, hrun1, hrel1, hwf1, htawf⟩ :=
        (hw.inferIOSim d ha).apply hwf0 hfe hc hrel0 hfrel
      exact out_of_eq
        ((hd.propLegs d htawf hb) fe lfe hfe hfrel st1 r0 st0' hwf1 hok0 lst1 hrel1)
        (run_bind' hrun1)
  unfold cached.core_c.prop_irrel_i at hok
  simp only [ConLeche.Cached.propIrrelI]
  obtain ⟨n1, hn1, hok⟩ := bind_eq_ok_iff.mp hok
  have e1 := PropRead.not_proof_fast_refines hfa hfw ha hn1
  split at hok
  · rename_i hc1
    obtain ⟨rfl, rfl⟩ : core.result.Result.Ok false = res ∧ st = st' := by
      simpa using Result.ok_injective hok
    refine ⟨lst, ?_, hrel, hwf, trivial⟩
    rw [← e1, hc1]
    simp
  · rename_i hc1
    have hn1f : ConLeche.notProofFast lfe.find? (absExpr a) = false := by
      rw [← e1]; simpa using hc1
    obtain ⟨n2, hn2, hok⟩ := bind_eq_ok_iff.mp hok
    have e2 := PropRead.not_proof_fast_refines hfa hfw hb hn2
    split at hok
    · rename_i hc2
      obtain ⟨rfl, rfl⟩ : core.result.Result.Ok false = res ∧ st = st' := by
        simpa using Result.ok_injective hok
      refine ⟨lst, ?_, hrel, hwf, trivial⟩
      rw [hn1f, ← e2, hc2]
      simp
    · rename_i hc2
      have hn2f : ConLeche.notProofFast lfe.find? (absExpr b) = false := by
        rw [← e2]; simpa using hc2
      rw [hn1f, hn2f]
      simp only [Bool.or_self, Bool.false_eq_true, if_false]
      obtain ⟨p1, hp1, hok⟩ := bind_eq_ok_iff.mp hok
      have f1 := PropRead.is_proof_fast_refines hfa hfw ha hp1
      split at hok
      · rename_i hd1
        obtain ⟨p2, hp2, hok⟩ := bind_eq_ok_iff.mp hok
        have f2 := PropRead.is_proof_fast_refines hfa hfw hb hp2
        rw [← f1, hd1, ← f2]
        split at hok
        · rename_i hd2
          obtain ⟨rfl, rfl⟩ : core.result.Result.Ok true = res ∧ st = st' := by
            simpa using Result.ok_injective hok
          refine ⟨lst, ?_, hrel, hwf, trivial⟩
          rw [hd2]
          simp
        · rename_i hd2
          have : p2 = false := by simpa using hd2
          rw [this]
          exact tail st res st' hwf hok lst hrel
      · rename_i hd1
        have hp1f : p1 = false := by simpa using hd1
        rw [← f1, hp1f]
        simp only [Bool.false_and, Bool.false_eq_true, if_false]
        exact tail st res st' hwf hok lst hrel

/-- `ConLeche/Cached/CoreC.lean:536` — **`stuck_irrel_i` refines
`stuckIrrelI`** (`core_c.rs:1215`): structural eta in either direction, then
unit-likeness, else proof irrelevance. -/
theorem stuck_irrel_i_refines (hd : DefEqDepsA mode fuel) (d : Std.U64)
    {a b : expr.Expr} (ha : ExprWF a) (hb : ExprWF b) :
    Sim id (fun _ => True)
      (fun st fe => cached.core_c.stuck_irrel_i mode fuel st fe d a b)
      (fun lfe => ConLeche.Cached.stuckIrrelI (absMode mode) (knot mode lfe fuel.val)
        lfe d.val (absExpr a) (absExpr b)) := by
  intro fe lfe hfe hfrel st res st' hwf hok lst hrel
  unfold cached.core_c.stuck_irrel_i at hok
  simp only [ConLeche.Cached.stuckIrrelI]
  obtain ⟨⟨r1, st1⟩, h1, hok⟩ := bind_eq_ok_iff.mp hok
  cases r1 with
  | Err err =>
    obtain ⟨rfl, rfl⟩ := err_arm hok
    exact ErrSim.bindCM ((hd.structEtaCert d ha hb).apply_err hwf hfe h1 hrel hfrel)
  | Ok v1 =>
    obtain ⟨lst1, hrun1, hrel1, hwf1, -⟩ :=
      (hd.structEtaCert d ha hb).apply hwf hfe h1 hrel hfrel
    simp only [id] at hrun1
    rw [run_bind' hrun1]
    cases v1 with
    | true =>
      obtain ⟨rfl, rfl⟩ : core.result.Result.Ok true = res ∧ st1 = st' := by
        simpa using Result.ok_injective hok
      exact ⟨lst1, by simp, hrel1, hwf1, trivial⟩
    | false =>
      simp only [Bool.false_eq_true, if_false] at hok ⊢
      obtain ⟨⟨r2, st2⟩, h2, hok⟩ := bind_eq_ok_iff.mp hok
      cases r2 with
      | Err err =>
        obtain ⟨rfl, rfl⟩ := err_arm hok
        exact ErrSim.bindCM ((hd.structEtaCert d hb ha).apply_err hwf1 hfe h2 hrel1 hfrel)
      | Ok v2 =>
        obtain ⟨lst2, hrun2, hrel2, hwf2, -⟩ :=
          (hd.structEtaCert d hb ha).apply hwf1 hfe h2 hrel1 hfrel
        simp only [id] at hrun2
        rw [run_bind' hrun2]
        cases v2 with
        | true =>
          obtain ⟨rfl, rfl⟩ : core.result.Result.Ok true = res ∧ st2 = st' := by
            simpa using Result.ok_injective hok
          exact ⟨lst2, by simp, hrel2, hwf2, trivial⟩
        | false =>
          simp only [Bool.false_eq_true, if_false] at hok ⊢
          obtain ⟨⟨r3, st3⟩, h3, hok⟩ := bind_eq_ok_iff.mp hok
          cases r3 with
          | Err err =>
            obtain ⟨rfl, rfl⟩ := err_arm hok
            exact ErrSim.bindCM ((hd.structUnitCert d ha hb).apply_err hwf2 hfe h3 hrel2 hfrel)
          | Ok v3 =>
            obtain ⟨lst3, hrun3, hrel3, hwf3, -⟩ :=
              (hd.structUnitCert d ha hb).apply hwf2 hfe h3 hrel2 hfrel
            simp only [id] at hrun3
            rw [run_bind' hrun3]
            cases v3 with
            | true =>
              obtain ⟨rfl, rfl⟩ : core.result.Result.Ok true = res ∧ st3 = st' := by
                simpa using Result.ok_injective hok
              exact ⟨lst3, by simp, hrel3, hwf3, trivial⟩
            | false =>
              simp only [Bool.false_eq_true, if_false] at hok ⊢
              exact (hd.proofIrrel d ha hb) fe lfe hfe hfrel st3 res st' hwf3 hok lst3 hrel3

/-- `ConLeche/Cached/CoreC.lean:224` — **`defeq_spine_i` refines
`defeqSpineI`** (`core_c.rs:527`): the lazy-delta same-head short-circuit,
levels through `isEquivListLM` and then the argument lists.  A `false` verdict
is never final, so an inconclusive level comparison simply answers `false`. -/
theorem defeq_spine_i_refines (hd : DefEqDepsA mode fuel) (d : Std.U64)
    {a b : expr.Expr} (ha : ExprWF a) (hb : ExprWF b) :
    Sim id (fun _ => True)
      (fun st fe => cached.core_c.defeq_spine_i mode fuel st fe d a b)
      (fun lfe => ConLeche.Cached.defeqSpineI (knot mode lfe fuel.val) lfe d.val
        (absExpr a) (absExpr b)) := by
  intro fe lfe hfe hfrel st res st' hwf hok lst hrel
  unfold cached.core_c.defeq_spine_i at hok
  simp only [arc_deref_eq, bind_tc_ok] at hok
  obtain ⟨fa, hfa, hok⟩ := bind_eq_ok_iff.mp hok
  obtain ⟨fb, hfb, hok⟩ := bind_eq_ok_iff.mp hok
  obtain ⟨hfaabs, hfawf⟩ := ExprOps.get_app_fn_refines ha hfa
  obtain ⟨hfbabs, hfbwf⟩ := ExprOps.get_app_fn_refines hb hfb
  simp only [ConLeche.Cached.defeqSpineI, ConLeche.Expr.getAppFn_spec,
    ← hfaabs, ← hfbabs]
  obtain ⟨⟨da, ka⟩⟩ := fa
  obtain ⟨⟨db, kb⟩⟩ := fb
  simp only [ExprOps.node_kind] at hok
  simp only [absExpr_mk]
  cases ka with
  | Const n us =>
    cases kb with
    | Const n2 us2 =>
      obtain ⟨args_a, hargsa, hok⟩ := bind_eq_ok_iff.mp hok
      obtain ⟨args_b, hargsb, hok⟩ := bind_eq_ok_iff.mp hok
      obtain ⟨b1, hb1, hok⟩ := bind_eq_ok_iff.mp hok
      obtain ⟨haa, hawf⟩ := ExprOps.get_app_args_refines ha hargsa
      obtain ⟨hbb, hbwf⟩ := ExprOps.get_app_args_refines hb hargsb
      obtain ⟨hnwf, huswf⟩ := CoreK.wf_const_inv hfawf rfl
      obtain ⟨hn2wf, hus2wf⟩ := CoreK.wf_const_inv hfbwf rfl
      have e1 := Name.beq_refines hnwf hn2wf hb1
      simp only [absExprKind, ConLeche.Expr.getAppArgsC_spec, ← haa, ← hbb]
      split at hok
      · rename_i hcb1
        have hne : absName n = absName n2 := by
          rw [hcb1] at e1; exact of_decide_eq_true e1.symm
        split at hok
        · rename_i hlen
          have hlen' : args_a.val.length = args_b.val.length := by
            have h1 : (alloc.vec.Vec.len args_a).val = args_a.val.length :=
              alloc.vec.Vec.len_val args_a
            have h2 : (alloc.vec.Vec.len args_b).val = args_b.val.length :=
              alloc.vec.Vec.len_val args_b
            rw [hlen] at h1; omega
          obtain ⟨⟨o, st1⟩, ho, hok⟩ := bind_eq_ok_iff.mp hok
          obtain ⟨lst1, hrun1, hrel1, hwf1⟩ :=
            StateC.is_equiv_list_l_m_refines hwf huswf hus2wf ho lst hrel
          simp only [StateT.run] at hrun1
          cases o with
          | none =>
            obtain ⟨rfl, rfl⟩ : core.result.Result.Ok false = res ∧ st1 = st' := by
              simpa using Result.ok_injective hok
            exact ⟨lst1, by simp [absExprs, hne, hlen', hrun1], hrel1, hwf1, trivial⟩
          | some v =>
            cases v with
            | true =>
              -- a tail call: con-leche's block *is* `defEqListI` from here,
              -- so the whole outcome passes straight through
              refine out_of_eq
                ((hd.defEqList d hawf hbwf) fe lfe hfe hfrel st1 res st' hwf1 hok lst1
                  hrel1) ?_
              simp [absExprs, hne, hlen', hrun1]
            | false =>
              obtain ⟨rfl, rfl⟩ : core.result.Result.Ok false = res ∧ st1 = st' := by
                simpa using Result.ok_injective hok
              exact ⟨lst1, by simp [absExprs, hne, hlen', hrun1], hrel1, hwf1, trivial⟩
        · rename_i hlen
          have hlen' : ¬ args_a.val.length = args_b.val.length := by
            intro hc
            refine hlen ?_
            have h1 : (alloc.vec.Vec.len args_a).val = args_a.val.length :=
              alloc.vec.Vec.len_val args_a
            have h2 : (alloc.vec.Vec.len args_b).val = args_b.val.length :=
              alloc.vec.Vec.len_val args_b
            scalar_tac
          obtain ⟨rfl, rfl⟩ : core.result.Result.Ok false = res ∧ st = st' := by
            simpa using Result.ok_injective hok
          exact ⟨lst, by simp [absExprs, hlen'], hrel, hwf, trivial⟩
      · rename_i hcb1
        have hne : ¬ absName n = absName n2 := by
          have hb1f : b1 = false := by simpa using hcb1
          rw [hb1f] at e1; exact of_decide_eq_false e1.symm
        obtain ⟨rfl, rfl⟩ : core.result.Result.Ok false = res ∧ st = st' := by
          simpa using Result.ok_injective hok
        exact ⟨lst, by simp [absExprs, hne], hrel, hwf, trivial⟩
    | _ =>
      obtain ⟨rfl, rfl⟩ : core.result.Result.Ok false = res ∧ st = st' := by
        simpa using Result.ok_injective hok
      exact ⟨lst, by simp [absExprKind], hrel, hwf, trivial⟩
  | _ =>
    obtain ⟨rfl, rfl⟩ : core.result.Result.Ok false = res ∧ st = st' := by
      simpa using Result.ok_injective hok
    exact ⟨lst, by simp [absExprKind], hrel, hwf, trivial⟩


/-- `ConLeche/Cached/CoreC.lean:1571-1590` — **`defeq_binders_i` refines the
∀/λ congruence arms** (`core_c.rs:4167`): the domains, the bodies at a fresh
variable of the *right* side's domain, and last the prop-ness annotations at
the verified modes.  The two arms are byte-identical apart from the message,
which the `is_forall` flag picks.

This is the block's one **explicit throw** (task #67): under a verified mode
with disagreeing `pw` annotations the Rust returns
`not_implemented(M_PI | M_LAM)` (`core_c.rs:4231`/`:4235`) exactly where the
cited body throws `.notImplemented` (`CoreC.lean:1579`/`:1588`) — same step,
same kind, and the messages are not compared. -/
theorem defeq_binders_i_refines (hw : Wrappers mode fuel) (d : Std.U64)
    {t1 bo1 t2 bo2 : expr.Expr} {m1 m2 : expr.BinderMeta} (is_forall : Bool)
    (ht1 : ExprWF t1) (hbo1 : ExprWF bo1) (hm1 : BinderMetaWF m1)
    (ht2 : ExprWF t2) (hbo2 : ExprWF bo2) (hm2 : BinderMetaWF m2) :
    Sim id (fun _ => True)
      (fun st fe =>
        cached.core_c.defeq_binders_i mode fuel st fe d t1 bo1 m1 t2 bo2 m2 is_forall)
      (fun lfe => DefEq.defeqBindersFrag (absMode mode) (knot mode lfe fuel.val) d.val
        (if is_forall then "sort-annotation mismatch (defeq-forall)"
          else "sort-annotation mismatch (defeq-lam)")
        (absExpr t1) (absExpr bo1) (absBinderMeta m1)
        (absExpr t2) (absExpr bo2) (absBinderMeta m2)) := by
  intro fe lfe hfe hfrel st res st' hwf hok lst hrel
  unfold cached.core_c.defeq_binders_i at hok
  simp only [arc_deref_eq, bind_tc_ok] at hok
  simp only [DefEq.defeqBindersFrag]
  obtain ⟨⟨r1, st1⟩, h1, hok⟩ := bind_eq_ok_iff.mp hok
  cases r1 with
  | Err err =>
    obtain ⟨rfl, rfl⟩ := err_arm hok
    exact ErrSim.bindCM ((hw.defeqSim d ht1 ht2).apply_err hwf hfe h1 hrel hfrel)
  | Ok v1 =>
    obtain ⟨lst1, hrun1, hrel1, hwf1, -⟩ :=
      (hw.defeqSim d ht1 ht2).apply hwf hfe h1 hrel hfrel
    simp only [id] at hrun1
    rw [run_bind' hrun1]
    cases v1 with
    | false =>
      obtain ⟨rfl, rfl⟩ : core.result.Result.Ok false = res ∧ st1 = st' := by
        simpa using Result.ok_injective hok
      exact ⟨lst1, by simp, hrel1, hwf1, trivial⟩
    | true =>
      obtain ⟨e2, he2, hok⟩ := bind_eq_ok_iff.mp hok
      rw [Expr.dup_eq he2] at hok
      obtain ⟨v, hv, hok⟩ := bind_eq_ok_iff.mp hok
      have hvabs : absExpr v = ConLeche.Expr.fvar d.val (absExpr t2) := Expr.fvar_refines hv
      have hvwf : ExprWF v := Expr.fvar_wf ht2 hv
      obtain ⟨o1, ho1, hok⟩ := bind_eq_ok_iff.mp hok
      obtain ⟨o2, ho2, hok⟩ := bind_eq_ok_iff.mp hok
      rw [StateC.inst1_m_eq] at ho1 ho2
      obtain ⟨ho1a, ho1w⟩ := ExprOpsC.instantiate1_refines hbo1 hvwf ho1
      obtain ⟨ho2a, ho2w⟩ := ExprOpsC.instantiate1_refines hbo2 hvwf ho2
      obtain ⟨i, hi, hok⟩ := bind_eq_ok_iff.mp hok
      have hiv : i.val = d.val + 1 := by
        have := ConRon.Refine.Nat.uadd_val hi; simpa using this
      obtain ⟨⟨r2, st2⟩, h2, hok⟩ := bind_eq_ok_iff.mp hok
      cases r2 with
      | Err err =>
        -- the body comparison threw; the two `inst1M` steps in front of it
        -- cannot, so con-leche reaches the same call and throws the same
        obtain ⟨rfl, rfl⟩ := err_arm hok
        refine ErrSim.trans ((hw.defeqSim i ho1w ho2w).apply_err hwf1 hfe h2 hrel1 hfrel) ?_
        intro le hle
        simp only [hiv, ho1a, ho2a, hvabs, StateT.run, Expr.val_zero] at hle
        simp [ConLeche.Cached.inst1M, hle]
      | Ok v2 =>
        obtain ⟨lst2, hrun2, hrel2, hwf2, -⟩ :=
          (hw.defeqSim i ho1w ho2w).apply hwf1 hfe h2 hrel1 hfrel
        simp only [id, hiv, ho1a, ho2a, hvabs, StateT.run, Expr.val_zero] at hrun2
        cases v2 with
        | false =>
          obtain ⟨rfl, rfl⟩ : core.result.Result.Ok false = res ∧ st2 = st' := by
            simpa using Result.ok_injective hok
          exact ⟨lst2, by simp [ConLeche.Cached.inst1M, hrun2], hrel2, hwf2, trivial⟩
        | true =>
          obtain ⟨b4, hb4, hok⟩ := bind_eq_ok_iff.mp hok
          have e4 := Env.verified_checks_refines hb4
          split at hok
          · rename_i hc4
            obtain ⟨b5, hb5, hok⟩ := bind_eq_ok_iff.mp hok
            have e5 := PropWhen.beq_refines hm1 hm2 hb5
            split at hok
            · rename_i hc5
              obtain ⟨rfl, rfl⟩ : core.result.Result.Ok true = res ∧ st2 = st' := by
                simpa using Result.ok_injective hok
              refine ⟨lst2, ?_, hrel2, hwf2, trivial⟩
              have hpw : absPropWhen m1.pw = absPropWhen m2.pw := by
                rw [hc5] at e5; exact of_decide_eq_true e5.symm
              simp [ConLeche.Cached.inst1M, hrun2, absBinderMeta, hpw]
            · rename_i hc5
              -- **the mirrored `notImplemented`** (`core_c.rs:4231`/`:4235`
              -- against `CoreC.lean:1579`/`:1588`): the verified mode with
              -- disagreeing prop-ness annotations makes *both* sides throw,
              -- at the same step and the same kind; the message is the tag
              -- the `is_forall` flag picks, and is never compared
              have hvc : (absMode mode).verifiedChecks = true := by
                have hb4t : b4 = true := by simpa using hc4
                rw [hb4t] at e4; exact e4.symm
              have hpw : ¬ absPropWhen m1.pw = absPropWhen m2.pw := by
                have hb5f : b5 = false := by simpa using hc5
                rw [hb5f] at e5; exact of_decide_eq_false e5.symm
              cases is_forall with
              | true =>
                simp only [if_true, bind_eq_ok_iff] at hok
                obtain ⟨_, -, _, -, ce, hce, hres⟩ := hok
                obtain ⟨rfl, rfl⟩ : core.result.Result.Err ce = res ∧ st2 = st' := by
                  simpa using hres
                rw [not_implemented_inv hce]
                refine ErrSim.notImplemented
                  (s := "sort-annotation mismatch (defeq-forall)") ?_
                simp [ConLeche.Cached.inst1M, hrun2, absBinderMeta, hvc, hpw]
              | false =>
                simp only [Bool.false_eq_true, if_false, bind_eq_ok_iff] at hok
                obtain ⟨_, -, _, -, ce, hce, hres⟩ := hok
                obtain ⟨rfl, rfl⟩ : core.result.Result.Err ce = res ∧ st2 = st' := by
                  simpa using hres
                rw [not_implemented_inv hce]
                refine ErrSim.notImplemented
                  (s := "sort-annotation mismatch (defeq-lam)") ?_
                simp [ConLeche.Cached.inst1M, hrun2, absBinderMeta, hvc, hpw]
          · rename_i hc4
            obtain ⟨rfl, rfl⟩ : core.result.Result.Ok true = res ∧ st2 = st' := by
              simpa using Result.ok_injective hok
            refine ⟨lst2, ?_, hrel2, hwf2, trivial⟩
            have hv4 : (absMode mode).verifiedChecks = false := by
              have hb4f : b4 = false := by simpa using hc4
              rw [hb4f] at e4; exact e4.symm
            simp [ConLeche.Cached.inst1M, hrun2, hv4]


/-- `ConLeche/Cached/CoreC.lean:1591-1603` — **`defeq_apps_i` refines the
`.app`/`.app` arm** (`core_c.rs:4225`): spine-wise congruence — equal spine
lengths, one head comparison, the argument lists pairwise, then the stuck
fallbacks. -/
theorem defeq_apps_i_refines (hw : Wrappers mode fuel) (hd : DefEqDepsA mode fuel)
    (d : Std.U64) {a b : expr.Expr} (ha : ExprWF a) (hb : ExprWF b) :
    Sim id (fun _ => True)
      (fun st fe => cached.core_c.defeq_apps_i mode fuel st fe d a b)
      (fun lfe => DefEq.defeqAppsFrag (absMode mode) (knot mode lfe fuel.val) lfe d.val
        (absExpr a) (absExpr b)) := by
  intro fe lfe hfe hfrel st res st' hwf hok lst hrel
  unfold cached.core_c.defeq_apps_i at hok
  dsimp only at hok
  obtain ⟨args_a, hargsa, hok⟩ := bind_eq_ok_iff.mp hok
  obtain ⟨args_b, hargsb, hok⟩ := bind_eq_ok_iff.mp hok
  obtain ⟨haa, hawf⟩ := ExprOps.get_app_args_refines ha hargsa
  obtain ⟨hbb, hbwf⟩ := ExprOps.get_app_args_refines hb hargsb
  have hla : (alloc.vec.Vec.len args_a).val = args_a.val.length :=
    alloc.vec.Vec.len_val args_a
  have hlb : (alloc.vec.Vec.len args_b).val = args_b.val.length :=
    alloc.vec.Vec.len_val args_b
  simp only [DefEq.defeqAppsFrag, ConLeche.Expr.getAppArgsC_spec, ← haa, ← hbb]
  split at hok
  · rename_i hlen
    have hlen' : ¬ (args_a.val.length = args_b.val.length) := by
      intro hc; simp only [bne_iff_ne, ne_eq] at hlen; exact hlen (by scalar_tac)
    exact out_of_eq
      ((stuck_irrel_i_refines hd d ha hb) fe lfe hfe hfrel st res st' hwf hok lst hrel)
      (by simp [absExprs, hlen'])
  · rename_i hlen
    have hlen' : args_a.val.length = args_b.val.length := by
      simp only [bne_iff_ne, ne_eq, Decidable.not_not] at hlen
      rw [hlen] at hla; omega
    obtain ⟨fa, hfa, hok⟩ := bind_eq_ok_iff.mp hok
    obtain ⟨fb, hfb, hok⟩ := bind_eq_ok_iff.mp hok
    obtain ⟨hfaabs, hfawf⟩ := ExprOps.get_app_fn_refines ha hfa
    obtain ⟨hfbabs, hfbwf⟩ := ExprOps.get_app_fn_refines hb hfb
    simp only [ConLeche.Expr.getAppFn_spec, ← hfaabs, ← hfbabs]
    obtain ⟨⟨r1, st1⟩, h1, hok⟩ := bind_eq_ok_iff.mp hok
    cases r1 with
    | Err err =>
      obtain ⟨rfl, rfl⟩ := err_arm hok
      refine ErrSim.trans ((hw.defeqSim d hfawf hfbwf).apply_err hwf hfe h1 hrel hfrel) ?_
      intro le hle
      simp only [StateT.run] at hle
      simp [absExprs, hlen', hle]
    | Ok v1 =>
      obtain ⟨lst1, hrun1, hrel1, hwf1, -⟩ :=
        (hw.defeqSim d hfawf hfbwf).apply hwf hfe h1 hrel hfrel
      simp only [id, StateT.run] at hrun1
      cases v1 with
      | false =>
        exact out_of_eq
          ((stuck_irrel_i_refines hd d ha hb) fe lfe hfe hfrel st1 res st' hwf1 hok lst1
            hrel1)
          (by simp [absExprs, hlen', hrun1])
      | true =>
        obtain ⟨⟨r2, st2⟩, h2, hok⟩ := bind_eq_ok_iff.mp hok
        cases r2 with
        | Err err =>
          obtain ⟨rfl, rfl⟩ := err_arm hok
          refine ErrSim.trans ((hd.defEqList d hawf hbwf).apply_err hwf1 hfe h2 hrel1 hfrel) ?_
          intro le hle
          simp only [StateT.run, absExprs] at hle
          simp [absExprs, hlen', hrun1, hle]
        | Ok v2 =>
          obtain ⟨lst2, hrun2, hrel2, hwf2, -⟩ :=
            (hd.defEqList d hawf hbwf).apply hwf1 hfe h2 hrel1 hfrel
          simp only [id, StateT.run, absExprs] at hrun2
          cases v2 with
          | true =>
            obtain ⟨rfl, rfl⟩ : core.result.Result.Ok true = res ∧ st2 = st' := by
              simpa using Result.ok_injective hok
            exact ⟨lst2, by simp [absExprs, hlen', hrun1, hrun2], hrel2, hwf2, trivial⟩
          | false =>
            exact out_of_eq
              ((stuck_irrel_i_refines hd d ha hb) fe lfe hfe hfrel st2 res st' hwf2 hok lst2
                hrel2)
              (by simp [absExprs, hlen', hrun1, hrun2])
/-- `ConLeche/Cached/CoreC.lean:1512-1514` — **`defeq_unfold_both_i` refines
the tail both equal-hint arms share** (`core_c.rs:4004`).

*The one place the canonical `Sim` shape needs the lazy-delta guards.*  The
cited `match ← unfoldDefinitionI fe a', ← unfoldDefinitionI fe b'` runs
**both** effects and only then matches, where the Rust short-circuits on the
first `None`; the two agree exactly because the `| _, _ => pure false` arm is
unreachable — under `unfoldableHeadC` on both sides `unfoldDefinitionI` takes
its `some` branch (`unfoldDefinitionI_not_none`).  Both guards hold at the
only call site, `defeq_delta_both_i` inside `defeq_delta_i`'s `true, true`
arm, so the caller discharges them. -/
private theorem defeq_unfold_both_of_loop (hd : DefEqDeps mode fuel) (d n : Std.U64)
    {k : ConLeche.FEnv → Bool → ConLeche.Expr → ConLeche.Expr →
      ConLeche.Cached.CheckCM Bool} (hk : LoopRef mode fuel d n k)
    {a2 b2 : expr.Expr} (ha : ExprWF a2) (hb : ExprWF b2)
    (fe : fenv.FEnv) (lfe : ConLeche.FEnv) (hfe : FEnvWF fe) (hfrel : FEnvRel fe lfe)
    (hua : ConLeche.Cached.unfoldableHeadC lfe (absExpr a2) = true)
    (hub : ConLeche.Cached.unfoldableHeadC lfe (absExpr b2) = true) :
    SimS id (fun _ => True)
      (fun st => cached.core_c.defeq_unfold_both_i mode fuel st fe d n a2 b2)
      (DefEq.defeqUnfoldBothFrag lfe (k lfe) (absExpr a2) (absExpr b2)) := by
  intro st res st' hwf hok lst hrel
  unfold cached.core_c.defeq_unfold_both_i at hok
  simp only [DefEq.defeqUnfoldBothFrag]
  obtain ⟨⟨r1, st1⟩, h1, hok⟩ := bind_eq_ok_iff.mp hok
  cases r1 with
  | Err err =>
    obtain ⟨rfl, rfl⟩ := err_arm hok
    exact ErrSim.bindCM ((hd.unfoldDefinition ha).apply_err hwf hfe h1 hrel hfrel)
  | Ok o =>
    obtain ⟨lst1, hrun1, hrel1, hwf1, howf⟩ :=
      (hd.unfoldDefinition ha).apply hwf hfe h1 hrel hfrel
    cases o with
    | none =>
      simp only [Option.map_none] at hrun1
      exact absurd hrun1 (unfoldDefinitionI_not_none hua)
    | some a3 =>
      simp only [Option.map_some] at hrun1
      rw [run_bind' hrun1]
      obtain ⟨⟨r2, st2⟩, h2, hok⟩ := bind_eq_ok_iff.mp hok
      cases r2 with
      | Err err =>
        obtain ⟨rfl, rfl⟩ := err_arm hok
        exact ErrSim.bindCM ((hd.unfoldDefinition hb).apply_err hwf1 hfe h2 hrel1 hfrel)
      | Ok o2 =>
        obtain ⟨lst2, hrun2, hrel2, hwf2, howf2⟩ :=
          (hd.unfoldDefinition hb).apply hwf1 hfe h2 hrel1 hfrel
        cases o2 with
        | none =>
          simp only [Option.map_none] at hrun2
          exact absurd hrun2 (unfoldDefinitionI_not_none hub)
        | some b3 =>
          simp only [Option.map_some] at hrun2
          rw [run_bind' hrun2]
          exact (hk false a3 b3 (howf a3 rfl) (howf2 b3 rfl)) fe lfe hfe hfrel st2 res st'
            hwf2 hok lst2 hrel2

/-- `ConLeche/Cached/CoreC.lean:1497-1517` — **`defeq_delta_both_i` refines
the `| true, true` arm** (`core_c.rs:3963`): unfold the side with the greater
hint, else try the same-head spine short-circuit, else unfold both.  The two
lazy-delta guards travel with it because its tail is
`defeq_unfold_both_i`'s. -/
private theorem defeq_delta_both_of_loop (hd : DefEqDeps mode fuel) (d n : Std.U64)
    {k : ConLeche.FEnv → Bool → ConLeche.Expr → ConLeche.Expr →
      ConLeche.Cached.CheckCM Bool} (hk : LoopRef mode fuel d n k)
    {a2 b2 : expr.Expr} (ha : ExprWF a2) (hb : ExprWF b2)
    (fe : fenv.FEnv) (lfe : ConLeche.FEnv) (hfe : FEnvWF fe) (hfrel : FEnvRel fe lfe)
    (hua : ConLeche.Cached.unfoldableHeadC lfe (absExpr a2) = true)
    (hub : ConLeche.Cached.unfoldableHeadC lfe (absExpr b2) = true) :
    SimS id (fun _ => True)
      (fun st => cached.core_c.defeq_delta_both_i mode fuel st fe d n a2 b2)
      (DefEq.defeqDeltaBothFrag (knot mode lfe fuel.val) lfe d.val (k lfe)
        (absExpr a2) (absExpr b2)) := by
  have hfa : FindAgree fe lfe := FindAgree.of_rel hfrel hfe
  have hfw : FindWF fe := FindWF.of_wf hfe
  intro st res st' hwf hok lst hrel
  unfold cached.core_c.defeq_delta_both_i at hok
  simp only [DefEq.defeqDeltaBothFrag]
  rw [run_pure', run_pure']
  obtain ⟨hA, hhA, hok⟩ := bind_eq_ok_iff.mp hok
  obtain ⟨hB, hhB, hok⟩ := bind_eq_ok_iff.mp hok
  have eA := headHintC_eq hfa hfw ha hhA
  have eB := headHintC_eq hfa hfw hb hhB
  rw [← eA, ← eB]
  obtain ⟨c1, hc1, hok⟩ := bind_eq_ok_iff.mp hok
  have e1 := Env.reducibility_hint_lt_refines hc1
  rw [← e1]
  cases c1 with
  | true =>
    simp only [if_true]
    obtain ⟨⟨r1, st1⟩, h1, hok⟩ := bind_eq_ok_iff.mp hok
    cases r1 with
    | Err err =>
      obtain ⟨rfl, rfl⟩ := err_arm hok
      exact ErrSim.bindCM ((hd.unfoldDefinition ha).apply_err hwf hfe h1 hrel hfrel)
    | Ok o =>
      obtain ⟨lst1, hrun1, hrel1, hwf1, howf⟩ :=
        (hd.unfoldDefinition ha).apply hwf hfe h1 hrel hfrel
      cases o with
      | none =>
        simp only [Option.map_none] at hrun1
        rw [run_bind' hrun1]
        obtain ⟨rfl, rfl⟩ : core.result.Result.Ok false = res ∧ st1 = st' := by
          simpa using Result.ok_injective hok
        exact ⟨lst1, by simp, hrel1, hwf1, trivial⟩
      | some a3 =>
        simp only [Option.map_some] at hrun1
        rw [run_bind' hrun1]
        exact (hk false a3 b2 (howf a3 rfl) hb) fe lfe hfe hfrel st1 res st' hwf1 hok lst1
          hrel1
  | false =>
    simp only [Bool.false_eq_true, if_false]
    obtain ⟨c2, hc2, hok⟩ := bind_eq_ok_iff.mp hok
    have e2 := Env.reducibility_hint_lt_refines hc2
    rw [← e2]
    cases c2 with
    | true =>
      simp only [if_true]
      obtain ⟨⟨r1, st1⟩, h1, hok⟩ := bind_eq_ok_iff.mp hok
      cases r1 with
      | Err err =>
        obtain ⟨rfl, rfl⟩ := err_arm hok
        exact ErrSim.bindCM ((hd.unfoldDefinition hb).apply_err hwf hfe h1 hrel hfrel)
      | Ok o =>
        obtain ⟨lst1, hrun1, hrel1, hwf1, howf⟩ :=
          (hd.unfoldDefinition hb).apply hwf hfe h1 hrel hfrel
        cases o with
        | none =>
          simp only [Option.map_none] at hrun1
          rw [run_bind' hrun1]
          obtain ⟨rfl, rfl⟩ : core.result.Result.Ok false = res ∧ st1 = st' := by
            simpa using Result.ok_injective hok
          exact ⟨lst1, by simp, hrel1, hwf1, trivial⟩
        | some b3 =>
          simp only [Option.map_some] at hrun1
          rw [run_bind' hrun1]
          exact (hk false a2 b3 ha (howf b3 rfl)) fe lfe hfe hfrel st1 res st' hwf1 hok lst1
            hrel1
    | false =>
      simp only [Bool.false_eq_true, if_false]
      rw [run_pure']
      obtain ⟨c3, hc3, hok⟩ := bind_eq_ok_iff.mp hok
      have e3 := Env.reducibility_hint_same_regular_refines hc3
      rw [← e3]
      cases c3 with
      | false =>
        simp only [Bool.false_and, Bool.false_eq_true, if_false]
        exact defeq_unfold_both_of_loop hd d n hk ha hb fe lfe hfe hfrel hua hub
          st res st' hwf hok lst hrel
      | true =>
        obtain ⟨c4, hc4, hok⟩ := bind_eq_ok_iff.mp hok
        have e4 := CoreK.same_const_heads_refines ha hb hc4
        rw [sameConstHeadsC_eq, ← e4]
        cases c4 with
        | false =>
          simp only [Bool.and_false, Bool.false_eq_true, if_false]
          exact defeq_unfold_both_of_loop hd d n hk ha hb fe lfe hfe hfrel hua hub
            st res st' hwf hok lst hrel
        | true =>
          simp only [Bool.and_self, if_true]
          obtain ⟨⟨r1, st1⟩, h1, hok⟩ := bind_eq_ok_iff.mp hok
          cases r1 with
          | Err err =>
            obtain ⟨rfl, rfl⟩ := err_arm hok
            exact ErrSim.bindCM
              ((defeq_spine_i_refines hd.toDefEqDepsA d ha hb).apply_err hwf hfe h1 hrel hfrel)
          | Ok v =>
            obtain ⟨lst1, hrun1, hrel1, hwf1, -⟩ :=
              (defeq_spine_i_refines hd.toDefEqDepsA d ha hb).apply hwf hfe h1 hrel
                hfrel
            simp only [id] at hrun1
            rw [run_bind' hrun1]
            cases v with
            | true =>
              obtain ⟨rfl, rfl⟩ : core.result.Result.Ok true = res ∧ st1 = st' := by
                simpa using Result.ok_injective hok
              exact ⟨lst1, by simp, hrel1, hwf1, trivial⟩
            | false =>
              simp only [Bool.false_eq_true, if_false]
              exact defeq_unfold_both_of_loop hd d n hk ha hb fe lfe hfe hfrel hua hub
                st1 res st' hwf1 hok lst1 hrel1

/-- `ConLeche/Cached/CoreC.lean:1488-1614` — **`defeq_delta_i` refines lazy
delta** (`core_c.rs:3927`): the two heads decide which side to unfold, and
`unfoldDefinitionI` runs only inside the branch that consumes it.  Neither
head unfoldable is `defeq_struct_i`'s arm, `Arms/DefEqStruct.lean`'s. -/
private theorem defeq_delta_of_loop (hd : DefEqDeps mode fuel) (d n : Std.U64)
    {k : ConLeche.FEnv → Bool → ConLeche.Expr → ConLeche.Expr →
      ConLeche.Cached.CheckCM Bool} (hk : LoopRef mode fuel d n k)
    {a2 b2 : expr.Expr} (ha : ExprWF a2) (hb : ExprWF b2) :
    Sim id (fun _ => True)
      (fun st fe => cached.core_c.defeq_delta_i mode fuel st fe d n a2 b2)
      (fun lfe => DefEq.defeqDeltaFrag (absMode mode) (knot mode lfe fuel.val) lfe d.val
        (k lfe) (absExpr a2) (absExpr b2)) := by
  intro fe lfe hfe hfrel st res st' hwf hok lst hrel
  have hfa : FindAgree fe lfe := FindAgree.of_rel hfrel hfe
  unfold cached.core_c.defeq_delta_i at hok
  simp only [DefEq.defeqDeltaFrag]
  rw [run_pure', run_pure']
  obtain ⟨ua, hua0, hok⟩ := bind_eq_ok_iff.mp hok
  obtain ⟨ub, hub0, hok⟩ := bind_eq_ok_iff.mp hok
  have eua := unfoldableHeadC_eq hfa ha hua0
  have eub := unfoldableHeadC_eq hfa hb hub0
  rw [← eua, ← eub]
  cases ua with
  | true =>
    cases ub with
    | true =>
      exact defeq_delta_both_of_loop hd d n hk ha hb fe lfe hfe hfrel eua.symm eub.symm
        st res st' hwf hok lst hrel
    | false =>
      obtain ⟨⟨r1, st1⟩, h1, hok⟩ := bind_eq_ok_iff.mp hok
      cases r1 with
      | Err err =>
        obtain ⟨rfl, rfl⟩ := err_arm hok
        exact ErrSim.bindCM ((hd.unfoldDefinition ha).apply_err hwf hfe h1 hrel hfrel)
      | Ok o =>
        obtain ⟨lst1, hrun1, hrel1, hwf1, howf⟩ :=
          (hd.unfoldDefinition ha).apply hwf hfe h1 hrel hfrel
        cases o with
        | none =>
          simp only [Option.map_none] at hrun1
          rw [run_bind' hrun1]
          obtain ⟨rfl, rfl⟩ : core.result.Result.Ok false = res ∧ st1 = st' := by
            simpa using Result.ok_injective hok
          exact ⟨lst1, by simp, hrel1, hwf1, trivial⟩
        | some a3 =>
          simp only [Option.map_some] at hrun1
          rw [run_bind' hrun1]
          exact (hk false a3 b2 (howf a3 rfl) hb) fe lfe hfe hfrel st1 res st' hwf1 hok lst1
            hrel1
  | false =>
    cases ub with
    | true =>
      obtain ⟨⟨r1, st1⟩, h1, hok⟩ := bind_eq_ok_iff.mp hok
      cases r1 with
      | Err err =>
        obtain ⟨rfl, rfl⟩ := err_arm hok
        exact ErrSim.bindCM ((hd.unfoldDefinition hb).apply_err hwf hfe h1 hrel hfrel)
      | Ok o =>
        obtain ⟨lst1, hrun1, hrel1, hwf1, howf⟩ :=
          (hd.unfoldDefinition hb).apply hwf hfe h1 hrel hfrel
        cases o with
        | none =>
          simp only [Option.map_none] at hrun1
          rw [run_bind' hrun1]
          obtain ⟨rfl, rfl⟩ : core.result.Result.Ok false = res ∧ st1 = st' := by
            simpa using Result.ok_injective hok
          exact ⟨lst1, by simp, hrel1, hwf1, trivial⟩
        | some b3 =>
          simp only [Option.map_some] at hrun1
          rw [run_bind' hrun1]
          exact (hk false a2 b3 ha (howf b3 rfl)) fe lfe hfe hfrel st1 res st' hwf1 hok lst1
            hrel1
    | false =>
      exact (hd.defeqStruct d ha hb) fe lfe hfe hfrel st res st' hwf hok lst hrel

/-- `ConLeche/Cached/CoreC.lean:1479-1614` — **`defeq_lits_i` refines literal
acceleration** (`core_c.rs:3881`): the fold runs only when *both* sides are
free of free variables, and a fold re-enters the loop at `pi = true`.  The
cited `!a'.hasFvar && !b'.hasFvar` is an `if` nest in the port (task #18's
Lean-side `Decidable` note), which is what `ecl` reconciles. -/
private theorem defeq_lits_of_loop (hd : DefEqDeps mode fuel) (d n : Std.U64)
    {k : ConLeche.FEnv → Bool → ConLeche.Expr → ConLeche.Expr →
      ConLeche.Cached.CheckCM Bool} (hk : LoopRef mode fuel d n k)
    {a2 b2 : expr.Expr} (ha : ExprWF a2) (hb : ExprWF b2) :
    Sim id (fun _ => True)
      (fun st fe => cached.core_c.defeq_lits_i mode fuel st fe d n a2 b2)
      (fun lfe => DefEq.defeqLitsFrag (absMode mode) (knot mode lfe fuel.val) lfe d.val
        (k lfe) (absExpr a2) (absExpr b2)) := by
  intro fe lfe hfe hfrel st res st' hwf hok lst hrel
  unfold cached.core_c.defeq_lits_i at hok
  simp only [DefEq.defeqLitsFrag, hasFvarC_eq]
  rw [run_pure']
  obtain ⟨fa0, hfa0, hok⟩ := bind_eq_ok_iff.mp hok
  have ea := ExprOps.has_fvar_refines ha hfa0
  obtain ⟨closed, hclosed, hok⟩ := bind_eq_ok_iff.mp hok
  have ecl : closed = (!(absExpr a2).hasFvar && !(absExpr b2).hasFvar) := by
    rw [← ea]
    cases fa0 with
    | true =>
      simp only [Bool.not_true, Bool.false_and]
      simp only [if_true] at hclosed
      exact (Result.ok_injective hclosed).symm
    | false =>
      simp only [Bool.false_eq_true, if_false] at hclosed
      obtain ⟨fb0, hfb0, hclosed⟩ := bind_eq_ok_iff.mp hclosed
      have eb := ExprOps.has_fvar_refines hb hfb0
      rw [← eb]
      cases fb0 with
      | true =>
        simp only [Bool.not_false, Bool.not_true, Bool.true_and]
        simp only [if_true] at hclosed
        exact (Result.ok_injective hclosed).symm
      | false =>
        simp only [Bool.not_false, Bool.true_and]
        simp only [Bool.false_eq_true, if_false] at hclosed
        exact (Result.ok_injective hclosed).symm
  rw [← ecl]
  cases closed with
  | false =>
    simp only [Bool.false_eq_true, if_false]
    simp only [Bool.false_eq_true, if_false, bind_tc_ok] at hok
    exact defeq_delta_of_loop hd d n hk ha hb fe lfe hfe hfrel st res st' hwf hok lst hrel
  | true =>
    simp only [if_true]
    obtain ⟨⟨st1, ra⟩, hra, hok⟩ := bind_eq_ok_iff.mp hok
    obtain ⟨⟨ra1, st2⟩, hrn, hra⟩ := bind_eq_ok_iff.mp hra
    have hpair := Result.ok_injective hra
    rw [show st1 = st2 from (congrArg Prod.fst hpair).symm,
      show ra = ra1 from (congrArg Prod.snd hpair).symm] at hok
    cases ra1 with
    | Err err =>
      obtain ⟨rfl, rfl⟩ := err_arm hok
      exact ErrSim.bindCM ((hd.reduceNat d ha).apply_err hwf hfe hrn hrel hfrel)
    | Ok o =>
      obtain ⟨lst1, hrun1, hrel1, hwf1, howf⟩ :=
        (hd.reduceNat d ha).apply hwf hfe hrn hrel hfrel
      cases o with
      | some a3 =>
        simp only [Option.map_some] at hrun1
        rw [run_bind' hrun1]
        exact (hk true a3 b2 (howf a3 rfl) hb) fe lfe hfe hfrel st2 res st' hwf1 hok lst1
          hrel1
      | none =>
        simp only [Option.map_none] at hrun1
        rw [run_bind' hrun1]
        obtain ⟨⟨st3, rb⟩, hrb, hok⟩ := bind_eq_ok_iff.mp hok
        obtain ⟨⟨rb1, st4⟩, hrn2, hrb⟩ := bind_eq_ok_iff.mp hrb
        have hpair2 := Result.ok_injective hrb
        rw [show st3 = st4 from (congrArg Prod.fst hpair2).symm,
          show rb = rb1 from (congrArg Prod.snd hpair2).symm] at hok
        cases rb1 with
        | Err err =>
          obtain ⟨rfl, rfl⟩ := err_arm hok
          exact ErrSim.bindCM ((hd.reduceNat d hb).apply_err hwf1 hfe hrn2 hrel1 hfrel)
        | Ok o2 =>
          obtain ⟨lst2, hrun2, hrel2, hwf2, howf2⟩ :=
            (hd.reduceNat d hb).apply hwf1 hfe hrn2 hrel1 hfrel
          cases o2 with
          | some b3 =>
            simp only [Option.map_some] at hrun2
            rw [run_bind' hrun2]
            exact (hk true a2 b3 ha (howf2 b3 rfl)) fe lfe hfe hfrel st4 res st' hwf2 hok lst2
              hrel2
          | none =>
            simp only [Option.map_none] at hrun2
            rw [run_bind' hrun2]
            exact defeq_delta_of_loop hd d n hk ha hb fe lfe hfe hfrel st4 res st' hwf2 hok
              lst2 hrel2

/-- `ConLeche/Cached/CoreC.lean:1472-1614` — **`defeq_after_whnf_i` refines
the hoisted proof-irrelevance probe and its tail** (`core_c.rs:3849`): run
once per entry (the `pi` flag, the audit's D3) and never on a pair
`quickPair` decides (D4). -/
private theorem defeq_after_whnf_of_loop (hw : Wrappers mode fuel)
    (hd : DefEqDeps mode fuel) (d n : Std.U64) (pi : Bool)
    {k : ConLeche.FEnv → Bool → ConLeche.Expr → ConLeche.Expr →
      ConLeche.Cached.CheckCM Bool} (hk : LoopRef mode fuel d n k)
    {a2 b2 : expr.Expr} (ha : ExprWF a2) (hb : ExprWF b2) :
    Sim id (fun _ => True)
      (fun st fe => cached.core_c.defeq_after_whnf_i mode fuel st fe d n pi a2 b2)
      (fun lfe => DefEq.defeqAfterWhnfFrag (absMode mode) (knot mode lfe fuel.val) lfe
        d.val (k lfe) pi (absExpr a2) (absExpr b2)) := by
  intro fe lfe hfe hfrel st res st' hwf hok lst hrel
  unfold cached.core_c.defeq_after_whnf_i at hok
  simp only [DefEq.defeqAfterWhnfFrag]
  rw [run_pure']
  cases pi with
  | false =>
    simp only [Bool.false_and, Bool.false_eq_true, if_false]
    rw [run_pure']
    simp only [Bool.false_eq_true, if_false]
    simp only [Bool.false_eq_true, if_false, bind_tc_ok] at hok
    exact defeq_lits_of_loop hd d n hk ha hb fe lfe hfe hfrel st res st' hwf hok lst hrel
  | true =>
    obtain ⟨⟨st1, pir⟩, hpir, hok⟩ := bind_eq_ok_iff.mp hok
    obtain ⟨qp0, hqp, hpir⟩ := bind_eq_ok_iff.mp hpir
    have eqp := CoreK.quick_pair_refines hqp
    rw [← eqp]
    cases qp0 with
    | true =>
      simp only [Bool.not_true, Bool.and_false, Bool.false_eq_true, if_false]
      rw [run_pure']
      simp only [Bool.false_eq_true, if_false]
      have hp := Result.ok_injective hpir
      rw [show st1 = st from (congrArg Prod.fst hp).symm,
        show pir = core.result.Result.Ok false from (congrArg Prod.snd hp).symm] at hok
      have hok' : cached.core_c.defeq_lits_i mode fuel st fe d n a2 b2
          = ok (res, st') := hok
      exact defeq_lits_of_loop hd d n hk ha hb fe lfe hfe hfrel st res st' hwf hok' lst hrel
    | false =>
      simp only [Bool.not_false, Bool.and_true, if_true]
      obtain ⟨⟨pir1, st2⟩, hpi, hpir⟩ := bind_eq_ok_iff.mp hpir
      have hp := Result.ok_injective hpir
      rw [show st1 = st2 from (congrArg Prod.fst hp).symm,
        show pir = pir1 from (congrArg Prod.snd hp).symm] at hok
      cases pir1 with
      | Err err =>
        obtain ⟨rfl, rfl⟩ := err_arm hok
        exact ErrSim.bindCM
          ((prop_irrel_i_refines hw hd.toDefEqDepsA d ha hb).apply_err hwf hfe hpi hrel hfrel)
      | Ok v =>
        obtain ⟨lst1, hrun1, hrel1, hwf1, -⟩ :=
          (prop_irrel_i_refines hw hd.toDefEqDepsA d ha hb).apply hwf hfe hpi hrel
            hfrel
        simp only [id] at hrun1
        rw [run_bind' hrun1]
        cases v with
        | true =>
          obtain ⟨rfl, rfl⟩ : core.result.Result.Ok true = res ∧ st2 = st' := by
            simpa using Result.ok_injective hok
          exact ⟨lst1, by simp, hrel1, hwf1, trivial⟩
        | false =>
          simp only [Bool.false_eq_true, if_false]
          exact defeq_lits_of_loop hd d n hk ha hb fe lfe hfe hfrel st2 res st' hwf1 hok lst1
            hrel1

/-- `ConLeche/Cached/CoreC.lean:1456` — **`defeq_step_i` refines `defeqStepI`
at a given continuation** (`core_c.rs:3806`): the syntactic fast path, the
eq-true shortcut, head normalisation of both sides with `whnfCore` — no
delta — and then the rest of the cited body.  `defeqStepI`'s `k` is the loop
at the decremented budget, which the Rust passes as the budget itself, so the
correspondence is parametric in `k` and its refinement `hk`. -/
private theorem defeq_step_of_loop (hw : Wrappers mode fuel) (hd : DefEqDeps mode fuel)
    (d n : Std.U64) (pi : Bool)
    {k : ConLeche.FEnv → Bool → ConLeche.Expr → ConLeche.Expr →
      ConLeche.Cached.CheckCM Bool} (hk : LoopRef mode fuel d n k)
    {a b : expr.Expr} (ha : ExprWF a) (hb : ExprWF b) :
    Sim id (fun _ => True)
      (fun st fe => cached.core_c.defeq_step_i mode fuel st fe d n pi a b)
      (fun lfe => ConLeche.Cached.defeqStepI (absMode mode) (knot mode lfe fuel.val) lfe
        d.val (k lfe) pi (absExpr a) (absExpr b)) := by
  intro fe lfe hfe hfrel st res st' hwf hok lst hrel
  unfold cached.core_c.defeq_step_i at hok
  simp only [DefEq.defeqStepI_eq]
  obtain ⟨e0, he0, hok⟩ := bind_eq_ok_iff.mp hok
  have ee0 : (absExpr a == absExpr b) = e0 := by
    rw [Expr.beq_refines ha hb he0]; rfl
  rw [ee0]
  cases e0 with
  | true =>
    obtain ⟨rfl, rfl⟩ : core.result.Result.Ok true = res ∧ st = st' := by
      simpa using Result.ok_injective hok
    exact ⟨lst, by simp, hrel, hwf, trivial⟩
  | false =>
    simp only [Bool.false_eq_true, if_false]
    rw [run_pure', run_pure']
    simp only [hasFvarC_eq]
    obtain ⟨⟨st1, sc⟩, hsc, hok⟩ := bind_eq_ok_iff.mp hok
    -- the eq-true shortcut, as one step: it either answers, or it threw and
    -- con-leche's `if ← …` throws with it (task #67's second disjunct)
    have key : (∃ err : core_types.CheckError, sc = core.result.Result.Err err ∧
        ErrSim err
          (((if pi && (absExpr b).isBoolTrue && !(absExpr a).hasFvar then
              ConLeche.Cached.boolTrueShortcutI (knot mode lfe fuel.val) d.val (absExpr a)
            else pure false) : ConLeche.Cached.CheckCM Bool).run lst))
      ∨ (∃ (lst1 : ConLeche.Cached.CState) (scv : Bool),
        sc = core.result.Result.Ok scv ∧
        ((if pi && (absExpr b).isBoolTrue && !(absExpr a).hasFvar then
            ConLeche.Cached.boolTrueShortcutI (knot mode lfe fuel.val) d.val (absExpr a)
          else pure false) : ConLeche.Cached.CheckCM Bool).run lst = .ok (scv, lst1)
        ∧ StateRel st1 lst1 ∧ StateWF st1) := by
      cases pi with
      | false =>
        have hp := Result.ok_injective hsc
        have hs : st1 = st := (congrArg Prod.fst hp).symm
        exact Or.inr ⟨lst, false, (congrArg Prod.snd hp).symm, by simp,
          by rw [hs]; exact hrel, by rw [hs]; exact hwf⟩
      | true =>
        obtain ⟨bt0, hbt, hsc⟩ := bind_eq_ok_iff.mp hsc
        have ebt := CoreK.is_bool_true_refines hb CoreK.pinned_bool_true_name hbt
        cases bt0 with
        | false =>
          have hp := Result.ok_injective hsc
          have hs : st1 = st := (congrArg Prod.fst hp).symm
          exact Or.inr ⟨lst, false, (congrArg Prod.snd hp).symm, by simp [← ebt],
            by rw [hs]; exact hrel, by rw [hs]; exact hwf⟩
        | true =>
          obtain ⟨af0, haf, hsc⟩ := bind_eq_ok_iff.mp hsc
          have eaf := ExprOps.has_fvar_refines ha haf
          cases af0 with
          | true =>
            have hp := Result.ok_injective hsc
            have hs : st1 = st := (congrArg Prod.fst hp).symm
            exact Or.inr ⟨lst, false, (congrArg Prod.snd hp).symm, by simp [← ebt, ← eaf],
              by rw [hs]; exact hrel, by rw [hs]; exact hwf⟩
          | false =>
            obtain ⟨⟨sc1, st2⟩, hbs, hsc⟩ := bind_eq_ok_iff.mp hsc
            have hp := Result.ok_injective hsc
            have hs : st1 = st2 := (congrArg Prod.fst hp).symm
            have hr : sc = sc1 := (congrArg Prod.snd hp).symm
            cases sc1 with
            | Err err =>
              refine Or.inl ⟨err, hr, ?_⟩
              simp only [← ebt, ← eaf, Bool.not_false, Bool.and_true, if_true]
              exact (bool_true_shortcut_i_refines hw d ha).apply_err hwf hfe hbs hrel hfrel
            | Ok v =>
              obtain ⟨lst1, hrun1, hrel1, hwf1, -⟩ :=
                (bool_true_shortcut_i_refines hw d ha).apply hwf hfe hbs hrel hfrel
              simp only [id] at hrun1
              refine Or.inr ⟨lst1, v, hr, ?_, by rw [hs]; exact hrel1, by rw [hs]; exact hwf1⟩
              simp only [← ebt, ← eaf, Bool.not_false, Bool.and_true, if_true]
              exact hrun1
    rcases key with ⟨err, hscv, herr⟩ | ⟨lst1, scv, hscv, hg, hrel1, hwf1⟩
    · -- the shortcut threw: so does con-leche, at the same `if ← …`
      rw [hscv] at hok
      obtain ⟨rfl, rfl⟩ := err_arm hok
      exact ErrSim.bindCM herr
    rw [hscv] at hok
    rw [run_bind' hg]
    cases scv with
    | true =>
      obtain ⟨rfl, rfl⟩ : core.result.Result.Ok true = res ∧ st1 = st' := by
        simpa using Result.ok_injective hok
      exact ⟨lst1, by simp, hrel1, hwf1, trivial⟩
    | false =>
      simp only [Bool.false_eq_true, if_false]
      obtain ⟨⟨r1, st2⟩, h1, hok⟩ := bind_eq_ok_iff.mp hok
      cases r1 with
      | Err err =>
        obtain ⟨rfl, rfl⟩ := err_arm hok
        exact ErrSim.bindCM ((hw.whnfCoreSim d ha).apply_err hwf1 hfe h1 hrel1 hfrel)
      | Ok a2 =>
        obtain ⟨lst2, hrun2, hrel2, hwf2, ha2wf⟩ :=
          (hw.whnfCoreSim d ha).apply hwf1 hfe h1 hrel1 hfrel
        rw [run_bind' hrun2]
        obtain ⟨⟨r2, st3⟩, h2, hok⟩ := bind_eq_ok_iff.mp hok
        cases r2 with
        | Err err =>
          obtain ⟨rfl, rfl⟩ := err_arm hok
          exact ErrSim.bindCM ((hw.whnfCoreSim d hb).apply_err hwf2 hfe h2 hrel2 hfrel)
        | Ok b2 =>
          obtain ⟨lst3, hrun3, hrel3, hwf3, hb2wf⟩ :=
            (hw.whnfCoreSim d hb).apply hwf2 hfe h2 hrel2 hfrel
          rw [run_bind' hrun3]
          obtain ⟨e3, he3, hok⟩ := bind_eq_ok_iff.mp hok
          have ee3 : (absExpr a2 == absExpr b2) = e3 := by
            rw [Expr.beq_refines ha2wf hb2wf he3]; rfl
          rw [ee3]
          cases e3 with
          | true =>
            obtain ⟨rfl, rfl⟩ : core.result.Result.Ok true = res ∧ st3 = st' := by
              simpa using Result.ok_injective hok
            exact ⟨lst3, by simp, hrel3, hwf3, trivial⟩
          | false =>
            simp only [Bool.false_eq_true, if_false]
            exact defeq_after_whnf_of_loop hw hd d n pi hk ha2wf hb2wf fe lfe hfe hfrel
              st3 res st' hwf3 hok lst3 hrel3

/-- The induction that makes the budget a `Nat`: `defeq_loop_i` at a `U64`
whose `val` is `m` refines `defeqLoopI … m`.  This is the whole cycle — the
seven split helpers all call `defeq_loop_i` where con-leche calls `k`, and
each of them was proved above parametric in `k`, so the induction has only to
supply `k := defeqLoopI … m` at the decremented budget. -/
private theorem defeq_loop_aux (hw : Wrappers mode fuel) (hd : DefEqDeps mode fuel)
    (d : Std.U64) :
    ∀ (m : Nat) (n : Std.U64), n.val = m → ∀ (pi : Bool) (a b : expr.Expr),
      ExprWF a → ExprWF b →
      Sim id (fun _ => True)
        (fun st fe => cached.core_c.defeq_loop_i mode fuel st fe d n pi a b)
        (fun lfe => ConLeche.Cached.defeqLoopI (absMode mode) (knot mode lfe fuel.val) lfe
          d.val m pi (absExpr a) (absExpr b)) := by
  intro m
  induction m with
  | zero =>
    -- **the budget is spent on both sides at once** (task #67): the Rust
    -- builds `internal(<M>)` and `defeqLoopI … 0` throws `.internal`, at the
    -- same step and the same kind
    intro n hn pi a b ha hb fe lfe hfe hfrel st res st' hwf hok lst hrel
    have hz : n = 0#u64 := Std.UScalar.eq_of_val_eq (by simp [hn])
    unfold cached.core_c.defeq_loop_i at hok
    simp only [hz] at hok
    obtain ⟨_, -, hok⟩ := bind_eq_ok_iff.mp hok
    obtain ⟨v, -, hok⟩ := bind_eq_ok_iff.mp hok
    obtain ⟨ce, hce, hok⟩ := bind_eq_ok_iff.mp hok
    obtain ⟨rfl, rfl⟩ := err_arm hok
    have hce' : ce = .Internal v := internal_inv hce
    subst hce'
    exact ErrSim.internal
      (DefEq.defeqLoopI_zero_run (absMode mode) (knot mode lfe fuel.val) lfe d.val pi
        (absExpr a) (absExpr b) lst)
  | succ m ih =>
    intro n hn pi a b ha hb fe lfe hfe hfrel st res st' hwf hok lst hrel
    have hz : ¬ (n = 0#u64) := by
      intro hc
      rw [hc] at hn
      simp at hn
    dsimp only at hok
    unfold cached.core_c.defeq_loop_i at hok
    rw [if_neg hz] at hok
    obtain ⟨i, hi, hok⟩ := bind_eq_ok_iff.mp hok
    have hiv : i.val = m := by
      have h1 := ConRon.Refine.Nat.usub_val hi
      have h2 : ((1#u64 : Std.U64)).val = 1 := rfl
      omega
    have hstep := defeq_step_of_loop hw hd d i pi
      (k := fun lfe => ConLeche.Cached.defeqLoopI (absMode mode) (knot mode lfe fuel.val) lfe
        d.val m)
      (fun pi' x y hx hy => ih i hiv pi' x y hx hy) ha hb
    simp only [DefEq.defeqLoopI_succ]
    exact hstep fe lfe hfe hfrel st res st' hwf hok lst hrel

/-- `ConLeche/Cached/CoreC.lean:1617` — **`defeq_loop_i` refines
`defeqLoopI`** (`core_c.rs:4256`): the `U64` budget is con-leche's `Nat`
one, **exhaustion included** — at `0` the Rust throws `internal(<M>)` and
`defeqLoopI … 0` throws `.internal`, at the same step (task #67), which is
what `Core/Knot.lean`'s `wrappers_zero` proves for the six wrappers. -/
theorem defeq_loop_i_refines (hw : Wrappers mode fuel) (hd : DefEqDeps mode fuel)
    (d n : Std.U64) (pi : Bool) {a b : expr.Expr} (ha : ExprWF a) (hb : ExprWF b) :
    Sim id (fun _ => True)
      (fun st fe => cached.core_c.defeq_loop_i mode fuel st fe d n pi a b)
      (fun lfe => ConLeche.Cached.defeqLoopI (absMode mode) (knot mode lfe fuel.val) lfe
        d.val n.val pi (absExpr a) (absExpr b)) :=
  defeq_loop_aux hw hd d n.val n rfl pi a b ha hb

/-- The continuation the six split helpers run against, once the loop is
known: `defeq_loop_i` at the budget they thread. -/
private theorem loopRef_defeqLoopI (hw : Wrappers mode fuel) (hd : DefEqDeps mode fuel)
    (d n : Std.U64) :
    LoopRef mode fuel d n
      (fun lfe => ConLeche.Cached.defeqLoopI (absMode mode) (knot mode lfe fuel.val) lfe
        d.val n.val) :=
  fun pi _x _y hx hy => defeq_loop_i_refines hw hd d n pi hx hy

/-- `ConLeche/Cached/CoreC.lean:1512-1514` — **`defeq_unfold_both_i` refines
the shared tail of the equal-hint arms** (`core_c.rs:4004`), the continuation
being the loop at the budget it carries.  See `defeq_unfold_both_of_loop` for
why the two lazy-delta guards are hypotheses. -/
theorem defeq_unfold_both_i_refines (hw : Wrappers mode fuel) (hd : DefEqDeps mode fuel)
    (d n : Std.U64) {a2 b2 : expr.Expr} (ha : ExprWF a2) (hb : ExprWF b2)
    (fe : fenv.FEnv) (lfe : ConLeche.FEnv) (hfe : FEnvWF fe) (hfrel : FEnvRel fe lfe)
    (hua : ConLeche.Cached.unfoldableHeadC lfe (absExpr a2) = true)
    (hub : ConLeche.Cached.unfoldableHeadC lfe (absExpr b2) = true) :
    SimS id (fun _ => True)
      (fun st => cached.core_c.defeq_unfold_both_i mode fuel st fe d n a2 b2)
      (DefEq.defeqUnfoldBothFrag lfe
        (ConLeche.Cached.defeqLoopI (absMode mode) (knot mode lfe fuel.val) lfe d.val n.val)
        (absExpr a2) (absExpr b2)) :=
  defeq_unfold_both_of_loop hd d n (loopRef_defeqLoopI hw hd d n) ha hb fe lfe hfe hfrel hua hub

/-- `ConLeche/Cached/CoreC.lean:1497-1517` — **`defeq_delta_both_i` refines
the `| true, true` arm** (`core_c.rs:3963`), the continuation being the loop
at the budget it carries. -/
theorem defeq_delta_both_i_refines (hw : Wrappers mode fuel) (hd : DefEqDeps mode fuel)
    (d n : Std.U64) {a2 b2 : expr.Expr} (ha : ExprWF a2) (hb : ExprWF b2)
    (fe : fenv.FEnv) (lfe : ConLeche.FEnv) (hfe : FEnvWF fe) (hfrel : FEnvRel fe lfe)
    (hua : ConLeche.Cached.unfoldableHeadC lfe (absExpr a2) = true)
    (hub : ConLeche.Cached.unfoldableHeadC lfe (absExpr b2) = true) :
    SimS id (fun _ => True)
      (fun st => cached.core_c.defeq_delta_both_i mode fuel st fe d n a2 b2)
      (DefEq.defeqDeltaBothFrag (knot mode lfe fuel.val) lfe d.val
        (ConLeche.Cached.defeqLoopI (absMode mode) (knot mode lfe fuel.val) lfe d.val n.val)
        (absExpr a2) (absExpr b2)) :=
  defeq_delta_both_of_loop hd d n (loopRef_defeqLoopI hw hd d n) ha hb fe lfe hfe hfrel hua hub

/-- `ConLeche/Cached/CoreC.lean:1488-1614` — **`defeq_delta_i` refines lazy
delta** (`core_c.rs:3927`), the continuation being the loop at the budget it
carries. -/
theorem defeq_delta_i_refines (hw : Wrappers mode fuel) (hd : DefEqDeps mode fuel)
    (d n : Std.U64) {a2 b2 : expr.Expr} (ha : ExprWF a2) (hb : ExprWF b2) :
    Sim id (fun _ => True)
      (fun st fe => cached.core_c.defeq_delta_i mode fuel st fe d n a2 b2)
      (fun lfe => DefEq.defeqDeltaFrag (absMode mode) (knot mode lfe fuel.val) lfe d.val
        (ConLeche.Cached.defeqLoopI (absMode mode) (knot mode lfe fuel.val) lfe d.val n.val)
        (absExpr a2) (absExpr b2)) :=
  defeq_delta_of_loop hd d n (loopRef_defeqLoopI hw hd d n) ha hb

/-- `ConLeche/Cached/CoreC.lean:1479-1614` — **`defeq_lits_i` refines literal
acceleration** (`core_c.rs:3881`), the continuation being the loop at the
budget it carries. -/
theorem defeq_lits_i_refines (hw : Wrappers mode fuel) (hd : DefEqDeps mode fuel)
    (d n : Std.U64) {a2 b2 : expr.Expr} (ha : ExprWF a2) (hb : ExprWF b2) :
    Sim id (fun _ => True)
      (fun st fe => cached.core_c.defeq_lits_i mode fuel st fe d n a2 b2)
      (fun lfe => DefEq.defeqLitsFrag (absMode mode) (knot mode lfe fuel.val) lfe d.val
        (ConLeche.Cached.defeqLoopI (absMode mode) (knot mode lfe fuel.val) lfe d.val n.val)
        (absExpr a2) (absExpr b2)) :=
  defeq_lits_of_loop hd d n (loopRef_defeqLoopI hw hd d n) ha hb

/-- `ConLeche/Cached/CoreC.lean:1472-1614` — **`defeq_after_whnf_i` refines
the hoisted proof-irrelevance probe and its tail** (`core_c.rs:3849`), the
continuation being the loop at the budget it carries. -/
theorem defeq_after_whnf_i_refines (hw : Wrappers mode fuel) (hd : DefEqDeps mode fuel)
    (d n : Std.U64) (pi : Bool) {a2 b2 : expr.Expr} (ha : ExprWF a2) (hb : ExprWF b2) :
    Sim id (fun _ => True)
      (fun st fe => cached.core_c.defeq_after_whnf_i mode fuel st fe d n pi a2 b2)
      (fun lfe => DefEq.defeqAfterWhnfFrag (absMode mode) (knot mode lfe fuel.val) lfe d.val
        (ConLeche.Cached.defeqLoopI (absMode mode) (knot mode lfe fuel.val) lfe d.val n.val)
        pi (absExpr a2) (absExpr b2)) :=
  defeq_after_whnf_of_loop hw hd d n pi (loopRef_defeqLoopI hw hd d n) ha hb

/-- `ConLeche/Cached/CoreC.lean:1456` — **`defeq_step_i` refines
`defeqStepI`** (`core_c.rs:3806`), the continuation being the loop at the
budget it carries, which is what `defeqLoopI` passes. -/
theorem defeq_step_i_refines (hw : Wrappers mode fuel) (hd : DefEqDeps mode fuel)
    (d n : Std.U64) (pi : Bool) {a b : expr.Expr} (ha : ExprWF a) (hb : ExprWF b) :
    Sim id (fun _ => True)
      (fun st fe => cached.core_c.defeq_step_i mode fuel st fe d n pi a b)
      (fun lfe => ConLeche.Cached.defeqStepI (absMode mode) (knot mode lfe fuel.val) lfe d.val
        (ConLeche.Cached.defeqLoopI (absMode mode) (knot mode lfe fuel.val) lfe d.val n.val)
        pi (absExpr a) (absExpr b)) :=
  defeq_step_of_loop hw hd d n pi (loopRef_defeqLoopI hw hd d n) ha hb

/-- `ConLeche/Cached/CoreC.lean:1624` — **`defeq_body_i` refines
`defeqBodyI`** (`core_c.rs:4282`): the lazy-delta loop at its own closed
budget, entered at `pi = true`.  Task #49's `CoreK.defeq_loop_fuel_refines`
says the port's budget constant is con-leche's `defeqLoopFuel`. -/
theorem defeq_body_i_refines (hw : Wrappers mode fuel) (hd : DefEqDeps mode fuel)
    (d : Std.U64) {a b : expr.Expr} (ha : ExprWF a) (hb : ExprWF b) :
    Sim id (fun _ => True)
      (fun st fe => cached.core_c.defeq_body_i mode fuel st fe d a b)
      (fun lfe => ConLeche.Cached.defeqBodyI (absMode mode) (knot mode lfe fuel.val) lfe
        d.val (absExpr a) (absExpr b)) := by
  intro fe lfe hfe hfrel st res st' hwf hok lst hrel
  unfold cached.core_c.defeq_body_i at hok
  obtain ⟨i, hi, hok⟩ := bind_eq_ok_iff.mp hok
  have hiv : i.val = ConLeche.defeqLoopFuel := CoreK.defeq_loop_fuel_refines hi
  have hres := defeq_loop_i_refines hw hd d i true ha hb fe lfe hfe hfrel st res st' hwf hok
    lst hrel
  rw [hiv] at hres
  simpa [ConLeche.Cached.defeqBodyI] using hres


end


end ConRon.Refine.Core
