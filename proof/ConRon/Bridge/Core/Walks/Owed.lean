/-
# `ConRon.Bridge.Core.Walks.Owed` — the sixteen statements the round did not reach

Task #97-P3-CoreWalks.  DESIGN §8's `### Task #97-P3-Core` §6 ends with the
round's own estimate of where the next tier's work is:

> what the tier is waiting on … is a `BodySpec`-shaped theorem for the ~15
> `Arena/Core.lean` walks that are not knot slots (`iotaRec`, `projCertAt`,
> `projLitToCtor`, `propIrrel`, `stuckIrrel`, `etaCert`, `defeqSpine`,
> `defEqList`, `reduceNat`, `unfoldDefinition`, `annotPwPi`, `annotPwLam`,
> `IProjEntry.typeAt`, `lvlEq?`, the readbacks).  **It is bigger than the six
> bodies.**

This module is that list, **stated**.  `lvlEq?`/`lvlsEq?` and the readbacks
are `Bridge/Core/Walks/{Cached,Frame}.lean` and are CLOSED; `ensureSort` is
`Bridge/Core/EnsureSort.lean` and is CLOSED; `IProjEntry.typeAt` is the one
name of the list that is NOT here, and §3 says why; `isBoolTrue` is
`Bridge/Core/Walks/Guards.lean` and is CLOSED.  The sixteen below are what is
left of it, each with the con-leche function it refines named through
`Verify/Knot.lean`'s own `…Fueled` abbreviation, and each `sorry` with what
it is waiting on written at the site.

This is `Bridge/ExprOps/Owed.lean`'s role one tier up: a statement is not a
proof, but it is the interface, and the six body walks cannot be written
against a walk that has no statement.

## 1. The three answer shapes, and which walk has which

`Bridge/Core/Walks/Spec.lean`'s relations, at the pure call with its fuel
abstracted:

| shape | walks |
|---|---|
| `SimOOp` — an `Option EIdx` answer | `reduceNat`, `iotaRec` |
| `SimEOp` — an `EIdx` answer | `projLitToCtor` |
| `SimBOp` — a `Bool` answer | `projCertAt`, `propIrrel`, `stuckIrrel`, `etaCert`, `defeqSpine`, `defEqList`, `isPropType` |
| `SimVOp` — any shared type | `annotPwPi`, `annotPwLam` (`PropWhen`), `headHint` (`ReducibilityHint`) |
| an EQUATION — the pure side takes no fuel | `unfoldDefinition`, `unfoldableHead`, `sameConstHeads` (and `isBoolTrue`, CLOSED in `Walks/Guards.lean`) |

**The last row is the cheap one and it is worth naming.**  Four walks of the
group (three here, `isBoolTrue` in `Walks/Guards.lean`) refine a con-leche
function that is not in `CheckM` at all
(`unfoldDefinition env e : Option Expr`, `unfoldableHead env e : Bool`,
`sameConstHeads a b : Bool`, `Expr.isBoolTrue e : Bool`), so there is no
`∃ F` and no fuel bookkeeping: the conclusion is an equation between the
arena's answer and con-leche's.  They are the first four of these to write.

## 2. What they are all waiting on, in one sentence each

Ten of the sixteen wait on an `ExprOps`-tier callee rule that this tier
does not import (`getAppFn`, `getAppArgs`, `mkAppN`, `instLPFast`,
`liftLooseBVars`, `typeSortPW`), one waits on §3's missing denotation, one on
`Bridge/Core/Walks/Cached.lean`'s `constValAt_spec` (itself waiting on
`instLPFast_spec`), one on the fuel merge (`defEqList_spec`'s note), and the
rest on nothing but the work.  The per-site notes say which.

## 3. `IProjEntry.typeAt`, and the one thing the tier is missing that is not
a proof

`IProjEntry.typeAt` cannot be STATED here, because **the projection table has
no denotation**: `Arena/Frontend/Readback.lean` has `denoteCI` for a
`IConstantInfo` and `denoteCV` for a `IConstantVal`, and nothing for an
`IProjEntry` (`Arena/Env.lean:150`, ten fields, four of them handles).  Its
`denoteProjEntry` is the one piece of *new* denotation machinery the Core
walks tier needs, and it belongs beside the other ten transports in
`Bridge/Rel.lean` — which this round does not edit.  Every `.proj` arm of
`whnfCoreBody` and `inferBody` waits on it, and so do `projCert`,
`projCertAt`'s guard and `IProjEntry.fireOk`.  **That is the tier's one
structural gap; everything else on this list is labour.**
-/
import ConRon.Bridge.Core.Walks.Spec

namespace ConRon.Bridge.Core

set_option autoImplicit false
set_option mvcgen.warning false
set_option maxHeartbeats 1000000

open ConLeche ConRon.Arena ConRon.Bridge Std.Do

variable {mode : CheckMode} {env : Env} {fe : IFEnv}

/-! ## 1. The three with an unfueled pure side

con-leche's comparand is a plain function of the environment, so the
conclusion is an equation and there is no fuel existential anywhere in the
statement.  These are the cheapest walks of the tier — their fourth,
`isBoolTrue`, is CLOSED in `Bridge/Core/Walks/Guards.lean`, and the three
here differ from it only by needing `getAppFn`. -/

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:157-170 unfoldableHead —
**THEOREM 1 for `unfoldableHead`**: the delta step's DECISION, taken before
the unfolding is materialized.

**OPEN**: needs `Bridge/ExprOps/Spine.lean`'s `getAppFn_spec` (which is
closed) and `Bridge/StateOK.lean`'s `IFEnvOK.hit`/`.miss` at the head's name
— no import of the `ExprOps` tier is made by `Bridge/Core/Walks/**` this
round, which is the only reason this is not proved here. -/
theorem unfoldableHead_spec (s₀ : AState) (e : EIdx) (x : Expr)
    (hok : CheckOK mode env fe s₀) (hden : denoteE s₀.store e = some x) :
    ⦃fun s => ⌜s = s₀⌝⦄ ConRon.Arena.unfoldableHead fe e
    ⦃⇓? b s' => ⌜CheckOK mode env fe s' ∧ s'.store = s₀.store ∧
        s'.pins = s₀.pins ∧ b = ConLeche.unfoldableHead env x⌝⦄ := by
  sorry

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:172-181 headHint — **THEOREM 1
for `headHint`**: the reducibility hint of the constant at the head.

**OPEN**: `getAppFn_spec` and `IFEnvOK`, as above.  The answer type is one
both tiers share, so the relation is `SimVOp`'s — here spelled as the
equation it is, because con-leche's `headHint` takes no fuel. -/
theorem headHint_spec (s₀ : AState) (e : EIdx) (x : Expr)
    (hok : CheckOK mode env fe s₀) (hden : denoteE s₀.store e = some x) :
    ⦃fun s => ⌜s = s₀⌝⦄ ConRon.Arena.headHint fe e
    ⦃⇓? h s' => ⌜CheckOK mode env fe s' ∧ s'.store = s₀.store ∧
        s'.pins = s₀.pins ∧ h = ConLeche.headHint env x⌝⦄ := by
  sorry

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:183-192 sameConstHeads —
**THEOREM 1 for `sameConstHeads`**: the lazy-delta same-head short-circuit.

**OPEN**: `getAppFn_spec`, and `denoteN_inj` for the name comparison —
DESIGN §8.3's "index inequality IS structural inequality" at the name store,
which is where the arena's `==` on `NIdx` becomes con-leche's `==` on
`Name`. -/
theorem sameConstHeads_spec (s₀ : AState) (a b : EIdx) (x y : Expr)
    (hok : CheckOK mode env fe s₀) (hda : denoteE s₀.store a = some x)
    (hdb : denoteE s₀.store b = some y) :
    ⦃fun s => ⌜s = s₀⌝⦄ ConRon.Arena.sameConstHeads a b
    ⦃⇓? r s' => ⌜CheckOK mode env fe s' ∧ s'.store = s₀.store ∧
        s'.pins = s₀.pins ∧ r = ConLeche.sameConstHeads x y⌝⦄ := by
  sorry

/-! `isBoolTrue` was the fourth of this group and is **CLOSED** —
`Bridge/Core/Walks/Guards.lean`.  It was the cheapest of the seventeen (five
verification conditions, no `ExprOps` rule, no new denotation), and closing
it is this round's evidence that the row above really is the cheap one. -/

/-! ## 2. The delta step and the literal acceleration

`whnfStep`'s two callees (`Bridge/Core/Arms/Whnf.lean`'s `whnfLoop_delta`
and `whnfLoop_reduceNat` are their pure-side step lemmas, and both are
closed), which is why `whnfBody_spec` — the most reachable of the six body
walks — is still open. -/

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:136-155 unfoldDefinition —
**THEOREM 1 for `unfoldDefinition`**: unfold the (application of a)
definition at the head, one step.  The pure side takes no fuel, so the
conclusion is an equation through `denoteEO` (`Bridge/Rel.lean`).

**OPEN**: three callee rules — `getAppFn_spec`, `getAppArgs_spec` and
`mkAppN_spec` (all closed in `Bridge/ExprOps/Spine.lean`) — plus
`Bridge/Core/Walks/Cached.lean`'s `constValAt_spec`, which is itself waiting
on `ExprOps.instLPFast_spec`.  **This is the deepest chain on the list**, and
it is the reason `whnfBody_spec` cannot close before the `ExprOps` tier
does. -/
theorem unfoldDefinition_spec (s₀ : AState) (e : EIdx) (x : Expr)
    (hok : CheckOK mode env fe s₀) (hden : denoteE s₀.store e = some x) :
    ⦃fun s => ⌜s = s₀⌝⦄ ConRon.Arena.unfoldDefinition fe e
    ⦃⇓? r s' => ⌜CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧
        denoteEO s'.store r = some (ConLeche.unfoldDefinition env x)⌝⦄ := by
  sorry

/-- con-leche: ConLeche/Kernel/Core.lean:156-208 reduceNat — **THEOREM 1 for
`reduceNat`**: the literal acceleration, run in the `whnf` loop before
delta-unfolding.  The divergence audit's D15 is preserved by the twin (the
FIRST argument is head-normalised and, unless it is a literal, the step fails
without touching the second), so the two sides' CALL SEQUENCES agree and the
proof is a straight walk.

**OPEN**: `KnotSpec.whnf` at the two arguments (available), plus callee rules
for `rawNatLit?`, `natLitSupported`, `natOpStored`, `natBinOpName` and
`natOpResult` — five `Arena/Core.lean` walks of the state-only group that
this round did not reach either.  Nothing in it needs the `ExprOps`
tier. -/
theorem reduceNat_spec {fuel : Nat} (hsim : KnotSpec mode env fe fuel)
    (s₀ : AState) (d : Nat) (e : EIdx) (x : Expr)
    (hok : CheckOK mode env fe s₀) (hden : denoteE s₀.store e = some x)
    (hw : Expr.WScoped d x) :
    ⦃fun s => ⌜s = s₀⌝⦄
      ConRon.Arena.reduceNat (coreKnot mode fe id fuel) fe d e
    ⦃⇓? r s' => ⌜CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧
        SimOOp (fun F => ConLeche.reduceNatFueled mode env F d x) d
          s'.store r⌝⦄ := by
  sorry

/-! ## 3. The ι step and the projection rule

`whnfCoreBody`'s `.app` and `.proj` clauses' callees. -/

/-- con-leche: ConLeche/Kernel/Core.lean:797-910 iotaRec — **THEOREM 1 for
`iotaRec`**: one ι step at a recursor application, with the stuck-major
machinery under it.

**OPEN, and the largest single item of the tier**: `Arena/Core.lean`'s
`iotaRec` is `iotaRecAt` over `findRule`, and `iotaRecAt` is 85 lines over
`prepareMajor` (120 lines of `majorToCtor`), `recFireComparands`,
`ruleRhsAt` and `iotaCerts`.  Six knot-calling walks under one statement;
the corresponding con-leche tower is `Verify/Iota*.lean`.  Its `ruleRhsAt`
leg waits on `ExprOps.instLPFast_spec` like the other two instantiated
caches. -/
theorem iotaRec_spec {fuel : Nat} (hsim : KnotSpec mode env fe fuel)
    (s₀ : AState) (d : Nat) (e : EIdx) (x : Expr)
    (hok : CheckOK mode env fe s₀) (hden : denoteE s₀.store e = some x)
    (hw : Expr.WScoped d x) :
    ⦃fun s => ⌜s = s₀⌝⦄
      ConRon.Arena.iotaRec mode (coreKnot mode fe id fuel) fe d e
    ⦃⇓? r s' => ⌜CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧
        SimOOp (fun F => ConLeche.iotaRecFueled mode env F d x) d
          s'.store r⌝⦄ := by
  sorry

/-- con-leche: ConLeche/Kernel/Core.lean:742-756 projLitToCtor — **THEOREM 1
for `projLitToCtor`**: a string-literal scrutinee expands to its reduced
constructor form before the projection table is consulted.

**OPEN**: `strLitSupported`, `strLitToConstructor` and `litMajorToCtor` as
callee rules, plus `KnotSpec.whnf`.  `strLitToConstructor` builds a cons
spine in the store, so its rule is the first in this tier whose
postcondition is a genuine `Ext` rather than a store equation. -/
theorem projLitToCtor_spec {fuel : Nat} (hsim : KnotSpec mode env fe fuel)
    (s₀ : AState) (d : Nat) (h : EIdx) (x : Expr)
    (hok : CheckOK mode env fe s₀) (hden : denoteE s₀.store h = some x)
    (hw : Expr.WScoped d x) :
    ⦃fun s => ⌜s = s₀⌝⦄
      ConRon.Arena.projLitToCtor (coreKnot mode fe id fuel) fe d h
    ⦃⇓? r s' => ⌜CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧
        SimEOp (fun F => ConLeche.projLitToCtorFueled mode env F d x) d
          s'.store r⌝⦄ := by
  sorry

/-- con-leche: ConLeche/Kernel/Core.lean:949-961 projCertAt — **THEOREM 1 for
`projCertAt`**: the fire certificate of a projection, gated on
`mode.verifiedChecks`.

**OPEN**: the `verified = false` arm is `pure true` on both sides and is
free; the `true` arm is `projCert`, which reads the projection table and
therefore waits on §3's `denoteProjEntry`.  The argument list's denotation is
`Frontend.denoteEList`, which `Bridge/Rel.lean` already has. -/
theorem projCertAt_spec {fuel : Nat} (hsim : KnotSpec mode env fe fuel)
    (s₀ : AState) (d : Nat) (verified lic : Bool) (c : NIdx) (us : LsIdx)
    (args : List EIdx) (cn : ConLeche.Name) (ls : List Level)
    (xs : List Expr) (hok : CheckOK mode env fe s₀)
    (hc : denoteN s₀.store.ns c = some cn)
    (hus : denoteLs s₀.store.lss us = some ls)
    (hargs : Frontend.denoteEList s₀.store args = some xs) :
    ⦃fun s => ⌜s = s₀⌝⦄
      ConRon.Arena.projCertAt (coreKnot mode fe id fuel) fe d verified lic c
        us args
    ⦃⇓? b s' => ⌜CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧
        SimBOp
          (fun F => ConLeche.projCertAtFueled mode env F d verified lic cn ls
            xs) b⌝⦄ := by
  sorry

/-! ## 4. The `defeq` body's five certificate walks

`Bridge/Core/Arms/Defeq.lean`'s `defeqBody_spec` names exactly these five as
the callee rules it is missing. -/

/-- con-leche: ConLeche/Kernel/Core.lean:307-349 propIrrel — **THEOREM 1 for
`propIrrel`**, the hoisted proof-irrelevance test.

**OPEN**: `notProofFast` as a callee rule (an `IFEnvOK` consequence over the
derived word), then `KnotSpec.inferIO` at both subjects and `KnotSpec.defeq`
at their types. -/
theorem propIrrel_spec {fuel : Nat} (hsim : KnotSpec mode env fe fuel)
    (s₀ : AState) (d : Nat) (a b : EIdx) (x y : Expr)
    (hok : CheckOK mode env fe s₀) (hda : denoteE s₀.store a = some x)
    (hdb : denoteE s₀.store b = some y)
    (hwa : Expr.WScoped d x) (hwb : Expr.WScoped d y) :
    ⦃fun s => ⌜s = s₀⌝⦄
      ConRon.Arena.propIrrel (coreKnot mode fe id fuel) fe d a b
    ⦃⇓? r s' => ⌜CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧
        SimBOp (fun F => ConLeche.propIrrelFueled mode env F d x y) r⌝⦄ := by
  sorry

/-- con-leche: ConLeche/Kernel/Core.lean:532-542 stuckIrrel — **THEOREM 1 for
`stuckIrrel`**, the fallback at two stuck terms: structure-η in both
directions, then the unit certificate.

**OPEN**: `structEtaCert` and `structUnitCert` as callee rules, which are two
more knot-calling walks (`structEtaCertWith` is 70 lines and sits under
both). -/
theorem stuckIrrel_spec {fuel : Nat} (hsim : KnotSpec mode env fe fuel)
    (s₀ : AState) (d : Nat) (a b : EIdx) (x y : Expr)
    (hok : CheckOK mode env fe s₀) (hda : denoteE s₀.store a = some x)
    (hdb : denoteE s₀.store b = some y)
    (hwa : Expr.WScoped d x) (hwb : Expr.WScoped d y) :
    ⦃fun s => ⌜s = s₀⌝⦄
      ConRon.Arena.stuckIrrel mode (coreKnot mode fe id fuel) fe d a b
    ⦃⇓? r s' => ⌜CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧
        SimBOp (fun F => ConLeche.stuckIrrelFueled mode env F d x y) r⌝⦄ := by
  sorry

/-- con-leche: ConLeche/Kernel/Core.lean:505-530 etaCert — **THEOREM 1 for
`etaCert`**: η at a λ against a non-λ.

**OPEN**: the rebuild is `internE (.app (lift b) (.bvar 0))` under a binder,
so it needs `ExprOps.liftLooseBVars`'s spec (closed in
`Bridge/ExprOps/Subst.lean`) and `KnotSpec.defeq` one depth down.  The
statement's FOUR subjects are the λ's two children, its binder datum and the
comparand — `Bridge/Rel.lean`'s `RelE.lam` shape, at the level of a whole
walk. -/
theorem etaCert_spec {fuel : Nat} (hsim : KnotSpec mode env fe fuel)
    (s₀ : AState) (d : Nat) (ty₁ body₁ b : EIdx) (m₁ : BinderMeta)
    (t x y : Expr) (hok : CheckOK mode env fe s₀)
    (hdt : denoteE s₀.store ty₁ = some t)
    (hdx : denoteE s₀.store body₁ = some x)
    (hdy : denoteE s₀.store b = some y)
    (hwa : Expr.WScoped d (.lam t x m₁)) (hwb : Expr.WScoped d y) :
    ⦃fun s => ⌜s = s₀⌝⦄
      ConRon.Arena.etaCert mode (coreKnot mode fe id fuel) fe d ty₁ body₁ m₁ b
    ⦃⇓? r s' => ⌜CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧
        SimBOp (fun F => ConLeche.etaCertFueled mode env F d t x m₁ y)
          r⌝⦄ := by
  sorry

/-- con-leche: ConLeche/Kernel/Core.lean:1420-1439 defeqSpine — **THEOREM 1
for `defeqSpine`**: two applications of the same constant are defeq if their
universe arguments and their argument vectors are.

**OPEN**: `getAppFn_spec`/`getAppArgs_spec` (`ExprOps` tier), `lvlsEq?_spec`
(CLOSED, `Bridge/Core/Walks/Cached.lean`) and `defEqList_spec` below.  Three
of the four are in hand, which makes this the most nearly reachable of the
five. -/
theorem defeqSpine_spec {fuel : Nat} (hsim : KnotSpec mode env fe fuel)
    (s₀ : AState) (d : Nat) (a b : EIdx) (x y : Expr)
    (hok : CheckOK mode env fe s₀) (hda : denoteE s₀.store a = some x)
    (hdb : denoteE s₀.store b = some y)
    (hwa : Expr.WScoped d x) (hwb : Expr.WScoped d y) :
    ⦃fun s => ⌜s = s₀⌝⦄
      ConRon.Arena.defeqSpine (coreKnot mode fe id fuel) fe d a b
    ⦃⇓? r s' => ⌜CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧
        SimBOp (fun F => ConLeche.defeqSpineFueled mode env F d x y) r⌝⦄ := by
  sorry

/-- con-leche: ConLeche/Kernel/Core.lean:245-254 defEqList — **THEOREM 1 for
`defEqList`**: pairwise definitional equality of two argument vectors.

**OPEN**: a `List` induction over `KnotSpec.defeq` — no `ExprOps` rule and no
new denotation — **plus the fuel merge**.  The two subjects are LISTS, so
task #97-P3-0's finding 3 applies: they are quantified inside the relation
(here, by `Frontend.denoteEList` hypotheses at the entry) rather than taken
as `∀`s a recursive call would leave as metavariables.

**The fuel merge is the tier's one unpriced line item** (DESIGN §8's
`### Task #97-P3-CoreWalks` §6.1).  Task #97-P3-Core said con-leche's
`FueledM` wrapper is not needed here because the arena's side is a triple;
that is true of a BODY and false of a LOOP.  Each iteration of this
recursion hands out its own `∃ F` and they have to become one, which is
`Verify/Mono.lean`'s job — and con-leche has `isDefEqCore_mono` and
`pureFns_mono` but no `defEqList_mono`, because `FueledM` did its merging
for it.  Ten lines in `Verify/Mono.lean`'s own shape, owed by the bridge,
and the same debt sits unpaid under `whnfBody_spec`'s loop. -/
theorem defEqList_spec {fuel : Nat} (hsim : KnotSpec mode env fe fuel)
    (s₀ : AState) (d : Nat) (as bs : List EIdx) (xs ys : List Expr)
    (hok : CheckOK mode env fe s₀)
    (hda : Frontend.denoteEList s₀.store as = some xs)
    (hdb : Frontend.denoteEList s₀.store bs = some ys)
    (hwa : ∀ x ∈ xs, Expr.WScoped d x) (hwb : ∀ y ∈ ys, Expr.WScoped d y) :
    ⦃fun s => ⌜s = s₀⌝⦄
      ConRon.Arena.defEqList (coreKnot mode fe id fuel) fe d as bs
    ⦃⇓? r s' => ⌜CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧
        SimBOp (fun F => ConLeche.defEqListFueled mode env F d xs ys)
          r⌝⦄ := by
  sorry

/-! ## 5. The annotation pass's three

`Bridge/Core/Arms/Annotate.lean`'s `annotateBody_spec` names `annotPwPi` and
`annotPwLam`; `isPropType` is under both. -/

/-- con-leche: ConLeche/Kernel/Core.lean:1721-1730 isPropType — **THEOREM 1
for `isPropType`**: is the annotated type a proposition?

**OPEN**: `KnotSpec.annotate` (available) then the head-symbol reader
`typeSortPW`, which is an `ExprOps` walk (`Bridge/ExprOps/Walks.lean`'s
group, closed) this tier does not import. -/
theorem isPropType_spec {fuel : Nat} (hsim : KnotSpec mode env fe fuel)
    (s₀ : AState) (d : Nat) (ty : EIdx) (t : Expr)
    (hok : CheckOK mode env fe s₀) (hden : denoteE s₀.store ty = some t)
    (hw : Expr.WScoped d t) :
    ⦃fun s => ⌜s = s₀⌝⦄
      ConRon.Arena.isPropType (coreKnot mode fe id fuel) fe d ty
    ⦃⇓? r s' => ⌜CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧
        SimBOp
          (fun F => ConLeche.isPropType (ConLeche.pureFns mode env F) env d t)
          r⌝⦄ := by
  sorry

/-- con-leche: ConLeche/Kernel/Core.lean:1746-1777 annotPwPi — **THEOREM 1
for `annotPwPi`**: the `PropWhen` datum a ∀ binder is stamped with.

**OPEN**: `isPropType_spec` above, plus the head-symbol reader `forallPw`
(`ExprOps` tier).  `PropWhen` is a type both tiers share, so the answer
relation is `SimVOp` and nothing has to be denoted. -/
theorem annotPwPi_spec {fuel : Nat} (hsim : KnotSpec mode env fe fuel)
    (s₀ : AState) (d : Nat) (body' : EIdx) (x : Expr)
    (hok : CheckOK mode env fe s₀) (hden : denoteE s₀.store body' = some x)
    (hw : Expr.WScoped d x) :
    ⦃fun s => ⌜s = s₀⌝⦄
      ConRon.Arena.annotPwPi (coreKnot mode fe id fuel) fe d body'
    ⦃⇓? pw s' => ⌜CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧
        SimVOp
          (fun F => ConLeche.annotPwPi (ConLeche.pureFns mode env F) env d x)
          pw⌝⦄ := by
  sorry

/-- con-leche: ConLeche/Kernel/Core.lean:1779-1793 annotPwLam — **THEOREM 1
for `annotPwLam`**: the same at a λ binder.

**OPEN**: `isPropType_spec` and the `lamPw` reader. -/
theorem annotPwLam_spec {fuel : Nat} (hsim : KnotSpec mode env fe fuel)
    (s₀ : AState) (d : Nat) (body' : EIdx) (x : Expr)
    (hok : CheckOK mode env fe s₀) (hden : denoteE s₀.store body' = some x)
    (hw : Expr.WScoped d x) :
    ⦃fun s => ⌜s = s₀⌝⦄
      ConRon.Arena.annotPwLam (coreKnot mode fe id fuel) fe d body'
    ⦃⇓? pw s' => ⌜CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧
        SimVOp
          (fun F => ConLeche.annotPwLam (ConLeche.pureFns mode env F) env d x)
          pw⌝⦄ := by
  sorry

end ConRon.Bridge.Core
