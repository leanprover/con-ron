/-
# `ConRon.Bridge.Core.Walks.Owed` — the sixteen non-slot walks: six CLOSED, TEN open

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

## 0a. Round 3: six of the sixteen are CLOSED, and five of them moved out

Task #97-P3-Core round 3 closed `unfoldableHead`, `headHint`,
`sameConstHeads`, `defeqSpine`, `isPropType` and `defEqList`.  **`defEqList`
is the only one still here** (§4): the other five live in
`Bridge/Core/Walks/Spine.lean`, a sibling module off the knot-facing import
chain, because a module that imports the `ExprOps` tier or `mvcgen`s over
`ensureSort` cannot sit in one closure with `Core/EnsureSort.lean` — that
module's own header has the error message and the reason.  The statements
below are therefore the TEN that are open, plus `defEqList`'s proof and the
pure side of two walks whose arena side is not written.

Three things made the six possible, and none of them is about any one walk:

1. **`Bridge/Core/**` imports the `ExprOps` tier.**  Its thirteen modules
   reached zero `sorry` while round 2 ran, and task #97-P3-CoreWalks left
   three walks here with the note *"until this tier imports the `ExprOps`
   tier"*.  The import is `ConRon.Bridge.ExprOps.Spine` and it costs nothing:
   no theorem of that tier is registered `@[spec]`, so `mvcgen` sees them
   only where they are passed.
2. **The knot's six slots in ANSWER shape** (`Bridge/Core/Knot.lean`, round
   3): §0's rule, paid once at the knot instead of per site.
3. **The fuel merge** (`Bridge/Core/Walks/Mono.lean`, round 2), which
   `defEqList`'s cons arm and `isPropType`'s conclusion both spend.

## 0. The shape correction of task #97-P3-Core-2, and why it was forced

The first two statements of this module — `unfoldDefinition_spec` and
`reduceNat_spec`, the two `whnfBody_spec` consumes — took the subject's
denotation as an explicit `(x : Expr)` argument with a
`denoteE s₀.store e = some x` hypothesis.  **That shape cannot be used from a
caller that reaches the walk through another call**, and `whnfStep` is
exactly such a caller: it runs `r.whnfCore` first and hands `reduceNat` the
REDUCT, whose denotation is not known until the first call's postcondition is
in hand.  `mvcgen` must guess `x` when it applies the spec, it guesses the
only `Expr` in scope (the *original* subject), and the side goal it leaves —
`denoteE s.store <reduct> = some <original>` — is false.

The fix is task #97-P3-0's own **rule 4** (*"a precondition with no `Expr` in
it, so that a recursive call's side goal carries no metavariable"*) taken one
step further: the denotation goes into the hypothesis as an **existential**
(`∃ x, denoteE s₀.store e = some x ∧ Expr.WScoped d x`, which names no
metavariable) and out of the postcondition as a **universal** (`∀ x,
denoteE s₀.store e = some x → …`), which is the shape
`Bridge/Core/Walks/Cached.lean`'s closed exemplars already have and the shape
`Bridge/Core/Arms/Whnf.lean`'s `whnfLoop_spec` needs at every iteration.
The other fourteen statements below keep the explicit-argument shape for now;
each should move the day its caller is written, and the rule is: *a walk
whose subject is another walk's ANSWER must not take that answer's denotation
as an explicit argument.*

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

## 2. What the TEN that are left are waiting on (round 3's reading)

* **three on a module that does not exist** — `propIrrel`, `annotPwPi` and
  `annotPwLam` read `Arena/PropRead.lean`'s `notProofFast`, `isProofFast`,
  `typeSortPW` and `proofPW`, and that file has no bridge spec anywhere.  It
  is a tier, not a callee rule, and nobody had costed it;
* **three on `instLPFast_spec`'s missing cache frame** — `unfoldDefinition`
  through `Walks/Cached.lean`'s `constValAt_spec`, and `projCertAt` through
  `Walks/Proj.lean`'s `projCert_spec` / `constTyAt_spec`.  DESIGN §8's
  `### Task #97-P3-Core-2` round 3 finding 19 has the two conjuncts the
  `ExprOps` tier owes;
* **`etaCert`** — nothing outside this tier: its pure side is proved below
  and so is the callee rule's answer shape;
* **`reduceNat`** — five state-only walks of `Arena/Core.lean` and nothing
  else, which is why round 2's §9 named it first;
* **`projLitToCtor`** — `strLitSupported`, `strLitToConstructor` and
  `litMajorToCtor`;
* **`stuckIrrel`** and **`iotaRec`**, the two towers.

(Round 2's reading of this list said *"ten of the sixteen wait on an
`ExprOps`-tier callee rule that this tier does not import"*.  That was true
of the import and wrong about the count: the `ExprOps` import closed three
walks outright and is not what any of the remaining ten is blocked on.)

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
import ConRon.Bridge.Core.Walks.Mono

namespace ConRon.Bridge.Core

set_option autoImplicit false
set_option mvcgen.warning false
set_option maxHeartbeats 1000000

open ConLeche ConRon.Arena ConRon.Bridge Std.Do

variable {mode : CheckMode} {env : Env} {fe : IFEnv}

/-! `isBoolTrue` was the fourth of this group and is **CLOSED** —
`Bridge/Core/Walks/Guards.lean`.  It was the cheapest of the seventeen (five
verification conditions, no `ExprOps` rule, no new denotation), and closing
it is this round's evidence that the row above really is the cheap one. -/

/-! ## 2. The delta step and the literal acceleration

`whnfStep`'s two callees (`Bridge/Core/Arms/Whnf.lean`'s `whnfLoop_delta`
and `whnfLoop_reduceNat` are their pure-side step lemmas, and both are
closed), which is why `whnfBody_spec` — the most reachable of the six body
walks — is still open. -/

/-! `unfoldDefinition_spec` **moved to `Bridge/Core/Walks/Spine.lean`** in
round 4 and is CLOSED there: it needs `getAppFn`/`getAppArgs`/`mkAppN` from
the `ExprOps` tier and the index facts that module owns, and the reason it
could not import them from here (finding 18) is gone. -/

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
    (s₀ : AState) (d : Nat) (e : EIdx) (hok : CheckOK mode env fe s₀)
    (hdw : ∃ x, denoteE s₀.store e = some x ∧ Expr.WScoped d x) :
    ⦃fun s => ⌜s = s₀⌝⦄
      ConRon.Arena.reduceNat (coreKnot mode fe id fuel) fe d e
    ⦃⇓? r s' => ⌜CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧
        ∀ x, denoteE s₀.store e = some x →
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

/-! `projCertAt_spec` **moved to `Bridge/Core/Walks/Proj.lean`** in round 4
and is CLOSED there, beside `projCert_spec`. -/

/-! ## 4. The `defeq` body's five certificate walks

`Bridge/Core/Arms/Defeq.lean`'s `defeqBody_spec` names exactly these five as
the callee rules it is missing. -/

/-- con-leche: ConLeche/Kernel/Core.lean:307-349 propIrrel — **THEOREM 1 for
`propIrrel`**, the hoisted proof-irrelevance test.

**OPEN, on a MODULE that does not exist** (round 3's reading): `notProofFast`
and `isProofFast` are `Arena/PropRead.lean` walks and that file has no bridge
spec anywhere — not one.  After them it is `KnotSpec.inferIO'` at both
subjects and `KnotSpec.defeq'` at their types, both in hand.  It shares its
blocker with `annotPwPi` and `annotPwLam` below. -/
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

/-! ### `etaCert`'s pure side, and the ExprOps slot in ANSWER shape

The walk itself is not closed (its arm list is in the statement's note), but
**its whole pure side is**, and so is the one callee rule whose published
shape it cannot use.  Both are here because they are what the next round
starts from and neither is about `etaCert` alone:

* the four step equations below are con-leche's `etaCert` at its four exits,
  each one `simp only` over the knot record's five slot equations;
* `instantiate1Fast_specE` is **finding 5.2 at the `ExprOps` tier**.
  `Bridge/ExprOps/Inst1.lean`'s `instantiate1Fast_spec` takes the
  SUBSTITUTED VALUE's denotation as an explicit `(ve : Expr)` argument, and
  `etaCert` substitutes a free variable it has just INTERNED — so `mvcgen`
  guesses `ve` from the `Expr`s in scope (measured: it guesses the
  comparand `y`) and leaves a false side goal.  The primed form is the same
  four lines as `Bridge/Core/Knot.lean`'s six slots, and it is the shape
  every interning caller of the substitution walks will want. -/

/-- con-leche: ConLeche/Kernel/Core.lean:505-530 etaCert — the comparand's
type does not reduce to a ∀, so there is nothing to η-expand against. -/
theorem etaCertFueled_nf {F d : Nat} {t x : Expr} {m₁ : BinderMeta} {y : Expr}
    {tb w : Expr}
    (h1 : ConLeche.inferTypeIO mode env F d y = .ok tb)
    (h2 : ConLeche.whnf mode env F d tb = .ok w)
    (hw : ∀ p q m, w ≠ .forallE p q m) :
    ConLeche.etaCertFueled mode env F d t x m₁ y = .ok false := by
  have e1 : (ConLeche.pureFns mode env F).inferIO d y = .ok tb := h1
  have e2 : (ConLeche.pureFns mode env F).whnf d tb = .ok w := h2
  simp only [ConLeche.etaCertFueled, ConLeche.etaCert, e1, e2, bind,
    Except.bind]
  rfl

/-- con-leche: ConLeche/Kernel/Core.lean:505-530 etaCert — the ∀'s domain
is not the λ's. -/
theorem etaCertFueled_dom {F d : Nat} {t x : Expr} {m₁ : BinderMeta}
    {y : Expr} {tb ty₂ bd₂ : Expr} {m₂ : BinderMeta}
    (h1 : ConLeche.inferTypeIO mode env F d y = .ok tb)
    (h2 : ConLeche.whnf mode env F d tb = .ok (.forallE ty₂ bd₂ m₂))
    (h3 : ConLeche.isDefEqCore mode env F d ty₂ t = .ok false) :
    ConLeche.etaCertFueled mode env F d t x m₁ y = .ok false := by
  have e1 : (ConLeche.pureFns mode env F).inferIO d y = .ok tb := h1
  have e2 : (ConLeche.pureFns mode env F).whnf d tb
      = .ok (.forallE ty₂ bd₂ m₂) := h2
  have e3 : (ConLeche.pureFns mode env F).defeq d ty₂ t = .ok false := h3
  simp only [ConLeche.etaCertFueled, ConLeche.etaCert, e1, e2, e3, bind,
    Except.bind]
  rfl

/-- con-leche: ConLeche/Kernel/Core.lean:505-530 etaCert — the domains
agree and the bodies do not. -/
theorem etaCertFueled_body {F d : Nat} {t x : Expr} {m₁ : BinderMeta}
    {y : Expr} {tb ty₂ bd₂ : Expr} {m₂ : BinderMeta}
    (h1 : ConLeche.inferTypeIO mode env F d y = .ok tb)
    (h2 : ConLeche.whnf mode env F d tb = .ok (.forallE ty₂ bd₂ m₂))
    (h3 : ConLeche.isDefEqCore mode env F d ty₂ t = .ok true)
    (h4 : ConLeche.isDefEqCore mode env F (d + 1)
      (x.instantiate1 (.fvar d t)) (.app y (.fvar d t)) = .ok false) :
    ConLeche.etaCertFueled mode env F d t x m₁ y = .ok false := by
  have e1 : (ConLeche.pureFns mode env F).inferIO d y = .ok tb := h1
  have e2 : (ConLeche.pureFns mode env F).whnf d tb
      = .ok (.forallE ty₂ bd₂ m₂) := h2
  have e3 : (ConLeche.pureFns mode env F).defeq d ty₂ t = .ok true := h3
  have e4 : (ConLeche.pureFns mode env F).defeq (d + 1)
      (x.instantiate1 (.fvar d t)) (.app y (.fvar d t)) = .ok false := h4
  simp only [ConLeche.etaCertFueled, ConLeche.etaCert, e1, e2, e3, e4, bind,
    Except.bind, if_true]
  rfl

/-- con-leche: ConLeche/Kernel/Core.lean:505-530 etaCert — **the
certificate**: the domains agree, the opened bodies agree, and (at a verified
mode) the two `PropWhen` data agree.  Task #161's regime agreement is checked
LAST on both sides, which is what makes the two call sequences the same. -/
theorem etaCertFueled_yes {F d : Nat} {t x : Expr} {m₁ : BinderMeta}
    {y : Expr} {tb ty₂ bd₂ : Expr} {m₂ : BinderMeta}
    (h1 : ConLeche.inferTypeIO mode env F d y = .ok tb)
    (h2 : ConLeche.whnf mode env F d tb = .ok (.forallE ty₂ bd₂ m₂))
    (h3 : ConLeche.isDefEqCore mode env F d ty₂ t = .ok true)
    (h4 : ConLeche.isDefEqCore mode env F (d + 1)
      (x.instantiate1 (.fvar d t)) (.app y (.fvar d t)) = .ok true)
    (h5 : (mode.verifiedChecks && !(m₁.pw == m₂.pw)) = false) :
    ConLeche.etaCertFueled mode env F d t x m₁ y = .ok true := by
  have e1 : (ConLeche.pureFns mode env F).inferIO d y = .ok tb := h1
  have e2 : (ConLeche.pureFns mode env F).whnf d tb
      = .ok (.forallE ty₂ bd₂ m₂) := h2
  have e3 : (ConLeche.pureFns mode env F).defeq d ty₂ t = .ok true := h3
  have e4 : (ConLeche.pureFns mode env F).defeq (d + 1)
      (x.instantiate1 (.fvar d t)) (.app y (.fvar d t)) = .ok true := h4
  simp only [ConLeche.etaCertFueled, ConLeche.etaCert, e1, e2, e3, e4, h5,
    bind, Except.bind, if_true]
  rfl

/-! `etaCert_spec` **moved to `Bridge/Core/Walks/Spine.lean`** in round 4
and is CLOSED there, beside `instantiate1Fast_specE`, the one callee rule
whose answer shape it needs. -/

/-! ### `defEqList`, the tier's first `List` recursion

The two list inversions, the four pure-side step equations, the induction
itself, and the caller-facing statement derived from it.

**The statement the induction runs on is not the one `Owed.lean` published**,
and for finding 5.2's reason one step further out: at the recursive call the
subjects `as'` and `bs'` are known but their DENOTATIONS are not — the state
has moved, so `denoteEList s'.store as' = some ?xs` arrives with a
metavariable and `mvcgen` guesses `?xs := xs`, the whole list.  So
`defEqList_go` takes the two denotations as existentials and hands them back
as universals — the primed shape of `Bridge/Core/Knot.lean`'s six slots, at a
walk rather than a slot — and `defEqList_spec` below is four lines over it.
The rule generalises: *the ∃/∀ shape is not about knot slots, it is about
every recursive call whose state has moved.* -/

/-- con-leche: none — the empty handle list denotes the empty list. -/
theorem denoteEList_nil_inv {st : EStore} {xs : List Expr}
    (h : Frontend.denoteEList st [] = some xs) : xs = [] := by
  simp only [Frontend.denoteEList] at h; exact (Option.some.inj h).symm

/-- con-leche: none — a denoting cons is a cons of denotations. -/
theorem denoteEList_cons_inv {st : EStore} {a : EIdx} {as : List EIdx}
    {xs : List Expr} (h : Frontend.denoteEList st (a :: as) = some xs) :
    ∃ x xs', denoteE st a = some x ∧ Frontend.denoteEList st as = some xs' ∧
      xs = x :: xs' := by
  simp only [Frontend.denoteEList] at h
  cases ha : denoteE st a with
  | none => rw [ha] at h; simp at h
  | some x =>
    cases has : Frontend.denoteEList st as with
    | none => rw [ha, has] at h; simp at h
    | some xs' => rw [ha, has] at h; exact ⟨x, xs', rfl, rfl, (Option.some.inj h).symm⟩

/-- con-leche: ConLeche/Kernel/Core.lean:245-254 defEqList — two empty
spines agree. -/
theorem defEqListFueled_nil {F d : Nat} :
    ConLeche.defEqListFueled mode env F d [] [] = .ok true := rfl

/-- con-leche: ConLeche/Kernel/Core.lean:245-254 defEqList — a length
mismatch declines (empty against a cons). -/
theorem defEqListFueled_ln {F d : Nat} {y : Expr} {ys : List Expr} :
    ConLeche.defEqListFueled mode env F d [] (y :: ys) = .ok false := rfl

/-- con-leche: ConLeche/Kernel/Core.lean:245-254 defEqList — and the
other way round. -/
theorem defEqListFueled_rn {F d : Nat} {x : Expr} {xs : List Expr} :
    ConLeche.defEqListFueled mode env F d (x :: xs) [] = .ok false := rfl

/-- con-leche: ConLeche/Kernel/Core.lean:245-254 defEqList — the heads
agree, so the verdict is the tails'.  **At ONE fuel**: the caller merges the
head's and the tail's with `isDefEqCore_mono` and `defEqListFueled_mono`. -/
theorem defEqListFueled_cons_true {F d : Nat} {x y : Expr}
    {xs ys : List Expr} {r : Bool}
    (h : ConLeche.isDefEqCore mode env F d x y = .ok true)
    (ht : ConLeche.defEqListFueled mode env F d xs ys = .ok r) :
    ConLeche.defEqListFueled mode env F d (x :: xs) (y :: ys) = .ok r := by
  have hd : (ConLeche.pureFns mode env F).defeq d x y = .ok true := h
  simp only [ConLeche.defEqListFueled, ConLeche.defEqList, hd, bind,
    Except.bind, if_true]
  exact ht

/-- con-leche: ConLeche/Kernel/Core.lean:245-254 defEqList — the heads
disagree, so the spines do. -/
theorem defEqListFueled_cons_false {F d : Nat} {x y : Expr}
    {xs ys : List Expr}
    (h : ConLeche.isDefEqCore mode env F d x y = .ok false) :
    ConLeche.defEqListFueled mode env F d (x :: xs) (y :: ys) = .ok false := by
  have hd : (ConLeche.pureFns mode env F).defeq d x y = .ok false := h
  simp only [ConLeche.defEqListFueled, ConLeche.defEqList, hd, bind,
    Except.bind]
  rfl

/-- con-leche: ConLeche/Kernel/Core.lean:245-254 defEqList — **the
induction**, in the ∃/∀ shape the recursive call forces (see the section
note).  Four arms; the cons/cons arm has eight verification conditions and the
fuel merge. -/
theorem defEqList_go {fuel : Nat} (hsim : KnotSpec mode env fe fuel) (d : Nat) :
    ∀ (as bs : List EIdx) (s₀ : AState),
      CheckOK mode env fe s₀ →
      (∃ xs, Frontend.denoteEList s₀.store as = some xs ∧
        ∀ x ∈ xs, Expr.WScoped d x) →
      (∃ ys, Frontend.denoteEList s₀.store bs = some ys ∧
        ∀ y ∈ ys, Expr.WScoped d y) →
      ⦃fun s => ⌜s = s₀⌝⦄
        ConRon.Arena.defEqList (coreKnot mode fe id fuel) fe d as bs
      ⦃⇓? r s' => ⌜CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
          s'.pins = s₀.pins ∧
          ∀ xs ys, Frontend.denoteEList s₀.store as = some xs →
            Frontend.denoteEList s₀.store bs = some ys →
            SimBOp (fun F => ConLeche.defEqListFueled mode env F d xs ys) r⌝⦄ := by
  intro as
  induction as with
  | nil =>
    intro bs s₀ hok hda hdb
    cases bs with
    | nil =>
      mvcgen [ConRon.Arena.defEqList]
      bridge_peel; subst_vars
      refine ⟨hok, Ext.refl _, rfl, fun xs ys hx hy => ?_⟩
      obtain rfl := denoteEList_nil_inv hx
      obtain rfl := denoteEList_nil_inv hy
      exact ⟨0, defEqListFueled_nil⟩
    | cons b bs' =>
      mvcgen [ConRon.Arena.defEqList]
      bridge_peel; subst_vars
      refine ⟨hok, Ext.refl _, rfl, fun xs ys hx hy => ?_⟩
      obtain rfl := denoteEList_nil_inv hx
      obtain ⟨y, ys', _, _, rfl⟩ := denoteEList_cons_inv hy
      exact ⟨0, defEqListFueled_ln⟩
  | cons a as' ih =>
    intro bs s₀ hok hda hdb
    cases bs with
    | nil =>
      mvcgen [ConRon.Arena.defEqList]
      bridge_peel; subst_vars
      refine ⟨hok, Ext.refl _, rfl, fun xs ys hx hy => ?_⟩
      obtain ⟨x, xs', _, _, rfl⟩ := denoteEList_cons_inv hx
      obtain rfl := denoteEList_nil_inv hy
      exact ⟨0, defEqListFueled_rn⟩
    | cons b bs' =>
      have hdq := hsim.defeq'
      mvcgen [ConRon.Arena.defEqList, hdq, ih]
      case vc1 => bridge_peel; subst_vars; exact hok
      case vc2 =>
        bridge_peel; subst_vars
        obtain ⟨xs, hxs, hw⟩ := hda
        obtain ⟨x, xs', hx, _, rfl⟩ := denoteEList_cons_inv hxs
        exact ⟨x, hx, hw x (by simp)⟩
      case vc3 =>
        bridge_peel; subst_vars
        obtain ⟨ys, hys, hw⟩ := hdb
        obtain ⟨y, ys', hy, _, rfl⟩ := denoteEList_cons_inv hys
        exact ⟨y, hy, hw y (by simp)⟩
      case vc4 =>
        bridge_peel; subst_vars
        rename_i s2 s1 rb s0 hck1 hxt21 hpn12 hdefeq
        intro hck hxt hpn hrec
        refine ⟨hck, hxt21.trans hxt, by rw [hpn, hpn12],
          fun xs ys hx hy => ?_⟩
        obtain ⟨x, xs', hdx, hdxs, rfl⟩ := denoteEList_cons_inv hx
        obtain ⟨y, ys', hdy, hdys, rfl⟩ := denoteEList_cons_inv hy
        obtain ⟨F1, hF1⟩ := hdefeq x y hdx hdy
        obtain ⟨F2, hF2⟩ :=
          hrec xs' ys' (denoteEList_ext hxt21 as' xs' hdxs)
            (denoteEList_ext hxt21 bs' ys' hdys)
        exact ⟨max F1 F2,
          defEqListFueled_cons_true
            (ConLeche.isDefEqCore_mono (Nat.le_max_left _ _) hF1)
            (defEqListFueled_mono (Nat.le_max_right _ _) hF2)⟩
      case vc5 => bridge_peel; subst_vars; intro s hck _ _ _; exact hck
      case vc6 =>
        bridge_peel; subst_vars
        intro s _ hxt _ _
        obtain ⟨xs, hxs, hw⟩ := hda
        obtain ⟨x, xs', _, hdxs, rfl⟩ := denoteEList_cons_inv hxs
        exact ⟨xs', denoteEList_ext hxt as' xs' hdxs,
          fun z hz => hw z (by simp [hz])⟩
      case vc7 =>
        bridge_peel; subst_vars
        intro s _ hxt _ _
        obtain ⟨ys, hys, hw⟩ := hdb
        obtain ⟨y, ys', _, hdys, rfl⟩ := denoteEList_cons_inv hys
        exact ⟨ys', denoteEList_ext hxt bs' ys' hdys,
          fun z hz => hw z (by simp [hz])⟩
      case vc8 =>
        bridge_peel; subst_vars
        rename_i s1 rb hnb s0 hck0 hxt10 hpn01 hdefeq
        obtain rfl : rb = false := by
          cases rb with
          | false => rfl
          | true => exact absurd rfl hnb
        refine ⟨hck0, hxt10, hpn01, fun xs ys hx hy => ?_⟩
        obtain ⟨x, xs', hdx, _, rfl⟩ := denoteEList_cons_inv hx
        obtain ⟨y, ys', hdy, _, rfl⟩ := denoteEList_cons_inv hy
        obtain ⟨F1, hF1⟩ := hdefeq x y hdx hdy
        exact ⟨F1, defEqListFueled_cons_false hF1⟩

/-- con-leche: ConLeche/Kernel/Core.lean:245-254 defEqList — **THEOREM 1 for
`defEqList`**: pairwise definitional equality of two argument vectors.
**CLOSED** (round 3), at the published statement, over `defEqList_go`'s
induction.

DESIGN §8's `### Task #97-P3-CoreWalks` §6.1 named the fuel merge as the one
thing this walk was missing beyond the induction; `Walks/Mono.lean`'s
`defEqListFueled_mono` is it, and the cons arm's `max F₁ F₂` over it and
con-leche's own `isDefEqCore_mono` is two lines. -/
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
  have hb := defEqList_go hsim d as bs s₀ hok ⟨xs, hda, hwa⟩ ⟨ys, hdb, hwb⟩
  mvcgen [hb]
  intro h1 h2 h3 h4
  exact ⟨h1, h2, h3, h4 xs ys hda hdb⟩

/-! ## 5. The annotation pass's three

`Bridge/Core/Arms/Annotate.lean`'s `annotateBody_spec` names `annotPwPi` and
`annotPwLam`; `isPropType` is under both. -/

/-- con-leche: ConLeche/Kernel/Core.lean:1746-1777 annotPwPi — **THEOREM 1
for `annotPwPi`**: the `PropWhen` datum a ∀ binder is stamped with.

**OPEN**: `isPropType_spec` (CLOSED, `Bridge/Core/Walks/Spine.lean`) and the
head-symbol reader — which is **`Arena/PropRead.lean`'s `typeSortPW`, not an
`ExprOps` walk**, and that file has no bridge spec anywhere (round 3's
correction; `ExprOps/Walks.lean`'s `forallPw_spec` is a different reader and
is not what this clause calls).  `PropWhen` is a type both tiers share, so
the answer relation is `SimVOp` and nothing has to be denoted. -/
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

**OPEN**: `isPropType_spec` (CLOSED) and `Arena/PropRead.lean`'s `proofPW`
— the same missing module as `annotPwPi` and `propIrrel` (round 3). -/
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

/-! ## 6. The axiom census

The round's one CLOSED walk in this module, its induction, and the pure-side
step equations of the two walks whose arena side is still open. -/

section Census

#print axioms denoteEList_cons_inv
#print axioms defEqListFueled_cons_true
#print axioms defEqList_go
#print axioms defEqList_spec
#print axioms etaCertFueled_yes

end Census

end ConRon.Bridge.Core
