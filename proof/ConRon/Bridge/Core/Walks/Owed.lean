/-
# `ConRon.Bridge.Core.Walks.Owed` — the sixteen non-slot walks (all CLOSED now; the notes below keep each round's status)

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
`Verify/Knot.lean`'s own `…Fueled` abbreviation, and each (proved since) with
what it was waiting on noted at the site.

This is `Bridge/ExprOps/Owed.lean`'s role one tier up: a statement is not a
proof, but it is the interface, and the six body walks cannot be written
against a walk that has no statement.

## 0a. Round 3: six of the sixteen are CLOSED, and five of them moved out

Task #97-P3-Core round 3 closed `unfoldableHead`, `headHint`,
`sameConstHeads`, `defeqSpine`, `isPropType` (deleted with con-leche's
`isPropType`, task #105) and `defEqList`.  **`defEqList`
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
   no theorem of that tier is registered `@[spec]`, so `vcgen` (`mvcgen`
   then) sees them only where they are passed.
2. **The knot's six slots in ANSWER shape** (`Bridge/Core/Knot.lean`, round
   3): §0's rule, paid once at the knot instead of per site.
3. **The fuel merge** (`Bridge/Core/Walks/Mono.lean`, round 2), which
   `defEqList`'s cons arm spends.

## 0. The shape correction of task #97-P3-Core-2, and why it was forced

The first two statements of this module — `unfoldDefinition_spec` and
`reduceNat_spec`, the two `whnfBody_spec` consumes — took the subject's
denotation as an explicit `(x : Expr)` argument with a
`denoteE s₀.store e = some x` hypothesis.  **That shape cannot be used from a
caller that reaches the walk through another call**, and `whnfStep` is
exactly such a caller: it runs `r.whnfCore` first and hands `reduceNat` the
REDUCT, whose denotation is not known until the first call's postcondition is
in hand.  `mvcgen` had to guess `x` when it applied the spec, it guessed the
only `Expr` in scope (the *original* subject), and the side goal it left —
`denoteE s.store <reduct> = some <original>` — was false.  (`vcgen` guesses
nothing: it leaves `x` a metavariable and an `Expr` goal of its own, which is
no better.)

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
| `SimBOp` — a `Bool` answer | `projCertAt`, `propIrrel`, `stuckIrrel`, `etaCert`, `defeqSpine`, `defEqList` |
| an EQUATION — the pure side takes no fuel | `unfoldDefinition`, `unfoldableHead`, `sameConstHeads` (and `headHint`, `isBoolTrue`, CLOSED in `Walks/Spine.lean`, `Walks/Guards.lean`) |

**The last row is the cheap one and it is worth naming.**  Five walks of the
group (three here, `headHint` in `Walks/Spine.lean`, `isBoolTrue` in
`Walks/Guards.lean`) refine a con-leche function that is not in `CheckM` at all
(`unfoldDefinition env e : Option Expr`, `unfoldableHead env e : Bool`,
`sameConstHeads a b : Bool`, `headHint env e : ReducibilityHint`,
`Expr.isBoolTrue e : Bool`), so there is no
`∃ F` and no fuel bookkeeping: the conclusion is an equation between the
arena's answer and con-leche's.  They are the first four of these to write.

## 2. What the THREE that are left are waiting on (round 5)

Round 4 closed four of round 3's ten and moved each to the module whose
imports it needs: `unfoldDefinition` and `etaCert` to `Walks/Spine.lean`,
`projCertAt` to `Walks/Proj.lean`, `reduceNat` to `Walks/Nat.lean`.  Round 5
closed three more — `propIrrel`, `annotPwPi` and `annotPwLam`, which waited
on `Arena/PropRead.lean`'s readers — and moved them beside those readers'
theorems, to `Walks/PropRead.lean`.  Left here:

* **`projLitToCtor`** — `strLitSupported`, `strLitToConstructor` and
  `litMajorToCtor`;
* **`stuckIrrel`** and **`iotaRec`**, the two towers (`iotaRec`'s
  `ruleRhsAt` and `iotaCertsFull` legs are now closed callee rules).

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
import ConRon.Bridge.Frame
import ConRon.Bridge.Grind

namespace ConRon.Bridge.Core

set_option autoImplicit false
set_option experimental.vcgen true
set_option maxHeartbeats 1000000

open ConLeche ConRon.Arena ConRon.Bridge Std.WP
open scoped Lean.Order

variable {mode : CheckMode} {env : Env} {fe : IFEnv}

/-! `isBoolTrue` was the fourth of this group and is **CLOSED** —
`Bridge/Core/Walks/Guards.lean`.  It was the cheapest of the seventeen (five
verification conditions, no `ExprOps` rule, no new denotation), and closing
it is this round's evidence that the row above really is the cheap one. -/

/-! ## 2. The delta step and the literal acceleration

`whnfStep`'s two callees (`Bridge/Core/Arms/Whnf.lean`'s `whnfLoop_delta`
and `whnfLoop_reduceNat` are their pure-side step lemmas, and both are
closed), which is why `whnfBody_spec` — the most reachable of the six body
walks — was still open then (closed since). -/

/-! `unfoldDefinition_spec` **moved to `Bridge/Core/Walks/Spine.lean`** in
round 4 and is CLOSED there: it needs `getAppFn`/`getAppArgs`/`mkAppN` from
the `ExprOps` tier and the index facts that module owns, and the reason it
could not import them from here (finding 18) is gone. -/

/-! `reduceNat_spec` **moved to `Bridge/Core/Walks/Nat.lean`** in round 4
and is CLOSED there, over the six state-only walks under it. -/

/-! ## 3. The ι step and the projection rule

`whnfCoreBody`'s `.app` and `.proj` clauses' callees. -/

/-! `iotaRec_spec` **moved to `Bridge/Core/Walks/Iota.lean`** in round 6: its
η rescue calls `structEtaCertWith` (`Walks/Stuck.lean`), which this module
cannot import.  It gained `hμ` and `EnvWF env` there (that module's note). -/

/-! `projLitToCtor_spec` **moved to `Bridge/Core/Walks/ProjLit.lean`** in round
5 and is CLOSED there, over `strLitSupported_spec` (`Walks/StrLit.lean`) and
`strLitToConstructor_spec` (`Walks/StrCtor.lean`). -/

/-! `projCertAt_spec` **moved to `Bridge/Core/Walks/Proj.lean`** in round 4
and is CLOSED there, beside `projCert_spec`. -/

/-! ## 4. The `defeq` body's five certificate walks

`Bridge/Core/Arms/Defeq.lean`'s `defeqBody_spec` names exactly these five as
the callee rules it is missing. -/

/-! `propIrrel_spec` **moved to `Bridge/Core/Walks/PropRead.lean`** in round 5
and is CLOSED there, over that module's `notProofFast` / `isProofFast`. -/

/-! `stuckIrrel_spec` **moved to `Bridge/Core/Walks/Stuck.lean`** in round 5,
where it is PROVED from three child walks (`structEtaCert_spec`,
`structUnitCert_spec`, `proofIrrel_spec`) and gains the precondition
`hμ : mode.verifiedChecks = true` (that module's note says why). -/

/-! ### `etaCert`'s pure side, and the ExprOps slot in ANSWER shape

The walk itself is not closed (its arm list is in the statement's note), but
**its whole pure side is**, and so is the one callee rule whose published
shape it cannot use.  Both are here because they are what the next round
starts from and neither is about `etaCert` alone:

* the six step equations below are con-leche's `etaCert` at its six exits,
  each one `simp only` over the knot record's slot equations;
* `instantiate1Fast_specE` is **finding 5.2 at the `ExprOps` tier**.
  `Bridge/ExprOps/Inst1.lean`'s `instantiate1Fast_spec` takes the
  SUBSTITUTED VALUE's denotation as an explicit `(ve : Expr)` argument, and
  `etaCert` substitutes a free variable it has just INTERNED — so `mvcgen`
  guesses `ve` from the `Expr`s in scope (measured: it guesses the
  comparand `y`) and leaves a false side goal.  The primed form is the same
  four lines as `Bridge/Core/Knot.lean`'s slots, and it is the shape
  every interning caller of the substitution walks will want. -/

/-- con-leche: ConLeche/Kernel/Core.lean:461-484 etaCert — the comparand's
head is a λ, a `let` or a loose variable (not `ioNeutral`), so there is no
certificate. -/
theorem etaCertFueled_notNeutral {F d : Nat} {t x y : Expr}
    (hn : y.ioNeutral = false) :
    ConLeche.etaCertFueled mode env F d t x y = .ok false := by
  simp only [ConLeche.etaCertFueled, ConLeche.etaCert, hn]
  rfl

/-- con-leche: ConLeche/Kernel/Core.lean:461-484 etaCert — the comparand's
type does not reduce to a ∀, so there is nothing to η-expand against. -/
theorem etaCertFueled_nf {F d : Nat} {t x y : Expr} {tb w : Expr}
    (hn : y.ioNeutral = true)
    (h1 : ConLeche.inferTypeIO mode env F d y = .ok tb)
    (h2 : ConLeche.whnf mode env F d tb = .ok w)
    (hw : ∀ p q, w ≠ .forallE p q) :
    ConLeche.etaCertFueled mode env F d t x y = .ok false := by
  have e1 : (ConLeche.pureFns mode env F).inferIO d y = .ok tb := h1
  have e2 : (ConLeche.pureFns mode env F).whnf d tb = .ok w := h2
  simp only [ConLeche.etaCertFueled, ConLeche.etaCert, hn, e1, e2, bind,
    Except.bind, Bool.not_true, Bool.false_eq_true, ite_false]
  cases w <;> first | rfl | exact absurd rfl (hw _ _)

/-- con-leche: ConLeche/Kernel/Core.lean:461-484 etaCert — the ∀'s domain
is not the λ's. -/
theorem etaCertFueled_dom {F d : Nat} {t x y : Expr} {tb ty₂ bd₂ : Expr}
    (hn : y.ioNeutral = true)
    (h1 : ConLeche.inferTypeIO mode env F d y = .ok tb)
    (h2 : ConLeche.whnf mode env F d tb = .ok (.forallE ty₂ bd₂))
    (h3 : ConLeche.isDefEqCore mode env F d ty₂ t = .ok false) :
    ConLeche.etaCertFueled mode env F d t x y = .ok false := by
  have e1 : (ConLeche.pureFns mode env F).inferIO d y = .ok tb := h1
  have e2 : (ConLeche.pureFns mode env F).whnf d tb = .ok (.forallE ty₂ bd₂) := h2
  have e3 : (ConLeche.pureFns mode env F).defeq d ty₂ t = .ok false := h3
  simp only [ConLeche.etaCertFueled, ConLeche.etaCert, hn, e1, e2, e3, bind,
    Except.bind, Bool.not_true, Bool.false_eq_true, ite_false]
  rfl

/-- con-leche: ConLeche/Kernel/Core.lean:461-484 etaCert — the domains
agree and the bodies do not. -/
theorem etaCertFueled_body {F d : Nat} {t x y : Expr} {tb ty₂ bd₂ : Expr}
    (hn : y.ioNeutral = true)
    (h1 : ConLeche.inferTypeIO mode env F d y = .ok tb)
    (h2 : ConLeche.whnf mode env F d tb = .ok (.forallE ty₂ bd₂))
    (h3 : ConLeche.isDefEqCore mode env F d ty₂ t = .ok true)
    (h4 : ConLeche.isDefEqCore mode env F (d + 1)
      (x.instantiate1 (.fvar d t)) (.app y (.fvar d t)) = .ok false) :
    ConLeche.etaCertFueled mode env F d t x y = .ok false := by
  have e1 : (ConLeche.pureFns mode env F).inferIO d y = .ok tb := h1
  have e2 : (ConLeche.pureFns mode env F).whnf d tb = .ok (.forallE ty₂ bd₂) := h2
  have e3 : (ConLeche.pureFns mode env F).defeq d ty₂ t = .ok true := h3
  have e4 : (ConLeche.pureFns mode env F).defeq (d + 1)
      (x.instantiate1 (.fvar d t)) (.app y (.fvar d t)) = .ok false := h4
  simp only [ConLeche.etaCertFueled, ConLeche.etaCert, hn, e1, e2, e3, e4, bind,
    Except.bind, Bool.not_true, Bool.false_eq_true, ite_false, ite_true]
  rfl

/-- con-leche: ConLeche/Kernel/Core.lean:461-484 etaCert — **the
certificate at the trusted mode**: the domains agree and the opened bodies
agree; no λ/η tax. -/
theorem etaCertFueled_trusted {F d : Nat} {t x y : Expr} {tb ty₂ bd₂ : Expr}
    (hn : y.ioNeutral = true)
    (h1 : ConLeche.inferTypeIO mode env F d y = .ok tb)
    (h2 : ConLeche.whnf mode env F d tb = .ok (.forallE ty₂ bd₂))
    (h3 : ConLeche.isDefEqCore mode env F d ty₂ t = .ok true)
    (h4 : ConLeche.isDefEqCore mode env F (d + 1)
      (x.instantiate1 (.fvar d t)) (.app y (.fvar d t)) = .ok true)
    (hv : mode.verifiedChecks = false) :
    ConLeche.etaCertFueled mode env F d t x y = .ok true := by
  have e1 : (ConLeche.pureFns mode env F).inferIO d y = .ok tb := h1
  have e2 : (ConLeche.pureFns mode env F).whnf d tb = .ok (.forallE ty₂ bd₂) := h2
  have e3 : (ConLeche.pureFns mode env F).defeq d ty₂ t = .ok true := h3
  have e4 : (ConLeche.pureFns mode env F).defeq (d + 1)
      (x.instantiate1 (.fvar d t)) (.app y (.fvar d t)) = .ok true := h4
  simp only [ConLeche.etaCertFueled, ConLeche.etaCert, hn, e1, e2, e3, e4, hv,
    bind, Except.bind, Bool.not_true, Bool.false_eq_true, ite_false, ite_true]
  rfl

/-- con-leche: ConLeche/Kernel/Core.lean:461-484 etaCert — **the
certificate at the verified mode**: the domains and the opened bodies agree,
and the verdict is the λ/η tax's — the λ body's FULL-grade type against the
∀'s codomain, both at the fresh variable (task #342, T2). -/
theorem etaCertFueled_tax {F d : Nat} {t x y : Expr} {tb ty₂ bd₂ t₁ : Expr}
    {r : Bool}
    (hn : y.ioNeutral = true)
    (h1 : ConLeche.inferTypeIO mode env F d y = .ok tb)
    (h2 : ConLeche.whnf mode env F d tb = .ok (.forallE ty₂ bd₂))
    (h3 : ConLeche.isDefEqCore mode env F d ty₂ t = .ok true)
    (h4 : ConLeche.isDefEqCore mode env F (d + 1)
      (x.instantiate1 (.fvar d t)) (.app y (.fvar d t)) = .ok true)
    (hv : mode.verifiedChecks = true)
    (h5 : ConLeche.inferTypeCore mode env F (d + 1)
      (x.instantiate1 (.fvar d t)) = .ok t₁)
    (h6 : ConLeche.isDefEqCore mode env F (d + 1) t₁
      (bd₂.instantiate1 (.fvar d t)) = .ok r) :
    ConLeche.etaCertFueled mode env F d t x y = .ok r := by
  have e1 : (ConLeche.pureFns mode env F).inferIO d y = .ok tb := h1
  have e2 : (ConLeche.pureFns mode env F).whnf d tb = .ok (.forallE ty₂ bd₂) := h2
  have e3 : (ConLeche.pureFns mode env F).defeq d ty₂ t = .ok true := h3
  have e4 : (ConLeche.pureFns mode env F).defeq (d + 1)
      (x.instantiate1 (.fvar d t)) (.app y (.fvar d t)) = .ok true := h4
  have e5 : (ConLeche.pureFns mode env F).infer (d + 1)
      (x.instantiate1 (.fvar d t)) = .ok t₁ := h5
  have e6 : (ConLeche.pureFns mode env F).defeq (d + 1) t₁
      (bd₂.instantiate1 (.fvar d t)) = .ok r := h6
  simp only [ConLeche.etaCertFueled, ConLeche.etaCert, hn, e1, e2, e3, e4, e5,
    e6, hv, bind, Except.bind, Bool.not_true, Bool.false_eq_true, ite_false,
    ite_true]
  cases r <;> rfl

/-! `etaCert_spec` **moved to `Bridge/Core/Walks/Spine.lean`** in round 4
and is CLOSED there, beside `instantiate1Fast_specE`, the one callee rule
whose answer shape it needs. -/

/-! ### `defEqList`, the tier's first `List` recursion

The two list inversions, the four pure-side step equations, the induction
itself, and the caller-facing statement derived from it.

**The induction runs at given denotations** (task #123; until then it ran
on the ∃/∀ shape of `defEqList_go`): the recursive call's lists are the
TAILS of the denotations the cons arm opens before the walk, so the induction
hypothesis goes into `vcgen`'s list instantiated at them, and `vcgen` has
nothing to guess.  (Finding 5.2's problem — at the recursive call the state
has moved, so `denoteEList s'.store as' = some ?xs` arrives with a
metavariable that `mvcgen` guessed as the whole list — is gone with it.)
`defEqList_go`, the ∃/∀ shape a caller whose state has moved needs, and
`defEqList_spec` are both stated over `defEqList_specA`. -/

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
    Except.bind, ite_true]
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

/-! ## Vocabulary candidates for Bridge/Grind.lean (task #123) -/

/-- con-leche: none — the empty handle list denotes the empty list. -/
@[bridge_grind =] theorem denoteEList_nil_eq (st : EStore) :
    Frontend.denoteEList st [] = some [] := rfl

/-- con-leche: none — a cons of handles, as an `Ans` atom about its
denotation (`Bridge/Grind.lean` §3): whatever it denotes is the cons of the
head's and the tail's denotations. -/
theorem denoteEList_cons_ans (st : EStore) (a : EIdx) (as : List EIdx) :
    Ans (fun xs => ∃ x xs', denoteE st a = some x ∧
      Frontend.denoteEList st as = some xs' ∧ xs = x :: xs')
      (Frontend.denoteEList st (a :: as)) :=
  fun _ h => denoteEList_cons_inv h
grind_pattern [bridge_grind] denoteEList_cons_ans => Frontend.denoteEList st (a :: as)

/-- con-leche: none — `denoteEList_ext` as an equation (`Bridge/Grind.lean`'s
`denote_le` at a handle list). -/
theorem denoteEList_le {st st' : EStore} {l : List EIdx} (hx : st ≤ st')
    (hd : Frontend.denoteEList st l ≠ none) :
    Frontend.denoteEList st' l = Frontend.denoteEList st l := by
  obtain ⟨xs, hxs⟩ := Option.ne_none_iff_exists'.mp hd
  rw [hxs]; exact denoteEList_ext hx _ _ hxs
grind_pattern [bridge_grind] denoteEList_le => st ≤ st', Frontend.denoteEList st l

/-! #### The four exits as `grind` lemmas (tasks #120, #121, #123)

The answer is stated about `defEqListOp`, con-leche's walk at a pair of
lists as ONE term: the lists are then subterms `grind` can match (inside the
`fun F => …` of the published statement they are not), and each exit below
is a lemma whose every variable occurs in its pattern.  The published
statements are the same propositions (`defEqListOp` unfolds to the `fun`). -/

/-- con-leche: ConLeche/Kernel/Core.lean:245-254 defEqList — con-leche's
walk at a pair of argument lists, as a fuelled run (an atom for `grind`). -/
def defEqListOp (mode : CheckMode) (env : Env) (d : Nat) (xs ys : List Expr) :
    Nat → CheckM Bool :=
  fun F => ConLeche.defEqListFueled mode env F d xs ys

/-- con-leche: ConLeche/Kernel/Core.lean:245-254 defEqList — the two empty
lists (at any fuel). -/
theorem defEqList_nil_nil_sim {d : Nat} :
    SimBOp (defEqListOp mode env d [] []) true :=
  ⟨0, rfl⟩
grind_pattern [bridge_grind] defEqList_nil_nil_sim => defEqListOp mode env d [] []

/-- con-leche: ConLeche/Kernel/Core.lean:245-254 defEqList — lists of
different lengths, the left one empty. -/
theorem defEqList_nil_cons_sim {d : Nat} {y : Expr} {ys : List Expr} :
    SimBOp (defEqListOp mode env d [] (y :: ys)) false :=
  ⟨0, rfl⟩
grind_pattern [bridge_grind] defEqList_nil_cons_sim => defEqListOp mode env d [] (y :: ys)

/-- con-leche: ConLeche/Kernel/Core.lean:245-254 defEqList — lists of
different lengths, the right one empty. -/
theorem defEqList_cons_nil_sim {d : Nat} {x : Expr} {xs : List Expr} :
    SimBOp (defEqListOp mode env d (x :: xs) []) false :=
  ⟨0, rfl⟩
grind_pattern [bridge_grind] defEqList_cons_nil_sim => defEqListOp mode env d (x :: xs) []

/-- con-leche: ConLeche/Kernel/Core.lean:245-254 defEqList — the cons/cons
arm, heads agreeing: the verdict is the tails', the head's and the tail's
fuels merged (`isDefEqCore_mono`, `defEqListFueled_mono`).  Both premises are
the callees' answer atoms. -/
theorem defEqList_cons_true_sim {d : Nat} {x y : Expr}
    {xs ys : List Expr} {r : Bool}
    (h : SimV (ConLeche.isDefEqCore mode env) d x y true)
    (ht : SimBOp (defEqListOp mode env d xs ys) r) :
    SimBOp (defEqListOp mode env d (x :: xs) (y :: ys)) r :=
  let ⟨F₁, h⟩ := h
  let ⟨F₂, ht⟩ := ht
  ⟨max F₁ F₂, defEqListFueled_cons_true
    (ConLeche.isDefEqCore_mono (Nat.le_max_left _ _) h)
    (defEqListFueled_mono (Nat.le_max_right _ _) ht)⟩
grind_pattern [bridge_grind] defEqList_cons_true_sim =>
  SimV (ConLeche.isDefEqCore mode env) d x y true, SimBOp (defEqListOp mode env d xs ys) r

/-- con-leche: ConLeche/Kernel/Core.lean:245-254 defEqList — the heads
disagree: so do the spines. -/
theorem defEqList_cons_false_sim {d : Nat} {x y : Expr} {xs ys : List Expr}
    (h : SimV (ConLeche.isDefEqCore mode env) d x y false) :
    SimBOp (defEqListOp mode env d (x :: xs) (y :: ys)) false :=
  let ⟨F, h⟩ := h
  ⟨F, defEqListFueled_cons_false h⟩
grind_pattern [bridge_grind] defEqList_cons_false_sim =>
  SimV (ConLeche.isDefEqCore mode env) d x y false, defEqListOp mode env d (x :: xs) (y :: ys)

/-- con-leche: ConLeche/Kernel/Core.lean:245-254 defEqList — **the
induction**, at given denotations (`defEqListOp`'s answer).  The recursive
call's lists are the tails of THESE denotations, so the induction hypothesis
goes into `vcgen`'s list instantiated at them (task #122's rule for a
parameter the program does not name). -/
theorem defEqList_specA {fuel : Nat} (hsim : KnotSpec mode env fe fuel) (d : Nat) :
    ∀ (as bs : List EIdx) (xs ys : List Expr) (s₀ : AState),
      CheckOK mode env fe s₀ →
      Frontend.denoteEList s₀.store as = some xs →
      Frontend.denoteEList s₀.store bs = some ys →
      (∀ x ∈ xs, Expr.WScoped d x) → (∀ y ∈ ys, Expr.WScoped d y) →
      ⦃fun s => s = s₀⦄
        ConRon.Arena.defEqList (coreKnot mode fe id fuel) fe d as bs
      ⦃fun r s' => CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
          s'.pins = s₀.pins ∧ SimBOp (defEqListOp mode env d xs ys) r; ⊤⦄ := by
  intro as
  induction as with
  | nil =>
    intro bs xs ys s₀ hok hda hdb _ _
    cases bs <;>
    sym only [bridge_grind] => vcgen [ConRon.Arena.defEqList.eq_def] <;> finish
  | cons a as' ih =>
    intro bs xs ys s₀ hok hda hdb hwx hwy
    cases bs with
    | nil =>
      clear ih hwx hwy
      sym only [bridge_grind] => vcgen [ConRon.Arena.defEqList.eq_def] <;> finish
    | cons b bs' =>
      -- the two lists' heads and tails, before the walk: the recursive call
      -- is at the tails' denotations
      obtain ⟨x, xs', hx, hxs', rfl⟩ := denoteEList_cons_inv hda
      obtain ⟨y, ys', hy, hys', rfl⟩ := denoteEList_cons_inv hdb
      have hwx0 : Expr.WScoped d x := hwx x (by simp)
      have hwy0 : Expr.WScoped d y := hwy y (by simp)
      -- the induction hypothesis at the tails, and nothing quantified left in
      -- the context for `grind` to instantiate
      have step := fun s₁ h1 h2 h3 =>
        ih bs' xs' ys' s₁ h1 h2 h3 (fun z hz => hwx z (by simp [hz]))
          (fun z hz => hwy z (by simp [hz]))
      clear ih hwx hwy
      sym only [bridge_grind] =>
        vcgen [ConRon.Arena.defEqList, hsim.defeq s₀ d a b x y hok hx hy hwx0 hwy0,
          step] <;> finish

/-- con-leche: ConLeche/Kernel/Core.lean:245-254 defEqList — **the
induction**, in the ∃/∀ shape a caller whose state has moved needs (see the
section note): `defEqList_specA` at the denotations it is handed. -/
theorem defEqList_go {fuel : Nat} (hsim : KnotSpec mode env fe fuel) (d : Nat) :
    ∀ (as bs : List EIdx) (s₀ : AState),
      CheckOK mode env fe s₀ →
      (∃ xs, Frontend.denoteEList s₀.store as = some xs ∧
        ∀ x ∈ xs, Expr.WScoped d x) →
      (∃ ys, Frontend.denoteEList s₀.store bs = some ys ∧
        ∀ y ∈ ys, Expr.WScoped d y) →
      ⦃fun s => s = s₀⦄
        ConRon.Arena.defEqList (coreKnot mode fe id fuel) fe d as bs
      ⦃fun r s' => CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
          s'.pins = s₀.pins ∧
          ∀ xs ys, Frontend.denoteEList s₀.store as = some xs →
            Frontend.denoteEList s₀.store bs = some ys →
            SimBOp (fun F => ConLeche.defEqListFueled mode env F d xs ys) r; ⊤⦄ := by
  intro as bs s₀ hok ⟨xs, hxs, hwx⟩ ⟨ys, hys, hwy⟩
  -- the answer over `defEqListOp` (the same proposition)
  show ⦃fun s => s = s₀⦄ ConRon.Arena.defEqList (coreKnot mode fe id fuel) fe d as bs
    ⦃fun r s' => CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧
        ∀ xs ys, Frontend.denoteEList s₀.store as = some xs →
          Frontend.denoteEList s₀.store bs = some ys →
          SimBOp (defEqListOp mode env d xs ys) r; ⊤⦄
  sym only [bridge_grind] =>
    vcgen [defEqList_specA hsim d as bs xs ys s₀ hok hxs hys hwx hwy] <;> finish

/-- con-leche: ConLeche/Kernel/Core.lean:245-254 defEqList — **THEOREM 1 for
`defEqList`**: pairwise definitional equality of two argument vectors.
**CLOSED** (round 3), at the published statement: `defEqList_specA`, whose
answer is the same proposition.

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
    ⦃fun s => s = s₀⦄
      ConRon.Arena.defEqList (coreKnot mode fe id fuel) fe d as bs
    ⦃fun r s' => CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧
        SimBOp (fun F => ConLeche.defEqListFueled mode env F d xs ys)
          r; ⊤⦄ :=
  defEqList_specA hsim d as bs xs ys s₀ hok hda hdb hwa hwb

/-! ## 6. The axiom census

The round's one CLOSED walk in this module, its induction, and the pure-side
step equations of the two walks whose arena side was then still open (closed
since). -/

section Census

#print axioms denoteEList_cons_inv
#print axioms defEqListFueled_cons_true
#print axioms defEqList_go
#print axioms defEqList_spec
#print axioms etaCertFueled_tax

end Census

end ConRon.Bridge.Core
