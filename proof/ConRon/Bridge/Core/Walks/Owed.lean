/-
# `ConRon.Bridge.Core.Walks.Owed` — `etaCert`'s pure side and `defEqList`

The `Arena/Core.lean` walks that are not knot slots each have a
`BodySpec`-shaped Theorem 1 statement, with the con-leche function it refines
named through `Verify/Knot.lean`'s own `…Fueled` abbreviation.  This module
holds two of them:

* `etaCert`'s six pure-side step equations (its arena-side theorem,
  `etaCert_spec`, is in `Walks/Spine.lean`, beside `instantiate1Fast_specE`);
* `defEqList`, in full: the list inversions, the step equations, the
  induction `defEqList_specA` and the caller-facing `defEqList_go` /
  `defEqList_spec` (§3).

The others live in the module whose imports they need:

| walk | module |
|---|---|
| `lvlEq?`/`lvlsEq?`, the readbacks | `Walks/{Cached,Frame}.lean` |
| `ensureSort` | `Core/EnsureSort.lean` |
| `isBoolTrue` | `Walks/Guards.lean` |
| `unfoldableHead`, `unfoldDefinition`, `headHint`, `sameConstHeads`, `defeqSpine`, `etaCert` | `Walks/Spine.lean` |
| `reduceNat` | `Walks/Nat.lean` |
| `projCertAt` | `Walks/Proj.lean` |
| `projLitToCtor` | `Walks/ProjLit.lean` |
| `propIrrel`, `annotPwPi`, `annotPwLam` | `Walks/PropRead.lean` |
| `stuckIrrel` | `Walks/Stuck.lean` |
| `iotaRec` | `Walks/Iota.lean` |

## 0. The subject's denotation: an existential in, a universal out

A walk's subject may be another walk's ANSWER — `whnfStep` runs `r.whnfCore`
first and hands `reduceNat` the REDUCT, whose denotation is not known until
the first call's postcondition is in hand.  A statement that took the
subject's denotation as an explicit `(x : Expr)` argument with a
`denoteE s₀.store e = some x` hypothesis would make the verification
condition generator guess `x` (it leaves it a metavariable and an `Expr`
goal of its own).  So the denotation goes into the hypothesis as an
**existential** (`∃ x, denoteE s₀.store e = some x ∧ Expr.WScoped d x`,
which names no metavariable) and out of the postcondition as a
**universal** (`∀ x, denoteE s₀.store e = some x → …`), the shape
`Bridge/Core/Arms/Whnf.lean`'s `whnfLoop_spec` needs at every iteration.
The rule: *a walk whose subject is another walk's ANSWER must not take that
answer's denotation as an explicit argument.*

## 1. The three answer shapes, and which walk has which

`Bridge/Core/Walks/Spec.lean`'s relations, at the pure call with its fuel
abstracted:

| shape | walks |
|---|---|
| `SimOOp` — an `Option EIdx` answer | `reduceNat`, `iotaRec` |
| `SimEOp` — an `EIdx` answer | `projLitToCtor` |
| `SimBOp` — a `Bool` answer | `projCertAt`, `propIrrel`, `stuckIrrel`, `etaCert`, `defeqSpine`, `defEqList` |
| an EQUATION — the pure side takes no fuel | `unfoldDefinition`, `unfoldableHead`, `sameConstHeads`, `headHint`, `isBoolTrue` |

The last row refines con-leche functions that are not in `CheckM` at all
(`unfoldDefinition env e : Option Expr`, `unfoldableHead env e : Bool`,
`sameConstHeads a b : Bool`, `headHint env e : ReducibilityHint`,
`Expr.isBoolTrue e : Bool`), so there is no `∃ F` and no fuel bookkeeping:
the conclusion is an equation between the arena's answer and con-leche's.
-/
import ConRon.Bridge.Core.Walks.Spec
import ConRon.Bridge.Core.Walks.Mono
import ConRon.Bridge.Grind

namespace ConRon.Bridge.Core

set_option autoImplicit false
set_option experimental.vcgen true
set_option maxHeartbeats 1000000

open ConLeche ConRon.Arena ConRon.Bridge Std.WP
open scoped Lean.Order

variable {mode : CheckMode} {env : Env} {fe : IFEnv}

/-! ## 2. `etaCert`'s pure side

The six step equations below are con-leche's `etaCert` at its six exits,
each one `simp only` over the knot record's slot equations.  The arena-side
theorem, `etaCert_spec`, is in `Walks/Spine.lean`, beside
`instantiate1Fast_specE`: `Bridge/ExprOps/Inst1.lean`'s
`instantiate1Fast_spec` takes the SUBSTITUTED VALUE's denotation as an
explicit `(ve : Expr)` argument, and `etaCert` substitutes a free variable
it has just INTERNED, so it needs the §0 answer shape of that rule. -/

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
∀'s codomain, both at the fresh variable (con-leche's task #342, T2). -/
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

/-! ## 3. `defEqList`, a `List` recursion

The two list inversions, the four pure-side step equations, the induction
itself, and the caller-facing statement derived from it.

**The induction runs at given denotations**: the recursive call's lists are
the TAILS of the denotations the cons arm opens before the walk, so the
induction hypothesis goes into `vcgen`'s list instantiated at them, and
`vcgen` has nothing to guess.
`defEqList_go`, the ∃/∀ shape a caller whose state has moved needs, and
`defEqList_spec` are both stated over `defEqList_specA`. -/

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

/-! #### The four exits as `grind` lemmas

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
goes into `vcgen`'s list instantiated at them (rule for a
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
It is `defEqList_specA`, whose answer is the same proposition; the cons
arm's fuel is the `max F₁ F₂` of the head's and the tail's, merged by
con-leche's own `isDefEqCore_mono` and `Walks/Mono.lean`'s
`defEqListFueled_mono`. -/
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

/-! ## 4. The axiom census

`defEqList`'s walk, its induction and a step equation, and `etaCert`'s
pure-side step equation. -/

section Census

#print axioms denoteEList_cons_inv
#print axioms defEqListFueled_cons_true
#print axioms defEqList_go
#print axioms defEqList_spec
#print axioms etaCertFueled_tax

end Census

end ConRon.Bridge.Core
