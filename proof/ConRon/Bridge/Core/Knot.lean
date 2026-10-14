/-
# `ConRon.Bridge.Core.Knot` — Theorem 1's statement for the checker core

DESIGN §8.2's **Theorem 1** at the knot: the six slots of the arena twin's
`coreKnot` at fuel `f` refine con-leche's own fueled entry points on
well-scoped inputs.  This module holds the STATEMENT (`KnotSpec`), the answer
relations it is phrased with, and the fuel-zero base case; the per-body arm
lemmas are `Bridge/Core/Arms/*.lean`, the memo-wrapper steps are
`Bridge/Core/Memo.lean`, and the induction that ties them is
`Bridge/Core/Induction.lean`.

## The shape, and where it comes from

con-leche built exactly this tower twice — once over its own arena
(`Verify/SimIKnot.lean`'s `SSimI`, quoted in
`_tmp/t97/conleche-arena-history.md` §2.3) and once over its cached tier
(`Verify/Cached/KnotC.lean`'s `SSimC`) — and the architecture is the same
three pieces both times: **one walk per twin body, five memo wrapper steps,
one knot induction**.  `KnotSpec` is `SSimC` with

| con-leche | here |
|---|---|
| `CSOK mode env s` | `CheckOK mode env fe s` (`Bridge/StateOK.lean`) |
| `RelC i e` (the cached tier's erasure) | `denoteE s₀.store i = some e` |
| `SimC mode env s₀ (RelEC d) c p` | the `Std.WP` triple `⦃fun s => s = s₀⦄ c ⦃fun r s' => …; ⊤⦄` |
| `(fueledFns mode env).whnfCore d e` | `∃ F, ConLeche.whnfCore mode env F d e = .ok v` |

The `FueledM` wrapper con-leche uses to carry fuel monotonicity through a
`bind` is not needed here, because the arena's side of every statement is a
`Std.WP` triple rather than a monadic value that has to be composed: the fuel
existential sits inside the answer relation and `vcgen` never touches it.

## Why the exception postcondition is `⊤`

Partial correctness (`⦃P⦄ c ⦃Q; ⊤⦄`), as everywhere in this library: a (B)
function may fail and Theorem 1 claims nothing then — con-leche's `SimAt`
(`Verify/SimI.lean:244`) has the same shape, and DESIGN §8.2's statement of
Theorem 1 is an implication out of `= .ok …`.

## Why the pure side is `∃ F` and not a fixed fuel

DESIGN §8.2: the bridge delivers `∃ F, ConLeche.checkDecl μ (fueledOps μ F) …`,
and `checkDeclsPure_sound_of` consumes it at any `F`.  The memo makes the
existential unavoidable rather than merely convenient: a cache row records an
answer the body computed at SOME earlier fuel, and re-deriving it at the
query's fuel is exactly what `CacheOK`'s depth-universal `∃ F, ∀ d` clause
(`Bridge/StateOK.lean`) exists to avoid.
-/
import ConRon.Bridge.Specs
import ConLeche.Verify.Knot
import ConLeche.Verify.Deep
import ConLeche.Verify.InferLemmas
import ConLeche.Verify.InferLeaves
import ConLeche.Verify.InferIOLeaves
import ConLeche.Verify.Abstract

namespace ConRon.Bridge.Core

set_option autoImplicit false
set_option experimental.vcgen true

open ConLeche ConRon.Arena ConRon.Bridge Std.WP
open scoped Lean.Order

/-! ## The answer relations

Two shapes, because the six slots have two result types: five answer a handle
and `defeq` answers a `Bool`.  Both are `Bridge/Rel.lean`'s `RelE`/`RelV`
pattern with the pure side's fuel existential and the well-scopedness of the
answer folded in — the two extra facts every CALLER of a slot needs and that
con-leche's `RelEC` carries for the same reason. -/

/-- con-leche: ConLeche/Verify/SimI.lean:250 RelE — **the handle-valued
answer relation of a core entry point**: the answer handle denotes a
well-scoped `v` that con-leche's own fueled operation produces at some fuel.

The `WScoped d v` conjunct is not decoration: the memo insert
(`Bridge/Core/Memo.lean`) needs it to restate the run in `CacheOK`'s
depth-universal form, and every caller that feeds an answer back into another
slot needs it as that call's precondition. -/
def SimE (op : Nat → Nat → Expr → CheckM Expr) (d : Nat) (e : Expr)
    (st' : EStore) (r : EIdx) : Prop :=
  ∃ v, denoteE st' r = some v ∧ Expr.WScoped d v ∧ ∃ F, op F d e = .ok v

/-- con-leche: ConLeche/Verify/SimI.lean:252 RelV — the `Bool`-valued answer
relation, for the `defeq` slot.  No store and no scope check: the answer names
no handle. -/
def SimV (op : Nat → Nat → Expr → Expr → CheckM Bool) (d : Nat)
    (a b : Expr) (x : Bool) : Prop :=
  ∃ F, op F d a b = .ok x

/-! ## The knot statement

The six slots of `ConRon.Arena.coreKnot mode fe id f` — which is
`Arena/Core.lean`'s `pureFnsA mode fe f`, the MEMOIZED knot (deviation 5 of
task #97c: the arena has one knot and the memo probes are inline in its
slots) — against con-leche's six fueled entry points of
`ConLeche/Kernel/TypeChecker.lean`. -/

/-- con-leche: ConLeche/Verify/Cached/DiscC1.lean:34 SSimC
con-leche: ConLeche/Verify/SimIKnot.lean:28 SSimI
**THEOREM 1 AT THE KNOT.**  At fuel `f`, every slot of the arena's memoized
knot refines con-leche's corresponding fueled entry point on inputs that
denote and are well scoped at the query's depth.

The record is what makes the arms writable: a body's theorem takes
`KnotSpec f` as a hypothesis and `hsim.whnfCore` goes into `vcgen`'s spec
list like any other `@[spec]` theorem (DESIGN `### Task #97s`,
rule 8 — "the record of knot hypotheses costs nothing"). -/
structure KnotSpec (mode : CheckMode) (env : Env) (fe : IFEnv) (f : Nat) :
    Prop where
  /-- Head normalization without delta, in either mode (`c` is the official
  kernel's `cheap_proj`; con-leche's claims generalize the same way). -/
  whnfCore : ∀ {c : Bool} (s₀ : AState) (d : Nat) (i : EIdx) (e : Expr),
    CheckOK mode env fe s₀ → denoteE s₀.store i = some e →
    Expr.WScoped d e →
    ⦃fun s => s = s₀⦄ (coreKnot mode fe id f).whnfCore c d i
    ⦃fun r s' => CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧
        SimE (fun F d e => ConLeche.whnfCore mode env F d e c) d e s'.store r; ⊤⦄
  /-- The full reduction loop. -/
  whnf : ∀ (s₀ : AState) (d : Nat) (i : EIdx) (e : Expr),
    CheckOK mode env fe s₀ → denoteE s₀.store i = some e →
    Expr.WScoped d e →
    ⦃fun s => s = s₀⦄ (coreKnot mode fe id f).whnf d i
    ⦃fun r s' => CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧
        SimE (ConLeche.whnf mode env) d e s'.store r; ⊤⦄
  /-- Full-grade type inference. -/
  infer : ∀ (s₀ : AState) (d : Nat) (i : EIdx) (e : Expr),
    CheckOK mode env fe s₀ → denoteE s₀.store i = some e →
    Expr.WScoped d e →
    ⦃fun s => s = s₀⦄ (coreKnot mode fe id f).infer d i
    ⦃fun r s' => CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧
        SimE (ConLeche.inferTypeCore mode env) d e s'.store r; ⊤⦄
  /-- Definitional equality, at the ORDERED pair the memo is keyed by. -/
  defeq : ∀ (s₀ : AState) (d : Nat) (i j : EIdx) (a b : Expr),
    CheckOK mode env fe s₀ → denoteE s₀.store i = some a →
    denoteE s₀.store j = some b →
    Expr.WScoped d a → Expr.WScoped d b →
    ⦃fun s => s = s₀⦄ (coreKnot mode fe id f).defeq d i j
    ⦃fun x s' => CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧
        SimV (ConLeche.isDefEqCore mode env) d a b x; ⊤⦄
  /-- The io grade (con-leche's task #170): its own body, its own table. -/
  inferIO : ∀ (s₀ : AState) (d : Nat) (i : EIdx) (e : Expr),
    CheckOK mode env fe s₀ → denoteE s₀.store i = some e →
    Expr.WScoped d e →
    ⦃fun s => s = s₀⦄ (coreKnot mode fe id f).inferIO d i
    ⦃fun r s' => CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧
        SimE (ConLeche.inferTypeIO mode env) d e s'.store r; ⊤⦄

/-! ## The base case

At fuel `0` every slot of `coreKnot` is `fail (.internal "fuel exhausted: …")`
and a `fail` never returns, so under the `⊤` exception postcondition the whole postcondition is
vacuous — con-leche's `ssimC_zero`, which is six `SimC.throw`s. -/

/-- con-leche: ConLeche/Verify/Cached/DiscC1.lean:70 ssimC_zero — the knot at
fuel `0` refines everything, because it returns nothing. -/
theorem knotSpec_zero (mode : CheckMode) (env : Env) (fe : IFEnv) :
    KnotSpec mode env fe 0 where
  whnfCore := fun _ _ _ _ _ _ _ => AM.triple_of_run fun _ _ _ _ h => nomatch h
  whnf := fun _ _ _ _ _ _ _ => AM.triple_of_run fun _ _ _ _ h => nomatch h
  infer := fun _ _ _ _ _ _ _ => AM.triple_of_run fun _ _ _ _ h => nomatch h
  defeq := fun _ _ _ _ _ _ _ _ _ _ _ => AM.triple_of_run fun _ _ _ _ h => nomatch h
  inferIO := fun _ _ _ _ _ _ _ => AM.triple_of_run fun _ _ _ _ h => nomatch h

/-! ## The slots in answer shape

`KnotSpec`'s fields take the subject's denotation as an explicit `(e : Expr)`
with a `denoteE s₀.store i = some e` hypothesis: the right shape for a caller
that holds the denotation, and the wrong one for a caller that reaches the
slot through another call, whose answer's denotation the program does not
name.  For those callers the slots are restated over the subject's
denotation TERM: the precondition `DenWS d (denoteE s₀.store i)` (it denotes,
in scope), the answer a named predicate on that term (`SlotAns`, or
`Bridge/Grind.lean`'s `PairAns` at two subjects) with its equation at
`some` — no `∃` to prove, no `∀` to instantiate, no `fun` for `grind`. -/

/-- con-leche: none — a precondition on an optional subject: it denotes, in
scope at `d`. -/
def DenWS (d : Nat) : Option Expr → Prop | some e => Expr.WScoped d e | none => False

/-- con-leche: none — `DenWS` at a denoting subject. -/
@[bridge_grind =] theorem DenWS.some_eq (d : Nat) (e : Expr) :
    DenWS d (some e) = Expr.WScoped d e := rfl

/-- con-leche: none — a `DenWS` precondition: the subject denotes.  Registered from
`Core/Walks/Stuck.lean` on (the walks that chain knot calls on an answer's
denotation); for `Core/Arms/Whnf.lean`, whose preconditions are `DenWS` too, it
costs 7 %. -/
theorem DenWS.isSome {d : Nat} {o : Option Expr} (h : DenWS d o) : o.isSome = true := by
  cases o with
  | none => exact h.elim
  | some _ => rfl

/-- con-leche: none — a knot slot's answer about an optional subject: at a
denoting subject `e`, the slot's `SimE` at `e`. -/
def SlotAns (op : Nat → Nat → Expr → CheckM Expr) (d : Nat) (st : EStore) (r : EIdx) :
    Option Expr → Prop
  | some e => SimE op d e st r
  | none => True

/-- con-leche: none — `SlotAns` at a denoting subject. -/
@[bridge_grind =] theorem SlotAns.some_eq (op : Nat → Nat → Expr → CheckM Expr) (d : Nat)
    (st : EStore) (r : EIdx) (e : Expr) : SlotAns op d st r (some e) = SimE op d e st r :=
  rfl

/-- con-leche: none — a triple whose answer is a `Bool` about the
denotations of two subjects, restated over the denotation terms
(`PairAns`): the subjects' denotations are terms, not parameters. -/
theorem pairAns_of_spec {mode : CheckMode} {env : Env} {fe : IFEnv} {m : AM Bool}
    {P : Expr → Expr → Bool → Prop} {s₀ : AState} {a b : EIdx} {d : Nat}
    (hda : DenWS d (denoteE s₀.store a)) (hdb : DenWS d (denoteE s₀.store b))
    (h : ∀ x y, denoteE s₀.store a = some x → denoteE s₀.store b = some y →
      Expr.WScoped d x → Expr.WScoped d y →
      ⦃fun s => s = s₀⦄ m
      ⦃fun r s' => CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
          s'.pins = s₀.pins ∧ P x y r; ⊤⦄) :
    ⦃fun s => s = s₀⦄ m
    ⦃fun r s' => CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧ PairAns P (denoteE s₀.store a) (denoteE s₀.store b) r; ⊤⦄ := by
  cases ha : denoteE s₀.store a with
  | none => rw [ha] at hda; exact hda.elim
  | some x =>
  cases hb : denoteE s₀.store b with
  | none => rw [hb] at hdb; exact hdb.elim
  | some y =>
  rw [ha] at hda; rw [hb] at hdb
  exact h x y ha hb hda hdb

/-- con-leche: ConLeche/Verify/SimIKnot.lean:28 SSimI — the `whnf` slot in
answer shape. -/
theorem KnotSpec.whnfS {mode : CheckMode} {env : Env} {fe : IFEnv} {f : Nat}
    (hsim : KnotSpec mode env fe f) (s₀ : AState) (d : Nat) (i : EIdx)
    (hok : CheckOK mode env fe s₀) (hw : DenWS d (denoteE s₀.store i)) :
    ⦃fun s => s = s₀⦄ (coreKnot mode fe id f).whnf d i
    ⦃fun r s' => CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧ s'.pins = s₀.pins ∧
        SlotAns (ConLeche.whnf mode env) d s'.store r (denoteE s₀.store i); ⊤⦄ := by
  cases hd : denoteE s₀.store i with
  | none => rw [hd] at hw; exact hw.elim
  | some e => rw [hd] at hw; exact hsim.whnf s₀ d i e hok hd hw

/-- con-leche: ConLeche/Verify/SimIKnot.lean:28 SSimI — the io-grade
inference slot in answer shape. -/
theorem KnotSpec.inferIOS {mode : CheckMode} {env : Env} {fe : IFEnv} {f : Nat}
    (hsim : KnotSpec mode env fe f) (s₀ : AState) (d : Nat) (i : EIdx)
    (hok : CheckOK mode env fe s₀) (hw : DenWS d (denoteE s₀.store i)) :
    ⦃fun s => s = s₀⦄ (coreKnot mode fe id f).inferIO d i
    ⦃fun r s' => CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧ s'.pins = s₀.pins ∧
        SlotAns (ConLeche.inferTypeIO mode env) d s'.store r (denoteE s₀.store i); ⊤⦄ := by
  cases hd : denoteE s₀.store i with
  | none => rw [hd] at hw; exact hw.elim
  | some e => rw [hd] at hw; exact hsim.inferIO s₀ d i e hok hd hw

/-- con-leche: ConLeche/Verify/SimIKnot.lean:28 SSimI — the `defeq` slot in
answer shape (`PairAns` of `SimV`). -/
theorem KnotSpec.defeqS {mode : CheckMode} {env : Env} {fe : IFEnv} {f : Nat}
    (hsim : KnotSpec mode env fe f) (s₀ : AState) (d : Nat) (i j : EIdx)
    (hok : CheckOK mode env fe s₀)
    (hi : DenWS d (denoteE s₀.store i)) (hj : DenWS d (denoteE s₀.store j)) :
    ⦃fun s => s = s₀⦄ (coreKnot mode fe id f).defeq d i j
    ⦃fun r s' => CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧ s'.pins = s₀.pins ∧
        PairAns (SimV (ConLeche.isDefEqCore mode env) d) (denoteE s₀.store i)
          (denoteE s₀.store j) r; ⊤⦄ :=
  pairAns_of_spec hi hj fun a b ha hb hwa hwb => hsim.defeq s₀ d i j a b hok ha hb hwa hwb

/-! ## The body statement, once

Every one of the six body theorems has the same shape — the body at a knot
record `r` that satisfies `KnotSpec … f`, against con-leche's body at the
fueled record.  Rather than restate it six times with the pure comparand
changed, `BodySpec` fixes the four things that vary: the twin's body, the
pure operation one fuel level up, and the two result shapes.

`Arms/*.lean` state their body theorem as `BodySpec …`, `Memo.lean` consumes
it, and `Induction.lean` never sees a body at all. -/

/-- con-leche: ConLeche/Verify/Cached/DiscC4.lean whnfCoreBodyC_sim — the
common shape of the five handle-valued body theorems: at a knot record one
fuel level down, the twin's body refines con-leche's fueled entry point at
`f + 1`.

The pure comparand is the fueled ENTRY (`ConLeche.whnfCore mode env (F + 1)`)
rather than con-leche's body applied to `fueledFns`, because
`Verify/Knot.lean`'s `whnfCore_succ` identifies the two and the entry is what
`CacheOK` is stated at. -/
def BodySpec (mode : CheckMode) (env : Env) (fe : IFEnv)
    (body : Nat → EIdx → AM EIdx) (op : Nat → Nat → Expr → CheckM Expr) :
    Prop :=
  ∀ (s₀ : AState) (d : Nat) (i : EIdx) (e : Expr),
    CheckOK mode env fe s₀ → denoteE s₀.store i = some e →
    Expr.WScoped d e →
    ⦃fun s => s = s₀⦄ body d i
    ⦃fun r s' => CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧
        SimE op d e s'.store r; ⊤⦄

/-- con-leche: ConLeche/Verify/Cached/DiscC6.lean defeqBodyC_sim — the same
at the `Bool`-valued body, which takes two subjects. -/
def BodySpecV (mode : CheckMode) (env : Env) (fe : IFEnv)
    (body : Nat → EIdx → EIdx → AM Bool)
    (op : Nat → Nat → Expr → Expr → CheckM Bool) : Prop :=
  ∀ (s₀ : AState) (d : Nat) (i j : EIdx) (a b : Expr),
    CheckOK mode env fe s₀ → denoteE s₀.store i = some a →
    denoteE s₀.store j = some b →
    Expr.WScoped d a → Expr.WScoped d b →
    ⦃fun s => s = s₀⦄ body d i j
    ⦃fun x s' => CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧
        SimV op d a b x; ⊤⦄

end ConRon.Bridge.Core
