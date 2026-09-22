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
| `SimC mode env s₀ (RelEC d) c p` | the `Std.Do` triple `⦃s = s₀⦄ c ⦃⇓? r s' => …⦄` |
| `(fueledFns mode env).whnfCore d e` | `∃ F, ConLeche.whnfCore mode env F d e = .ok v` |

The `FueledM` wrapper con-leche uses to carry fuel monotonicity through a
`bind` is not needed here, because the arena's side of every statement is a
`Std.Do` triple rather than a monadic value that has to be composed: the fuel
existential sits inside the answer relation and `mvcgen` never touches it.

## Why `⇓?`

Partial correctness, as everywhere in this library: a (B) function may fail
and Theorem 1 claims nothing then — con-leche's `SimAt`
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
set_option mvcgen.warning false

open ConLeche ConRon.Arena ConRon.Bridge Std.Do

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

/-! ### The eliminators

`Bridge/Rel.lean`'s five, in the two shapes above.  `SimV` needs none but
`.mk`: it mentions no store, so nothing transports. -/

/-- con-leche: none — the answer survives an arena extension. -/
theorem SimE.ext {op : Nat → Nat → Expr → CheckM Expr} {d : Nat} {e : Expr}
    {st st' : EStore} {r : EIdx} (h : SimE op d e st r) (hx : Ext st st') :
    SimE op d e st' r := by
  obtain ⟨v, hv, hw, F, hF⟩ := h
  exact ⟨v, denote_ext hv hx, hw, F, hF⟩

/-- con-leche: none — the answer's denotation, forgetting the pure run. -/
theorem SimE.denote {op : Nat → Nat → Expr → CheckM Expr} {d : Nat}
    {e : Expr} {st : EStore} {r : EIdx} (h : SimE op d e st r) :
    (denoteE st r).isSome = true := by
  obtain ⟨v, hv, _, _, _⟩ := h
  rw [hv]; rfl

/-- con-leche: none — the answer's well-scopedness, which is what a caller
that feeds it into a second slot needs. -/
theorem SimE.wscoped {op : Nat → Nat → Expr → CheckM Expr} {d : Nat}
    {e v : Expr} {st : EStore} {r : EIdx} (h : SimE op d e st r)
    (hv : denoteE st r = some v) : Expr.WScoped d v := by
  obtain ⟨v', hv', hw, _, _⟩ := h
  rw [hv] at hv'
  obtain rfl := Option.some.inj hv'
  exact hw

/-- con-leche: none — **the `CacheOK` shape from an answer**: a slot's answer
at a subject that is well scoped at the query's depth is a row of the entry
cache, once the run has been made depth-universal.  The depth-invariance
theorem is the caller's (`Bridge/Core/Memo.lean` supplies con-leche's six),
which is why it is a hypothesis here. -/
theorem SimE.toCache {op : Nat → Nat → Expr → CheckM Expr} {d : Nat}
    {e v : Expr} {st : EStore} {r : EIdx} (h : SimE op d e st r)
    (hinv : ∀ (F d' : Nat), Expr.wscopedB d' e = true →
      op F d' e = op F d e) (hv : denoteE st r = some v) :
    ∃ F, ∀ d', Expr.wscopedB d' e = true → op F d' e = .ok v := by
  obtain ⟨v', hv', _, F, hF⟩ := h
  rw [hv] at hv'
  obtain rfl := Option.some.inj hv'
  exact ⟨F, fun d' hd' => by rw [hinv F d' hd']; exact hF⟩

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
`KnotSpec f` as a hypothesis and `hsim.whnfCore` goes into `mvcgen`'s spec
list like any other `@[spec]` theorem (task #97s round 2's rule 8 — "the
record of knot hypotheses costs nothing"). -/
structure KnotSpec (mode : CheckMode) (env : Env) (fe : IFEnv) (f : Nat) :
    Prop where
  /-- Head normalization without delta. -/
  whnfCore : ∀ (s₀ : AState) (d : Nat) (i : EIdx) (e : Expr),
    CheckOK mode env fe s₀ → denoteE s₀.store i = some e →
    Expr.WScoped d e →
    ⦃fun s => ⌜s = s₀⌝⦄ (coreKnot mode fe id f).whnfCore d i
    ⦃⇓? r s' => ⌜CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧
        SimE (ConLeche.whnfCore mode env) d e s'.store r⌝⦄
  /-- The full reduction loop. -/
  whnf : ∀ (s₀ : AState) (d : Nat) (i : EIdx) (e : Expr),
    CheckOK mode env fe s₀ → denoteE s₀.store i = some e →
    Expr.WScoped d e →
    ⦃fun s => ⌜s = s₀⌝⦄ (coreKnot mode fe id f).whnf d i
    ⦃⇓? r s' => ⌜CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧
        SimE (ConLeche.whnf mode env) d e s'.store r⌝⦄
  /-- Full-grade type inference. -/
  infer : ∀ (s₀ : AState) (d : Nat) (i : EIdx) (e : Expr),
    CheckOK mode env fe s₀ → denoteE s₀.store i = some e →
    Expr.WScoped d e →
    ⦃fun s => ⌜s = s₀⌝⦄ (coreKnot mode fe id f).infer d i
    ⦃⇓? r s' => ⌜CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧
        SimE (ConLeche.inferTypeCore mode env) d e s'.store r⌝⦄
  /-- Definitional equality, at the ORDERED pair the memo is keyed by. -/
  defeq : ∀ (s₀ : AState) (d : Nat) (i j : EIdx) (a b : Expr),
    CheckOK mode env fe s₀ → denoteE s₀.store i = some a →
    denoteE s₀.store j = some b →
    Expr.WScoped d a → Expr.WScoped d b →
    ⦃fun s => ⌜s = s₀⌝⦄ (coreKnot mode fe id f).defeq d i j
    ⦃⇓? x s' => ⌜CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧
        SimV (ConLeche.isDefEqCore mode env) d a b x⌝⦄
  /-- The annotation pass. -/
  annotate : ∀ (s₀ : AState) (d : Nat) (i : EIdx) (e : Expr),
    CheckOK mode env fe s₀ → denoteE s₀.store i = some e →
    Expr.WScoped d e →
    ⦃fun s => ⌜s = s₀⌝⦄ (coreKnot mode fe id f).annotate d i
    ⦃⇓? r s' => ⌜CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧
        SimE (ConLeche.annotateCore mode env) d e s'.store r⌝⦄
  /-- The io grade (con-leche's task #170): its own body, its own table. -/
  inferIO : ∀ (s₀ : AState) (d : Nat) (i : EIdx) (e : Expr),
    CheckOK mode env fe s₀ → denoteE s₀.store i = some e →
    Expr.WScoped d e →
    ⦃fun s => ⌜s = s₀⌝⦄ (coreKnot mode fe id f).inferIO d i
    ⦃⇓? r s' => ⌜CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧
        SimE (ConLeche.inferTypeIO mode env) d e s'.store r⌝⦄

/-! ## The base case

At fuel `0` every slot of `coreKnot` is `fail (.internal "fuel exhausted: …")`
and a `fail` never returns, so under `⇓?` the whole postcondition is
vacuous — con-leche's `ssimC_zero`, which is six `SimC.throw`s. -/

/-- con-leche: ConLeche/Verify/Cached/DiscC1.lean:70 ssimC_zero — the knot at
fuel `0` refines everything, because it returns nothing. -/
theorem knotSpec_zero (mode : CheckMode) (env : Env) (fe : IFEnv) :
    KnotSpec mode env fe 0 where
  whnfCore := fun _ _ _ _ _ _ _ => by intro _ _; trivial
  whnf := fun _ _ _ _ _ _ _ => by intro _ _; trivial
  infer := fun _ _ _ _ _ _ _ => by intro _ _; trivial
  defeq := fun _ _ _ _ _ _ _ _ _ _ _ => by intro _ _; trivial
  annotate := fun _ _ _ _ _ _ _ => by intro _ _; trivial
  inferIO := fun _ _ _ _ _ _ _ => by intro _ _; trivial

/-! ## The six slots in ANSWER shape (task #97-P3-Core round 3)

`KnotSpec`'s six fields take the subject's denotation as an explicit
`(e : Expr)` argument with a `denoteE s₀.store i = some e` hypothesis.  That
is the right shape for a caller that already holds the denotation, and it is
the WRONG shape for a caller that reaches the slot through another call —
task #97-P3-Core-2's finding 5.2, which re-shaped `reduceNat_spec` and
`unfoldDefinition_spec` for exactly this reason:

> `mvcgen` must guess `e` when it applies the spec; it guesses the only
> `Expr` in scope — the *original* subject — and the side goal it leaves is
> false.

`isPropType` is the smallest walk that meets it (`r.inferIO d ty'` on
`r.annotate`'s ANSWER), and every remaining walk of
`Bridge/Core/Walks/Owed.lean` that chains two knot calls meets it too.  So
rather than re-derive the existential/universal form at each site, the six
slots are restated here, once: **the denotation goes IN as an existential
(which names no metavariable) and OUT as a universal**.  Each is four lines
over its own field, and `denoteE`'s functionality at one handle is the whole
argument.

The primed forms do not replace the unprimed ones — a caller that holds the
denotation should keep using the field, which leaves it one fewer `∀` to
instantiate. -/

/-- con-leche: ConLeche/Verify/Cached/DiscC1.lean:70 ssimC_zero — the
whnfCore slot in ANSWER shape (see the section note). -/
theorem KnotSpec.whnfCore' {mode : CheckMode} {env : Env} {fe : IFEnv} {f : Nat}
    (hsim : KnotSpec mode env fe f)
    (s₀ : AState) (d : Nat) (i : EIdx) (hok : CheckOK mode env fe s₀)
    (hdw : ∃ e, denoteE s₀.store i = some e ∧ Expr.WScoped d e) :
    ⦃fun s => ⌜s = s₀⌝⦄ (coreKnot mode fe id f).whnfCore d i
    ⦃⇓? r s' => ⌜CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧
        ∀ e, denoteE s₀.store i = some e →
          SimE (ConLeche.whnfCore mode env) d e s'.store r⌝⦄ := by
  obtain ⟨e₀, hd, hwf⟩ := hdw
  have hb := hsim.whnfCore s₀ d i e₀ hok hd hwf
  mvcgen [hb]
  intro h1 h2 h3 h4
  refine ⟨h1, h2, h3, fun e he => ?_⟩
  rw [hd] at he; obtain rfl := (Option.some.inj he).symm; exact h4

/-- con-leche: ConLeche/Verify/Cached/DiscC1.lean:70 ssimC_zero — the
whnf slot in ANSWER shape. -/
theorem KnotSpec.whnf' {mode : CheckMode} {env : Env} {fe : IFEnv} {f : Nat}
    (hsim : KnotSpec mode env fe f)
    (s₀ : AState) (d : Nat) (i : EIdx) (hok : CheckOK mode env fe s₀)
    (hdw : ∃ e, denoteE s₀.store i = some e ∧ Expr.WScoped d e) :
    ⦃fun s => ⌜s = s₀⌝⦄ (coreKnot mode fe id f).whnf d i
    ⦃⇓? r s' => ⌜CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧
        ∀ e, denoteE s₀.store i = some e →
          SimE (ConLeche.whnf mode env) d e s'.store r⌝⦄ := by
  obtain ⟨e₀, hd, hwf⟩ := hdw
  have hb := hsim.whnf s₀ d i e₀ hok hd hwf
  mvcgen [hb]
  intro h1 h2 h3 h4
  refine ⟨h1, h2, h3, fun e he => ?_⟩
  rw [hd] at he; obtain rfl := (Option.some.inj he).symm; exact h4

/-- con-leche: ConLeche/Verify/Cached/DiscC1.lean:70 ssimC_zero — the
full-grade inference slot in ANSWER shape. -/
theorem KnotSpec.infer' {mode : CheckMode} {env : Env} {fe : IFEnv} {f : Nat}
    (hsim : KnotSpec mode env fe f)
    (s₀ : AState) (d : Nat) (i : EIdx) (hok : CheckOK mode env fe s₀)
    (hdw : ∃ e, denoteE s₀.store i = some e ∧ Expr.WScoped d e) :
    ⦃fun s => ⌜s = s₀⌝⦄ (coreKnot mode fe id f).infer d i
    ⦃⇓? r s' => ⌜CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧
        ∀ e, denoteE s₀.store i = some e →
          SimE (ConLeche.inferTypeCore mode env) d e s'.store r⌝⦄ := by
  obtain ⟨e₀, hd, hwf⟩ := hdw
  have hb := hsim.infer s₀ d i e₀ hok hd hwf
  mvcgen [hb]
  intro h1 h2 h3 h4
  refine ⟨h1, h2, h3, fun e he => ?_⟩
  rw [hd] at he; obtain rfl := (Option.some.inj he).symm; exact h4

/-- con-leche: ConLeche/Verify/Cached/DiscC1.lean:70 ssimC_zero — the
annotation slot in ANSWER shape. -/
theorem KnotSpec.annotate' {mode : CheckMode} {env : Env} {fe : IFEnv} {f : Nat}
    (hsim : KnotSpec mode env fe f)
    (s₀ : AState) (d : Nat) (i : EIdx) (hok : CheckOK mode env fe s₀)
    (hdw : ∃ e, denoteE s₀.store i = some e ∧ Expr.WScoped d e) :
    ⦃fun s => ⌜s = s₀⌝⦄ (coreKnot mode fe id f).annotate d i
    ⦃⇓? r s' => ⌜CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧
        ∀ e, denoteE s₀.store i = some e →
          SimE (ConLeche.annotateCore mode env) d e s'.store r⌝⦄ := by
  obtain ⟨e₀, hd, hwf⟩ := hdw
  have hb := hsim.annotate s₀ d i e₀ hok hd hwf
  mvcgen [hb]
  intro h1 h2 h3 h4
  refine ⟨h1, h2, h3, fun e he => ?_⟩
  rw [hd] at he; obtain rfl := (Option.some.inj he).symm; exact h4

/-- con-leche: ConLeche/Verify/Cached/DiscC1.lean:70 ssimC_zero — the io
grade in ANSWER shape.  This is the one `isPropType` needs. -/
theorem KnotSpec.inferIO' {mode : CheckMode} {env : Env} {fe : IFEnv} {f : Nat}
    (hsim : KnotSpec mode env fe f)
    (s₀ : AState) (d : Nat) (i : EIdx) (hok : CheckOK mode env fe s₀)
    (hdw : ∃ e, denoteE s₀.store i = some e ∧ Expr.WScoped d e) :
    ⦃fun s => ⌜s = s₀⌝⦄ (coreKnot mode fe id f).inferIO d i
    ⦃⇓? r s' => ⌜CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧
        ∀ e, denoteE s₀.store i = some e →
          SimE (ConLeche.inferTypeIO mode env) d e s'.store r⌝⦄ := by
  obtain ⟨e₀, hd, hwf⟩ := hdw
  have hb := hsim.inferIO s₀ d i e₀ hok hd hwf
  mvcgen [hb]
  intro h1 h2 h3 h4
  refine ⟨h1, h2, h3, fun e he => ?_⟩
  rw [hd] at he; obtain rfl := (Option.some.inj he).symm; exact h4

/-- con-leche: ConLeche/Verify/Cached/DiscC1.lean:70 ssimC_zero — the
defeq slot in ANSWER shape, at BOTH subjects. -/
theorem KnotSpec.defeq' {mode : CheckMode} {env : Env} {fe : IFEnv} {f : Nat}
    (hsim : KnotSpec mode env fe f)
    (s₀ : AState) (d : Nat) (i j : EIdx) (hok : CheckOK mode env fe s₀)
    (hda : ∃ a, denoteE s₀.store i = some a ∧ Expr.WScoped d a)
    (hdb : ∃ b, denoteE s₀.store j = some b ∧ Expr.WScoped d b) :
    ⦃fun s => ⌜s = s₀⌝⦄ (coreKnot mode fe id f).defeq d i j
    ⦃⇓? x s' => ⌜CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧
        ∀ a b, denoteE s₀.store i = some a → denoteE s₀.store j = some b →
          SimV (ConLeche.isDefEqCore mode env) d a b x⌝⦄ := by
  obtain ⟨a₀, hda1, hda2⟩ := hda
  obtain ⟨b₀, hdb1, hdb2⟩ := hdb
  have hb := hsim.defeq s₀ d i j a₀ b₀ hok hda1 hdb1 hda2 hdb2
  mvcgen [hb]
  intro h1 h2 h3 h4
  refine ⟨h1, h2, h3, fun a b ha hbb => ?_⟩
  rw [hda1] at ha; rw [hdb1] at hbb
  obtain rfl := (Option.some.inj ha).symm
  obtain rfl := (Option.some.inj hbb).symm
  exact h4

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
    ⦃fun s => ⌜s = s₀⌝⦄ body d i
    ⦃⇓? r s' => ⌜CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧
        SimE op d e s'.store r⌝⦄

/-- con-leche: ConLeche/Verify/Cached/DiscC6.lean defeqBodyC_sim — the same
at the `Bool`-valued body, which takes two subjects. -/
def BodySpecV (mode : CheckMode) (env : Env) (fe : IFEnv)
    (body : Nat → EIdx → EIdx → AM Bool)
    (op : Nat → Nat → Expr → Expr → CheckM Bool) : Prop :=
  ∀ (s₀ : AState) (d : Nat) (i j : EIdx) (a b : Expr),
    CheckOK mode env fe s₀ → denoteE s₀.store i = some a →
    denoteE s₀.store j = some b →
    Expr.WScoped d a → Expr.WScoped d b →
    ⦃fun s => ⌜s = s₀⌝⦄ body d i j
    ⦃⇓? x s' => ⌜CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧
        SimV op d a b x⌝⦄

end ConRon.Bridge.Core
