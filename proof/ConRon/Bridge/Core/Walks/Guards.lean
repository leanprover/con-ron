/-
# `ConRon.Bridge.Core.Walks.Guards` — the `defeq` body's cheap tests

`Arena/Core.lean`'s definitional-equality block (`defeqBody` and its
lazy-delta steps) runs scalar tests — `isBoolTrue`, `sameConstHeads`,
`unfoldableHead` — that read the handle word or one `view` and nothing else.
They are the cheapest walks of the whole non-slot tier, because con-leche's comparand is a
plain function (no `CheckM`, no fuel), so the conclusion is an EQUATION
between the arena's answer and con-leche's and there is no `∃ F` to carry.

This module holds `isBoolTrue_spec`: five verification conditions, no
`ExprOps` callee rule, no new denotation.  Its two siblings that need
`getAppFn` (`sameConstHeads_spec`, `unfoldableHead_spec`) are in
`Spine.lean`, over the `ExprOps` tier.

## What it cashes

DESIGN §8.3's **"index inequality IS structural inequality"**, twice in one
walk: the twin tests `us != emptyLevels` where con-leche matches `.const c []`,
and `c == boolTrueName`'s pin handle where con-leche compares `Name`s.
`denoteLs_inj` and `denoteN_inj` (`Arena/WFProofs.lean`) are exactly what
turns each handle test into its structural one — and `PinsOK` is what says
the pin handle denotes what it is named for.  `pinNames_boolTrue` below is
the one-line bridge from `Bridge/Specs.lean`'s quantified `pinAt_spec` to the
named slot.
-/
import ConRon.Bridge.Core.Walks.Spec
import ConRon.Bridge.Grind

namespace ConRon.Bridge.Core

set_option autoImplicit false
set_option experimental.vcgen true
set_option maxHeartbeats 1000000

open ConLeche ConRon.Arena ConRon.Bridge Std.WP
open scoped Lean.Order

variable {mode : CheckMode} {env : Env} {fe : IFEnv}

/-- con-leche: ConLeche/Kernel/Basis/Names.lean:109-116 reservedBasisNames —
the `PIN_BOOL_TRUE` slot of `pinNames` is `Bool.true`'s name.  `rfl`: both
sides are closed terms, which is what makes `PinsOK.names` usable at a
NAMED slot rather than only at a quantified one. -/
theorem pinNames_boolTrue :
    pinNames[PIN_BOOL_TRUE]? = some ConLeche.boolTrueName := by rfl

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:452-457 Expr.isBoolTrue — **the
catch-all arm's obligation**: a handle whose view is not a `.const` denotes
an expression that is not a `.const`, so con-leche's own `isBoolTrue`
answers `false` on it.  Ten `denote_*_inv`s and no `grind`; this is
`Bridge/Core/Memo.lean`'s `denote_stuck_of_whnfCoreStuckTag` at one
constructor instead of six. -/
theorem isBoolTrue_of_not_const {st : EStore} (hwf : StoreWF st) {h : EIdx}
    {e : Expr} {v : ENodeView} (hv : st.view h = some v)
    (he : denoteE st h = some e)
    (hne : ∀ c us, v ≠ .const c us) : ConLeche.Expr.isBoolTrue e = false := by
  cases v with
  | bvar i => rw [denote_bvar_inv hwf hv he]; rfl
  | fvar k t =>
    obtain ⟨t', rfl, _⟩ := denote_fvar_inv hwf hv he; rfl
  | sort u => obtain ⟨l, rfl, _⟩ := denote_sort_inv hwf hv he; rfl
  | const n us => exact absurd rfl (hne n us)
  | app f a => obtain ⟨p, q, rfl, _, _⟩ := denote_app_inv hwf hv he; rfl
  | lam ty b => obtain ⟨p, q, rfl, _, _⟩ := denote_lam_inv hwf hv he; rfl
  | forallE ty b =>
    obtain ⟨p, q, rfl, _, _⟩ := denote_forallE_inv hwf hv he; rfl
  | letE ty w b =>
    obtain ⟨p, q, r, rfl, _, _, _⟩ := denote_letE_inv hwf hv he; rfl
  | lit l => rw [denote_lit_inv hwf hv he]; rfl
  | proj n i sub => obtain ⟨p, q, rfl, _, _⟩ := denote_proj_inv hwf hv he; rfl

/-! ### The arms as `grind` lemmas

Each exit of the twin is one lemma in the shape its verification condition
has, registered with `@[bridge_grind]`; `isBoolTrue_spec` is then `vcgen` with
`finish`.  The subject's constant view comes from `Bridge/Grind.lean` §6
(the tag test the twin makes first, `DenoteView.const`, `exprTag_const`,
`ENodeView.tagOf_const`), and con-leche's `isBoolTrue` is met at a
constant by the two lemmas for its universe-argument and name tests. -/

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:452-457 Expr.isBoolTrue — the
tag-first twin's `else` arm: a handle whose TAG is not `const`. -/
theorem isBoolTrue_of_tag {st : EStore} (hwf : StoreWF st) {h : EIdx} {e : Expr}
    (he : denoteE st h = some e) (ht : ¬ h.tag = ETag.const) :
    ConLeche.Expr.isBoolTrue e = false := by
  obtain ⟨v, hv⟩ := denoteE_view he
  exact isBoolTrue_of_not_const hwf hv he
    (fun c us hh => view_tagOf_ne hv (t := ETag.const) (by simpa using ht)
      (by rw [hh]; rfl))
grind_pattern [bridge_grind] isBoolTrue_of_tag =>
  ConLeche.Expr.isBoolTrue e, denoteE st h

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:452-457 Expr.isBoolTrue — the
universe-argument test fails: the handle is not the empty-levels pin, so the
denoted list is not `[]` (`denoteLs_inj`: index inequality IS structural
inequality). -/
theorem isBoolTrue_levels {st : EStore} (hwf : StoreWF st) {u e : LsIdx}
    {n : ConLeche.Name} {l : List Level} (hne : ¬ u = e)
    (hus : denoteLs st.lss u = some l) (hel : denoteLs st.lss e = some []) :
    ConLeche.Expr.isBoolTrue (.const n l) = false := by
  obtain ⟨rk, hrk⟩ := hwf
  cases l with
  | nil => exact absurd (denoteLs_inj hrk.lss hus hel) hne
  | cons a as => rfl
grind_pattern [bridge_grind] isBoolTrue_levels =>
  ConLeche.Expr.isBoolTrue (.const n l), denoteLs st.lss u, denoteLs st.lss e

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:452-457 Expr.isBoolTrue — the
universe arguments are the empty list, and the name decides by handle
(`denoteN_inj`: index equality IS name equality). -/
theorem isBoolTrue_name {st : EStore} (hwf : StoreWF st) {c b : NIdx}
    {n : ConLeche.Name} (hc : denoteN st.ns c = some n)
    (hbtn : denoteN st.ns b = some ConLeche.boolTrueName) :
    ConLeche.Expr.isBoolTrue (.const n []) = (c == b) := by
  obtain ⟨rk, hrk⟩ := hwf
  simp only [ConLeche.Expr.isBoolTrue]
  by_cases hb : n = ConLeche.boolTrueName
  · subst hb
    obtain rfl := denoteN_inj hrk.nsWF hc hbtn
    simp only [beq_self_eq_true]
  · have h1 : (c == b) = false := by
      simp only [beq_eq_false_iff_ne]
      intro hcc; subst hcc; exact hb (Option.some.inj (hc.symm.trans hbtn))
    have h2 : (n == ConLeche.boolTrueName) = false := by
      simp only [beq_eq_false_iff_ne]; exact hb
    rw [h1, h2]
grind_pattern [bridge_grind] isBoolTrue_name =>
  ConLeche.Expr.isBoolTrue (.const n []), denoteN st.ns c, denoteN st.ns b

/-- con-leche: ConLeche/Kernel/Basis/Names.lean:109-116 reservedBasisNames —
the `Bool.true` pin, as the name it denotes (`pinAt_spec` at the named slot,
`pinNames_boolTrue`). -/
theorem boolTrueName_spec (s₀ : AState) (hp : PinsOK s₀) :
    ⦃fun s => s = s₀⦄ ConRon.Arena.boolTrueName
    ⦃fun n s' => s' = s₀ ∧ denoteN s₀.store.ns n = some ConLeche.boolTrueName; ⊤⦄ := by
  have hbt := pinNames_boolTrue
  vcgen [ConRon.Arena.boolTrueName, pinBoolTrue] with finish

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:452-457 Expr.isBoolTrue —
**THEOREM 1 for `isBoolTrue`**: is `e` the constant `Bool.true` (the official
kernel's `is_constant(e, Bool.true)`)?

Five verification conditions: the universe-argument test, the name test
(both signs), the catch-all of the view match and the tag test.  **Both tests
are DESIGN §8.3's "index inequality IS structural inequality" cashed** — the
twin compares an `LsIdx` against the empty-levels pin and an `NIdx` against
the `Bool.true` pin where con-leche compares a `List Level` against `[]` and
a `Name` against `boolTrueName`, and `denoteLs_inj` / `denoteN_inj` are what
make the two the same test.

It needs nothing from the `ExprOps` tier, nothing from `denoteProjEntry` and
no fuel bookkeeping (con-leche's `Expr.isBoolTrue` is a plain function). -/
theorem isBoolTrue_spec (s₀ : AState) (h : EIdx) (x : Expr)
    (hok : CheckOK mode env fe s₀) (hden : denoteE s₀.store h = some x) :
    ⦃fun s => s = s₀⦄ ConRon.Arena.isBoolTrue h
    ⦃fun b s' => CheckOK mode env fe s' ∧ s'.store = s₀.store ∧
        s'.pins = s₀.pins ∧ b = ConLeche.Expr.isBoolTrue x; ⊤⦄ := by
  -- the pin table's invariant at the initial state: the two pin reads'
  -- precondition (as a registered forward rule it would fire at every
  -- `CheckOK` of every walk)
  sym only [bridge_grind, hok.pins] =>
    vcgen [ConRon.Arena.isBoolTrue, ConRon.Arena.emptyLevels, boolTrueName_spec] <;> finish

/-! ## `isEagerReduce`

The argument check's test (con-leche's `Expr.isEagerReduce`, official
`is_eager_reduce`): the head constant `eagerReduce` under exactly two
applications.  The twin reads two `viewApp`s and one `viewConst` and compares
the name handle against the `eagerReduce` pin; con-leche's function is met as
ONE equation over tags and projections (`isEagerReduce_eq`), and the handle
test is the name test by `nidx_eq_of_denote` (registered here, guarded). -/

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:420-422 eagerReduceName — the
`PIN_EAGER_REDUCE` slot of `pinNames` is `eagerReduce`'s name. -/
theorem pinNames_eagerReduce :
    pinNames[PIN_EAGER_REDUCE]? = some ConLeche.eagerReduceName := by rfl

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:420-422 eagerReduceName — the
`eagerReduce` pin, as the name it denotes. -/
theorem eagerReduceName_spec (s₀ : AState) (hp : PinsOK s₀) :
    ⦃fun s => s = s₀⦄ ConRon.Arena.eagerReduceName
    ⦃fun n s' => s' = s₀ ∧
        denoteN s₀.store.ns n = some ConLeche.eagerReduceName; ⊤⦄ := by
  have hbt := pinNames_eagerReduce
  vcgen [ConRon.Arena.eagerReduceName, pinEagerReduce] with finish

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:424-429 Expr.isEagerReduce — as
one equation over tags and projections. -/
theorem isEagerReduce_eq (e : Expr) :
    e.isEagerReduce = (exprTag e == ETag.app && exprTag (exprFn e) == ETag.app &&
      exprTag (exprFn (exprFn e)) == ETag.const &&
      exprConstName (exprFn (exprFn e)) == ConLeche.eagerReduceName) := by
  rcases e with _ | _ | _ | _ | ⟨f, _⟩ | _ | _ | _ | _ | _ <;> try rfl
  rcases f with _ | _ | _ | _ | ⟨g, _⟩ | _ | _ | _ | _ | _ <;> try rfl
  rcases g with _ | _ | _ | ⟨c, _⟩ | _ | _ | _ | _ | _ | _ <;> try rfl

local grind_pattern [bridge_grind] nidx_eq_of_denote => StoreWF st, denoteN st.ns a, denoteN st.ns b where
  guard denoteN st.ns a = denoteN st.ns b
  a =/= b
local grind_pattern [bridge_grind] view_of_viewConst => st.viewConst i, some (n, us) where
  guard st.viewConst i = some (n, us)

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:424-429 Expr.isEagerReduce —
**THEOREM 1 for `isEagerReduce`**: is `e` of the form `eagerReduce _ _`
(official `is_eager_reduce`)? -/
theorem isEagerReduce_spec (s₀ : AState) (h : EIdx) (x : Expr)
    (hok : CheckOK mode env fe s₀) (hden : denoteE s₀.store h = some x) :
    ⦃fun s => s = s₀⦄ ConRon.Arena.isEagerReduce h
    ⦃fun b s' => CheckOK mode env fe s' ∧ s'.store = s₀.store ∧
        s'.pins = s₀.pins ∧ b = ConLeche.Expr.isEagerReduce x; ⊤⦄ := by
  sym only [bridge_grind, hok.pins, isEagerReduce_eq] =>
    vcgen [ConRon.Arena.isEagerReduce, eagerReduceName_spec] <;> finish

/-! ## The axiom census -/

section Census

#print axioms pinNames_boolTrue
#print axioms isBoolTrue_of_not_const
#print axioms isBoolTrue_levels
#print axioms isBoolTrue_name
#print axioms isBoolTrue_spec
#print axioms pinNames_eagerReduce
#print axioms isEagerReduce_eq
#print axioms isEagerReduce_spec

end Census

end ConRon.Bridge.Core
