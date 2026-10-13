/-
# `ConRon.Bridge.Core.Walks.Guards` — the `defeq` body's cheap tests

Task #97-P3-CoreWalks.  `Arena/Core.lean`'s definitional-equality block
(`defeqBody` and its lazy-delta steps since task #109, `defeqStep` before)
runs scalar tests — `isBoolTrue`, `sameConstHeads`, `unfoldableHead` (and,
before task #109, `quickPair`) — that read the handle word or one `view` and
nothing else.  They are the
cheapest walks of the whole non-slot tier, because con-leche's comparand is a
plain function (no `CheckM`, no fuel), so the conclusion is an EQUATION
between the arena's answer and con-leche's and there is no `∃ F` to carry.

**`isBoolTrue_spec` is CLOSED**, and it is the round's demonstration that the
cheap row of `Bridge/Core/Walks/Owed.lean`'s table really is cheap: five
verification conditions, no `ExprOps` callee rule, no new denotation, ~45
lines.  Its two siblings that need `getAppFn` (`sameConstHeads`,
`unfoldableHead`) stay in `Owed.lean` until this tier imports the `ExprOps`
tier.

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
import ConRon.Bridge.Frame

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

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:452-457 Expr.isBoolTrue — the
tag-first twin's `else` arm: a handle whose TAG is not `const` (task #120:
in the shape `bridge_fwd` instantiates from the arm's own hypotheses). -/
theorem isBoolTrue_of_tag {st : EStore} (hwf : StoreWF st) {h : EIdx} {e : Expr}
    (he : denoteE st h = some e) (ht : ¬ (h.tag == ETag.const) = true) :
    ConLeche.Expr.isBoolTrue e = false := by
  obtain ⟨v, hv⟩ := denoteE_view he
  exact isBoolTrue_of_not_const hwf hv he
    (fun c us hh => view_tagOf_ne hv (t := ETag.const) ht (by rw [hh]; rfl))

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:452-457 Expr.isBoolTrue — the
universe-argument test fails: the handle is not the empty-levels pin, so the
denoted list is not `[]` (task #120: the arm as a lemma in the shape the
verification condition has). -/
theorem isBoolTrue_levels {st : EStore} (hwf : StoreWF st) {u e : LsIdx}
    {n : ConLeche.Name} {l : List Level} (hne : (u != e) = true)
    (hus : denoteLs st.lss u = some l) (hel : denoteLs st.lss e = some []) :
    false = ConLeche.Expr.isBoolTrue (.const n l) := by
  obtain ⟨rk, hrk⟩ := hwf
  cases l with
  | nil => exact absurd (denoteLs_inj hrk.lss hus hel) (by simpa using hne)
  | cons a as => rfl

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:452-457 Expr.isBoolTrue — the
universe arguments are the empty list, and the name decides by handle
(`denoteN_inj`: index equality IS name equality). -/
theorem isBoolTrue_name {st : EStore} (hwf : StoreWF st) {u e : LsIdx}
    {c b : NIdx} {n : ConLeche.Name} {l : List Level} (hne : ¬ (u != e) = true)
    (hus : denoteLs st.lss u = some l) (hel : denoteLs st.lss e = some [])
    (hc : denoteN st.ns c = some n)
    (hbtn : denoteN st.ns b = some ConLeche.boolTrueName) :
    (c == b) = ConLeche.Expr.isBoolTrue (.const n l) := by
  obtain ⟨rk, hrk⟩ := hwf
  obtain rfl : u = e := by simpa using hne
  obtain rfl := eq_of_eq_some hus hel
  simp only [ConLeche.Expr.isBoolTrue]
  by_cases hb : n = ConLeche.boolTrueName
  · subst hb
    obtain rfl := denoteN_inj hrk.nsWF hc hbtn
    simp only [beq_self_eq_true]
  · have h1 : (c == b) = false := by
      simp only [beq_eq_false_iff_ne]
      intro hcc; subst hcc; exact hb (eq_of_eq_some hc hbtn)
    have h2 : (n == ConLeche.boolTrueName) = false := by
      simp only [beq_eq_false_iff_ne]; exact hb
    rw [h1, h2]

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:452-457 Expr.isBoolTrue —
**THEOREM 1 for `isBoolTrue`**: is `e` the constant `Bool.true` (the official
kernel's `is_constant(e, Bool.true)`)?  CLOSED.

Five verification conditions: two pin-table side goals (`PinsOK`, in hand),
the universe-argument test, the name test, and the catch-all.  **Both tests
are DESIGN §8.3's "index inequality IS structural inequality" cashed** — the
twin compares an `LsIdx` against the empty-levels pin and an `NIdx` against
the `Bool.true` pin where con-leche compares a `List Level` against `[]` and
a `Name` against `boolTrueName`, and `denoteLs_inj` / `denoteN_inj` are what
make the two the same test.

It needs nothing from the `ExprOps` tier, nothing from `denoteProjEntry` and
no fuel bookkeeping (con-leche's `Expr.isBoolTrue` is a plain function), which
is why it was the round's third closed walk and the cheapest of the
seventeen. -/
theorem isBoolTrue_spec (s₀ : AState) (h : EIdx) (x : Expr)
    (hok : CheckOK mode env fe s₀) (hden : denoteE s₀.store h = some x) :
    ⦃fun s => s = s₀⦄ ConRon.Arena.isBoolTrue h
    ⦃fun b s' => CheckOK mode env fe s' ∧ s'.store = s₀.store ∧
        s'.pins = s₀.pins ∧ b = ConLeche.Expr.isBoolTrue x; ⊤⦄ := by
  have hp := hok.pins
  have hbt := pinNames_boolTrue
  vcgen [ConRon.Arena.isBoolTrue, ConRon.Arena.emptyLevels,
    ConRon.Arena.boolTrueName, ConRon.Arena.pinBoolTrue]
  all_goals (bridge_peel; subst_vars)
  bridge_auto [isBoolTrue_of_not_const, isBoolTrue_of_tag, isBoolTrue_levels,
    isBoolTrue_name]

/-! ## The axiom census -/

section Census

#print axioms pinNames_boolTrue
#print axioms isBoolTrue_of_not_const
#print axioms isBoolTrue_levels
#print axioms isBoolTrue_name
/-! **The round's third closed non-slot walk**, and the first that is not a
memo wrapper. -/
#print axioms isBoolTrue_spec

end Census

end ConRon.Bridge.Core
