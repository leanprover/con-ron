/-
# `ConRon.Bridge.Core.Walks.Guards` — the `defeq` body's cheap tests

Task #97-P3-CoreWalks.  `Arena/Core.lean`'s `defeqStep` opens with a run of
scalar tests — `isBoolTrue`, `quickPair`, `sameConstHeads`, `unfoldableHead`
— that read the handle word or one `view` and nothing else.  They are the
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

namespace ConRon.Bridge.Core

set_option autoImplicit false
set_option mvcgen.warning false
set_option maxHeartbeats 1000000

open ConLeche ConRon.Arena ConRon.Bridge Std.Do

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
  | lam ty b m => obtain ⟨p, q, rfl, _, _⟩ := denote_lam_inv hwf hv he; rfl
  | forallE ty b m =>
    obtain ⟨p, q, rfl, _, _⟩ := denote_forallE_inv hwf hv he; rfl
  | letE ty w b =>
    obtain ⟨p, q, r, rfl, _, _, _⟩ := denote_letE_inv hwf hv he; rfl
  | lit l => rw [denote_lit_inv hwf hv he]; rfl
  | proj n i sub => obtain ⟨p, q, rfl, _, _⟩ := denote_proj_inv hwf hv he; rfl

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
    ⦃fun s => ⌜s = s₀⌝⦄ ConRon.Arena.isBoolTrue h
    ⦃⇓? b s' => ⌜CheckOK mode env fe s' ∧ s'.store = s₀.store ∧
        s'.pins = s₀.pins ∧ b = ConLeche.Expr.isBoolTrue x⌝⦄ := by
  have hp := hok.pins
  obtain ⟨rk, hrk⟩ := hok.state.wf
  mvcgen [ConRon.Arena.isBoolTrue, ConRon.Arena.emptyLevels,
    ConRon.Arena.boolTrueName, ConRon.Arena.pinBoolTrue]
  case vc1 => bridge_peel; subst_vars; exact hp
  case vc3 => bridge_peel; subst_vars; exact hp
  case vc2 =>
    bridge_peel; subst_vars
    rename_i hne _st hel hview
    refine ⟨hok, rfl, rfl, ?_⟩
    obtain ⟨nm, ls, rfl, _hc, hus⟩ := denote_const_inv hok.state.wf hview hden
    cases ls with
    | nil =>
      exact absurd (denoteLs_inj hrk.lss hus hel) (by simpa using hne)
    | cons a as => rfl
  case vc4 =>
    bridge_peel; subst_vars
    rename_i hc0 hu0 hr0 hne hbt0 _st hbt hel hview
    refine ⟨hok, rfl, rfl, ?_⟩
    obtain ⟨nm, ls, rfl, hc, hus⟩ := denote_const_inv hok.state.wf hview hden
    have husr : hu0 = hr0 := by simpa using hne
    subst husr
    rw [hus] at hel
    obtain rfl := Option.some.inj hel
    have hbtn := hbt _ pinNames_boolTrue
    simp only [ConLeche.Expr.isBoolTrue]
    by_cases hb : nm = ConLeche.boolTrueName
    · subst hb
      obtain rfl := denoteN_inj hrk.nsWF hc hbtn
      simp only [beq_self_eq_true]
    · have hcr : hc0 ≠ hbt0 := by
        intro hcc
        subst hcc
        rw [hc] at hbtn
        exact hb (Option.some.inj hbtn)
      have h1 : (hc0 == hbt0) = false := by
        simp only [beq_eq_false_iff_ne]; exact hcr
      have h2 : (nm == ConLeche.boolTrueName) = false := by
        simp only [beq_eq_false_iff_ne]; exact hb
      rw [h1, h2]
  case vc5 =>
    bridge_peel; subst_vars
    rename_i hne _st hview
    exact ⟨hok, rfl, rfl,
      (isBoolTrue_of_not_const hok.state.wf hview hden
        (fun c us hc => hne c us hc)).symm⟩
  -- the tag-first `else` arm (task #97-P5-Core round 4): no view read, so it
  -- is recovered from the denotation, and its tag is not `const`
  all_goals
    bridge_peel; subst_vars
    obtain ⟨v, hv⟩ := denoteE_view hden
    exact ⟨hok, rfl, rfl,
      (isBoolTrue_of_not_const hok.state.wf hv hden
        (fun c us hh => view_tagOf_ne hv (t := ETag.const) (by assumption)
          (by rw [hh]; rfl))).symm⟩


/-! ## The axiom census -/

section Census

#print axioms pinNames_boolTrue
#print axioms isBoolTrue_of_not_const
/-! **The round's third closed non-slot walk**, and the first that is not a
memo wrapper. -/
#print axioms isBoolTrue_spec

end Census

end ConRon.Bridge.Core
