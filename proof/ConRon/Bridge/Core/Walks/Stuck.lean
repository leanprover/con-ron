/-
# `ConRon.Bridge.Core.Walks.Stuck` — the stuck fallback, `stuckIrrel`

Task #97-P3-Core round 5.  `stuckIrrel` is the `defeq` body's fallback at two
structurally distinct stuck terms — structure-η in both directions, then
unit-likeness, then proof irrelevance — and every congruence failure of
`defeqStep` ends in it.  Round 4 left it in `Walks/Owed.lean` as one
statement over a tower; this module skeletonises the tower top-down:

| walk | twin | con-leche | status |
|---|---|---|---|
| `stuckIrrel_spec` | `Arena/Core.lean:1564` | `Kernel/Core.lean:532-542` | **proved** from the three below |
| `structEtaCert_spec` | `:1502` (over `structEtaCertWith`, `:1416`) | `:450-473` (`:376-448`) | OPEN |
| `structUnitCert_spec` | `:1513` | `:475-503` | OPEN |
| `proofIrrel_spec` | `:1265` | `:284-305` | OPEN |

**One precondition added, and why.**  The twin gates the type-former
telescope certificate of `structUnitCert` (and the two certificate families
of `structEtaCertWith`) on `mode.certs` — the EXECUTED core's
`Cached/CoreC.lean:437/440/508` — where con-leche's spec body runs it
unconditionally.  At `mode.certs = false` the twin answers `true` where the
spec may answer `false`, so the published `stuckIrrel_spec` was **false at
the trusted mode**.  It now takes `hμ : mode.verifiedChecks = true`, which
is what every body theorem of this tier already has in hand
(`certs_of_verifiedChecks`, con-leche's `Verify/BetaGate.lean:126`).
-/
import ConRon.Bridge.Core.Walks.PropRead

namespace ConRon.Bridge.Core

set_option autoImplicit false
set_option mvcgen.warning false
set_option maxHeartbeats 1000000

open ConLeche ConRon.Arena ConRon.Bridge Std.Do

variable {mode : CheckMode} {env : Env} {fe : IFEnv}

/-! ## 1. The three children -/

/-- con-leche: ConLeche/Kernel/Core.lean:450-473 structEtaCert — **THEOREM 1
for `structEtaCert`**: structural η certification of a fully applied
constructor `a` against a stuck `b` of an η-capable stored structure.

**OPEN**: `etaCtorShape` (`getAppFn`, the index, `getAppArgs`), two knot
slots (`inferIO`, `whnf`), then `structEtaCertWith` — seventy lines over
`towerSlotsAll`/`recSlotsAll`, `reservedBasisNames`, `lvlsEq?_spec`,
`constTyAt_spec`, `iotaCerts_spec`, `structEtaProjCerts` (a `List Nat`
recursion over `projFnName`, `stripPis`, `constTyAt`, `iotaCerts`),
`etaProjs` (`projNodesGo`/`projAppsGo`, `mkAppN`) and `defEqList_spec`. -/
theorem structEtaCert_spec {fuel : Nat} (hμ : mode.verifiedChecks = true)
    (hsim : KnotSpec mode env fe fuel)
    (s₀ : AState) (d : Nat) (a b : EIdx) (x y : Expr)
    (hok : CheckOK mode env fe s₀) (hda : denoteE s₀.store a = some x)
    (hdb : denoteE s₀.store b = some y)
    (hwa : Expr.WScoped d x) (hwb : Expr.WScoped d y) :
    ⦃fun s => ⌜s = s₀⌝⦄
      ConRon.Arena.structEtaCert mode (coreKnot mode fe id fuel) fe d a b
    ⦃⇓? r s' => ⌜CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧
        SimBOp (fun F => ConLeche.structEtaCertFueled mode env F d x y) r⌝⦄ := by
  sorry

/-- con-leche: ConLeche/Kernel/Core.lean:475-503 structUnitCert — **THEOREM 1
for `structUnitCert`**: `a` and `b` inhabit the same stored unit-like family.

**OPEN**: two `inferIO`/`whnf` pairs, `getAppFn`/`getAppArgs`, the index,
`reservedBasisNames`, `viewLsLen`, `KnotSpec.defeq`, `constTyAt_spec`,
`iotaCerts_spec`; the `mode.certs` gate is where `hμ` is spent. -/
theorem structUnitCert_spec {fuel : Nat} (hμ : mode.verifiedChecks = true)
    (hsim : KnotSpec mode env fe fuel)
    (s₀ : AState) (d : Nat) (a b : EIdx) (x y : Expr)
    (hok : CheckOK mode env fe s₀) (hda : denoteE s₀.store a = some x)
    (hdb : denoteE s₀.store b = some y)
    (hwa : Expr.WScoped d x) (hwb : Expr.WScoped d y) :
    ⦃fun s => ⌜s = s₀⌝⦄
      ConRon.Arena.structUnitCert mode (coreKnot mode fe id fuel) fe d a b
    ⦃⇓? r s' => ⌜CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧
        SimBOp (fun F => ConLeche.structUnitCertFueled mode env F d x y) r⌝⦄ := by
  sorry

/-- con-leche: ConLeche/Kernel/Core.lean:284-305 proofIrrel — **THEOREM 1 for
`proofIrrel`**: the stuck fallback's proof irrelevance — both unit-like, or
both types' sorts `Prop`.

**OPEN**: `isUnitLikeTy` (`Arena/Core.lean:339`, no bridge spec yet), then
exactly `propIrrel`'s slow arm (`Walks/PropRead.lean`'s `propIrrel_spec`
proves that arm; its `propIrrel_slow*` step lemmas are the pure side). -/
theorem proofIrrel_spec {fuel : Nat} (hsim : KnotSpec mode env fe fuel)
    (s₀ : AState) (d : Nat) (a b : EIdx) (x y : Expr)
    (hok : CheckOK mode env fe s₀) (hda : denoteE s₀.store a = some x)
    (hdb : denoteE s₀.store b = some y)
    (hwa : Expr.WScoped d x) (hwb : Expr.WScoped d y) :
    ⦃fun s => ⌜s = s₀⌝⦄
      ConRon.Arena.proofIrrel (coreKnot mode fe id fuel) fe d a b
    ⦃⇓? r s' => ⌜CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧
        SimBOp (fun F => ConLeche.proofIrrelFueled mode env F d x y) r⌝⦄ := by
  sorry

/-! ## 2. The pure side: `stuckIrrel` at its four exits -/

/-- con-leche: ConLeche/Kernel/Core.lean:532-542 stuckIrrel — the first η
direction certifies. -/
theorem stuckIrrelFueled_eta1 {F d : Nat} {x y : Expr}
    (h : ConLeche.structEtaCertFueled mode env F d x y = .ok true) :
    ConLeche.stuckIrrelFueled mode env F d x y = .ok true := by
  have h' : ConLeche.structEtaCert mode (ConLeche.pureFns mode env F) env d x y
      = .ok true := h
  simp only [ConLeche.stuckIrrelFueled, ConLeche.stuckIrrel, h', bind,
    Except.bind, if_true, pure, Except.pure]

/-- con-leche: ConLeche/Kernel/Core.lean:532-542 stuckIrrel — the second η
direction certifies. -/
theorem stuckIrrelFueled_eta2 {F d : Nat} {x y : Expr}
    (h1 : ConLeche.structEtaCertFueled mode env F d x y = .ok false)
    (h2 : ConLeche.structEtaCertFueled mode env F d y x = .ok true) :
    ConLeche.stuckIrrelFueled mode env F d x y = .ok true := by
  have h1' : ConLeche.structEtaCert mode (ConLeche.pureFns mode env F) env d x y
      = .ok false := h1
  have h2' : ConLeche.structEtaCert mode (ConLeche.pureFns mode env F) env d y x
      = .ok true := h2
  simp only [ConLeche.stuckIrrelFueled, ConLeche.stuckIrrel, h1', h2', bind,
    Except.bind, Bool.false_eq_true, if_false, if_true, pure, Except.pure]

/-- con-leche: ConLeche/Kernel/Core.lean:532-542 stuckIrrel — unit-likeness
certifies. -/
theorem stuckIrrelFueled_unit {F d : Nat} {x y : Expr}
    (h1 : ConLeche.structEtaCertFueled mode env F d x y = .ok false)
    (h2 : ConLeche.structEtaCertFueled mode env F d y x = .ok false)
    (h3 : ConLeche.structUnitCertFueled mode env F d x y = .ok true) :
    ConLeche.stuckIrrelFueled mode env F d x y = .ok true := by
  have h1' : ConLeche.structEtaCert mode (ConLeche.pureFns mode env F) env d x y
      = .ok false := h1
  have h2' : ConLeche.structEtaCert mode (ConLeche.pureFns mode env F) env d y x
      = .ok false := h2
  have h3' : ConLeche.structUnitCert (ConLeche.pureFns mode env F) env d x y
      = .ok true := h3
  simp only [ConLeche.stuckIrrelFueled, ConLeche.stuckIrrel, h1', h2', h3',
    bind, Except.bind, Bool.false_eq_true, if_false, if_true, pure,
    Except.pure]

/-- con-leche: ConLeche/Kernel/Core.lean:532-542 stuckIrrel — none of the
three certifies, so proof irrelevance decides. -/
theorem stuckIrrelFueled_proof {F d : Nat} {x y : Expr} {r : Bool}
    (h1 : ConLeche.structEtaCertFueled mode env F d x y = .ok false)
    (h2 : ConLeche.structEtaCertFueled mode env F d y x = .ok false)
    (h3 : ConLeche.structUnitCertFueled mode env F d x y = .ok false)
    (h4 : ConLeche.proofIrrelFueled mode env F d x y = .ok r) :
    ConLeche.stuckIrrelFueled mode env F d x y = .ok r := by
  have h1' : ConLeche.structEtaCert mode (ConLeche.pureFns mode env F) env d x y
      = .ok false := h1
  have h2' : ConLeche.structEtaCert mode (ConLeche.pureFns mode env F) env d y x
      = .ok false := h2
  have h3' : ConLeche.structUnitCert (ConLeche.pureFns mode env F) env d x y
      = .ok false := h3
  have h4' : ConLeche.proofIrrel (ConLeche.pureFns mode env F) env d x y
      = .ok r := h4
  simp only [ConLeche.stuckIrrelFueled, ConLeche.stuckIrrel, h1', h2', h3',
    h4', bind, Except.bind, Bool.false_eq_true, if_false]

/-! ## 3. The walk -/

/-- con-leche: ConLeche/Kernel/Core.lean:532-542 stuckIrrel — **THEOREM 1 for
`stuckIrrel`**, the fallback at two stuck terms: structure-η in both
directions, then the unit certificate, then proof irrelevance.

**PROVED** (round 5, moved here from `Walks/Owed.lean`) from the three
children above, staged by `triple_seq`, with the fuel merge at each exit.
**Statement change: the precondition `hμ` is new** (module note). -/
theorem stuckIrrel_spec {fuel : Nat} (hμ : mode.verifiedChecks = true)
    (hsim : KnotSpec mode env fe fuel)
    (s₀ : AState) (d : Nat) (a b : EIdx) (x y : Expr)
    (hok : CheckOK mode env fe s₀) (hda : denoteE s₀.store a = some x)
    (hdb : denoteE s₀.store b = some y)
    (hwa : Expr.WScoped d x) (hwb : Expr.WScoped d y) :
    ⦃fun s => ⌜s = s₀⌝⦄
      ConRon.Arena.stuckIrrel mode (coreKnot mode fe id fuel) fe d a b
    ⦃⇓? r s' => ⌜CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧
        SimBOp (fun F => ConLeche.stuckIrrelFueled mode env F d x y) r⌝⦄ := by
  unfold ConRon.Arena.stuckIrrel
  refine triple_seq (structEtaCert_spec hμ hsim s₀ d a b x y hok hda hdb hwa
    hwb) ?_
  rintro r1 s1 ⟨hok1, hx1, hp1, F1, hF1⟩
  cases r1
  · try dsimp only
    have hda1 := denote_ext hda hx1
    have hdb1 := denote_ext hdb hx1
    refine triple_seq (structEtaCert_spec hμ hsim s1 d b a y x hok1 hdb1 hda1
      hwb hwa) ?_
    rintro r2 s2 ⟨hok2, hx2, hp2, F2, hF2⟩
    cases r2
    · try dsimp only
      have hda2 := denote_ext hda1 hx2
      have hdb2 := denote_ext hdb1 hx2
      refine triple_seq (structUnitCert_spec hμ hsim s2 d a b x y hok2 hda2 hdb2
        hwa hwb) ?_
      rintro r3 s3 ⟨hok3, hx3, hp3, F3, hF3⟩
      cases r3
      · try dsimp only
        refine triple_mono (proofIrrel_spec hsim s3 d a b x y hok3
          (denote_ext hda2 hx3) (denote_ext hdb2 hx3) hwa hwb) ?_
        rintro r4 s4 ⟨hok4, hx4, hp4, F4, hF4⟩
        refine ⟨hok4, hx1.trans (hx2.trans (hx3.trans hx4)),
          hp4.trans (hp3.trans (hp2.trans hp1)),
          max (max F1 F2) (max F3 F4), ?_⟩
        exact stuckIrrelFueled_proof
          (structEtaCertFueled_mono (Nat.le_trans (Nat.le_max_left F1 F2)
            (Nat.le_max_left _ _)) hF1)
          (structEtaCertFueled_mono (Nat.le_trans (Nat.le_max_right F1 F2)
            (Nat.le_max_left _ _)) hF2)
          (structUnitCertFueled_mono (Nat.le_trans (Nat.le_max_left F3 F4)
            (Nat.le_max_right _ _)) hF3)
          (proofIrrelFueled_mono (Nat.le_trans (Nat.le_max_right F3 F4)
            (Nat.le_max_right _ _)) hF4)
      · try dsimp only
        mvcgen
        bridge_peel; subst_vars
        refine ⟨hok3, hx1.trans (hx2.trans hx3), hp3.trans (hp2.trans hp1),
          max (max F1 F2) F3, ?_⟩
        exact stuckIrrelFueled_unit
          (structEtaCertFueled_mono (Nat.le_trans (Nat.le_max_left F1 F2)
            (Nat.le_max_left _ _)) hF1)
          (structEtaCertFueled_mono (Nat.le_trans (Nat.le_max_right F1 F2)
            (Nat.le_max_left _ _)) hF2)
          (structUnitCertFueled_mono (Nat.le_max_right _ _) hF3)
    · try dsimp only
      mvcgen
      bridge_peel; subst_vars
      refine ⟨hok2, hx1.trans hx2, hp2.trans hp1, max F1 F2, ?_⟩
      exact stuckIrrelFueled_eta2
        (structEtaCertFueled_mono (Nat.le_max_left _ _) hF1)
        (structEtaCertFueled_mono (Nat.le_max_right _ _) hF2)
  · try dsimp only
    mvcgen
    bridge_peel; subst_vars
    exact ⟨hok1, hx1, hp1, F1, stuckIrrelFueled_eta1 hF1⟩

/-! ## 4. The axiom census -/

section Census

#print axioms stuckIrrelFueled_eta1
#print axioms stuckIrrelFueled_eta2
#print axioms stuckIrrelFueled_unit
#print axioms stuckIrrelFueled_proof
/-! `sorryAx` expected on the three children and, through them, on
`stuckIrrel_spec`. -/
#print axioms stuckIrrel_spec

end Census

end ConRon.Bridge.Core
