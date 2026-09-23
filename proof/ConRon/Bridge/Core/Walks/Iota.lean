/-
# `ConRon.Bridge.Core.Walks.Iota` — the ι step, `iotaRec`

Task #97-P3-Core round 6 (lane `iota`).  `iotaRec` is `whnfCoreBody`'s ι
step: at a stored recursor applied to exactly its telescope, the major premise
is PREPARED (the K rescue on the raw major, or head normalisation, the literal
conversion and the η / `And` rescue), and a matching rule of a fully applied
constructor fires after the level and parameter comparison and the three
certificate runs.  Round 4 left it in `Walks/Owed.lean` as one statement over
the whole tower; it moved here because the η rescue calls
`structEtaCertWith` (`Walks/Stuck.lean`), which `Owed.lean` cannot import.

The module is top-down, one theorem per twin function:

| walk | twin (`Arena/Core.lean`) | con-leche |
|---|---|---|
| `iotaRec_spec` | `:2049` | `Kernel/Core.lean:797-910` |
| `iotaRecAt_spec` | `:1959` | the same clause at a held spine |
| `prepareMajor_spec` | `:1871` | `:758-795` |
| `majorToCtor_spec` | `:1660` | `:544-726` |
| `litMajorToCtor_spec` | `:1774` | `:728-740` |
| `recFireComparands_spec` | `:1920` | `CoreDefs.lean:948-968` |
| `iotaIndexOk_spec` | `:1252` | `Core.lean:255-265` |

and the state-only readers under them (`isCtorApp`, `litToCtorIfNat`,
`capsNeverZero`, `fabScopeOk`, `etaFabArgsE`, `andRescueSlots`).

**Preconditions added to `iotaRec_spec`** (it had neither): `hμ :
mode.verifiedChecks = true` — the twin gates the rescue certificates and the
ι certificate family on `mode.certs` (`Cached/CoreC.lean:576/588/621/654/658/
797/814`) where con-leche's spec body runs them unconditionally, the same
repair round 5 made to `stuckIrrel_spec` — and `henv : EnvWF env`, the
hypothesis of con-leche's own `iotaRec_WScoped` / `prepareMajorFueled_WScoped`
(the answer's scoping, which `SimOOp` states) and of `const_ty_hasFvar` (the
certificate runs' subjects).
-/
import ConRon.Bridge.Core.Walks.Stuck
import ConRon.Bridge.Core.Walks.ProjLit

namespace ConRon.Bridge.Core

set_option autoImplicit false
set_option mvcgen.warning false
set_option maxHeartbeats 1000000

open ConLeche ConRon.Arena ConRon.Bridge Std.Do

variable {mode : CheckMode} {env : Env} {fe : IFEnv}

/-! ## 1. State-only readers -/

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:46-53 isCtorApp — **THEOREM 1
for `isCtorApp`**: an equation with con-leche's reader. -/
theorem isCtorApp_spec (s₀ : AState) (a : EIdx) (x : Expr)
    (hok : CheckOK mode env fe s₀) (hda : denoteE s₀.store a = some x) :
    ⦃fun s => ⌜s = s₀⌝⦄ ConRon.Arena.isCtorApp fe a
    ⦃⇓? r s' => ⌜s' = s₀ ∧ r = ConLeche.isCtorApp env x⌝⦄ := by
  sorry

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:264-268 litToCtorIfNat —
**THEOREM 1 for `litToCtorIfNat`**: a supported `Nat` literal one layer. -/
theorem litToCtorIfNat_spec (s₀ : AState) (h : EIdx) (x : Expr)
    (hok : CheckOK mode env fe s₀) (hda : denoteE s₀.store h = some x) :
    ⦃fun s => ⌜s = s₀⌝⦄ ConRon.Arena.litToCtorIfNat fe h
    ⦃⇓? r s' => ⌜CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧
        denoteE s'.store r = some (ConLeche.litToCtorIfNat env x)⌝⦄ := by
  sorry

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:93-95 capsNeverZero —
**THEOREM 1 for `capsNeverZero`**. -/
theorem capsNeverZero_spec (s₀ : AState) (lps : List NIdx) (us : LsIdx)
    (icaps : IIndCaps) (ks : List ConLeche.Name) (vs : List Level)
    (caps : IndCaps) (hok : CheckOK mode env fe s₀)
    (hks : Frontend.denoteNList s₀.store.ns lps = some ks)
    (hvs : denoteLs s₀.store.lss us = some vs)
    (hcaps : Frontend.denoteCaps s₀.store icaps = some caps) :
    ⦃fun s => ⌜s = s₀⌝⦄ ConRon.Arena.capsNeverZero lps us icaps
    ⦃⇓? r s' => ⌜CheckOK mode env fe s' ∧ s'.store = s₀.store ∧
        s'.pins = s₀.pins ∧ r = ConLeche.capsNeverZero ks vs caps⌝⦄ := by
  sorry

/-- con-leche: ConLeche/Kernel/Core.lean:586-588 majorToCtor (the scope
guard) — **THEOREM 1 for `fabScopeOk`**: the executed tier's three memoised
walks decide con-leche's syntactic guard. -/
theorem fabScopeOk_spec (s₀ : AState) (d : Nat) (fab major : EIdx)
    (ef em : Expr) (hok : CheckOK mode env fe s₀)
    (hf : denoteE s₀.store fab = some ef) (hm : denoteE s₀.store major = some em) :
    ⦃fun s => ⌜s = s₀⌝⦄ ConRon.Arena.fabScopeOk d fab major
    ⦃⇓? r s' => ⌜CheckOK mode env fe s' ∧ s'.store = s₀.store ∧
        s'.pins = s₀.pins ∧
        r = (ef.wscopedB d && ef.looseBVarsBounded 0 &&
          ef.fvarLeaves.all (fun l => em.fvarLeaves.contains l))⌝⦄ := by
  sorry

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:761-766 etaFabArgsE — **THEOREM
1 for `etaFabArgsE`**: the η rescue's fabricated argument spine. -/
theorem etaFabArgsE_spec (s₀ : AState) (T : NIdx) (ust : LsIdx)
    (targs : List EIdx) (major : EIdx) (nF : Nat) (Tn : ConLeche.Name)
    (ls : List Level) (ts : List Expr) (x : Expr)
    (hok : CheckOK mode env fe s₀) (hT : denoteN s₀.store.ns T = some Tn)
    (hus : denoteLs s₀.store.lss ust = some ls)
    (hts : Frontend.denoteEList s₀.store targs = some ts)
    (hx : denoteE s₀.store major = some x) :
    ⦃fun s => ⌜s = s₀⌝⦄ ConRon.Arena.etaFabArgsE fe T ust targs major nF
    ⦃⇓? r s' => ⌜CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧
        Frontend.denoteEList s'.store r =
          some (ConLeche.etaFabArgsE env Tn ls ts x nF)⌝⦄ := by
  sorry

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:796-813 andRescueSlots —
**THEOREM 1 for `andRescueSlots`**: the pinned `And`'s two slots, ready to
fire. -/
theorem andRescueSlots_spec (s₀ : AState) (ctor : NIdx) (nP : Nat)
    (ust : LsIdx) (cn : ConLeche.Name) (ls : List Level)
    (hok : CheckOK mode env fe s₀) (hc : denoteN s₀.store.ns ctor = some cn)
    (hus : denoteLs s₀.store.lss ust = some ls) :
    ⦃fun s => ⌜s = s₀⌝⦄ ConRon.Arena.andRescueSlots fe ctor nP ust
    ⦃⇓? r s' => ⌜CheckOK mode env fe s' ∧ s'.store = s₀.store ∧
        s'.pins = s₀.pins ∧ r = ConLeche.andRescueSlots env cn nP ls⌝⦄ := by
  sorry

/-! ## 2. The major's preparation -/

/-- con-leche: ConLeche/Kernel/Core.lean:728-740 litMajorToCtor — **THEOREM
1 for `litMajorToCtor`**: a `Nat` literal one layer, a supported `String`
literal to its reduced constructor form. -/
theorem litMajorToCtor_spec {fuel : Nat} (hsim : KnotSpec mode env fe fuel)
    (s₀ : AState) (d : Nat) (h : EIdx) (x : Expr)
    (hok : CheckOK mode env fe s₀) (hden : denoteE s₀.store h = some x)
    (hw : Expr.WScoped d x) :
    ⦃fun s => ⌜s = s₀⌝⦄
      ConRon.Arena.litMajorToCtor (coreKnot mode fe id fuel) fe d h
    ⦃⇓? r s' => ⌜CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧
        SimEOp (fun F => ConLeche.litMajorToCtorFueled mode env F d x) d
          s'.store r⌝⦄ := by
  sorry

/-- con-leche: ConLeche/Kernel/Core.lean:544-726 majorToCtor — **THEOREM 1
for `majorToCtor`**, the stuck-major rescue: K, η, and the pinned `And`.
The recursor's name is unused on both sides (`_recName`). -/
theorem majorToCtor_spec {fuel : Nat} (hμ : mode.verifiedChecks = true)
    (henv : ConLeche.EnvWF env) (hsim : KnotSpec mode env fe fuel)
    (s₀ : AState) (d : Nat) (c : NIdx) (rules : List IRecRule) (major : EIdx)
    (cn : ConLeche.Name) (rules' : List RecRule) (x : Expr)
    (hok : CheckOK mode env fe s₀)
    (hr : Frontend.denoteRules s₀.store rules = some rules')
    (hden : denoteE s₀.store major = some x) (hw : Expr.WScoped d x) :
    ⦃fun s => ⌜s = s₀⌝⦄
      ConRon.Arena.majorToCtor mode (coreKnot mode fe id fuel) fe d c rules
        major
    ⦃⇓? r s' => ⌜CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧
        SimEOp (fun F => ConLeche.majorToCtorFueled mode env F d cn rules' x) d
          s'.store r⌝⦄ := by
  sorry

/-- con-leche: ConLeche/Kernel/Core.lean:758-795 prepareMajor — **THEOREM 1
for `prepareMajor`**: the official kernel's order, K rescue on the raw major
or head normalisation first. -/
theorem prepareMajor_spec {fuel : Nat} (hμ : mode.verifiedChecks = true)
    (henv : ConLeche.EnvWF env) (hsim : KnotSpec mode env fe fuel)
    (s₀ : AState) (d : Nat) (c : NIdx) (rules : List IRecRule) (major : EIdx)
    (cn : ConLeche.Name) (rules' : List RecRule) (x : Expr)
    (hok : CheckOK mode env fe s₀)
    (hr : Frontend.denoteRules s₀.store rules = some rules')
    (hden : denoteE s₀.store major = some x) (hw : Expr.WScoped d x) :
    ⦃fun s => ⌜s = s₀⌝⦄
      ConRon.Arena.prepareMajor mode (coreKnot mode fe id fuel) fe d c rules
        major
    ⦃⇓? r s' => ⌜CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧
        SimEOp (fun F => ConLeche.prepareMajorFueled mode env F d cn rules' x) d
          s'.store r⌝⦄ := by
  sorry

/-! ## 3. The firing rule's comparands and the index comparison -/

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:948-968 recFireComparands —
**THEOREM 1 for `recFireComparands`**: both comparand lists, substituted and
re-interned. -/
theorem recFireComparands_spec (s₀ : AState) (rl : IRecRule) (rl' : RecRule)
    (lps : List NIdx) (us : LsIdx) (cvjLps : List NIdx) (args : List EIdx)
    (rP : Nat) (ks : List ConLeche.Name) (vs : List Level)
    (cs : List ConLeche.Name) (xs : List Expr)
    (hok : CheckOK mode env fe s₀)
    (hrl : Frontend.denoteRule s₀.store rl = some rl')
    (hks : Frontend.denoteNList s₀.store.ns lps = some ks)
    (hvs : denoteLs s₀.store.lss us = some vs)
    (hcs : Frontend.denoteNList s₀.store.ns cvjLps = some cs)
    (hxs : Frontend.denoteEList s₀.store args = some xs) :
    ⦃fun s => ⌜s = s₀⌝⦄
      ConRon.Arena.recFireComparands rl lps us cvjLps args rP
    ⦃⇓? r s' => ⌜CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧
        denoteLs s'.store.lss r.1 =
          some (ConLeche.recFireComparands rl' ks vs cs xs rP).1 ∧
        Frontend.denoteEList s'.store r.2 =
          some (ConLeche.recFireComparands rl' ks vs cs xs rP).2⌝⦄ := by
  sorry

/-- con-leche: ConLeche/Kernel/Core.lean:255-265 iotaIndexOk — **THEOREM 1
for `iotaIndexOk`**: the canonical-index comparison of a firing redex. -/
theorem iotaIndexOk_spec {fuel : Nat} (hsim : KnotSpec mode env fe fuel)
    (s₀ : AState) (d mI rP cnP : Nat) (tyC : EIdx) (margs idx : List EIdx)
    (ty : Expr) (ms is : List Expr)
    (hok : CheckOK mode env fe s₀) (hty : denoteE s₀.store tyC = some ty)
    (hms : Frontend.denoteEList s₀.store margs = some ms)
    (his : Frontend.denoteEList s₀.store idx = some is)
    (hwty : Expr.WScoped d ty) (hwms : ∀ z ∈ ms, Expr.WScoped d z)
    (hwis : ∀ z ∈ is, Expr.WScoped d z) :
    ⦃fun s => ⌜s = s₀⌝⦄
      ConRon.Arena.iotaIndexOk (coreKnot mode fe id fuel) fe d mI rP cnP tyC
        margs idx
    ⦃⇓? r s' => ⌜CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧
        SimBOp (fun F => ConLeche.iotaIndexOkFueled mode env F d mI rP cnP ty
          ms is) r⌝⦄ := by
  sorry

/-! ## 4. The ι step -/

/-- con-leche: ConLeche/Kernel/Core.lean:797-910 iotaRec — **THEOREM 1 for
`iotaRecAt`**: one ι step at a spine the caller already holds (task
#97-P6-9's hoist).  The held head `h` is not an application (it is a spine
head), so `getAppFn`/`getAppArgs` of `Expr.mkAppN h xs` are `h` and `xs`,
which is the equation the hoist owes. -/
theorem iotaRecAt_spec {fuel : Nat} (hμ : mode.verifiedChecks = true)
    (henv : ConLeche.EnvWF env) (hsim : KnotSpec mode env fe fuel)
    (s₀ : AState) (d : Nat) (hd : EIdx) (sargs : Array EIdx) (n : Nat)
    (h : Expr) (xs : List Expr)
    (hok : CheckOK mode env fe s₀) (hdh : denoteE s₀.store hd = some h)
    (hnapp : ∀ f a, h ≠ .app f a)
    (hxs : Frontend.denoteEList s₀.store (sargs.toList.take n) = some xs)
    (hw : Expr.WScoped d (Expr.mkAppN h xs)) :
    ⦃fun s => ⌜s = s₀⌝⦄
      ConRon.Arena.iotaRecAt mode (coreKnot mode fe id fuel) fe d hd sargs n
    ⦃⇓? r s' => ⌜CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧
        SimOOp (fun F => ConLeche.iotaRecFueled mode env F d (Expr.mkAppN h xs))
          d s'.store r⌝⦄ := by
  sorry

/-- con-leche: ConLeche/Kernel/Core.lean:797-910 iotaRec — **THEOREM 1 for
`iotaRec`**: one ι step at a recursor application, with the stuck-major
machinery under it.  Moved here from `Walks/Owed.lean` (round 6); **the
preconditions `hμ` and `henv` are new** (module note). -/
theorem iotaRec_spec {fuel : Nat} (hμ : mode.verifiedChecks = true)
    (henv : ConLeche.EnvWF env) (hsim : KnotSpec mode env fe fuel)
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

section Census

#print axioms isCtorApp_spec
#print axioms litToCtorIfNat_spec
#print axioms capsNeverZero_spec
#print axioms fabScopeOk_spec
#print axioms etaFabArgsE_spec
#print axioms andRescueSlots_spec
#print axioms litMajorToCtor_spec
#print axioms majorToCtor_spec
#print axioms prepareMajor_spec
#print axioms recFireComparands_spec
#print axioms iotaIndexOk_spec
#print axioms iotaRecAt_spec
#print axioms iotaRec_spec

end Census

end ConRon.Bridge.Core
