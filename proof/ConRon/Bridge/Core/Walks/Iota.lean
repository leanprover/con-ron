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
import ConRon.Bridge.Core.Walks.IotaMajor

namespace ConRon.Bridge.Core

set_option autoImplicit false
set_option mvcgen.warning false
set_option maxHeartbeats 1000000

open ConLeche ConRon.Arena ConRon.Bridge Std.Do

variable {mode : CheckMode} {env : Env} {fe : IFEnv}

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
which is the equation the hoist owes.  The count `n` is the whole held
vector (`hn`): both callers pass `size`, and at a larger `n` the twin's
arity guard reads `n` where con-leche's reads the spine. -/
theorem iotaRecAt_spec {fuel : Nat} (hμ : mode.verifiedChecks = true)
    (henv : ConLeche.EnvWF env) (hsim : KnotSpec mode env fe fuel)
    (s₀ : AState) (d : Nat) (hd : EIdx) (sargs : Array EIdx) (n : Nat)
    (h : Expr) (xs : List Expr)
    (hok : CheckOK mode env fe s₀) (hdh : denoteE s₀.store hd = some h)
    (hnapp : ∀ f a, h ≠ .app f a)
    (hn : n = sargs.size)
    (hxs : Frontend.denoteEList s₀.store sargs.toList = some xs)
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
  unfold ConRon.Arena.iotaRec
  refine triple_seq (ExprOps.getAppFn_spec coreWalkFuel s₀ e hok.state
    (by rw [hden]; rfl)) ?_
  rintro hd s1 ⟨hs1, hrelF⟩
  subst s1
  refine triple_seq (ExprOps.getAppArgs_spec coreWalkFuel s₀ e hok.state
    (by rw [hden]; rfl)) ?_
  rintro args s2 ⟨hs2, hrelA⟩
  subst s2
  have hmk : Expr.mkAppN x.getAppFn x.getAppArgs = x := Expr.mkAppN_getApp x
  refine triple_mono (iotaRecAt_spec hμ henv hsim s₀ d hd args.toArray
    args.length x.getAppFn x.getAppArgs hok (hrelF x hden)
    (fun f a => ConLeche.Expr.getAppFn_not_app x f a) (by simp)
    (by simpa using hrelA x hden) (by rw [hmk]; exact hw)) ?_
  rintro r s' ⟨h1, h2, h3, h4⟩
  rw [hmk] at h4
  exact ⟨h1, h2, h3, h4⟩

section Census