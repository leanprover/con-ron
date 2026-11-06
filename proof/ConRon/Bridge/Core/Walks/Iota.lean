/-
# `ConRon.Bridge.Core.Walks.Iota` — the ι step, `iotaRec`

`iotaRec` is `whnfCoreBody`'s ι step: at a stored recursor applied
to exactly its telescope whose stored type has that arity, the major premise
is PREPARED (`Walks/IotaMajor.lean`), and a matching rule of a fully applied
constructor fires after **the ι case split** (con-leche task #342 L10, S5c):
at the verified mode, a case-3 redex (not K, the constructor's family may be
`Prop` at the rule's comparand levels) compares the constructor's levels and
parameters with the comparands, certifies the constructor telescope at the
full grade and compares the indices; every other redex fires unchecked.

The module is top-down, one theorem per twin function:

| walk | twin (`Arena/Core.lean`) | con-leche |
|---|---|---|
| `iotaRecAt_spec` | `iotaRecAt` | `Kernel/Core.lean:786-868` |
| `iotaFam_spec` | its certificate family | the same clause's case split |
| `recFireLevels_spec`, `recFireArgs_spec` | `recFireLevels`, `recFireArgs` | `CoreDefs.lean:906-920` |
| `iotaCase3_spec`, `iotaCtorNeverProp_spec` | `iotaCase3`, `iotaCtorNeverProp` | `CoreDefs.lean:72-104` |
| `iotaIndexOk_spec` | `iotaIndexOk` | `Core.lean:282-288` |

The comparand, case-split and index walks are `sym only [bridge_grind, …] =>
vcgen [f, callee specs…] <;> finish`, in the answer shapes of
`Walks/IotaMajor.lean`.  `iotaFam_spec` and `iotaRecAt_spec` are staged:
`triple_seq` through the callees, each exit `triple_pure_at` at the pure
side's value.

`henv : EnvWF env` is the hypothesis of con-leche's own `iotaRec_WScoped` /
`prepareMajorFueled_WScoped` (the answer's scoping, which `SimOOp` states), of
`const_ty_hasFvar` (the certificate runs' subjects) and of the nested pins'
closedness.
-/
module

import ConRon.Bridge.Core.Walks.IotaMajor
import ConRon.Bridge.Core.Walks.Former
import ConRon.Bridge.Core.Walks.IotaLeaves
import ConRon.Bridge.Core.Walks.StrLit
import ConRon.Bridge.Core.Walks.StrCtor
import ConRon.Bridge.Core.Walks.PropRead
import ConRon.Bridge.Core.Walks.Proj
public import ConRon.Bridge.Core.Walks.Spine
import ConRon.Bridge.Core.Walks.Cached
import ConRon.Bridge.ExprOps.Owed
import ConRon.Bridge.ExprOps.MemoSpecs
public import ConRon.Bridge.Core.Walks.Owed
import ConRon.Bridge.Core.Walks.Mono
import ConRon.Bridge.Core.Memo
import ConLeche.Verify.Deep
import ConRon.Bridge.SpecsL
import ConRon.Bridge.Specs
import ConRon.Bridge.GrindAttr

public section

namespace ConRon.Bridge.Core

set_option autoImplicit false
set_option experimental.vcgen true
set_option maxHeartbeats 1000000

open ConLeche ConRon.Arena ConRon.Bridge Std.WP
open scoped Lean.Order

variable {mode : CheckMode} {eager : Bool} {env : Env} {fe : IFEnv}

local grind_pattern [bridge_grind] nidx_eq_of_denote => StoreWF st, denoteN st.ns a, denoteN st.ns b where
  guard denoteN st.ns a = denoteN st.ns b
  a =/= b

/-! ## The comparands -/

/-- con-leche: none — `internLevel` at the tier's invariant. -/
theorem internLevel_specC (s₀ : AState) (u : Level) (hok : CheckOK eager env fe s₀) :
    ⦃fun s => s = s₀⦄ internLevel u
    ⦃fun h s' => CheckOK eager env fe s' ∧ Ext s₀.store s'.store ∧ s'.pins = s₀.pins ∧
        denoteL s'.store.ls h = some u; ⊤⦄ :=
  triple_mono (internLevel_spec s₀ u hok.state.wf)
    (fun _ _ ⟨hwf', hx', _, _, _, _, hc', hp', hd⟩ => ⟨hok.mono ⟨hwf'⟩ hx' hc' hp', hx', hp', hd⟩)

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:906-920 recFireComparands — the canonical
rule's level comparands, `cvjLps.map fun p => Level.subst lps us (.param p)`. -/
theorem substParamLevels_spec (ks : List ConLeche.Name) (vs : List Level) :
    ∀ (ps : List NIdx) (s₀ : AState) (cs : List ConLeche.Name),
      CheckOK eager env fe s₀ → Frontend.denoteNList s₀.store.ns ps = some cs →
      ⦃fun s => s = s₀⦄ ConRon.Arena.substParamLevels ks vs ps
      ⦃fun r s' => CheckOK eager env fe s' ∧ Ext s₀.store s'.store ∧
          s'.pins = s₀.pins ∧
          denoteLList s'.store.ls r =
            some (cs.map fun p => Level.subst ks vs (.param p)); ⊤⦄ := by
  intro ps
  induction ps with
  | nil =>
    intro s₀ cs hok hcs
    sym only [bridge_grind, Frontend.denoteNList, denoteLList, List.map_nil] =>
      vcgen [ConRon.Arena.substParamLevels] <;> finish
  | cons p ps ih =>
    intro s₀ cs hok hcs
    obtain ⟨c0, cs', hp0, hps, rfl⟩ := denoteNList_cons_inv hcs
    have step := fun s => ih s cs'
    clear ih
    sym only [bridge_grind, denoteLList, List.map_cons, CheckOK.readN' hok] =>
      vcgen [ConRon.Arena.substParamLevels,
        internLevel_specC (eager := eager) (env := env) (fe := fe), step] <;> finish

/-- the nested pin comparand -/
@[expose] def pinCmpFn (xs : List Expr) (rP : Nat) (ks : List ConLeche.Name) (us : List Level)
    (p : Expr) : Expr :=
  Expr.instSpine (xs.take rP) (rP - 1) (p.instantiateLevelParams ks us)

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:906-920 recFireComparands — the nested
rule's parameter pins, level-instantiated and instantiated at the recursor's
leading-argument spine. -/
theorem instSpinePins_spec (lps : List NIdx) (us : LsIdx) (args : List EIdx)
    (rP : Nat) (ksv : List ConLeche.Name) (usv : List Level) (xs : List Expr) :
    ∀ (pins : List EIdx) (s₀ : AState) (Ps : List Expr),
      CheckOK eager env fe s₀ →
      Frontend.denoteNList s₀.store.ns lps = some ksv →
      denoteLs s₀.store.lss us = some usv →
      Frontend.denoteEList s₀.store args = some xs →
      Frontend.denoteEList s₀.store pins = some Ps →
      ⦃fun s => s = s₀⦄ ConRon.Arena.instSpinePins lps us args rP pins
      ⦃fun r s' => CheckOK eager env fe s' ∧ Ext s₀.store s'.store ∧
          s'.pins = s₀.pins ∧
          Frontend.denoteEList s'.store r = some (Ps.map (pinCmpFn xs rP ksv usv)); ⊤⦄ := by
  intro pins
  induction pins with
  | nil =>
    intro s₀ Ps hok _ _ _ hPs
    sym only [bridge_grind, List.map_nil] =>
      vcgen [ConRon.Arena.instSpinePins] <;> finish
  | cons p ps ih =>
    intro s₀ Ps hok hks hus hxs hPs
    obtain ⟨P, Ps', hP, hPs', rfl⟩ := denoteEList_cons_inv hPs
    have step := fun s => ih s Ps'
    clear ih
    sym only [bridge_grind, List.map_cons, pinCmpFn, CheckOK.readN' hok, CheckOK.readL' hok,
        CheckOK.readLs' hok] =>
      vcgen [ConRon.Arena.instSpinePins, ExprOps.instLPFast_spec (ksv := ksv) (usv := usv),
        ExprOps.instSpine_spec, step] <;> finish

/-- con-leche's `piResidual` along a fixed spine, as a function of the telescope -/
def piResAt (xs : List Expr) (e : Expr) : Option Expr := ConLeche.piResidual e xs

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:704-707 piResidual — the empty spine. -/
theorem piResAt_nil (e : Expr) : piResAt [] e = some e := by
  simp [piResAt, ConLeche.piResidual]

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:704-707 piResidual — one argument, as an
equation over the telescope's tag and body. -/
theorem piResAt_cons (x : Expr) (xs : List Expr) (e : Expr) :
    piResAt (x :: xs) e =
      if exprTag e = ETag.forallE then piResAt xs ((exprBody e).instantiate1 x) else none := by
  cases e <;> simp only [piResAt, ConLeche.piResidual, exprTag, exprBody] <;>
    first | rfl | rw [if_neg (by decide)]

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:704-707 piResidual — **THEOREM 1 for
`piResidual`**: the telescope residual along an argument spine, at whatever the
telescope handle denotes. -/
theorem piResidual_specA : ∀ (as : List EIdx) (s₀ : AState) (h : EIdx)
    (xs : List Expr), CheckOK eager env fe s₀ → (denoteE s₀.store h).isSome = true →
    Frontend.denoteEList s₀.store as = some xs →
    ⦃fun s => s = s₀⦄ ConRon.Arena.piResidual h as
    ⦃fun r s' => CheckOK eager env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧
        MapRel (piResAt xs) (denoteE s₀.store h) (denoteEO s'.store r); ⊤⦄ := by
  intro as
  induction as with
  | nil =>
    intro s₀ h xs hok hh hxs
    sym only [bridge_grind, piResAt_nil] => vcgen [ConRon.Arena.piResidual] <;> finish
  | cons a as ih =>
    intro s₀ h xs hok hh hxs
    obtain ⟨x, xs', hx, hxs', rfl⟩ := denoteEList_cons_inv hxs
    have step := fun s b => ih s b xs'
    clear ih
    sym only [bridge_grind, piResAt_cons] =>
      vcgen [ConRon.Arena.piResidual, instantiate1Fast_specR (eager := eager) (env := env) (fe := fe), step] <;> finish

/-- con-leche: none — a denoting rule's fields, as one equation. -/
theorem denoteRule_eq {st : EStore} {rl : IRecRule} {rl' : RecRule}
    (hrl : Frontend.denoteRule st rl = some rl') :
    ∃ c f rr, denoteN st.ns rl.ctor = some c ∧
      Frontend.denoteFire st rl.fire = some f ∧ denoteE st rl.rhs = some rr ∧
      rl' = ⟨c, rl.nfields, f, rr⟩ := by
  simp only [Frontend.denoteRule] at hrl
  split at hrl
  · rename_i c f rr hc hf hr; cases hrl; exact ⟨c, f, rr, hc, hf, hr, rfl⟩
  · simp at hrl

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:906-920 recFireComparands —
`instSpinePins_spec` at whatever the pins denote (the caller's match binds them). -/
theorem instSpinePins_specA (lps : List NIdx) (us : LsIdx) (args : List EIdx)
    (rP : Nat) (ksv : List ConLeche.Name) (usv : List Level) (xs : List Expr)
    (pins : List EIdx) (s₀ : AState) (hok : CheckOK eager env fe s₀)
    (hks : Frontend.denoteNList s₀.store.ns lps = some ksv)
    (hus : denoteLs s₀.store.lss us = some usv)
    (hxs : Frontend.denoteEList s₀.store args = some xs)
    (hPs : (Frontend.denoteEList s₀.store pins).isSome = true) :
    ⦃fun s => s = s₀⦄ ConRon.Arena.instSpinePins lps us args rP pins
    ⦃fun r s' => CheckOK eager env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧
        MapRel (List.map (pinCmpFn xs rP ksv usv)) (Frontend.denoteEList s₀.store pins)
          (Frontend.denoteEList s'.store r); ⊤⦄ := by
  obtain ⟨Ps, hPs⟩ := Option.isSome_iff_exists.mp hPs
  rw [hPs]
  exact instSpinePins_spec lps us args rP ksv usv xs pins s₀ Ps hok hks hus hxs hPs

/-- the canonical rule's level comparand -/
@[expose] def paramLvlFn (ks : List ConLeche.Name) (vs : List Level) (p : ConLeche.Name) : Level :=
  Level.subst ks vs (.param p)

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:1140-1162 recFireComparands — at a nested rule. -/
theorem recFireComparands_nested (c : ConLeche.Name) (nf : Nat) (L : List Level)
    (P : List Expr) (rr : Expr) (cnP : Nat) (lps : List ConLeche.Name) (us : List Level)
    (cvjLps : List ConLeche.Name) (args : List Expr) (rP : Nat) :
    ConLeche.recFireComparands ⟨c, nf, .nested L P, rr⟩ cnP lps us cvjLps args rP =
      (L.map (Level.subst lps us), P.map (pinCmpFn args rP lps us)) := rfl

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:1140-1162 recFireComparands — at a plain rule. -/
theorem recFireComparands_plain (c : ConLeche.Name) (nf : Nat)
    (rr : Expr) (cnP : Nat) (lps : List ConLeche.Name) (us : List Level)
    (cvjLps : List ConLeche.Name) (args : List Expr) (rP : Nat) :
    ConLeche.recFireComparands ⟨c, nf, .plain, rr⟩ cnP lps us cvjLps args rP =
      (cvjLps.map (paramLvlFn lps us), args.take cnP) := rfl

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:1140-1162 recFireComparands — at a rule
with stored levels. -/
theorem recFireComparands_levels (c : ConLeche.Name) (nf : Nat) (L : List Level)
    (rr : Expr) (cnP : Nat) (lps : List ConLeche.Name) (us : List Level)
    (cvjLps : List ConLeche.Name) (args : List Expr) (rP : Nat) :
    ConLeche.recFireComparands ⟨c, nf, .levels L, rr⟩ cnP lps us cvjLps args rP =
      (L.map (Level.subst lps us), args.take cnP) := rfl

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:906-920 recFireComparands — **THEOREM 1 for
`recFireArgs`**: the constructor-PARAMETER comparands (`(recFireComparands …).2`). -/
theorem recFireArgs_spec (s₀ : AState) (rl : IRecRule) (rl' : RecRule) (cnP : Nat)
    (lps : List NIdx) (us : LsIdx) (args : List EIdx) (rP : Nat)
    (ks : List ConLeche.Name) (vs : List Level) (cs : List ConLeche.Name)
    (xs : List Expr)
    (hok : CheckOK eager env fe s₀)
    (hrl : Frontend.denoteRule s₀.store rl = some rl')
    (hks : Frontend.denoteNList s₀.store.ns lps = some ks)
    (hvs : denoteLs s₀.store.lss us = some vs)
    (hxs : Frontend.denoteEList s₀.store args = some xs) :
    ⦃fun s => s = s₀⦄ ConRon.Arena.recFireArgs rl cnP lps us args rP
    ⦃fun r s' => CheckOK eager env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧
        Frontend.denoteEList s'.store r =
          some (ConLeche.recFireComparands rl' cnP ks vs cs xs rP).2; ⊤⦄ := by
  obtain ⟨c, f, rr, _hc, hf, _hr, rfl⟩ := denoteRule_eq hrl
  cases hfire : rl.fire with
  | nested lvls pins =>
    rw [hfire] at hf
    obtain ⟨Lv, Ps, _, hPs, rfl⟩ : ∃ Lv Ps,
        denoteLList s₀.store.ls lvls = some Lv ∧
        Frontend.denoteEList s₀.store pins = some Ps ∧ f = .nested Lv Ps := by
      simp only [Frontend.denoteFire] at hf
      split at hf
      · rename_i Lv Ps h1 h2; cases hf; exact ⟨Lv, Ps, h1, h2, rfl⟩
      · simp at hf
    sym only [bridge_grind, recFireComparands_nested] =>
      vcgen [ConRon.Arena.recFireArgs,
        instSpinePins_specA lps us args rP ks vs xs (eager := eager) (env := env) (fe := fe)] <;> finish
  | plain =>
    rw [hfire] at hf
    obtain rfl : f = .plain := by simpa [Frontend.denoteFire] using hf.symm
    sym only [bridge_grind, recFireComparands_plain] =>
      vcgen [ConRon.Arena.recFireArgs] <;> finish
  | levels lvls =>
    rw [hfire] at hf
    obtain ⟨Lv, _, rfl⟩ : ∃ Lv, denoteLList s₀.store.ls lvls = some Lv ∧ f = .levels Lv := by
      simp only [Frontend.denoteFire, Option.map_eq_some_iff] at hf
      obtain ⟨Lv, h1, h2⟩ := hf; exact ⟨Lv, h1, h2.symm⟩
    sym only [bridge_grind, recFireComparands_levels] =>
      vcgen [ConRon.Arena.recFireArgs] <;> finish

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:906-920 recFireComparands — the nested
rule's level comparands, `lvls.map (Level.subst lps us)`. -/
theorem substLevelsAt_spec (ks : List ConLeche.Name) (vs : List Level) :
    ∀ (lvls : List LIdx) (s₀ : AState) (L : List Level),
      CheckOK eager env fe s₀ → denoteLList s₀.store.ls lvls = some L →
      ⦃fun s => s = s₀⦄ ConRon.Arena.substLevelsAt ks vs lvls
      ⦃fun r s' => CheckOK eager env fe s' ∧ Ext s₀.store s'.store ∧
          s'.pins = s₀.pins ∧
          denoteLList s'.store.ls r = some (L.map (Level.subst ks vs)); ⊤⦄ := by
  intro lvls
  induction lvls with
  | nil =>
    intro s₀ L hok hL
    sym only [bridge_grind, denoteLList, List.map_nil] =>
      vcgen [ConRon.Arena.substLevelsAt] <;> finish
  | cons u us ih =>
    intro s₀ L hok hL
    obtain ⟨l0, L', hu, hus, rfl⟩ := denoteLList_cons_inv hL
    have step := fun s => ih s L'
    clear ih
    sym only [bridge_grind, denoteLList, List.map_cons, CheckOK.readL' hok] =>
      vcgen [ConRon.Arena.substLevelsAt,
        internLevel_specC (eager := eager) (env := env) (fe := fe), step] <;> finish

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:906-920 recFireComparands — the
level comparands, which do not read the argument spine. -/
@[expose] def cmpLevels (rl : RecRule) (lps : List ConLeche.Name) (us : List Level)
    (cvjLps : List ConLeche.Name) : List Level :=
  (ConLeche.recFireComparands rl 0 lps us cvjLps [] 0).1

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:906-920 recFireComparands — the level
comparands do not read the spine. -/
theorem recFireComparands_fst (rl : RecRule) (cnP : Nat) (lps : List ConLeche.Name)
    (us : List Level) (cvjLps : List ConLeche.Name) (args : List Expr) (rP : Nat) :
    (ConLeche.recFireComparands rl cnP lps us cvjLps args rP).1 = cmpLevels rl lps us cvjLps := by
  unfold cmpLevels ConLeche.recFireComparands; cases rl.fire <;> rfl

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:1140-1162 recFireComparands — the level
comparands at a nested rule. -/
theorem cmpLevels_nested (c : ConLeche.Name) (nf : Nat) (L : List Level)
    (P : List Expr) (rr : Expr) (lps : List ConLeche.Name) (us : List Level)
    (cvjLps : List ConLeche.Name) :
    cmpLevels ⟨c, nf, .nested L P, rr⟩ lps us cvjLps = L.map (Level.subst lps us) := rfl

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:1140-1162 recFireComparands — the level
comparands at a plain rule. -/
theorem cmpLevels_plain (c : ConLeche.Name) (nf : Nat) (rr : Expr)
    (lps : List ConLeche.Name) (us : List Level) (cvjLps : List ConLeche.Name) :
    cmpLevels ⟨c, nf, .plain, rr⟩ lps us cvjLps = cvjLps.map (paramLvlFn lps us) := rfl

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:1140-1162 recFireComparands — the level
comparands at a rule with stored levels. -/
theorem cmpLevels_levels (c : ConLeche.Name) (nf : Nat) (L : List Level) (rr : Expr)
    (lps : List ConLeche.Name) (us : List Level) (cvjLps : List ConLeche.Name) :
    cmpLevels ⟨c, nf, .levels L, rr⟩ lps us cvjLps = L.map (Level.subst lps us) := rfl

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:906-920 recFireComparands —
`substLevelsAt_spec` at whatever the level list denotes. -/
theorem substLevelsAt_specA (ks : List ConLeche.Name) (vs : List Level)
    (lvls : List LIdx) (s₀ : AState) (hok : CheckOK eager env fe s₀)
    (hL : (denoteLList s₀.store.ls lvls).isSome = true) :
    ⦃fun s => s = s₀⦄ ConRon.Arena.substLevelsAt ks vs lvls
    ⦃fun r s' => CheckOK eager env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧
        MapRel (List.map (Level.subst ks vs)) (denoteLList s₀.store.ls lvls)
          (denoteLList s'.store.ls r); ⊤⦄ := by
  obtain ⟨L, hL⟩ := Option.isSome_iff_exists.mp hL
  rw [hL]
  exact substLevelsAt_spec ks vs lvls s₀ L hok hL

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:906-920 recFireComparands —
`substParamLevels_spec` at whatever the name list denotes. -/
theorem substParamLevels_specA (ks : List ConLeche.Name) (vs : List Level)
    (ps : List NIdx) (s₀ : AState) (hok : CheckOK eager env fe s₀)
    (hcs : (Frontend.denoteNList s₀.store.ns ps).isSome = true) :
    ⦃fun s => s = s₀⦄ ConRon.Arena.substParamLevels ks vs ps
    ⦃fun r s' => CheckOK eager env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧
        MapRel (List.map (paramLvlFn ks vs)) (Frontend.denoteNList s₀.store.ns ps)
          (denoteLList s'.store.ls r); ⊤⦄ := by
  obtain ⟨cs, hcs⟩ := Option.isSome_iff_exists.mp hcs
  rw [hcs]
  exact substParamLevels_spec ks vs ps s₀ cs hok hcs

/-- con-leche: none — a level-list node's denotation is its list's. -/
theorem denoteLsView_eq (st : EStore) (v : LsNodeView) :
    denoteLsView st.lss v = denoteLList st.ls v := rfl

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:906-920 recFireComparands — **THEOREM 1 for
`recFireLevels`**: the LEVEL comparands, substituted and interned. -/
theorem recFireLevels_spec (s₀ : AState) (rl : IRecRule) (rl' : RecRule)
    (lps : List NIdx) (us : LsIdx) (cvjLps : List NIdx)
    (ks : List ConLeche.Name) (vs : List Level) (cs : List ConLeche.Name)
    (hok : CheckOK eager env fe s₀)
    (hrl : Frontend.denoteRule s₀.store rl = some rl')
    (hks : Frontend.denoteNList s₀.store.ns lps = some ks)
    (hvs : denoteLs s₀.store.lss us = some vs)
    (hcs : Frontend.denoteNList s₀.store.ns cvjLps = some cs) :
    ⦃fun s => s = s₀⦄ ConRon.Arena.recFireLevels rl lps us cvjLps
    ⦃fun r s' => CheckOK eager env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧
        denoteLs s'.store.lss r = some (cmpLevels rl' ks vs cs); ⊤⦄ := by
  obtain ⟨c, f, rr, _hc, hf, _hr, rfl⟩ := denoteRule_eq hrl
  cases hfire : rl.fire with
  | nested lvls pins =>
    rw [hfire] at hf
    obtain ⟨Lv, Ps, hLv, _, rfl⟩ : ∃ Lv Ps,
        denoteLList s₀.store.ls lvls = some Lv ∧
        Frontend.denoteEList s₀.store pins = some Ps ∧ f = .nested Lv Ps := by
      simp only [Frontend.denoteFire] at hf
      split at hf
      · rename_i Lv Ps h1 h2; cases hf; exact ⟨Lv, Ps, h1, h2, rfl⟩
      · simp at hf
    sym only [bridge_grind, cmpLevels_nested, CheckOK.readN' hok, → CheckOK.readLs', lsViewOK_of_denoteLList,
        denoteLsView_eq] =>
      vcgen [ConRon.Arena.recFireLevels, substLevelsAt_specA (eager := eager) (env := env) (fe := fe),
        internLsNode_okS (eager := eager) (env := env) (fe := fe)] <;> finish
  | plain =>
    rw [hfire] at hf
    obtain rfl : f = .plain := by simpa [Frontend.denoteFire] using hf.symm
    sym only [bridge_grind, cmpLevels_plain, CheckOK.readN' hok, → CheckOK.readLs', lsViewOK_of_denoteLList,
        denoteLsView_eq] =>
      vcgen [ConRon.Arena.recFireLevels, substParamLevels_specA (eager := eager) (env := env) (fe := fe),
        internLsNode_okS (eager := eager) (env := env) (fe := fe)] <;> finish
  | levels lvls =>
    rw [hfire] at hf
    obtain ⟨Lv, hLv, rfl⟩ : ∃ Lv, denoteLList s₀.store.ls lvls = some Lv ∧ f = .levels Lv := by
      simp only [Frontend.denoteFire, Option.map_eq_some_iff] at hf
      obtain ⟨Lv, h1, h2⟩ := hf; exact ⟨Lv, h1, h2.symm⟩
    sym only [bridge_grind, cmpLevels_levels, CheckOK.readN' hok, → CheckOK.readLs', lsViewOK_of_denoteLList,
        denoteLsView_eq] =>
      vcgen [ConRon.Arena.recFireLevels, substLevelsAt_specA (eager := eager) (env := env) (fe := fe),
        internLsNode_okS (eager := eager) (env := env) (fe := fe)] <;> finish

/-- `defEqList`'s answer at two optional subject lists -/
@[expose] def DefEqLAns (mode : CheckMode) (eager : Bool) (env : Env) (d : Nat) (r : Bool) :
    Option (List Expr) → Option (List Expr) → Prop
  | some xs, some ys => SimBOp (defEqListOp mode eager env d xs ys) r
  | _, _ => True

/-- con-leche: none — `DefEqLAns` at two denoting lists. -/
@[bridge_grind =] theorem DefEqLAns.some_eq (d : Nat) (r : Bool) (xs ys : List Expr) :
    DefEqLAns mode eager env d r (some xs) (some ys) = SimBOp (defEqListOp mode eager env d xs ys) r := rfl

/-- con-leche: ConLeche/Kernel/Core.lean:245-254 defEqList — `defEqList_specA` at
whatever the two lists denote. -/
theorem defEqList_specB {fuel : Nat} (hsim : KnotSpec eager env fe fuel) (d : Nat)
    (as bs : List EIdx) (s₀ : AState) (hok : CheckOK eager env fe s₀)
    (ha : OptAllWS d (Frontend.denoteEList s₀.store as))
    (hb : OptAllWS d (Frontend.denoteEList s₀.store bs)) :
    ⦃fun s => s = s₀⦄
      ConRon.Arena.defEqList (coreKnot .verified eager fe id fuel) fe d as bs
    ⦃fun r s' => CheckOK eager env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧
        DefEqLAns .verified eager env d r (Frontend.denoteEList s₀.store as)
          (Frontend.denoteEList s₀.store bs); ⊤⦄ := by
  cases hxs : Frontend.denoteEList s₀.store as with
  | none => rw [hxs] at ha; exact ha.elim
  | some xs =>
  cases hys : Frontend.denoteEList s₀.store bs with
  | none => rw [hys] at hb; exact hb.elim
  | some ys =>
  rw [hxs] at ha; rw [hys] at hb
  exact defEqList_specA hsim d as bs xs ys s₀ hok hxs hys ha hb

/-- con-leche: none — a suffix of a well-scoped list is well-scoped. -/
theorem allWS_drop {d : Nat} {xs : List Expr} (h : AllWS d xs) (n : Nat) :
    AllWS d (xs.drop n) := fun x hx => h x (List.mem_of_mem_drop hx)
grind_pattern [bridge_grind] allWS_drop => AllWS d xs, xs.drop n


/-- con-leche's `iotaIndexOk` at its fixed arguments, as a fuelled run -/
def iotaIndexOkOp (mode : CheckMode) (eager : Bool) (env : Env) (d mI rP cnP : Nat) (ty : Expr)
    (ms is : List Expr) : Nat → CheckM Bool :=
  fun F => ConLeche.iotaIndexOkFueled mode eager env F d mI rP cnP ty ms is

/-- con-leche: ConLeche/Kernel/Core.lean:282-288 iotaIndexOk — no indices to compare. -/
theorem iotaIndexOk_rP {d mI rP cnP : Nat} {ty : Expr} {ms is : List Expr}
    (h : mI = rP) : SimBOp (iotaIndexOkOp mode eager env d mI rP cnP ty ms is) true :=
  ⟨0, by simp [iotaIndexOkOp, ConLeche.iotaIndexOkFueled, ConLeche.iotaIndexOk, h]; rfl⟩
grind_pattern [bridge_grind] iotaIndexOk_rP => iotaIndexOkOp mode eager env d mI rP cnP ty ms is

/-- con-leche: ConLeche/Kernel/Core.lean:282-288 iotaIndexOk — the constructor telescope
is too short. -/
theorem iotaIndexOk_none {d mI rP cnP : Nat} {ty : Expr} {ms is : List Expr}
    (h : mI ≠ rP) (hn : piResAt ms ty = none) :
    SimBOp (iotaIndexOkOp mode eager env d mI rP cnP ty ms is) false :=
  ⟨0, by
    simp only [iotaIndexOkOp, ConLeche.iotaIndexOkFueled, ConLeche.iotaIndexOk, h,
      ite_false]
    simp only [piResAt] at hn; rw [hn]; rfl⟩
grind_pattern [bridge_grind] iotaIndexOk_none => iotaIndexOkOp mode eager env d mI rP cnP ty ms is

/-- con-leche: ConLeche/Kernel/Core.lean:282-288 iotaIndexOk — the residual's indices
against the redex's. -/
theorem iotaIndexOk_some {d mI rP cnP : Nat} {ty e : Expr} {ms is : List Expr} {b : Bool}
    (h : mI ≠ rP) (hs : piResAt ms ty = some e)
    (hd : SimBOp (defEqListOp mode eager env d (e.getAppArgs.drop cnP) is) b) :
    SimBOp (iotaIndexOkOp mode eager env d mI rP cnP ty ms is) b := by
  obtain ⟨F, hF⟩ := hd
  refine ⟨F, ?_⟩
  simp only [piResAt] at hs
  simp only [iotaIndexOkOp, ConLeche.iotaIndexOkFueled, ConLeche.iotaIndexOk, h, ite_false, hs]
  exact hF
grind_pattern [bridge_grind] iotaIndexOk_some =>
  iotaIndexOkOp mode eager env d mI rP cnP ty ms is, SimBOp (defEqListOp mode eager env d (e.getAppArgs.drop cnP) is) b

/-- con-leche: none — con-leche's `piResidual_WScoped` at `piResAt`. -/
theorem piResAt_WScoped {d : Nat} {xs : List Expr} {t e : Expr} (h : piResAt xs t = some e)
    (hw : Expr.WScoped d t) (hxs : AllWS d xs) : Expr.WScoped d e :=
  ConLeche.piResidual_WScoped h hw hxs
grind_pattern [bridge_grind] piResAt_WScoped => piResAt xs t, some e, Expr.WScoped d t where
  guard piResAt xs t = some e

/-- con-leche: ConLeche/Kernel/Core.lean:282-288 iotaIndexOk — **THEOREM 1 for
`iotaIndexOk`**: the canonical-index comparison of a firing redex. -/
theorem iotaIndexOk_spec {fuel : Nat} (hsim : KnotSpec eager env fe fuel)
    (s₀ : AState) (d mI rP cnP : Nat) (tyC : EIdx) (margs idx : List EIdx)
    (ty : Expr) (ms is : List Expr)
    (hok : CheckOK eager env fe s₀) (hty : denoteE s₀.store tyC = some ty)
    (hms : Frontend.denoteEList s₀.store margs = some ms)
    (his : Frontend.denoteEList s₀.store idx = some is)
    (hwty : Expr.WScoped d ty) (hwms : AllWS d ms) (hwis : AllWS d is) :
    ⦃fun s => s = s₀⦄
      ConRon.Arena.iotaIndexOk (coreKnot .verified eager fe id fuel) fe d mI rP cnP tyC
        margs idx
    ⦃fun r s' => CheckOK eager env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧
        SimBOp (iotaIndexOkOp .verified eager env d mI rP cnP ty ms is) r; ⊤⦄ := by
  sym only [bridge_grind] =>
    vcgen [ConRon.Arena.iotaIndexOk, piResidual_specA (eager := eager) (env := env) (fe := fe) (xs := ms), ExprOps.getAppArgs_spec,
      defEqList_specB hsim] <;> finish

/-! ### `iotaRec`'s pure side at its exits

Each exit is con-leche's `iotaRec` at a subject `E` whose spine head and
arguments are known (`hE1`, `hE2`), with the facts the twin's stages name. -/

/-- con-leche: ConLeche/Kernel/Core.lean:786-868 iotaRec — the head is not a
constant. -/
theorem iotaRecFueled_nohead {F d : Nat} {E : Expr}
    (hE1 : ∀ c us, E.getAppFn ≠ .const c us) :
    ConLeche.iotaRecFueled mode eager env F d E = .ok none := by
  simp only [ConLeche.iotaRecFueled, ConLeche.iotaRec]
  first
    | rfl
    | (split
       · rename_i c us heq; exact absurd heq (hE1 c us)
       · rfl)

/-- con-leche: ConLeche/Kernel/Core.lean:786-868 iotaRec — the head is not a
stored recursor. -/
theorem iotaRecFueled_norec {F d : Nat} {E : Expr} {c : ConLeche.Name}
    {us : List Level} (hE1 : E.getAppFn = .const c us)
    (hf : ∀ cv mI rP isK rules, env.find? c ≠ some (.recInfo cv mI rP isK rules)) :
    ConLeche.iotaRecFueled mode eager env F d E = .ok none := by
  simp only [ConLeche.iotaRecFueled, ConLeche.iotaRec, hE1]
  first
    | rfl
    | (split
       · rename_i cv mI rP isK rules heq; exact absurd heq (hf cv mI rP isK rules)
       · rfl)

/-- con-leche: ConLeche/Kernel/Core.lean:786-868 iotaRec — the arity, level or
telescope-arity guard fails. -/
theorem iotaRecFueled_guard {F d : Nat} {E : Expr} {c : ConLeche.Name}
    {us : List Level} {cv : ConstantVal} {mI rP : Nat} {isK : Bool} {rules : List RecRule}
    (hE1 : E.getAppFn = .const c us)
    (hf : env.find? c = some (.recInfo cv mI rP isK rules))
    (hg : ¬ (E.getAppArgs.length = mI + 1 ∧ us.length = cv.levelParams.length ∧
      (Expr.peelPis (mI + 1) cv.type).isSome = true)) :
    ConLeche.iotaRecFueled mode eager env F d E = .ok none := by
  simp only [ConLeche.iotaRecFueled, ConLeche.iotaRec, hE1, hf]
  rw [ite_eq_right hg]
  rfl

/-- con-leche: ConLeche/Kernel/Core.lean:789-888 iotaRec — **the ι case
split's certificate family** at fuel `F`: off at the trusted mode; at a case-3
redex (`iotaCase3At`, a knot walk) the level comparison, the parameter
comparison, the constructor telescope at the full grade and the index
comparison.  A copy of the con-leche text that `iotaRecFueled_pre` ties to it
by `rfl`. -/
def iotaFam (mode : CheckMode) (eager : Bool) (env : Env) (F d mI rP : Nat) (isK : Bool)
    (cvj : ConstantVal) (cnP : Nat) (usj : List Level) (cmp : List Level × List Expr)
    (margs args : List Expr) : CheckM Bool :=
  if mode.verifiedChecks then
    (iotaCase3At (ConLeche.pureFns mode eager env F).whnf env.find? isK cvj cmp.1 >>= fun c3 =>
      if c3 then do
        if ← ConLeche.liftFueled "level comparison" (Level.isEquivList usj cmp.1) then
          if ← ConLeche.defEqListFueled mode eager env F d (margs.take cnP) cmp.2 then
            if ← ConLeche.iotaCertsFullFueled mode eager env F d
                (cvj.type.instantiateLevelParams cvj.levelParams usj) margs then
              ConLeche.iotaIndexOkFueled mode eager env F d mI rP cnP
                (cvj.type.instantiateLevelParams cvj.levelParams usj)
                margs ((args.take mI).drop rP)
            else pure false
          else pure false
        else pure false
      else pure true)
  else pure true

/-- con-leche: ConLeche/Kernel/Core.lean:789-888 iotaRec — past the guard and
the major's preparation, as a function of the prepared major: every later exit
is a statement about this tail. -/
def iotaTail (mode : CheckMode) (eager : Bool) (env : Env) (F d : Nat) (us : List Level)
    (cv : ConstantVal) (mI rP : Nat) (isK : Bool) (rules : List RecRule) (args : List Expr)
    (major : Expr) : CheckM (Option Expr) :=
  match major.getAppFn with
  | .const cj usj =>
    match env.find? cj with
    | some (.ctorInfo cvj cnP _) =>
      match rules.find? (fun r' => r'.ctor == cj) with
      | some rl =>
        let margs := major.getAppArgs
        if margs.length = cnP + rl.nfields then do
          if ← iotaFam mode eager env F d mI rP isK cvj cnP usj
              (ConLeche.recFireComparands rl cnP cv.levelParams us cvj.levelParams
                args rP) margs args then
            pure (some (Expr.mkAppN
              (rl.rhs.instantiateLevelParams cv.levelParams us)
              (args.take rP ++ margs.drop cnP)))
          else pure none
        else pure none
      | none => pure none
    | _ => pure none
  | _ => pure none

/-- con-leche: ConLeche/Kernel/Core.lean:789-888 iotaRec — the prefix: head,
recursor, guard, the prepared major; the rest is `iotaTail`. -/
theorem iotaRecFueled_pre {F d : Nat} {E : Expr} {c : ConLeche.Name}
    {us : List Level} {cv : ConstantVal} {mI rP : Nat} {isK : Bool} {rules : List RecRule}
    {major : Expr}
    (hE1 : E.getAppFn = .const c us)
    (hf : env.find? c = some (.recInfo cv mI rP isK rules))
    (hg : E.getAppArgs.length = mI + 1 ∧ us.length = cv.levelParams.length ∧
      (Expr.peelPis (mI + 1) cv.type).isSome = true)
    (hpm : ConLeche.prepareMajorFueled mode eager env F d c isK rules
      (E.getAppArgs.getD mI (.bvar 0)) = .ok major) :
    ConLeche.iotaRecFueled mode eager env F d E =
      iotaTail mode eager env F d us cv mI rP isK rules E.getAppArgs major := by
  have hpm' : ConLeche.prepareMajor mode (ConLeche.pureFns mode eager env F) env d c
      isK rules (E.getAppArgs.getD mI (.bvar 0)) = .ok major := hpm
  simp only [ConLeche.iotaRecFueled, ConLeche.iotaRec, hE1, hf]
  rw [ite_eq_left hg]
  simp only [hpm', bind, Except.bind]
  rfl

/-- con-leche: ConLeche/Kernel/Core.lean:786-868 iotaRec — the prepared
major's head is not a constant. -/
theorem iotaTail_nohead {F d : Nat} {us : List Level} {cv : ConstantVal}
    {mI rP : Nat} {isK : Bool} {rules : List RecRule} {args : List Expr} {major : Expr}
    (hm : ∀ cj usj, major.getAppFn ≠ .const cj usj) :
    iotaTail mode eager env F d us cv mI rP isK rules args major = .ok none := by
  simp only [iotaTail]
  first
    | rfl
    | (split
       · rename_i c us heq; exact absurd heq (hm c us)
       · rfl)

/-- con-leche: ConLeche/Kernel/Core.lean:786-868 iotaRec — the head is not a
stored constructor. -/
theorem iotaTail_noctor {F d : Nat} {us : List Level} {cv : ConstantVal}
    {mI rP : Nat} {isK : Bool} {rules : List RecRule} {args : List Expr} {major : Expr}
    {cj : ConLeche.Name} {usj : List Level}
    (hm : major.getAppFn = .const cj usj)
    (hf : ∀ cvj a b, env.find? cj ≠ some (.ctorInfo cvj a b)) :
    iotaTail mode eager env F d us cv mI rP isK rules args major = .ok none := by
  simp only [iotaTail, hm]
  first
    | rfl
    | (split
       · rename_i cvj a b heq; exact absurd heq (hf cvj a b)
       · rfl)

/-- con-leche: ConLeche/Kernel/Core.lean:786-868 iotaRec — no rule matches the
constructor. -/
theorem iotaTail_norule {F d : Nat} {us : List Level} {cv : ConstantVal}
    {mI rP : Nat} {isK : Bool} {rules : List RecRule} {args : List Expr} {major : Expr}
    {cj : ConLeche.Name} {usj : List Level} {cvj : ConstantVal} {a b : Nat}
    (hm : major.getAppFn = .const cj usj)
    (hf : env.find? cj = some (.ctorInfo cvj a b))
    (hr : rules.find? (fun r' => r'.ctor == cj) = none) :
    iotaTail mode eager env F d us cv mI rP isK rules args major = .ok none := by
  simp only [iotaTail, hm, hf, hr]
  rfl

/-- con-leche: ConLeche/Kernel/Core.lean:786-868 iotaRec — the constructor is
not fully applied. -/
theorem iotaTail_len {F d : Nat} {us : List Level} {cv : ConstantVal}
    {mI rP : Nat} {isK : Bool} {rules : List RecRule} {args : List Expr} {major : Expr}
    {cj : ConLeche.Name} {usj : List Level} {cvj : ConstantVal} {a b : Nat}
    {rl : RecRule}
    (hm : major.getAppFn = .const cj usj)
    (hf : env.find? cj = some (.ctorInfo cvj a b))
    (hr : rules.find? (fun r' => r'.ctor == cj) = some rl)
    (hl : ¬ major.getAppArgs.length = a + rl.nfields) :
    iotaTail mode eager env F d us cv mI rP isK rules args major = .ok none := by
  simp only [iotaTail, hm, hf, hr]
  rw [ite_eq_right hl]
  rfl

/-- con-leche: ConLeche/Kernel/Core.lean:786-868 iotaRec — **the firing
block**, as a function of the certificate family's verdict. -/
theorem iotaTail_fire {F d : Nat} {us : List Level} {cv : ConstantVal}
    {mI rP : Nat} {isK : Bool} {rules : List RecRule} {args : List Expr} {major : Expr}
    {cj : ConLeche.Name} {usj : List Level} {cvj : ConstantVal} {a b : Nat}
    {rl : RecRule} {fam : Bool}
    (hm : major.getAppFn = .const cj usj)
    (hf : env.find? cj = some (.ctorInfo cvj a b))
    (hr : rules.find? (fun r' => r'.ctor == cj) = some rl)
    (hl : major.getAppArgs.length = a + rl.nfields)
    (hfam : iotaFam mode eager env F d mI rP isK cvj a usj
      (ConLeche.recFireComparands rl a cv.levelParams us cvj.levelParams args rP)
      major.getAppArgs args = .ok fam) :
    iotaTail mode eager env F d us cv mI rP isK rules args major =
      .ok (if fam then
        some (Expr.mkAppN (rl.rhs.instantiateLevelParams cv.levelParams us)
          (args.take rP ++ major.getAppArgs.drop a))
      else none) := by
  simp only [iotaTail, hm, hf, hr]
  rw [ite_eq_left hl]
  simp only [hfam, bind, Except.bind]
  cases fam <;> rfl

/-- con-leche: none — the certificate family's pure side is fuel-monotone. -/
theorem iotaFam_mono {F G d mI rP : Nat} {isK : Bool} {cvj : ConstantVal} {cnP : Nat}
    {usj : List Level} {cmp : List Level × List Expr} {margs args : List Expr}
    {b : Bool} (hle : F ≤ G)
    (h : iotaFam mode eager env F d mI rP isK cvj cnP usj cmp margs args = .ok b) :
    iotaFam mode eager env G d mI rP isK cvj cnP usj cmp margs args = .ok b := by
  unfold iotaFam at h ⊢
  by_cases hv : mode.verifiedChecks = true
  case neg => rw [ite_eq_right hv] at h ⊢; exact h
  rw [ite_eq_left hv] at h ⊢
  cases hc : iotaCase3At (ConLeche.pureFns mode eager env F).whnf env.find? isK cvj cmp.1 with
  | error e => rw [hc] at h; cases h
  | ok c3 =>
  rw [hc] at h
  rw [iotaCase3AtFueled_mono hle hc]
  simp only [bind, Except.bind] at h ⊢
  cases c3
  · exact h
  simp only [ite_true] at h ⊢
  cases hl : Level.isEquivList usj cmp.1 with
  | none =>
    simp [ConLeche.liftFueled, hl] at h
  | some b1 =>
    simp only [ConLeche.liftFueled, hl, pure, Except.pure] at h ⊢
    cases b1
    · exact h
    simp only [ite_true] at h ⊢
    cases h2 : ConLeche.defEqListFueled mode eager env F d (margs.take cnP) cmp.2 with
    | error e => rw [h2] at h; cases h
    | ok b2 =>
      rw [h2] at h
      rw [defEqListFueled_mono hle h2]
      cases b2
      · exact h
      simp only [ite_true] at h ⊢
      cases h3 : ConLeche.iotaCertsFullFueled mode eager env F d
          (cvj.type.instantiateLevelParams cvj.levelParams usj) margs with
      | error e => rw [h3] at h; cases h
      | ok b3 =>
        rw [h3] at h
        rw [iotaCertsFullFueled_mono hle h3]
        cases b3
        · exact h
        simp only [ite_true] at h ⊢
        exact iotaIndexOkFueled_mono hle h

/-- con-leche: none — the family off case 3. -/
theorem iotaFam_true {F d mI rP : Nat} {isK : Bool} {cvj : ConstantVal} {cnP : Nat}
    {usj : List Level} {cmp : List Level × List Expr} {margs args : List Expr}
    (h : iotaCase3At (ConLeche.pureFns .verified eager env F).whnf env.find? isK cvj cmp.1 =
      .ok false) :
    iotaFam .verified eager env F d mI rP isK cvj cnP usj cmp margs args = .ok true := by
  unfold iotaFam
  simp only [CheckMode.verifiedChecks, ite_true, h, bind, Except.bind, Bool.false_eq_true,
    ite_false]; rfl

/-- con-leche: none — the family past case 3's test, as a function of the
four verdicts. -/
theorem iotaFam_fire {F d mI rP : Nat} {isK : Bool} {cvj : ConstantVal} {cnP : Nat}
    {usj : List Level} {cmp : List Level × List Expr} {margs args : List Expr}
    {b1 b2 b3 b4 : Bool}
    (hc : iotaCase3At (ConLeche.pureFns .verified eager env F).whnf env.find? isK cvj cmp.1 =
      .ok true)
    (h1 : Level.isEquivList usj cmp.1 = some b1)
    (h2 : b1 = true → ConLeche.defEqListFueled .verified eager env F d
      (margs.take cnP) cmp.2 = .ok b2)
    (h3 : b1 = true → b2 = true → ConLeche.iotaCertsFullFueled .verified eager env F d
      (cvj.type.instantiateLevelParams cvj.levelParams usj) margs = .ok b3)
    (h4 : b1 = true → b2 = true → b3 = true → ConLeche.iotaIndexOkFueled .verified eager
      env F d mI rP cnP
      (cvj.type.instantiateLevelParams cvj.levelParams usj) margs
      ((args.take mI).drop rP) = .ok b4) :
    iotaFam .verified eager env F d mI rP isK cvj cnP usj cmp margs args =
      .ok (b1 && b2 && b3 && b4) := by
  unfold iotaFam
  have hv : CheckMode.verified.verifiedChecks = true := rfl
  rw [ite_eq_left hv]
  simp only [hc, bind, Except.bind, ite_true]
  simp only [ConLeche.liftFueled, h1, pure, Except.pure]
  cases b1
  · rfl
  simp only [ite_true, h2 rfl]
  cases b2
  · rfl
  simp only [ite_true, h3 rfl rfl]
  cases b3
  · rfl
  simp only [ite_true, h4 rfl rfl rfl]
  cases b4 <;> rfl

/-! ### The twin side's index and rule facts -/

/-- con-leche: ConLeche/Verify/SimI.lean:54 ISOK — the index's HIT half at a
recursor. -/
theorem env_rec_of_index {s : AState} (hok : CheckOK eager env fe s)
    {c : NIdx} {cn : ConLeche.Name} {icv : IConstantVal} {mI rP : Nat} {isK : Bool}
    {rules : List IRecRule} (hn : denoteN s.store.ns c = some cn)
    (hfd : fe.find? c = some (.recInfo icv mI rP isK rules)) :
    ∃ dcv drules, Frontend.denoteCV s.store icv = some dcv ∧
      Frontend.denoteRules s.store rules = some drules ∧
      env.find? cn = some (.recInfo dcv mI rP isK drules) := by
  obtain ⟨nm', cc, hn', hci, hfind⟩ := hok.ienv.hit c _ hfd
  obtain rfl := Option.some.inj (hn'.symm.trans hn)
  simp only [Frontend.denoteCI] at hci
  split at hci
  · rename_i dcv dr hdcv hdr
    cases hci
    exact ⟨dcv, dr, hdcv, hdr, hfind⟩
  · simp at hci

/-- con-leche: ConLeche/Verify/SimI.lean:54 ISOK — the MISS half at a
recursor. -/
theorem env_not_rec_of_index {s : AState} (hok : CheckOK eager env fe s)
    {c : NIdx} {cn : ConLeche.Name} (hn : denoteN s.store.ns c = some cn)
    (hnd : ∀ v mI rP k rs, fe.find? c ≠ some (.recInfo v mI rP k rs)) :
    ∀ cv mI rP k rs, env.find? cn ≠ some (.recInfo cv mI rP k rs) := by
  intro cv mI rP k rs hcon
  cases hf : fe.find? c with
  | none => rw [IFEnvOK.miss hok.state hok.ienv hn hf] at hcon; simp at hcon
  | some ci =>
    obtain ⟨nm', cc, hn', hci, hfind⟩ := hok.ienv.hit c ci hf
    obtain rfl := Option.some.inj (hn'.symm.trans hn)
    rw [hfind] at hcon
    obtain rfl := Option.some.inj hcon
    cases ci with
    | recInfo v mI' rP' k' rs' => exact hnd v mI' rP' k' rs' hf
    | _ =>
      simp only [Frontend.denoteCI] at hci
      first
        | (simp at hci)
        | (split at hci <;> simp at hci)

/-- con-leche: ConLeche/Kernel/Core.lean:797-910 iotaRec — `findRule` IS the
rule lookup `rules.find? (fun r' => r'.ctor == cj)`, across the denotation. -/
theorem findRule_denote {st : EStore} (hwf : StoreWF st) {cj : NIdx}
    {cjn : ConLeche.Name} (hcj : denoteN st.ns cj = some cjn) :
    ∀ {rules : List IRecRule} {rules' : List RecRule},
      Frontend.denoteRules st rules = some rules' →
      (∀ rl, ConRon.Arena.findRule rules cj = some rl →
        ∃ rl', Frontend.denoteRule st rl = some rl' ∧
          rules'.find? (fun r => r.ctor == cjn) = some rl') ∧
      (ConRon.Arena.findRule rules cj = none →
        rules'.find? (fun r => r.ctor == cjn) = none)
  | [], rules', h => by
    simp only [Frontend.denoteRules, Option.some.injEq] at h
    subst h
    exact ⟨fun rl h => by simp [ConRon.Arena.findRule] at h, fun _ => rfl⟩
  | r :: rs, rules', h => by
    simp only [Frontend.denoteRules] at h
    split at h
    · rename_i x xs hx hxs
      cases h
      obtain ⟨hr1, hr2⟩ := findRule_denote hwf hcj hxs
      obtain ⟨_, hc, _, _⟩ := rule_denote hx
      obtain ⟨rk, hrk⟩ := hwf
      have hbeq : (r.ctor == cj) = (x.ctor == cjn) := beq_of_denoteN hrk.nsWF hc hcj
      by_cases hb : (r.ctor == cj) = true
      · have hb' : (x.ctor == cjn) = true := hbeq ▸ hb
        refine ⟨fun rl hrl => ?_, fun hn => ?_⟩
        · simp only [ConRon.Arena.findRule, hb, ite_true, Option.some.injEq] at hrl
          subst hrl
          exact ⟨x, hx, by simp [List.find?, hb']⟩
        · simp [ConRon.Arena.findRule, hb] at hn
      · have hb' : (x.ctor == cjn) = false := by rw [← hbeq]; simpa using hb
        have hbf : (r.ctor == cj) = false := by simpa using hb
        refine ⟨fun rl hrl => ?_, fun hn => ?_⟩
        · simp only [ConRon.Arena.findRule, hbf, Bool.false_eq_true, ite_false] at hrl
          obtain ⟨rl', h1, h2⟩ := hr1 rl hrl
          exact ⟨rl', h1, by simp [List.find?, hb', h2]⟩
        · simp only [ConRon.Arena.findRule, hbf, Bool.false_eq_true, ite_false] at hn
          simp [List.find?, hb', hr2 hn]
    · simp at h

/-- con-leche: none — an in-range `getD` of a denoting list denotes the
`getD` of the denotation, whatever the two defaults. -/
theorem denoteEList_getD_lt {st : EStore} :
    ∀ {hs : List EIdx} {xs : List Expr}, Frontend.denoteEList st hs = some xs →
      ∀ {i : Nat}, i < hs.length → ∀ (a : EIdx) (b : Expr),
        denoteE st (hs.getD i a) = some (xs.getD i b)
  | [], _, _, _, hi, _, _ => by simp at hi
  | h :: hs, xs, hd, i, hi, a, b => by
    obtain ⟨x, xs', hx, hxs, rfl⟩ := denoteEList_cons_inv hd
    cases i with
    | zero => simpa using hx
    | succ i =>
      simp only [List.getD_cons_succ]
      exact denoteEList_getD_lt hxs (by simp at hi; omega) a b

/-- con-leche: none — `SimOOp` at a `none` answer. -/
theorem simOOp_none {P : Nat → CheckM (Option Expr)} {d F : Nat} {st : EStore}
    (h : P F = .ok none) : SimOOp P d st none :=
  ⟨none, rfl, fun _ hx => absurd hx (by simp), F, h⟩

/-- con-leche: ConLeche/Kernel/Core.lean:786-868 iotaRec — **the ι case
split's certificate family** (task #342 L10, S5c): nothing at a K rule or a family never `Prop` at the comparand levels, and at
a case-3 redex the level comparison, the parameter comparison, the
constructor telescope at the full grade and the index comparison. -/
theorem iotaFam_spec {α : Type} {fuel : Nat} (henv : ConLeche.EnvWF env)
    (hsim : KnotSpec eager env fe fuel)
    (s₁ : AState) (d : Nat) (icv icvj : IConstantVal)
    (us usj : LsIdx) (isK : Bool) (rl : IRecRule) (args margs : List EIdx)
    (mI rP : Nat) (ls lsj : List Level) (dcv dcvj : ConstantVal)
    (cjn : ConLeche.Name) (cnP cnF : Nat) (rl' : RecRule) (xs ms : List Expr)
    (hok : CheckOK eager env fe s₁)
    (hls : denoteLs s₁.store.lss us = some ls)
    (hlsj : denoteLs s₁.store.lss usj = some lsj)
    (hdcv : Frontend.denoteCV s₁.store icv = some dcv)
    (hdcvj : Frontend.denoteCV s₁.store icvj = some dcvj)
    (hfindj : env.find? cjn = some (.ctorInfo dcvj cnP cnF))
    (hms : Frontend.denoteEList s₁.store margs = some ms)
    (hxs : Frontend.denoteEList s₁.store args = some xs)
    (hrl' : Frontend.denoteRule s₁.store rl = some rl')
    (hwxs : ∀ z ∈ xs, Expr.WScoped d z) (hwms : ∀ z ∈ ms, Expr.WScoped d z)
    (hcmpW : ∀ z ∈ (ConLeche.recFireComparands rl' cnP dcv.levelParams ls
      dcvj.levelParams xs rP).2, Expr.WScoped d z)
    (k : Bool → AM α) (Q : α → AState → Prop)
    (hk : ∀ b s, (CheckOK eager env fe s ∧ Ext s₁.store s.store ∧
        s.pins = s₁.pins ∧
        ∃ F, iotaFam .verified eager env F d mI rP isK dcvj cnP lsj
          (ConLeche.recFireComparands rl' cnP dcv.levelParams ls dcvj.levelParams
            xs rP) ms xs = .ok b) →
      ⦃fun s' => s' = s⦄ k b ⦃fun r s' => Q r s'; ⊤⦄) :
    ⦃fun s => s = s₁⦄ (do
      let fam ← if CheckMode.verified.verifiedChecks then do
        let cmpL ← ConRon.Arena.recFireLevels rl icv.levelParams us icvj.levelParams
        if ← ConRon.Arena.iotaCase3At (coreKnot .verified eager fe id fuel) fe isK icvj cmpL then do
          if ← ConRon.Arena.liftFueled "level comparison"
              (← ConRon.Arena.lvlsEq? usj cmpL) then do
            let cmpA ← ConRon.Arena.recFireArgs rl cnP icv.levelParams us args rP
            if ← ConRon.Arena.defEqList (coreKnot .verified eager fe id fuel) fe d
                (margs.take cnP) cmpA then do
              let tyC ← ConRon.Arena.constTyAt icvj usj
              if ← ConRon.Arena.iotaCertsFull (coreKnot .verified eager fe id fuel) fe d tyC
                  margs then
                ConRon.Arena.iotaIndexOk (coreKnot .verified eager fe id fuel) fe d mI rP
                  cnP tyC margs ((args.take mI).drop rP)
              else pure false
            else pure false
          else pure false
        else pure true
      else pure true
      k fam : AM α)
    ⦃fun r s' => Q r s'; ⊤⦄ := by
  obtain ⟨_, hlps, _⟩ := denoteCV_inv hdcv
  obtain ⟨_, hlpsj, _⟩ := denoteCV_inv hdcvj
  have hnamej : dcvj.name = cjn := env_find_name hfindj
  have hv : CheckMode.verified.verifiedChecks = true := rfl
  rw [ite_eq_left hv]
  refine triple_seq (recFireLevels_spec s₁ rl rl' icv.levelParams us
    icvj.levelParams dcv.levelParams ls dcvj.levelParams hok hrl' hlps hls
    hlpsj) ?_
  rintro cmpL s2 ⟨hok2, hx2, hp2, hcL⟩
  have hcL2 : denoteLs s2.store.lss cmpL = some (ConLeche.recFireComparands rl' cnP
      dcv.levelParams ls dcvj.levelParams xs rP).1 := by rw [recFireComparands_fst]; exact hcL
  refine triple_seq (iotaCase3At_spec hsim henv s2 isK icvj dcvj cmpL _ hok2
    (denoteCV_ext hdcvj hx2) hcL2) ?_
  rintro c3 s3 ⟨hok3, hx23, hp3, F0, hF0⟩
  have hx13 : Ext s₁.store s3.store := hx2.trans hx23
  have hp13 : s3.pins = s₁.pins := hp3.trans hp2
  by_cases hc3t : c3 = true
  case neg =>
    rw [ite_eq_right hc3t, pure_bind]
    have hc3f : c3 = false := by simpa using hc3t
    subst hc3f
    exact hk _ _ ⟨hok3, hx13, hp13, F0, iotaFam_true hF0⟩
  rw [ite_eq_left hc3t]
  subst hc3t
  refine triple_seq (lvlsEq?_spec s3 usj cmpL hok3) ?_
  rintro rq s4 ⟨hok4, hst4, hp4, lu, lv, hlu, hlv, hrq⟩
  rw [denoteLs_ext hlsj hx13] at hlu
  obtain rfl := Option.some.inj hlu
  rw [denoteLs_ext hcL2 hx23] at hlv
  obtain rfl := Option.some.inj hlv
  refine triple_seq (liftFueled_spec s4 _ rq) ?_
  rintro b1 s5 ⟨hs5, hb1⟩
  subst s5
  have hx14 : Ext s₁.store s4.store := by rw [hst4]; exact hx13
  have hp14 : s4.pins = s₁.pins := hp4.trans hp13
  have h1 : Level.isEquivList lsj (ConLeche.recFireComparands rl' cnP
      dcv.levelParams ls dcvj.levelParams xs rP).1 = some b1 := by
    rw [← hrq, hb1]
  by_cases hb1t : b1 = true
  case neg =>
    rw [ite_eq_right hb1t, pure_bind]
    have hb1f : b1 = false := by simpa using hb1t
    subst hb1f
    refine hk _ _ ⟨hok4, hx14, hp14, F0, ?_⟩
    rw [iotaFam_fire (b2 := false) (b3 := false) (b4 := false) hF0 h1
      (fun h => by cases h) (fun h => by cases h) (fun h => by cases h)]
    rfl
  rw [ite_eq_left hb1t]
  subst hb1t
  refine triple_seq (recFireArgs_spec s4 rl rl' cnP icv.levelParams us args rP
    dcv.levelParams ls dcvj.levelParams xs hok4 (denoteRule_ext hrl' hx14)
    (denoteNListE_ext hx14 _ _ hlps) (denoteLs_ext hls hx14)
    (denoteEList_ext hx14 _ _ hxs)) ?_
  rintro cmpA s6 ⟨hok6, hx6, hp6, hcA⟩
  have hx16 := hx14.trans hx6
  have hp16 : s6.pins = s₁.pins := hp6.trans hp14
  have hmt := ExprOps.denoteEList_take cnP _ _ (denoteEList_ext hx16 _ _ hms)
  refine triple_seq (defEqList_spec hsim s6 d _ _ _ _ hok6 hmt hcA
    (fun z hz => hwms z (List.mem_of_mem_take hz)) hcmpW) ?_
  rintro y s7 ⟨hok7, hx7, hp7, F1, hF1⟩
  have hx17 := hx16.trans hx7
  have hp17 : s7.pins = s₁.pins := hp7.trans hp16
  by_cases hyt : y = true
  case neg =>
    rw [ite_eq_right hyt, pure_bind]
    have hyf : y = false := by simpa using hyt
    subst hyf
    refine hk _ _ ⟨hok7, hx17, hp17, max F0 F1, ?_⟩
    rw [iotaFam_fire (b1 := true) (b2 := false) (b3 := false) (b4 := false)
      (iotaCase3AtFueled_mono (Nat.le_max_left _ _) hF0) h1
      (fun _ => defEqListFueled_mono (Nat.le_max_right _ _) hF1)
      (fun _ h => by cases h) (fun _ h => by cases h)]
    rfl
  rw [ite_eq_left hyt]
  subst hyt
  refine triple_seq (constTyAt_spec s7 icvj usj cjn lsj (.ctorInfo dcvj cnP cnF)
    hok7 (by rw [denoteCV_name (denoteCV_ext hdcvj hx17), hnamej])
    (denoteLs_ext hlsj hx17) hfindj (denoteCV_ext hdcvj hx17)) ?_
  rintro tyC s8 ⟨hok8, hx8, hp8, htyC⟩
  have hwtyC : Expr.WScoped d
      (dcvj.type.instantiateLevelParams dcvj.levelParams lsj) :=
    Expr.WScoped.of_not_hasFvar (const_ty_hasFvar henv hfindj lsj)
  have hM8 := denoteEList_ext (hx17.trans hx8) _ _ hms
  refine triple_seq (iotaCertsFull_spec hsim d tyC margs s8 hok8
    ⟨_, _, htyC, hwtyC, hM8, hwms⟩) ?_
  rintro c2 s9 ⟨hok9, hx9, hp9, hc2⟩
  obtain ⟨F2, hF2⟩ := hc2 _ _ htyC hM8
  have hx19 := hx17.trans (hx8.trans hx9)
  have hp19 : s9.pins = s₁.pins := hp9.trans (hp8.trans hp17)
  by_cases hc2t : c2 = true
  case neg =>
    rw [ite_eq_right hc2t, pure_bind]
    have hc2f : c2 = false := by simpa using hc2t
    subst hc2f
    refine hk _ _ ⟨hok9, hx19, hp19, max F0 (max F1 F2), ?_⟩
    rw [iotaFam_fire (b1 := true) (b2 := true) (b3 := false) (b4 := false)
      (iotaCase3AtFueled_mono (by omega) hF0) h1
      (fun _ => defEqListFueled_mono (by omega) hF1)
      (fun _ _ => iotaCertsFullFueled_mono (by omega) hF2)
      (fun _ _ h => by cases h)]
    rfl
  rw [ite_eq_left hc2t]
  subst hc2t
  have hI := ExprOps.denoteEList_drop rP _ _
    (ExprOps.denoteEList_take mI _ _ (denoteEList_ext hx19 _ _ hxs))
  refine triple_seq (iotaIndexOk_spec hsim s9 d mI rP cnP tyC margs
    ((args.take mI).drop rP) _ _ _ hok9 (denote_ext htyC hx9)
    (denoteEList_ext hx9 _ _ hM8) hI hwtyC hwms
    (fun z hz => hwxs z (List.mem_of_mem_take (List.mem_of_mem_drop hz)))) ?_
  rintro c4 s10 ⟨hok10, hx10, hp10, F3, hF3⟩
  refine hk _ _ ⟨hok10, hx19.trans hx10, hp10.trans hp19, max F0 (max F1 (max F2 F3)), ?_⟩
  rw [iotaFam_fire (b1 := true) (b2 := true) (b3 := true) (b4 := c4)
    (iotaCase3AtFueled_mono (by omega) hF0) h1
    (fun _ => defEqListFueled_mono (by omega) hF1)
    (fun _ _ => iotaCertsFullFueled_mono (by omega) hF2)
    (fun _ _ _ => iotaIndexOkFueled_mono (by omega) hF3)]
  cases c4 <;> rfl

/-- con-leche: none — a `pure` exit at a pinned state. -/
theorem triple_pure_at {α : Type} {s₀ : AState} {v : α}
    {Q : α → AState → Prop} (h : Q v s₀) :
    ⦃fun s => s = s₀⦄ (pure v : AM α) ⦃fun r s => Q r s; ⊤⦄ := by
  vcgen
  subst_vars; exact h

/-- con-leche: ConLeche/Kernel/Core.lean:786-868 iotaRec — **THEOREM 1 for
`iotaRecAt`**: one ι step at a spine the caller already holds (task
#97-P6-9's hoist).  The held head `h` is not an application (it is a spine
head), so `getAppFn`/`getAppArgs` of `Expr.mkAppN h xs` are `h` and `xs`,
which is the equation the hoist owes.  The count `n` is the whole held
vector (`hn`): both callers pass `size`, and at a larger `n` the twin's
arity guard reads `n` where con-leche's reads the spine. -/
theorem iotaRecAt_spec {fuel : Nat}
    (henv : ConLeche.EnvWF env) (hsim : KnotSpec eager env fe fuel)
    (s₀ : AState) (d : Nat) (hd : EIdx) (sargs : Array EIdx) (n : Nat)
    (h : Expr) (xs : List Expr)
    (hok : CheckOK eager env fe s₀) (hdh : denoteE s₀.store hd = some h)
    (hnapp : ∀ f a, h ≠ .app f a)
    (hn : n = sargs.size)
    (hxs : Frontend.denoteEList s₀.store sargs.toList = some xs)
    (hw : Expr.WScoped d (Expr.mkAppN h xs)) :
    ⦃fun s => s = s₀⦄
      ConRon.Arena.iotaRecAt .verified (coreKnot .verified eager fe id fuel) fe d hd sargs n
    ⦃fun r s' => CheckOK eager env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧
        SimOOp (fun F => ConLeche.iotaRecFueled .verified eager env F d (Expr.mkAppN h xs))
          d s'.store r; ⊤⦄ := by
  have hwf := hok.state.wf
  subst hn
  have hxl : xs.length = sargs.size := by rw [denoteEList_len hxs]; simp
  unfold ConRon.Arena.iotaRecAt
  by_cases htag : (hd.tag == ETag.const) = true
  · rw [ite_eq_left htag]
    refine triple_seq (viewConst_spec s₀ hd) ?_
    rintro oc s1 ⟨hs1, hoc⟩
    subst s1
    cases oc with
    | none => exact triple_failDanglingE
    | some cu =>
      obtain ⟨c, us⟩ := cu
      have hv := view_of_viewConst_tag htag hoc.symm
      obtain ⟨cn, ls, rfl, hcn, hls⟩ := denote_const_inv hwf hv hdh
      have hE1 : (Expr.mkAppN (.const cn ls) xs).getAppFn = .const cn ls := by
        rw [Expr.getAppFn_mkAppN]; rfl
      have hE2 : (Expr.mkAppN (.const cn ls) xs).getAppArgs = xs := by
        rw [Expr.getAppArgs_mkAppN]; rfl
      have hwargs : ∀ z ∈ xs, Expr.WScoped d z := fun z hz =>
        Expr.WScoped.getAppArgs hw z (by rw [hE2]; exact hz)
      dsimp only
      split
      next icv mI rP isK rules hfc =>
        obtain ⟨dcv, drules, hdcv, hdr, hfind⟩ := env_rec_of_index hok hcn hfc
        obtain ⟨_, hlps, hty⟩ := denoteCV_inv hdcv
        have hlenlps := denoteNList_len hlps
        by_cases hne : sargs.size ≠ mI + 1
        · rw [ite_eq_left hne]
          have hfin : SimOOp (fun F => ConLeche.iotaRecFueled .verified eager env F d
              (Expr.mkAppN (.const cn ls) xs)) d s₀.store none :=
            simOOp_none (F := 0) (iotaRecFueled_guard hE1 hfind (by
              rw [hE2]; intro hg; exact hne (by rw [← hxl, hg.1])))
          exact triple_pure_at ⟨hok, Ext.refl _, rfl, hfin⟩
        · rw [ite_eq_right hne]
          have hmI : sargs.size = mI + 1 := by simpa using hne
          have hargs : Frontend.denoteEList s₀.store
              (takeEidx sargs sargs.size).toList = some xs := by
            rw [ExprOps.takeEidx_toList, List.take_of_length_le (by simp)]
            exact hxs
          have hal : (takeEidx sargs sargs.size).toList.length = mI + 1 := by
            rw [← denoteEList_len hargs, hxl, hmI]
          refine triple_seq (viewLsLen_spec s₀ us) ?_
          rintro ol s2 ⟨hs2, hol⟩
          subst s2
          rw [viewLen_of_denoteLs hls] at hol
          subst hol
          dsimp only
          refine triple_seq (peelPis_spec s₀ hwf (mI + 1) icv.type dcv.type hty) ?_
          rintro peeled s2 ⟨hs2, hpeel⟩
          subst s2
          have hpi : peeled.isSome = (Expr.peelPis (mI + 1) dcv.type).isSome := by
            cases peeled <;> cases hp : Expr.peelPis (mI + 1) dcv.type <;>
              simp_all [denoteEO]
          by_cases hg : (takeEidx sargs sargs.size).toList.length = mI + 1 ∧
              ls.length = icv.levelParams.length ∧ peeled.isSome = true
          · rw [ite_eq_left hg]
            have hgP : xs.length = mI + 1 ∧ ls.length = dcv.levelParams.length ∧
                (Expr.peelPis (mI + 1) dcv.type).isSome = true :=
              ⟨by rw [hxl, hmI], by rw [hg.2.1, hlenlps], by rw [← hpi]; exact hg.2.2⟩
            refine triple_seq (internE_ok_spec (eager := eager) (env := env) (fe := fe)
              s₀ (.bvar 0) hok viewOK_bvar) ?_
            rintro b0 s3 ⟨hok3, hx3, hp3, _⟩
            have hargs3 := denoteEList_ext hx3 _ _ hargs
            have hmaj := denoteEList_getD_lt hargs3 (i := mI) (by rw [hal]; omega) b0
              (.bvar 0)
            have hmI' : mI < xs.length := by omega
            have hwmaj : Expr.WScoped d (xs.getD mI (.bvar 0)) := by
              simp only [List.getD, List.getElem?_eq_getElem hmI', Option.getD_some]
              exact hwargs _ (List.getElem_mem hmI')
            refine triple_seq (prepareMajor_spec hsim henv s3 d c isK rules _ cn drules _
              hok3 (denoteRules_ext hx3 _ _ hdr) hmaj hwmaj) ?_
            rintro major s4 ⟨hok4, hx4, hp4, vmaj, hvmaj, hwvmaj, Fp, hFp⟩
            have hx04 := hx3.trans hx4
            have hp04 : s4.pins = s₀.pins := hp4.trans hp3
            have hwf4 := hok4.state.wf
            have hT : ∀ G, Fp ≤ G → ConLeche.iotaRecFueled .verified eager env G d
                (Expr.mkAppN (.const cn ls) xs) =
                iotaTail .verified eager env G d ls dcv mI rP isK drules xs vmaj := by
              intro G hG
              rw [iotaRecFueled_pre hE1 hfind (by rw [hE2]; exact hgP)
                (by rw [hE2]; exact prepareMajorFueled_mono hG hFp), hE2]
            refine triple_seq (ExprOps.getAppFn_spec coreWalkFuel s4 major hok4.state
              (by rw [hvmaj]; rfl)) ?_
            rintro mh s5 ⟨hs5, hrelF⟩
            subst s5
            have hmh := hrelF vmaj hvmaj
            obtain ⟨vh, hvh⟩ := denoteE_view hmh
            refine tag_view_bind_triple hvh ?_
              (fun hne => by cases vh <;> first | rfl | exact absurd rfl hne)
            cases vh
            case const cj usj =>
              obtain ⟨cjn, lsj, hgfm, hcjn, hlsj⟩ := denote_const_inv hwf4 hvh hmh
              dsimp only
              split
              next icvj cnP cnF hfj =>
                obtain ⟨dcvj, hdcvj, hfindj⟩ := env_ctor_of_index hok4 hcjn hfj
                have hdr4 := denoteRules_ext hx04 _ _ hdr
                obtain ⟨hfr1, hfr2⟩ := findRule_denote hwf4 hcjn hdr4
                split
                next rl hrl =>
                  obtain ⟨rl', hrl', hfind'⟩ := hfr1 rl hrl
                  obtain ⟨hnf, hrlc, hrlrhs, _⟩ := rule_denote hrl'
                  have hctor : rl'.ctor = cjn := by
                    have := List.find?_some hfind'
                    simpa using this
                  refine triple_seq (ExprOps.getAppArgs_spec coreWalkFuel s4 major
                    hok4.state (by rw [hvmaj]; rfl)) ?_
                  rintro margs s6 ⟨hs6, hrelA⟩
                  subst s6
                  have hmargs := hrelA vmaj hvmaj
                  have hmlen := denoteEList_len hmargs
                  by_cases hl : margs.length = cnP + rl.nfields
                  · rw [ite_eq_left hl]
                    have hlP : vmaj.getAppArgs.length = cnP + rl'.nfields := by
                      rw [hmlen, hl, hnf]
                    have hwmargs : ∀ z ∈ vmaj.getAppArgs, Expr.WScoped d z :=
                      Expr.WScoped.getAppArgs hwvmaj
                    have hpinsW : ∀ lvls pins, rl'.fire = .nested lvls pins →
                        ∀ pin ∈ pins, pin.hasFvar = false := by
                      intro lvls pins hf' pin hpin
                      obtain ⟨-, -, -, -, g5⟩ :=
                        (henv.consts _ (ConLeche.Env.find?_mem hfind)).2.2.2.2.2 dcv mI rP isK
                          drules rfl rl' (List.mem_of_find?_eq_some hfind')
                      exact ((g5 lvls pins hf').2.2.1 pin hpin).1
                    have hcmpW := ConLeche.recFireComparands_snd_WScoped (cnP := cnP) rl'
                      dcv.levelParams ls dcvj.levelParams xs rP hwargs hpinsW
                    refine iotaFam_spec henv hsim s4 d icv icvj us usj isK rl
                      (takeEidx sargs sargs.size).toList margs mI rP ls lsj dcv dcvj
                      cjn cnP cnF rl' xs vmaj.getAppArgs hok4 (denoteLs_ext hls hx04)
                      hlsj (denoteCV_ext hdcv hx04) hdcvj hfindj hmargs
                      (denoteEList_ext hx04 _ _ hargs) hrl' hwargs hwmargs hcmpW _ _ ?_
                    rintro fam s7 ⟨hok7, hx7, hp7, Ff, hFf⟩
                    have hx07 := hx04.trans hx7
                    have hp07 : s7.pins = s₀.pins := hp7.trans hp04
                    have hval : ConLeche.iotaRecFueled .verified eager env (max Fp Ff) d
                        (Expr.mkAppN (.const cn ls) xs) = .ok (if fam then
                          some (Expr.mkAppN
                            (rl'.rhs.instantiateLevelParams dcv.levelParams ls)
                            (xs.take rP ++ vmaj.getAppArgs.drop cnP))
                        else none) := by
                      rw [hT _ (Nat.le_max_left _ _)]
                      exact iotaTail_fire hgfm hfindj hfind' hlP
                        (iotaFam_mono (Nat.le_max_right _ _) hFf)
                    by_cases hft : fam = true
                    · rw [ite_eq_left hft]
                      subst hft
                      refine triple_seq (ruleRhsAt_spec s7 c rl.ctor icv.levelParams
                        rl.rhs us cn cjn ls dcv mI rP isK drules rl' hok7
                        (denoteN_ext hcn hx07)
                        (by rw [← hctor]; exact denoteN_ext hrlc hx7)
                        (denoteLs_ext hls hx07) (denoteNListE_ext hx07 _ _ hlps)
                        (denote_ext hrlrhs hx7) hfind hfind') ?_
                      rintro rhs s8 ⟨hok8, hx8, hp8, hrhs⟩
                      have hB : Frontend.denoteEList s8.store
                          ((takeEidx sargs sargs.size).toList.take rP ++
                            margs.drop cnP) =
                          some (xs.take rP ++ vmaj.getAppArgs.drop cnP) := by
                        exact denoteEList_appendI
                          (ExprOps.denoteEList_take rP _ _
                            (denoteEList_ext (hx07.trans hx8) _ _ hargs))
                          (ExprOps.denoteEList_drop _ _ _
                            (denoteEList_ext (hx7.trans hx8) _ _ hmargs))
                      refine triple_seq (ExprOps.mkAppN_spec _ s8 rhs hok8.state
                        (by rw [hrhs]; rfl) (by rw [hB]; rfl)) ?_
                      rintro x s9 ⟨hst9, hx9, _, hc9, hp9, hrel⟩
                      have hok9 : CheckOK eager env fe s9 := hok8.mono hst9 hx9 hc9 hp9
                      have hxd := hrel _ _ hrhs hB
                      have hvw := ConLeche.iotaRec_WScoped henv hval hw
                      have hfin : SimOOp (fun F => ConLeche.iotaRecFueled .verified eager env F d
                          (Expr.mkAppN (.const cn ls) xs)) d s9.store (some x) :=
                        ⟨_, by simp [denoteEO, hxd], fun y hy => by
                          cases hy; exact hvw, _, hval⟩
                      exact triple_pure_at ⟨hok9, hx07.trans (hx8.trans hx9),
                        hp9.trans (hp8.trans hp07), hfin⟩
                    · rw [ite_eq_right hft]
                      have hff : fam = false := by simpa using hft
                      subst hff
                      have hfin : SimOOp (fun F => ConLeche.iotaRecFueled .verified eager env F d
                          (Expr.mkAppN (.const cn ls) xs)) d s7.store none :=
                        simOOp_none hval
                      exact triple_pure_at ⟨hok7, hx07, hp07, hfin⟩
                  · rw [ite_eq_right hl]
                    have hfin : SimOOp (fun F => ConLeche.iotaRecFueled .verified eager env F d
                        (Expr.mkAppN (.const cn ls) xs)) d s4.store none :=
                      simOOp_none (F := Fp) (by
                        rw [hT _ (Nat.le_refl _)]
                        exact iotaTail_len hgfm hfindj hfind' (by rw [hmlen, hnf]; exact hl))
                    exact triple_pure_at ⟨hok4, hx04, hp04, hfin⟩
                next hrl =>
                  have hfin : SimOOp (fun F => ConLeche.iotaRecFueled .verified eager env F d
                      (Expr.mkAppN (.const cn ls) xs)) d s4.store none :=
                    simOOp_none (F := Fp) (by
                      rw [hT _ (Nat.le_refl _)]
                      exact iotaTail_norule hgfm hfindj (hfr2 hrl))
                  exact triple_pure_at ⟨hok4, hx04, hp04, hfin⟩
              next hnd =>
                have hnc := env_not_ctor_of_index hok4 hcjn (fun v p q h => hnd v p q h)
                have hfin : SimOOp (fun F => ConLeche.iotaRecFueled .verified eager env F d
                    (Expr.mkAppN (.const cn ls) xs)) d s4.store none :=
                  simOOp_none (F := Fp) (by rw [hT _ (Nat.le_refl _)]
                                            exact iotaTail_noctor hgfm hnc)
                exact triple_pure_at ⟨hok4, hx04, hp04, hfin⟩
            all_goals
              dsimp only
              have hnc := denote_not_const hwf4 hvh hmh (by intro c us h; cases h)
              have hfin : SimOOp (fun F => ConLeche.iotaRecFueled .verified eager env F d
                  (Expr.mkAppN (.const cn ls) xs)) d s4.store none :=
                simOOp_none (F := Fp) (by rw [hT _ (Nat.le_refl _)]
                                          exact iotaTail_nohead hnc)
              exact triple_pure_at ⟨hok4, hx04, hp04, hfin⟩
          · rw [ite_eq_right hg]
            have hfin : SimOOp (fun F => ConLeche.iotaRecFueled .verified eager env F d
                (Expr.mkAppN (.const cn ls) xs)) d s₀.store none :=
              simOOp_none (F := 0) (iotaRecFueled_guard hE1 hfind (by
                rw [hE2]; intro hg'
                exact hg ⟨hal, by rw [hg'.2.1, hlenlps], by rw [hpi]; exact hg'.2.2⟩))
            exact triple_pure_at ⟨hok, Ext.refl _, rfl, hfin⟩
      next hnd =>
        have hnr := env_not_rec_of_index hok hcn (fun v mI rP k rs h => hnd v mI rP k rs h)
        have hfin : SimOOp (fun F => ConLeche.iotaRecFueled .verified eager env F d
            (Expr.mkAppN (.const cn ls) xs)) d s₀.store none :=
          simOOp_none (F := 0) (iotaRecFueled_norec hE1 hnr)
        exact triple_pure_at ⟨hok, Ext.refl _, rfl, hfin⟩
  · rw [ite_eq_right htag]
    obtain ⟨v, hv⟩ := denoteE_view hdh
    have hvt := EStore.tagOf_of_view hv
    have hnc := denote_not_const hwf hv hdh (by
      intro c us h; subst h; exact htag (by rw [hvt]; rfl))
    have hfin : SimOOp (fun F => ConLeche.iotaRecFueled .verified eager env F d
        (Expr.mkAppN h xs)) d s₀.store none :=
      simOOp_none (F := 0) (iotaRecFueled_nohead (by
        rw [Expr.getAppFn_mkAppN]
        cases h with
        | app f a => exact absurd rfl (hnapp f a)
        | _ => exact hnc))
    exact triple_pure_at ⟨hok, Ext.refl _, rfl, hfin⟩

section Census
#print axioms isCtorApp_spec
#print axioms litToCtorIfNat_spec
#print axioms fabScopeOk_spec
#print axioms etaFabArgsE_spec
#print axioms andRescueSlots_spec
#print axioms litMajorToCtor_spec
#print axioms majorK_spec
#print axioms majorEta_spec
#print axioms majorAnd_spec
#print axioms majorToCtor_spec
#print axioms prepareMajor_spec
#print axioms recFireLevels_spec
#print axioms recFireArgs_spec
#print axioms formerSortLoop_spec
#print axioms iotaCase3At_spec
#print axioms piResidual_specA
#print axioms iotaIndexOk_spec
#print axioms iotaFam_spec
#print axioms iotaRecAt_spec

end Census

end ConRon.Bridge.Core
