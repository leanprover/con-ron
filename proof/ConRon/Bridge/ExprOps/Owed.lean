/-
# `ConRon.Bridge.ExprOps.Owed` — the eight statements the round did not reach

DESIGN §8.2's Theorem 1 for the eight twins of `Arena/ExprOps.lean` whose
STATEMENT this round owes and whose PROOF it did not reach.  They are here
rather than missing because the statement is the deliverable that matters for
the next round: it is what fixes the shape the arms are written against, and
`Bridge/ExprOps/{Abs,Reset,InstLP}.lean` already carry the whole step-lemma
layer each of them needs.

Every one is `sorry`, every one is listed in DESIGN §8's task section, and
none of them is a *mathematical* gap: five are `…Fast` entry brackets whose
`…Go` is already proved (the bracket is `clear`, walk, `clear`, which is the
shape `ExprOps/Inst1.lean`'s `instantiate1Fast_spec` closes in three lines),
and three are the three walks whose fuel induction the round ran out on —
`abstractRangeGo` (whose step lemmas `Abs.lean` has, `AbsRangeAt.*`),
`renameConstsGo` (whose step lemmas `Reset.lean` has, `RenameAt.*`) and
`instLPGo` (whose level half `InstLP.lean` closes and whose expression half
is `resetMetaGo`'s shape with the `hasLP` cutoff).

The **deviations each statement carries** are the ones
`Arena/ExprOps.lean`'s own doc comments name:

* `abstractRangeGo` / `abstractRangeFast` are the EXECUTED form and
  `abstractRange` (proved in `Abs.lean`) is the SPEC descent — task
  #97-P6-11's clause change, whose equation is `Abs.lean`'s
  `abstractRange_zero_eq` and `abstractRange_of_fvarRange_le`;
* `renameConstsGo`'s `f : NIdx → NIdx` is a map on HANDLES, so its theorem
  carries the hypothesis that `f` denotes con-leche's `fn : Name → Name`;
* `instLPGo`'s `ks`/`us` are TRANSIENT `List Name` / `List Level` (DESIGN
  §8.3 lesson 4), so `instLPFast`'s theorem carries the readback hypotheses
  its entry establishes with `readNames` / `readLevels`;
* all five `…Fast` entries clear their memo before and after, so their
  postcondition carries `s'.memos.xC = ∅` and NOT the memo invariant — which
  is why a per-call memo never appears in a caller's invariant.
-/
import ConRon.Bridge.ExprOps.Abs
import ConRon.Bridge.ExprOps.Reset
import ConRon.Bridge.ExprOps.InstLP

namespace ConRon.Bridge.ExprOps

set_option autoImplicit false
set_option mvcgen.warning false

open ConLeche ConRon.Arena ConRon.Bridge Std.Do

/-! ## `abstract1`'s entry -/

/-- con-leche: ConLeche/Kernel/ExprOps.lean:1930-1932 abstract1Fast —
**OPEN** (task #97-P3-0): the bracket over `abstract1Go_spec`, whose shape is
`ExprOps/Inst1.lean`'s `instantiate1Fast_spec`. -/
theorem abstract1Fast_spec (fuel : Nat) (s₀ : AState) (e : EIdx) (d k : Nat)
    (hok : StateOK s₀) (hden : (denoteE s₀.store e).isSome = true) :
    ⦃fun s => ⌜s = s₀⌝⦄ abstract1Fast fuel e d k
    ⦃⇓? r s' => ⌜StateOK s' ∧ Ext s₀.store s'.store ∧
        s'.caches = s₀.caches ∧ s'.pins = s₀.pins ∧ s'.memos.abs1C = ∅ ∧
        RelE (fun x => Expr.abstract1 x d k) s₀.store e s'.store r⌝⦄ := by
  sorry

/-! ## `abstractRange`'s executed form -/

/-- con-leche: ConLeche/Kernel/ExprOps.lean:791-811 abstractRange —
**OPEN** (task #97-P3-0): the EXECUTED descent, against the SPEC descent
`Abs.lean` proves.  Its step lemmas are `Abs.lean`'s `AbsRangeAt.*`. -/
theorem abstractRangeGo_spec (d k : Nat) (fuel : Nat) (s₀ : AState) (c : EIdx)
    (cur : Nat) (hok : StateOK s₀) (hm : Abs1MemoA d s₀)
    (hden : (denoteE s₀.store c).isSome = true) :
    ⦃fun s => ⌜s = s₀⌝⦄ abstractRangeGo d k fuel c cur
    ⦃⇓? r s' => ⌜StateOK s' ∧ Ext s₀.store s'.store ∧
        s'.caches = s₀.caches ∧ s'.pins = s₀.pins ∧
        RelE (fun x => Expr.abstractRange x d k cur) s₀.store c s'.store r⌝⦄ := by
  sorry

/-- con-leche: ConLeche/Kernel/ExprOps.lean:791-811 abstractRange —
**OPEN** (task #97-P3-0): the bracket over `abstractRangeGo_spec`. -/
theorem abstractRangeFast_spec (fuel : Nat) (s₀ : AState) (e : EIdx)
    (d k c : Nat) (hok : StateOK s₀)
    (hden : (denoteE s₀.store e).isSome = true) :
    ⦃fun s => ⌜s = s₀⌝⦄ abstractRangeFast fuel e d k c
    ⦃⇓? r s' => ⌜StateOK s' ∧ Ext s₀.store s'.store ∧
        s'.caches = s₀.caches ∧ s'.pins = s₀.pins ∧ s'.memos.abs1C = ∅ ∧
        RelE (fun x => Expr.abstractRange x d k c) s₀.store e s'.store r⌝⦄ := by
  sorry

/-! ## `resetMeta`'s entry -/

/-- con-leche: ConLeche/Kernel/ExprOps.lean:688 resetMetaFast — the bracket
over `Reset.lean`'s `resetMetaGo_spec`, in `ExprOps/Inst1.lean`'s
`instantiate1Fast_spec` shape: the memo is cleared before and after, and the
cleared memo satisfies `ResetMemoA` for free (`MemoOK.of_empty`). -/
theorem resetMetaFast_spec (fuel : Nat) (s₀ : AState) (e : EIdx)
    (hok : StateOK s₀) (hden : (denoteE s₀.store e).isSome = true) :
    ⦃fun s => ⌜s = s₀⌝⦄ resetMetaFast fuel e
    ⦃⇓? r s' => ⌜StateOK s' ∧ Ext s₀.store s'.store ∧
        s'.caches = s₀.caches ∧ s'.pins = s₀.pins ∧ s'.memos.resetC = ∅ ∧
        RelE Expr.resetMeta s₀.store e s'.store r⌝⦄ := by
  have hr := (resetMetaGo_spec fuel).run
  mvcgen [resetMetaFast, hr]
  all_goals bridge_vcs [Expr.resetMeta]

/-! ## `renameConsts`

`f : NIdx → NIdx` is a map on HANDLES; con-leche's is `fn : Name → Name`.
The hypothesis that relates them is what `Arena/ExprOps.lean`'s own note
("the only call site is the modeled-block contract, whose map is a lookup in
a table") says the `DeclCheck` tier will discharge. -/

/-- con-leche: ConLeche/Kernel/ExprOps.lean:999-1036 renameConstsGo —
**OPEN** (task #97-P3-0).  Its step lemmas are `Reset.lean`'s `RenameAt.*`,
`RenameAt.const_step` included. -/
theorem renameConstsGo_spec (f : NIdx → NIdx) (fn : ConLeche.Name → ConLeche.Name)
    (fuel : Nat) (s₀ : AState) (c : EIdx) (hok : StateOK s₀)
    (hm : RenameMemoA fn s₀)
    (hf : ∀ (n : NIdx) (x : ConLeche.Name), denoteN s₀.store.ns n = some x →
      denoteN s₀.store.ns (f n) = some (fn x))
    (hden : (denoteE s₀.store c).isSome = true) :
    ⦃fun s => ⌜s = s₀⌝⦄ renameConstsGo f fuel c
    ⦃⇓? r s' => ⌜StateOK s' ∧ RenameMemoA fn s' ∧ Ext s₀.store s'.store ∧
        s'.caches = s₀.caches ∧ s'.pins = s₀.pins ∧
        RelE (Expr.renameConsts fn) s₀.store c s'.store r⌝⦄ := by
  sorry

/-- con-leche: ConLeche/Kernel/ExprOps.lean:1112-1114 renameConstsFast —
**OPEN** (task #97-P3-0): the bracket over `renameConstsGo_spec`. -/
theorem renameConstsFast_spec (fuel : Nat) (f : NIdx → NIdx)
    (fn : ConLeche.Name → ConLeche.Name) (s₀ : AState) (e : EIdx)
    (hok : StateOK s₀)
    (hf : ∀ (n : NIdx) (x : ConLeche.Name), denoteN s₀.store.ns n = some x →
      denoteN s₀.store.ns (f n) = some (fn x))
    (hden : (denoteE s₀.store e).isSome = true) :
    ⦃fun s => ⌜s = s₀⌝⦄ renameConstsFast fuel f e
    ⦃⇓? r s' => ⌜StateOK s' ∧ Ext s₀.store s'.store ∧
        s'.caches = s₀.caches ∧ s'.pins = s₀.pins ∧ s'.memos.renameC = ∅ ∧
        RelE (Expr.renameConsts fn) s₀.store e s'.store r⌝⦄ := by
  sorry

/-! ## `instantiateLevelParams`

DESIGN §8.3 lesson 4: the level ALGORITHM runs on transient trees, so `ks`
and `us` are `List Name` and `List Level` in the walk and handles only at the
entry, which reads them back with `readNames` / `readLevels`.  The cutoff is
the `hasLP` bit and its licence is con-leche's
`Expr.instantiateLevelParams_eq_self` (`ExprOps.lean:2465`). -/

/-- con-leche: ConLeche/Kernel/ExprOps.lean:2566-2605 Expr.instLPGo —
**OPEN** (task #97-P3-0).  `InstLP.lean` closes its LEVEL half
(`substLMemoAt_spec`, `substLsMemoAt_spec`); what is owed is the expression
walk, which is `resetMetaGo`'s shape with the `hasLP` cutoff in front. -/
theorem instLPGo_spec (ks : List ConLeche.Name) (us : List Level) (fuel : Nat)
    (s₀ : AState) (c : EIdx) (hok : StateOK s₀) (hm : InstLPMemoA ks us s₀)
    (hml : InstLPLMemoA ks us s₀) (hmls : InstLPLsMemoA ks us s₀)
    (hden : (denoteE s₀.store c).isSome = true) :
    ⦃fun s => ⌜s = s₀⌝⦄ instLPGo ks us fuel c
    ⦃⇓? r s' => ⌜StateOK s' ∧ InstLPMemoA ks us s' ∧ Ext s₀.store s'.store ∧
        s'.caches = s₀.caches ∧ s'.pins = s₀.pins ∧
        RelE (fun x => x.instantiateLevelParams ks us) s₀.store c
          s'.store r⌝⦄ := by
  sorry

/-- con-leche: ConLeche/Kernel/ExprOps.lean:2718-2722 Expr.instLPFast —
**OPEN** (task #97-P3-0): the entry, which reads `ks` and `us` back ONCE and
then runs `instLPGo` on the transient trees. -/
theorem instLPFast_spec (fuel : Nat) (s₀ : AState) (ks : List NIdx)
    (us : LsIdx) (e : EIdx) (ksv : List ConLeche.Name) (usv : List Level)
    (hok : StateOK s₀)
    (hks : Frontend.denoteNList s₀.store.ns ks = some ksv)
    (hus : denoteLs s₀.store.lss us = some usv)
    (hden : (denoteE s₀.store e).isSome = true) :
    ⦃fun s => ⌜s = s₀⌝⦄ instLPFast fuel ks us e
    ⦃⇓? r s' => ⌜StateOK s' ∧ Ext s₀.store s'.store ∧
        s'.caches = s₀.caches ∧ s'.pins = s₀.pins ∧ s'.memos.instLPC = ∅ ∧
        RelE (fun x => x.instantiateLevelParams ksv usv) s₀.store e
          s'.store r⌝⦄ := by
  sorry

end ConRon.Bridge.ExprOps
