/-
# `ConRon.Bridge.Core.Walks.Guards` — the `defeq` body's cheap tests

`Arena/Core.lean`'s definitional-equality block (`defeqBody` and its
lazy-delta steps) runs cheap tests that read the handle word, one `view` and
the environment index.  con-leche's comparand is a plain function (no
`CheckM`, no fuel), so the conclusion is an EQUATION between the arena's
answer and con-leche's and there is no `∃ F` to carry.

This module holds the constructor shortcut's readers (`ctorTarget_spec`,
`ctorTargetFor_spec`, `ctorHeadAgainst_spec`) and `isEagerReduce_spec`.  The
siblings that need only `getAppFn` (`sameConstHeads_spec`,
`unfoldableHead_spec`) are in `Spine.lean`, over the `ExprOps` tier.

## What it cashes

DESIGN §8.3's **"index inequality IS structural inequality"**: the twin
compares name handles where con-leche compares `Name`s; `denoteN_inj`
(`Arena/WFProofs.lean`) turns each handle test into its structural one, and
`PinsOK` says a pin handle denotes what it is named for.
-/
module

public import ConRon.Bridge.Grind
import ConRon.Bridge.Core.Walks.Iota
import ConRon.Bridge.Core.Walks.PropRead
import ConRon.Bridge.Core.Walks.Stuck
import ConRon.Bridge.Core.Walks.Nat
import ConLeche.Verify.PropRead
import ConRon.Bridge.Core.Memo
import ConRon.Bridge.Core.Walks.StrLit
import ConRon.Bridge.Core.Walks.Proj
import ConRon.Bridge.Core.Walks.IotaLeaves
import ConRon.Bridge.ExprOps.Ranges
import ConRon.Bridge.ExprOps.Spine
import ConRon.Bridge.Specs
import ConRon.Bridge.GrindAttr
public import ConRon.Arena.Core

public section

namespace ConRon.Bridge.Core

set_option autoImplicit false
set_option experimental.vcgen true
set_option maxHeartbeats 1000000

open ConLeche ConRon.Arena ConRon.Bridge Std.WP
open scoped Lean.Order

variable {eager : Bool} {env : Env} {fe : IFEnv}

/-- con-leche: ConLeche/Kernel/Basis/Names.lean:109-116 reservedBasisNames —
the `PIN_BOOL_TRUE` slot of `pinNames` is `Bool.true`'s name.  `rfl`: both
sides are closed terms, which is what makes `PinsOK.names` usable at a
NAMED slot rather than only at a quantified one. -/
theorem pinNames_boolTrue :
    pinNames[PIN_BOOL_TRUE]? = some ConLeche.boolTrueName := by rfl

/-- con-leche: ConLeche/Kernel/Basis/Names.lean:109-116 reservedBasisNames —
the `Bool.true` pin, as the name it denotes (`pinAt_spec` at the named slot,
`pinNames_boolTrue`). -/
theorem boolTrueName_spec (s₀ : AState) (hp : PinsOK s₀) :
    ⦃fun s => s = s₀⦄ ConRon.Arena.boolTrueName
    ⦃fun n s' => s' = s₀ ∧ denoteN s₀.store.ns n = some ConLeche.boolTrueName; ⊤⦄ := by
  have hbt := pinNames_boolTrue
  vcgen [ConRon.Arena.boolTrueName, pinBoolTrue] with finish

/-- con-leche: none — `CheckOK` across a stage that moved nothing but the
memos. -/
theorem _root_.ConRon.Bridge.CheckOK.of_store_eq {eager : Bool} {env : Env} {fe : IFEnv}
    {s s' : AState} (h : CheckOK eager env fe s) (hst : s'.store = s.store)
    (hc : s'.caches = s.caches) (hp : s'.pins = s.pins) :
    CheckOK eager env fe s' :=
  h.mono ⟨by rw [hst]; exact h.state.wf⟩ (by rw [hst]; exact Ext.refl _) hc hp

/-! ## The constructor shortcut's readers

`ctorTarget`, `ctorTargetFor` and `ctorHeadAgainst` (con-leche task #592) read
the head and the environment index; their answers are names, related by
`OptNRel` (the handle denotes the name, or both are absent). -/

/-- An optional name handle against an optional name: both absent, or the
handle denotes the name. -/
@[expose] def OptNRel (st : EStore) (r : Option NIdx) (o : Option ConLeche.Name) : Prop :=
  r.map (denoteN st.ns) = o.map some

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:746-764 ctorTarget
con-leche: ConLeche/Cached/CoreC.lean:144-157 ctorTargetC — **THEOREM 1 for
`ctorTarget`**: read-only (the fvar test's memo only), an `OptNRel` with
con-leche's target.  The spine is counted (`numArgs`), con-leche's is listed
(`getAppArgs.length`). -/
theorem ctorTarget_spec (s₀ : AState) (a : EIdx) (x : Expr)
    (hok : CheckOK eager env fe s₀) (hda : denoteE s₀.store a = some x) :
    ⦃fun s => s = s₀⦄ ConRon.Arena.ctorTarget fe a
    ⦃fun r s' => CheckOK eager env fe s' ∧ s'.store = s₀.store ∧ s'.pins = s₀.pins ∧
        OptNRel s₀.store r (ConLeche.ctorTarget env x); ⊤⦄ := by
  have hwf := hok.state.wf
  unfold ConRon.Arena.ctorTarget
  refine triple_seq (ExprOps.hasFvarFast_spec coreWalkFuel s₀ a hok.state
    (by rw [hda]; rfl)) ?_
  rintro hf s1 ⟨hst1, hc1, hp1, hr1⟩
  have hfe : hf = x.hasFvar := hr1 x hda
  subst hfe
  have hok1 := hok.of_store_eq hst1 hc1 hp1
  have hda1 : denoteE s1.store a = some x := by rw [hst1]; exact hda
  have hwf1 := hok1.state.wf
  cases hfx : x.hasFvar
  · simp only [Bool.false_eq_true, ite_false]
    refine triple_seq (ExprOps.getAppFn_spec coreWalkFuel s1 a hok1.state
      (by rw [hda1]; rfl)) ?_
    rintro hd s2 ⟨rfl, hrelF⟩
    have hdd : denoteE s2.store hd = some x.getAppFn := hrelF x hda1
    obtain ⟨vh, hvh⟩ := denoteE_view hdd
    refine tag_view_bind_triple hvh ?_
      (fun hne => by cases vh <;> first | rfl | exact absurd rfl hne)
    cases vh
    case const c us =>
      obtain ⟨cn, ls, hgf, hcn, -⟩ := denote_const_inv hwf1 hvh hdd
      dsimp only
      split
      next icv cnP cnF T hfd =>
        obtain ⟨dcv, -, hfind⟩ := env_ctor_of_index hok1 hcn hfd
        have hTn := env_ctor_induct_of_index hok1 hfd
        generalize (denoteN s2.store.ns T).getD default = Tn at hfind hTn
        unfold ConRon.Arena.pinNat
        refine triple_seq (pinAt_specE s2 PIN_NAT hok1.pins) ?_
        rintro nn s3 ⟨rfl, hnn⟩
        rw [pinNames_eq_natName] at hnn
        have hTeq : (T == nn) = (Tn == ConLeche.natName) := by
          rw [beq_handle_eq hwf1 hTn hnn]
        rw [hTeq]
        have hcn0 : denoteN s₀.store.ns c = some cn := by rw [← hst1]; exact hcn
        cases hTN : (Tn == ConLeche.natName)
        · have hTN' : ¬ Tn = ConLeche.natName := by simpa using hTN
          simp only [Bool.false_eq_true, ite_false]
          refine triple_seq (numArgs_specA coreWalkFuel s3 a hok1 (by rw [hda1]; rfl)) ?_
          rintro n s4 ⟨rfl, hn⟩
          rw [hda1] at hn
          simp only [Option.map_some, Option.some.injEq] at hn
          subst hn
          have hna : x.numArgs = x.getAppArgs.length := Expr.numArgs_eq_length x
          by_cases hlen : (x.numArgs == cnP + cnF) = true
          · rw [ite_eq_left hlen]
            rw [hna] at hlen
            simp only [beq_iff_eq] at hlen
            split
            next icvT icaps hfdT =>
              obtain ⟨dcvT, dcaps, -, hdcaps, hfindT⟩ := env_ind_of_index hok1 hTn hfdT
              have hcE : dcaps.eta = icaps.eta := (denoteCaps_fields hdcaps).1
              have hcN : dcaps.neverZero = icaps.neverZero := denoteCaps_neverZero hdcaps
              by_cases hg : (icaps.neverZero && !icaps.eta) = true
              · rw [ite_eq_left hg]
                refine triple_pureS ⟨hok1, hst1, hp1, ?_⟩
                simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at hg
                simp [OptNRel, hcn0, ConLeche.ctorTarget, hfx, hgf, hfind, hfindT, hTN', hlen,
                  hcE, hcN, hg]
              · rw [ite_eq_right hg]
                refine triple_pureS ⟨hok1, hst1, hp1, ?_⟩
                have hg' : ¬ (dcaps.neverZero = true ∧ dcaps.eta = false) := by
                  rw [hcE, hcN]; simpa using hg
                simp [OptNRel, ConLeche.ctorTarget, hfx, hgf, hfind, hfindT, hTN', hlen, hg']
            next hnd =>
              have hnf := env_not_ind_of_index hok1 hTn (fun v c h => hnd v c h)
              refine triple_pureS ⟨hok1, hst1, hp1, ?_⟩
              cases hfT : env.find? Tn with
              | none => simp [OptNRel, ConLeche.ctorTarget, hfx, hgf, hfind, hTN', hlen, hfT]
              | some ci =>
                cases ci with
                | indInfo cv caps => exact absurd hfT (hnf cv caps)
                | _ => simp [OptNRel, ConLeche.ctorTarget, hfx, hgf, hfind, hTN', hlen, hfT]
          · rw [ite_eq_right hlen]
            refine triple_pureS ⟨hok1, hst1, hp1, ?_⟩
            rw [hna] at hlen
            simp only [beq_iff_eq] at hlen
            simp [OptNRel, ConLeche.ctorTarget, hfx, hgf, hfind, hlen]
        · have hTN' : Tn = ConLeche.natName := by simpa using hTN
          simp only [ite_true]
          refine triple_pureS ⟨hok1, hst1, hp1, ?_⟩
          simp [OptNRel, ConLeche.ctorTarget, hfx, hgf, hfind, hTN']
      next hnd =>
        have hnc := env_not_ctor_of_index hok1 hcn (fun v p q t h => hnd v p q t h)
        refine triple_pureS ⟨hok1, hst1, hp1, ?_⟩
        simp only [OptNRel, Option.map_none, ConLeche.ctorTarget, hfx, Bool.false_eq_true,
          ite_false, hgf]
    all_goals
      dsimp only
      refine triple_pureS ⟨hok1, hst1, hp1, ?_⟩
      have hnc := denote_not_const hwf1 hvh hdd (by intro c us h; cases h)
      simp only [OptNRel, Option.map_none, ConLeche.ctorTarget, hfx, Bool.false_eq_true,
        ite_false]
  · simp only [ite_true]
    exact triple_pureS ⟨hok1, hst1, hp1, by simp [OptNRel, ConLeche.ctorTarget, hfx]⟩

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:766-771 ctorTargetFor
con-leche: ConLeche/Cached/CoreC.lean:159-161 ctorTargetForC — **THEOREM 1 for
`ctorTargetFor`**: the eager flag, else the other side's fvar test, then
`ctorTarget_spec`. -/
theorem ctorTargetFor_spec (s₀ : AState) (eg : Bool) (o a : EIdx) (y x : Expr)
    (hok : CheckOK eager env fe s₀) (hdo : denoteE s₀.store o = some y)
    (hda : denoteE s₀.store a = some x) :
    ⦃fun s => s = s₀⦄ ConRon.Arena.ctorTargetFor fe eg o a
    ⦃fun r s' => CheckOK eager env fe s' ∧ s'.store = s₀.store ∧ s'.pins = s₀.pins ∧
        OptNRel s₀.store r (ConLeche.ctorTargetFor env eg y x); ⊤⦄ := by
  unfold ConRon.Arena.ctorTargetFor
  cases eg
  · simp only [Bool.false_eq_true, ite_false]
    refine triple_seq (ExprOps.hasFvarFast_spec coreWalkFuel s₀ o hok.state
      (by rw [hdo]; rfl)) ?_
    rintro hf s1 ⟨hst1, hc1, hp1, hr1⟩
    have hfe : hf = y.hasFvar := hr1 y hdo
    subst hfe
    have hok1 := hok.of_store_eq hst1 hc1 hp1
    cases hfy : y.hasFvar
    · simp only [Bool.false_eq_true, ite_false]
      refine triple_mono (ctorTarget_spec s1 a x hok1 (by rw [hst1]; exact hda)) ?_
      rintro r s' ⟨h1, h2, h3, h4⟩
      refine ⟨h1, h2.trans hst1, h3.trans hp1, ?_⟩
      rw [← hst1]
      simp only [ConLeche.ctorTargetFor, hfy, Bool.not_false, Bool.or_true, ite_true]
      exact h4
    · simp only [ite_true]
      exact triple_pureS ⟨hok1, hst1, hp1, by simp [OptNRel, ConLeche.ctorTargetFor, hfy]⟩
  · simp only [ite_true]
    refine triple_mono (ctorTarget_spec s₀ a x hok hda) ?_
    rintro r s' ⟨h1, h2, h3, h4⟩
    exact ⟨h1, h2, h3, by simpa [ConLeche.ctorTargetFor] using h4⟩

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:773-783 ctorHeadAgainst
con-leche: ConLeche/Cached/CoreC.lean:163-171 ctorHeadAgainstC — **THEOREM 1
for `ctorHeadAgainst`**: read-only, an equation with con-leche's reader. -/
theorem ctorHeadAgainst_spec (s₀ : AState) (c : NIdx) (cn : ConLeche.Name) (w : EIdx)
    (x : Expr) (hok : CheckOK eager env fe s₀) (hc : denoteN s₀.store.ns c = some cn)
    (hdw : denoteE s₀.store w = some x) :
    ⦃fun s => s = s₀⦄ ConRon.Arena.ctorHeadAgainst fe c w
    ⦃fun r s' => s' = s₀ ∧ r = ConLeche.ctorHeadAgainst env cn x; ⊤⦄ := by
  have hwf := hok.state.wf
  unfold ConRon.Arena.ctorHeadAgainst
  refine triple_seq (ExprOps.getAppFn_spec coreWalkFuel s₀ w hok.state
    (by rw [hdw]; rfl)) ?_
  rintro hd s1 ⟨rfl, hrelF⟩
  have hdd : denoteE s1.store hd = some x.getAppFn := hrelF x hdw
  obtain ⟨vh, hvh⟩ := denoteE_view hdd
  refine tag_view_bind_triple hvh ?_
    (fun hne => by cases vh <;> first | rfl | exact absurd rfl hne)
  cases vh
  case const d us =>
    obtain ⟨dn, ls, hgf, hdn, -⟩ := denote_const_inv hwf hvh hdd
    dsimp only
    have hdc : (d == c) = (dn == cn) := beq_handle_eq hwf hdn hc
    rw [hdc]
    cases hb : (dn == cn)
    · simp only [Bool.false_eq_true, ite_false]
      split
      next icv p q t hfd =>
        obtain ⟨dcv, -, hfind⟩ := env_ctor_of_index hok hdn hfd
        exact triple_pureS ⟨rfl, by simp [ConLeche.ctorHeadAgainst, hgf, hb, hfind]⟩
      next hnd =>
        have hnc := env_not_ctor_of_index hok hdn (fun v p q t h => hnd v p q t h)
        refine triple_pureS ⟨rfl, ?_⟩
        simp only [ConLeche.ctorHeadAgainst, hgf, hb, Bool.false_eq_true, ite_false]
    · simp only [ite_true]
      exact triple_pureS ⟨rfl, by simp [ConLeche.ctorHeadAgainst, hgf, hb]⟩
  all_goals
    dsimp only
    refine triple_pureS ⟨rfl, ?_⟩
    have hnc := denote_not_const hwf hvh hdd (by intro c us h; cases h)
    simp only [ConLeche.ctorHeadAgainst]
    try
      generalize x.getAppFn = g at hnc ⊢
      cases g <;> first | rfl | exact absurd rfl (hnc _ _)

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
    (hok : CheckOK eager env fe s₀) (hden : denoteE s₀.store h = some x) :
    ⦃fun s => s = s₀⦄ ConRon.Arena.isEagerReduce h
    ⦃fun b s' => CheckOK eager env fe s' ∧ s'.store = s₀.store ∧
        s'.pins = s₀.pins ∧ b = ConLeche.Expr.isEagerReduce x; ⊤⦄ := by
  sym only [bridge_grind, hok.pins, isEagerReduce_eq] =>
    vcgen [ConRon.Arena.isEagerReduce, eagerReduceName_spec] <;> finish

/-! ## The axiom census -/

section Census

#print axioms ctorTarget_spec
#print axioms ctorTargetFor_spec
#print axioms ctorHeadAgainst_spec
#print axioms pinNames_eagerReduce
#print axioms isEagerReduce_eq
#print axioms isEagerReduce_spec

end Census

end ConRon.Bridge.Core
