/-
# `ConRon.Bridge.Core.Walks.IotaMajor` — the ι major's preparation

Task #97-P3-Core round 6 (lane `iota`): `litMajorToCtor`, the stuck-major
rescue `majorToCtor` (K, η, the pinned `And`) and `prepareMajor`, which runs
them in the official kernel's order.  See `Walks/Iota.lean`'s note for the two
preconditions (`hμ`, `EnvWF env`).
-/
import ConRon.Bridge.Core.Walks.IotaLeaves

namespace ConRon.Bridge.Core

set_option autoImplicit false
set_option mvcgen.warning false
set_option maxHeartbeats 1000000

open ConLeche ConRon.Arena ConRon.Bridge Std.Do

variable {mode : CheckMode} {env : Env} {fe : IFEnv}

/-! ## 2. The major's preparation -/

/-- con-leche: ConLeche/Kernel/Core.lean:728-740 litMajorToCtor — every
major but a string literal takes the `Nat` conversion. -/
theorem litMajorToCtorFueled_nstr {F d : Nat} {x : Expr}
    (hx : ∀ str, x ≠ .lit (.strVal str)) :
    ConLeche.litMajorToCtorFueled mode env F d x =
      .ok (ConLeche.litToCtorIfNat env x) := by
  cases x with
  | lit l =>
    cases l with
    | strVal str => exact absurd rfl (hx str)
    | natVal n => rfl
  | _ => rfl

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
  have hwf := hok.state.wf
  obtain ⟨v, hv⟩ := denoteE_view hden
  unfold ConRon.Arena.litMajorToCtor
  refine view_bind_triple hv ?_
  -- every major but a string literal: the `Nat` conversion
  have hnat : (∀ str, x ≠ .lit (.strVal str)) →
      ⦃fun s => ⌜s = s₀⌝⦄ ConRon.Arena.litToCtorIfNat fe h
      ⦃⇓? r s' => ⌜CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
          s'.pins = s₀.pins ∧
          SimEOp (fun F => ConLeche.litMajorToCtorFueled mode env F d x) d
            s'.store r⌝⦄ := by
    intro hnl
    refine triple_mono (litToCtorIfNat_spec s₀ h x hok hden) ?_
    rintro r s' ⟨hok', hx', hp', hr⟩
    refine ⟨hok', hx', hp', _, hr, ConLeche.litToCtorIfNat_WScoped hw, 0, ?_⟩
    exact litMajorToCtorFueled_nstr hnl
  cases v
  case lit l =>
    obtain rfl := denote_lit_inv hwf hv hden
    cases l with
    | natVal n => exact hnat (by intro str h; cases h)
    | strVal str =>
      dsimp only
      refine triple_seq (strLitSupported_spec s₀ hok) ?_
      rintro sup s1 ⟨hok1, hx1, hp1, hsup⟩
      split
      next hsupt =>
        have hS : ConLeche.strLitSupported env = true := hsup ▸ hsupt
        refine triple_seq (strLitToConstructor_spec s1 str hok1) ?_
        rintro c s2 ⟨hok2, hx2, hp2, hc⟩
        refine triple_mono (hsim.whnf s2 d c _ hok2 hc
          (strLitToConstructor_WScoped str d)) ?_
        rintro r s3 ⟨hok3, hx3, hp3, w, hw3, hww, F, hF⟩
        refine ⟨hok3, hx1.trans (hx2.trans hx3), hp3.trans (hp2.trans hp1),
          w, hw3, hww, F, ?_⟩
        simp only [ConLeche.litMajorToCtorFueled, ConLeche.litMajorToCtor, hS,
          if_true]
        exact hF
      next hsupf =>
        have hS : ConLeche.strLitSupported env = false := by
          rw [← hsup]; simpa using hsupf
        mvcgen
        bridge_peel; subst_vars
        refine ⟨hok1, hx1, hp1, .lit (.strVal str), denote_ext hden hx1, hw, 0,
          ?_⟩
        simp only [ConLeche.litMajorToCtorFueled, ConLeche.litMajorToCtor, hS,
          Bool.false_eq_true, if_false]
        rfl
  all_goals
    dsimp only
    refine hnat ?_
    intro str hx
    subst hx
    have := view_of_denote_lit hwf hv hden
    cases this

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

/-- con-leche: none — a denoting rule list has the same K bit. -/
theorem recRuleK_denote {st : EStore} {rules : List IRecRule}
    {rules' : List RecRule} (h : Frontend.denoteRules st rules = some rules') :
    ConRon.Arena.recRuleK rules = ConLeche.recRuleK rules' := by
  match rules, h with
  | [], h =>
    simp only [Frontend.denoteRules] at h; cases h; rfl
  | [r], h =>
    simp only [Frontend.denoteRules] at h
    split at h
    · rename_i x xs hx hxs
      obtain rfl : xs = [] := by
        simp only [Frontend.denoteRules, Option.some.injEq] at hxs; exact hxs.symm
      cases h
      simp only [Frontend.denoteRule] at hx
      split at hx
      · cases hx; rfl
      · simp at hx
    · simp at h
  | r1 :: r2 :: rs, h =>
    have hl := denoteRules_len h
    match rules', hl with
    | a :: b :: cs, _ => rfl

/-- con-leche: ConLeche/Kernel/Core.lean:758-795 prepareMajor — at a
K-flagged recursor: the rescue on the raw major, then `whnf`, then the literal
conversion. -/
theorem prepareMajorFueled_k {F d : Nat} {cn : ConLeche.Name}
    {rules' : List RecRule} {x m1 m2 m3 : Expr}
    (hk : ConLeche.recRuleK rules' = true)
    (h1 : ConLeche.majorToCtorFueled mode env F d cn rules' x = .ok m1)
    (h2 : ConLeche.whnf mode env F d m1 = .ok m2)
    (h3 : ConLeche.litMajorToCtorFueled mode env F d m2 = .ok m3) :
    ConLeche.prepareMajorFueled mode env F d cn rules' x = .ok m3 := by
  have e1 : ConLeche.majorToCtor mode (ConLeche.pureFns mode env F) env d cn
      rules' x = .ok m1 := h1
  have e2 : (ConLeche.pureFns mode env F).whnf d m1 = .ok m2 := h2
  have e3 : ConLeche.litMajorToCtor (ConLeche.pureFns mode env F) env d m2 =
      .ok m3 := h3
  simp only [ConLeche.prepareMajorFueled, ConLeche.prepareMajor, hk, if_true,
    e1, e2, e3, bind, Except.bind]

/-- con-leche: ConLeche/Kernel/Core.lean:758-795 prepareMajor — elsewhere:
`whnf`, the literal conversion, then the rescue. -/
theorem prepareMajorFueled_nk {F d : Nat} {cn : ConLeche.Name}
    {rules' : List RecRule} {x m1 m2 m3 : Expr}
    (hk : ConLeche.recRuleK rules' = false)
    (h1 : ConLeche.whnf mode env F d x = .ok m1)
    (h2 : ConLeche.litMajorToCtorFueled mode env F d m1 = .ok m2)
    (h3 : ConLeche.majorToCtorFueled mode env F d cn rules' m2 = .ok m3) :
    ConLeche.prepareMajorFueled mode env F d cn rules' x = .ok m3 := by
  have e1 : (ConLeche.pureFns mode env F).whnf d x = .ok m1 := h1
  have e2 : ConLeche.litMajorToCtor (ConLeche.pureFns mode env F) env d m1 =
      .ok m2 := h2
  have e3 : ConLeche.majorToCtor mode (ConLeche.pureFns mode env F) env d cn
      rules' m2 = .ok m3 := h3
  simp only [ConLeche.prepareMajorFueled, ConLeche.prepareMajor, hk,
    Bool.false_eq_true, if_false, e1, e2, e3, bind, Except.bind]

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
  unfold ConRon.Arena.prepareMajor
  rw [recRuleK_denote hr]
  split
  next hk =>
    refine triple_seq (majorToCtor_spec hμ henv hsim s₀ d c rules major cn
      rules' x hok hr hden hw) ?_
    rintro m1 s1 ⟨hok1, hx1, hp1, v1, hv1, hwv1, F1, hF1⟩
    refine triple_seq (hsim.whnf s1 d m1 v1 hok1 hv1 hwv1) ?_
    rintro m2 s2 ⟨hok2, hx2, hp2, v2, hv2, hwv2, F2, hF2⟩
    refine triple_mono (litMajorToCtor_spec hsim s2 d m2 v2 hok2 hv2 hwv2) ?_
    rintro m3 s3 ⟨hok3, hx3, hp3, v3, hv3, hwv3, F3, hF3⟩
    refine ⟨hok3, hx1.trans (hx2.trans hx3), hp3.trans (hp2.trans hp1), v3, hv3,
      hwv3, max F1 (max F2 F3), prepareMajorFueled_k hk
        (majorToCtorFueled_mono (by omega) hF1) (ConLeche.whnf_mono (by omega) hF2)
        (litMajorToCtorFueled_mono (by omega) hF3)⟩
  next hk =>
    have hk' : ConLeche.recRuleK rules' = false := by simpa using hk
    refine triple_seq (hsim.whnf s₀ d major x hok hden hw) ?_
    rintro m1 s1 ⟨hok1, hx1, hp1, v1, hv1, hwv1, F1, hF1⟩
    refine triple_seq (litMajorToCtor_spec hsim s1 d m1 v1 hok1 hv1 hwv1) ?_
    rintro m2 s2 ⟨hok2, hx2, hp2, v2, hv2, hwv2, F2, hF2⟩
    refine triple_mono (majorToCtor_spec hμ henv hsim s2 d c rules m2 cn rules'
      v2 hok2 (denoteRules_ext (hx1.trans hx2) _ _ hr) hv2 hwv2) ?_
    rintro m3 s3 ⟨hok3, hx3, hp3, v3, hv3, hwv3, F3, hF3⟩
    refine ⟨hok3, hx1.trans (hx2.trans hx3), hp3.trans (hp2.trans hp1), v3, hv3,
      hwv3, max F1 (max F2 F3), prepareMajorFueled_nk hk'
        (ConLeche.whnf_mono (by omega) hF1)
        (litMajorToCtorFueled_mono (by omega) hF2)
        (majorToCtorFueled_mono (by omega) hF3)⟩


end ConRon.Bridge.Core
