/-
# `ConRon.Bridge.Core.Arms.DefeqLazy` — Theorem 1 for the easy cases and lazy delta

Task #109.  con-leche 8afe1815 restructures definitional equality after the
official `is_def_eq_core`; this module holds one spec per twin function of
the part between the cheap head normalization and the stuck comparison,
each relating `Arena/Core.lean`'s function to con-leche's at
`pureFns mode env F` with the frame (`CheckOK`, `Ext`, pins) and the answer
in the eventual form `Ev` (`Arms/DefeqBase.lean`):

| twin function | spec | answer relation |
|---|---|---|
| `quickDefEq` | `quickDefEq_spec` | the same `Option Bool` |
| `isNatZero`, `natPred?` | `isNatZero_spec`, `natPred?_spec` | equation / `denoteEO` |
| `defeqOffset` | `defeqOffset_spec` | the same `Option Bool` |
| `headIsProj` | `headIsProj_spec` | equation |
| `tryUnfoldProjApp` | `tryUnfoldProjApp_spec` | `denoteEO`, scoped |
| `deltaQuick`, `lazyDeltaStep` | `deltaQuick_spec`, `lazyDeltaStep_spec` | `DSRel` |
| `lazyDeltaReduction` | `lazyDeltaReduction_spec` (induction on the budget) | `LRRel` |

The binder arms of `quickDefEq` are the port's batched descent
(`defeqBinders`), whose identification is `Arms/DefeqPeel.lean`'s
`defeqBinders_spec`.
-/
import ConRon.Bridge.Core.Arms.DefeqBase
import ConRon.Bridge.Core.Arms.DefeqPeel

namespace ConRon.Bridge.Core

set_option autoImplicit false
set_option mvcgen.warning false
set_option maxHeartbeats 1000000

open ConLeche ConRon.Arena ConRon.Bridge Std.Do

variable {mode : CheckMode} {env : Env}

/-- A tag test at a denotation of known constructor: `exprTag` computes, and
the two `UInt32` literals are compared by `decide`. -/
local macro "tag_dec" : tactic => `(tactic| (simp only [exprTag]; try decide))

/-! ## 1. `quickDefEq` -/

/-- con-leche: ConLeche/Kernel/Core.lean:1478-1515 quickDefEq — a pair that is
not one of the four easy kinds (two sorts, two literals, two `∀`s, two `λ`s)
answers `none`. -/
theorem quickDefEq_none {r : CoreFns CheckM} {d : Nat} {x y : Expr}
    (hne : (x == y) = false)
    (h : ¬ (exprTag x = exprTag y ∧ (exprTag x = ETag.sort ∨
      exprTag x = ETag.lit ∨ exprTag x = ETag.forallE ∨ exprTag x = ETag.lam))) :
    ConLeche.quickDefEq mode r d x y = pure none := by
  unfold ConLeche.quickDefEq
  rw [if_neg (by simp [hne])]
  split
  all_goals first
    | rfl
    | (exfalso; apply h; simp [exprTag])

section QuickArms

variable {fe : IFEnv} {fuel d : Nat} {s₀ : AState} {x y : Expr}

/-- con-leche: ConLeche/Kernel/Core.lean:1478-1515 quickDefEq — **the `none`
exit**, at a pair `quickDefEq_none` covers. -/
theorem qd_none_exit (hok : CheckOK mode env fe s₀) (hne : (x == y) = false)
    (h : ¬ (exprTag x = exprTag y ∧ (exprTag x = ETag.sort ∨
      exprTag x = ETag.lit ∨ exprTag x = ETag.forallE ∨ exprTag x = ETag.lam))) :
    ⦃fun s => ⌜s = s₀⌝⦄ (pure none : AM (Option Bool))
    ⦃⇓? o s' => ⌜CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧
        Ev (fun F => ConLeche.quickDefEq mode (ConLeche.pureFns mode env F) d x y
          = .ok o)⌝⦄ :=
  triple_pure_post ⟨hok, Ext.refl _, rfl, ⟨0, fun _ _ => quickDefEq_none hne h⟩⟩

/-- con-leche: ConLeche/Kernel/Core.lean:1478-1515 quickDefEq — **two sorts**:
the level comparison. -/
theorem qdArm_sort (u v : LIdx) (lu lv : ConLeche.Level)
    (hok : CheckOK mode env fe s₀)
    (hu : denoteL s₀.store.ls u = some lu) (hv : denoteL s₀.store.ls v = some lv)
    (hne : (Expr.sort lu == Expr.sort lv) = false) :
    ⦃fun s => ⌜s = s₀⌝⦄
      (do
        let o ← lvlEq? u v
        let ok ← ConRon.Arena.liftFueled "level comparison" o
        pure (some ok))
    ⦃⇓? o s' => ⌜CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧
        Ev (fun F => ConLeche.quickDefEq mode (ConLeche.pureFns mode env F) d
          (.sort lu) (.sort lv) = .ok o)⌝⦄ := by
  refine triple_seq (lvlEq?_spec s₀ u v hok) ?_
  rintro o s2 ⟨hok2, hst2, hp2, lu', lv', hu', hv', rfl⟩
  rw [hu] at hu'; rw [hv] at hv'
  obtain rfl := Option.some.inj hu'
  obtain rfl := Option.some.inj hv'
  cases ho : ConLeche.Level.isEquiv lu lv with
  | none =>
    exact triple_seq (Q := fun _ _ => False) triple_fail (fun _ _ h => h.elim)
  | some b =>
    exact triple_pure_post ⟨hok2, by rw [hst2]; exact Ext.refl _, hp2,
      ⟨0, fun _ _ => by
        dsimp only
        unfold ConLeche.quickDefEq
        rw [if_neg (by simp [hne])]
        simp only [ConLeche.liftFueled, ho, bind, Except.bind, pure,
          Except.pure]⟩⟩

/-- con-leche: ConLeche/Kernel/Core.lean:1478-1515 quickDefEq — **two
literals**: the literal comparison. -/
theorem qdArm_lit {l₁ l₂ : ConLeche.Literal} (hok : CheckOK mode env fe s₀)
    (hne : (Expr.lit l₁ == Expr.lit l₂) = false) :
    ⦃fun s => ⌜s = s₀⌝⦄ (pure (some (l₁ == l₂)) : AM (Option Bool))
    ⦃⇓? o s' => ⌜CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧
        Ev (fun F => ConLeche.quickDefEq mode (ConLeche.pureFns mode env F) d
          (.lit l₁) (.lit l₂) = .ok o)⌝⦄ :=
  triple_pure_post ⟨hok, Ext.refl _, rfl, ⟨0, fun _ _ => by
    dsimp only; unfold ConLeche.quickDefEq; rw [if_neg (by simp [hne])]; rfl⟩⟩

/-- con-leche: ConLeche/Kernel/Core.lean:1478-1515 quickDefEq — **two binders
of one kind**, batched (`defeqBinders_spec`). -/
theorem qdArm_binder (hsim : KnotSpec mode env fe fuel) (isLam : Bool)
    (ty₁ bd₁ ty₂ bd₂ : EIdx) (m₁ m₂ : ConLeche.BinderMeta) (t₁ c₁ t₂ c₂ : Expr)
    (hok : CheckOK mode env fe s₀)
    (h1 : denoteE s₀.store ty₁ = some t₁) (h2 : denoteE s₀.store bd₁ = some c₁)
    (h3 : denoteE s₀.store ty₂ = some t₂) (h4 : denoteE s₀.store bd₂ = some c₂)
    (hwa : Expr.WScoped d (bndE isLam t₁ c₁ m₁))
    (hwb : Expr.WScoped d (bndE isLam t₂ c₂ m₂))
    (hne : (bndE isLam t₁ c₁ m₁ == bndE isLam t₂ c₂ m₂) = false) :
    ⦃fun s => ⌜s = s₀⌝⦄
      (do
        let ok ← defeqBinders mode (coreKnot mode fe id fuel) d ty₁ bd₁ m₁ ty₂
          bd₂ m₂ isLam
        pure (some ok))
    ⦃⇓? o s' => ⌜CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧
        Ev (fun F => ConLeche.quickDefEq mode (ConLeche.pureFns mode env F) d
          (bndE isLam t₁ c₁ m₁) (bndE isLam t₂ c₂ m₂) = .ok o)⌝⦄ := by
  refine triple_seq (defeqBinders_spec hsim s₀ d ty₁ bd₁ ty₂ bd₂ m₁ m₂
    isLam t₁ c₁ t₂ c₂ hok h1 h2 h3 h4 hwa hwb hne) ?_
  rintro ok s1 ⟨hok1, hx1, hp1, hF⟩
  exact triple_pure_post ⟨hok1, hx1, hp1,
    Ev.of_mono (fun hle h => quickDefEqF_mono hle h) hF⟩

end QuickArms

/-- con-leche: ConLeche/Kernel/Core.lean:1478-1515 quickDefEq — **THEOREM 1
for the easy cases**: handle equality is syntactic equality, the two tag
tests are con-leche's constructor match, and the four arms are `qdArm_*`. -/
theorem quickDefEq_spec {fe : IFEnv} {fuel : Nat}
    (hsim : KnotSpec mode env fe fuel) (d : Nat) (s₀ : AState) (a b : EIdx)
    (x y : Expr) (hok : CheckOK mode env fe s₀)
    (hx : denoteE s₀.store a = some x) (hy : denoteE s₀.store b = some y)
    (hwx : Expr.WScoped d x) (hwy : Expr.WScoped d y) :
    ⦃fun s => ⌜s = s₀⌝⦄ ConRon.Arena.quickDefEq mode (coreKnot mode fe id fuel) d a b
    ⦃⇓? o s' => ⌜CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧
        Ev (fun F => ConLeche.quickDefEq mode (ConLeche.pureFns mode env F) d x y
          = .ok o)⌝⦄ := by
  have hwf := hok.state.wf
  unfold ConRon.Arena.quickDefEq
  rw [beq_of_denoteE hwf hx hy]
  split
  · rename_i hab
    exact triple_pure_post ⟨hok, Ext.refl _, rfl, ⟨0, fun _ _ => by
      dsimp only
      unfold ConLeche.quickDefEq; rw [if_pos hab]; rfl⟩⟩
  rename_i hab
  have hne : (x == y) = false := by simpa using hab
  simp only [tag_of_denote hwf hx, tag_of_denote hwf hy]
  split
  · rename_i ht
    exact qd_none_exit hok hne (by
      rintro ⟨h1, _⟩; simp [h1] at ht)
  rename_i ht
  split
  · rename_i hk
    obtain ⟨va, hva⟩ := denoteE_view hx
    obtain ⟨vb, hvb⟩ := denoteE_view hy
    refine view_bind_triple hva ?_
    refine view_bind_triple hvb ?_
    have hA := VD.of_view hwf hva hx
    have hB := VD.of_view hwf hvb hy
    rcases hA with ⟨i1⟩ | ⟨k1, t1, et1, ht1⟩ | ⟨u1, l1, hl1⟩ | ⟨n1, us1, nm1, ls1, hn1, hls1⟩ | ⟨f1, a1, ef1, ea1, hf1, ha1⟩ | ⟨ty1, bd1, m1, et1, eb1, hty1, hbd1⟩ | ⟨ty1, bd1, m1, et1, eb1, hty1, hbd1⟩ | ⟨ty1, w1, bd1, et1, ew1, eb1, hty1, hw1, hbd1⟩ | ⟨lit1⟩ | ⟨pn1, pi1, ps1, pnm1, pes1, hpn1, hps1⟩
    · -- left: bvar
      rcases hB with ⟨i2⟩ | ⟨k2, t2, et2, ht2⟩ | ⟨u2, l2, hl2⟩ | ⟨n2, us2, nm2, ls2, hn2, hls2⟩ | ⟨f2, a2, ef2, ea2, hf2, ha2⟩ | ⟨ty2, bd2, m2, et2, eb2, hty2, hbd2⟩ | ⟨ty2, bd2, m2, et2, eb2, hty2, hbd2⟩ | ⟨ty2, w2, bd2, et2, ew2, eb2, hty2, hw2, hbd2⟩ | ⟨lit2⟩ | ⟨pn2, pi2, ps2, pnm2, pes2, hpn2, hps2⟩
      · exact qd_none_exit hok hne (by simp only [exprTag]; decide)
      · exact qd_none_exit hok hne (by simp only [exprTag]; decide)
      · exact qd_none_exit hok hne (by simp only [exprTag]; decide)
      · exact qd_none_exit hok hne (by simp only [exprTag]; decide)
      · exact qd_none_exit hok hne (by simp only [exprTag]; decide)
      · exact qd_none_exit hok hne (by simp only [exprTag]; decide)
      · exact qd_none_exit hok hne (by simp only [exprTag]; decide)
      · exact qd_none_exit hok hne (by simp only [exprTag]; decide)
      · exact qd_none_exit hok hne (by simp only [exprTag]; decide)
      · exact qd_none_exit hok hne (by simp only [exprTag]; decide)
    · -- left: fvar
      rcases hB with ⟨i2⟩ | ⟨k2, t2, et2, ht2⟩ | ⟨u2, l2, hl2⟩ | ⟨n2, us2, nm2, ls2, hn2, hls2⟩ | ⟨f2, a2, ef2, ea2, hf2, ha2⟩ | ⟨ty2, bd2, m2, et2, eb2, hty2, hbd2⟩ | ⟨ty2, bd2, m2, et2, eb2, hty2, hbd2⟩ | ⟨ty2, w2, bd2, et2, ew2, eb2, hty2, hw2, hbd2⟩ | ⟨lit2⟩ | ⟨pn2, pi2, ps2, pnm2, pes2, hpn2, hps2⟩
      · exact qd_none_exit hok hne (by simp only [exprTag]; decide)
      · exact qd_none_exit hok hne (by simp only [exprTag]; decide)
      · exact qd_none_exit hok hne (by simp only [exprTag]; decide)
      · exact qd_none_exit hok hne (by simp only [exprTag]; decide)
      · exact qd_none_exit hok hne (by simp only [exprTag]; decide)
      · exact qd_none_exit hok hne (by simp only [exprTag]; decide)
      · exact qd_none_exit hok hne (by simp only [exprTag]; decide)
      · exact qd_none_exit hok hne (by simp only [exprTag]; decide)
      · exact qd_none_exit hok hne (by simp only [exprTag]; decide)
      · exact qd_none_exit hok hne (by simp only [exprTag]; decide)
    · -- left: sort
      rcases hB with ⟨i2⟩ | ⟨k2, t2, et2, ht2⟩ | ⟨u2, l2, hl2⟩ | ⟨n2, us2, nm2, ls2, hn2, hls2⟩ | ⟨f2, a2, ef2, ea2, hf2, ha2⟩ | ⟨ty2, bd2, m2, et2, eb2, hty2, hbd2⟩ | ⟨ty2, bd2, m2, et2, eb2, hty2, hbd2⟩ | ⟨ty2, w2, bd2, et2, ew2, eb2, hty2, hw2, hbd2⟩ | ⟨lit2⟩ | ⟨pn2, pi2, ps2, pnm2, pes2, hpn2, hps2⟩
      · exact qd_none_exit hok hne (by simp only [exprTag]; decide)
      · exact qd_none_exit hok hne (by simp only [exprTag]; decide)
      · exact qdArm_sort u1 u2 l1 l2 hok hl1 hl2 hne
      · exact qd_none_exit hok hne (by simp only [exprTag]; decide)
      · exact qd_none_exit hok hne (by simp only [exprTag]; decide)
      · exact qd_none_exit hok hne (by simp only [exprTag]; decide)
      · exact qd_none_exit hok hne (by simp only [exprTag]; decide)
      · exact qd_none_exit hok hne (by simp only [exprTag]; decide)
      · exact qd_none_exit hok hne (by simp only [exprTag]; decide)
      · exact qd_none_exit hok hne (by simp only [exprTag]; decide)
    · -- left: const
      rcases hB with ⟨i2⟩ | ⟨k2, t2, et2, ht2⟩ | ⟨u2, l2, hl2⟩ | ⟨n2, us2, nm2, ls2, hn2, hls2⟩ | ⟨f2, a2, ef2, ea2, hf2, ha2⟩ | ⟨ty2, bd2, m2, et2, eb2, hty2, hbd2⟩ | ⟨ty2, bd2, m2, et2, eb2, hty2, hbd2⟩ | ⟨ty2, w2, bd2, et2, ew2, eb2, hty2, hw2, hbd2⟩ | ⟨lit2⟩ | ⟨pn2, pi2, ps2, pnm2, pes2, hpn2, hps2⟩
      · exact qd_none_exit hok hne (by simp only [exprTag]; decide)
      · exact qd_none_exit hok hne (by simp only [exprTag]; decide)
      · exact qd_none_exit hok hne (by simp only [exprTag]; decide)
      · exact qd_none_exit hok hne (by simp only [exprTag]; decide)
      · exact qd_none_exit hok hne (by simp only [exprTag]; decide)
      · exact qd_none_exit hok hne (by simp only [exprTag]; decide)
      · exact qd_none_exit hok hne (by simp only [exprTag]; decide)
      · exact qd_none_exit hok hne (by simp only [exprTag]; decide)
      · exact qd_none_exit hok hne (by simp only [exprTag]; decide)
      · exact qd_none_exit hok hne (by simp only [exprTag]; decide)
    · -- left: app
      rcases hB with ⟨i2⟩ | ⟨k2, t2, et2, ht2⟩ | ⟨u2, l2, hl2⟩ | ⟨n2, us2, nm2, ls2, hn2, hls2⟩ | ⟨f2, a2, ef2, ea2, hf2, ha2⟩ | ⟨ty2, bd2, m2, et2, eb2, hty2, hbd2⟩ | ⟨ty2, bd2, m2, et2, eb2, hty2, hbd2⟩ | ⟨ty2, w2, bd2, et2, ew2, eb2, hty2, hw2, hbd2⟩ | ⟨lit2⟩ | ⟨pn2, pi2, ps2, pnm2, pes2, hpn2, hps2⟩
      · exact qd_none_exit hok hne (by simp only [exprTag]; decide)
      · exact qd_none_exit hok hne (by simp only [exprTag]; decide)
      · exact qd_none_exit hok hne (by simp only [exprTag]; decide)
      · exact qd_none_exit hok hne (by simp only [exprTag]; decide)
      · exact qd_none_exit hok hne (by simp only [exprTag]; decide)
      · exact qd_none_exit hok hne (by simp only [exprTag]; decide)
      · exact qd_none_exit hok hne (by simp only [exprTag]; decide)
      · exact qd_none_exit hok hne (by simp only [exprTag]; decide)
      · exact qd_none_exit hok hne (by simp only [exprTag]; decide)
      · exact qd_none_exit hok hne (by simp only [exprTag]; decide)
    · -- left: lam
      rcases hB with ⟨i2⟩ | ⟨k2, t2, et2, ht2⟩ | ⟨u2, l2, hl2⟩ | ⟨n2, us2, nm2, ls2, hn2, hls2⟩ | ⟨f2, a2, ef2, ea2, hf2, ha2⟩ | ⟨ty2, bd2, m2, et2, eb2, hty2, hbd2⟩ | ⟨ty2, bd2, m2, et2, eb2, hty2, hbd2⟩ | ⟨ty2, w2, bd2, et2, ew2, eb2, hty2, hw2, hbd2⟩ | ⟨lit2⟩ | ⟨pn2, pi2, ps2, pnm2, pes2, hpn2, hps2⟩
      · exact qd_none_exit hok hne (by simp only [exprTag]; decide)
      · exact qd_none_exit hok hne (by simp only [exprTag]; decide)
      · exact qd_none_exit hok hne (by simp only [exprTag]; decide)
      · exact qd_none_exit hok hne (by simp only [exprTag]; decide)
      · exact qd_none_exit hok hne (by simp only [exprTag]; decide)
      · exact qdArm_binder hsim true ty1 bd1 ty2 bd2 m1 m2 et1 eb1 et2 eb2 hok hty1 hbd1 hty2 hbd2 hwx hwy hne
      · exact qd_none_exit hok hne (by simp only [exprTag]; decide)
      · exact qd_none_exit hok hne (by simp only [exprTag]; decide)
      · exact qd_none_exit hok hne (by simp only [exprTag]; decide)
      · exact qd_none_exit hok hne (by simp only [exprTag]; decide)
    · -- left: forallE
      rcases hB with ⟨i2⟩ | ⟨k2, t2, et2, ht2⟩ | ⟨u2, l2, hl2⟩ | ⟨n2, us2, nm2, ls2, hn2, hls2⟩ | ⟨f2, a2, ef2, ea2, hf2, ha2⟩ | ⟨ty2, bd2, m2, et2, eb2, hty2, hbd2⟩ | ⟨ty2, bd2, m2, et2, eb2, hty2, hbd2⟩ | ⟨ty2, w2, bd2, et2, ew2, eb2, hty2, hw2, hbd2⟩ | ⟨lit2⟩ | ⟨pn2, pi2, ps2, pnm2, pes2, hpn2, hps2⟩
      · exact qd_none_exit hok hne (by simp only [exprTag]; decide)
      · exact qd_none_exit hok hne (by simp only [exprTag]; decide)
      · exact qd_none_exit hok hne (by simp only [exprTag]; decide)
      · exact qd_none_exit hok hne (by simp only [exprTag]; decide)
      · exact qd_none_exit hok hne (by simp only [exprTag]; decide)
      · exact qd_none_exit hok hne (by simp only [exprTag]; decide)
      · exact qdArm_binder hsim false ty1 bd1 ty2 bd2 m1 m2 et1 eb1 et2 eb2 hok hty1 hbd1 hty2 hbd2 hwx hwy hne
      · exact qd_none_exit hok hne (by simp only [exprTag]; decide)
      · exact qd_none_exit hok hne (by simp only [exprTag]; decide)
      · exact qd_none_exit hok hne (by simp only [exprTag]; decide)
    · -- left: letE
      rcases hB with ⟨i2⟩ | ⟨k2, t2, et2, ht2⟩ | ⟨u2, l2, hl2⟩ | ⟨n2, us2, nm2, ls2, hn2, hls2⟩ | ⟨f2, a2, ef2, ea2, hf2, ha2⟩ | ⟨ty2, bd2, m2, et2, eb2, hty2, hbd2⟩ | ⟨ty2, bd2, m2, et2, eb2, hty2, hbd2⟩ | ⟨ty2, w2, bd2, et2, ew2, eb2, hty2, hw2, hbd2⟩ | ⟨lit2⟩ | ⟨pn2, pi2, ps2, pnm2, pes2, hpn2, hps2⟩
      · exact qd_none_exit hok hne (by simp only [exprTag]; decide)
      · exact qd_none_exit hok hne (by simp only [exprTag]; decide)
      · exact qd_none_exit hok hne (by simp only [exprTag]; decide)
      · exact qd_none_exit hok hne (by simp only [exprTag]; decide)
      · exact qd_none_exit hok hne (by simp only [exprTag]; decide)
      · exact qd_none_exit hok hne (by simp only [exprTag]; decide)
      · exact qd_none_exit hok hne (by simp only [exprTag]; decide)
      · exact qd_none_exit hok hne (by simp only [exprTag]; decide)
      · exact qd_none_exit hok hne (by simp only [exprTag]; decide)
      · exact qd_none_exit hok hne (by simp only [exprTag]; decide)
    · -- left: lit
      rcases hB with ⟨i2⟩ | ⟨k2, t2, et2, ht2⟩ | ⟨u2, l2, hl2⟩ | ⟨n2, us2, nm2, ls2, hn2, hls2⟩ | ⟨f2, a2, ef2, ea2, hf2, ha2⟩ | ⟨ty2, bd2, m2, et2, eb2, hty2, hbd2⟩ | ⟨ty2, bd2, m2, et2, eb2, hty2, hbd2⟩ | ⟨ty2, w2, bd2, et2, ew2, eb2, hty2, hw2, hbd2⟩ | ⟨lit2⟩ | ⟨pn2, pi2, ps2, pnm2, pes2, hpn2, hps2⟩
      · exact qd_none_exit hok hne (by simp only [exprTag]; decide)
      · exact qd_none_exit hok hne (by simp only [exprTag]; decide)
      · exact qd_none_exit hok hne (by simp only [exprTag]; decide)
      · exact qd_none_exit hok hne (by simp only [exprTag]; decide)
      · exact qd_none_exit hok hne (by simp only [exprTag]; decide)
      · exact qd_none_exit hok hne (by simp only [exprTag]; decide)
      · exact qd_none_exit hok hne (by simp only [exprTag]; decide)
      · exact qd_none_exit hok hne (by simp only [exprTag]; decide)
      · exact qdArm_lit hok hne
      · exact qd_none_exit hok hne (by simp only [exprTag]; decide)
    · -- left: proj
      rcases hB with ⟨i2⟩ | ⟨k2, t2, et2, ht2⟩ | ⟨u2, l2, hl2⟩ | ⟨n2, us2, nm2, ls2, hn2, hls2⟩ | ⟨f2, a2, ef2, ea2, hf2, ha2⟩ | ⟨ty2, bd2, m2, et2, eb2, hty2, hbd2⟩ | ⟨ty2, bd2, m2, et2, eb2, hty2, hbd2⟩ | ⟨ty2, w2, bd2, et2, ew2, eb2, hty2, hw2, hbd2⟩ | ⟨lit2⟩ | ⟨pn2, pi2, ps2, pnm2, pes2, hpn2, hps2⟩
      · exact qd_none_exit hok hne (by simp only [exprTag]; decide)
      · exact qd_none_exit hok hne (by simp only [exprTag]; decide)
      · exact qd_none_exit hok hne (by simp only [exprTag]; decide)
      · exact qd_none_exit hok hne (by simp only [exprTag]; decide)
      · exact qd_none_exit hok hne (by simp only [exprTag]; decide)
      · exact qd_none_exit hok hne (by simp only [exprTag]; decide)
      · exact qd_none_exit hok hne (by simp only [exprTag]; decide)
      · exact qd_none_exit hok hne (by simp only [exprTag]; decide)
      · exact qd_none_exit hok hne (by simp only [exprTag]; decide)
      · exact qd_none_exit hok hne (by simp only [exprTag]; decide)

  · rename_i hk
    exact qd_none_exit hok hne (by
      rintro ⟨_, h2⟩; apply hk; rcases h2 with h | h | h | h <;> simp [h])

/-! ## 2. Offsets: `isNatZero`, `natPred?`, `defeqOffset` -/

section Offsets

variable {fe : IFEnv}

/-- con-leche: ConLeche/Kernel/Core.lean:1517-1521 Expr.isNatZero — **THEOREM
1 for the zero test**: read-only, and con-leche's answer. -/
theorem isNatZero_spec (s₀ : AState) (e : EIdx) (x : Expr)
    (hok : CheckOK mode env fe s₀) (hx : denoteE s₀.store e = some x) :
    ⦃fun s => ⌜s = s₀⌝⦄ ConRon.Arena.isNatZero e
    ⦃⇓? r s' => ⌜s' = s₀ ∧ r = x.isNatZero⌝⦄ := by
  have hwf := hok.state.wf
  obtain ⟨v, hv⟩ := denoteE_view hx
  unfold ConRon.Arena.isNatZero
  rw [tag_of_denote hwf hx]
  rcases VD.of_view hwf hv hx with _ | _ | _ | ⟨c, us, nm, ls, hc, hus⟩ | _ |
    _ | _ | _ | ⟨l⟩ | _
  case lit =>
    rw [if_pos (by tag_dec)]
    refine view_bind_triple hv ?_
    rcases l with n | st
    · cases n <;> exact triple_pure_post ⟨rfl, rfl⟩
    · exact triple_pure_post ⟨rfl, rfl⟩
  case const =>
    rw [if_neg (by tag_dec), if_pos (by tag_dec)]
    refine view_bind_triple hv ?_
    refine triple_seq (pinEmptyLevels_spec s₀ hok.pins) ?_
    rintro el s2 ⟨hs2, hel⟩
    subst s2
    refine triple_seq (pinAt_spec s₀ PIN_NAT_ZERO hok.pins) ?_
    rintro nz s3 ⟨hs3, hnz⟩
    subst s3
    refine triple_pure_post ⟨rfl, ?_⟩
    rw [beq_handle_eq hwf hc (hnz _ rfl)]
    cases ls with
    | nil =>
      have : (us == el) = true := beq_iff_eq.mpr ((ls_eq_iff_nil hwf hus hel).mpr rfl)
      rw [this, Bool.and_true]; rfl
    | cons l ls =>
      have : (us == el) = false := by
        cases h : us == el
        · rfl
        · exact absurd ((ls_eq_iff_nil hwf hus hel).mp (beq_iff_eq.mp h)) (by simp)
      rw [this, Bool.and_false]; rfl
  all_goals
    rw [if_neg (by tag_dec), if_neg (by tag_dec)]
    exact triple_pure_post ⟨rfl, rfl⟩

/-- con-leche: ConLeche/Kernel/Core.lean:1528-1533 Expr.natPred? — a
predecessor of a well-scoped term is well-scoped. -/
theorem natPred?_WScoped {d : Nat} {x p : Expr} (h : x.natPred? = some p)
    (hw : Expr.WScoped d x) : Expr.WScoped d p := by
  unfold ConLeche.Expr.natPred? at h
  split at h
  · cases h; simp [Expr.WScoped]
  · split at h
    · cases h; simp only [Expr.WScoped] at hw; exact hw.2
    · cases h
  · cases h

/-- con-leche: ConLeche/Kernel/Core.lean:1528-1533 Expr.natPred? — **THEOREM 1
for the predecessor**: a nonzero literal's predecessor is interned, a
`Nat.succ x` answers `x`. -/
theorem natPred?_spec (s₀ : AState) (e : EIdx) (x : Expr)
    (hok : CheckOK mode env fe s₀) (hx : denoteE s₀.store e = some x) :
    ⦃fun s => ⌜s = s₀⌝⦄ ConRon.Arena.natPred? e
    ⦃⇓? o s' => ⌜CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧ denoteEO s'.store o = some x.natPred?⌝⦄ := by
  have hwf := hok.state.wf
  obtain ⟨v, hv⟩ := denoteE_view hx
  unfold ConRon.Arena.natPred?
  have htg := tag_of_denote hwf hx
  rw [htg]
  rcases VD.of_view hwf hv hx with _ | _ | _ | _ | ⟨f, a, ef, ea, hf, ha⟩ |
    _ | _ | _ | ⟨l⟩ | _
  case lit =>
    rw [if_pos (by tag_dec)]
    refine view_bind_triple hv ?_
    rcases l with n | st
    · cases n with
      | zero => exact triple_pure_post ⟨hok, Ext.refl _, rfl, rfl⟩
      | succ n =>
        refine triple_seq (internE_ok_spec s₀ (.lit (.natVal n)) hok viewOK_lit) ?_
        rintro l s1 ⟨hok1, hx1, hp1, hd1⟩
        exact triple_pure_post ⟨hok1, hx1, hp1, by
          simp only [denoteEO, hd1, denoteEView]; rfl⟩
    · exact triple_pure_post ⟨hok, Ext.refl _, rfl, rfl⟩
  case app =>
    rw [if_neg (by tag_dec), if_pos (by tag_dec)]
    refine triple_seq (viewApp_spec s₀ e) ?_
    rintro p s1 ⟨hs1, rfl⟩
    subst s1
    cases hva : s₀.store.viewApp e with
    | none => exact triple_failDanglingE
    | some p =>
    obtain ⟨f', a'⟩ := p
    have hv' := view_of_viewApp htg hva
    rw [hv] at hv'
    cases hv'
    dsimp only
    obtain ⟨vf, hvf⟩ := denoteE_view hf
    refine tag_view_bind_triple hvf ?_
      (fun hne => by cases vf <;> first | rfl | exact absurd rfl hne)
    rcases VD.of_view hwf hvf hf with _ | _ | _ | ⟨c, us, nm, ls, hc, hus⟩ | _ |
      _ | _ | _ | _ | _
    case const =>
      refine triple_seq (pinEmptyLevels_spec s₀ hok.pins) ?_
      rintro el s2 ⟨hs2, hel⟩
      subst s2
      refine triple_seq (pinAt_spec s₀ PIN_NAT_SUCC hok.pins) ?_
      rintro ns s3 ⟨hs3, hns⟩
      subst s3
      have hiff : (c = ns ∧ us = el) ↔ (nm = ConLeche.natSuccName ∧ ls = []) := by
        rw [n_eq_iff_pin hwf hc (hns _ rfl), ls_eq_iff_nil hwf hus hel]
      split
      · rename_i h
        simp only [Bool.and_eq_true, beq_iff_eq] at h
        obtain ⟨rfl, rfl⟩ := hiff.mp h
        exact triple_pure_post ⟨hok, Ext.refl _, rfl, by
          simp [denoteEO, ha, ConLeche.Expr.natPred?]⟩
      · rename_i h
        simp only [Bool.and_eq_true, beq_iff_eq] at h
        refine triple_pure_post ⟨hok, Ext.refl _, rfl, ?_⟩
        cases ls with
        | nil =>
          have hne : ¬ nm = ConLeche.natSuccName :=
            fun h' => h (hiff.mpr ⟨h', rfl⟩)
          simp [denoteEO, ConLeche.Expr.natPred?, hne]
        | cons _ _ => simp [denoteEO, ConLeche.Expr.natPred?]
    all_goals
      exact triple_pure_post ⟨hok, Ext.refl _, rfl, by
        simp [denoteEO, ConLeche.Expr.natPred?]⟩
  all_goals
    rw [if_neg (by tag_dec), if_neg (by tag_dec)]
    exact triple_pure_post ⟨hok, Ext.refl _, rfl, rfl⟩

/-- con-leche: ConLeche/Kernel/Core.lean:1523-1526 Expr.isLit — the twin's
tag test IS con-leche's `isLit`. -/
theorem exprTag_lit (x : Expr) : (exprTag x == ETag.lit) = x.isLit := by
  cases x <;> simp only [exprTag, ConLeche.Expr.isLit] <;> decide

/-- con-leche: ConLeche/Kernel/Core.lean:1535-1547 defeqOffset — **THEOREM 1
for the offset check**: the two zero tests, the literal guard, the two
predecessors, and the knot on the predecessors. -/
theorem defeqOffset_spec {fuel : Nat} (hsim : KnotSpec mode env fe fuel)
    (d : Nat) (s₀ : AState) (a b : EIdx) (x y : Expr)
    (hok : CheckOK mode env fe s₀)
    (hx : denoteE s₀.store a = some x) (hy : denoteE s₀.store b = some y)
    (hwx : Expr.WScoped d x) (hwy : Expr.WScoped d y) :
    ⦃fun s => ⌜s = s₀⌝⦄ ConRon.Arena.defeqOffset (coreKnot mode fe id fuel) d a b
    ⦃⇓? o s' => ⌜CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧
        Ev (fun F => ConLeche.defeqOffset (ConLeche.pureFns mode env F) d x y
          = .ok o)⌝⦄ := by
  have hwf := hok.state.wf
  unfold ConRon.Arena.defeqOffset
  refine triple_seq (isNatZero_spec s₀ a x hok hx) ?_
  rintro za s1 ⟨hs1, rfl⟩
  subst s1
  refine triple_seq (isNatZero_spec s₀ b y hok hy) ?_
  rintro zb s1 ⟨hs1, rfl⟩
  subst s1
  split
  · rename_i hz
    exact triple_pure_post ⟨hok, Ext.refl _, rfl, ⟨0, fun _ _ => by
      dsimp only; unfold ConLeche.defeqOffset; rw [if_pos hz]; rfl⟩⟩
  rename_i hz
  rw [tag_of_denote hwf hx, tag_of_denote hwf hy, exprTag_lit, exprTag_lit]
  split
  · rename_i hl
    exact triple_pure_post ⟨hok, Ext.refl _, rfl, ⟨0, fun _ _ => by
      dsimp only; unfold ConLeche.defeqOffset; rw [if_neg hz, if_pos hl]; rfl⟩⟩
  rename_i hl
  refine triple_seq (natPred?_spec s₀ a x hok hx) ?_
  rintro o1 s1 ⟨hok1, hx1, hp1, ho1⟩
  cases o1 with
  | none =>
    have hn : x.natPred? = none := by
      simp only [denoteEO, Option.some.injEq] at ho1; exact ho1.symm
    exact triple_pure_post ⟨hok1, hx1, hp1, ⟨0, fun F _ => by
      dsimp only; unfold ConLeche.defeqOffset; rw [if_neg hz, if_neg hl, hn]; rfl⟩⟩
  | some p =>
    obtain ⟨px, hpx, hdp⟩ : ∃ px, x.natPred? = some px ∧
        denoteE s1.store p = some px := by
      simp only [denoteEO, Option.map_eq_some_iff] at ho1
      obtain ⟨px, hd, he⟩ := ho1
      exact ⟨px, he.symm, hd⟩
    dsimp only
    refine triple_seq (natPred?_spec s1 b y hok1 (denote_ext hy hx1)) ?_
    rintro o2 s2 ⟨hok2, hx2, hp2, ho2⟩
    cases o2 with
    | none =>
      have hn : y.natPred? = none := by
        simp only [denoteEO, Option.some.injEq] at ho2; exact ho2.symm
      exact triple_pure_post ⟨hok2, hx1.trans hx2, hp2.trans hp1, ⟨0, fun F _ => by
        dsimp only; unfold ConLeche.defeqOffset
        rw [if_neg hz, if_neg hl, hpx, hn]; rfl⟩⟩
    | some q =>
      obtain ⟨qy, hqy, hdq⟩ : ∃ qy, y.natPred? = some qy ∧
          denoteE s2.store q = some qy := by
        simp only [denoteEO, Option.map_eq_some_iff] at ho2
        obtain ⟨qy, hd, he⟩ := ho2
        exact ⟨qy, he.symm, hd⟩
      dsimp only
      refine triple_seq (hsim.defeq s2 d p q px qy hok2 (denote_ext hdp hx2) hdq
        (natPred?_WScoped hpx hwx) (natPred?_WScoped hqy hwy)) ?_
      rintro ok s3 ⟨hok3, hx3, hp3, F3, hF3⟩
      exact triple_pure_post ⟨hok3, (hx1.trans hx2).trans hx3,
        hp3.trans (hp2.trans hp1), ⟨F3, fun F hF => by
          dsimp only
          unfold ConLeche.defeqOffset
          rw [if_neg hz, if_neg hl, hpx, hqy]
          simp only [ConLeche.defeq_def, ConLeche.isDefEqCore_mono hF hF3, bind,
            Except.bind, pure, Except.pure]⟩⟩

end Offsets

/-! ## 3. Projection heads: `headIsProj`, `tryUnfoldProjApp` -/

section ProjHeads

variable {fe : IFEnv}

/-- con-leche: ConLeche/Kernel/Core.lean:1549-1553 Expr.headIsProj — the tag
test IS con-leche's constructor match. -/
theorem exprTag_proj (z : Expr) :
    (exprTag z == ETag.proj) = (match z with | .proj _ _ _ => true | _ => false) := by
  cases z <;> simp only [exprTag] <;> decide

/-- con-leche: ConLeche/Kernel/Core.lean:1549-1553 Expr.headIsProj — **THEOREM
1 for the projection-head test**: read-only. -/
theorem headIsProj_spec (s₀ : AState) (e : EIdx) (x : Expr)
    (hok : CheckOK mode env fe s₀) (hx : denoteE s₀.store e = some x) :
    ⦃fun s => ⌜s = s₀⌝⦄ ConRon.Arena.headIsProj e
    ⦃⇓? r s' => ⌜s' = s₀ ∧ r = x.headIsProj⌝⦄ := by
  unfold ConRon.Arena.headIsProj
  refine triple_seq (ExprOps.getAppFn_spec coreWalkFuel s₀ e hok.state
    (by rw [hx]; rfl)) ?_
  rintro h s1 ⟨hs1, hh⟩
  subst s1
  refine triple_pure_post ⟨rfl, ?_⟩
  rw [tag_of_denote hok.state.wf (hh x hx), exprTag_proj]
  rfl

/-- con-leche: ConLeche/Kernel/Core.lean:1555-1563 tryUnfoldProjApp — **THEOREM
1 for the projection-application unfolding**: the head test, the FULL
`whnfCore` through the knot, and handle equality as syntactic equality. -/
theorem tryUnfoldProjApp_spec {fuel : Nat} (hsim : KnotSpec mode env fe fuel)
    (d : Nat) (s₀ : AState) (e : EIdx) (x : Expr)
    (hok : CheckOK mode env fe s₀) (hx : denoteE s₀.store e = some x)
    (hwx : Expr.WScoped d x) :
    ⦃fun s => ⌜s = s₀⌝⦄ ConRon.Arena.tryUnfoldProjApp (coreKnot mode fe id fuel) d e
    ⦃⇓? o s' => ⌜CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧
        ∃ v, denoteEO s'.store o = some v ∧ (∀ z, v = some z → Expr.WScoped d z) ∧
          Ev (fun F => ConLeche.tryUnfoldProjApp (ConLeche.pureFns mode env F) d x
            = .ok v)⌝⦄ := by
  unfold ConRon.Arena.tryUnfoldProjApp
  refine triple_seq (headIsProj_spec s₀ e x hok hx) ?_
  rintro hp s1 ⟨hs1, rfl⟩
  subst s1
  split
  · rename_i hh
    refine triple_seq (hsim.whnfCore (c := false) s₀ d e x hok hx hwx) ?_
    rintro e' s1 ⟨hok1, hx1, hp1, v, hv, hwv, F1, hF1⟩
    have hE : Ev (fun F => ConLeche.whnfCore mode env F d x false = .ok v) :=
      Ev.of_mono (fun hle h => ConLeche.whnfCore_mono hle h) ⟨F1, hF1⟩
    have hbeq := beq_of_denoteE hok1.state.wf hv (denote_ext hx hx1)
    split
    · rename_i heq
      rw [hbeq] at heq
      exact triple_pure_post ⟨hok1, hx1, hp1, none, rfl, (fun _ h => nomatch h),
        hE.imp fun F hF => by
          unfold ConLeche.tryUnfoldProjApp
          simp only [hh, if_true, ConLeche.whnfCore_def, hF, heq, bind,
            Except.bind, pure, Except.pure]⟩
    · rename_i heq
      rw [hbeq] at heq
      exact triple_pure_post ⟨hok1, hx1, hp1, some v, by simp [denoteEO, hv],
        (fun _ h => by cases h; exact hwv),
        hE.imp fun F hF => by
          unfold ConLeche.tryUnfoldProjApp
          simp only [hh, if_true, ConLeche.whnfCore_def, hF, heq, bind,
            Except.bind, pure, Except.pure, Bool.false_eq_true, if_false]⟩
  · rename_i hh
    exact triple_pure_post ⟨hok, Ext.refl _, rfl, none, rfl, (fun _ h => nomatch h),
      ⟨0, fun _ _ => by
        dsimp only; unfold ConLeche.tryUnfoldProjApp; rw [if_neg hh]; rfl⟩⟩

end ProjHeads

/-! ## 4. One lazy-delta step: `deltaQuick`, `lazyDeltaStep` -/

/-- con-leche: ConLeche/Kernel/Core.lean:1565-1572 DeltaStep — **the answer
relation of a lazy-delta step**: the same outcome, and at `cont` the two
handles denote the two terms, both well scoped. -/
def DSRel (st : EStore) (d : Nat) : DeltaStepA → DeltaStep → Prop
  | .cont a b, .cont x y => denoteE st a = some x ∧ denoteE st b = some y ∧
      Expr.WScoped d x ∧ Expr.WScoped d y
  | .eq, .eq => True
  | .diff, .diff => True
  | .unknown, .unknown => True
  | _, _ => False

/-- con-leche: none — `DSRel` survives store growth. -/
theorem DSRel.ext {st st' : EStore} {d : Nat} {o : DeltaStepA} {v : DeltaStep}
    (h : DSRel st d o v) (hx : Ext st st') : DSRel st' d o v := by
  cases o <;> cases v <;> simp only [DSRel] at h ⊢
  exact ⟨denote_ext h.1 hx, denote_ext h.2.1 hx, h.2.2⟩

section Step

variable {fe : IFEnv}

/-- con-leche: ConLeche/Kernel/Core.lean:1574-1579 deltaQuick — **THEOREM 1
for the end of a step**: `quickDefEq` on the new pair. -/
theorem deltaQuick_spec {fuel : Nat} (hsim : KnotSpec mode env fe fuel)
    (d : Nat) (s₀ : AState) (a b : EIdx) (x y : Expr)
    (hok : CheckOK mode env fe s₀)
    (hx : denoteE s₀.store a = some x) (hy : denoteE s₀.store b = some y)
    (hwx : Expr.WScoped d x) (hwy : Expr.WScoped d y) :
    ⦃fun s => ⌜s = s₀⌝⦄ ConRon.Arena.deltaQuick mode (coreKnot mode fe id fuel) d a b
    ⦃⇓? o s' => ⌜CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧
        ∃ v, DSRel s'.store d o v ∧
          Ev (fun F => ConLeche.deltaQuick mode (ConLeche.pureFns mode env F) d x y
            = .ok v)⌝⦄ := by
  unfold ConRon.Arena.deltaQuick
  refine triple_seq (quickDefEq_spec hsim d s₀ a b x y hok hx hy hwx hwy) ?_
  rintro q s1 ⟨hok1, hx1, hp1, hq⟩
  have fin : ∀ (o : DeltaStepA) (v : DeltaStep), DSRel s1.store d o v →
      (∀ F, ConLeche.quickDefEq mode (ConLeche.pureFns mode env F) d x y = .ok q →
        ConLeche.deltaQuick mode (ConLeche.pureFns mode env F) d x y = .ok v) →
      ⦃fun s => ⌜s = s1⌝⦄ (pure o : AM DeltaStepA)
      ⦃⇓? o s' => ⌜CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧
        ∃ v, DSRel s'.store d o v ∧
          Ev (fun F => ConLeche.deltaQuick mode (ConLeche.pureFns mode env F) d x y
            = .ok v)⌝⦄ := fun o v hr hv =>
    triple_pure_post ⟨hok1, hx1, hp1, v, hr, hq.imp fun F h => hv F h⟩
  rcases q with _ | _ | _
  · exact fin (.cont a b) (.cont x y)
      ⟨denote_ext hx hx1, denote_ext hy hx1, hwx, hwy⟩ (fun F h => by
        unfold ConLeche.deltaQuick
        simp only [h, bind, Except.bind, pure, Except.pure])
  · exact fin .diff .diff trivial (fun F h => by
      unfold ConLeche.deltaQuick
      simp only [h, bind, Except.bind, pure, Except.pure])
  · exact fin .eq .eq trivial (fun F h => by
      unfold ConLeche.deltaQuick
      simp only [h, bind, Except.bind, pure, Except.pure])

end Step

end ConRon.Bridge.Core
