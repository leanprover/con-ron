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

/-- con-leche: none — **the postcondition of a lazy-delta step's stages**: the
frame, and an outcome related to the pure goal's answer `P F`, which holds
eventually. -/
def DSPost (mode : CheckMode) (env : Env) (fe : IFEnv) (s₀ : AState) (d : Nat)
    (P : Nat → CheckM DeltaStep) (o : DeltaStepA) (s' : AState) : Prop :=
  CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧ s'.pins = s₀.pins ∧
    ∃ v, DSRel s'.store d o v ∧ Ev (fun F => P F = .ok v)

section StepExits

variable {fe : IFEnv} {fuel d : Nat} {s₀ s : AState} {P : Nat → CheckM DeltaStep}

/-- con-leche: none — a `pure` outcome. -/
theorem ds_pure_exit {o : DeltaStepA} {v : DeltaStep}
    (hok : CheckOK mode env fe s) (hxs : Ext s₀.store s.store)
    (hps : s.pins = s₀.pins) (hr : DSRel s.store d o v)
    (hP : Ev (fun F => P F = .ok v)) :
    ⦃fun s' => ⌜s' = s⌝⦄ (pure o : AM DeltaStepA)
    ⦃⇓? o s' => ⌜DSPost mode env fe s₀ d P o s'⌝⦄ :=
  triple_pure_post ⟨hok, hxs, hps, v, hr, hP⟩

/-- con-leche: ConLeche/Kernel/Core.lean:1574-1579 deltaQuick — **the step's
end**: `deltaQuick` on a pair the pure goal reduces to. -/
theorem ds_quick_exit (hsim : KnotSpec mode env fe fuel) (p q : EIdx) (u w : Expr)
    (hok : CheckOK mode env fe s) (hxs : Ext s₀.store s.store)
    (hps : s.pins = s₀.pins) (hp : denoteE s.store p = some u)
    (hq : denoteE s.store q = some w) (hwu : Expr.WScoped d u)
    (hww : Expr.WScoped d w)
    (hred : Ev (fun F => P F =
      ConLeche.deltaQuick mode (ConLeche.pureFns mode env F) d u w)) :
    ⦃fun s' => ⌜s' = s⌝⦄ ConRon.Arena.deltaQuick mode (coreKnot mode fe id fuel) d p q
    ⦃⇓? o s' => ⌜DSPost mode env fe s₀ d P o s'⌝⦄ := by
  refine triple_mono (deltaQuick_spec hsim d s p q u w hok hp hq hwu hww) ?_
  rintro o s' ⟨hok', hx', hp', v, hr, hv⟩
  exact ⟨hok', hxs.trans hx', hp'.trans hps, v, hr,
    (hred.and hv).imp fun _ ⟨h1, h2⟩ => h1.trans h2⟩

/-- con-leche: ConLeche/Kernel/Core.lean:1581-1642 lazyDeltaStep — **an
unfolded side through the cheap `whnfCore`, then the step's end**, the
unfolded side on the left. -/
theorem ds_whnf_quick_exit_l (hsim : KnotSpec mode env fe fuel) (p q : EIdx)
    (u w : Expr) (hok : CheckOK mode env fe s) (hxs : Ext s₀.store s.store)
    (hps : s.pins = s₀.pins) (hp : denoteE s.store p = some u)
    (hq : denoteE s.store q = some w) (hwu : Expr.WScoped d u)
    (hww : Expr.WScoped d w)
    (hred : Ev (fun F => ∀ u₃, ConLeche.whnfCore mode env F d u true = .ok u₃ →
      P F = ConLeche.deltaQuick mode (ConLeche.pureFns mode env F) d u₃ w)) :
    ⦃fun s' => ⌜s' = s⌝⦄ (do
        let p₃ ← (coreKnot mode fe id fuel).whnfCore true d p
        ConRon.Arena.deltaQuick mode (coreKnot mode fe id fuel) d p₃ q)
    ⦃⇓? o s' => ⌜DSPost mode env fe s₀ d P o s'⌝⦄ := by
  refine triple_seq (hsim.whnfCore (c := true) s d p u hok hp hwu) ?_
  rintro p₃ s1 ⟨hok1, hx1, hp1, u₃, hd3, hw3, F1, hF1⟩
  have hW : Ev (fun F => ConLeche.whnfCore mode env F d u true = .ok u₃) :=
    Ev.of_mono (fun hle h => ConLeche.whnfCore_mono hle h) ⟨F1, hF1⟩
  exact ds_quick_exit hsim p₃ q u₃ w hok1 (hxs.trans hx1) (hp1.trans hps) hd3
    (denote_ext hq hx1) hw3 hww ((hred.and hW).imp fun _ ⟨h1, h2⟩ => h1 u₃ h2)

/-- con-leche: ConLeche/Kernel/Core.lean:1581-1642 lazyDeltaStep — the same,
the unfolded side on the right. -/
theorem ds_whnf_quick_exit_r (hsim : KnotSpec mode env fe fuel) (p q : EIdx)
    (u w : Expr) (hok : CheckOK mode env fe s) (hxs : Ext s₀.store s.store)
    (hps : s.pins = s₀.pins) (hp : denoteE s.store p = some u)
    (hq : denoteE s.store q = some w) (hwu : Expr.WScoped d u)
    (hww : Expr.WScoped d w)
    (hred : Ev (fun F => ∀ w₃, ConLeche.whnfCore mode env F d w true = .ok w₃ →
      P F = ConLeche.deltaQuick mode (ConLeche.pureFns mode env F) d u w₃)) :
    ⦃fun s' => ⌜s' = s⌝⦄ (do
        let q₃ ← (coreKnot mode fe id fuel).whnfCore true d q
        ConRon.Arena.deltaQuick mode (coreKnot mode fe id fuel) d p q₃)
    ⦃⇓? o s' => ⌜DSPost mode env fe s₀ d P o s'⌝⦄ := by
  refine triple_seq (hsim.whnfCore (c := true) s d q w hok hq hww) ?_
  rintro q₃ s1 ⟨hok1, hx1, hp1, w₃, hd3, hw3, F1, hF1⟩
  have hW : Ev (fun F => ConLeche.whnfCore mode env F d w true = .ok w₃) :=
    Ev.of_mono (fun hle h => ConLeche.whnfCore_mono hle h) ⟨F1, hF1⟩
  exact ds_quick_exit hsim p q₃ u w₃ hok1 (hxs.trans hx1) (hp1.trans hps)
    (denote_ext hp hx1) hd3 hwu hw3 ((hred.and hW).imp fun _ ⟨h1, h2⟩ => h1 w₃ h2)

/-- con-leche: ConLeche/Kernel/CoreDefs.lean unfoldDefinition — **an unfolding
and what follows it**, in the step's postcondition. -/
theorem ds_unfold_seq (henv : ConLeche.EnvWF env) (e : EIdx) (u : Expr)
    (f : Option EIdx → AM DeltaStepA)
    (hok : CheckOK mode env fe s) (he : denoteE s.store e = some u)
    (hwu : Expr.WScoped d u)
    (hsome : ∀ (s' : AState) (e₂ : EIdx) (u₂ : Expr),
      CheckOK mode env fe s' → Ext s.store s'.store → s'.pins = s.pins →
      denoteE s'.store e₂ = some u₂ → Expr.WScoped d u₂ →
      unfoldDefinition env u = some u₂ →
      ⦃fun t => ⌜t = s'⌝⦄ f (some e₂) ⦃⇓? r t => ⌜DSPost mode env fe s₀ d P r t⌝⦄)
    (hnone : ∀ (s' : AState), CheckOK mode env fe s' →
      Ext s.store s'.store → s'.pins = s.pins →
      unfoldDefinition env u = none →
      ⦃fun t => ⌜t = s'⌝⦄ f none ⦃⇓? r t => ⌜DSPost mode env fe s₀ d P r t⌝⦄) :
    ⦃fun t => ⌜t = s⌝⦄ (ConRon.Arena.unfoldDefinition fe e >>= f)
    ⦃⇓? r t => ⌜DSPost mode env fe s₀ d P r t⌝⦄ := by
  refine triple_seq (unfoldDefinition_spec henv s d e hok ⟨u, he, hwu⟩) ?_
  rintro o s1 ⟨hok1, hx1, hp1, ho⟩
  obtain ⟨hdo, hwo⟩ := ho u he
  cases o with
  | some e₂ =>
    obtain ⟨u₂, hu₂, hd₂⟩ := denoteEO_some_inv hdo
    exact hsome s1 e₂ u₂ hok1 hx1 hp1 hd₂ (hwo u₂ hu₂) hu₂
  | none =>
    exact hnone s1 hok1 hx1 hp1 (denoteEO_none_inv hdo)

/-- con-leche: ConLeche/Kernel/Core.lean:1555-1563 tryUnfoldProjApp — **the
projection-application probe and what follows it**. -/
theorem ds_try_seq (hsim : KnotSpec mode env fe fuel) (e : EIdx) (u : Expr)
    (f : Option EIdx → AM DeltaStepA)
    (hok : CheckOK mode env fe s) (he : denoteE s.store e = some u)
    (hwu : Expr.WScoped d u)
    (hsome : ∀ (s' : AState) (e₂ : EIdx) (u₂ : Expr),
      CheckOK mode env fe s' → Ext s.store s'.store → s'.pins = s.pins →
      denoteE s'.store e₂ = some u₂ → Expr.WScoped d u₂ →
      Ev (fun F => ConLeche.tryUnfoldProjApp (ConLeche.pureFns mode env F) d u
        = .ok (some u₂)) →
      ⦃fun t => ⌜t = s'⌝⦄ f (some e₂) ⦃⇓? r t => ⌜DSPost mode env fe s₀ d P r t⌝⦄)
    (hnone : ∀ (s' : AState), CheckOK mode env fe s' →
      Ext s.store s'.store → s'.pins = s.pins →
      Ev (fun F => ConLeche.tryUnfoldProjApp (ConLeche.pureFns mode env F) d u
        = .ok none) →
      ⦃fun t => ⌜t = s'⌝⦄ f none ⦃⇓? r t => ⌜DSPost mode env fe s₀ d P r t⌝⦄) :
    ⦃fun t => ⌜t = s⌝⦄
      (ConRon.Arena.tryUnfoldProjApp (coreKnot mode fe id fuel) d e >>= f)
    ⦃⇓? r t => ⌜DSPost mode env fe s₀ d P r t⌝⦄ := by
  refine triple_seq (tryUnfoldProjApp_spec hsim d s e u hok he hwu) ?_
  rintro o s1 ⟨hok1, hx1, hp1, v, hv, hwv, hE⟩
  cases o with
  | some e₂ =>
    obtain ⟨u₂, rfl, hd₂⟩ := denoteEO_some_inv hv
    exact hsome s1 e₂ u₂ hok1 hx1 hp1 hd₂ (hwv u₂ rfl) hE
  | none =>
    obtain rfl := denoteEO_none_inv hv
    exact hnone s1 hok1 hx1 hp1 hE

end StepExits

/-- con-leche: ConLeche/Kernel/Core.lean:1581-1642 lazyDeltaStep — **THEOREM 1
for one lazy-delta step**: the two unfoldability reads, the one-sided arms
(the projection-application probe on the other side first), and the
two-sided arm (hints, the same-head spine shortcut, both unfoldings); every
unfolded side goes through the CHEAP `whnfCore` and the step ends in
`deltaQuick`. -/
theorem lazyDeltaStep_spec {fe : IFEnv} {fuel : Nat} (henv : ConLeche.EnvWF env)
    (hsim : KnotSpec mode env fe fuel) (d : Nat) (s₀ : AState) (a b : EIdx)
    (x y : Expr) (hok : CheckOK mode env fe s₀)
    (hx : denoteE s₀.store a = some x) (hy : denoteE s₀.store b = some y)
    (hwx : Expr.WScoped d x) (hwy : Expr.WScoped d y) :
    ⦃fun s => ⌜s = s₀⌝⦄
      ConRon.Arena.lazyDeltaStep mode (coreKnot mode fe id fuel) fe d a b
    ⦃⇓? o s' => ⌜DSPost mode env fe s₀ d
      (fun F => ConLeche.lazyDeltaStep mode (ConLeche.pureFns mode env F) env d x y)
      o s'⌝⦄ := by
  unfold ConRon.Arena.lazyDeltaStep
  refine triple_seq (unfoldableHead_spec s₀ a x hok hx) ?_
  rintro ua s2 ⟨hok2, hst2, hp2, rfl⟩
  refine triple_seq (unfoldableHead_spec s2 b y hok2 (by rw [hst2]; exact hy)) ?_
  rintro ub s3 ⟨hok3, hst3, hp3, rfl⟩
  have hst13 : s3.store = s₀.store := hst3.trans hst2
  have hx3 : denoteE s3.store a = some x := by rw [hst13]; exact hx
  have hy3 : denoteE s3.store b = some y := by rw [hst13]; exact hy
  have hx03 : Ext s₀.store s3.store := by rw [hst13]; exact Ext.refl _
  have hp03 : s3.pins = s₀.pins := hp3.trans hp2
  cases hua : ConLeche.unfoldableHead env x <;>
    cases hub : ConLeche.unfoldableHead env y
  · -- neither unfolds
    exact ds_pure_exit (v := .unknown) hok3 hx03 hp03 trivial ⟨0, fun _ _ => by
      dsimp only; unfold ConLeche.lazyDeltaStep; rw [hua, hub]; rfl⟩
  · -- only the right unfolds: the left's projection application first
    refine ds_try_seq hsim a x _ hok3 hx3 hwx ?_ ?_
    · intro s' a₂ u₂ hok' hx' hp' hd₂ hw₂ hT
      exact ds_quick_exit hsim a₂ b u₂ y hok' (hx03.trans hx') (hp'.trans hp03) hd₂
        (denote_ext hy3 hx') hw₂ hwy (hT.imp fun F hT => by
          unfold ConLeche.lazyDeltaStep
          simp only [hua, hub, hT, bind, Except.bind])
    · intro s' hok' hx' hp' hT
      refine ds_unfold_seq henv b y _ hok' (denote_ext hy3 hx') hwy ?_ ?_
      · intro s'' b₂ w₂ hok'' hx'' hp'' hd₂ hw₂ hu
        exact ds_whnf_quick_exit_r hsim a b₂ x w₂ hok'' ((hx03.trans hx').trans hx'')
          (hp''.trans (hp'.trans hp03)) (denote_ext (denote_ext hx3 hx') hx'') hd₂
          hwx hw₂ (hT.imp fun F hT w₃ hw => by
            unfold ConLeche.lazyDeltaStep
            simp only [hua, hub, hT, hu, ConLeche.whnfCore_def, hw, bind,
              Except.bind])
      · intro s'' hok'' hx'' hp'' hu
        exact ds_pure_exit (v := .unknown) hok'' ((hx03.trans hx').trans hx'')
          (hp''.trans (hp'.trans hp03)) trivial (hT.imp fun F hT => by
            unfold ConLeche.lazyDeltaStep
            simp only [hua, hub, hT, hu, bind, Except.bind, pure, Except.pure])
  · -- only the left unfolds: the right's projection application first
    refine ds_try_seq hsim b y _ hok3 hy3 hwy ?_ ?_
    · intro s' b₂ w₂ hok' hx' hp' hd₂ hw₂ hT
      exact ds_quick_exit hsim a b₂ x w₂ hok' (hx03.trans hx') (hp'.trans hp03)
        (denote_ext hx3 hx') hd₂ hwx hw₂ (hT.imp fun F hT => by
          unfold ConLeche.lazyDeltaStep
          simp only [hua, hub, hT, bind, Except.bind])
    · intro s' hok' hx' hp' hT
      refine ds_unfold_seq henv a x _ hok' (denote_ext hx3 hx') hwx ?_ ?_
      · intro s'' a₂ u₂ hok'' hx'' hp'' hd₂ hw₂ hu
        exact ds_whnf_quick_exit_l hsim a₂ b u₂ y hok'' ((hx03.trans hx').trans hx'')
          (hp''.trans (hp'.trans hp03)) hd₂ (denote_ext (denote_ext hy3 hx') hx'')
          hw₂ hwy (hT.imp fun F hT u₃ hw => by
            unfold ConLeche.lazyDeltaStep
            simp only [hua, hub, hT, hu, ConLeche.whnfCore_def, hw, bind,
              Except.bind])
      · intro s'' hok'' hx'' hp'' hu
        exact ds_pure_exit (v := .unknown) hok'' ((hx03.trans hx').trans hx'')
          (hp''.trans (hp'.trans hp03)) trivial (hT.imp fun F hT => by
            unfold ConLeche.lazyDeltaStep
            simp only [hua, hub, hT, hu, bind, Except.bind, pure, Except.pure])
  · -- both unfold: the hints decide
    refine triple_seq (headHint_spec s3 a x hok3 hx3) ?_
    rintro ha s4 ⟨hok4, hst4, hp4, rfl⟩
    refine triple_seq (headHint_spec s4 b y hok4 (by rw [hst4]; exact hy3)) ?_
    rintro hb s5 ⟨hok5, hst5, hp5, rfl⟩
    have hst35 : s5.store = s3.store := hst5.trans hst4
    have hx5 : denoteE s5.store a = some x := by rw [hst35]; exact hx3
    have hy5 : denoteE s5.store b = some y := by rw [hst35]; exact hy3
    have hx05 : Ext s₀.store s5.store := by rw [hst35]; exact hx03
    have hp05 : s5.pins = s₀.pins := hp5.trans (hp4.trans hp03)
    split
    · rename_i hlt
      refine ds_unfold_seq henv a x _ hok5 hx5 hwx ?_ ?_
      · intro s' a₂ u₂ hok' hx' hp' hd₂ hw₂ hu
        exact ds_whnf_quick_exit_l hsim a₂ b u₂ y hok' (hx05.trans hx')
          (hp'.trans hp05) hd₂ (denote_ext hy5 hx') hw₂ hwy
          ⟨0, fun F _ u₃ hw => by
            unfold ConLeche.lazyDeltaStep
            simp only [hua, hub, hlt, if_true, hu, ConLeche.whnfCore_def, hw,
              bind, Except.bind]⟩
      · intro s' hok' hx' hp' hu
        exact ds_pure_exit (v := .unknown) hok' (hx05.trans hx') (hp'.trans hp05) trivial
          ⟨0, fun F _ => by
            dsimp only
            unfold ConLeche.lazyDeltaStep
            simp only [hua, hub, hlt, if_true, hu, pure, Except.pure]⟩
    rename_i hlt1
    simp only [Bool.not_eq_true] at hlt1
    split
    · rename_i hlt2
      refine ds_unfold_seq henv b y _ hok5 hy5 hwy ?_ ?_
      · intro s' b₂ w₂ hok' hx' hp' hd₂ hw₂ hu
        exact ds_whnf_quick_exit_r hsim a b₂ x w₂ hok' (hx05.trans hx')
          (hp'.trans hp05) (denote_ext hx5 hx') hd₂ hwx hw₂
          ⟨0, fun F _ w₃ hw => by
            unfold ConLeche.lazyDeltaStep
            simp only [Bool.false_eq_true, ↓reduceIte, hua, hub, hlt1, hlt2, hu,
              ConLeche.whnfCore_def, hw, bind, Except.bind]⟩
      · intro s' hok' hx' hp' hu
        exact ds_pure_exit (v := .unknown) hok' (hx05.trans hx') (hp'.trans hp05) trivial
          ⟨0, fun F _ => by
            dsimp only
            unfold ConLeche.lazyDeltaStep
            simp only [Bool.false_eq_true, ↓reduceIte, hua, hub, hlt1, hlt2, hu, pure,
              Except.pure]⟩
    rename_i hlt2
    simp only [Bool.not_eq_true] at hlt2
    refine triple_seq (sameConstHeads_spec s5 a b x y hok5 hx5 hy5) ?_
    rintro sch s6 ⟨hok6, hst6, hp6, rfl⟩
    have hx6 : denoteE s6.store a = some x := by rw [hst6]; exact hx5
    have hy6 : denoteE s6.store b = some y := by rw [hst6]; exact hy5
    have hx06 : Ext s₀.store s6.store := by rw [hst6]; exact hx05
    have hp06 : s6.pins = s₀.pins := hp6.trans hp05
    -- the same-head spine shortcut, at both guard outcomes
    have hsp : ∀ (c : Bool), ⦃fun s => ⌜s = s6⌝⦄
        (if c = true then ConRon.Arena.defeqSpine (coreKnot mode fe id fuel) fe d a b
          else pure false)
        ⦃⇓? sp s' => ⌜CheckOK mode env fe s' ∧ Ext s6.store s'.store ∧
          s'.pins = s6.pins ∧
          Ev (fun F => (if c = true then ConLeche.defeqSpine
            (ConLeche.pureFns mode env F) env d x y else pure false)
            = (.ok sp : CheckM Bool))⌝⦄ := by
      intro c
      cases c
      · exact triple_pure_post ⟨hok6, Ext.refl _, rfl, Ev.const rfl⟩
      · refine triple_mono (defeqSpine_spec hsim s6 d a b x y hok6 hx6 hy6 hwx hwy) ?_
        rintro sp s7 ⟨hok7, hx7, hp7, hspF⟩
        exact ⟨hok7, hx7, hp7, Ev.of_mono (p := fun F => ConLeche.defeqSpine
          (ConLeche.pureFns mode env F) env d x y = .ok sp)
          (fun hle h => defeqSpineFueled_mono hle h) hspF⟩
    dsimp only
    refine triple_ite_bind ?_
    refine triple_seq (hsp _) ?_
    rintro sp s7 ⟨hok7, hx7, hp7, hspE⟩
    have hx07 := hx06.trans hx7
    have hp07 : s7.pins = s₀.pins := hp7.trans hp06
    cases sp
    · simp only [Bool.false_eq_true, ↓reduceIte]
      refine ds_unfold_seq henv a x _ hok7 (denote_ext hx6 hx7) hwx ?_ ?_
      · intro s' a₂ u₂ hok' hx' hp' hd₂ hw₂ hu
        refine ds_unfold_seq henv b y _ hok' (denote_ext (denote_ext hy6 hx7) hx')
          hwy ?_ ?_
        · intro s'' b₂ w₂ hok'' hx'' hp'' hd₂' hw₂' hu'
          dsimp only
          refine triple_seq (hsim.whnfCore (c := true) s'' d a₂ u₂ hok''
            (denote_ext hd₂ hx'') hw₂) ?_
          rintro a₃ t1 ⟨hokt1, hxt1, hpt1, u₃, hdu₃, hwu₃, Fa, hFa⟩
          refine triple_seq (hsim.whnfCore (c := true) t1 d b₂ w₂ hokt1
            (denote_ext hd₂' hxt1) hw₂') ?_
          rintro b₃ t2 ⟨hokt2, hxt2, hpt2, w₃, hdw₃, hww₃, Fb, hFb⟩
          have hWa : Ev (fun F => ConLeche.whnfCore mode env F d u₂ true = .ok u₃) :=
            Ev.of_mono (fun hle h => ConLeche.whnfCore_mono hle h) ⟨Fa, hFa⟩
          have hWb : Ev (fun F => ConLeche.whnfCore mode env F d w₂ true = .ok w₃) :=
            Ev.of_mono (fun hle h => ConLeche.whnfCore_mono hle h) ⟨Fb, hFb⟩
          exact ds_quick_exit hsim a₃ b₃ u₃ w₃ hokt2
            ((((hx07.trans hx').trans hx'').trans hxt1).trans hxt2)
            (hpt2.trans (hpt1.trans (hp''.trans (hp'.trans hp07))))
            (denote_ext hdu₃ hxt2) hdw₃ hwu₃ hww₃
            ((hspE.and (hWa.and hWb)).imp fun F ⟨hs, hwa, hwb⟩ => by
              unfold ConLeche.lazyDeltaStep
              simp only [hua, hub, hlt1, hlt2, Bool.false_eq_true, ↓reduceIte]
              rw [hs]
              simp only [bind, Except.bind, Bool.false_eq_true, ↓reduceIte, hu, hu',
                ConLeche.whnfCore_def, hwa, hwb])
        · intro s'' hok'' hx'' hp'' hu'
          exact ds_pure_exit (v := .unknown) hok'' ((hx07.trans hx').trans hx'')
            (hp''.trans (hp'.trans hp07)) trivial (hspE.imp fun F hs => by
              unfold ConLeche.lazyDeltaStep
              simp only [hua, hub, hlt1, hlt2, Bool.false_eq_true, ↓reduceIte]
              rw [hs]
              simp only [bind, Except.bind, Bool.false_eq_true, ↓reduceIte, hu, hu',
                pure, Except.pure])
      · intro s' hok' hx' hp' hu
        refine triple_seq (unfoldDefinition_spec henv s' d b hok'
          ⟨y, denote_ext (denote_ext hy6 hx7) hx', hwy⟩) ?_
        rintro o s'' ⟨hok'', hx'', hp'', _⟩
        exact ds_pure_exit (v := .unknown) hok'' ((hx07.trans hx').trans hx'')
          (hp''.trans (hp'.trans hp07)) trivial (hspE.imp fun F hs => by
            unfold ConLeche.lazyDeltaStep
            simp only [hua, hub, hlt1, hlt2, Bool.false_eq_true, ↓reduceIte]
            rw [hs]
            simp only [bind, Except.bind, Bool.false_eq_true, ↓reduceIte, hu,
              pure, Except.pure])
    · simp only [↓reduceIte]
      exact ds_pure_exit (v := .eq) hok7 hx07 hp07 trivial (hspE.imp fun F hs => by
        unfold ConLeche.lazyDeltaStep
        simp only [hua, hub, hlt1, hlt2, Bool.false_eq_true, ↓reduceIte]
        rw [hs]
        simp only [bind, Except.bind, ↓reduceIte, pure, Except.pure])

/-! ## 5. The lazy-delta loop -/

/-- con-leche: ConLeche/Kernel/Core.lean:1644-1649 LazyRes — **the answer
relation of the loop**: the same verdict, or the pair it got stuck on,
denoted and well scoped. -/
def LRRel (st : EStore) (d : Nat) : LazyResA → LazyRes → Prop
  | .verdict v, .verdict w => v = w
  | .unknown a b, .unknown x y => denoteE st a = some x ∧ denoteE st b = some y ∧
      Expr.WScoped d x ∧ Expr.WScoped d y
  | _, _ => False

unseal ConLeche.defeqLoopFuel in
/-- con-leche: ConLeche/Kernel/Core.lean:1651-1654 defeqLoopFuel — the two
budgets are the same number (task #97c); con-leche's is `@[irreducible]`. -/
theorem defeqLoopFuel_eq :
    ConRon.Arena.defeqLoopFuel = ConLeche.defeqLoopFuel := rfl

/-- con-leche: ConLeche/Kernel/Core.lean:1656-1689 lazyDeltaReduction —
**THEOREM 1 for the lazy-delta loop**, at every budget, by induction on it:
the offset check, the fvar-guarded literal acceleration on either side
(whose reduct goes to the knot), then one `lazyDeltaStep`, whose `cont` is
the next iteration. -/
theorem lazyDeltaReduction_spec {fe : IFEnv} {fuel : Nat}
    (henv : ConLeche.EnvWF env) (hsim : KnotSpec mode env fe fuel) (d : Nat) :
    ∀ (n : Nat) (s₀ : AState) (a b : EIdx) (x y : Expr),
      CheckOK mode env fe s₀ →
      denoteE s₀.store a = some x → denoteE s₀.store b = some y →
      Expr.WScoped d x → Expr.WScoped d y →
      ⦃fun s => ⌜s = s₀⌝⦄
        ConRon.Arena.lazyDeltaReduction mode (coreKnot mode fe id fuel) fe d n a b
      ⦃⇓? o s' => ⌜CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
          s'.pins = s₀.pins ∧
          ∃ v, LRRel s'.store d o v ∧
            Ev (fun F => ConLeche.lazyDeltaReduction mode
              (ConLeche.pureFns mode env F) env d n x y = .ok v)⌝⦄
  | 0, s₀, a, b, x, y, _, _, _, _, _ => by
    rw [ConRon.Arena.lazyDeltaReduction]
    exact triple_fail
  | n + 1, s₀, a, b, x, y, hok, hx, hy, hwx, hwy => by
    rw [ConRon.Arena.lazyDeltaReduction]
    refine triple_seq (defeqOffset_spec hsim d s₀ a b x y hok hx hy hwx hwy) ?_
    rintro o s1 ⟨hok1, hx1, hp1, hO⟩
    cases o with
    | some v =>
      exact triple_pure_post ⟨hok1, hx1, hp1, .verdict v, rfl, hO.imp fun F h => by
        rw [ConLeche.lazyDeltaReduction]
        simp only [h, bind, Except.bind, pure, Except.pure]⟩
    | none =>
    dsimp only
    refine triple_seq (defeqNoFvars_spec s1 a b x y hok1 (denote_ext hx hx1)
      (denote_ext hy hx1)) ?_
    rintro nf s2 ⟨hok2, hst2, hp2, rfl⟩
    have hx12 : Ext s1.store s2.store := by rw [hst2]; exact Ext.refl _
    have hx02 := hx1.trans hx12
    have hp02 : s2.pins = s₀.pins := hp2.trans hp1
    have hdx2 := denote_ext hx hx02
    have hdy2 := denote_ext hy hx02
    -- literal acceleration on the left
    refine triple_seq (reduceNatIf_spec hsim s2 d a x _ hok2 hdx2 hwx) ?_
    rintro o1 s3 ⟨hok3, hx3, hp3, v1, hv1, hwv1, hN1⟩
    have hx03 := hx02.trans hx3
    have hp03 : s3.pins = s₀.pins := hp3.trans hp02
    cases o1 with
    | some a₂ =>
      obtain ⟨z, rfl, hz⟩ := denoteEO_some_inv hv1
      dsimp only
      refine triple_seq (hsim.defeq s3 d a₂ b z y hok3 hz (denote_ext hdy2 hx3)
        (hwv1 z rfl) hwy) ?_
      rintro v s4 ⟨hok4, hx4, hp4, F4, hF4⟩
      have hD : Ev (fun F => ConLeche.isDefEqCore mode env F d z y = .ok v) :=
        Ev.of_mono (fun hle h => ConLeche.isDefEqCore_mono hle h) ⟨F4, hF4⟩
      exact triple_pure_post ⟨hok4, hx03.trans hx4, hp4.trans hp03, .verdict v, rfl,
        ((hO.and hN1).and hD).imp fun F ⟨⟨h1, h2⟩, h3⟩ => by
          rw [ConLeche.lazyDeltaReduction]
          simp only [h1, bind, Except.bind]
          rw [h2]
          simp only [ConLeche.defeq_def, h3, pure, Except.pure]⟩
    | none =>
    obtain rfl := denoteEO_none_inv hv1
    dsimp only
    -- literal acceleration on the right
    refine triple_seq (reduceNatIf_spec hsim s3 d b y _ hok3 (denote_ext hdy2 hx3)
      hwy) ?_
    rintro o2 s4 ⟨hok4, hx4, hp4, v2, hv2, hwv2, hN2⟩
    have hx04 := hx03.trans hx4
    have hp04 : s4.pins = s₀.pins := hp4.trans hp03
    have hdx4 := denote_ext hx hx04
    have hdy4 := denote_ext hy hx04
    cases o2 with
    | some b₂ =>
      obtain ⟨z, rfl, hz⟩ := denoteEO_some_inv hv2
      dsimp only
      refine triple_seq (hsim.defeq s4 d a b₂ x z hok4 hdx4 hz hwx
        (hwv2 z rfl)) ?_
      rintro v s5 ⟨hok5, hx5, hp5, F5, hF5⟩
      have hD : Ev (fun F => ConLeche.isDefEqCore mode env F d x z = .ok v) :=
        Ev.of_mono (fun hle h => ConLeche.isDefEqCore_mono hle h) ⟨F5, hF5⟩
      exact triple_pure_post ⟨hok5, hx04.trans hx5, hp5.trans hp04, .verdict v, rfl,
        (((hO.and hN1).and hN2).and hD).imp fun F ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ => by
          rw [ConLeche.lazyDeltaReduction]
          simp only [h1, bind, Except.bind]
          rw [h2]
          simp only
          rw [h3]
          simp only [ConLeche.defeq_def, h4, pure, Except.pure]⟩
    | none =>
    obtain rfl := denoteEO_none_inv hv2
    dsimp only
    -- one lazy-delta step
    refine triple_seq (lazyDeltaStep_spec henv hsim d s4 a b x y hok4 hdx4 hdy4
      hwx hwy) ?_
    rintro st s5 ⟨hok5, hx5, hp5, w, hr, hS⟩
    have hx05 := hx04.trans hx5
    have hp05 : s5.pins = s₀.pins := hp5.trans hp04
    have hpre : ∀ F, ConLeche.defeqOffset (ConLeche.pureFns mode env F) d x y
          = .ok none →
        (if (!x.hasFvar && !y.hasFvar) = true then
          ConLeche.reduceNat (ConLeche.pureFns mode env F) env d x
          else pure none) = (.ok none : CheckM (Option Expr)) →
        (if (!x.hasFvar && !y.hasFvar) = true then
          ConLeche.reduceNat (ConLeche.pureFns mode env F) env d y
          else pure none) = (.ok none : CheckM (Option Expr)) →
        ConLeche.lazyDeltaReduction mode (ConLeche.pureFns mode env F) env d (n + 1)
          x y =
        (ConLeche.lazyDeltaStep mode (ConLeche.pureFns mode env F) env d x y >>=
          fun r => match r with
            | .cont a' b' => ConLeche.lazyDeltaReduction mode
                (ConLeche.pureFns mode env F) env d n a' b'
            | .eq => pure (.verdict true)
            | .diff => pure (.verdict false)
            | .unknown => pure (.unknown x y)) := by
      intro F h1 h2 h3
      rw [ConLeche.lazyDeltaReduction]
      simp only [h1, bind, Except.bind]
      rw [h2]
      simp only
      rw [h3]
      rfl
    have hP := ((hO.and hN1).and hN2).imp fun F ⟨⟨h1, h2⟩, h3⟩ => hpre F h1 h2 h3
    rcases st with ⟨a', b'⟩ | _ | _ | _ <;> rcases w with ⟨x', y'⟩ | _ | _ | _ <;>
      simp only [DSRel] at hr
    · -- `cont`: the next iteration
      obtain ⟨ha', hb', hwx', hwy'⟩ := hr
      refine triple_mono (lazyDeltaReduction_spec henv hsim d n s5 a' b' x' y' hok5
        ha' hb' hwx' hwy') ?_
      rintro o s6 ⟨hok6, hx6, hp6, v, hrv, hL⟩
      exact ⟨hok6, hx05.trans hx6, hp6.trans hp05, v, hrv,
        ((hP.and hS).and hL).imp fun F ⟨⟨h1, h2⟩, h3⟩ => by
          rw [h1, show ConLeche.lazyDeltaStep mode (ConLeche.pureFns mode env F) env d x y
            = _ from h2]; exact h3⟩
    · -- `eq`
      exact triple_pure_post ⟨hok5, hx05, hp05, .verdict true, rfl,
        (hP.and hS).imp fun F ⟨h1, h2⟩ => by
          rw [h1, show ConLeche.lazyDeltaStep mode (ConLeche.pureFns mode env F) env d
            x y = _ from h2]
          rfl⟩
    · -- `diff`
      exact triple_pure_post ⟨hok5, hx05, hp05, .verdict false, rfl,
        (hP.and hS).imp fun F ⟨h1, h2⟩ => by
          rw [h1, show ConLeche.lazyDeltaStep mode (ConLeche.pureFns mode env F) env d
            x y = _ from h2]
          rfl⟩
    · -- `unknown`: the pair the loop got stuck on
      exact triple_pure_post ⟨hok5, hx05, hp05, .unknown x y,
        ⟨denote_ext hx hx05, denote_ext hy hx05, hwx, hwy⟩,
        (hP.and hS).imp fun F ⟨h1, h2⟩ => by
          rw [h1, show ConLeche.lazyDeltaStep mode (ConLeche.pureFns mode env F) env d
            x y = _ from h2]
          rfl⟩

end ConRon.Bridge.Core
