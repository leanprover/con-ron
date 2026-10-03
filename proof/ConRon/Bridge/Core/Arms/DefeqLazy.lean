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

end ConRon.Bridge.Core
