/-
# `ConRon.Bridge.Core.Arms.DefeqStuck` — Theorem 1 for `defeqStuck`

Task #109.  con-leche's `defeqStuck` (the tail of the official kernel's
`is_def_eq_core`, after lazy delta, the proj/proj check and the full
`whnfCore` restart) is the old `defeqStep`'s congruence half minus the arms
that moved: the sorts, literals and binders went to `quickDefEq`
(`Arms/DefeqLazy.lean`), the `Nat` literal/constructor pairs to
`defeqOffset`, the proj/proj pair to `defeqProjPair`.  What is left is
proved here, arm by arm, as before:

| arm | lemma |
|---|---|
| a string literal against `String.ofList` (either side) | `dqArm_strL`, `dqArm_strR` |
| two free variables | `dqArm_fvar` |
| two constants | `dqArm_const` |
| two stuck applications (spine-wise) | `dqArm_app` |
| η on a one-sided λ | `dqArm_etaL`, `dqArm_etaR` |
| everything else | `dqArm_stuck` (`stuckIrrel`) |
| the dispatch | `defeqStuck_spec` |

Each arm is stated against an arbitrary pure goal `G` that follows
eventually from con-leche's `defeqStuck` at the arm's pair (`DqPost`,
`Arms/DefeqBase.lean`).
-/
import ConRon.Bridge.Core.Arms.DefeqBase

namespace ConRon.Bridge.Core

set_option autoImplicit false
set_option mvcgen.warning false
set_option maxHeartbeats 1000000

open ConLeche ConRon.Arena ConRon.Bridge Std.Do

variable {mode : CheckMode} {env : Env}

section Arms

variable {fe : IFEnv} {fuel d : Nat} {s₀ s₁ : AState} {G : Nat → Bool → Prop}

/-- con-leche: ConLeche/Kernel/Core.lean:532-542 stuckIrrel — **the stuck
fallback arm**, at any pair the dispatch sends there. -/
theorem dqArm_stuck (hμ : mode.verifiedChecks = true)
    (henv : ConLeche.EnvWF env) (hsim : KnotSpec mode env fe fuel) (a' b' : EIdx)
    (x' y' : Expr) (hok : CheckOK mode env fe s₁)
    (hx₁ : Ext s₀.store s₁.store) (hp₁ : s₁.pins = s₀.pins)
    (hx : denoteE s₁.store a' = some x') (hy : denoteE s₁.store b' = some y')
    (hwx : Expr.WScoped d x') (hwy : Expr.WScoped d y')
    (hred : ∀ F, ConLeche.defeqStuck mode (ConLeche.pureFns mode env F) env d x' y' =
      ConLeche.stuckIrrel mode (ConLeche.pureFns mode env F) env d x' y')
    (hG : Ev (fun F => ∀ r, ConLeche.defeqStuck mode (ConLeche.pureFns mode env F) env d
      x' y' = .ok r → G F r)) :
    ⦃fun s => ⌜s = s₁⌝⦄
      ConRon.Arena.stuckIrrel mode (coreKnot mode fe id fuel) fe d a' b'
    ⦃⇓? r s' => ⌜DqPost mode env fe s₀ G r s'⌝⦄ :=
  dq_stuck_exit hμ henv hsim a' b' x' y' hok hx₁ hp₁ hx hy hwx hwy
    (hG.imp fun F h r hr => h r (by rw [hred F]; exact hr))

/-- con-leche: ConLeche/Kernel/Core.lean:1685-1688 defeqStep — **η, the λ on
the left**. -/
theorem dqArm_etaL (hμ : mode.verifiedChecks = true)
    (henv : ConLeche.EnvWF env) (hsim : KnotSpec mode env fe fuel) (a' b' ty₁ bd₁ : EIdx)
    (m₁ : ConLeche.BinderMeta) (t₁ c₁ y' : Expr)
    (hok : CheckOK mode env fe s₁)
    (hx₁ : Ext s₀.store s₁.store) (hp₁ : s₁.pins = s₀.pins)
    (hx : denoteE s₁.store a' = some (.lam t₁ c₁ m₁))
    (hty : denoteE s₁.store ty₁ = some t₁)
    (hbd : denoteE s₁.store bd₁ = some c₁)
    (hy : denoteE s₁.store b' = some y')
    (hwx : Expr.WScoped d (.lam t₁ c₁ m₁)) (hwy : Expr.WScoped d y')
    (hred : ∀ F, ConLeche.defeqStuck mode (ConLeche.pureFns mode env F) env d
        (.lam t₁ c₁ m₁) y' =
      (ConLeche.etaCert mode (ConLeche.pureFns mode env F) env d t₁ c₁ m₁ y'
        >>= fun b => if b then pure true else
          ConLeche.stuckIrrel mode (ConLeche.pureFns mode env F) env d
            (.lam t₁ c₁ m₁) y'))
    (hG : Ev (fun F => ∀ r, ConLeche.defeqStuck mode (ConLeche.pureFns mode env F) env d
      (.lam t₁ c₁ m₁) y' = .ok r → G F r)) :
    ⦃fun s => ⌜s = s₁⌝⦄
      (do
        let e ← ConRon.Arena.etaCert mode (coreKnot mode fe id fuel) fe d ty₁
          bd₁ m₁ b'
        if e = true then pure true
        else ConRon.Arena.stuckIrrel mode (coreKnot mode fe id fuel) fe d a' b')
    ⦃⇓? r s' => ⌜DqPost mode env fe s₀ G r s'⌝⦄ := by
  refine triple_seq (etaCert_spec hsim s₁ d ty₁ bd₁ b' m₁ t₁ c₁ y' hok hty hbd
    hy hwx hwy) ?_
  rintro e s2 ⟨hok2, hx2, hp2, he⟩
  have hE : Ev (fun F => ConLeche.etaCert mode (ConLeche.pureFns mode env F)
      env d t₁ c₁ m₁ y' = .ok e) :=
    Ev.of_mono (fun hle h => etaCertFueled_mono hle h) he
  cases e
  · simp only [Bool.false_eq_true, ↓reduceIte]
    exact dq_stuck_exit hμ henv hsim a' b' _ y' hok2 (hx₁.trans hx2) (hp2.trans hp₁)
      (denote_ext hx hx2) (denote_ext hy hx2) hwx hwy
      ((hG.and hE).imp fun F ⟨h, h2⟩ r hr => h r (by
        rw [hred F]; simp only [bind, Except.bind, h2, Bool.false_eq_true,
          ↓reduceIte]; exact hr))
  · simp only [↓reduceIte]
    exact dq_pure_exit hok2 (hx₁.trans hx2) (hp2.trans hp₁)
      ((hG.and hE).imp fun F ⟨h, h2⟩ => h true (by
        rw [hred F]; simp only [bind, Except.bind, h2, ↓reduceIte]; rfl))

/-- con-leche: ConLeche/Kernel/Core.lean:1689-1692 defeqStep — **η, the λ on
the right**. -/
theorem dqArm_etaR (hμ : mode.verifiedChecks = true)
    (henv : ConLeche.EnvWF env) (hsim : KnotSpec mode env fe fuel) (a' b' ty₂ bd₂ : EIdx)
    (m₂ : ConLeche.BinderMeta) (x' t₂ c₂ : Expr)
    (hok : CheckOK mode env fe s₁)
    (hx₁ : Ext s₀.store s₁.store) (hp₁ : s₁.pins = s₀.pins)
    (hx : denoteE s₁.store a' = some x')
    (hy : denoteE s₁.store b' = some (.lam t₂ c₂ m₂))
    (hty : denoteE s₁.store ty₂ = some t₂)
    (hbd : denoteE s₁.store bd₂ = some c₂)
    (hwx : Expr.WScoped d x') (hwy : Expr.WScoped d (.lam t₂ c₂ m₂))
    (hred : ∀ F, ConLeche.defeqStuck mode (ConLeche.pureFns mode env F) env d
        x' (.lam t₂ c₂ m₂) =
      (ConLeche.etaCert mode (ConLeche.pureFns mode env F) env d t₂ c₂ m₂ x'
        >>= fun b => if b then pure true else
          ConLeche.stuckIrrel mode (ConLeche.pureFns mode env F) env d
            x' (.lam t₂ c₂ m₂)))
    (hG : Ev (fun F => ∀ r, ConLeche.defeqStuck mode (ConLeche.pureFns mode env F) env d
      x' (.lam t₂ c₂ m₂) = .ok r → G F r)) :
    ⦃fun s => ⌜s = s₁⌝⦄
      (do
        let e ← ConRon.Arena.etaCert mode (coreKnot mode fe id fuel) fe d ty₂
          bd₂ m₂ a'
        if e = true then pure true
        else ConRon.Arena.stuckIrrel mode (coreKnot mode fe id fuel) fe d a' b')
    ⦃⇓? r s' => ⌜DqPost mode env fe s₀ G r s'⌝⦄ := by
  refine triple_seq (etaCert_spec hsim s₁ d ty₂ bd₂ a' m₂ t₂ c₂ x' hok hty hbd
    hx hwy hwx) ?_
  rintro e s2 ⟨hok2, hx2, hp2, he⟩
  have hE : Ev (fun F => ConLeche.etaCert mode (ConLeche.pureFns mode env F)
      env d t₂ c₂ m₂ x' = .ok e) :=
    Ev.of_mono (fun hle h => etaCertFueled_mono hle h) he
  cases e
  · simp only [Bool.false_eq_true, ↓reduceIte]
    exact dq_stuck_exit hμ henv hsim a' b' x' _ hok2 (hx₁.trans hx2) (hp2.trans hp₁)
      (denote_ext hx hx2) (denote_ext hy hx2) hwx hwy
      ((hG.and hE).imp fun F ⟨h, h2⟩ r hr => h r (by
        rw [hred F]; simp only [bind, Except.bind, h2, Bool.false_eq_true,
          ↓reduceIte]; exact hr))
  · simp only [↓reduceIte]
    exact dq_pure_exit hok2 (hx₁.trans hx2) (hp2.trans hp₁)
      ((hG.and hE).imp fun F ⟨h, h2⟩ => h true (by
        rw [hred F]; simp only [bind, Except.bind, h2, ↓reduceIte]; rfl))


/-- con-leche: ConLeche/Kernel/Core.lean:1605-1608 defeqStep — **two free
variables**: equal indices are defeq, else stuck. -/
theorem dqArm_fvar (hμ : mode.verifiedChecks = true)
    (henv : ConLeche.EnvWF env) (hsim : KnotSpec mode env fe fuel) (a' b' : EIdx)
    (i j : Nat) (t₁ t₂ : Expr)
    (hok : CheckOK mode env fe s₁)
    (hx₁ : Ext s₀.store s₁.store) (hp₁ : s₁.pins = s₀.pins)
    (hx : denoteE s₁.store a' = some (.fvar i t₁))
    (hy : denoteE s₁.store b' = some (.fvar j t₂))
    (hwx : Expr.WScoped d (.fvar i t₁)) (hwy : Expr.WScoped d (.fvar j t₂))
    (hG : Ev (fun F => ∀ r, ConLeche.defeqStuck mode (ConLeche.pureFns mode env F) env d
      (.fvar i t₁) (.fvar j t₂) = .ok r → G F r)) :
    ⦃fun s => ⌜s = s₁⌝⦄
      (if (i == j) = true then pure true
        else ConRon.Arena.stuckIrrel mode (coreKnot mode fe id fuel) fe d a' b')
    ⦃⇓? r s' => ⌜DqPost mode env fe s₀ G r s'⌝⦄ := by
  split
  · rename_i h
    exact dq_pure_exit hok hx₁ hp₁ (hG.imp fun F hh => hh _ (by
      show (if (i == j) = true then _ else _) = _
      rw [if_pos h]; rfl))
  · rename_i h
    exact dq_stuck_exit hμ henv hsim a' b' _ _ hok hx₁ hp₁ hx hy hwx hwy
      (hG.imp fun F hh r hr => hh r (by
        show (if (i == j) = true then _ else _) = _
        rw [if_neg h]; exact hr))

/-- con-leche: ConLeche/Kernel/Core.lean:1609-1615 defeqStep — **two
constants**: the same name at equivalent universe arguments, else stuck. -/
theorem dqArm_const (hμ : mode.verifiedChecks = true)
    (henv : ConLeche.EnvWF env) (hsim : KnotSpec mode env fe fuel) (a' b' : EIdx)
    (n n' : NIdx) (us us' : LsIdx) (nm nm' : ConLeche.Name)
    (ls ls' : List ConLeche.Level)
    (hok : CheckOK mode env fe s₁)
    (hx₁ : Ext s₀.store s₁.store) (hp₁ : s₁.pins = s₀.pins)
    (hx : denoteE s₁.store a' = some (.const nm ls))
    (hy : denoteE s₁.store b' = some (.const nm' ls'))
    (hn : denoteN s₁.store.ns n = some nm) (hn' : denoteN s₁.store.ns n' = some nm')
    (hus : denoteLs s₁.store.lss us = some ls)
    (hus' : denoteLs s₁.store.lss us' = some ls')
    (hG : Ev (fun F => ∀ r, ConLeche.defeqStuck mode (ConLeche.pureFns mode env F) env d
      (.const nm ls) (.const nm' ls') = .ok r → G F r)) :
    ⦃fun s => ⌜s = s₁⌝⦄
      (if n = n' then do
          let o ← lvlsEq? us us'
          let b ← ConRon.Arena.liftFueled "level comparison" o
          if b = true then pure true
          else ConRon.Arena.stuckIrrel mode (coreKnot mode fe id fuel) fe d a' b'
        else ConRon.Arena.stuckIrrel mode (coreKnot mode fe id fuel) fe d a' b')
    ⦃⇓? r s' => ⌜DqPost mode env fe s₀ G r s'⌝⦄ := by
  have hwf := hok.state.wf
  have hiff := n_eq_iff_pin hwf hn hn'
  have hwx : Expr.WScoped d (.const nm ls) := by simp [Expr.WScoped]
  have hwy : Expr.WScoped d (.const nm' ls') := by simp [Expr.WScoped]
  split
  · rename_i h
    have h' := hiff.mp h
    refine triple_seq (lvlsEq?_spec s₁ us us' hok) ?_
    rintro o s2 ⟨hok2, hst2, hp2, lu, lv, hlu, hlv, rfl⟩
    rw [hus] at hlu; rw [hus'] at hlv
    obtain rfl := Option.some.inj hlu
    obtain rfl := Option.some.inj hlv
    have hx2 : Ext s₀.store s2.store := by rw [hst2]; exact hx₁
    cases ho : ConLeche.Level.isEquivList ls ls' with
    | none => exact triple_fail
    | some b =>
      refine triple_seq (triple_pure_post (Q := fun r s => r = b ∧ s = s2) ⟨rfl, rfl⟩) ?_
      rintro bb s3 ⟨hbb, hs3⟩
      subst bb; subst s3
      have hpure : ∀ F, ConLeche.defeqStuck mode (ConLeche.pureFns mode env F) env d
          (.const nm ls) (.const nm' ls') =
          (if b = true then pure true else ConLeche.stuckIrrel mode
            (ConLeche.pureFns mode env F) env d (.const nm ls) (.const nm' ls')) := by
        intro F
        exact (if_pos h').trans (by rw [ho]; rfl)
      split
      · rename_i hb
        exact dq_pure_exit hok2 hx2 (hp2.trans hp₁) (hG.imp fun F hh => hh _ (by
          rw [hpure F, if_pos hb]; rfl))
      · rename_i hb
        exact dq_stuck_exit hμ henv hsim a' b' _ _ hok2 hx2 (hp2.trans hp₁)
          (by rw [hst2]; exact hx) (by rw [hst2]; exact hy) hwx hwy
          (hG.imp fun F hh r hr => hh r (by rw [hpure F, if_neg hb]; exact hr))
  · rename_i h
    exact dq_stuck_exit hμ henv hsim a' b' _ _ hok hx₁ hp₁ hx hy hwx hwy
      (hG.imp fun F hh r hr => hh r
        ((if_neg (fun h' => h (hiff.mpr h'))).trans hr))


/-- con-leche: ConLeche/Kernel/Core.lean:1595-1599 defeqStep — **a `String`
literal against a unary `String.ofList` application, literal on the left**:
the literal's constructor form against the application. -/
theorem dqArm_strL (hμ : mode.verifiedChecks = true)
    (henv : ConLeche.EnvWF env) (hsim : KnotSpec mode env fe fuel) (a' b' fo : EIdx)
    (st : String) (ef ex : Expr)
    (hok : CheckOK mode env fe s₁)
    (hx₁ : Ext s₀.store s₁.store) (hp₁ : s₁.pins = s₀.pins)
    (hx : denoteE s₁.store a' = some (.lit (.strVal st)))
    (hy : denoteE s₁.store b' = some (.app ef ex))
    (hf : denoteE s₁.store fo = some ef)
    (hwy : Expr.WScoped d (.app ef ex))
    (hG : Ev (fun F => ∀ r, ConLeche.defeqStuck mode (ConLeche.pureFns mode env F) env d
      (.lit (.strVal st)) (.app ef ex) = .ok r → G F r)) :
    ⦃fun s => ⌜s = s₁⌝⦄
      (do
        if fo.tag == ETag.const then
          match ← view fo with
          | .const cO usO => do
            let el ← emptyLevels
            let sl ← pinStringOfList
            let sup ← ConRon.Arena.strLitSupported fe
            if cO = sl ∧ usO = el ∧ sup = true then do
              let c ← ConRon.Arena.strLitToConstructor st
              (coreKnot mode fe id fuel).defeq d c b'
            else ConRon.Arena.stuckIrrel mode (coreKnot mode fe id fuel) fe d a' b'
          | _ => ConRon.Arena.stuckIrrel mode (coreKnot mode fe id fuel) fe d a' b'
        else ConRon.Arena.stuckIrrel mode (coreKnot mode fe id fuel) fe d a' b')
    ⦃⇓? r s' => ⌜DqPost mode env fe s₀ G r s'⌝⦄ := by
  have hwf := hok.state.wf
  have hwx : Expr.WScoped d (.lit (.strVal st)) := by simp [Expr.WScoped]
  obtain ⟨vf, hvf⟩ := denoteE_view hf
  refine tag_view_bind_triple hvf ?_
    (fun hne => by cases vf <;> first | rfl | exact absurd rfl hne)
  rcases VD.of_view hwf hvf hf with _ | _ | _ | ⟨c, us, nm, ls, hc, hus⟩ | _ |
    _ | _ | _ | _ | _
  case const =>
    refine triple_seq (pinEmptyLevels_spec s₁ hok.pins) ?_
    rintro el s2 ⟨hs2, hel⟩
    subst s2
    refine triple_seq (pinAt_spec s₁ PIN_STRING_OF_LIST hok.pins) ?_
    rintro sl s3 ⟨hs3, hsl⟩
    subst s3
    have hiff : (c = sl ∧ us = el) ↔ (nm = ConLeche.stringOfListName ∧ ls = []) := by
      rw [n_eq_iff_pin hwf hc (hsl _ rfl), ls_eq_iff_nil hwf hus hel]
    refine triple_seq (strLitSupported_spec s₁ hok) ?_
    rintro sup s4 ⟨hok4, hx4, hp4, rfl⟩
    have hx04 := hx₁.trans hx4
    have hp04 : s4.pins = s₀.pins := hp4.trans hp₁
    split
    · rename_i h
      obtain ⟨rfl, rfl⟩ := hiff.mp ⟨h.1, h.2.1⟩
      have hsup := h.2.2
      refine triple_seq (strLitToConstructor_spec s4 st hok4) ?_
      rintro cc s5 ⟨hok5, hx5, hp5, hd5⟩
      exact dq_defeq_exit hsim cc b' _ _ hok5 (hx04.trans hx5) (hp5.trans hp04)
        hd5 (denote_ext hy (hx4.trans hx5)) (strLitToConstructor_WScoped st d)
        hwy (hG.imp fun _ hh r hr => hh r ((if_pos (show ConLeche.stringOfListName = ConLeche.stringOfListName ∧
          ([] : List ConLeche.Level) = [] ∧ ConLeche.strLitSupported env = true
          from ⟨rfl, rfl, hsup⟩)).trans hr))
    · rename_i h
      exact dq_stuck_exit hμ henv hsim a' b' _ _ hok4 hx04 hp04 (denote_ext hx hx4)
        (denote_ext hy hx4) hwx hwy (hG.imp fun _ hh r hr => hh r
          ((if_neg (fun h' => h ⟨(hiff.mpr ⟨h'.1, h'.2.1⟩).1,
            (hiff.mpr ⟨h'.1, h'.2.1⟩).2, h'.2.2⟩)).trans hr))
  all_goals
    exact dq_stuck_exit hμ henv hsim a' b' _ _ hok hx₁ hp₁ hx hy hwx hwy
      (hG.imp fun _ h r hr => h r hr)

/-- con-leche: ConLeche/Kernel/Core.lean:1600-1604 defeqStep — the same,
literal on the right. -/
theorem dqArm_strR (hμ : mode.verifiedChecks = true)
    (henv : ConLeche.EnvWF env) (hsim : KnotSpec mode env fe fuel) (a' b' fo : EIdx)
    (st : String) (ef ex : Expr)
    (hok : CheckOK mode env fe s₁)
    (hx₁ : Ext s₀.store s₁.store) (hp₁ : s₁.pins = s₀.pins)
    (hx : denoteE s₁.store a' = some (.app ef ex))
    (hy : denoteE s₁.store b' = some (.lit (.strVal st)))
    (hf : denoteE s₁.store fo = some ef)
    (hwx : Expr.WScoped d (.app ef ex))
    (hG : Ev (fun F => ∀ r, ConLeche.defeqStuck mode (ConLeche.pureFns mode env F) env d
      (.app ef ex) (.lit (.strVal st)) = .ok r → G F r)) :
    ⦃fun s => ⌜s = s₁⌝⦄
      (do
        if fo.tag == ETag.const then
          match ← view fo with
          | .const cO usO => do
            let el ← emptyLevels
            let sl ← pinStringOfList
            let sup ← ConRon.Arena.strLitSupported fe
            if cO = sl ∧ usO = el ∧ sup = true then do
              let c ← ConRon.Arena.strLitToConstructor st
              (coreKnot mode fe id fuel).defeq d a' c
            else ConRon.Arena.stuckIrrel mode (coreKnot mode fe id fuel) fe d a' b'
          | _ => ConRon.Arena.stuckIrrel mode (coreKnot mode fe id fuel) fe d a' b'
        else ConRon.Arena.stuckIrrel mode (coreKnot mode fe id fuel) fe d a' b')
    ⦃⇓? r s' => ⌜DqPost mode env fe s₀ G r s'⌝⦄ := by
  have hwf := hok.state.wf
  have hwy : Expr.WScoped d (.lit (.strVal st)) := by simp [Expr.WScoped]
  obtain ⟨vf, hvf⟩ := denoteE_view hf
  refine tag_view_bind_triple hvf ?_
    (fun hne => by cases vf <;> first | rfl | exact absurd rfl hne)
  rcases VD.of_view hwf hvf hf with _ | _ | _ | ⟨c, us, nm, ls, hc, hus⟩ | _ |
    _ | _ | _ | _ | _
  case const =>
    refine triple_seq (pinEmptyLevels_spec s₁ hok.pins) ?_
    rintro el s2 ⟨hs2, hel⟩
    subst s2
    refine triple_seq (pinAt_spec s₁ PIN_STRING_OF_LIST hok.pins) ?_
    rintro sl s3 ⟨hs3, hsl⟩
    subst s3
    have hiff : (c = sl ∧ us = el) ↔ (nm = ConLeche.stringOfListName ∧ ls = []) := by
      rw [n_eq_iff_pin hwf hc (hsl _ rfl), ls_eq_iff_nil hwf hus hel]
    refine triple_seq (strLitSupported_spec s₁ hok) ?_
    rintro sup s4 ⟨hok4, hx4, hp4, rfl⟩
    have hx04 := hx₁.trans hx4
    have hp04 : s4.pins = s₀.pins := hp4.trans hp₁
    split
    · rename_i h
      obtain ⟨rfl, rfl⟩ := hiff.mp ⟨h.1, h.2.1⟩
      have hsup := h.2.2
      refine triple_seq (strLitToConstructor_spec s4 st hok4) ?_
      rintro cc s5 ⟨hok5, hx5, hp5, hd5⟩
      exact dq_defeq_exit hsim a' cc _ _ hok5 (hx04.trans hx5) (hp5.trans hp04)
        (denote_ext hx (hx4.trans hx5)) hd5 hwx (strLitToConstructor_WScoped st d)
        (hG.imp fun _ hh r hr => hh r ((if_pos (show ConLeche.stringOfListName = ConLeche.stringOfListName ∧
          ([] : List ConLeche.Level) = [] ∧ ConLeche.strLitSupported env = true
          from ⟨rfl, rfl, hsup⟩)).trans hr))
    · rename_i h
      exact dq_stuck_exit hμ henv hsim a' b' _ _ hok4 hx04 hp04 (denote_ext hx hx4)
        (denote_ext hy hx4) hwx hwy (hG.imp fun _ hh r hr => hh r
          ((if_neg (fun h' => h ⟨(hiff.mpr ⟨h'.1, h'.2.1⟩).1,
            (hiff.mpr ⟨h'.1, h'.2.1⟩).2, h'.2.2⟩)).trans hr))
  all_goals
    exact dq_stuck_exit hμ henv hsim a' b' _ _ hok hx₁ hp₁ hx hy hwx hwy
      (hG.imp fun _ h r hr => h r hr)

/-- con-leche: ConLeche/Kernel/Core.lean:1663-1675 defeqStep — **two stuck
applications**: spine-wise congruence (equal lengths, the heads, the
argument lists), else stuck. -/
theorem dqArm_app (hμ : mode.verifiedChecks = true)
    (henv : ConLeche.EnvWF env) (hsim : KnotSpec mode env fe fuel) (a' b' : EIdx)
    (ef₁ ea₁ ef₂ ea₂ : Expr)
    (hok : CheckOK mode env fe s₁)
    (hx₁ : Ext s₀.store s₁.store) (hp₁ : s₁.pins = s₀.pins)
    (hx : denoteE s₁.store a' = some (.app ef₁ ea₁))
    (hy : denoteE s₁.store b' = some (.app ef₂ ea₂))
    (hwx : Expr.WScoped d (.app ef₁ ea₁)) (hwy : Expr.WScoped d (.app ef₂ ea₂))
    (hG : Ev (fun F => ∀ r, ConLeche.defeqStuck mode (ConLeche.pureFns mode env F) env d
      (.app ef₁ ea₁) (.app ef₂ ea₂) = .ok r → G F r)) :
    ⦃fun s => ⌜s = s₁⌝⦄
      (do
        let aa ← getAppArgs coreWalkFuel a'
        let bb ← getAppArgs coreWalkFuel b'
        if aa.length = bb.length then do
          let fa ← getAppFn coreWalkFuel a'
          let fb ← getAppFn coreWalkFuel b'
          let dq ← (coreKnot mode fe id fuel).defeq d fa fb
          if dq = true then do
            let dl ← ConRon.Arena.defEqList (coreKnot mode fe id fuel) fe d aa bb
            if dl = true then pure true
            else ConRon.Arena.stuckIrrel mode (coreKnot mode fe id fuel) fe d a' b'
          else ConRon.Arena.stuckIrrel mode (coreKnot mode fe id fuel) fe d a' b'
        else ConRon.Arena.stuckIrrel mode (coreKnot mode fe id fuel) fe d a' b')
    ⦃⇓? r s' => ⌜DqPost mode env fe s₀ G r s'⌝⦄ := by
  have hpure : ∀ F, ConLeche.defeqStuck mode (ConLeche.pureFns mode env F) env d
      (.app ef₁ ea₁) (.app ef₂ ea₂) =
      (if (Expr.app ef₁ ea₁).getAppArgs.length =
          (Expr.app ef₂ ea₂).getAppArgs.length then
        (ConLeche.isDefEqCore mode env F d (Expr.app ef₁ ea₁).getAppFn
            (Expr.app ef₂ ea₂).getAppFn >>= fun b =>
          if b = true then
            (ConLeche.defEqList (ConLeche.pureFns mode env F) env d
                (Expr.app ef₁ ea₁).getAppArgs (Expr.app ef₂ ea₂).getAppArgs
              >>= fun b2 => if b2 = true then pure true
                else ConLeche.stuckIrrel mode (ConLeche.pureFns mode env F) env d
                  (.app ef₁ ea₁) (.app ef₂ ea₂))
          else ConLeche.stuckIrrel mode (ConLeche.pureFns mode env F) env d
            (.app ef₁ ea₁) (.app ef₂ ea₂))
      else ConLeche.stuckIrrel mode (ConLeche.pureFns mode env F) env d
        (.app ef₁ ea₁) (.app ef₂ ea₂)) := by
    intro F; cases ef₁ <;> rfl
  refine triple_seq (ExprOps.getAppArgs_spec coreWalkFuel s₁ a' hok.state
    (by rw [hx]; rfl)) ?_
  rintro aa s2 ⟨hs2, haa⟩
  subst s2
  refine triple_seq (ExprOps.getAppArgs_spec coreWalkFuel s₁ b' hok.state
    (by rw [hy]; rfl)) ?_
  rintro bb s3 ⟨hs3, hbb⟩
  subst s3
  have haa' := haa _ hx
  have hbb' := hbb _ hy
  have hlen : (aa.length = bb.length) ↔ ((Expr.app ef₁ ea₁).getAppArgs.length =
      (Expr.app ef₂ ea₂).getAppArgs.length) := by
    rw [denoteEList_len haa', denoteEList_len hbb']
  split
  · rename_i hl
    have hl' := hlen.mp hl
    refine triple_seq (ExprOps.getAppFn_spec coreWalkFuel s₁ a' hok.state
      (by rw [hx]; rfl)) ?_
    rintro fa s4 ⟨hs4, hfa⟩
    subst s4
    refine triple_seq (ExprOps.getAppFn_spec coreWalkFuel s₁ b' hok.state
      (by rw [hy]; rfl)) ?_
    rintro fb s5 ⟨hs5, hfb⟩
    subst s5
    refine triple_seq (hsim.defeq s₁ d fa fb _ _ hok (hfa _ hx) (hfb _ hy)
      (Expr.WScoped.getAppFn hwx) (Expr.WScoped.getAppFn hwy)) ?_
    rintro dq s6 ⟨hok6, hx6, hp6, hdq⟩
    have hD : Ev (fun F => ConLeche.isDefEqCore mode env F d
        (Expr.app ef₁ ea₁).getAppFn (Expr.app ef₂ ea₂).getAppFn = .ok dq) :=
      Ev.of_mono (fun hle h => ConLeche.isDefEqCore_mono hle h) hdq
    have hx06 := hx₁.trans hx6
    have hp06 : s6.pins = s₀.pins := hp6.trans hp₁
    cases dq
    · simp only [Bool.false_eq_true, ↓reduceIte]
      exact dq_stuck_exit hμ henv hsim a' b' _ _ hok6 hx06 hp06 (denote_ext hx hx6)
        (denote_ext hy hx6) hwx hwy ((hG.and hD).imp fun F ⟨hh, hd⟩ r hr =>
          hh r (by
            rw [hpure F, if_pos hl']
            simp only [bind, Except.bind, hd, Bool.false_eq_true, ↓reduceIte]
            exact hr))
    · simp only [↓reduceIte]
      refine triple_seq (defEqList_spec hsim s6 d aa bb _ _ hok6
        (denoteEList_ext hx6 _ _ haa') (denoteEList_ext hx6 _ _ hbb')
        (Expr.WScoped.getAppArgs hwx) (Expr.WScoped.getAppArgs hwy)) ?_
      rintro dl s7 ⟨hok7, hx7, hp7, hdl⟩
      have hL : Ev (fun F => ConLeche.defEqList (ConLeche.pureFns mode env F) env d
          (Expr.app ef₁ ea₁).getAppArgs (Expr.app ef₂ ea₂).getAppArgs = .ok dl) :=
        Ev.of_mono (fun hle h => defEqListFueled_mono hle h) hdl
      have hx07 := hx06.trans hx7
      have hp07 : s7.pins = s₀.pins := hp7.trans hp06
      cases dl
      · simp only [Bool.false_eq_true, ↓reduceIte]
        exact dq_stuck_exit hμ henv hsim a' b' _ _ hok7 hx07 hp07 (denote_ext hx (hx6.trans hx7))
          (denote_ext hy (hx6.trans hx7)) hwx hwy
          ((hG.and hD |>.and hL).imp fun F ⟨⟨hh, hd⟩, hl2⟩ r hr => hh r (by
            rw [hpure F, if_pos hl']
            simp only [bind, Except.bind, hd, hl2, Bool.false_eq_true,
              ↓reduceIte]
            exact hr))
      · simp only [↓reduceIte]
        exact dq_pure_exit hok7 hx07 hp07
          ((hG.and hD |>.and hL).imp fun F ⟨⟨hh, hd⟩, hl2⟩ => hh true (by
            rw [hpure F, if_pos hl']
            simp only [bind, Except.bind, hd, hl2, ↓reduceIte]
            rfl))
  · rename_i hl
    exact dq_stuck_exit hμ henv hsim a' b' _ _ hok hx₁ hp₁ hx hy hwx hwy
      (hG.imp fun F hh r hr => hh r (by
        rw [hpure F, if_neg (fun h' => hl (hlen.mpr h'))]; exact hr))

end Arms

/-- con-leche: ConLeche/Kernel/Core.lean:1722-1789 defeqStuck — **THEOREM 1
for the stuck comparison**: the twin's `defeqStuck` against con-leche's, at an
arbitrary pure goal `G` that follows eventually from con-leche's answer. -/
theorem defeqStuck_spec {fe : IFEnv} {fuel : Nat}
    (henv : ConLeche.EnvWF env) (hμ : mode.verifiedChecks = true)
    (hsim : KnotSpec mode env fe fuel) (d : Nat)
    (s₀ s₁ : AState) (a' b' : EIdx) (x' y' : Expr)
    (hok : CheckOK mode env fe s₁) (hx₁ : Ext s₀.store s₁.store)
    (hp₁ : s₁.pins = s₀.pins)
    (hx : denoteE s₁.store a' = some x') (hy : denoteE s₁.store b' = some y')
    (hwx : Expr.WScoped d x') (hwy : Expr.WScoped d y')
    (G : Nat → Bool → Prop)
    (hG : Ev (fun F => ∀ r, ConLeche.defeqStuck mode (ConLeche.pureFns mode env F)
      env d x' y' = .ok r → G F r)) :
    ⦃fun s => ⌜s = s₁⌝⦄ ConRon.Arena.defeqStuck mode (coreKnot mode fe id fuel) fe d a' b'
    ⦃⇓? r s' => ⌜DqPost mode env fe s₀ G r s'⌝⦄ := by
  have hwf := hok.state.wf
  unfold ConRon.Arena.defeqStuck
  obtain ⟨va, hva⟩ := denoteE_view hx
  obtain ⟨vb, hvb⟩ := denoteE_view hy
  refine view_bind_triple hva ?_
  refine view_bind_triple hvb ?_
  have hA := VD.of_view hwf hva hx
  have hB := VD.of_view hwf hvb hy
  rcases hA with ⟨i1⟩ | ⟨k1, t1, et1, ht1⟩ | ⟨u1, l1, hl1⟩ | ⟨n1, us1, nm1, ls1, hn1, hls1⟩ | ⟨f1, a1, ef1, ea1, hf1, ha1⟩ | ⟨ty1, bd1, m1, et1, eb1, hty1, hbd1⟩ | ⟨ty1, bd1, m1, et1, eb1, hty1, hbd1⟩ | ⟨ty1, w1, bd1, et1, ew1, eb1, hty1, hw1, hbd1⟩ | ⟨lit1⟩ | ⟨pn1, pi1, ps1, pnm1, pes1, hpn1, hps1⟩
  · -- left: bvar
    rcases hB with ⟨i2⟩ | ⟨k2, t2, et2, ht2⟩ | ⟨u2, l2, hl2⟩ | ⟨n2, us2, nm2, ls2, hn2, hls2⟩ | ⟨f2, a2, ef2, ea2, hf2, ha2⟩ | ⟨ty2, bd2, m2, et2, eb2, hty2, hbd2⟩ | ⟨ty2, bd2, m2, et2, eb2, hty2, hbd2⟩ | ⟨ty2, w2, bd2, et2, ew2, eb2, hty2, hw2, hbd2⟩ | ⟨lit2⟩ | ⟨pn2, pi2, ps2, pnm2, pes2, hpn2, hps2⟩
    · exact dqArm_stuck hμ henv hsim a' b' _ _ hok hx₁ hp₁ hx hy hwx hwy (fun _ => by rfl) hG
    · exact dqArm_stuck hμ henv hsim a' b' _ _ hok hx₁ hp₁ hx hy hwx hwy (fun _ => by rfl) hG
    · exact dqArm_stuck hμ henv hsim a' b' _ _ hok hx₁ hp₁ hx hy hwx hwy (fun _ => by rfl) hG
    · exact dqArm_stuck hμ henv hsim a' b' _ _ hok hx₁ hp₁ hx hy hwx hwy (fun _ => by rfl) hG
    · exact dqArm_stuck hμ henv hsim a' b' _ _ hok hx₁ hp₁ hx hy hwx hwy (fun _ => by rfl) hG
    · exact dqArm_etaR hμ henv hsim a' b' ty2 bd2 m2 _ et2 eb2 hok hx₁ hp₁ hx hy hty2 hbd2 hwx hwy (fun _ => by rfl) hG
    · exact dqArm_stuck hμ henv hsim a' b' _ _ hok hx₁ hp₁ hx hy hwx hwy (fun _ => by rfl) hG
    · exact dqArm_stuck hμ henv hsim a' b' _ _ hok hx₁ hp₁ hx hy hwx hwy (fun _ => by rfl) hG
    · rcases lit2 with nv2 | sv2
      · exact dqArm_stuck hμ henv hsim a' b' _ _ hok hx₁ hp₁ hx hy hwx hwy (fun _ => by rfl) hG
      · exact dqArm_stuck hμ henv hsim a' b' _ _ hok hx₁ hp₁ hx hy hwx hwy (fun _ => by rfl) hG
    · exact dqArm_stuck hμ henv hsim a' b' _ _ hok hx₁ hp₁ hx hy hwx hwy (fun _ => by rfl) hG
  · -- left: fvar
    rcases hB with ⟨i2⟩ | ⟨k2, t2, et2, ht2⟩ | ⟨u2, l2, hl2⟩ | ⟨n2, us2, nm2, ls2, hn2, hls2⟩ | ⟨f2, a2, ef2, ea2, hf2, ha2⟩ | ⟨ty2, bd2, m2, et2, eb2, hty2, hbd2⟩ | ⟨ty2, bd2, m2, et2, eb2, hty2, hbd2⟩ | ⟨ty2, w2, bd2, et2, ew2, eb2, hty2, hw2, hbd2⟩ | ⟨lit2⟩ | ⟨pn2, pi2, ps2, pnm2, pes2, hpn2, hps2⟩
    · exact dqArm_stuck hμ henv hsim a' b' _ _ hok hx₁ hp₁ hx hy hwx hwy (fun _ => by rfl) hG
    · exact dqArm_fvar hμ henv hsim a' b' k1 k2 et1 et2 hok hx₁ hp₁ hx hy hwx hwy hG
    · exact dqArm_stuck hμ henv hsim a' b' _ _ hok hx₁ hp₁ hx hy hwx hwy (fun _ => by rfl) hG
    · exact dqArm_stuck hμ henv hsim a' b' _ _ hok hx₁ hp₁ hx hy hwx hwy (fun _ => by rfl) hG
    · exact dqArm_stuck hμ henv hsim a' b' _ _ hok hx₁ hp₁ hx hy hwx hwy (fun _ => by rfl) hG
    · exact dqArm_etaR hμ henv hsim a' b' ty2 bd2 m2 _ et2 eb2 hok hx₁ hp₁ hx hy hty2 hbd2 hwx hwy (fun _ => by rfl) hG
    · exact dqArm_stuck hμ henv hsim a' b' _ _ hok hx₁ hp₁ hx hy hwx hwy (fun _ => by rfl) hG
    · exact dqArm_stuck hμ henv hsim a' b' _ _ hok hx₁ hp₁ hx hy hwx hwy (fun _ => by rfl) hG
    · rcases lit2 with nv2 | sv2
      · exact dqArm_stuck hμ henv hsim a' b' _ _ hok hx₁ hp₁ hx hy hwx hwy (fun _ => by rfl) hG
      · exact dqArm_stuck hμ henv hsim a' b' _ _ hok hx₁ hp₁ hx hy hwx hwy (fun _ => by rfl) hG
    · exact dqArm_stuck hμ henv hsim a' b' _ _ hok hx₁ hp₁ hx hy hwx hwy (fun _ => by rfl) hG
  · -- left: sort
    rcases hB with ⟨i2⟩ | ⟨k2, t2, et2, ht2⟩ | ⟨u2, l2, hl2⟩ | ⟨n2, us2, nm2, ls2, hn2, hls2⟩ | ⟨f2, a2, ef2, ea2, hf2, ha2⟩ | ⟨ty2, bd2, m2, et2, eb2, hty2, hbd2⟩ | ⟨ty2, bd2, m2, et2, eb2, hty2, hbd2⟩ | ⟨ty2, w2, bd2, et2, ew2, eb2, hty2, hw2, hbd2⟩ | ⟨lit2⟩ | ⟨pn2, pi2, ps2, pnm2, pes2, hpn2, hps2⟩
    · exact dqArm_stuck hμ henv hsim a' b' _ _ hok hx₁ hp₁ hx hy hwx hwy (fun _ => by rfl) hG
    · exact dqArm_stuck hμ henv hsim a' b' _ _ hok hx₁ hp₁ hx hy hwx hwy (fun _ => by rfl) hG
    · exact dqArm_stuck hμ henv hsim a' b' _ _ hok hx₁ hp₁ hx hy hwx hwy (fun _ => by rfl) hG
    · exact dqArm_stuck hμ henv hsim a' b' _ _ hok hx₁ hp₁ hx hy hwx hwy (fun _ => by rfl) hG
    · exact dqArm_stuck hμ henv hsim a' b' _ _ hok hx₁ hp₁ hx hy hwx hwy (fun _ => by rfl) hG
    · exact dqArm_etaR hμ henv hsim a' b' ty2 bd2 m2 _ et2 eb2 hok hx₁ hp₁ hx hy hty2 hbd2 hwx hwy (fun _ => by rfl) hG
    · exact dqArm_stuck hμ henv hsim a' b' _ _ hok hx₁ hp₁ hx hy hwx hwy (fun _ => by rfl) hG
    · exact dqArm_stuck hμ henv hsim a' b' _ _ hok hx₁ hp₁ hx hy hwx hwy (fun _ => by rfl) hG
    · rcases lit2 with nv2 | sv2
      · exact dqArm_stuck hμ henv hsim a' b' _ _ hok hx₁ hp₁ hx hy hwx hwy (fun _ => by rfl) hG
      · exact dqArm_stuck hμ henv hsim a' b' _ _ hok hx₁ hp₁ hx hy hwx hwy (fun _ => by rfl) hG
    · exact dqArm_stuck hμ henv hsim a' b' _ _ hok hx₁ hp₁ hx hy hwx hwy (fun _ => by rfl) hG
  · -- left: const
    rcases hB with ⟨i2⟩ | ⟨k2, t2, et2, ht2⟩ | ⟨u2, l2, hl2⟩ | ⟨n2, us2, nm2, ls2, hn2, hls2⟩ | ⟨f2, a2, ef2, ea2, hf2, ha2⟩ | ⟨ty2, bd2, m2, et2, eb2, hty2, hbd2⟩ | ⟨ty2, bd2, m2, et2, eb2, hty2, hbd2⟩ | ⟨ty2, w2, bd2, et2, ew2, eb2, hty2, hw2, hbd2⟩ | ⟨lit2⟩ | ⟨pn2, pi2, ps2, pnm2, pes2, hpn2, hps2⟩
    · exact dqArm_stuck hμ henv hsim a' b' _ _ hok hx₁ hp₁ hx hy hwx hwy (fun _ => by rfl) hG
    · exact dqArm_stuck hμ henv hsim a' b' _ _ hok hx₁ hp₁ hx hy hwx hwy (fun _ => by rfl) hG
    · exact dqArm_stuck hμ henv hsim a' b' _ _ hok hx₁ hp₁ hx hy hwx hwy (fun _ => by rfl) hG
    · exact dqArm_const hμ henv hsim a' b' n1 n2 us1 us2 nm1 nm2 ls1 ls2 hok hx₁ hp₁ hx hy hn1 hn2 hls1 hls2 hG
    · exact dqArm_stuck hμ henv hsim a' b' _ _ hok hx₁ hp₁ hx hy hwx hwy (fun _ => by rfl) hG
    · exact dqArm_etaR hμ henv hsim a' b' ty2 bd2 m2 _ et2 eb2 hok hx₁ hp₁ hx hy hty2 hbd2 hwx hwy (fun _ => by rfl) hG
    · exact dqArm_stuck hμ henv hsim a' b' _ _ hok hx₁ hp₁ hx hy hwx hwy (fun _ => by rfl) hG
    · exact dqArm_stuck hμ henv hsim a' b' _ _ hok hx₁ hp₁ hx hy hwx hwy (fun _ => by rfl) hG
    · rcases lit2 with nv2 | sv2
      · exact dqArm_stuck hμ henv hsim a' b' _ _ hok hx₁ hp₁ hx hy hwx hwy (fun _ => by rfl) hG
      · exact dqArm_stuck hμ henv hsim a' b' _ _ hok hx₁ hp₁ hx hy hwx hwy (fun _ => by rfl) hG
    · exact dqArm_stuck hμ henv hsim a' b' _ _ hok hx₁ hp₁ hx hy hwx hwy (fun _ => by rfl) hG
  · -- left: app
    rcases hB with ⟨i2⟩ | ⟨k2, t2, et2, ht2⟩ | ⟨u2, l2, hl2⟩ | ⟨n2, us2, nm2, ls2, hn2, hls2⟩ | ⟨f2, a2, ef2, ea2, hf2, ha2⟩ | ⟨ty2, bd2, m2, et2, eb2, hty2, hbd2⟩ | ⟨ty2, bd2, m2, et2, eb2, hty2, hbd2⟩ | ⟨ty2, w2, bd2, et2, ew2, eb2, hty2, hw2, hbd2⟩ | ⟨lit2⟩ | ⟨pn2, pi2, ps2, pnm2, pes2, hpn2, hps2⟩
    · exact dqArm_stuck hμ henv hsim a' b' _ _ hok hx₁ hp₁ hx hy hwx hwy (fun _ => by (cases ef1 <;> rfl)) hG
    · exact dqArm_stuck hμ henv hsim a' b' _ _ hok hx₁ hp₁ hx hy hwx hwy (fun _ => by (cases ef1 <;> rfl)) hG
    · exact dqArm_stuck hμ henv hsim a' b' _ _ hok hx₁ hp₁ hx hy hwx hwy (fun _ => by (cases ef1 <;> rfl)) hG
    · exact dqArm_stuck hμ henv hsim a' b' _ _ hok hx₁ hp₁ hx hy hwx hwy (fun _ => by (cases ef1 <;> rfl)) hG
    · exact dqArm_app hμ henv hsim a' b' ef1 ea1 ef2 ea2 hok hx₁ hp₁ hx hy hwx hwy hG
    · exact dqArm_etaR hμ henv hsim a' b' ty2 bd2 m2 _ et2 eb2 hok hx₁ hp₁ hx hy hty2 hbd2 hwx hwy (fun _ => by (cases ef1 <;> rfl)) hG
    · exact dqArm_stuck hμ henv hsim a' b' _ _ hok hx₁ hp₁ hx hy hwx hwy (fun _ => by (cases ef1 <;> rfl)) hG
    · exact dqArm_stuck hμ henv hsim a' b' _ _ hok hx₁ hp₁ hx hy hwx hwy (fun _ => by (cases ef1 <;> rfl)) hG
    · rcases lit2 with nv2 | sv2
      · exact dqArm_stuck hμ henv hsim a' b' _ _ hok hx₁ hp₁ hx hy hwx hwy (fun _ => by (cases ef1 <;> rfl)) hG
      · exact dqArm_strR hμ henv hsim a' b' f1 sv2 ef1 ea1 hok hx₁ hp₁ hx hy hf1 hwx hG
    · exact dqArm_stuck hμ henv hsim a' b' _ _ hok hx₁ hp₁ hx hy hwx hwy (fun _ => by (cases ef1 <;> rfl)) hG
  · -- left: lam
    rcases hB with ⟨i2⟩ | ⟨k2, t2, et2, ht2⟩ | ⟨u2, l2, hl2⟩ | ⟨n2, us2, nm2, ls2, hn2, hls2⟩ | ⟨f2, a2, ef2, ea2, hf2, ha2⟩ | ⟨ty2, bd2, m2, et2, eb2, hty2, hbd2⟩ | ⟨ty2, bd2, m2, et2, eb2, hty2, hbd2⟩ | ⟨ty2, w2, bd2, et2, ew2, eb2, hty2, hw2, hbd2⟩ | ⟨lit2⟩ | ⟨pn2, pi2, ps2, pnm2, pes2, hpn2, hps2⟩
    · exact dqArm_etaL hμ henv hsim a' b' ty1 bd1 m1 et1 eb1 _ hok hx₁ hp₁ hx hty1 hbd1 hy hwx hwy (fun _ => by rfl) hG
    · exact dqArm_etaL hμ henv hsim a' b' ty1 bd1 m1 et1 eb1 _ hok hx₁ hp₁ hx hty1 hbd1 hy hwx hwy (fun _ => by rfl) hG
    · exact dqArm_etaL hμ henv hsim a' b' ty1 bd1 m1 et1 eb1 _ hok hx₁ hp₁ hx hty1 hbd1 hy hwx hwy (fun _ => by rfl) hG
    · exact dqArm_etaL hμ henv hsim a' b' ty1 bd1 m1 et1 eb1 _ hok hx₁ hp₁ hx hty1 hbd1 hy hwx hwy (fun _ => by rfl) hG
    · exact dqArm_etaL hμ henv hsim a' b' ty1 bd1 m1 et1 eb1 _ hok hx₁ hp₁ hx hty1 hbd1 hy hwx hwy (fun _ => by rfl) hG
    · exact dqArm_etaL hμ henv hsim a' b' ty1 bd1 m1 et1 eb1 _ hok hx₁ hp₁ hx hty1 hbd1 hy hwx hwy (fun _ => by rfl) hG
    · exact dqArm_etaL hμ henv hsim a' b' ty1 bd1 m1 et1 eb1 _ hok hx₁ hp₁ hx hty1 hbd1 hy hwx hwy (fun _ => by rfl) hG
    · exact dqArm_etaL hμ henv hsim a' b' ty1 bd1 m1 et1 eb1 _ hok hx₁ hp₁ hx hty1 hbd1 hy hwx hwy (fun _ => by rfl) hG
    · rcases lit2 with nv2 | sv2
      · exact dqArm_etaL hμ henv hsim a' b' ty1 bd1 m1 et1 eb1 _ hok hx₁ hp₁ hx hty1 hbd1 hy hwx hwy (fun _ => by rfl) hG
      · exact dqArm_etaL hμ henv hsim a' b' ty1 bd1 m1 et1 eb1 _ hok hx₁ hp₁ hx hty1 hbd1 hy hwx hwy (fun _ => by rfl) hG
    · exact dqArm_etaL hμ henv hsim a' b' ty1 bd1 m1 et1 eb1 _ hok hx₁ hp₁ hx hty1 hbd1 hy hwx hwy (fun _ => by rfl) hG
  · -- left: forallE
    rcases hB with ⟨i2⟩ | ⟨k2, t2, et2, ht2⟩ | ⟨u2, l2, hl2⟩ | ⟨n2, us2, nm2, ls2, hn2, hls2⟩ | ⟨f2, a2, ef2, ea2, hf2, ha2⟩ | ⟨ty2, bd2, m2, et2, eb2, hty2, hbd2⟩ | ⟨ty2, bd2, m2, et2, eb2, hty2, hbd2⟩ | ⟨ty2, w2, bd2, et2, ew2, eb2, hty2, hw2, hbd2⟩ | ⟨lit2⟩ | ⟨pn2, pi2, ps2, pnm2, pes2, hpn2, hps2⟩
    · exact dqArm_stuck hμ henv hsim a' b' _ _ hok hx₁ hp₁ hx hy hwx hwy (fun _ => by rfl) hG
    · exact dqArm_stuck hμ henv hsim a' b' _ _ hok hx₁ hp₁ hx hy hwx hwy (fun _ => by rfl) hG
    · exact dqArm_stuck hμ henv hsim a' b' _ _ hok hx₁ hp₁ hx hy hwx hwy (fun _ => by rfl) hG
    · exact dqArm_stuck hμ henv hsim a' b' _ _ hok hx₁ hp₁ hx hy hwx hwy (fun _ => by rfl) hG
    · exact dqArm_stuck hμ henv hsim a' b' _ _ hok hx₁ hp₁ hx hy hwx hwy (fun _ => by rfl) hG
    · exact dqArm_etaR hμ henv hsim a' b' ty2 bd2 m2 _ et2 eb2 hok hx₁ hp₁ hx hy hty2 hbd2 hwx hwy (fun _ => by rfl) hG
    · exact dqArm_stuck hμ henv hsim a' b' _ _ hok hx₁ hp₁ hx hy hwx hwy (fun _ => by rfl) hG
    · exact dqArm_stuck hμ henv hsim a' b' _ _ hok hx₁ hp₁ hx hy hwx hwy (fun _ => by rfl) hG
    · rcases lit2 with nv2 | sv2
      · exact dqArm_stuck hμ henv hsim a' b' _ _ hok hx₁ hp₁ hx hy hwx hwy (fun _ => by rfl) hG
      · exact dqArm_stuck hμ henv hsim a' b' _ _ hok hx₁ hp₁ hx hy hwx hwy (fun _ => by rfl) hG
    · exact dqArm_stuck hμ henv hsim a' b' _ _ hok hx₁ hp₁ hx hy hwx hwy (fun _ => by rfl) hG
  · -- left: letE
    rcases hB with ⟨i2⟩ | ⟨k2, t2, et2, ht2⟩ | ⟨u2, l2, hl2⟩ | ⟨n2, us2, nm2, ls2, hn2, hls2⟩ | ⟨f2, a2, ef2, ea2, hf2, ha2⟩ | ⟨ty2, bd2, m2, et2, eb2, hty2, hbd2⟩ | ⟨ty2, bd2, m2, et2, eb2, hty2, hbd2⟩ | ⟨ty2, w2, bd2, et2, ew2, eb2, hty2, hw2, hbd2⟩ | ⟨lit2⟩ | ⟨pn2, pi2, ps2, pnm2, pes2, hpn2, hps2⟩
    · exact dqArm_stuck hμ henv hsim a' b' _ _ hok hx₁ hp₁ hx hy hwx hwy (fun _ => by rfl) hG
    · exact dqArm_stuck hμ henv hsim a' b' _ _ hok hx₁ hp₁ hx hy hwx hwy (fun _ => by rfl) hG
    · exact dqArm_stuck hμ henv hsim a' b' _ _ hok hx₁ hp₁ hx hy hwx hwy (fun _ => by rfl) hG
    · exact dqArm_stuck hμ henv hsim a' b' _ _ hok hx₁ hp₁ hx hy hwx hwy (fun _ => by rfl) hG
    · exact dqArm_stuck hμ henv hsim a' b' _ _ hok hx₁ hp₁ hx hy hwx hwy (fun _ => by rfl) hG
    · exact dqArm_etaR hμ henv hsim a' b' ty2 bd2 m2 _ et2 eb2 hok hx₁ hp₁ hx hy hty2 hbd2 hwx hwy (fun _ => by rfl) hG
    · exact dqArm_stuck hμ henv hsim a' b' _ _ hok hx₁ hp₁ hx hy hwx hwy (fun _ => by rfl) hG
    · exact dqArm_stuck hμ henv hsim a' b' _ _ hok hx₁ hp₁ hx hy hwx hwy (fun _ => by rfl) hG
    · rcases lit2 with nv2 | sv2
      · exact dqArm_stuck hμ henv hsim a' b' _ _ hok hx₁ hp₁ hx hy hwx hwy (fun _ => by rfl) hG
      · exact dqArm_stuck hμ henv hsim a' b' _ _ hok hx₁ hp₁ hx hy hwx hwy (fun _ => by rfl) hG
    · exact dqArm_stuck hμ henv hsim a' b' _ _ hok hx₁ hp₁ hx hy hwx hwy (fun _ => by rfl) hG
  · -- left: lit
    rcases lit1 with nv1 | sv1
    · -- Nat literal
      rcases hB with ⟨i2⟩ | ⟨k2, t2, et2, ht2⟩ | ⟨u2, l2, hl2⟩ | ⟨n2, us2, nm2, ls2, hn2, hls2⟩ | ⟨f2, a2, ef2, ea2, hf2, ha2⟩ | ⟨ty2, bd2, m2, et2, eb2, hty2, hbd2⟩ | ⟨ty2, bd2, m2, et2, eb2, hty2, hbd2⟩ | ⟨ty2, w2, bd2, et2, ew2, eb2, hty2, hw2, hbd2⟩ | ⟨lit2⟩ | ⟨pn2, pi2, ps2, pnm2, pes2, hpn2, hps2⟩
      · exact dqArm_stuck hμ henv hsim a' b' _ _ hok hx₁ hp₁ hx hy hwx hwy (fun _ => by rfl) hG
      · exact dqArm_stuck hμ henv hsim a' b' _ _ hok hx₁ hp₁ hx hy hwx hwy (fun _ => by rfl) hG
      · exact dqArm_stuck hμ henv hsim a' b' _ _ hok hx₁ hp₁ hx hy hwx hwy (fun _ => by rfl) hG
      · exact dqArm_stuck hμ henv hsim a' b' _ _ hok hx₁ hp₁ hx hy hwx hwy (fun _ => by rfl) hG
      · exact dqArm_stuck hμ henv hsim a' b' _ _ hok hx₁ hp₁ hx hy hwx hwy (fun _ => by rfl) hG
      · exact dqArm_etaR hμ henv hsim a' b' ty2 bd2 m2 _ et2 eb2 hok hx₁ hp₁ hx hy hty2 hbd2 hwx hwy (fun _ => by rfl) hG
      · exact dqArm_stuck hμ henv hsim a' b' _ _ hok hx₁ hp₁ hx hy hwx hwy (fun _ => by rfl) hG
      · exact dqArm_stuck hμ henv hsim a' b' _ _ hok hx₁ hp₁ hx hy hwx hwy (fun _ => by rfl) hG
      · rcases lit2 with nv2 | sv2
        · exact dqArm_stuck hμ henv hsim a' b' _ _ hok hx₁ hp₁ hx hy hwx hwy (fun _ => by rfl) hG
        · exact dqArm_stuck hμ henv hsim a' b' _ _ hok hx₁ hp₁ hx hy hwx hwy (fun _ => by rfl) hG
      · exact dqArm_stuck hμ henv hsim a' b' _ _ hok hx₁ hp₁ hx hy hwx hwy (fun _ => by rfl) hG
    · -- String literal
      rcases hB with ⟨i2⟩ | ⟨k2, t2, et2, ht2⟩ | ⟨u2, l2, hl2⟩ | ⟨n2, us2, nm2, ls2, hn2, hls2⟩ | ⟨f2, a2, ef2, ea2, hf2, ha2⟩ | ⟨ty2, bd2, m2, et2, eb2, hty2, hbd2⟩ | ⟨ty2, bd2, m2, et2, eb2, hty2, hbd2⟩ | ⟨ty2, w2, bd2, et2, ew2, eb2, hty2, hw2, hbd2⟩ | ⟨lit2⟩ | ⟨pn2, pi2, ps2, pnm2, pes2, hpn2, hps2⟩
      · exact dqArm_stuck hμ henv hsim a' b' _ _ hok hx₁ hp₁ hx hy hwx hwy (fun _ => by rfl) hG
      · exact dqArm_stuck hμ henv hsim a' b' _ _ hok hx₁ hp₁ hx hy hwx hwy (fun _ => by rfl) hG
      · exact dqArm_stuck hμ henv hsim a' b' _ _ hok hx₁ hp₁ hx hy hwx hwy (fun _ => by rfl) hG
      · exact dqArm_stuck hμ henv hsim a' b' _ _ hok hx₁ hp₁ hx hy hwx hwy (fun _ => by rfl) hG
      · exact dqArm_strL hμ henv hsim a' b' f2 sv1 ef2 ea2 hok hx₁ hp₁ hx hy hf2 hwy hG
      · exact dqArm_etaR hμ henv hsim a' b' ty2 bd2 m2 _ et2 eb2 hok hx₁ hp₁ hx hy hty2 hbd2 hwx hwy (fun _ => by rfl) hG
      · exact dqArm_stuck hμ henv hsim a' b' _ _ hok hx₁ hp₁ hx hy hwx hwy (fun _ => by rfl) hG
      · exact dqArm_stuck hμ henv hsim a' b' _ _ hok hx₁ hp₁ hx hy hwx hwy (fun _ => by rfl) hG
      · rcases lit2 with nv2 | sv2
        · exact dqArm_stuck hμ henv hsim a' b' _ _ hok hx₁ hp₁ hx hy hwx hwy (fun _ => by rfl) hG
        · exact dqArm_stuck hμ henv hsim a' b' _ _ hok hx₁ hp₁ hx hy hwx hwy (fun _ => by rfl) hG
      · exact dqArm_stuck hμ henv hsim a' b' _ _ hok hx₁ hp₁ hx hy hwx hwy (fun _ => by rfl) hG
  · -- left: proj
    rcases hB with ⟨i2⟩ | ⟨k2, t2, et2, ht2⟩ | ⟨u2, l2, hl2⟩ | ⟨n2, us2, nm2, ls2, hn2, hls2⟩ | ⟨f2, a2, ef2, ea2, hf2, ha2⟩ | ⟨ty2, bd2, m2, et2, eb2, hty2, hbd2⟩ | ⟨ty2, bd2, m2, et2, eb2, hty2, hbd2⟩ | ⟨ty2, w2, bd2, et2, ew2, eb2, hty2, hw2, hbd2⟩ | ⟨lit2⟩ | ⟨pn2, pi2, ps2, pnm2, pes2, hpn2, hps2⟩
    · exact dqArm_stuck hμ henv hsim a' b' _ _ hok hx₁ hp₁ hx hy hwx hwy (fun _ => by rfl) hG
    · exact dqArm_stuck hμ henv hsim a' b' _ _ hok hx₁ hp₁ hx hy hwx hwy (fun _ => by rfl) hG
    · exact dqArm_stuck hμ henv hsim a' b' _ _ hok hx₁ hp₁ hx hy hwx hwy (fun _ => by rfl) hG
    · exact dqArm_stuck hμ henv hsim a' b' _ _ hok hx₁ hp₁ hx hy hwx hwy (fun _ => by rfl) hG
    · exact dqArm_stuck hμ henv hsim a' b' _ _ hok hx₁ hp₁ hx hy hwx hwy (fun _ => by rfl) hG
    · exact dqArm_etaR hμ henv hsim a' b' ty2 bd2 m2 _ et2 eb2 hok hx₁ hp₁ hx hy hty2 hbd2 hwx hwy (fun _ => by rfl) hG
    · exact dqArm_stuck hμ henv hsim a' b' _ _ hok hx₁ hp₁ hx hy hwx hwy (fun _ => by rfl) hG
    · exact dqArm_stuck hμ henv hsim a' b' _ _ hok hx₁ hp₁ hx hy hwx hwy (fun _ => by rfl) hG
    · rcases lit2 with nv2 | sv2
      · exact dqArm_stuck hμ henv hsim a' b' _ _ hok hx₁ hp₁ hx hy hwx hwy (fun _ => by rfl) hG
      · exact dqArm_stuck hμ henv hsim a' b' _ _ hok hx₁ hp₁ hx hy hwx hwy (fun _ => by rfl) hG
    · exact dqArm_stuck hμ henv hsim a' b' _ _ hok hx₁ hp₁ hx hy hwx hwy (fun _ => by rfl) hG

/-- con-leche: ConLeche/Kernel/Core.lean:1722-1789 defeqStuck — the same, in
the eventual form the callers merge: con-leche's answer itself. -/
theorem defeqStuck_spec' {fe : IFEnv} {fuel : Nat}
    (henv : ConLeche.EnvWF env) (hμ : mode.verifiedChecks = true)
    (hsim : KnotSpec mode env fe fuel) (d : Nat)
    (s₀ : AState) (a' b' : EIdx) (x' y' : Expr)
    (hok : CheckOK mode env fe s₀)
    (hx : denoteE s₀.store a' = some x') (hy : denoteE s₀.store b' = some y')
    (hwx : Expr.WScoped d x') (hwy : Expr.WScoped d y') :
    ⦃fun s => ⌜s = s₀⌝⦄ ConRon.Arena.defeqStuck mode (coreKnot mode fe id fuel) fe d a' b'
    ⦃⇓? r s' => ⌜CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧
        Ev (fun F => ConLeche.defeqStuck mode (ConLeche.pureFns mode env F)
          env d x' y' = .ok r)⌝⦄ := by
  refine triple_mono (defeqStuck_spec henv hμ hsim d s₀ s₀ a' b' x' y' hok
    (Ext.refl _) rfl hx hy hwx hwy
    (fun F r => ConLeche.defeqStuck mode (ConLeche.pureFns mode env F) env d x' y'
      = .ok r) ⟨0, fun _ _ _ h => h⟩) ?_
  rintro r s' ⟨hok', hx', hp', hF⟩
  exact ⟨hok', hx', hp', Ev.of_mono (fun hle h => defeqStuckF_mono hle h) hF⟩

#print axioms defeqStuck_spec'

end ConRon.Bridge.Core
