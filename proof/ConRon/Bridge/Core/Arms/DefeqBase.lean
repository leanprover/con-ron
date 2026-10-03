/-
# `ConRon.Bridge.Core.Arms.DefeqBase` — the definitional-equality arm's toolkit

Task #109 (con-leche 8afe1815, `is_def_eq_core` restructured).  The pieces
every spec of `Arms/DefeqLazy.lean`, `Arms/DefeqStuck.lean` and
`Arms/Defeq.lean` shares, moved here from the old `Arms/Defeq.lean` (where
they served `defeqStep`, the loop step con-leche 8afe1815 replaced) so that
the three can build in parallel:

| group | contents |
|---|---|
| fuel | `Ev` ("from some fuel on") and its rules; `DqPost`, the frame-and-verdict postcondition |
| stage rules | `triple_pure_post`, `triple_ite_bind`, `CheckOK.of_store_eq` |
| guarded calls | `boolTrueShortcutIf_spec`, `defeqNoFvars_spec`, `reduceNatIf_spec` |
| denotations | `exprTag` / `tag_of_denote`, `VD` / `VD.of_view`, `ls_eq_iff_nil`, `n_eq_iff_pin` |
| exits | `dq_pure_exit`, `dq_defeq_exit`, `dq_stuck_exit` |
| monotonicity | `…F_mono` for the helpers of the new defeq block the specs merge at (`Walks/Mono.lean`'s shape) |
-/
import ConRon.Bridge.Core.Memo
import ConRon.Bridge.Core.Walks.PropRead
import ConRon.Bridge.Core.Walks.Stuck
import ConRon.Bridge.Core.Walks.ProjLit
import ConRon.Bridge.Core.Walks.Guards
import ConRon.Bridge.Core.Walks.Mono
import ConRon.Bridge.ExprOps.Ranges

namespace ConRon.Bridge.Core

set_option autoImplicit false
set_option mvcgen.warning false
set_option maxHeartbeats 1000000

open ConLeche ConRon.Arena ConRon.Bridge Std.Do

variable {mode : CheckMode} {env : Env}

/-! ## 1. Fuel: `Ev`

Every stage of a spec names a pure fact at SOME fuel.  The facts are carried
in the **eventually** form `Ev` — "from some fuel on" — which is closed under
conjunction for free, and one `Ev.exists` at the exit picks the fuel.  Each
stage turns its callee's `∃ F` into `Ev` by the callee's own monotonicity
lemma (§6). -/
/-- con-leche: none — **eventually at every fuel**: `p` holds from some fuel
on.  The fuel-monotone facts of the pure tier are exactly the ones that can
be put in this form, and two of them combine with no arithmetic at the use
site. -/
def Ev (p : Nat → Prop) : Prop := ∃ F₀, ∀ F, F₀ ≤ F → p F

/-- con-leche: none — `Ev` is closed under conjunction. -/
theorem Ev.and {p q : Nat → Prop} (hp : Ev p) (hq : Ev q) :
    Ev (fun F => p F ∧ q F) := by
  obtain ⟨F₁, h₁⟩ := hp
  obtain ⟨F₂, h₂⟩ := hq
  exact ⟨max F₁ F₂, fun F hF =>
    ⟨h₁ F (Nat.le_trans (Nat.le_max_left _ _) hF),
     h₂ F (Nat.le_trans (Nat.le_max_right _ _) hF)⟩⟩

/-- con-leche: none — a fuel-free fact holds eventually. -/
theorem Ev.const {P : Prop} (h : P) : Ev (fun _ => P) := ⟨0, fun _ _ => h⟩

/-- con-leche: none — the consequence rule of `Ev`. -/
theorem Ev.imp {p q : Nat → Prop} (hp : Ev p) (h : ∀ F, p F → q F) : Ev q := by
  obtain ⟨F₀, h₀⟩ := hp
  exact ⟨F₀, fun F hF => h F (h₀ F hF)⟩

/-- con-leche: ConLeche/Verify/Mono.lean:158 isDefEqCore_mono — **the
entry into `Ev`**: a fuel-monotone fact that holds at some fuel holds
eventually. -/
theorem Ev.of_mono {p : Nat → Prop} (hm : ∀ {f f' : Nat}, f ≤ f' → p f → p f')
    (h : ∃ F, p F) : Ev p := by
  obtain ⟨F, hF⟩ := h
  exact ⟨F, fun F' h' => hm h' hF⟩

/-- con-leche: none — **the exit from `Ev`**: the fuel the exit names. -/
theorem Ev.exists {p : Nat → Prop} (h : Ev p) : ∃ F, p F := by
  obtain ⟨F₀, h₀⟩ := h
  exact ⟨F₀, h₀ F₀ (Nat.le_refl _)⟩

/-- con-leche: none — `Ev` at the exit: a goal that follows eventually from a
fact that holds eventually holds at some fuel. -/
theorem Ev.finish {P G : Nat → Prop} (hG : Ev (fun F => P F → G F))
    (hP : Ev P) : ∃ F, G F :=
  (Ev.exists (hG.and hP)).imp fun _ h => h.1 h.2

/-- con-leche: none — the frame-and-verdict postcondition every stage of the
step ends in: the state invariant, the store only grown and the pins
untouched since `s₀`, and the pure goal `G` at some fuel. -/
def DqPost (mode : CheckMode) (env : Env) (fe : IFEnv) (s₀ : AState)
    (G : Nat → Bool → Prop) (r : Bool) (s' : AState) : Prop :=
  CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧ s'.pins = s₀.pins ∧
    ∃ F, G F r

/-- con-leche: none — **a `pure` exit** at a pinned state. -/
theorem triple_pure_post {α : Type} {s₀ : AState} {v : α}
    {Q : α → AState → Prop} (h : Q v s₀) :
    ⦃fun s => ⌜s = s₀⌝⦄ (pure v : AM α) ⦃⇓? r s => ⌜Q r s⌝⦄ := by
  mvcgen
  subst_vars; exact h

/-- con-leche: none — **a join point**: the do-compiler's
`if c then x >>= jp else y >>= jp` is the bind of the `if`. -/
theorem triple_ite_bind {α β : Type} {c : Prop} [Decidable c] {x y : AM α}
    {f : α → AM β} {s₀ : AState} {R : β → AState → Prop}
    (h : ⦃fun s => ⌜s = s₀⌝⦄ ((if c then x else y) >>= f)
      ⦃⇓? b s => ⌜R b s⌝⦄) :
    ⦃fun s => ⌜s = s₀⌝⦄ (if c then x >>= f else y >>= f)
      ⦃⇓? b s => ⌜R b s⌝⦄ := by
  by_cases hc : c
  · rw [if_pos hc] at h ⊢; exact h
  · rw [if_neg hc] at h ⊢; exact h

/-- con-leche: none — `CheckOK` across a stage that moved nothing but the
memos. -/
theorem _root_.ConRon.Bridge.CheckOK.of_store_eq {mode : CheckMode} {env : Env} {fe : IFEnv}
    {s s' : AState} (h : CheckOK mode env fe s) (hst : s'.store = s.store)
    (hc : s'.caches = s.caches) (hp : s'.pins = s.pins) :
    CheckOK mode env fe s' :=
  h.mono ⟨by rw [hst]; exact h.state.wf⟩ (by rw [hst]; exact Ext.refl _) hc hp

/-- con-leche: ConLeche/Kernel/Core.lean:1443-1455 boolTrueShortcut —
**the eq-true shortcut's guarded call**, both guard outcomes: the twin's
`boolTrueShortcut` is `KnotSpec.whnf` then `isBoolTrue`, con-leche's is
`whnf` then `Expr.isBoolTrue`. -/
theorem boolTrueShortcutIf_spec {fe : IFEnv} {fuel : Nat}
    (hsim : KnotSpec mode env fe fuel) (s₀ : AState) (d : Nat) (a : EIdx)
    (x : Expr) (c : Bool) (hok : CheckOK mode env fe s₀)
    (hx : denoteE s₀.store a = some x) (hwx : Expr.WScoped d x) :
    ⦃fun s => ⌜s = s₀⌝⦄
      (if c = true then
        ConRon.Arena.boolTrueShortcut (coreKnot mode fe id fuel) d a
      else pure false)
    ⦃⇓? sc s' => ⌜CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧
        Ev (fun F => (if c then
          ConLeche.boolTrueShortcut (ConLeche.pureFns mode env F) d x
          else pure false) = (.ok sc : CheckM Bool))⌝⦄ := by
  cases c
  · simp only [Bool.false_eq_true, if_false]
    exact triple_pure_post ⟨hok, Ext.refl _, rfl, Ev.const rfl⟩
  · simp only [if_true]
    unfold ConRon.Arena.boolTrueShortcut
    refine triple_seq (hsim.whnf s₀ d a x hok hx hwx) ?_
    rintro w s1 ⟨hok1, hx1, hp1, v, hv, _hwv, F1, hF1⟩
    refine triple_mono (isBoolTrue_spec s1 w v hok1 hv) ?_
    rintro sc s2 ⟨hok2, hst2, hp2, rfl⟩
    refine ⟨hok2, by rw [hst2]; exact hx1, hp2.trans hp1, ?_⟩
    refine Ev.of_mono (p := fun F => ConLeche.boolTrueShortcut
      (ConLeche.pureFns mode env F) d x = .ok v.isBoolTrue)
      (fun hle h => boolTrueShortcutFueled_mono hle h) ⟨F1, ?_⟩
    simp only [ConLeche.boolTrueShortcut, ConLeche.whnf_def, hF1, bind,
      Except.bind, pure, Except.pure]


/-! ## 2. Denotations and guards -/

/-- con-leche: none — **the constructor tag of a denotation**: the four tag
bits of a handle are the tag of the expression it denotes. -/
def exprTag : Expr → UInt32
  | .bvar _ => ETag.bvar
  | .fvar _ _ => ETag.fvar
  | .sort _ => ETag.sort
  | .const _ _ => ETag.const
  | .app _ _ => ETag.app
  | .lam _ _ _ => ETag.lam
  | .forallE _ _ _ => ETag.forallE
  | .letE _ _ _ => ETag.letE
  | .lit _ => ETag.lit
  | .proj _ _ _ => ETag.proj

/-- con-leche: none — DESIGN §8.3: a handle's tag is its denotation's. -/
theorem tag_of_denote {st : EStore} (hwf : StoreWF st) {h : EIdx} {e : Expr}
    (hd : denoteE st h = some e) : h.tag = exprTag e := by
  obtain ⟨v, hv⟩ := denoteE_view hd
  rw [EStore.tagOf_of_view hv]
  cases v with
  | bvar i => rw [denote_bvar_inv hwf hv hd]; rfl
  | fvar k t => obtain ⟨t', rfl, _⟩ := denote_fvar_inv hwf hv hd; rfl
  | sort u => obtain ⟨l, rfl, _⟩ := denote_sort_inv hwf hv hd; rfl
  | const n us => obtain ⟨nm, ls, rfl, _, _⟩ := denote_const_inv hwf hv hd; rfl
  | app f a => obtain ⟨p, q, rfl, _, _⟩ := denote_app_inv hwf hv hd; rfl
  | lam ty b m => obtain ⟨p, q, rfl, _, _⟩ := denote_lam_inv hwf hv hd; rfl
  | forallE ty b m =>
    obtain ⟨p, q, rfl, _, _⟩ := denote_forallE_inv hwf hv hd; rfl
  | letE ty w b =>
    obtain ⟨p, q, r, rfl, _, _, _⟩ := denote_letE_inv hwf hv hd; rfl
  | lit l => rw [denote_lit_inv hwf hv hd]; rfl
  | proj n i sub => obtain ⟨p, q, rfl, _, _⟩ := denote_proj_inv hwf hv hd; rfl


/-- con-leche: ConLeche/Kernel/Core.lean:1656-1689 lazyDeltaReduction — the literal
guard: the twin's two eager fvar-range reads are con-leche's
`!a'.hasFvar && !b'.hasFvar`. -/
theorem defeqNoFvars_spec {fe : IFEnv} (s₀ : AState) (a b : EIdx) (x y : Expr)
    (hok : CheckOK mode env fe s₀) (hx : denoteE s₀.store a = some x)
    (hy : denoteE s₀.store b = some y) :
    ⦃fun s => ⌜s = s₀⌝⦄ ConRon.Arena.defeqNoFvars a b
    ⦃⇓? nf s' => ⌜CheckOK mode env fe s' ∧ s'.store = s₀.store ∧
        s'.pins = s₀.pins ∧ nf = (!x.hasFvar && !y.hasFvar)⌝⦄ := by
  unfold ConRon.Arena.defeqNoFvars
  refine triple_seq (ExprOps.hasFvarFast_spec coreWalkFuel s₀ a hok.state
    (by rw [hx]; rfl)) ?_
  rintro hfa s1 ⟨hst1, hc1, hp1, hr1⟩
  have hok1 := hok.of_store_eq hst1 hc1 hp1
  have e1 : hfa = x.hasFvar := hr1 x hx
  subst e1
  cases hxa : x.hasFvar
  · simp only [Bool.false_eq_true, if_false]
    refine triple_seq (ExprOps.hasFvarFast_spec coreWalkFuel s1 b hok1.state
      (by rw [hst1, hy]; rfl)) ?_
    rintro hfb s2 ⟨hst2, hc2, hp2, hr2⟩
    have e2 : hfb = y.hasFvar := hr2 y (by rw [hst1]; exact hy)
    subst e2
    exact triple_pure_post ⟨hok1.of_store_eq hst2 hc2 hp2, hst2.trans hst1,
      hp2.trans hp1, by simp⟩
  · simp only [if_true]
    exact triple_pure_post ⟨hok1, hst1, hp1, by simp⟩

/-- con-leche: ConLeche/Kernel/Core.lean:1656-1689 lazyDeltaReduction — **the
guarded literal acceleration**, both guard outcomes, in the `SimOOp` shape
with the fuel carried eventually. -/
theorem reduceNatIf_spec {fe : IFEnv} {fuel : Nat}
    (hsim : KnotSpec mode env fe fuel) (s₀ : AState) (d : Nat) (e : EIdx)
    (x : Expr) (c : Bool) (hok : CheckOK mode env fe s₀)
    (hx : denoteE s₀.store e = some x) (hwx : Expr.WScoped d x) :
    ⦃fun s => ⌜s = s₀⌝⦄
      (if c = true then
        ConRon.Arena.reduceNat (coreKnot mode fe id fuel) fe d e
      else pure none)
    ⦃⇓? o s' => ⌜CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧
        ∃ v, denoteEO s'.store o = some v ∧
          (∀ z, v = some z → Expr.WScoped d z) ∧
          Ev (fun F => (if c then
            ConLeche.reduceNat (ConLeche.pureFns mode env F) env d x
            else pure none) = (.ok v : CheckM (Option Expr)))⌝⦄ := by
  cases c
  · simp only [Bool.false_eq_true, if_false]
    exact triple_pure_post ⟨hok, Ext.refl _, rfl, none, rfl,
      (fun _ h => nomatch h), Ev.const rfl⟩
  · simp only [if_true]
    refine triple_mono (reduceNat_spec hsim s₀ d e hok ⟨x, hx, hwx⟩) ?_
    rintro o s1 ⟨hok1, hx1, hp1, hsim1⟩
    obtain ⟨v, hv, hwv, hF⟩ := hsim1 x hx
    exact ⟨hok1, hx1, hp1, v, hv, hwv,
      Ev.of_mono (p := fun F => ConLeche.reduceNat
        (ConLeche.pureFns mode env F) env d x = .ok v)
        (fun hle h => reduceNatFueled_mono hle h) hF⟩

/-! ## 3. The exits, once

Every exit of a `Bool`-valued spec ends in a `pure` verdict, a knot `defeq`,
or the stuck fallback; each is proved here once, at an arbitrary pure goal
`G` that follows eventually from the exit's own pure run. -/

/-- con-leche: none — **a `pure` verdict** at the end of a stage. -/
theorem dq_pure_exit {fe : IFEnv} {s₀ s : AState} {G : Nat → Bool → Prop}
    {v : Bool} (hok : CheckOK mode env fe s) (hxs : Ext s₀.store s.store)
    (hps : s.pins = s₀.pins) (hG : Ev (fun F => G F v)) :
    ⦃fun s' => ⌜s' = s⌝⦄ (pure v : AM Bool)
    ⦃⇓? r s' => ⌜DqPost mode env fe s₀ G r s'⌝⦄ :=
  triple_pure_post ⟨hok, hxs, hps, hG.exists⟩


/-- con-leche: ConLeche/Kernel/TypeChecker.lean:51 isDefEqCore — **a knot
`defeq`** as the verdict. -/
theorem dq_defeq_exit {fe : IFEnv} {fuel d : Nat}
    (hsim : KnotSpec mode env fe fuel) {s₀ s : AState}
    {G : Nat → Bool → Prop} (p q : EIdx) (u w : Expr)
    (hok : CheckOK mode env fe s) (hxs : Ext s₀.store s.store)
    (hps : s.pins = s₀.pins) (hp : denoteE s.store p = some u)
    (hq : denoteE s.store q = some w) (hwu : Expr.WScoped d u)
    (hww : Expr.WScoped d w)
    (hG : Ev (fun F => ∀ r, ConLeche.isDefEqCore mode env F d u w = .ok r →
      G F r)) :
    ⦃fun s' => ⌜s' = s⌝⦄ (coreKnot mode fe id fuel).defeq d p q
    ⦃⇓? r s' => ⌜DqPost mode env fe s₀ G r s'⌝⦄ := by
  refine triple_mono (hsim.defeq s d p q u w hok hp hq hwu hww) ?_
  rintro r s' ⟨hok', hx', hp', hr⟩
  exact ⟨hok', hxs.trans hx', hp'.trans hps,
    Ev.finish (hG.imp fun _ h => h r)
      (Ev.of_mono (fun hle h => ConLeche.isDefEqCore_mono hle h) hr)⟩

/-- con-leche: ConLeche/Kernel/Core.lean:569-576 stuckIrrel — **the stuck
fallback** as the verdict, over `stuckIrrel_spec` (`Walks/Owed.lean`,
closed since).  The one call site of that rule in this module. -/
theorem dq_stuck_exit {fe : IFEnv} {fuel d : Nat}
    (hμ : mode.verifiedChecks = true) (henv : ConLeche.EnvWF env)
    (hsim : KnotSpec mode env fe fuel) {s₀ s : AState}
    {G : Nat → Bool → Prop} (p q : EIdx) (u w : Expr)
    (hok : CheckOK mode env fe s) (hxs : Ext s₀.store s.store)
    (hps : s.pins = s₀.pins) (hp : denoteE s.store p = some u)
    (hq : denoteE s.store q = some w) (hwu : Expr.WScoped d u)
    (hww : Expr.WScoped d w)
    (hG : Ev (fun F => ∀ r, ConLeche.stuckIrrel mode
      (ConLeche.pureFns mode env F) env d u w = .ok r → G F r)) :
    ⦃fun s' => ⌜s' = s⌝⦄
      ConRon.Arena.stuckIrrel mode (coreKnot mode fe id fuel) fe d p q
    ⦃⇓? r s' => ⌜DqPost mode env fe s₀ G r s'⌝⦄ := by
  refine triple_mono (stuckIrrel_spec hμ henv hsim s d p q u w hok hp hq hwu hww) ?_
  rintro r s' ⟨hok', hx', hp', hr⟩
  exact ⟨hok', hxs.trans hx', hp'.trans hps,
    Ev.finish (hG.imp fun _ h => h r)
      (Ev.of_mono (fun hle h => stuckIrrelFueled_mono hle h) hr)⟩

/-! ### The congruence arms

`VD` is the `view`-and-denotation pair at one handle, as one inductive: a
case split on it names the view's children and the denotation's in one step,
which is what the congruence dispatch (a hundred pairs) needs. -/

/-- con-leche: none — **a handle's view and its denotation, together**:
`denoteEView`'s ten equations as constructors. -/
inductive VD (st : EStore) : ENodeView → Expr → Prop
  | bvar (i : Nat) : VD st (.bvar i) (.bvar i)
  | fvar (k : Nat) (t : EIdx) (e : Expr) :
      denoteE st t = some e → VD st (.fvar k t) (.fvar k e)
  | sort (u : LIdx) (l : ConLeche.Level) :
      denoteL st.ls u = some l → VD st (.sort u) (.sort l)
  | const (n : NIdx) (us : LsIdx) (nm : ConLeche.Name)
      (ls : List ConLeche.Level) :
      denoteN st.ns n = some nm → denoteLs st.lss us = some ls →
      VD st (.const n us) (.const nm ls)
  | app (f a : EIdx) (ef ea : Expr) :
      denoteE st f = some ef → denoteE st a = some ea →
      VD st (.app f a) (.app ef ea)
  | lam (ty b : EIdx) (m : ConLeche.BinderMeta) (et eb : Expr) :
      denoteE st ty = some et → denoteE st b = some eb →
      VD st (.lam ty b m) (.lam et eb m)
  | forallE (ty b : EIdx) (m : ConLeche.BinderMeta) (et eb : Expr) :
      denoteE st ty = some et → denoteE st b = some eb →
      VD st (.forallE ty b m) (.forallE et eb m)
  | letE (ty w b : EIdx) (et ew eb : Expr) :
      denoteE st ty = some et → denoteE st w = some ew →
      denoteE st b = some eb → VD st (.letE ty w b) (.letE et ew eb)
  | lit (l : ConLeche.Literal) : VD st (.lit l) (.lit l)
  | proj (n : NIdx) (i : Nat) (sub : EIdx) (nm : ConLeche.Name) (es : Expr) :
      denoteN st.ns n = some nm → denoteE st sub = some es →
      VD st (.proj n i sub) (.proj nm i es)

/-- con-leche: none — the ten `denote_*_inv` lemmas of `Bridge/Rel.lean`, at
once. -/
theorem VD.of_view {st : EStore} (hwf : StoreWF st) {h : EIdx}
    {v : ENodeView} {x : Expr} (hv : st.view h = some v)
    (hd : denoteE st h = some x) : VD st v x := by
  cases v with
  | bvar i => rw [denote_bvar_inv hwf hv hd]; exact .bvar i
  | fvar k t =>
    obtain ⟨t', rfl, ht⟩ := denote_fvar_inv hwf hv hd; exact .fvar k t t' ht
  | sort u =>
    obtain ⟨l, rfl, hl⟩ := denote_sort_inv hwf hv hd; exact .sort u l hl
  | const n us =>
    obtain ⟨nm, ls, rfl, hn, hl⟩ := denote_const_inv hwf hv hd
    exact .const n us nm ls hn hl
  | app f a =>
    obtain ⟨p, q, rfl, hp, hq⟩ := denote_app_inv hwf hv hd
    exact .app f a p q hp hq
  | lam ty b m =>
    obtain ⟨p, q, rfl, hp, hq⟩ := denote_lam_inv hwf hv hd
    exact .lam ty b m p q hp hq
  | forallE ty b m =>
    obtain ⟨p, q, rfl, hp, hq⟩ := denote_forallE_inv hwf hv hd
    exact .forallE ty b m p q hp hq
  | letE ty w b =>
    obtain ⟨p, q, r, rfl, hp, hq, hr⟩ := denote_letE_inv hwf hv hd
    exact .letE ty w b p q r hp hq hr
  | lit l => rw [denote_lit_inv hwf hv hd]; exact .lit l
  | proj n i sub =>
    obtain ⟨nm, es, rfl, hn, hs⟩ := denote_proj_inv hwf hv hd
    exact .proj n i sub nm es hn hs


/-- con-leche: none — the empty-levels pin against a denoted level list:
handle equality is list equality. -/
theorem ls_eq_iff_nil {st : EStore} (hwf : StoreWF st) {us el : LsIdx}
    {ls : List ConLeche.Level} (hus : denoteLs st.lss us = some ls)
    (hel : denoteLs st.lss el = some []) : us = el ↔ ls = [] := by
  obtain ⟨rk, hrk⟩ := hwf
  constructor
  · rintro rfl; rw [hus] at hel; exact Option.some.inj hel
  · rintro rfl; exact denoteLs_inj hrk.lss hus hel

/-- con-leche: none — a pinned name against a denoted name. -/
theorem n_eq_iff_pin {st : EStore} (hwf : StoreWF st) {c nz : NIdx}
    {nm x : ConLeche.Name} (hc : denoteN st.ns c = some nm)
    (hnz : denoteN st.ns nz = some x) : c = nz ↔ nm = x := by
  obtain ⟨rk, hrk⟩ := hwf
  exact name_eq_iff_of_denoteN hrk.nsWF hc hnz

/-! ## 4. Monotonicity of the new defeq block

`Walks/Mono.lean`'s shape (the record-level `MRefines` from `Verify/PairM`'s
two projections, then the fueled corollary at `pureFns_mono`), for every
helper of the restructured `is_def_eq_core` that `Walks/Mono.lean` does not
already cover. -/

section MonoDefeq

variable {r₁ r₂ : CoreFns CheckM}

/-- con-leche: ConLeche/Verify/Mono.lean:52 whnfCoreBody_mono — the easy
cases refine at a refined record. -/
theorem quickDefEq_monoR (h : FnsRefines r₁ r₂) (d : Nat) (a b : Expr) :
    MRefines (ConLeche.quickDefEq mode r₁ d a b)
      (ConLeche.quickDefEq mode r₂ d a b) := by
  have := (ConLeche.quickDefEq mode (pairFns r₁ r₂ h) d a b).property
  rwa [quickDefEq_fst_proj, quickDefEq_snd_proj] at this

/-- con-leche: ConLeche/Verify/Mono.lean:52 whnfCoreBody_mono — the proj/proj
check. -/
theorem defeqProjPair_monoR (h : FnsRefines r₁ r₂) (d : Nat) (a b : Expr) :
    MRefines (ConLeche.defeqProjPair mode r₁ env d a b)
      (ConLeche.defeqProjPair mode r₂ env d a b) := by
  have := (ConLeche.defeqProjPair mode (pairFns r₁ r₂ h) env d a b).property
  rwa [defeqProjPair_fst_proj, defeqProjPair_snd_proj] at this

/-- con-leche: ConLeche/Verify/Mono.lean:52 whnfCoreBody_mono — the stuck
comparison. -/
theorem defeqStuck_monoR (h : FnsRefines r₁ r₂) (d : Nat) (a b : Expr) :
    MRefines (ConLeche.defeqStuck mode r₁ env d a b)
      (ConLeche.defeqStuck mode r₂ env d a b) := by
  have := (ConLeche.defeqStuck mode (pairFns r₁ r₂ h) env d a b).property
  rwa [defeqStuck_fst_proj, defeqStuck_snd_proj] at this

end MonoDefeq

/-- con-leche: ConLeche/Verify/Mono.lean:158 isDefEqCore_mono — the merge at
`quickDefEq`. -/
theorem quickDefEqF_mono {f f' : Nat} (hle : f ≤ f') {d : Nat} {a b : Expr}
    {r : Option Bool}
    (hr : ConLeche.quickDefEq mode (pureFns mode env f) d a b = .ok r) :
    ConLeche.quickDefEq mode (pureFns mode env f') d a b = .ok r :=
  quickDefEq_monoR (pureFns_mono env hle) d a b r hr

/-- con-leche: ConLeche/Verify/Mono.lean:158 isDefEqCore_mono — the merge at
`defeqProjPair`. -/
theorem defeqProjPairF_mono {f f' : Nat} (hle : f ≤ f') {d : Nat} {a b : Expr}
    {r : Bool}
    (hr : ConLeche.defeqProjPair mode (pureFns mode env f) env d a b = .ok r) :
    ConLeche.defeqProjPair mode (pureFns mode env f') env d a b = .ok r :=
  defeqProjPair_monoR (pureFns_mono env hle) d a b r hr

/-- con-leche: ConLeche/Verify/Mono.lean:158 isDefEqCore_mono — the merge at
`defeqStuck`. -/
theorem defeqStuckF_mono {f f' : Nat} (hle : f ≤ f') {d : Nat} {a b : Expr}
    {r : Bool}
    (hr : ConLeche.defeqStuck mode (pureFns mode env f) env d a b = .ok r) :
    ConLeche.defeqStuck mode (pureFns mode env f') env d a b = .ok r :=
  defeqStuck_monoR (pureFns_mono env hle) d a b r hr

end ConRon.Bridge.Core
