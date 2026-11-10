/-
# `ConRon.Bridge.Core.Arms.DefeqBinders` — Theorem 1 for the binder-telescope congruence

`quickDefEq`'s two binder arms (two ∀s, two λs) run `defeqBinders`
(con-leche's `is_def_eq_binding` shape, `Kernel/Core.lean`), one level at a
time against con-leche's own loop: the twin keeps the variables so far as a
push-order `Array` (`ExprOps.InstLVec` relates it to the specification's
innermost-first list) and opens with `instantiateListFast`, which denotes
con-leche's `instantiateList` over that list (`ExprOps.instantiateListFast_spec`).

| twin function | spec |
|---|---|
| `defeqBindersInner` | `defeqBindersInner_spec` |
| `defeqDomain` | `defeqDomain_spec` (the answer from some fuel on) |
| `defeqBinders` | `defeqBinders_spec` (induction on the descent budget) |

The pure side (§1) is one equation per exit of con-leche's `defeqBinders`
(`binders_dom_false`, `binders_leaf`, `binders_descend`) and two of
`defeqDomain`; the scoping of the next level is `instantiateList_cons` and
`WScoped.instantiate1` (`binders_wscoped_next`).  The proofs keep this
module's earlier triple-chaining style (a repair, not a new walk).
-/
module

import ConRon.Bridge.Core.Memo
public import ConRon.Bridge.ExprOps.Subst
import ConRon.Bridge.ExprOps.Spine
import ConRon.Bridge.ExprOps.Walks
public import ConRon.Bridge.Core.Knot
import ConRon.Bridge.Core.Walks.Mono
import ConLeche.Verify.Mono
public import ConLeche.Verify.Knot
import ConRon.Bridge.Specs

public section

namespace ConRon.Bridge.Core

set_option autoImplicit false
set_option experimental.vcgen true
set_option maxHeartbeats 1000000

open ConLeche ConRon.Arena ConRon.Bridge Std.WP
open scoped Lean.Order

variable {mode : CheckMode} {eager : Bool} {env : Env}

/-! ## 1. The pure side -/

section Pure

variable {r : CoreFns CheckM}

/-- con-leche: ConLeche/Kernel/Core.lean:1456-1460 defeqDomain — two equal
raw domains. -/
theorem defeqDomain_same {d : Nat} {ws : List Expr} {t₁ t₂ D : Expr}
    (h : (t₁ == t₂) = true) : ConLeche.defeqDomain r d ws t₁ t₂ D = .ok true := by
  simp [ConLeche.defeqDomain, h, pure, Except.pure]

/-- con-leche: ConLeche/Kernel/Core.lean:1456-1460 defeqDomain — two
different raw domains: the opened left one against `D`. -/
theorem defeqDomain_cmp {d : Nat} {ws : List Expr} {t₁ t₂ D : Expr} {v : Bool}
    (h : (t₁ == t₂) = false) (hv : r.defeq d (t₁.instantiateList ws 0) D = .ok v) :
    ConLeche.defeqDomain r d ws t₁ t₂ D = .ok v := by
  simp [ConLeche.defeqDomain, h, hv]

/-- con-leche: ConLeche/Kernel/Core.lean:1462-1485 defeqBinders — the
domains differ. -/
theorem binders_dom_false {lam : Bool} {n d : Nat} {ws : List Expr} {t₁ c₁ t₂ c₂ : Expr}
    (h : ConLeche.defeqDomain r d ws t₁ t₂ (t₂.instantiateList ws 0) = .ok false) :
    ConLeche.defeqBinders mode r lam n d ws t₁ c₁ t₂ c₂ = .ok false := by
  rw [ConLeche.defeqBinders.eq_def]
  simp [h, bind, Except.bind, pure, Except.pure]

/-- con-leche: ConLeche/Kernel/Core.lean:1462-1485 defeqBinders — the
domains agree and the descent stops here (budget out, or not both binders of
the kind): the innermost level, both bodies opened over the pushed list. -/
theorem binders_leaf {lam : Bool} {n d : Nat} {ws : List Expr} {t₁ c₁ t₂ c₂ : Expr}
    {x : Bool}
    (h : ConLeche.defeqDomain r d ws t₁ t₂ (t₂.instantiateList ws 0) = .ok true)
    (hstop : n = 0 ∨ Expr.binderPair? lam c₁ c₂ = none)
    (hin : ConLeche.defeqBindersInner mode r lam d
      (c₁.instantiateList (.fvar d (t₂.instantiateList ws 0) :: ws) 0)
      (c₂.instantiateList (.fvar d (t₂.instantiateList ws 0) :: ws) 0) = .ok x) :
    ConLeche.defeqBinders mode r lam n d ws t₁ c₁ t₂ c₂ = .ok x := by
  rw [ConLeche.defeqBinders.eq_def]
  simp only [h, bind, Except.bind, pure, Except.pure]
  rcases hstop with rfl | hn
  · exact hin
  · rw [hn]; cases n <;> exact hin

/-- con-leche: ConLeche/Kernel/Core.lean:1462-1485 defeqBinders — the
domains agree and both bodies are binders of the kind: one level deeper, at
the pushed list. -/
theorem binders_descend {lam : Bool} {n d : Nat} {ws : List Expr}
    {t₁ c₁ t₂ c₂ a b c e : Expr} {x : Bool}
    (h : ConLeche.defeqDomain r d ws t₁ t₂ (t₂.instantiateList ws 0) = .ok true)
    (hbp : Expr.binderPair? lam c₁ c₂ = some (a, b, c, e))
    (hn : ConLeche.defeqBinders mode r lam n (d + 1)
      (.fvar d (t₂.instantiateList ws 0) :: ws) a b c e = .ok x) :
    ConLeche.defeqBinders mode r lam (n + 1) d ws t₁ c₁ t₂ c₂ = .ok x := by
  rw [ConLeche.defeqBinders.eq_def]
  simp only [h, bind, Except.bind, pure, Except.pure, hbp]
  exact hn

end Pure

/-- con-leche: ConLeche/Kernel/ExprOps.lean:551-575 instantiateList — a
binder of either kind opens componentwise, the body one cursor up. -/
theorem binderOf_instantiateList (lam : Bool) (t b : Expr) (ws : List Expr) (k : Nat) :
    (Expr.binderOf lam t b).instantiateList ws k =
      Expr.binderOf lam (t.instantiateList ws k) (b.instantiateList ws (k + 1)) := by
  cases lam <;> simp [Expr.binderOf, Expr.instantiateList]

/-- con-leche: none — a binder of either kind is scoped exactly when its two
components are. -/
theorem wscoped_binderOf {d : Nat} {lam : Bool} {t b : Expr} :
    Expr.WScoped d (Expr.binderOf lam t b) ↔ Expr.WScoped d t ∧ Expr.WScoped d b := by
  cases lam <;> simp [Expr.binderOf, Expr.WScoped]

/-- con-leche: ConLeche/Kernel/ExprOps.lean:606 instantiateList_cons — the
level's opening one variable further in: a term scoped at `d` over the list,
at cursor `k + 1`, is scoped at `d + 1` over the pushed list at cursor `k`. -/
theorem binders_wscoped_next {d k : Nat} {D e : Expr} {ws : List Expr}
    (hD : Expr.WScoped d D) (he : Expr.WScoped d (e.instantiateList ws (k + 1))) :
    Expr.WScoped (d + 1) (e.instantiateList (.fvar d D :: ws) k) := by
  rw [Expr.instantiateList_cons]
  exact Expr.WScoped.instantiate1 hD k he

/-- con-leche: ConLeche/Kernel/ExprOps.lean:840-845 binderPair? — two
binders of the kind answer their components. -/
theorem binderPair?_binderOf (lam : Bool) (a b c e : Expr) :
    Expr.binderPair? lam (Expr.binderOf lam a b) (Expr.binderOf lam c e) =
      some (a, b, c, e) := by
  cases lam <;> rfl

/-! ## 2. The twin -/

variable {fe : IFEnv} {fuel : Nat}

/-- con-leche: ConLeche/Kernel/Core.lean:1447-1454 defeqBindersInner — **the
innermost level**: the opened bodies through the knot, and for λs their
FULL-grade types. -/
theorem defeqBindersInner_spec (hsim : KnotSpec eager env fe fuel) (lam : Bool) (d : Nat)
    {s₀ : AState} (b₁ b₂ : EIdx) (x₁ x₂ : Expr) (hok : CheckOK eager env fe s₀)
    (hd1 : denoteE s₀.store b₁ = some x₁) (hd2 : denoteE s₀.store b₂ = some x₂)
    (hw1 : Expr.WScoped (d + 1) x₁) (hw2 : Expr.WScoped (d + 1) x₂) :
    ⦃fun s => s = s₀⦄
      ConRon.Arena.defeqBindersInner .verified (coreKnot .verified eager fe id fuel) lam d b₁ b₂
    ⦃fun r s' => CheckOK eager env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧
        ∃ F, ConLeche.defeqBindersInner .verified (ConLeche.pureFns .verified eager env F) lam d
          x₁ x₂ = .ok r; ⊤⦄ := by
  unfold ConRon.Arena.defeqBindersInner
  refine triple_seq (hsim.defeq s₀ (d + 1) b₁ b₂ x₁ x₂ hok hd1 hd2 hw1 hw2) ?_
  rintro v s1 ⟨hok1, hx1, hp1, F1, hF1⟩
  have e1 : (ConLeche.pureFns .verified eager env F1).defeq (d + 1) x₁ x₂ = .ok v := hF1
  cases v
  · simp only [Bool.not_false, ite_true]
    exact triple_pure_post ⟨hok1, hx1, hp1, F1, by
      simp [ConLeche.defeqBindersInner, e1, bind, Except.bind, pure, Except.pure]⟩
  simp only [Bool.not_true, Bool.false_eq_true, ite_false, CheckMode.verifiedChecks,
    Bool.and_true]
  cases lam
  · simp only [Bool.false_eq_true, ite_false]
    exact triple_pure_post ⟨hok1, hx1, hp1, F1, by
      simp [ConLeche.defeqBindersInner, e1, bind, Except.bind, pure, Except.pure]⟩
  simp only [ite_true]
  refine triple_seq (hsim.infer s1 (d + 1) b₁ x₁ hok1 (denote_ext hd1 hx1) hw1) ?_
  rintro t₁ s2 ⟨hok2, hx2, hp2, T1, hT1, hwT1, F2, hF2⟩
  refine triple_seq (hsim.infer s2 (d + 1) b₂ x₂ hok2
    (denote_ext hd2 (hx1.trans hx2)) hw2) ?_
  rintro t₂ s3 ⟨hok3, hx3, hp3, T2, hT2, hwT2, F3, hF3⟩
  refine triple_mono (hsim.defeq s3 (d + 1) t₁ t₂ T1 T2 hok3
    (denote_ext hT1 hx3) hT2 hwT1 hwT2) ?_
  rintro r s4 ⟨hok4, hx4, hp4, F4, hF4⟩
  refine ⟨hok4, hx1.trans (hx2.trans (hx3.trans hx4)),
    by rw [hp4, hp3, hp2, hp1], F1 + F2 + F3 + F4, ?_⟩
  have e1 : (ConLeche.pureFns .verified eager env (F1 + F2 + F3 + F4)).defeq (d + 1) x₁ x₂
      = .ok true := ConLeche.isDefEqCore_mono (by omega) hF1
  have e2 : (ConLeche.pureFns .verified eager env (F1 + F2 + F3 + F4)).infer (d + 1) x₁
      = .ok T1 := ConLeche.inferTypeCore_mono (by omega) hF2
  have e3 : (ConLeche.pureFns .verified eager env (F1 + F2 + F3 + F4)).infer (d + 1) x₂
      = .ok T2 := ConLeche.inferTypeCore_mono (by omega) hF3
  have e4 : (ConLeche.pureFns .verified eager env (F1 + F2 + F3 + F4)).defeq (d + 1) T1 T2
      = .ok r := ConLeche.isDefEqCore_mono (by omega) hF4
  cases r <;>
    simp [ConLeche.defeqBindersInner, e1, e2, e3, e4, CheckMode.verifiedChecks, bind,
      Except.bind, pure, Except.pure]

/-- con-leche: ConLeche/Kernel/Core.lean:1456-1460 defeqDomain — **one
level's domains**: the same raw handle is `true` (the specification's
`ty₁ == ty₂` on the denotations); otherwise the left domain is opened over
the vector and compared through the knot.  The answer holds from some fuel on
(`DefeqBase`'s `Ev` spelled out: this module sits below `DefeqBase`). -/
theorem defeqDomain_spec (hsim : KnotSpec eager env fe fuel) (d : Nat) {s₀ : AState}
    (fvs : Array EIdx) (ws : List Expr) (ty₁ ty₂ dom₂ : EIdx) (t₁ t₂ D : Expr)
    (hok : CheckOK eager env fe s₀) (hvec : ExprOps.InstLVec s₀.store fvs ws)
    (h1 : denoteE s₀.store ty₁ = some t₁) (h2 : denoteE s₀.store ty₂ = some t₂)
    (hD : denoteE s₀.store dom₂ = some D)
    (hw1 : Expr.WScoped d (t₁.instantiateList ws 0)) (hwD : Expr.WScoped d D) :
    ⦃fun s => s = s₀⦄
      ConRon.Arena.defeqDomain (coreKnot .verified eager fe id fuel) d fvs ty₁ ty₂ dom₂
    ⦃fun r s' => CheckOK eager env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧
        ∃ F₀, ∀ F, F₀ ≤ F → ConLeche.defeqDomain (ConLeche.pureFns .verified eager env F) d ws
          t₁ t₂ D = .ok r; ⊤⦄ := by
  unfold ConRon.Arena.defeqDomain
  rw [beq_of_denoteE hok.state.wf h1 h2]
  split
  · rename_i hsame
    exact triple_pure_post ⟨hok, Ext.refl _, rfl, 0, fun _ _ => defeqDomain_same hsame⟩
  · rename_i hne
    have hne' : (t₁ == t₂) = false := by simpa using hne
    refine triple_seq (ExprOps.instantiateListFast_spec coreWalkFuel s₀ ty₁ fvs 0 ws
      hok.state hvec (by rw [h1]; rfl)) ?_
    rintro o1 s1 ⟨hst1, hx1, hc1, hp1, _, hrel1⟩
    have hok1 := hok.mono hst1 hx1 hc1 hp1
    refine triple_mono (hsim.defeq s1 d o1 dom₂ _ _ hok1 (hrel1 _ h1)
      (denote_ext hD hx1) hw1 hwD) ?_
    rintro v s2 ⟨hok2, hx2, hp2, F1, hF1⟩
    exact ⟨hok2, hx1.trans hx2, hp2.trans hp1, F1, fun F hF =>
      defeqDomain_cmp hne' (ConLeche.isDefEqCore_mono hF hF1)⟩

/-- con-leche: ConLeche/Kernel/Core.lean:1462-1485 defeqBinders — **the
innermost level on the twin side**: both raw bodies opened over the pushed
vector, then `defeqBindersInner_spec`. -/
theorem bindersLeaf_spec (hsim : KnotSpec eager env fe fuel) (lam : Bool) (d : Nat)
    {s₀ : AState} (fvs : Array EIdx) (ws : List Expr) (bd₁ bd₂ : EIdx) (c₁ c₂ : Expr)
    (hok : CheckOK eager env fe s₀) (hvec : ExprOps.InstLVec s₀.store fvs ws)
    (h1 : denoteE s₀.store bd₁ = some c₁) (h2 : denoteE s₀.store bd₂ = some c₂)
    (hw1 : Expr.WScoped (d + 1) (c₁.instantiateList ws 0))
    (hw2 : Expr.WScoped (d + 1) (c₂.instantiateList ws 0)) :
    ⦃fun s => s = s₀⦄
      (do
        let b₁ ← instantiateListFast coreWalkFuel bd₁ fvs 0
        let b₂ ← instantiateListFast coreWalkFuel bd₂ fvs 0
        ConRon.Arena.defeqBindersInner .verified (coreKnot .verified eager fe id fuel) lam d
          b₁ b₂ : AM Bool)
    ⦃fun r s' => CheckOK eager env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧
        ∃ F, ConLeche.defeqBindersInner .verified (ConLeche.pureFns .verified eager env F) lam d
          (c₁.instantiateList ws 0) (c₂.instantiateList ws 0) = .ok r; ⊤⦄ := by
  refine triple_seq (ExprOps.instantiateListFast_spec coreWalkFuel s₀ bd₁ fvs 0 ws
    hok.state hvec (by rw [h1]; rfl)) ?_
  rintro o1 s1 ⟨hst1, hx1, hc1, hp1, _, hrel1⟩
  have hok1 := hok.mono hst1 hx1 hc1 hp1
  have h2' := denote_ext h2 hx1
  refine triple_seq (ExprOps.instantiateListFast_spec coreWalkFuel s1 bd₂ fvs 0 ws
    hst1 (hvec.ext hx1) (by rw [h2']; rfl)) ?_
  rintro o2 s2 ⟨hst2, hx2, hc2, hp2, _, hrel2⟩
  have hok2 := hok1.mono hst2 hx2 hc2 hp2
  refine triple_mono (defeqBindersInner_spec hsim lam d o1 o2 _ _ hok2
    (denote_ext (hrel1 _ h1) hx2) (hrel2 _ h2') hw1 hw2) ?_
  rintro r s3 ⟨hok3, hx3, hp3, hF⟩
  exact ⟨hok3, hx1.trans (hx2.trans hx3), hp3.trans (hp2.trans hp1), hF⟩

/-- con-leche: ConLeche/Kernel/Core.lean:1462-1485 defeqBinders — **THEOREM 1
for the binder-telescope congruence**, by induction on the descent budget:
at every level the right domain opened over the vector, the domains
(`defeqDomain_spec`), the fresh variable at the opened right domain, then the
budget and `binderPair?` — one level deeper at the pushed vector, or the
innermost level (`bindersLeaf_spec`).  The vector `fvs` denotes the
specification's list `ws` reversed (`InstLVec`); the four scoping premises
are the components opened over `ws`, the bodies one cursor up. -/
theorem defeqBinders_spec (hsim : KnotSpec eager env fe fuel) (lam : Bool) (n : Nat) :
    ∀ (d : Nat) (s₀ : AState) (fvs : Array EIdx) (ws : List Expr)
      (ty₁ bd₁ ty₂ bd₂ : EIdx) (t₁ c₁ t₂ c₂ : Expr),
      CheckOK eager env fe s₀ → ExprOps.InstLVec s₀.store fvs ws →
      denoteE s₀.store ty₁ = some t₁ → denoteE s₀.store bd₁ = some c₁ →
      denoteE s₀.store ty₂ = some t₂ → denoteE s₀.store bd₂ = some c₂ →
      Expr.WScoped d (t₁.instantiateList ws 0) → Expr.WScoped d (c₁.instantiateList ws 1) →
      Expr.WScoped d (t₂.instantiateList ws 0) → Expr.WScoped d (c₂.instantiateList ws 1) →
      ⦃fun s => s = s₀⦄
        ConRon.Arena.defeqBinders .verified (coreKnot .verified eager fe id fuel) lam n d fvs
          ty₁ bd₁ ty₂ bd₂
      ⦃fun r s' => CheckOK eager env fe s' ∧ Ext s₀.store s'.store ∧
          s'.pins = s₀.pins ∧
          ∃ F, ConLeche.defeqBinders .verified (ConLeche.pureFns .verified eager env F) lam n d
            ws t₁ c₁ t₂ c₂ = .ok r; ⊤⦄ := by
  intro d s₀ fvs ws ty₁ bd₁ ty₂ bd₂ t₁ c₁ t₂ c₂ hok hvec h1 h2 h3 h4 hw1 hwc1 hw2 hwc2
  rw [ConRon.Arena.defeqBinders.eq_def]
  dsimp only
  -- the right domain, opened over the vector
  refine triple_seq (ExprOps.instantiateListFast_spec coreWalkFuel s₀ ty₂ fvs 0 ws
    hok.state hvec (by rw [h3]; rfl)) ?_
  rintro dom₂ s1 ⟨hst1, hx1, hc1, hp1, _, hrel1⟩
  have hok1 := hok.mono hst1 hx1 hc1 hp1
  have hD : denoteE s1.store dom₂ = some (t₂.instantiateList ws 0) := hrel1 _ h3
  -- the domains
  refine triple_seq (defeqDomain_spec hsim d fvs ws ty₁ ty₂ dom₂ t₁ t₂ _ hok1
    (hvec.ext hx1) (denote_ext h1 hx1) (denote_ext h3 hx1) hD hw1 hw2) ?_
  rintro v s2 ⟨hok2, hx2, hp2, F1, hF1⟩
  cases v
  · simp only [Bool.not_false, ite_true]
    exact triple_pure_post ⟨hok2, hx1.trans hx2, hp2.trans hp1, F1,
      binders_dom_false (hF1 F1 (Nat.le_refl _))⟩
  simp only [Bool.not_true, Bool.false_eq_true, ite_false]
  -- the level's variable, at the opened right domain
  have hD2 := denote_ext hD hx2
  refine triple_seq (internFVarE_spec s2 d dom₂ hok2.state.wf (by rw [hD2]; rfl)) ?_
  rintro fv s3 ⟨hwf3, hx3, -, -, -, hc3, hp3, -, hfv⟩
  have hok3 := hok2.mono ⟨hwf3⟩ hx3 hc3 hp3
  have hx03 : Ext s₀.store s3.store := hx1.trans (hx2.trans hx3)
  have hp03 : s3.pins = s₀.pins := hp3.trans (hp2.trans hp1)
  have hfv' : denoteE s3.store fv = some (.fvar d (t₂.instantiateList ws 0)) := by
    rw [hfv]; simp [denoteEView, denote_ext hD2 hx3]
  have hvec3 : ExprOps.InstLVec s3.store (fvs.push fv)
      (.fvar d (t₂.instantiateList ws 0) :: ws) := by
    unfold ExprOps.InstLVec
    simp only [Array.toList_push, List.reverse_cons]
    exact ExprOps.denoteEList_snoc hfv' _ _ (hvec.ext hx03)
  have hb1 := denote_ext h2 hx03
  have hb2 := denote_ext h4 hx03
  have hwo1 := binders_wscoped_next (k := 0) hw2 hwc1
  have hwo2 := binders_wscoped_next (k := 0) hw2 hwc2
  -- the innermost level, from either exit
  have leaf : ∀ (hstop : n = 0 ∨ Expr.binderPair? lam c₁ c₂ = none),
      ⦃fun s => s = s3⦄
        (do
          let b₁ ← instantiateListFast coreWalkFuel bd₁ (fvs.push fv) 0
          let b₂ ← instantiateListFast coreWalkFuel bd₂ (fvs.push fv) 0
          ConRon.Arena.defeqBindersInner .verified (coreKnot .verified eager fe id fuel) lam d
            b₁ b₂ : AM Bool)
      ⦃fun r s' => CheckOK eager env fe s' ∧ Ext s₀.store s'.store ∧
          s'.pins = s₀.pins ∧
          ∃ F, ConLeche.defeqBinders .verified (ConLeche.pureFns .verified eager env F) lam n d
            ws t₁ c₁ t₂ c₂ = .ok r; ⊤⦄ := by
    intro hstop
    refine triple_mono (bindersLeaf_spec hsim lam d (fvs.push fv) _ bd₁ bd₂ c₁ c₂ hok3 hvec3
      hb1 hb2 hwo1 hwo2) ?_
    rintro r s' ⟨hok', hx', hp', F2, hF2⟩
    exact ⟨hok', hx03.trans hx', hp'.trans hp03, max F1 F2,
      binders_leaf (hF1 _ (by omega)) hstop
        (defeqBindersInnerFueled_mono (by omega) hF2)⟩
  cases n with
  | zero => exact leaf (.inl rfl)
  | succ m =>
    dsimp only
    refine triple_seq (ExprOps.binderPair?_spec lam s3 bd₁ bd₂ hok3.state
      (by rw [hb1]; rfl) (by rw [hb2]; rfl)) ?_
    rintro bp s4 ⟨rfl, hrel⟩
    cases bp with
    | none =>
      have hbp : Expr.binderPair? lam c₁ c₂ = none := by
        simpa only [hb1, hb2, opt2, Option.some.injEq] using hrel
      exact leaf (.inr hbp)
    | some q =>
      obtain ⟨ty₁', bd₁', ty₂', bd₂'⟩ := q
      obtain ⟨hda, hdb⟩ := hrel
      rw [hb1, eq_comm, opt2_eq_some_iff] at hda
      rw [hb2, eq_comm, opt2_eq_some_iff] at hdb
      obtain ⟨et₁, eb₁, hd1, hd2, rfl⟩ := hda
      obtain ⟨et₂, eb₂, hd3, hd4, rfl⟩ := hdb
      dsimp only
      rw [binderOf_instantiateList, wscoped_binderOf] at hwc1 hwc2
      refine triple_mono (defeqBinders_spec hsim lam m (d + 1) _ (fvs.push fv) _
        ty₁' bd₁' ty₂' bd₂' et₁ eb₁ et₂ eb₂ hok3 hvec3 hd1 hd2 hd3 hd4
        (binders_wscoped_next (k := 0) hw2 hwc1.1)
        (binders_wscoped_next (k := 1) hw2 hwc1.2)
        (binders_wscoped_next (k := 0) hw2 hwc2.1)
        (binders_wscoped_next (k := 1) hw2 hwc2.2)) ?_
      rintro r s' ⟨hok', hx', hp', F2, hF2⟩
      exact ⟨hok', hx03.trans hx', hp'.trans hp03, max F1 F2,
        binders_descend (hF1 _ (by omega)) (binderPair?_binderOf lam _ _ _ _)
          (defeqBindersFueled_mono (by omega) hF2)⟩
termination_by n

/-! ## The axiom census -/

#print axioms defeqDomain_same
#print axioms defeqDomain_cmp
#print axioms binders_dom_false
#print axioms binders_leaf
#print axioms binders_descend
#print axioms defeqBindersInner_spec
#print axioms defeqDomain_spec
#print axioms bindersLeaf_spec
#print axioms defeqBinders_spec

end ConRon.Bridge.Core
