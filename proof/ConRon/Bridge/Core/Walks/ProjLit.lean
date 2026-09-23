/-
# `ConRon.Bridge.Core.Walks.ProjLit` — the projection scrutinee's literal expansion

Task #97-P3-Core round 5.  `projLitToCtor` is the `.proj` clause's second
step: a string-literal scrutinee expands to its constructor form and is
head-normalised before the projection table is consulted.  Round 4 left it
in `Walks/Owed.lean` waiting on `strLitSupported`, `strLitToConstructor` and
`litMajorToCtor`; the first is `Walks/StrLit.lean`'s (this round, the leaves
helper), the second `Walks/StrCtor.lean`'s (this round), and the third turns
out not to be under `projLitToCtor` at all — it is the ι major's, under
`iotaRec`.  So the walk is now three stages.
-/
import ConRon.Bridge.Core.Walks.StrLit
import ConRon.Bridge.Core.Walks.StrCtor

namespace ConRon.Bridge.Core

set_option autoImplicit false
set_option mvcgen.warning false
set_option maxHeartbeats 1000000

open ConLeche ConRon.Arena ConRon.Bridge Std.Do

variable {mode : CheckMode} {env : Env} {fe : IFEnv}

/-- con-leche: none — a handle that denotes a literal views as that literal. -/
theorem view_of_denote_lit {st : EStore} (hwf : StoreWF st) {h : EIdx}
    {v : ENodeView} {l : Literal} (hv : st.view h = some v)
    (hd : denoteE st h = some (.lit l)) : v = .lit l := by
  cases v with
  | bvar i => have := denote_bvar_inv hwf hv hd; cases this
  | fvar k t => obtain ⟨_, h, _⟩ := denote_fvar_inv hwf hv hd; cases h
  | sort u => obtain ⟨_, h, _⟩ := denote_sort_inv hwf hv hd; cases h
  | const n us => obtain ⟨_, _, h, _, _⟩ := denote_const_inv hwf hv hd; cases h
  | app f a => obtain ⟨_, _, h, _, _⟩ := denote_app_inv hwf hv hd; cases h
  | lam ty b m => obtain ⟨_, _, h, _, _⟩ := denote_lam_inv hwf hv hd; cases h
  | forallE ty b m =>
    obtain ⟨_, _, h, _, _⟩ := denote_forallE_inv hwf hv hd; cases h
  | letE ty w b =>
    obtain ⟨_, _, _, h, _, _, _⟩ := denote_letE_inv hwf hv hd; cases h
  | lit l' => have := denote_lit_inv hwf hv hd; cases this; rfl
  | proj n i sub => obtain ⟨_, _, h, _, _⟩ := denote_proj_inv hwf hv hd; cases h

/-- con-leche: ConLeche/Kernel/Core.lean:742-756 projLitToCtor — **THEOREM 1
for `projLitToCtor`**: a string-literal scrutinee expands to its reduced
constructor form before the projection table is consulted.

**CLOSED** (round 5, moved here from `Walks/Owed.lean`, statement
unchanged): the scrutinee's `view`, `strLitSupported_spec`,
`strLitToConstructor_spec` and `KnotSpec.whnf`; every other scrutinee passes
through on both sides. -/
theorem projLitToCtor_spec {fuel : Nat} (hsim : KnotSpec mode env fe fuel)
    (s₀ : AState) (d : Nat) (h : EIdx) (x : Expr)
    (hok : CheckOK mode env fe s₀) (hden : denoteE s₀.store h = some x)
    (hw : Expr.WScoped d x) :
    ⦃fun s => ⌜s = s₀⌝⦄
      ConRon.Arena.projLitToCtor (coreKnot mode fe id fuel) fe d h
    ⦃⇓? r s' => ⌜CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧
        SimEOp (fun F => ConLeche.projLitToCtorFueled mode env F d x) d
          s'.store r⌝⦄ := by
  have hwf := hok.state.wf
  obtain ⟨v, hv⟩ := denoteE_view hden
  unfold ConRon.Arena.projLitToCtor
  refine view_bind_triple hv ?_
  -- every scrutinee but a string literal passes through
  have hpass : (∀ str, x ≠ .lit (.strVal str)) →
      ⦃fun s => ⌜s = s₀⌝⦄ (pure h : AM EIdx)
      ⦃⇓? r s' => ⌜CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
          s'.pins = s₀.pins ∧
          SimEOp (fun F => ConLeche.projLitToCtorFueled mode env F d x) d
            s'.store r⌝⦄ := by
    intro hnl
    mvcgen
    bridge_peel; subst_vars
    refine ⟨hok, Ext.refl _, rfl, x, hden, hw, 0, ?_⟩
    simp only [ConLeche.projLitToCtorFueled, ConLeche.projLitToCtor]
    first
      | rfl
      | (split
         · rename_i str heq; exact absurd heq (hnl str)
         · rfl)
  cases v
  case lit l =>
    obtain rfl := denote_lit_inv hwf hv hden
    cases l with
    | natVal n => exact hpass (by intro str h; cases h)
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
        simp only [ConLeche.projLitToCtorFueled, ConLeche.projLitToCtor, hS,
          if_true]
        exact hF
      next hsupf =>
        have hS : ConLeche.strLitSupported env = false := by
          rw [← hsup]; simpa using hsupf
        mvcgen
        bridge_peel; subst_vars
        refine ⟨hok1, hx1, hp1, .lit (.strVal str), denote_ext hden hx1, hw, 0,
          ?_⟩
        simp only [ConLeche.projLitToCtorFueled, ConLeche.projLitToCtor, hS,
          Bool.false_eq_true, if_false]
        rfl
  all_goals
    dsimp only
    refine hpass ?_
    intro str hx
    subst hx
    have := view_of_denote_lit hwf hv hden
    cases this

section Census

#print axioms projLitToCtor_spec

end Census

end ConRon.Bridge.Core
