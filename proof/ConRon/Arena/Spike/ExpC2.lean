/-
# Experiment C2 — the Lean twin refines con-leche's `instantiate1`

DESIGN §8.6's experiment C2, closed.  **No `Vec` and no `u32` occur**: this
half of Theorem 2 is *denotation only*, and it is experiment A's recipe — the
seven-rule spec-theorem template and one uniform closer — with ten
constructors cut to three.

The measurement the round-2 report wants from this file is that the recipe
transfers: `MiniSpecs.lean` is `Specs.lean`'s eight groups at the mini arena,
and with it in place the theorem below is `mvcgen` plus a closer.
-/
import ConRon.Arena.Spike.MiniSpecs

namespace ConRon.Arena.Spike

open ConLeche Std.Do

set_option mvcgen.warning false
set_option maxHeartbeats 2000000

/-- **The uniform closer**, at the mini arena.  `Specs.lean`'s `spike_vcs`
with the mini layer's lemma names, and — round 2's elaboration finding — the
three `Inst1AtM` transports left *out* of the hint list, because the
`_step` lemmas already carry the chain and tagging them as well is what sent
`grind` into a 144-instantiation spiral on subject 1. -/
macro "mini_vcs" : tactic => `(tactic| first
  | (intro hf; exact False.elim hf)
  | (subst_vars
     grind (instances := 4000) [MWF, MExt.trans, MExt.refl, Inst1MemoM.get,
       Inst1AtM.app_step, Inst1AtM.lam_step,
       Inst1AtM.bvar_hit, Inst1AtM.bvar_gt, Inst1AtM.bvar_le,
       Inst1MemoM.mono, DenotesM.ext, DenotesM.app_inv, DenotesM.lam_inv]))

/-- con-leche: ConLeche/Kernel/ExprOps.lean:33 instantiate1 — **experiment
C2**, as a Hoare triple in the template's shape. -/
theorem instantiate1_C2_spec (v : Nat) (ve : Expr) :
    ∀ (fuel : Nat) (s₀ : MState) (h d : Nat),
      MWF s₀ → Inst1MemoM ve s₀ → DenotesM s₀ v ve → DenotesSome s₀ h →
      ⦃fun s => ⌜s = s₀⌝⦄ mInstantiate1 v fuel h d
      ⦃⇓? r s' => ⌜MWF s' ∧ Inst1MemoM ve s' ∧ MExt s₀ s' ∧
          Inst1AtM ve d s₀ h s' r⌝⦄ := by
  intro fuel
  induction fuel with
  | zero =>
    intro s₀ h d _ _ _ _
    mvcgen [mInstantiate1]
    all_goals mini_vcs
  | succ fuel ih =>
    intro s₀ h d hwf hm hv hden
    mvcgen [mInstantiate1, ih]
    all_goals mini_vcs


/-! ## Theorem 1 as a statement about a *run*

`MM.of_run` is `Specs.lean`'s `AM.of_run` at the mini state: the one
soundness step from a triple back to `c.run s = .ok (a, s') → …`, which is
the form the composition with C1 consumes. -/

/-- con-leche: none — the `WP` soundness step for `MM`. -/
theorem MM.of_run {α : Type} {prog : MM α} {s s' : MState} {a : α}
    {P : MState → Prop} {Q : α → MState → Prop}
    (hp : P s) (h : prog.run s = .ok (a, s'))
    (hwp : ⦃fun s => ⌜P s⌝⦄ prog ⦃⇓? r s'' => ⌜Q r s''⌝⦄) : Q a s' := by
  have hs := hwp s
  simp only [WP.wp, PredTrans.apply_pushArg] at hs
  rw [h] at hs
  exact hs hp

/-- **Experiment C2** — the Lean twin refines con-leche's `instantiate1`.
No `Vec` and no `u32` occur: this half is *denotation only*. -/
theorem instantiate1_C2 (s s' : MState) (v fuel h d r : Nat) (ve e : Expr)
    (hwf : MWF s) (hmemo : Inst1MemoM ve s)
    (hv : DenotesM s v ve) (he : DenotesM s h e)
    (hrun : (mInstantiate1 v fuel h d).run s = .ok (r, s')) :
    MWF s' ∧ MExt s s' ∧ DenotesM s' r (e.instantiate1 ve d) := by
  have hq := MM.of_run (P := fun x => x = s) rfl hrun
    (instantiate1_C2_spec v ve fuel s h d hwf hmemo hv ⟨e, he⟩)
  exact ⟨hq.1, hq.2.2.1, hq.2.2.2 e he⟩

end ConRon.Arena.Spike
