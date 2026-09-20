/-
# Experiment A, subject 3 — the memo-probing wrapper, by `mvcgen`

`ConLeche/Cached/CoreC.lean:1877` (`memoEI`) at the `whnfCore` table, with the
body abstracted as a hypothesis exactly as con-leche's `memoEI_whnfCore_sim`
takes the body's simulation (`Verify/SimIKnot.lean`).

This is the subject that carries **lesson 8**: the memo key is the handle
alone, and an entry is justified by a depth-universal fact at some fuel
(`∃ F, ∀ d, …`).  The whole of that lives in `WhnfAt`/`WhnfMemoOK`
(`Specs.lean`); the proof below never mentions it.
-/
import ConRon.Arena.Spike.ExpA

namespace ConRon.Arena.Spike

open ConLeche Std.Do

set_option mvcgen.warning false
set_option maxHeartbeats 4000000

/-- The uniform closer at the `whnfCore` grade: the same three moves as
`spike_vcs`, with the `whnfCore` memo's lemmas instead of the
`instantiate1` memo's. -/
macro "spike_vcs3" : tactic => `(tactic| first
  | (intro hf; exact False.elim hf)
  | (spike_peel
     subst_vars
     grind (instances := 8000) [StateOK, WhnfMemoOK.mono, WhnfMemoOK.insert,
       WhnfMemoOK.get, Ext.trans, Ext.refl, Option.isSome_iff_exists]))

/-- con-leche: ConLeche/Verify/SimIKnot.lean:28 SSimI — **Theorem 1 for the
memo wrapper**: if the body simulates the pure operation, so does the wrapper.
The body is a hypothesis, in exactly the shape the knot will hand it. -/
theorem memoWhnfCore_spec (pw : Nat → Nat → Expr → CheckM Expr)
    (f : Nat → EIdx → AM EIdx)
    (hf : ∀ (s₁ : AState) (d : Nat) (c : EIdx), StateOK s₁ → WhnfMemoOK pw s₁ →
      (denoteE s₁.store c).isSome = true →
      ⦃fun s => ⌜s = s₁⌝⦄ f d c
      ⦃⇓? r s' => ⌜StateOK s' ∧ WhnfMemoOK pw s' ∧ Ext s₁.store s'.store ∧
          WhnfAt pw s₁.store c s'.store r⌝⦄)
    (s₀ : AState) (d : Nat) (h : EIdx) (hok : StateOK s₀) (hm : WhnfMemoOK pw s₀)
    (hden : (denoteE s₀.store h).isSome = true) :
    ⦃fun s => ⌜s = s₀⌝⦄ memoWhnfCore f d h
    ⦃⇓? h' s' => ⌜StateOK s' ∧ WhnfMemoOK pw s' ∧ Ext s₀.store s'.store ∧
        WhnfAt pw s₀.store h s'.store h'⌝⦄ := by
  mvcgen [memoWhnfCore, hf]
  all_goals spike_vcs3

/-- con-leche: ConLeche/Verify/BridgeI.lean:— runEntryE_bridge — the same
statement about a *run*, which is what the knot induction consumes. -/
theorem memoWhnfCore_run {pw : Nat → Nat → Expr → CheckM Expr}
    {f : Nat → EIdx → AM EIdx}
    (hf : ∀ (s₁ : AState) (d : Nat) (c : EIdx), StateOK s₁ → WhnfMemoOK pw s₁ →
      (denoteE s₁.store c).isSome = true →
      ⦃fun s => ⌜s = s₁⌝⦄ f d c
      ⦃⇓? r s' => ⌜StateOK s' ∧ WhnfMemoOK pw s' ∧ Ext s₁.store s'.store ∧
          WhnfAt pw s₁.store c s'.store r⌝⦄)
    {s₀ s' : AState} {d : Nat} {h h' : EIdx} (hok : StateOK s₀)
    (hm : WhnfMemoOK pw s₀) (hden : (denoteE s₀.store h).isSome = true)
    (hrun : (memoWhnfCore f d h).run s₀ = .ok (h', s')) :
    StateOK s' ∧ WhnfMemoOK pw s' ∧ Ext s₀.store s'.store ∧
      WhnfAt pw s₀.store h s'.store h' :=
  AM.of_run (P := fun s => s = s₀) rfl hrun
    (memoWhnfCore_spec pw f hf s₀ d h hok hm hden)

end ConRon.Arena.Spike
