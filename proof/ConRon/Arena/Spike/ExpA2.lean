/-
# Experiment A, subject 2 — the `app`-of-`lam` β arm of `whnfCoreBody`

`ConLeche/Kernel/Core.lean:1935`, the `.app` clause, with the knot record
abstracted as a hypothesis exactly as con-leche's body takes `r : CoreFns m`.
This is the subject that tests whether the `@[spec]`/`mvcgen` idiom composes
through a *record of hypotheses* rather than through global lemmas.

**Status**: the twin (`whnfCoreAppArm`, `Twins.lean`) is written and the
statement is below; the proof is `sorry`.  The spike's budget went to
subject 1, whose 61 verification conditions are what taught the discipline in
`Specs.lean`; subject 3 (`ExpA3.lean`) then closed in 2.0 s *with that
discipline already in place*, which is the number that matters for
extrapolating to subject 2.  What subject 2 adds over subject 3 is a
`CoreFnsA` record of three triple-shaped hypotheses instead of one, and a
pure side that has to be *computed* (`whnfCoreBody`'s `.app` clause reduced
in `Except`) rather than assumed — see the report.
-/
import ConRon.Arena.Spike.Specs

namespace ConRon.Arena.Spike

open ConLeche Std.Do

set_option mvcgen.warning false

/-- con-leche: ConLeche/Verify/SimI.lean:250 RelE — the pure side of a
`whnfCore`-grade step, at a *fixed* pure record (the knot is not tied here,
so there is no `∃ F`; that appears one level up, in subject 3). -/
def PureAt (op : Expr → CheckM Expr) (st : EStore) (c : EIdx) (st' : EStore)
    (r : EIdx) : Prop :=
  ∀ e, denoteE st c = some e → ∃ e', denoteE st' r = some e' ∧ op e = .ok e'

/-- con-leche: ConLeche/Verify/SimIKnot.lean:28 SSimI — the knot record's
simulation hypothesis, one clause per slot `whnfCoreAppArm` calls. -/
structure CoreSimA (rp : CoreFns CheckM) (ra : CoreFnsA) : Prop where
  whnfCore : ∀ (s₀ : AState) (dep : Nat) (c : EIdx), StateOK s₀ →
    (denoteE s₀.store c).isSome = true → s₀.inst1C = ∅ →
    ⦃fun s => ⌜s = s₀⌝⦄ ra.whnfCore dep c
    ⦃⇓? r s' => ⌜StateOK s' ∧ Ext s₀.store s'.store ∧ s'.inst1C = ∅ ∧
        PureAt (rp.whnfCore dep) s₀.store c s'.store r⌝⦄
  inferIO : ∀ (s₀ : AState) (dep : Nat) (c : EIdx), StateOK s₀ →
    (denoteE s₀.store c).isSome = true → s₀.inst1C = ∅ →
    ⦃fun s => ⌜s = s₀⌝⦄ ra.inferIO dep c
    ⦃⇓? r s' => ⌜StateOK s' ∧ Ext s₀.store s'.store ∧ s'.inst1C = ∅ ∧
        PureAt (rp.inferIO dep) s₀.store c s'.store r⌝⦄
  defeq : ∀ (s₀ : AState) (dep : Nat) (c₁ c₂ : EIdx), StateOK s₀ →
    (denoteE s₀.store c₁).isSome = true → (denoteE s₀.store c₂).isSome = true →
    s₀.inst1C = ∅ →
    ⦃fun s => ⌜s = s₀⌝⦄ ra.defeq dep c₁ c₂
    ⦃⇓? b s' => ⌜StateOK s' ∧ Ext s₀.store s'.store ∧ s'.inst1C = ∅ ∧
        ∀ e₁ e₂, denoteE s₀.store c₁ = some e₁ → denoteE s₀.store c₂ = some e₂ →
          rp.defeq dep e₁ e₂ = .ok b⌝⦄

/-- con-leche: ConLeche/Kernel/Core.lean:1941 whnfCoreBody (the `.app` arm) —
**Theorem 1 for subject 2**.  NOT PROVED; see the module doc. -/
theorem whnfCoreAppArm_spec (mode : CheckMode) (env : Env) (rp : CoreFns CheckM)
    (ra : CoreFnsA) (hsim : CoreSimA rp ra) (fuel : Nat) (s₀ : AState)
    (dep : Nat) (hh f a : EIdx) (hok : StateOK s₀) (hempty : s₀.inst1C = ∅)
    (hview : s₀.store.view hh = some (.app f a))
    (hden : (denoteE s₀.store hh).isSome = true) :
    ⦃fun s => ⌜s = s₀⌝⦄ whnfCoreAppArm mode ra fuel dep f a
    ⦃⇓? h' s' => ⌜StateOK s' ∧ Ext s₀.store s'.store ∧ s'.inst1C = ∅ ∧
        PureAt (whnfCoreBody mode rp env dep) s₀.store hh s'.store h'⌝⦄ := by
  sorry

end ConRon.Arena.Spike
