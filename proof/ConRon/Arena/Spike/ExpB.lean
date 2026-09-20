/-
# Experiment B — the same theorem, by hand

DESIGN §8.6's experiment B: subject 3's Theorem 1 written the way con-ron's
current refinement proofs are written (`proof/ConRon/Refine/**`): state the
claim about the *run*, unfold the monad, case on each step, apply the store
lemmas by name.  No `mvcgen`, no `@[spec]` — the same `Specs.lean` lemmas,
applied explicitly.

The point is the comparison in `_tmp/t97/spike-report.md`: this file and
`ExpA3.lean` prove the same fact.
-/
import ConRon.Arena.Spike.Specs

namespace ConRon.Arena.Spike

open ConLeche Std.Do

/-- con-leche: ConLeche/Verify/SimI.lean:244 SimAt — the hypothesis and the
conclusion of subject 3, in the *forward* shape: a statement about a run,
with no Hoare triple anywhere. -/
def SimRun (pw : Nat → Nat → Expr → CheckM Expr) (c : Nat → EIdx → AM EIdx) : Prop :=
  ∀ (s₁ : AState) (d : Nat) (x : EIdx), StateOK s₁ → WhnfMemoOK pw s₁ →
    (denoteE s₁.store x).isSome = true →
    ∀ r s', (c d x).run s₁ = .ok (r, s') →
      StateOK s' ∧ WhnfMemoOK pw s' ∧ Ext s₁.store s'.store ∧
        WhnfAt pw s₁.store x s'.store r

/-- con-leche: ConLeche/Cached/CoreC.lean:1877 memoEI — **experiment B**: the
memo wrapper's Theorem 1, by hand. -/
theorem memoWhnfCore_run_hand {pw : Nat → Nat → Expr → CheckM Expr}
    {f : Nat → EIdx → AM EIdx} (hf : SimRun pw f) : SimRun pw (memoWhnfCore f) := by
  intro s₀ d h hok hm hden h' s' hrun
  simp only [memoWhnfCore, whnfCoreGet, whnfCoreSet, StateT.run, StateT.bind,
    StateT.get, StateT.pure, get, set, getThe, MonadStateOf.get,
    MonadStateOf.set, bind, pure, Except.bind, Except.pure] at hrun
  cases hget : s₀.whnfCoreC[h]? with
  | some r =>
    -- the memo HIT: the state is untouched and the entry is the answer
    rw [hget] at hrun
    simp only [StateT.pure] at hrun
    obtain ⟨rfl, rfl⟩ := hrun
    exact ⟨hok, hm, Ext.refl _, WhnfMemoOK.get hm hget⟩
  | none =>
    -- the memo MISS: run the body, then insert
    rw [hget] at hrun
    simp only [StateT.bind, StateT.get, StateT.set, StateT.pure] at hrun
    cases hbody : (f d h) s₀ with
    | error e =>
      rw [hbody] at hrun
      simp only [Bind.bind, Except.bind] at hrun
      exact absurd hrun (by simp)
    | ok p =>
      obtain ⟨r, s₁⟩ := p
      rw [hbody] at hrun
      simp at hrun
      obtain ⟨rfl, rfl⟩ := hrun
      obtain ⟨hok₁, hm₁, hx₁, hans⟩ := hf s₀ d h hok hm hden r s₁ hbody
      refine ⟨⟨hok₁.wf⟩, ?_, hx₁, hans⟩
      exact WhnfMemoOK.insert hm₁ rfl rfl
        (denote_isSome_ext hden hx₁) (hans.retarget hx₁ hden)

end ConRon.Arena.Spike
