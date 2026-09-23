/-
# `ConRon.Bridge.Core.Walks.FvarB` — `FvarBSpec`, discharged for the Core tier

Task #97-P3-Core round 6 (the maintainer's ruling 2 on round 5's question).
`Bridge/ExprOps/Abs.lean` takes `fvarB`'s Theorem 1 as the hypothesis
`ExprOps.FvarBSpec`; `Bridge/ExprOps/Ranges.lean`'s `fvarB_spec` states
everything it asks EXCEPT the `abs1C` frame (`fvarB` writes only `fvarBC`).
This module supplies that frame — a program-level fact over `fvarRangeGo`'s
mutual block — and assembles the record as `ConRon.Bridge.Core.fvarBSpec`, so
the Core tier's `abstract1Fast_spec` callers (`Arms/InferIO.lean`'s
`inferBodyIO_lam`, and the batched binder clauses) have their hypothesis.

**A duplicate.**  `Bridge/Inductives/Rel.lean:2598-2730` holds the same
proof (`Inductives.A1Prog`, `fvarRangeGo_a1`, `fvarB_a1`,
`Inductives.fvarBSpec`), which the Core tier cannot import (it sits above
`Bridge/Checker/Hyp.lean`, which imports this tier).  This copy is the one
below both tiers; **the Inductives lane should delete its copy and import
this module.**  Better still, `Ranges.lean`'s `fvarB_spec` gaining the
`abs1C` conjunct makes both one line.

The run-form helpers (`bindOk`, `pureOk`, `failOk`, `view_run`) are
`Inductives/Rel.lean`'s, copied under the `FvarB` namespace for the same
import reason.
-/
import ConRon.Bridge.Core.Walks.Cached
import ConRon.Bridge.ExprOps.Ranges

namespace ConRon.Bridge.Core

set_option autoImplicit false

open ConLeche ConRon.Arena ConRon.Bridge Std.Do

namespace FvarB

/-- con-leche: none — the `AM` bind's inversion (`Inductives/Rel.lean`'s
`bindOk`, copied). -/
theorem bindOk {α β : Type} {x : AM α} {f : α → AM β} {s s' : AState}
    {b : β} (h : (x >>= f) s = .ok (b, s')) :
    ∃ a s₁, x s = .ok (a, s₁) ∧ f a s₁ = .ok (b, s') := by
  have h' : ((x s) >>= (fun p => f p.1 p.2)) = .ok (b, s') := h
  clear h
  revert h'
  cases hx : x s with
  | error e => intro h; exact nomatch h
  | ok p =>
    obtain ⟨a, s₁⟩ := p
    intro h
    exact ⟨a, s₁, rfl, h⟩

/-- con-leche: none — the `AM` `pure`'s inversion (copied). -/
theorem pureOk {α : Type} {a r : α} {s s' : AState}
    (h : (pure a : AM α) s = .ok (r, s')) : r = a ∧ s' = s := by
  have h' : Except.ok ((a, s) : α × AState) = .ok (r, s') := h
  injection h' with h''
  injection h'' with h1 h2
  exact ⟨h1.symm, h2.symm⟩

/-- con-leche: none — a failing primitive cannot have accepted (copied). -/
theorem failOk {α : Type} {e : Arena.CheckError} {r : α} {s s' : AState}
    (h : (fail e : AM α) s = .ok (r, s')) : False := by
  simp only [Arena.fail, throwThe, MonadExceptOf.throw] at h
  exact nomatch h

/-- con-leche: none — `view`, as a run (copied). -/
theorem view_run {s s' : AState} {h : EIdx} {v : ENodeView}
    (hrun : view h s = .ok (v, s')) : s' = s ∧ s.store.view h = some v :=
  AM.of_run (P := fun t => t = s) rfl hrun (view_spec s h)

/-- con-leche: none — every accepting run leaves `abs1C` alone. -/
def A1Prog {α : Type} (c : AM α) : Prop :=
  ∀ (s s' : AState) (a : α), c s = .ok (a, s') → s'.memos.abs1C = s.memos.abs1C

theorem A1Prog.pure {α : Type} (a : α) : A1Prog (pure a : AM α) := by
  intro s s' b h; obtain ⟨-, rfl⟩ := pureOk h; rfl

theorem A1Prog.bind {α β : Type} {x : AM α} {f : α → AM β}
    (hx : A1Prog x) (hf : ∀ a, A1Prog (f a)) : A1Prog (x >>= f) := by
  intro s s' b h
  obtain ⟨a, s₁, h1, h2⟩ := bindOk h
  exact (hf a s₁ s' b h2).trans (hx s s₁ a h1)

theorem A1Prog.fail {α : Type} (e : Arena.CheckError) : A1Prog (Arena.fail e : AM α) := by
  intro s s' a h; exact absurd h (fun hc => failOk hc)

theorem A1Prog.fvarBGet (k : EIdx) : A1Prog (Arena.fvarBGet k) := by
  intro s s' a h
  simp only [Arena.fvarBGet] at h
  obtain ⟨t, s₁, h1, h2⟩ := bindOk h
  obtain ⟨rfl, rfl⟩ := Core.AM.get_ok h1
  obtain ⟨-, rfl⟩ := pureOk h2; rfl

theorem A1Prog.fvarBSet (k : EIdx) (r : Nat) : A1Prog (Arena.fvarBSet k r) := by
  intro s s' a h
  simp only [Arena.fvarBSet] at h
  obtain ⟨t, s₁, h1, h2⟩ := bindOk h
  obtain ⟨rfl, rfl⟩ := Core.AM.get_ok h1
  rw [Core.AM.set_ok h2]

theorem A1Prog.fvarBClear : A1Prog Arena.fvarBClear := by
  intro s s' a h
  simp only [Arena.fvarBClear] at h
  obtain ⟨t, s₁, h1, h2⟩ := bindOk h
  obtain ⟨rfl, rfl⟩ := Core.AM.get_ok h1
  rw [Core.AM.set_ok h2]

theorem A1Prog.view (k : EIdx) : A1Prog (Arena.view k) := by
  intro s s' a h
  obtain ⟨rfl, -⟩ := view_run h; rfl

theorem A1Prog.derivedE (k : EIdx) : A1Prog (Arena.derivedE k) := by
  intro s s' a h
  simp only [Arena.derivedE] at h
  obtain ⟨t, s₁, h1, h2⟩ := bindOk h
  obtain ⟨rfl, rfl⟩ := Core.AM.get_ok h1
  obtain ⟨-, rfl⟩ := pureOk h2; rfl

/-- con-leche: none — `fvarRangeGo`'s mutual block leaves `abs1C` alone, at
every fuel. -/
theorem fvarRangeGo_a1 : ∀ (fuel : Nat) (h : EIdx), A1Prog (Arena.fvarRangeGo fuel h) := by
  intro fuel
  induction fuel with
  | zero => intro h; rw [Arena.fvarRangeGo_zero]; exact A1Prog.fail _
  | succ fuel ih =>
    intro h
    rw [Arena.fvarRangeGo_succ]
    refine A1Prog.bind (A1Prog.fvarBGet h) (fun o => ?_)
    cases o with
    | some r => exact A1Prog.pure r
    | none =>
      refine A1Prog.bind ?_ (fun r => A1Prog.bind (A1Prog.fvarBSet h r) (fun _ => A1Prog.pure r))
      refine A1Prog.bind (A1Prog.view h) (fun v => ?_)
      cases v with
      | fvar idx t => exact A1Prog.pure _
      | bvar _ => exact A1Prog.pure _
      | sort _ => exact A1Prog.pure _
      | const _ _ => exact A1Prog.pure _
      | lit _ => exact A1Prog.pure _
      | app f a =>
        simp only [Arena.fvarRangeArmApp]
        exact A1Prog.bind (ih f) (fun _ => A1Prog.bind (ih a) (fun _ => A1Prog.pure _))
      | lam ty b _ =>
        simp only [Arena.fvarRangeArmBind]
        exact A1Prog.bind (ih ty) (fun _ => A1Prog.bind (ih b) (fun _ => A1Prog.pure _))
      | forallE ty b _ =>
        simp only [Arena.fvarRangeArmBind]
        exact A1Prog.bind (ih ty) (fun _ => A1Prog.bind (ih b) (fun _ => A1Prog.pure _))
      | letE ty w b =>
        simp only [Arena.fvarRangeArmLet]
        exact A1Prog.bind (ih ty) (fun _ => A1Prog.bind (ih w)
          (fun _ => A1Prog.bind (ih b) (fun _ => A1Prog.pure _)))
      | proj _ _ sub => exact ih sub

/-- con-leche: none — and so does `fvarB`. -/
theorem fvarB_a1 (fuel : Nat) (e : EIdx) : A1Prog (Arena.fvarB fuel e) := by
  simp only [Arena.fvarB]
  refine A1Prog.bind (A1Prog.derivedE e) (fun der => ?_)
  split
  · simp only [Arena.fvarRangeMemo]
    exact A1Prog.bind A1Prog.fvarBClear (fun _ => A1Prog.bind (fvarRangeGo_a1 fuel e)
      (fun r => A1Prog.bind A1Prog.fvarBClear (fun _ => A1Prog.pure r)))
  · exact A1Prog.pure _

/-- con-leche: none — a run lemma is a triple (the converse of `AM.of_run`). -/
theorem triple_of_run {α : Type} {prog : AM α} {P : AState → Prop}
    {Q : α → AState → Prop}
    (h : ∀ (s : AState) (a : α) (s' : AState), P s → prog.run s = .ok (a, s') →
      Q a s') :
    ⦃fun s => ⌜P s⌝⦄ prog ⦃⇓? r s'' => ⌜Q r s''⌝⦄ := by
  intro s hp
  simp only [WP.wp, PredTrans.apply_pushArg]
  cases hr : prog.run s with
  | error e => trivial
  | ok p => exact h s p.1 p.2 hp hr

end FvarB

/-- con-leche: ConLeche/Kernel/ExprOps.lean:1436-1441 fvarB — **`Abs.lean`'s
hypothesis, discharged for the Core tier**: `Ranges.lean`'s `fvarB_spec`
plus `FvarB.fvarB_a1`.  (`Inductives.fvarBSpec` in `Bridge/Inductives/Rel.lean`
is a duplicate, see the module note.) -/
theorem fvarBSpec : ExprOps.FvarBSpec where
  run := fun fuel s₁ h hok hden => FvarB.triple_of_run (P := fun s => s = s₁) (by
    intro s a s' hs hr
    subst hs
    obtain ⟨h1, h2, h3, h4⟩ := AM.of_run (P := fun t => t = s) rfl hr
      (ExprOps.fvarB_spec fuel s h hok hden)
    exact ⟨h1, h2, h3, FvarB.fvarB_a1 fuel h s s' a hr, h4⟩)

/-! `fvarBSpec`: `[propext, Classical.choice, Quot.sound]` expected. -/
#print axioms fvarBSpec

end ConRon.Bridge.Core
