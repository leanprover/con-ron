/-
# `ConRon.Bridge.Core.Walks.FvarB` — `FvarBSpec`, discharged for the Core tier

Task #97-P3-Core round 6 (the maintainer's ruling 2 on round 5's question).
`Bridge/ExprOps/Abs.lean` takes `fvarB`'s Theorem 1 as the hypothesis
`ExprOps.FvarBSpec`; `Bridge/ExprOps/Ranges.lean`'s `fvarB_spec` states
everything it asks EXCEPT the `abs1C` frame (`fvarB` writes only `fvarBC`).
This module supplies that frame — a program-level fact over `fvarRangeGo`'s
mutual block — and assembles the record as `ConRon.Bridge.Core.fvarBSpec`, so
the Core tier's `abstract1Fast_spec` callers (`Arms/InferIO.lean`'s
`inferBodyIO_lam`, and the batched binder clauses) and the Inductives tier
have their hypothesis.  `Ranges.lean`'s `fvarB_spec` gaining the `abs1C`
conjunct would make this module one line.
-/
import ConRon.Bridge.Core.Walks.Cached
import ConRon.Bridge.ExprOps.Ranges

namespace ConRon.Bridge.Core

set_option autoImplicit false

open ConLeche ConRon.Arena ConRon.Bridge Std.Do

namespace FvarB

/-- con-leche: none — every accepting run leaves `abs1C` alone. -/
def A1Prog {α : Type} (c : AM α) : Prop :=
  ∀ (s s' : AState) (a : α), c s = .ok (a, s') → s'.memos.abs1C = s.memos.abs1C

theorem A1Prog.pure {α : Type} (a : α) : A1Prog (pure a : AM α) := by
  intro s s' b h; obtain ⟨-, rfl⟩ := AM.pure_ok h; rfl

theorem A1Prog.bind {α β : Type} {x : AM α} {f : α → AM β}
    (hx : A1Prog x) (hf : ∀ a, A1Prog (f a)) : A1Prog (x >>= f) := by
  intro s s' b h
  obtain ⟨a, s₁, h1, h2⟩ := AM.bind_ok h
  exact (hf a s₁ s' b h2).trans (hx s s₁ a h1)

theorem A1Prog.fail {α : Type} (e : Arena.CheckError) : A1Prog (Arena.fail e : AM α) := by
  intro s s' a h; exact absurd h (fun hc => AM.fail_ok hc)

theorem A1Prog.fvarBGet (k : EIdx) : A1Prog (Arena.fvarBGet k) := by
  intro s s' a h
  simp only [Arena.fvarBGet] at h
  obtain ⟨t, s₁, h1, h2⟩ := AM.bind_ok h
  obtain ⟨rfl, rfl⟩ := AM.get_ok h1
  obtain ⟨-, rfl⟩ := AM.pure_ok h2; rfl

theorem A1Prog.fvarBSet (k : EIdx) (r : Nat) : A1Prog (Arena.fvarBSet k r) := by
  intro s s' a h
  simp only [Arena.fvarBSet] at h
  obtain ⟨t, s₁, h1, h2⟩ := AM.bind_ok h
  obtain ⟨rfl, rfl⟩ := AM.get_ok h1
  rw [AM.set_ok h2]

theorem A1Prog.fvarBClear : A1Prog Arena.fvarBClear := by
  intro s s' a h
  simp only [Arena.fvarBClear] at h
  obtain ⟨t, s₁, h1, h2⟩ := AM.bind_ok h
  obtain ⟨rfl, rfl⟩ := AM.get_ok h1
  rw [AM.set_ok h2]

theorem A1Prog.view (k : EIdx) : A1Prog (Arena.view k) := by
  intro s s' a h
  obtain ⟨rfl, -⟩ := view_run h; rfl

theorem A1Prog.derivedE (k : EIdx) : A1Prog (Arena.derivedE k) := by
  intro s s' a h
  simp only [Arena.derivedE] at h
  obtain ⟨t, s₁, h1, h2⟩ := AM.bind_ok h
  obtain ⟨rfl, rfl⟩ := AM.get_ok h1
  obtain ⟨-, rfl⟩ := AM.pure_ok h2; rfl

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

end FvarB

/-- con-leche: ConLeche/Kernel/ExprOps.lean:1436-1441 fvarB — **`Abs.lean`'s
hypothesis, discharged for the Core tier**: `Ranges.lean`'s `fvarB_spec`
plus `FvarB.fvarB_a1`. -/
theorem fvarBSpec : ExprOps.FvarBSpec where
  run := fun fuel s₁ h hok hden => AM.triple_of_run (P := fun s => s = s₁) (by
    intro s a s' hs hr
    subst hs
    obtain ⟨h1, h2, h3, h4⟩ := AM.of_run (P := fun t => t = s) rfl hr
      (ExprOps.fvarB_spec fuel s h hok hden)
    exact ⟨h1, h2, h3, FvarB.fvarB_a1 fuel h s s' a hr, h4⟩)

/-! `fvarBSpec`: `[propext, Classical.choice, Quot.sound]` expected. -/
#print axioms fvarBSpec

end ConRon.Bridge.Core
