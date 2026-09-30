/-
# `ConRon.Refine.Fixpoint` — partial correctness for Aeneas `partial_fixpoint`s

Task #99-PFIX.  Every function Aeneas extracts is a `partial_fixpoint` over
`Result`, and Lean derives `<f>.fixpoint_induct` for each of them:

```
f.fixpoint_induct : ∀ (motive : (α → Result β) → Prop),
  Lean.Order.admissible motive → (∀ g, motive g → motive (fun x => body[g])) →
  motive f
```

What Lean does NOT derive for `Result` is `<f>.partial_correctness`: that form
is generated only when the fixpoint is taken in `Option`'s flat order (the
check is `isOptionFixpoint`, `Lean/Elab/PreDefinition/PartialFixpoint/
Induction.lean`), and its one ingredient is `Option.admissible_eq_some`.

`Result` is an interaction tree (`Aeneas/Std/Primitives.lean`: `ok` is `ret`,
`fail` is a `vis` with no continuation, `div` is `⊥`), so its order is not
flat — but below an `ok a` there are only `div` and `ok a` itself
(`ITree.le_unfold`).  That is all the `Option` proof uses, so the same lemma
holds: `Result.admissible_eq_ok` below.  Aeneas's own `dspec_admissible`
(`Aeneas/Std/WP.lean`) is the TOTAL-correctness-modulo-divergence variant —
it rules `fail` out — so it is the wrong shape for this project's statements,
which all say "if the Rust returns `ok o`, then …" and are silent on `fail`.

Every judgement of `Refine2/Tactic/Lockstep.lean` (`LS`, `LSR`, `LSV`, `LSW`,
`LSP`) and every `… = ok o → …` refinement lemma of `Refine/` is of that
shape, so each one, closed under `∀` over the function's arguments
(`admissible_pi`, `admissible_pi_apply`), is an admissible motive.
`ok_imp_admissible` does that closing for the common case, and the
`admissible_ok_imp` tactic proves the side goal `fixpoint_induct` leaves.
-/
import Aeneas

open Aeneas Aeneas.Std Result
open Lean.Order

namespace ConRon.Refine.Fixpoint

unseal Result in
/-- **The admissibility lemma**: `Result`'s analogue of
`Lean.Order.Option.admissible_eq_some`.  A chain whose supremum is `ok y`
contains `ok y` itself (every element lies below the supremum, and below
`ok y` there are only `div` and `ok y`; a chain of `div`s has supremum
`div`). -/
theorem admissible_eq_ok {α : Type} (P : Prop) (y : α) :
    admissible (fun (x : Result α) => x = ok y → P) := by
  intro c hchain h hsup
  by_cases hex : ∃ x, c x ∧ x ≠ div
  · obtain ⟨x, hcx, hx⟩ := hex
    have hle : x ⊑ CCPO.csup hchain := le_csup hchain hcx
    rw [hsup] at hle
    have hle' : @PartialOrder.rel (Aeneas.Data.Coinductive.ITree RustEffect α) _ x
        (Aeneas.Data.Coinductive.ITree.ret y) := hle
    rw [Aeneas.Data.Coinductive.ITree.le_unfold] at hle'
    rcases hle' with hdiv | ⟨r, hx1, hy⟩ | ⟨i, t1, t2, -, hv, -⟩
    · exact absurd hdiv hx
    · have : r = y := by simpa using hy.symm
      subst this
      exact h x hcx hx1
    · exact absurd hv (by simp)
  · have hall : ∀ x, c x → x ⊑ (div : Result α) := by
      intro x hcx
      have : x = div := by
        by_contra hne; exact hex ⟨x, hcx, hne⟩
      subst this; exact PartialOrder.rel_refl
    have hle := csup_le hchain hall
    have hdiv : CCPO.csup hchain = (div : Result α) :=
      Aeneas.Data.Coinductive.ITree.le_div_is_div _ hle
    rw [hsup] at hdiv
    exact absurd hdiv Aeneas.Data.Coinductive.not_ret_div

/-- The leaf of every motive: one function, applied to its (uncurried)
argument. -/
theorem admissible_apply_eq_ok {γ : Type} {α : Type} (a : γ) (P : Prop) (y : α) :
    admissible (fun (f : γ → Result α) => f a = ok y → P) :=
  admissible_apply (fun _ (x : Result α) => x = ok y → P) a (admissible_eq_ok P y)

/-- **The side goal `f.fixpoint_induct` leaves**, for a partial-correctness
motive `fun f => ∀ args…, hyps… → ∀ o, f args… = ok o → Q args… o`:
uncurry `f` (Aeneas's own `DspecInduction.curry_admissible`), peel every `∀`
and every hypothesis with `admissible_pi`, and close the leaf with
`admissible_apply_eq_ok`.  A motive stated through a definition whose body is
that shape (`LSR` and friends) wants the definition unfolded first. -/
macro "admissible_ok_imp" : tactic =>
  `(tactic| (
    (repeat' apply Aeneas.DspecInduction.curry_admissible)
    beta_reduce
    (repeat' (apply admissible_pi; intro))
    first
      | exact admissible_apply_eq_ok _ _ _
      | exact admissible_eq_ok _ _))

open Lean Elab Tactic Meta in
/-- **`partial_induct f`: the `partial_correctness` principle Lean does not
derive for `Result`, as a tactic.**  On a goal that mentions `f` (typically
`∀ args…, hyps… → ∀ o, f args… = ok o → Q …`, after `revert`), apply
`f.fixpoint_induct` with the goal itself as the motive — every application
of `f` abstracted — and close the admissibility side goal with
`admissible_ok_imp`.  What is left is the step: for an arbitrary `g`
satisfying the goal, the goal for `f`'s body at `g`.  The motive
construction is Aeneas's `dspec_induction`'s (`Aeneas/Tactic/Step/
DspecInduction.lean`), which does the same for `dspec` and splits `f`'s
arguments into the ones `fixpoint_induct` keeps fixed and the ones it
quantifies. -/
elab "partial_induct" func:ident : tactic => do
  let goal ← getMainGoal
  let goalTy ← instantiateMVars (← goal.getType)
  let fnName ← realizeGlobalConstNoOverloadWithInfo func
  let fiName := fnName ++ `fixpoint_induct
  executeReservedNameAction fiName
  let fi ← mkConstWithFreshMVarLevels fiName
  let fnParams ← forallTelescope (← inferType (← mkConstWithFreshMVarLevels fnName))
    fun xs _ => xs.mapM fun x => return (← x.fvarId!.getDecl).userName
  let fiParams ← forallTelescope (← inferType fi)
    fun xs _ => xs.mapM fun x => return (← x.fvarId!.getDecl).userName
  let fiParams := fiParams.extract 0 (fiParams.size - 3)
  let isConst := fnParams.map fun x => fiParams.contains x
  let some app := goalTy.find? (fun e => e.getAppFn.isConstOf fnName)
    | throwError "partial_induct: {fnName} does not occur in the goal"
  let args := app.getAppArgs
  let constArgs := (args.zip isConst).filterMap fun (x, b) => if b then some x else none
  let fiApp := mkAppN fi constArgs
  let fiTy ← whnf (← inferType fiApp)
  let .forallE _ motiveTy _ _ := fiTy | throwError "partial_induct: unexpected fixpoint_induct"
  let .forallE _ gTy _ _ := motiveTy | throwError "partial_induct: unexpected motive type"
  let motive ← withLocalDeclD `g gTy fun g => do
    let body := goalTy.replace fun e =>
      if e.getAppFn.isConstOf fnName then
        let eas := e.getAppArgs
        some (mkAppN g ((eas.zip isConst).filterMap fun (x, b) => if b then none else some x))
      else none
    mkLambdaFVars #[g] body
  let [gAdm, gStep] ← goal.apply (mkApp fiApp motive)
    | throwError "partial_induct: apply produced an unexpected number of goals"
  setGoals [gAdm]
  evalTactic (← `(tactic| admissible_ok_imp))
  unless (← getGoals).isEmpty do throwError "partial_induct: admissibility not closed"
  setGoals [gStep]

end ConRon.Refine.Fixpoint

/-! ## The two forms on a toy recursion: by hand, and by `partial_induct` -/

namespace ConRon.Refine.Fixpoint.Test
def tst (x y : Nat) : Result Nat :=
  if x = 0 then .ok y else tst (x - 1) (y + 1)
partial_fixpoint
example : ∀ x y o, tst x y = ok o → o = x + y := by
  apply tst.fixpoint_induct (motive := fun f => ∀ x y o, f x y = ok o → o = x + y)
  · admissible_ok_imp
  · intro g ih x y o h
    beta_reduce at h
    split at h
    · simp_all
    · have := ih _ _ _ h; omega
example : ∀ x y o, tst x y = ok o → o = x + y := by
  partial_induct tst
  intro g ih x y o h
  beta_reduce at h
  split at h
  · simp_all
  · have := ih _ _ _ h; omega
end ConRon.Refine.Fixpoint.Test
