/-
# `ConRon.Bridge.Inductives.Decl` — the arm, and `IndSpec`

`Arena/Inductives.lean`'s `checkIndDecl` against con-leche's `.indDecl` arm of
`ConLeche/Kernel/Checker.lean:564-600`, and the theorem
`Bridge/Checker/Hyp.lean` names as `IndSpec`.

## The dispatch, clause for clause

Both sides are the same four lines: the declared parameter count first and for
BOTH routes (con-leche's task #228), then ONE ROUTE (its task #210) chosen by
the RECOGNISER alone (its task #219).  So the arm is three sub-statements
composed —

    indParamsOk_spec     (Bridge/Inductives/Decl.lean, below)
    nativeParts?_spec    (Bridge/Inductives/NativeParts.lean)
    checkNative_spec     (Bridge/Inductives/NativeInstall.lean)
    checkModeled_spec    (Bridge/Inductives/Modeled.lean)

— and `checkDecl_ind_route` below is the pure side's own step lemma in task
#97-P3-Core §5's shape (`rw` at con-leche's clause, one `simp only` with the
arm's own hypotheses).

**Why the recogniser's statement is two-sided.**  `ROp`
(`Bridge/Inductives/Rel.lean`) makes `nativeParts?_spec` say `none ↔ none`.
Without that the twin could take the modeled route where con-leche takes the
fixpoint one and Theorem 1 would be a statement about a different program.
This is the tier's only place where a one-sided refinement would be unsound,
and it is why the `Option` relation is what it is.

## FINDING — `IndSpec` as `Hyp.lean` states it cannot be discharged, and the
## two clauses that are wrong

`Bridge/Checker/Hyp.lean`'s `IndSpec.run` concludes

    StateOK s' ∧ Ext s.store s'.store ∧ s'.pins = s.pins ∧
      PersIFEnv fe' ∧ IFEnvCoh fe' ∧ fe.visibleBelow ≤ fe'.visibleBelow ∧ …

and two of those seven clauses are wrong for this arm.

1. **`PersIFEnv fe'` is FALSE.**  `Arena/Checker.lean`'s bracket is
   `flushCaches; enterScratch; <the step>; promoteNew; dropScratch`, so
   `checkDecl` — and therefore `checkIndDecl` — runs with the SCRATCH TIER
   OPEN, and every constant the route installs carries a freshly interned,
   hence scratch, type (`checkMemberVal` annotates; `checkNativeRec`
   fabricates the recursor).  Persistence is `promoteNew`'s job, one level up.
   `Bridge/Checker/Decl.lean`'s own `DeclOut` says this in prose — "There is
   **no persistence clause**: `checkDecl` does not promote […] Writing
   `PersIFEnv` into `DeclOut` would be stating a falsehood about the very
   deviation task #97-P6-2 introduced" — and `IndSpec` contradicts it.
2. **`Pushed fe fe'` is MISSING**, and `DeclOut` needs it: it is the clause
   that makes `checkDeclStep`'s promotion counter `k` mean "the constants this
   step installed".  Only the arm can supply it, so a hypothesis that omits it
   cannot discharge `checkDecl_bridge_ind`.

## Status: CLOSED of its own (task #97-P3-Ind round 2)

**No `sorry` in this module.**  `indParamsOk_spec` closed on
`piSortTeleLen?_spec`, so `checkIndDecl_bridge` then carried `sorryAx` through
exactly THREE sub-statements — `nativeParts?_spec` (the recogniser),
`checkNative_spec` and `checkModeled_spec` (the two routes) — and through
nothing of its own.  All three are closed since (task #97-P3-Ind rounds
3–9): the tier is `sorry`-free.  `IndOut` also gained an eighth clause this round,
`ProjOut`, which is what `Bridge/Checker/Inv.lean`'s `IFEnvOK_of_denote` needs
of the index the arm produced; `indSpec_of_bridge` drops it until
`Bridge/Checker/Hyp.lean`'s `IndSpec` asks for it.

`IndOut` (`Bridge/Inductives/Rel.lean`) is `IndSpec`'s conclusion with those
two corrected — `PersIFEnv` dropped, `Pushed` added — and `checkIndDecl_bridge`
below is proved at it.  **The correction has landed** (task #97-P3-Checker-2):
`Bridge/Checker/Hyp.lean`'s `IndSpec.run` is `IndOut`'s seven clauses, so
`indSpec_of_bridge` is a record projection and this module has no `sorry` that
is not an unproved sub-statement.
-/
import ConRon.Bridge.Inductives.Rel

namespace ConRon.Bridge.Inductives

set_option autoImplicit false

open ConLeche ConRon.Arena ConRon.Bridge

/-! ## The declared parameter count -/

/-- con-leche: ConLeche/Kernel/Env.lean:614-621 indParamsOk — official's own
one-sided check, run before the dispatch and for both routes (con-leche's task
#228).  A `Bool` answer, so `RV` and no target store.

**CLOSED** (task #97-P3-Ind round 2): a list induction over
`piSortTeleLen?_spec` (`Bridge/Inductives/Rel.lean`, proved there on loan from
`Bridge/ExprOps/TelescopeF.lean`) and `Frontend.denoteCI`'s case split — the
`.indInfo` and `.ctorInfo` arms are the only two that read anything, and the
other five answer `true` on both sides because the denotation does not change
a constant's constructor.

`indParamsOk_tail` is the shared continuation: the twin's `do` block pushes
the `if` INTO each match arm (so there is no outer `bind` to invert), and this
is that `if` with the recursive call, stated once. -/
theorem indParamsOk_tail {nP : Nat} {rest : List IConstantInfo}
    {xs : List ConstantInfo} {ok : Bool} {s s' : AState} {r : Bool}
    (ih : PSpec (fun st => Frontend.denoteCIList st rest = some xs)
      (Arena.indParamsOk nP rest) (RV (ConLeche.indParamsOk nP xs)))
    (hok : StateOK s) (hcs : Frontend.denoteCIList s.store rest = some xs)
    (hrun : (if ok = true then Arena.indParamsOk nP rest
      else (pure false : AM Bool)) s = .ok (r, s')) :
    PStep s s' ∧ r = (ok && ConLeche.indParamsOk nP xs) := by
  cases ok with
  | true =>
    simp only [if_true] at hrun
    obtain ⟨hstep, hr⟩ := ih s s' r hok hcs hrun
    exact ⟨hstep, by rw [hr]; simp⟩
  | false =>
    simp only [Bool.false_eq_true, if_false] at hrun
    obtain ⟨rfl, rfl⟩ := pureOk hrun
    exact ⟨PStep.refl hok, by simp⟩

theorem indParamsOk_spec (nP : Nat) (block : List IConstantInfo)
    (b : List ConstantInfo) :
    PSpec (fun st => Frontend.denoteCIList st block = some b)
      (Arena.indParamsOk nP block) (RV (ConLeche.indParamsOk nP b)) := by
  induction block generalizing b with
  | nil =>
    intro s₀ s' r hok hd hrun
    simp only [Frontend.denoteCIList, Option.some.injEq] at hd
    subst hd
    simp only [Arena.indParamsOk] at hrun
    obtain ⟨rfl, rfl⟩ := pureOk hrun
    exact ⟨PStep.refl hok, rfl⟩
  | cons ci rest ih =>
    intro s₀ s' r hok hd hrun
    simp only [Frontend.denoteCIList] at hd
    cases hc : Frontend.denoteCI s₀.store ci with
    | none => rw [hc] at hd; simp at hd
    | some x =>
      cases hcs : Frontend.denoteCIList s₀.store rest with
      | none => rw [hc, hcs] at hd; simp at hd
      | some xs =>
        rw [hc, hcs] at hd
        obtain rfl := Option.some.inj hd
        simp only [Arena.indParamsOk] at hrun
        cases ci with
        | indInfo cvT caps =>
          simp only [Frontend.denoteCI] at hc
          cases hcv : Frontend.denoteCV s₀.store cvT with
          | none => rw [hcv] at hc; simp at hc
          | some cvP =>
            cases hcp : Frontend.denoteCaps s₀.store caps with
            | none => rw [hcv, hcp] at hc; simp at hc
            | some capsP =>
              rw [hcv, hcp] at hc
              obtain rfl := Option.some.inj hc
              obtain ⟨o, s₂, h3, h4⟩ := bindOk hrun
              obtain ⟨hstep1, ho⟩ :=
                piSortTeleLen?_spec Arena.coreWalkFuel cvT.type cvP.type s₀ s₂ o
                  hok (denoteCV_type hcv) h3
              have hcs₂ := denoteCIList_ext hstep1.ext _ _ hcs
              cases o with
              | none =>
                have h4' : (if (true : Bool) = true then Arena.indParamsOk nP rest
                    else (pure false : AM Bool)) s₂ = .ok (r, s') := h4
                obtain ⟨hstep2, hr⟩ := indParamsOk_tail (ih xs) hstep1.ok hcs₂ h4'
                refine ⟨hstep1.trans hstep2, ?_⟩
                rw [hr]
                simp only [ConLeche.indParamsOk, List.all_cons, ← ho]
              | some n =>
                have h4' : (if (decide (nP ≤ n)) = true then Arena.indParamsOk nP rest
                    else (pure false : AM Bool)) s₂ = .ok (r, s') := h4
                obtain ⟨hstep2, hr⟩ := indParamsOk_tail (ih xs) hstep1.ok hcs₂ h4'
                refine ⟨hstep1.trans hstep2, ?_⟩
                rw [hr]
                simp only [ConLeche.indParamsOk, List.all_cons, ← ho]
        | ctorInfo cv nPc nF =>
          simp only [Frontend.denoteCI, Option.map_eq_some_iff] at hc
          obtain ⟨cvP, _, rfl⟩ := hc
          have hrun' : (if (nPc == nP) = true then Arena.indParamsOk nP rest
              else (pure false : AM Bool)) s₀ = .ok (r, s') := hrun
          obtain ⟨hstep, hr⟩ := indParamsOk_tail (ih xs) hok hcs hrun'
          refine ⟨hstep, ?_⟩
          rw [hr]
          simp only [ConLeche.indParamsOk, List.all_cons]
        | axiomInfo v =>
          simp only [Frontend.denoteCI, Option.map_eq_some_iff] at hc
          obtain ⟨cvP, _, rfl⟩ := hc
          have hrun' : (if (true : Bool) = true then Arena.indParamsOk nP rest
              else (pure false : AM Bool)) s₀ = .ok (r, s') := hrun
          obtain ⟨hstep, hr⟩ := indParamsOk_tail (ih xs) hok hcs hrun'
          refine ⟨hstep, ?_⟩
          rw [hr]
          simp only [ConLeche.indParamsOk, List.all_cons]
        | projInfo t =>
          simp only [Frontend.denoteCI, Option.map_eq_some_iff] at hc
          obtain ⟨pt, _, rfl⟩ := hc
          have hrun' : (if (true : Bool) = true then Arena.indParamsOk nP rest
              else (pure false : AM Bool)) s₀ = .ok (r, s') := hrun
          obtain ⟨hstep, hr⟩ := indParamsOk_tail (ih xs) hok hcs hrun'
          refine ⟨hstep, ?_⟩
          rw [hr]
          simp only [ConLeche.indParamsOk, List.all_cons]
        | defnInfo v e hint =>
          simp only [Frontend.denoteCI] at hc
          split at hc
          · obtain rfl := Option.some.inj hc
            have hrun' : (if (true : Bool) = true then Arena.indParamsOk nP rest
                else (pure false : AM Bool)) s₀ = .ok (r, s') := hrun
            obtain ⟨hstep, hr⟩ := indParamsOk_tail (ih xs) hok hcs hrun'
            refine ⟨hstep, ?_⟩
            rw [hr]
            simp only [ConLeche.indParamsOk, List.all_cons]
          · exact nomatch hc
        | thmInfo v e =>
          simp only [Frontend.denoteCI] at hc
          split at hc
          · obtain rfl := Option.some.inj hc
            have hrun' : (if (true : Bool) = true then Arena.indParamsOk nP rest
                else (pure false : AM Bool)) s₀ = .ok (r, s') := hrun
            obtain ⟨hstep, hr⟩ := indParamsOk_tail (ih xs) hok hcs hrun'
            refine ⟨hstep, ?_⟩
            rw [hr]
            simp only [ConLeche.indParamsOk, List.all_cons]
          · exact nomatch hc
        | recInfo v mI rP rs =>
          simp only [Frontend.denoteCI] at hc
          split at hc
          · obtain rfl := Option.some.inj hc
            have hrun' : (if (true : Bool) = true then Arena.indParamsOk nP rest
                else (pure false : AM Bool)) s₀ = .ok (r, s') := hrun
            obtain ⟨hstep, hr⟩ := indParamsOk_tail (ih xs) hok hcs hrun'
            refine ⟨hstep, ?_⟩
            rw [hr]
            simp only [ConLeche.indParamsOk, List.all_cons]
          · exact nomatch hc

/-! ## The pure side's step lemma -/

/-- con-leche: ConLeche/Kernel/CheckDecl.lean:180-200 checkDecl (the
`.indDecl` arm) — at a block the basis recogniser refused and whose declared
parameter count checks out, `checkDecl` IS the recogniser's dispatch.  Stated
at `fueledOpsM μ`, where the tier's answers live (`FOk`). -/
theorem checkDecl_ind_route {μ : CheckMode} {pins : List NatOpPinSet} {env : Env}
    {b : List ConstantInfo} {nP : Nat}
    (hpin : ConLeche.basisPinHit b = none)
    (hparams : ConLeche.indParamsOk nP b = true) :
    ConLeche.checkDecl μ (fueledOpsM μ) pins env (.indDecl b nP)
      = (match ConLeche.blockParts? nP b with
         | some p => ConLeche.checkBlock (fueledOpsM μ) env b p
         | none => ConLeche.checkShapeless (fueledOpsM μ) env b) := by
  simp only [ConLeche.checkDecl, hpin, hparams, if_true]
  rfl

end ConRon.Bridge.Inductives
