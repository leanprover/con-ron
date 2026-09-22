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

`IndOut` (`Bridge/Inductives/Rel.lean`) is `IndSpec`'s conclusion with those
two corrected — `PersIFEnv` dropped, `Pushed` added — and `checkIndDecl_bridge`
below is proved at it.  **The correction has landed** (task #97-P3-Checker-2):
`Bridge/Checker/Hyp.lean`'s `IndSpec.run` is `IndOut`'s seven clauses, so
`indSpec_of_bridge` is a record projection and this module has no `sorry` that
is not an unproved sub-statement.
-/
import ConRon.Bridge.Inductives.Modeled

namespace ConRon.Bridge.Inductives

set_option autoImplicit false

open ConLeche ConRon.Arena ConRon.Bridge

/-! ## The declared parameter count -/

/-- con-leche: ConLeche/Kernel/Env.lean:614-621 indParamsOk — official's own
one-sided check, run before the dispatch and for both routes (con-leche's task
#228).  A `Bool` answer, so `RV` and no target store.

`sorry`: a list induction over `piSortTeleLen?`'s spec
(`Bridge/ExprOps/TelescopeF.lean`) and `Frontend.denoteCI`'s case split — the
`.indInfo` and `.ctorInfo` arms are the only two that read anything. -/
theorem indParamsOk_spec (nP : Nat) (block : List IConstantInfo)
    (b : List ConstantInfo) :
    PSpec (fun st => Frontend.denoteCIList st block = some b)
      (Arena.indParamsOk nP block) (RV (ConLeche.indParamsOk nP b)) := by
  sorry

/-! ## The pure side's step lemma

Task #97-P3-Core §5's rule 8: one step lemma per CLAUSE of the pure function.
`checkDecl`'s `.indDecl` arm has three exits — the pinned block (not ours),
the parameter-count reject, and the route — and this is the third, which is
the only one `checkIndDecl` twins. -/

/-- con-leche: ConLeche/Kernel/Checker.lean:564-600 checkDecl (the `.indDecl`
arm) — at a block the basis recogniser refused and whose declared parameter
count checks out, `checkDecl` IS the route dispatch. -/
theorem checkDecl_ind_route {μ : CheckMode} {ops : CheckerOps CheckM}
    {pins : List NatOpPinSet} {env : Env} {b : List ConstantInfo} {nP : Nat}
    (hpin : ConLeche.basisPinHit b = none)
    (hparams : ConLeche.indParamsOk nP b = true) :
    ConLeche.checkDecl μ ops pins env (.indDecl b nP)
      = (match ConLeche.nativeParts? nP b with
         | some p => ConLeche.checkNative ops env p
         | none => ConLeche.checkModeled μ ops env b) := by
  simp only [ConLeche.checkDecl, hpin, hparams, if_true]
  rfl

/-! ## The arm -/

/-- con-leche: ConLeche/Kernel/Checker.lean:564-600 checkDecl (the `.indDecl`
arm) — **THEOREM 1 AT THE INDUCTIVE ROUTE**: an accepting run of
`Arena.Inductives.checkIndDecl` at a block the basis recogniser refused
refines con-leche's `.indDecl` arm at some fuel, with the state invariant, the
append, the untouched pin table and the environment's three clauses.

`sorry`: the composition itself is four `AM.bind_ok` inversions over
`indParamsOk_spec`, `nativeParts?_spec`, `checkNative_spec` and
`checkModeled_spec`, closed by `checkDecl_ind_route` above; what it waits on
is those four, each of which waits in turn on the tier's leaf walks and on
`Bridge/Checker/Base.lean`'s `checkConstantVal_bridge` (task #97-P3-Checker's
item 11).  **No new mathematics is in this step** — it is the same assembly
`Bridge/Checker/Fold.lean`'s `checkDecl_bridge` does over its seven arms. -/
theorem checkIndDecl_bridge {μ : CheckMode} {env : Env} {fe fe' : IFEnv}
    {s s' : AState} {block : List IConstantInfo} {b : List ConstantInfo}
    {nP : Nat} {pinsP : List NatOpPinSet}
    (_hμ : μ.verifiedChecks = true) (hk : CoreSpec μ Arena.checkFuel)
    (hok : FoldOK μ env fe s)
    (hb : Frontend.denoteCIList s.store block = some b)
    (hpin : ConLeche.basisPinHit b = none)
    (hrun : Arena.Inductives.checkIndDecl μ fe block nP s = .ok (fe', s')) :
    IndOut fe fe' s s' (fun env' => ∃ F,
      ConLeche.checkDecl μ (ConLeche.fueledOps μ F) pinsP env (.indDecl b nP)
        = .ok env') := by
  -- the parameter-count gate
  simp only [Arena.Inductives.checkIndDecl] at hrun
  obtain ⟨okb, s₁, h1, h2⟩ := bindOk hrun
  obtain ⟨hstep1, hr1⟩ := indParamsOk_spec nP block b s s₁ okb hok.check.state hb h1
  subst hr1
  cases hparams : ConLeche.indParamsOk nP b with
  | false => rw [hparams] at h2; exact nomatch h2
  | true =>
    rw [hparams] at h2
    simp only [if_true] at h2
    -- the recogniser
    obtain ⟨p, s₂, h3, h4⟩ := bindOk h2
    have hb₁ : Frontend.denoteCIList s₁.store block = some b :=
      denoteCIList_ext hstep1.ext _ _ hb
    obtain ⟨hstep2, hr2⟩ :=
      nativeParts?_spec nP block b s₁ s₂ p hstep1.ok hb₁ h3
    have hstep12 : PStep s s₂ := hstep1.trans hstep2
    have hck₂ : CheckOK μ env fe s₂ := (hstep12.toCore hok.check).ok
    have hfe₂ : denoteFEnv s₂.store fe = some env :=
      denoteFEnv_ext hstep12.ext hok.denote
    have hb₂ : Frontend.denoteCIList s₂.store block = some b :=
      denoteCIList_ext hstep2.ext _ _ hb₁
    -- the two routes
    cases p with
    | none =>
      simp only [ROp] at hr2
      obtain ⟨hcore, hinst⟩ :=
        checkModeled_spec fe hk block b s₂ s' fe' hck₂ ⟨hb₂, hfe₂⟩ h4
      obtain ⟨env', hden, F, hrunP⟩ := hinst.denote
      exact
        { state := hcore.ok.state
          ext := (hstep12.ext.trans hcore.ext)
          pins := by rw [hcore.pins, hstep12.pins]
          coh := hinst.coh
          pushed := hinst.pushed
          visible := hinst.visible
          denote := ⟨env', hden, F, by
            rw [checkDecl_ind_route hpin hparams, hr2]; exact hrunP⟩ }
    | some pa =>
      simp only [ROp] at hr2
      obtain ⟨q, hq, hrel⟩ := hr2
      obtain ⟨hcore, hinst⟩ :=
        checkNative_spec fe hk pa q s₂ s' fe' hck₂ ⟨hrel, hfe₂⟩ h4
      obtain ⟨env', hden, F, hrunP⟩ := hinst.denote
      exact
        { state := hcore.ok.state
          ext := (hstep12.ext.trans hcore.ext)
          pins := by rw [hcore.pins, hstep12.pins]
          coh := hinst.coh
          pushed := hinst.pushed
          visible := hinst.visible
          denote := ⟨env', hden, F, by
            rw [checkDecl_ind_route hpin hparams, hq]; exact hrunP⟩ }

/-! ## `IndSpec`, and the two clauses that stand between it and this arm -/

/-- con-leche: ConLeche/Kernel/Checker.lean:440-609 checkDecl (the `.indDecl`
arm) — **`Bridge/Checker/Hyp.lean`'s `IndSpec`, adapted from
`checkIndDecl_bridge`.**

All seven conjuncts are `IndOut`'s own (`state`, `ext`, `pins`, `coh`,
`pushed`, `visible`, `denote`) — which they were not when this module was
written: `IndSpec` then asked for `PersIFEnv fe'`, which is **false of this
arm** (the route runs inside the bracket with the scratch tier open, so the
constants it installs are scratch handles and persistence is `promoteNew`'s
business one level up) and did not ask for `Pushed fe fe'`, which the consumer
needs.  `Bridge/Checker/Decl.lean`'s `DeclOut` always said so in prose.

**DONE (task #97-P3-Checker-2).**  `Bridge/Checker/Hyp.lean`'s `IndSpec.run`
now drops `PersIFEnv fe'` and asks for `Pushed fe fe'` in its place, so the
seven conjuncts are `IndOut`'s seven and this theorem is a record projection
with no `sorry` of its own.  Its `sorryAx` is `checkIndDecl_bridge`'s four
sub-statements and nothing else. -/
theorem indSpec_of_bridge {μ : CheckMode} (hμ : μ.verifiedChecks = true)
    (hk : CoreSpec μ Arena.checkFuel) : IndSpec μ := by
  refine ⟨fun {env fe fe' s s' block b nP pinsP} hok hb hpin hrun => ?_⟩
  have out := checkIndDecl_bridge (pinsP := pinsP) hμ hk hok hb hpin hrun
  obtain ⟨env', hden, F, hrunP⟩ := out.denote
  exact ⟨out.state, out.ext, out.pins, out.coh, out.pushed, out.visible, env',
    F, hden, hrunP⟩

end ConRon.Bridge.Inductives
