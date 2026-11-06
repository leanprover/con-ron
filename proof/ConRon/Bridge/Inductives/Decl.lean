/-
# `ConRon.Bridge.Inductives.Decl` — the route, and `IndSpec`

`Bridge/Checker/Hyp.lean`'s `checkIndRoute` (the `.indDecl` arm of
`Arena/CheckDecl.lean` past the pin recogniser) against con-leche's `.indDecl`
arm of `ConLeche/Kernel/CheckDecl.lean:158-185`, and the theorem
`Bridge/Checker/Hyp.lean` names as `IndSpec`.

## The dispatch, clause for clause

Both sides are the same four lines (task #105: con-leche's uniform route): the
declared parameter count first, then ONE ROUTE chosen by the RECOGNISER alone —
the uniform install at a recognised block, the decline at any other.  So the
arm is three sub-statements composed —

    indParamsOk_spec      (below)
    blockShape?_spec      (Bridge/Inductives/BlockShape.lean)
    checkBlock_bridge     (Bridge/Inductives/BlockTail.lean)
    checkShapeless_ne_ok  (Bridge/Checker/Hyp.lean)

— and `checkDecl_ind_route` below is the pure side's own step lemma.

**Why the recogniser's statement is two-sided.**  `ROp` makes
`blockShape?_spec` say `none ↔ none`.  Without that the twin could decline
where con-leche installs (or the reverse) and Theorem 1 would be a statement
about a different program.

`IndOut` (`Bridge/Inductives/Rel.lean`) is `IndSpec.run`'s conclusion
clause for clause, so
`indSpec_of_bridge` is a record projection of `checkIndRoute_bridge`, at the
Core tier's discharged hypothesis (`CoreSpec.of_core`).
-/
module

import ConRon.Bridge.Inductives.BlockTail
import ConRon.Bridge.Inductives.BlockShape
public import ConRon.Bridge.Inductives.Rel
import ConRon.Bridge.EnvDenote
import ConLeche.Verify.Inductives.BlockShapeInv

public section

namespace ConRon.Bridge.Inductives

set_option autoImplicit false

open ConLeche ConRon.Arena ConRon.Bridge

/-! ## The declared parameter count -/

/-- con-leche: ConLeche/Kernel/Env.lean:614-621 indParamsOk — official's own
one-sided check, run before the dispatch and for both routes (con-leche's task
#228).  A `Bool` answer, so `RV` and no target store.

**Proof:** a list induction over
`piSortTeleLen?_spec` (`Bridge/Inductives/Rel.lean`, proved there on loan from
`Bridge/ExprOps/Spine.lean`) and `Frontend.denoteCI`'s case split — the
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
    simp only [ite_true] at hrun
    obtain ⟨hstep, hr⟩ := ih s s' r hok hcs hrun
    exact ⟨hstep, by rw [hr]; simp⟩
  | false =>
    simp only [Bool.false_eq_true, ite_false] at hrun
    obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun
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
    obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun
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
              obtain ⟨o, s₂, h3, h4⟩ := AM.bind_ok hrun
              obtain ⟨hstep1, ho⟩ :=
                piSortTeleLen?_spec Arena.coreWalkFuel cvT.type cvP.type s₀ s₂ o
                  hok (denoteCV_type hcv) h3
              have hcs₂ := denoteCIList_mono hstep1.ext _ _ hcs
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
        | thmInfo v =>
          simp only [Frontend.denoteCI, Option.map_eq_some_iff] at hc
          obtain ⟨cvP, _, rfl⟩ := hc
          have hrun' : (if (true : Bool) = true then Arena.indParamsOk nP rest
              else (pure false : AM Bool)) s₀ = .ok (r, s') := hrun
          obtain ⟨hstep, hr⟩ := indParamsOk_tail (ih xs) hok hcs hrun'
          refine ⟨hstep, ?_⟩
          rw [hr]
          simp only [ConLeche.indParamsOk, List.all_cons]
        | recInfo v mI rP k rs =>
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

/-- con-leche: ConLeche/Kernel/CheckDecl.lean:158-185 checkDecl (the
`.indDecl` arm) — at a block the basis recogniser refused and whose declared
parameter count checks out, `checkDecl` IS the recogniser's dispatch.  Stated
at `fueledOpsM .verified`, where the tier's answers live (`FOk`). -/
theorem checkDecl_ind_route {μ : CheckMode} {pins : List NatOpPinSet} {env : Env}
    {b : List ConstantInfo} {nP : Nat}
    (hpin : ConLeche.basisNameHit b = none)
    (hparams : ConLeche.indParamsOk nP b = true) :
    ConLeche.checkDecl μ (fueledOpsM μ) pins env (.indDecl b nP)
      = (match ConLeche.blockShape? nP b with
         | some p => ConLeche.checkBlock (fueledOpsM μ) env b p
         | none => ConLeche.checkShapeless (fueledOpsM μ) env b) := by
  simp only [ConLeche.checkDecl, hpin, hparams, ite_true]
  rfl

/-! ## The route -/

/-- con-leche: ConLeche/Kernel/CheckDecl.lean:158-185 checkDecl (the
`.indDecl` arm past `basisNameHit`) — **THEOREM 1 AT THE INDUCTIVE ROUTE**: an
accepting run of `Bridge/Checker/Hyp.lean`'s `checkIndRoute` at a block the
basis recogniser refused refines con-leche's `.indDecl` arm at some fuel.

Three sub-statements composed, as the arm composes them: the declared
parameter count (`indParamsOk_spec`), the recogniser (`blockShape?_spec`,
two-sided: `none ↔ none`, so the twin declines exactly where con-leche does),
then the uniform route (`checkBlock_bridge`, its members at their declared
formers by `blockShape?_declared`) or the decline (`checkShapeless_ne_ok`);
`checkDecl_ind_route` is the pure side's step. -/
theorem checkIndRoute_bridge {env : Env} {fe fe' : IFEnv}
    {s s' : AState} {block : List IConstantInfo} {b : List ConstantInfo}
    {nP : Nat} {pinsP : List NatOpPinSet}
    (hk : CoreSpec Arena.checkFuel)
    (hok : FoldOK env fe s)
    (hb : Frontend.denoteCIList s.store block = some b)
    (hpin : ConLeche.basisNameHit b = none)
    (hrun : checkIndRoute fe block nP s = .ok (fe', s')) :
    IndOut s s' (∃ env' F,
      ConLeche.checkDecl .verified (ConLeche.fueledOps .verified F) pinsP env (.indDecl b nP)
        = .ok env') := by
  simp only [checkIndRoute] at hrun
  -- the parameter-count gate
  obtain ⟨okb, s₁, h1, h2⟩ := AM.bind_ok hrun
  obtain ⟨hstep1, hr1⟩ := indParamsOk_spec nP block b s s₁ okb hok.check.state hb h1
  subst hr1
  cases hparams : ConLeche.indParamsOk nP b with
  | false => rw [hparams] at h2; exact absurd h2 (fun h => AM.fail_ok h)
  | true =>
  rw [hparams] at h2
  simp only [Bool.not_true, Bool.false_eq_true, ite_false] at h2
  -- the recogniser
  obtain ⟨o, s₂, h3, h4⟩ := AM.bind_ok h2
  have c1 := hstep1.toCore hok.check
  have hb₁ : Frontend.denoteCIList s₁.store block = some b :=
    denoteCIList_mono hstep1.ext _ _ hb
  obtain ⟨c2, hr2⟩ := blockShape?_spec fe nP block b s₁ s₂ o c1.ok hb₁ h3
  have hext12 : Ext s.store s₂.store := hstep1.ext.trans c2.ext
  have hpins12 : s₂.pins = s.pins := by rw [c2.pins, hstep1.pins]
  cases o with
  | none => exact absurd h4 checkShapeless_ne_ok
  | some p =>
  simp only [ROp] at hr2
  obtain ⟨q, hq, hrel⟩ := hr2
  have out := checkBlock_bridge hk c2.ok hok.envWF
    (EnvRel.ofCheck hok.check hok.gate hok.envWF |>.mono hext12)
    (denoteCIList_mono c2.ext _ _ hb₁) hrel (ConLeche.blockShape?_declared hq) h4
  obtain ⟨env', hF⟩ := out.run
  exact
    { state := out.state
      ext := hext12.trans out.ext
      pins := by rw [out.pins, hpins12]
      run := ⟨env', FOk.checkDecl (pins := pinsP) (by
        rw [checkDecl_ind_route hpin hparams, hq]; exact hF)⟩ }

/-! ## `IndSpec` -/

/-- con-leche: ConLeche/Kernel/CheckDecl.lean:158-185 checkDecl (the
`.indDecl` arm) — **`Bridge/Checker/Hyp.lean`'s `IndSpec`, discharged**: a
record projection of `checkIndRoute_bridge` (`IndOut`'s clauses are
`IndSpec.run`'s), the Core tier's hypothesis supplied by `CoreSpec.of_core`. -/
theorem indSpec_of_bridge : IndSpec := by
  refine ⟨fun {env fe fe' s s' block b nP pinsP} hok hb hpin hrun => ?_⟩
  have out := checkIndRoute_bridge (pinsP := pinsP) CoreSpec.of_core hok hb hpin hrun
  exact ⟨out.state, out.ext, out.pins, out.run⟩

end ConRon.Bridge.Inductives
