/-
# `ConRon.Bridge.Inductives.SumParts` — Theorem 1 for the block's shape record

`Arena/Inductives/SumParts.lean` is two declarations, and they are the two
extremes of the tier.

* **`sumSplit` is not in `AM` at all** (task #97d-2's one deviation in this
  module: it matches on the members' CONSTRUCTORS and moves their fields, so
  the monad would buy nothing).  Its statement is therefore a plain
  implication between two `Option`s and not a `PSpec`, and it is the only
  such statement in the tier.
* **`InductiveShape.withSort` reads the pin table and the level cache**, so it
  is a `PSpec` like everything else.

## Why `sumSplit`'s statement is two-sided

`checkIndDecl`'s dispatch is the RECOGNISER alone (task #219): a block
`sumSplit` refuses goes to the modeled route and a block it accepts goes to
the fixpoint route.  So a twin that answered `none` where con-leche answers
`some` would take the OTHER route, and Theorem 1 would be about a different
program.  `ROp` (`Bridge/Inductives/Rel.lean`) is that two-sidedness, and it
is why the tier's `Option` relation is not a one-sided implication.

## Status: CLOSED (task #97-P3-Ind round 2)

**No `sorry` in this module**, and it is the tier's first file at zero.
`withSort_spec` moved from `PSpec` to `CSpec` on the way — round 2's finding,
argued in `Bridge/Inductives/Rel.lean`'s frame section: `lvlEq?` fills two of
the fourteen per-declaration cache tables.

**It STAYS at `CSpec` after task #97-P3-Frame**, which widened `PStep`'s cache
clause so that the FRAME is no longer what stands in the way
(`Core.lvlEq?_frame` is closed at `StateOK`).  The ANSWER is.  `withSort`'s
`isProp` field is `lvlEq?`'s verdict, `ShapeRel.isProp` is a conjunct of this
statement, and a `lvlEqC` hit answers `Level.isEquiv` only because
`LvlEqCacheOK` says so — an invariant `StateOK` does not carry.  At `PSpec`
this theorem would be FALSE of a poisoned cache.  `CSpec` is the grade the
answer lives at, not a weakening for convenience.
-/
import ConRon.Bridge.Inductives.StructParts

namespace ConRon.Bridge.Inductives

set_option autoImplicit false

open ConLeche ConRon.Arena ConRon.Bridge

/-! ## The member split -/

/-- con-leche: ConLeche/Kernel/Inductives/SumParts.lean:103-110 sumSplit — the
split's answer denotes: the constructors with their two counts, the recursor's
header, its two counts and its rules. -/
structure SplitRel
    (q : List (ConstantVal × Nat × Nat) × ConstantVal × Nat × Nat × List RecRule)
    (st : EStore)
    (r : List (IConstantVal × Nat × Nat) × IConstantVal × Nat × Nat × List IRecRule) :
    Prop where
  ctors : denoteCtors3 st r.1 = some q.1
  cvR : Frontend.denoteCV st r.2.1 = some q.2.1
  mI : r.2.2.1 = q.2.2.1
  rP : r.2.2.2.1 = q.2.2.2.1
  rules : Frontend.denoteRules st r.2.2.2.2 = some q.2.2.2.2

/-- con-leche: ConLeche/Kernel/Inductives/SumParts.lean:103-110 sumSplit — the
block's members after the type former.  **Two-sided** (`ROp`), because the
dispatch reads it.

**CLOSED** (task #97-P3-Ind round 2).  A structural induction on the block
with `Frontend.denoteCIList` inverted at the head; the seven-way case split on
the head's CONSTRUCTOR is what carries the two-sidedness, because
`Frontend.denoteCI` never changes a constant's constructor and both `sumSplit`
clauses dispatch on it.  The `.recInfo` arm splits once more on the tail: a
recursor closes the block only when nothing follows it, and a denoted tail is
empty exactly when the handle tail is. -/
theorem sumSplit_spec (st : EStore) (block : List IConstantInfo)
    (blockP : List ConstantInfo)
    (h : Frontend.denoteCIList st block = some blockP) :
    ROp SplitRel (ConLeche.sumSplit blockP) st (Arena.sumSplit block) := by
  induction block generalizing blockP with
  | nil =>
    simp only [Frontend.denoteCIList, Option.some.injEq] at h
    subst h
    rfl
  | cons c cs ih =>
    simp only [Frontend.denoteCIList] at h
    cases hc : Frontend.denoteCI st c with
    | none => rw [hc] at h; simp at h
    | some x =>
      cases hcs : Frontend.denoteCIList st cs with
      | none => rw [hc, hcs] at h; simp at h
      | some xs =>
        rw [hc, hcs] at h
        simp only [Option.some.injEq] at h
        subst h
        cases c with
        | axiomInfo v =>
          simp only [Frontend.denoteCI, Option.map_eq_some_iff] at hc
          obtain ⟨cv, _, rfl⟩ := hc
          rfl
        | defnInfo v e hint =>
          simp only [Frontend.denoteCI] at hc
          split at hc
          · rename_i cv y _ _
            obtain rfl := Option.some.inj hc
            rfl
          · exact nomatch hc
        | thmInfo v e =>
          simp only [Frontend.denoteCI] at hc
          split at hc
          · obtain rfl := Option.some.inj hc
            rfl
          · exact nomatch hc
        | indInfo v caps =>
          simp only [Frontend.denoteCI] at hc
          split at hc
          · obtain rfl := Option.some.inj hc
            rfl
          · exact nomatch hc
        | projInfo t =>
          simp only [Frontend.denoteCI, Option.map_eq_some_iff] at hc
          obtain ⟨pt, _, rfl⟩ := hc
          rfl
        | ctorInfo v nP nF =>
          simp only [Frontend.denoteCI, Option.map_eq_some_iff] at hc
          obtain ⟨cv, hcv, rfl⟩ := hc
          have harena : Arena.sumSplit (.ctorInfo v nP nF :: cs)
              = (Arena.sumSplit cs).map (fun q => ((v, nP, nF) :: q.1, q.2)) := rfl
          have hpure : ConLeche.sumSplit (.ctorInfo cv nP nF :: xs)
              = (ConLeche.sumSplit xs).map (fun q => ((cv, nP, nF) :: q.1, q.2)) := rfl
          rw [harena, hpure]
          have hih := ih xs hcs
          cases ha : Arena.sumSplit cs with
          | none =>
            rw [ha] at hih
            simp only [ROp] at hih
            simp only [hih, Option.map_none, ROp]
          | some a =>
            rw [ha] at hih
            obtain ⟨b, hb, hrel⟩ := hih
            rw [hb]
            exact ⟨_, rfl,
              { ctors := by simp only [denoteCtors3, hcv, hrel.ctors]
                cvR := hrel.cvR
                mI := hrel.mI
                rP := hrel.rP
                rules := hrel.rules }⟩
        | recInfo v mI rP rs =>
          simp only [Frontend.denoteCI] at hc
          cases hv : Frontend.denoteCV st v with
          | none => rw [hv] at hc; simp at hc
          | some cv =>
            cases hr : Frontend.denoteRules st rs with
            | none => rw [hv, hr] at hc; simp at hc
            | some rules =>
              rw [hv, hr] at hc
              obtain rfl := Option.some.inj hc
              cases cs with
              | nil =>
                simp only [Frontend.denoteCIList, Option.some.injEq] at hcs
                subst hcs
                exact ⟨_, rfl, ⟨rfl, hv, rfl, rfl, hr⟩⟩
              | cons c' cs' =>
                simp only [Frontend.denoteCIList] at hcs
                cases hc' : Frontend.denoteCI st c' with
                | none => rw [hc'] at hcs; simp at hcs
                | some x' =>
                  cases hcs' : Frontend.denoteCIList st cs' with
                  | none => rw [hc', hcs'] at hcs; simp at hcs
                  | some xs' =>
                    rw [hc', hcs'] at hcs
                    obtain rfl := Option.some.inj hcs
                    rfl

/-! ## The record completed with the former's sort -/

/-- con-leche: ConLeche/Kernel/Inductives/SumParts.lean:112-119 InductiveShape.withSort
The record completed with the result sort the former's install stage measured;
`isProp` is recomputed so the recogniser's invariant holds by definition.

**CORE grade, not pure** (task #97-P3-Ind round 2's finding; the argument is
in `Bridge/Inductives/Rel.lean`'s frame section).  Round 1 stated this at
`PSpec`, and `PSpec`'s frame says `s'.caches = s.caches` — which is FALSE of
this twin: `lvlEq?` probes and fills the level-equality cache and reads both
handles back through `readLevelM`, so two of the fourteen per-declaration
tables move.  `lvlEq?_spec` (`Bridge/Core/Walks/Cached.lean`, closed) is
stated at `CheckOK`/`CoreStep` for exactly that reason, and this statement now
matches it.  Its one caller, `checkSumInd`, is core grade already.

**CLOSED** (task #97-P3-Ind round 2): `pinZeroLevel_spec` and `lvlEq?_spec`
(both closed elsewhere), then the nine fields that do not move.  The one
content step is that the twin's verdict IS `Level.isEquiv sP .zero` — which is
`lvlEq?_spec` read as an EQUATION between `Option Bool`s rather than at its
`some true` half, task #97-P3-Core-2's strengthening, and what this module's
round-1 note asked for in the words "read at both signs".  The store does not
move at all (`lvlEq?` only fills caches), so there is no transport. -/
theorem withSort_spec {μ : CheckMode} {env : Env} (fe : IFEnv)
    (p : Arena.InductiveShape) (q : ConLeche.InductiveShape)
    (s : LIdx) (sP : Level) :
    CSpec μ env fe (fun st => ShapeRel st p q ∧ denoteL st.ls s = some sP)
      (Arena.InductiveShape.withSort p s)
      (RShape (ConLeche.InductiveShape.withSort q sP)) := by
  intro s₀ s' r hok hpre hrun
  obtain ⟨hrel, hs⟩ := hpre
  simp only [Arena.InductiveShape.withSort, Arena.zeroLevel] at hrun
  obtain ⟨z, s₁, h1, h2⟩ := bindOk hrun
  obtain ⟨hz1, hz2⟩ :=
    AM.of_run (P := fun t => t = s₀) rfl h1 (pinZeroLevel_spec s₀ hok.pins)
  rw [hz1] at h2
  obtain ⟨a, s₂, h3, h4⟩ := bindOk h2
  obtain ⟨hck, hst, hpin, lu, lv, hlu, hlv, ha⟩ :=
    AM.of_run (P := fun t => t = s₀) rfl h3 (Core.lvlEq?_spec s₀ s z hok)
  obtain ⟨hr1, hr2⟩ := pureOk h4
  subst hr1
  subst hr2
  -- the two levels the verdict is about ARE the result sort and `zero`
  obtain rfl : lu = sP := Option.some.inj (hlu.symm.trans hs)
  obtain rfl : lv = Level.zero := Option.some.inj (hlv.symm.trans hz2)
  refine ⟨⟨hck, by rw [hst]; exact Ext.refl _, hpin⟩, ?_⟩
  show ShapeRel _ _ _
  rw [hst]
  exact
    { cvT := hrel.cvT
      ctors := hrel.ctors
      nP := hrel.nP
      nIdx := hrel.nIdx
      cvR := hrel.cvR
      elim := hrel.elim
      resSort := hs
      rhss := hrel.rhss
      large := hrel.large
      isProp := by rw [ha]; rfl }

end ConRon.Bridge.Inductives
