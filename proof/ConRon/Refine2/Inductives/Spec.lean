/-
# `ConRon.Refine2.Inductives.Spec` — the twin-side transcriptions of this tier

**Task #97-P5-Ind** (DESIGN.md §8.2); pruned by **task #105** to the three
modules of the old tier that survive the uniform inductive route
(`struct_parts`, `struct_install`, `sum_install`) — the transcriptions of the
deleted generators, recognisers and native/modeled checks went with their
Rust.  DESIGN §3.4's rules (no closure, no `let`-bound handle outliving a
`match` arm, every `List` operation a named cursor recursion) split a twin's
`do` block wherever it has a `let`-boundary.  A Rust function produced by such
a split has **no named twin**, so its statement has no subject until the
fragment is given one.

This file is that subject, once, for the whole tier — the arrangement task
#97-P5-Checker §9 asks for (*"one collected transcription file per tier, with
`_unfold` equations, and no edit to the twin"*) and which
`Refine2/Checker/Spec.lean` is at the declaration checker.  Two kinds of
declaration live here and nothing else:

* a **`…Spec`** definition: a fragment of a twin, transcribed.  It is a
  TRANSCRIPTION and not a claim — a reader checks it against
  `proof/ConRon/Arena/Inductives/*.lean` clause for clause, which is why they
  are collected rather than scattered across nine files;
* an **`…_unfold`** equation: *the named twin IS its transcription composed*.
  These ARE claims, they are the only obligations of this tier about the TWIN
  rather than about the port, and they are `rfl`-shaped — a `do`-block
  equation in `StateT σ (Except ε)` needs task #97-P5-Checker's rule 10
  reduction discipline.

**The inner recursions are transcribed too, and deliberately.**  Lean lifts a
`let rec go` inside a `def` to a real top-level name (`paramLevels.go`), so
`structPsAt.go` and `structProjGuards.col` could be named directly.  They are
not, because the lifted signature's leading parameters are *whatever the
elaborator captured, in whatever order it captured them* — a statement keyed
on that is keyed on an implementation detail of the twin's elaboration and
would move under a whitespace change.  A transcription with explicit arguments
is stable, and the `_unfold` equation is what ties it back.

Nothing under `Arena/` is edited to make any of this convenient, which is the
standing rule for a twin (DESIGN §8.4).
-/
import ConRon.Refine2.Inductives.Shape
import ConRon.Arena.Inductives.StructInstall
import ConRon.Arena.Inductives.SumInstall
import ConRon.Arena.WFProofs

open Aeneas Aeneas.Std Result
open ConRon.Generated

namespace ConRon.Refine2

open scoped ConRon.Refine2.IndSide

open ConRon.Arena

/-! # `arena::inductives::struct_parts` -/

/-! ## `paramLevels` and `structPsAt` — the two inner `let rec`s of the generators -/

/-- `paramLevels`' inner `go` (`Arena/Inductives/StructParts.lean:51-62`): one
`param` level node per name, in order. -/
def paramLevelsGoSpec : List NIdx → AM (List LIdx)
  | [] => pure []
  | n :: ns => do
    let u ← internLNode (.param n)
    let rest ← paramLevelsGoSpec ns
    pure (u :: rest)

/-- The owed equation: `paramLevels` IS its `go` interned. -/
theorem paramLevels_unfold (lps : List NIdx) :
    paramLevels lps = (do internLsNode (← paramLevelsGoSpec lps)) := by
  have hgo : ∀ ns, paramLevels.go ns = paramLevelsGoSpec ns := by
    intro ns; induction ns with
    | nil => rfl
    | cons n ns ih => simp only [paramLevels.go, paramLevelsGoSpec, ih]
  simp only [paramLevels, hgo]

/-- `structPsAt`'s inner `go` (`Arena/Inductives/StructParts.lean:66-77`): `n`
parameter variables from the `k`-th on, `p_k = bvar (o + nP - 1 - k)`. -/
def structPsAtGoSpec (o nP : Nat) : Nat → Nat → AM (List EIdx)
  | 0, _ => pure []
  | n + 1, k => do
    let b ← internE (.bvar (o + nP - 1 - k))
    let rest ← structPsAtGoSpec o nP n (k + 1)
    pure (b :: rest)

/-- The owed equation: `structPsAt o nP` IS its `go` at `(nP, 0)`. -/
theorem structPsAt_unfold (o nP : Nat) :
    structPsAt o nP = structPsAtGoSpec o nP nP 0 := by
  have hgo : ∀ n k, structPsAt.go o nP n k = structPsAtGoSpec o nP n k := by
    intro n; induction n with
    | zero => intro k; rfl
    | succ n ih => intro k; simp only [structPsAt.go, structPsAtGoSpec, ih]
  simp only [structPsAt, hgo]

/-! # `arena::inductives::struct_install` -/

/-- `checkStructProjTable`'s `scopedOk` `let`, from the cursor on: the bodies'
scoping, validated once at insertion.  **All four conjuncts run for every
body**, as the twin's `do` does; the walk stops at the first body that fails,
which is `List.allM`. -/
def projBodiesScopedSpec (fe : IFEnv) (lps : List NIdx) (nP : Nat) :
    List EIdx → AM Bool
  | [] => pure true
  | b :: bs => do
    let w1 ← hasFvarFast coreWalkFuel b
    let w2 ← allLevelParamsDefined lps b
    let w3 ← constsResolveFFast fe b
    let w4 ← looseBVarsBoundedFast coreWalkFuel (nP + 1) b
    if !w1 && w2 && w3 && w4 then projBodiesScopedSpec fe lps nP bs else pure false

/-- `checkStructProjTable`'s tail: the structure must be stored and its table
not yet taken. -/
def checkStructProjTableTailSpec (T : NIdx) (fe : IFEnv) : AM Unit := do
  unless (fe.find? T).isSome do
    fail (.internal "direct structure: projection table before its structure")
  unless (fe.findTable? T).isNone do
    fail (.invalid "projection table taken")

/-- The owed equation: `checkStructProjTable` IS the bodies, their scoping and
`checkStructProjTableTailSpec`. -/
theorem checkStructProjTable_unfold (T : NIdx) (lps : List NIdx) (nP nF : Nat)
    (cvCa : IConstantVal) (fe : IFEnv) :
    checkStructProjTable T lps nP nF cvCa fe = (do
      let bodies ← unwrapOr (← structProjBodies T nP nF cvCa.type)
        (.internal "direct structure: projection bodies")
      let scopedOk ← projBodiesScopedSpec fe lps nP bodies.toList
      unless bodies.size = nF ∧ scopedOk do
        fail (.internal "direct structure: projection body scoping")
      checkStructProjTableTailSpec T fe) := by
  have hall := list_allM_counted (fun b => do
      let w1 ← hasFvarFast coreWalkFuel b
      let w2 ← allLevelParamsDefined lps b
      let w3 ← constsResolveFFast fe b
      let w4 ← looseBVarsBoundedFast coreWalkFuel (nP + 1) b
      pure (!w1 && w2 && w3 && w4))
    (projBodiesScopedSpec fe lps nP) rfl
    (by intro a l; twin_reduce [projBodiesScopedSpec])
  twin_reduce [checkStructProjTable, hall, checkStructProjTableTailSpec]

/-! # `arena::inductives::sum_install`

`checkSumCtor` is one twin `def` and four Rust functions: `check_sum_ctor`
(the constant check, the syntactic residual) and its three tails
`check_sum_ctor_frames`, `check_sum_ctor_resid`, `check_sum_ctor_sorts`, which
the twin's own comments name.  `fieldDomsResolve` / `idxArgsResolve` are twin
`def`s and need no transcription. -/

/-- `checkStructFieldSortsI`'s per-field universe bound: official's `leq`
against the family's sort at a non-propositional family, and the large
eliminator's escape hatch (`Prop`-valued or an index argument) at a
propositional one. -/
def fieldSortBoundSpec (isProp large : Bool) (s u : LIdx) (fv : EIdx)
    (idxArgs : List EIdx) : AM Unit := do
  if !isProp then do
    let lu ← readLevelM u
    let ls ← readLevelM s
    unless ← liftFueled "level comparison" (ConLeche.Level.leq lu ls) do
      fail (.invalid "direct sum: field universe too large")
  else if large then do
    let z ← zeroLevel
    unless (← lvlEq? u z) == some true || idxArgs.contains fv do
      fail (.invalid "direct sum: large eliminator with a non-propositional \
        field outside the indices")

/-- `checkSumCtor`'s tail (the Rust's `check_sum_ctor_sorts`): the two
resolutions and the fields' sorts. -/
def checkSumCtorSortsSpec (mode : ConLeche.CheckMode) (fe₀ fe : IFEnv) (nP : Nat)
    (resSort : LIdx) (isProp large : Bool) (nF : Nat)
    (xFvs idxArgs : List EIdx) : AM Unit := do
  unless ← fieldDomsResolve fe₀ xFvs do
    fail (.notImplemented "direct sum: field domain after the block")
  unless ← idxArgsResolve fe₀ idxArgs do
    fail (.invalid "direct sum: index expression mentions the block")
  checkStructFieldSortsI mode fe isProp large resSort nP xFvs idxArgs nF

/-- `checkSumCtor`'s residual stage (the Rust's `check_sum_ctor_resid`): the
opened residual is the family at the opened parameter variables followed by the
index expressions. -/
def checkSumCtorResidSpec (mode : ConLeche.CheckMode) (fe₀ fe : IFEnv) (T : NIdx)
    (lps : List NIdx) (nP nIdx : Nat) (resSort : LIdx) (isProp large : Bool)
    (nF : Nat) (pFvs xFvs : List EIdx) (xrest : EIdx) : AM Unit := do
  let us ← paramLevels lps
  let hd ← internE (.const T us)
  let xfn ← getAppFn coreWalkFuel xrest
  let xargs ← getAppArgs coreWalkFuel xrest
  unless xfn == hd && xargs.take nP == pFvs && xargs.length == nP + nIdx do
    fail (.notImplemented "direct sum: opened constructor residual")
  checkSumCtorSortsSpec mode fe₀ fe nP resSort isProp large nF xFvs
    (xargs.drop nP)

/-- `checkSumCtor`'s frame stage (the Rust's `check_sum_ctor_frames`): the
parameter pins against the type former's opened telescope, and the field
telescope opened. -/
def checkSumCtorFramesSpec (mode : ConLeche.CheckMode) (fe₀ fe : IFEnv) (T : NIdx)
    (lps : List NIdx) (nP nIdx : Nat) (resSort : LIdx) (isProp large : Bool)
    (nF : Nat) (cvTa cvCa : IConstantVal) : AM Unit := do
  let cq ← unwrapOr (← openPisAtFvarsF nP cvCa.type 0)
    (.notImplemented "direct sum: constructor telescope")
  let tq ← unwrapOr (← openPisAtFvarsF nP cvTa.type 0)
    (.notImplemented "direct sum: type former telescope")
  let tdoms ← fvarTypeDs tq.1
  checkStructDomsAt mode fe 0 cq.1 tdoms nP
  let xq ← unwrapOr (← openPisAtFvarsF nF cq.2 nP)
    (.notImplemented "direct sum: constructor field telescope")
  checkSumCtorResidSpec mode fe₀ fe T lps nP nIdx resSort isProp large nF
    cq.1 xq.1 xq.2

/-- The owed equation: `checkSumCtor` IS the constant check, the syntactic
residual pin and `checkSumCtorFramesSpec`. -/
theorem checkSumCtor_unfold (mode : ConLeche.CheckMode) (fe₀ fe : IFEnv) (T : NIdx)
    (lps : List NIdx) (nP nIdx : Nat) (resSort : LIdx) (isProp large : Bool)
    (cvC : IConstantVal) (nF : Nat) (cvTa : IConstantVal) :
    checkSumCtor mode fe₀ fe T lps nP nIdx resSort isProp large cvC nF cvTa = (do
      checkConstantVal mode fe cvC false
      let (_, cbody) ← unwrapOr (← stripPis (nP + nF) cvC.type)
        (.notImplemented "direct sum: constructor telescope")
      unless ← structCtorResidOk T lps nP nF nIdx cbody do
        fail (.invalid "direct sum: invalid constructor return type")
      checkSumCtorFramesSpec mode fe₀ fe T lps nP nIdx resSort isProp large nF
        cvTa cvC) := by
  twin_reduce [checkSumCtor, checkSumCtorFramesSpec, checkSumCtorResidSpec,
    checkSumCtorSortsSpec]

/-! ## The axiom census -/

/-- info: 'ConRon.Refine2.paramLevels_unfold' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms paramLevels_unfold

/-- info: 'ConRon.Refine2.checkSumCtor_unfold' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms checkSumCtor_unfold

end ConRon.Refine2
