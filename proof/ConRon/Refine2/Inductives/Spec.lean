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

/-! ## The memoised walk's arm dispatch

(`mentionsConst`'s walk is proved in `Refine2/Checker/Leaves.lean`, which needs
no transcription.) -/

/-- `hasLooseBVarBGo`'s arm dispatch below the cutoff and the probe
(`Arena/Inductives/StructParts.lean:346-392`).  `has_loose_bvar_b_node` is the
Rust split; this is what it computes. -/
def hasLooseBVarBNodeSpec (memo : Std.HashMap (EIdx × Nat) Bool) (i fuel : Nat) :
    ENodeView → AM (Bool × Std.HashMap (EIdx × Nat) Bool)
  | .app f a => do
    match ← hasLooseBVarBGo memo i fuel f with
    | (true, memo) => pure (true, memo)
    | (false, memo) => hasLooseBVarBGo memo i fuel a
  | .lam ty b _ => do
    match ← hasLooseBVarBGo memo i fuel ty with
    | (true, memo) => pure (true, memo)
    | (false, memo) => hasLooseBVarBGo memo (i + 1) fuel b
  | .forallE ty b _ => do
    match ← hasLooseBVarBGo memo i fuel ty with
    | (true, memo) => pure (true, memo)
    | (false, memo) => hasLooseBVarBGo memo (i + 1) fuel b
  | .letE t v b => do
    match ← hasLooseBVarBGo memo i fuel t with
    | (true, memo) => pure (true, memo)
    | (false, memo) => do
      match ← hasLooseBVarBGo memo i fuel v with
      | (true, memo) => pure (true, memo)
      | (false, memo) => hasLooseBVarBGo memo (i + 1) fuel b
  | .proj _ _ sub => hasLooseBVarBGo memo i fuel sub
  | _ => pure (false, memo)

/-- The owed equation: `hasLooseBVarBGo` at `fuel + 1` IS the derived-word
cutoff, the five leaf arms, the probe, `hasLooseBVarBNodeSpec` at the view and
the insert. -/
theorem hasLooseBVarBGo_unfold (memo : Std.HashMap (EIdx × Nat) Bool) (i fuel : Nat)
    (h : EIdx) :
    hasLooseBVarBGo memo i (fuel + 1) h = (do
      if (← bvarB fuel h) ≤ i then pure (false, memo) else
      match ← view h with
      | .bvar j => pure (i == j, memo)
      | .fvar _ _ | .sort _ | .const _ _ | .lit _ => pure (false, memo)
      | v =>
        match memo[(h, i)]? with
        | some r => pure (r, memo)
        | none => do
          let r ← hasLooseBVarBNodeSpec memo i fuel v
          pure (hasLooseBVarBIns h i r)) := by
  rw [hasLooseBVarBGo]
  refine am_bind_congr _ ?_
  intro bb
  split
  · rfl
  refine am_bind_congr _ ?_
  intro v
  cases v <;> twin_reduce [hasLooseBVarBNodeSpec] <;>
    (first
      | rfl
      | (cases hm : memo[(h, i)]? with
         | some r => rfl
         | none => pair_peel))

/-! ## `structProjGuards`' two inner `let rec`s -/

/-- `structProjGuards`' `col` (`Arena/Inductives/StructParts.lean:426-451`):
field `i`'s guard, joined from the sorts of the earlier fields a later field
uses. -/
def structProjGuardsColSpec (used : List Bool) (sorts : List LIdx) (z : LIdx) :
    Nat → Nat → LIdx → AM LIdx
  | _, 0, acc => pure acc
  | j, k + 1, acc => do
    if used.getD j false then do
      let m ← internLNode (.max acc (sorts.getD j z))
      structProjGuardsColSpec used sorts z (j + 1) k m
    else structProjGuardsColSpec used sorts z (j + 1) k acc

/-- `structProjGuards`' `row`: one guard per field. -/
def structProjGuardsRowSpec (used : List Bool) (sorts : List LIdx) (z : LIdx) :
    Nat → Nat → AM (List LIdx)
  | _, 0 => pure []
  | i, k + 1 => do
    let g ← structProjGuardsColSpec used sorts z 0 i (sorts.getD i z)
    let rest ← structProjGuardsRowSpec used sorts z (i + 1) k
    pure (g :: rest)

/-- The owed equation: `structProjGuards` IS `zeroLevel`, the shared-memo
`structUsedLaterList`, and `row` from field `0`. -/
theorem structProjGuards_unfold (cty : EIdx) (nP nF : Nat) (sorts : List LIdx) :
    structProjGuards cty nP nF sorts = (do
      let z ← zeroLevel
      let used ← structUsedLaterList cty nP ∅ nF 0
      structProjGuardsRowSpec used sorts z 0 nF) := by
  have hcol : ∀ (used : List Bool) (z : LIdx) j k acc,
      structProjGuards.col sorts z used j k acc
        = structProjGuardsColSpec used sorts z j k acc := by
    intro used z j k
    induction k generalizing j with
    | zero => intro acc; rfl
    | succ k ih => intro acc; simp only [structProjGuards.col, structProjGuardsColSpec, ih]
  have hrow : ∀ (used : List Bool) (z : LIdx) i k,
      structProjGuards.row sorts z used i k = structProjGuardsRowSpec used sorts z i k := by
    intro used z i k
    induction k generalizing i with
    | zero => rfl
    | succ k ih => simp only [structProjGuards.row, structProjGuardsRowSpec, hcol, ih]
  simp only [structProjGuards, hrow]

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

/-- The projection-function name family, from field `j` on — the twin's
`(List.range nF).allM`, as the counted recursion DESIGN §3.4 asks for.  The
modeled route spells the same test at its own call site, and this
transcription is the subject of both Rust functions. -/
def projFnFamilyFreeSpec (fe : IFEnv) (T : NIdx) : Nat → Nat → AM Bool
  | 0, _ => pure true
  | k + 1, j => do
    let pn ← projFnName T j
    if (fe.find? pn).isNone then projFnFamilyFreeSpec fe T k (j + 1)
    else pure false

/-- `checkStructProjTable`'s tail: the name family and the table's own
reserved name must be free, and then the table is stored. -/
def checkStructProjTableNamesSpec (T C : NIdx) (lps : List NIdx) (nP nF : Nat)
    (resSort : LIdx) (guards : List LIdx) (off : Nat) (bodies : Array EIdx)
    (fe : IFEnv) : AM IFEnv := do
  unless ← projFnFamilyFreeSpec fe T nF 0 do
    fail (.invalid "projection name family taken")
  let tn ← projTableName T
  unless (fe.find? tn).isNone do
    fail (.invalid "projection table taken")
  pure (fe.push (.projInfo ⟨T, tn, lps, nP, C, nF, resSort, bodies, guards, off⟩))

/-- The owed equation: `checkStructProjTable` IS the bodies, their scoping and
`checkStructProjTableNamesSpec`. -/
theorem checkStructProjTable_unfold (T C : NIdx) (lps : List NIdx) (nP nF : Nat)
    (resSort : LIdx) (guards : List LIdx) (off : Nat) (cvCa : IConstantVal)
    (fe : IFEnv) :
    checkStructProjTable T C lps nP nF resSort guards off cvCa fe = (do
      let bodies ← unwrapOr (← structProjBodies T nP nF cvCa.type)
        (.internal "direct structure: projection bodies")
      let scopedOk ← projBodiesScopedSpec fe lps nP bodies.toList
      unless bodies.size = nF ∧ scopedOk do
        fail (.internal "direct structure: projection body scoping")
      checkStructProjTableNamesSpec T C lps nP nF resSort guards off bodies fe) := by
  have hall := list_allM_counted (fun b => do
      let w1 ← hasFvarFast coreWalkFuel b
      let w2 ← allLevelParamsDefined lps b
      let w3 ← constsResolveFFast fe b
      let w4 ← looseBVarsBoundedFast coreWalkFuel (nP + 1) b
      pure (!w1 && w2 && w3 && w4))
    (projBodiesScopedSpec fe lps nP) rfl
    (by intro a l; twin_reduce [projBodiesScopedSpec])
  have hfam := range_allM_counted (fun j => do
      let pn ← projFnName T j
      pure (fe.find? pn).isNone)
    (projFnFamilyFreeSpec fe T) (fun i => rfl)
    (by intro m i; twin_reduce [projFnFamilyFreeSpec])
  twin_reduce [checkStructProjTable, hall, checkStructProjTableNamesSpec,
    List.range_eq_range', hfam]

/-! # `arena::inductives::sum_install`

`checkSumCtor` is one twin `def` and four Rust functions: `check_sum_ctor`
(the constant check, the syntactic residual) and its three tails
`check_sum_ctor_frames`, `check_sum_ctor_resid`, `check_sum_ctor_sorts`, which
the twin's own comments name.  `fieldDomsResolve` / `idxArgsResolve` are twin
`def`s and need no transcription. -/

/-- `whnfTelescope` at `0` binders.  **Lean cannot generate the twin's
equation lemmas** (`whnfTelescope.eq_def` fails: "no progress at goal" on the
`match (← view e'), n` whose catch-all arms split on the counter), so `rw
[whnfTelescope]` is unavailable; these two equations are the definition read
off the structural recursion by `delta`, one per counter shape, each with the
Rust's own arm order (the view first, the counter second). -/
theorem whnfTelescope_zero (mode : ConLeche.CheckMode) (fe : IFEnv) (i : Nat) (e : EIdx) :
    whnfTelescope mode fe i 0 e = (do
      let e' ← whnf mode fe checkFuel i e
      match ← view e' with
      | .sort s => pure ([], s)
      | _ => fail (.invalid "direct sum: type former does not reduce to a sort")) := by
  delta whnfTelescope
  dsimp only [Nat.brecOn.go, whnfTelescope._f]
  refine congrArg (bind (whnf mode fe checkFuel i e)) (funext fun e' => ?_)
  refine congrArg (bind (view e')) (funext fun v => ?_)
  cases v <;> rfl

/-- `whnfTelescope` at `n + 1` binders (see `whnfTelescope_zero`). -/
theorem whnfTelescope_succ (mode : ConLeche.CheckMode) (fe : IFEnv) (i n : Nat) (e : EIdx) :
    whnfTelescope mode fe i (n + 1) e = (do
      let e' ← whnf mode fe checkFuel i e
      match ← view e' with
      | .forallE dom body bm => do
        let fv ← internE (.fvar i dom)
        let b ← instantiate1Fast coreWalkFuel body fv 0
        let (bs, s) ← whnfTelescope mode fe (i + 1) n b
        pure ((dom, bm) :: bs, s)
      | _ => fail (.invalid "direct sum: type former does not reduce to a telescope")) := by
  delta whnfTelescope
  dsimp only [Nat.brecOn.go, whnfTelescope._f]
  refine congrArg (bind (whnf mode fe checkFuel i e)) (funext fun e' => ?_)
  refine congrArg (bind (view e')) (funext fun v => ?_)
  cases v <;> rfl

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
    (resSort : LIdx) (isProp large : Bool) (nF : Nat) (cvCa : IConstantVal)
    (xFvs idxArgs : List EIdx) : AM (IConstantVal × List LIdx) := do
  unless ← fieldDomsResolve fe₀ xFvs do
    fail (.notImplemented "direct sum: field domain after the block")
  unless ← idxArgsResolve fe₀ idxArgs do
    fail (.invalid "direct sum: index expression mentions the block")
  let sorts ← checkStructFieldSortsI mode fe isProp large resSort nP xFvs idxArgs nF
  pure (cvCa, sorts)

/-- `checkSumCtor`'s residual stage (the Rust's `check_sum_ctor_resid`): the
opened residual is the family at the opened parameter variables followed by the
index expressions. -/
def checkSumCtorResidSpec (mode : ConLeche.CheckMode) (fe₀ fe : IFEnv) (T : NIdx)
    (lps : List NIdx) (nP nIdx : Nat) (resSort : LIdx) (isProp large : Bool)
    (nF : Nat) (cvCa : IConstantVal) (pFvs xFvs : List EIdx) (xrest : EIdx) :
    AM (IConstantVal × List LIdx) := do
  let us ← paramLevels lps
  let hd ← internE (.const T us)
  let xfn ← getAppFn coreWalkFuel xrest
  let xargs ← getAppArgs coreWalkFuel xrest
  unless xfn == hd && xargs.take nP == pFvs && xargs.length == nP + nIdx do
    fail (.notImplemented "direct sum: opened constructor residual")
  checkSumCtorSortsSpec mode fe₀ fe nP resSort isProp large nF cvCa xFvs
    (xargs.drop nP)

/-- `checkSumCtor`'s frame stage (the Rust's `check_sum_ctor_frames`): the
parameter pins against the type former's opened telescope, and the field
telescope opened. -/
def checkSumCtorFramesSpec (mode : ConLeche.CheckMode) (fe₀ fe : IFEnv) (T : NIdx)
    (lps : List NIdx) (nP nIdx : Nat) (resSort : LIdx) (isProp large : Bool)
    (nF : Nat) (cvTa cvCa : IConstantVal) : AM (IConstantVal × List LIdx) := do
  let cq ← unwrapOr (← openPisAtFvarsF nP cvCa.type 0)
    (.notImplemented "direct sum: constructor telescope")
  let tq ← unwrapOr (← openPisAtFvarsF nP cvTa.type 0)
    (.notImplemented "direct sum: type former telescope")
  let tdoms ← fvarTypeDs tq.1
  checkStructDomsAt mode fe 0 cq.1 tdoms nP
  let xq ← unwrapOr (← openPisAtFvarsF nF cq.2 nP)
    (.notImplemented "direct sum: constructor field telescope")
  checkSumCtorResidSpec mode fe₀ fe T lps nP nIdx resSort isProp large nF cvCa
    cq.1 xq.1 xq.2

/-- The owed equation: `checkSumCtor` IS the constant check, the syntactic
residual pin and `checkSumCtorFramesSpec`. -/
theorem checkSumCtor_unfold (mode : ConLeche.CheckMode) (fe₀ fe : IFEnv) (T : NIdx)
    (lps : List NIdx) (nP nIdx : Nat) (resSort : LIdx) (isProp large : Bool)
    (cvC : IConstantVal) (nF : Nat) (cvTa : IConstantVal) :
    checkSumCtor mode fe₀ fe T lps nP nIdx resSort isProp large cvC nF cvTa = (do
      let cvCa ← checkConstantVal mode fe cvC
      let (_, cbody) ← unwrapOr (← stripPis (nP + nF) cvCa.type)
        (.notImplemented "direct sum: constructor telescope")
      unless ← structCtorResidOk T lps nP nF nIdx cbody do
        fail (.invalid "direct sum: invalid constructor return type")
      checkSumCtorFramesSpec mode fe₀ fe T lps nP nIdx resSort isProp large nF
        cvTa cvCa) := by
  twin_reduce [checkSumCtor, checkSumCtorFramesSpec, checkSumCtorResidSpec,
    checkSumCtorSortsSpec]

/-! ## The axiom census -/

/-- info: 'ConRon.Refine2.paramLevels_unfold' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms paramLevels_unfold

/-- info: 'ConRon.Refine2.hasLooseBVarBGo_unfold' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms hasLooseBVarBGo_unfold

/-- info: 'ConRon.Refine2.checkSumCtor_unfold' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms checkSumCtor_unfold

end ConRon.Refine2
