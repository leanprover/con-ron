/-
# `ConRon.Refine2.Inductives.Spec` — the twin-side transcriptions of this tier

**Task #97-P5-Ind** (DESIGN.md §8.2).  `arena::inductives` is **306 `pub fn`s
against 152 twin `def`s** — DESIGN §3.4's rules (no closure, no `let`-bound
handle outliving a `match` arm, every `List` operation a named cursor
recursion) split a twin's `do` block wherever it has a `let`-boundary, and
task #97-P4d-2's own table calls this *"the densest use of the rule in the
port"*.  A Rust function produced by such a split has **no named twin**, so its
statement has no subject until the fragment is given one.

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

/-! ## The two memoised walks' arm dispatches -/

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

/-- `mentionsConstGo`'s arm dispatch below the probe
(`Arena/Inductives/StructParts.lean:482-523`). -/
def mentionsConstNodeSpec (T : NIdx) (memo : Std.HashMap EIdx Bool) (fuel : Nat) :
    ENodeView → AM (Bool × Std.HashMap EIdx Bool)
  | .fvar _ ty => mentionsConstGo T memo fuel ty
  | .app f a => do
    let (b₁, memo) ← mentionsConstGo T memo fuel f
    let (b₂, memo) ← mentionsConstGo T memo fuel a
    pure (b₁ || b₂, memo)
  | .lam ty body _ => do
    let (b₁, memo) ← mentionsConstGo T memo fuel ty
    let (b₂, memo) ← mentionsConstGo T memo fuel body
    pure (b₁ || b₂, memo)
  | .forallE ty body _ => do
    let (b₁, memo) ← mentionsConstGo T memo fuel ty
    let (b₂, memo) ← mentionsConstGo T memo fuel body
    pure (b₁ || b₂, memo)
  | .letE ty val body => do
    let (b₁, memo) ← mentionsConstGo T memo fuel ty
    let (b₂, memo) ← mentionsConstGo T memo fuel val
    let (b₃, memo) ← mentionsConstGo T memo fuel body
    pure (b₁ || b₂ || b₃, memo)
  | .proj s _ sub => do
    let (b, memo) ← mentionsConstGo T memo fuel sub
    pure (s == T || b, memo)
  | _ => pure (false, memo)

/-- The owed equation: `mentionsConstGo` at `fuel + 1` IS the four leaf arms,
the probe, `mentionsConstNodeSpec` at the view and the insert. -/
theorem mentionsConstGo_unfold (T : NIdx) (memo : Std.HashMap EIdx Bool) (fuel : Nat)
    (h : EIdx) :
    mentionsConstGo T memo (fuel + 1) h = (do
      match ← view h with
      | .bvar _ | .sort _ | .lit _ => pure (false, memo)
      | .const n _ => pure (n == T, memo)
      | v =>
        match memo[h]? with
        | some r => pure (r, memo)
        | none => do
          let (r, memo) ← mentionsConstNodeSpec T memo fuel v
          pure (r, memo.insert h r)) := by
  rw [mentionsConstGo]
  refine am_bind_congr _ ?_
  intro v
  cases v <;> twin_reduce [mentionsConstNodeSpec] <;> rfl

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

/-! ## The axiom census -/

/-- info: 'ConRon.Refine2.paramLevels_unfold' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms paramLevels_unfold

/-- info: 'ConRon.Refine2.hasLooseBVarBGo_unfold' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms hasLooseBVarBGo_unfold

end ConRon.Refine2
