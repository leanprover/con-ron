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

open Aeneas Aeneas.Std Result
open ConRon.Generated

namespace ConRon.Refine2

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

/-! ## `structShape`'s four pieces

The twin is one `do` block with three `if … then pure false else do`
boundaries; DESIGN §3.4 makes each of them a function, because the `rbs`
telescope is a loan that may not outlive a `match` arm. -/

/-- The motive binder's codomain (`Arena/Inductives/StructParts.lean:216-261`,
the `motiveOk` `let`).  The twin writes `structElimLevel`'s body inline; the
two are the same definition. -/
def structShapeMotiveSpec (T : NIdx) (lps : List NIdx) (elim : NIdx) (large : Bool)
    (nP : Nat) (rbs : List (EIdx × ConLeche.BinderMeta)) : AM Bool := do
  match rbs[nP]? with
  | some (mdom, _) => do
    match ← view mdom with
    | .forallE mmaj mcod _ => do
      match ← view mcod with
      | .sort s' => do
        let want ← structElimLevel elim large
        let fam0 ← structFam T lps nP 0
        pure (s' == want && mmaj == fam0)
      | _ => pure false
    | _ => pure false
  | _ => pure false

/-- The minor premise's body (the `minorOk` `let`). -/
def structShapeMinorSpec (C : NIdx) (lps : List NIdx) (nP nF : Nat)
    (rbs : List (EIdx × ConLeche.BinderMeta)) : AM Bool := do
  match rbs[nP + 1]? with
  | some (mindom, _) => do
    match ← stripPis nF mindom with
    | some (_, mbody) => do
      let hd ← internE (.bvar nF)
      let sp ← structCtorSpine C lps nP nF
      let want ← internE (.app hd sp)
      pure (mbody == want)
    | none => pure false
  | none => pure false

/-- The major premise's domain (the twin's last `match`). -/
def structShapeMajorSpec (T : NIdx) (lps : List NIdx) (nP : Nat)
    (rbs : List (EIdx × ConLeche.BinderMeta)) : AM Bool := do
  match rbs[nP + 2]? with
  | some (majdom, _) => do
    let fam2 ← structFam T lps nP 2
    pure (majdom == fam2)
  | none => pure false

/-- `structShape`'s body once the three telescopes are peeled and the type
former's residual is a sort. -/
def structShapeAtSpec (T C : NIdx) (lps : List NIdx) (elim : NIdx) (large : Bool)
    (nP nF : Nat) (cbody : EIdx) (rbs : List (EIdx × ConLeche.BinderMeta)) (rbody : EIdx) :
    AM Bool := do
  let fam ← structFam T lps nP nF
  let b2 ← internE (.bvar 2)
  let b0 ← internE (.bvar 0)
  let want ← internE (.app b2 b0)
  if !(cbody == fam && rbody == want) then pure false else do
  if !(← structShapeMotiveSpec T lps elim large nP rbs) then pure false else do
  if !(← structShapeMinorSpec C lps nP nF rbs) then pure false else
  structShapeMajorSpec T lps nP rbs

/-- The owed equation: `structShape` IS the three peels and
`structShapeAtSpec`. -/
theorem structShape_unfold (T C : NIdx) (lps : List NIdx) (elim : NIdx)
    (large : Bool) (nP nF : Nat) (tty cty rty : EIdx) :
    structShape T C lps elim large nP nF tty cty rty = (do
      match ← stripPis nP tty, ← stripPis (nP + nF) cty, ← stripPis (nP + 3) rty with
      | some (_, tbody), some (_, cbody), some (rbs, rbody) => do
        match ← view tbody with
        | .sort _ => structShapeAtSpec T C lps elim large nP nF cbody rbs rbody
        | _ => pure false
      | _, _, _ => pure false) := by
  rw [structShape]
  refine am_bind_congr _ ?_; intro a
  refine am_bind_congr _ ?_; intro b
  refine am_bind_congr _ ?_; intro c
  rcases a with _ | ⟨_, tbody⟩ <;> rcases b with _ | ⟨_, cbody⟩ <;>
    rcases c with _ | ⟨rbs, rbody⟩ <;> simp only [] <;> (try rfl)
  refine am_bind_congr _ ?_; intro v
  cases v <;> simp only [] <;> (try rfl)
  rw [structShapeAtSpec, structShapeMotiveSpec, structShapeMinorSpec,
    structShapeMajorSpec, structElimLevel]
  twin_reduce
  refine am_bind_congr _ ?_; intro fam
  refine am_bind_congr _ ?_; intro b2
  refine am_bind_congr _ ?_; intro b0
  refine am_bind_congr _ ?_; intro want
  refine if_congr Iff.rfl rfl ?_
  rcases rbs[nP]? with _ | ⟨mdom, mm⟩ <;> twin_reduce <;> try (simp; done)
  refine am_bind_congr _ ?_; intro v1
  cases v1 <;> twin_reduce <;> try (simp; done)
  refine am_bind_congr _ ?_; intro v2
  cases v2 <;> twin_reduce <;> try (simp; done)
  refine if_congr Iff.rfl ?_ ?_ <;>
    refine am_bind_congr _ ?_ <;> intro y <;>
    refine am_bind_congr _ ?_ <;> intro fam0 <;>
    refine if_congr Iff.rfl rfl ?_
  all_goals (
    rcases rbs[nP + 1]? with _ | ⟨mindom, mm2⟩ <;> twin_reduce <;> try (simp; done)
    refine am_bind_congr _ ?_; intro sp1
    rcases sp1 with _ | ⟨_, mbody⟩ <;> twin_reduce <;> try (simp; done)
    refine am_bind_congr _ ?_; intro hd
    refine am_bind_congr _ ?_; intro spn
    refine am_bind_congr _ ?_; intro w2
    try twin_reduce
    try rfl)

/-! ## `structPartsCore?`'s five pieces -/

/-- The exported rule's right-hand side is the generated one (the `rhsOk`
`let`). -/
def structPartsRhsOkSpec (nP nF : Nat) (rhs : EIdx) : AM Bool := do
  match ← stripLams (nP + 2 + nF) rhs with
  | some (_, rbody) => do
    let want ← structRuleBody nF
    pure (rbody == want)
  | none => pure false

/-- The small eliminator's arm: the recursor's level parameters ARE the
block's, and `structShape` holds at `.anonymous`. -/
def structPartsCoreSmallSpec (cvT cvC : IConstantVal) (nP nF : Nat)
    (cvR : IConstantVal) (rule : IRecRule) (s : LIdx) (isProp : Bool) :
    AM (Option StructParts) := do
  let anon ← internNNode .anonymous
  if cvR.levelParams == cvT.levelParams &&
      (← structShape cvT.name cvC.name cvT.levelParams anon false nP nF
        cvT.type cvC.type cvR.type) then
    pure (some ⟨cvT, cvC, nP, nF, cvR, anon, s, rule.rhs, false, isProp⟩)
  else pure none

/-- WHICH eliminator the recursor is: the large one carries a fresh level
parameter in front of the block's own and passes `structShape` at
`large := true`; else the small one. -/
def structPartsCoreElimSpec (cvT cvC : IConstantVal) (nP nF : Nat)
    (cvR : IConstantVal) (rule : IRecRule) (s : LIdx) (isProp : Bool) :
    AM (Option StructParts) := do
  match cvR.levelParams with
  | elim :: relps =>
    if relps == cvT.levelParams && !cvT.levelParams.contains elim &&
        (← structShape cvT.name cvC.name cvT.levelParams elim true nP nF
          cvT.type cvC.type cvR.type) then
      pure (some ⟨cvT, cvC, nP, nF, cvR, elim, s, rule.rhs, true, isProp⟩)
    else structPartsCoreSmallSpec cvT cvC nP nF cvR rule s isProp
  | [] => structPartsCoreSmallSpec cvT cvC nP nF cvR rule s isProp

/-- The result sort, read off the type former's residual, and the eliminator
split under it. -/
def structPartsCoreSortSpec (cvT cvC : IConstantVal) (nP nF : Nat)
    (cvR : IConstantVal) (rule : IRecRule) : AM (Option StructParts) := do
  match ← stripPis nP cvT.type with
  | some (_, tbody) => do
    match ← view tbody with
    | .sort s => do
      let z ← zeroLevel
      let isProp := (← lvlEq? s z) == some true
      structPartsCoreElimSpec cvT cvC nP nF cvR rule s isProp
    | _ => pure none
  | _ => pure none

/-- The recogniser's body once the block's three members are in hand: the name
and arity pins, then the result sort. -/
def structPartsCoreAtSpec (cvT cvC : IConstantVal) (nP nF : Nat)
    (cvR : IConstantVal) (mI rP : Nat) (rule : IRecRule) :
    AM (Option StructParts) := do
  let recName ← internNNode (.str cvT.name "rec")
  let reserved ← reservedBasisNames
  let rhsOk ← structPartsRhsOkSpec nP nF rule.rhs
  if cvR.name == recName && cvC.levelParams == cvT.levelParams &&
      reserved.contains cvT.name == false &&
      reserved.contains cvC.name == false &&
      reserved.contains cvR.name == false &&
      mI == nP + 2 && rP == nP + 2 &&
      rule.ctor == cvC.name && rule.nfields == nF && rhsOk then
    structPartsCoreSortSpec cvT cvC nP nF cvR rule
  else pure none

/-- The owed equation: `structPartsCore?` IS its block guard and
`structPartsCoreAtSpec`. -/
theorem structPartsCore_unfold (block : List IConstantInfo) :
    structPartsCore? block = (match block with
      | [.indInfo cvT _, .ctorInfo cvC nP nF, .recInfo cvR mI rP [rule]] =>
        structPartsCoreAtSpec cvT cvC nP nF cvR mI rP rule
      | _ => pure none) := by
  rw [structPartsCore?.eq_def]
  split
  case h_2 hx =>
    split
    · exact (hx _ _ _ _ _ _ _ _ _ rfl).elim
    · rfl
  case h_1 cvT caps cvC nP nF cvR mI rP rule =>
  show _ = structPartsCoreAtSpec cvT cvC nP nF cvR mI rP rule
  rw [structPartsCoreAtSpec, structPartsRhsOkSpec]
  twin_reduce
  refine am_bind_congr _ ?_; intro recName
  refine am_bind_congr _ ?_; intro reserved
  refine am_bind_congr _ ?_; intro sl
  rcases sl with _ | ⟨_, rbody⟩ <;> twin_reduce <;> try (simp; done)
  refine am_bind_congr _ ?_; intro want
  refine if_congr Iff.rfl ?_ rfl
  rw [structPartsCoreSortSpec]
  twin_reduce
  refine am_bind_congr _ ?_; intro sp
  rcases sp with _ | ⟨_, tbody⟩ <;> twin_reduce <;> try (simp; done)
  refine am_bind_congr _ ?_; intro vw
  cases vw <;> twin_reduce <;> try (simp; done)
  refine am_bind_congr _ ?_; intro z
  refine am_bind_congr _ ?_; intro le
  rw [structPartsCoreElimSpec.eq_def]
  rcases hlp : cvR.levelParams with _ | ⟨elim, relps⟩ <;> (try twin_reduce)
  case nil => rw [structPartsCoreSmallSpec, hlp]; try twin_reduce
  case cons =>
    refine am_bind_congr _ ?_; intro b
    refine if_congr Iff.rfl rfl ?_
    rw [structPartsCoreSmallSpec, hlp]
    try twin_reduce

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
  cases v <;> twin_reduce [mentionsConstNodeSpec] <;>
    (first
      | rfl
      | (cases hm : memo[h]? with
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
    (by intro m i; twin_reduce [projFnFamilyFreeSpec]
        try (refine am_bind_congr _ ?_
             intro pn
             cases (fe.find? pn).isNone <;> rfl))
  twin_reduce [checkStructProjTable, hall, checkStructProjTableNamesSpec,
    List.range_eq_range', hfam]

/-! # `arena::inductives::sum_install` -/

/-- `checkSumInd`'s tail past `checkSumTele`: the checked telescope's residual
sort, the completed record and the install. -/
def checkSumIndAtSpec (fe : IFEnv) (p : InductiveShape) (isRec : Bool)
    (cvTa : IConstantVal) (s : LIdx) :
    AM (IFEnv × IConstantVal × InductiveShape) := do
  let (_, tbody) ← unwrapOr (← stripPis (p.nP + p.nIdx) cvTa.type)
    (.internal "direct sum: type former telescope")
  let sortS ← internE (.sort s)
  unless tbody == sortS do
    fail (.internal "direct sum: type former result sort")
  let p' ← p.withSort s
  let caps ← nativeCapsAt p' isRec
  pure (fe.push (.indInfo cvTa caps), cvTa, p')

/-- The owed equation: `checkSumInd` IS the constant check, `checkSumTele`
and `checkSumIndAtSpec`. -/
theorem checkSumInd_unfold (mode : ConLeche.CheckMode) (fe : IFEnv) (p : InductiveShape)
    (isRec : Bool) :
    checkSumInd mode fe p isRec = (do
      let cvTa₀ ← checkConstantVal mode fe p.cvT
      let (cvTa, s) ← checkSumTele mode fe p.cvT (p.nP + p.nIdx) cvTa₀
      checkSumIndAtSpec fe p isRec cvTa s) := by
  rfl

/-- `checkStructFieldSortsI`'s per-field universe bound: official's `leq`
against the family's sort at a non-propositional family, and the large
eliminator's escape hatch (`Prop`-valued or an index argument) at a
propositional one. -/
def fieldSortBoundSpec (isProp large : Bool) (s u : LIdx) (fv : EIdx)
    (idxArgs : List EIdx) : AM Unit := do
  if !isProp then do
    let lu ← readLevel u
    let ls ← readLevel s
    unless ← liftFueled "level comparison" (ConLeche.Level.leq lu ls) do
      fail (.invalid "direct sum: field universe too large")
  else if large then do
    let z ← zeroLevel
    unless (← lvlEq? u z) == some true || idxArgs.contains fv do
      fail (.invalid "direct sum: large eliminator with a non-propositional \
        field outside the indices")

/-- `normPosDom`'s arm past the two `mentionsConst` tests and the whnf: the
Π-binder descent, or the residual itself. -/
def normPosDomAtSpec (mode : ConLeche.CheckMode) (fe : IFEnv) (T : NIdx) (d fuel : Nat)
    (w : EIdx) : AM EIdx := do
  match ← view w with
  | .forallE dom body bm => do
    if ← mentionsConst T dom then
      fail (.invalid "direct sum: non positive occurrence of the inductive type")
    else do
      let fv ← internE (.fvar d dom)
      let opened ← instantiate1Fast coreWalkFuel body fv 0
      let body' ← normPosDom mode fe T (d + 1) fuel opened
      let closed ← abstract1Fast coreWalkFuel body' d 0
      internE (.forallE dom closed bm)
  | _ => pure w

/-- The owed equation: `normPosDom` at `fuel + 1` IS the two occurrence tests,
the whnf and `normPosDomAtSpec`. -/
theorem normPosDom_unfold (mode : ConLeche.CheckMode) (fe : IFEnv) (T : NIdx) (d fuel : Nat)
    (e : EIdx) :
    normPosDom mode fe T d (fuel + 1) e = (do
      if !(← mentionsConst T e) then pure e else do
      let w ← whnf mode fe checkFuel d e
      if !(← mentionsConst T w) then pure w else
      normPosDomAtSpec mode fe T d fuel w) := by
  rfl

/-- `checkSumCtor`'s third stage: the field domains resolve at the PRE-BLOCK
environment. -/
def fieldDomsResolveSpec (fe₀ : IFEnv) : List EIdx → AM Bool
  | [] => pure true
  | x :: xs => do
    if ← constsResolveFFast fe₀ (← fvarTypeD x) then fieldDomsResolveSpec fe₀ xs
    else pure false

/-- `checkSumCtor`'s fourth stage: the index expressions never mention the
block. -/
def idxArgsResolveSpec (fe₀ : IFEnv) : List EIdx → AM Bool
  | [] => pure true
  | e :: es => do
    if ← constsResolveFFast fe₀ e then idxArgsResolveSpec fe₀ es else pure false

/-- `checkSumCtor`'s tail: the two resolutions and the fields' sorts. -/
def checkSumCtorSortsSpec (mode : ConLeche.CheckMode) (fe₀ fe : IFEnv) (nP : Nat)
    (resSort : LIdx) (isProp large : Bool) (nF : Nat) (cvCa : IConstantVal)
    (xFvs idxArgs : List EIdx) : AM (IConstantVal × List LIdx) := do
  unless ← fieldDomsResolveSpec fe₀ xFvs do
    fail (.notImplemented "direct sum: field domain after the block")
  unless ← idxArgsResolveSpec fe₀ idxArgs do
    fail (.invalid "direct sum: index expression mentions the block")
  let sorts ← checkStructFieldSortsI mode fe isProp large resSort nP xFvs idxArgs nF
  pure (cvCa, sorts)

/-- `checkSumCtor`'s residual stage: the opened residual is the family at the
opened parameter variables followed by the index expressions. -/
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

/-- `checkSumCtor`'s frame stage: the parameter pins against the type former's
opened telescope, and the field telescope opened. -/
def checkSumCtorFramesSpec (mode : ConLeche.CheckMode) (fe₀ fe : IFEnv) (T : NIdx)
    (lps : List NIdx) (nP nIdx : Nat) (resSort : LIdx) (isProp large : Bool)
    (nF : Nat) (cvTa cvCa : IConstantVal) : AM (IConstantVal × List LIdx) := do
  let cq ← unwrapOr (← openPisAtFvarsF nP cvCa.type 0)
    (.notImplemented "direct sum: constructor telescope")
  let tq ← unwrapOr (← openPisAtFvarsF nP cvTa.type 0)
    (.notImplemented "direct sum: type former telescope")
  checkStructDomsAt mode fe 0 cq.1 (← tq.1.mapM fvarTypeD) nP
  let xq ← unwrapOr (← openPisAtFvarsF nF cq.2 nP)
    (.notImplemented "direct sum: constructor field telescope")
  checkSumCtorResidSpec mode fe₀ fe T lps nP nIdx resSort isProp large nF cvCa
    cq.1 xq.1 xq.2

/-- The owed equation: `checkSumCtor` IS the constant check, the
normalisation, the residual pin and `checkSumCtorFramesSpec`. -/
theorem checkSumCtor_unfold (mode : ConLeche.CheckMode) (fe₀ fe : IFEnv) (T : NIdx)
    (lps : List NIdx) (nP nIdx : Nat) (resSort : LIdx) (isProp large : Bool)
    (cvC : IConstantVal) (nF : Nat) (cvTa : IConstantVal) :
    checkSumCtor mode fe₀ fe T lps nP nIdx resSort isProp large cvC nF cvTa = (do
      let cvCa₀ ← checkConstantVal mode fe cvC
      let cvCa ← normCtorVal mode fe T nP nF cvC cvCa₀
      let (_, cbody) ← unwrapOr (← stripPis (nP + nF) cvCa.type)
        (.notImplemented "direct sum: constructor telescope")
      unless ← structCtorResidOk T lps nP nF nIdx cbody do
        fail (.invalid "direct sum: invalid constructor return type")
      checkSumCtorFramesSpec mode fe₀ fe T lps nP nIdx resSort isProp large nF
        cvTa cvCa) := by
  have hdoms := list_allM_counted (fun x => do constsResolveFFast fe₀ (← fvarTypeD x))
    (fieldDomsResolveSpec fe₀) rfl (by intro a l; twin_reduce [fieldDomsResolveSpec])
  have hidx := list_allM_counted (fun e => constsResolveFFast fe₀ e)
    (idxArgsResolveSpec fe₀) rfl (by intro a l; twin_reduce [idxArgsResolveSpec])
  twin_reduce [checkSumCtor, checkSumCtorFramesSpec, checkSumCtorResidSpec,
    checkSumCtorSortsSpec, hdoms, hidx]

/-! # `arena::inductives::native_parts` -/

/-- `recFamOk`'s closing `allM`: no index expression mentions the block. -/
def idxFreeOfSpec (T : NIdx) : List EIdx → AM Bool
  | [] => pure true
  | a :: rest => do
    if ← mentionsConst T a then pure false else idxFreeOfSpec T rest

/-- `recPositivity`'s `_` arm: the residual is either free of the block, the
family at a fitting spine, or a negative/unsupported occurrence. -/
def recPositivityAtSpec (T : NIdx) (lps : List NIdx) (nP nIdx o : Nat) (h : EIdx)
    (k : Nat) : AM RecFieldKind := do
  if !(← mentionsConst T h) then pure .ordinary else do
  let us ← paramLevels lps
  let hd ← internE (.const T us)
  let fn ← getAppFn coreWalkFuel h
  let args ← getAppArgs coreWalkFuel h
  if fn == hd then do
    let ps ← structPsAt (o + k) nP
    if args.length == nP + nIdx && args.take nP == ps then
      if ← recFamOk T lps nP nIdx (o + k) h then
        pure (if k == 0 then .recursive else .reflexive)
      else pure .negative
    else pure .negative
  else
    match ← view fn with
    | .const T' _ => pure (if T' == T then .negative else .unsupported)
    | _ => pure .unsupported

/-- The owed equation: `recPositivity` at `fuel + 1` IS the Π descent and
`recPositivityAtSpec`. -/
theorem recPositivity_unfold (T : NIdx) (lps : List NIdx) (nP nIdx o fuel : Nat)
    (h : EIdx) (k : Nat) :
    recPositivity T lps nP nIdx o (fuel + 1) h k = (do
      match ← view h with
      | .forallE dom body _ => do
        if ← mentionsConst T dom then pure .negative
        else recPositivity T lps nP nIdx o fuel body (k + 1)
      | _ => recPositivityAtSpec T lps nP nIdx o h k) := by
  rfl

/-- `recCtorKinds`' per-field post-step: a recursive or reflexive field a LATER
binder mentions is marked unsupported. -/
def recCtorKindAtSpec (cty : EIdx) (nP i : Nat) (k : RecFieldKind) :
    AM RecFieldKind := do
  match k with
  | .recursive =>
    pure (if ← structUsedLater cty nP i then .unsupported else .recursive)
  | .reflexive =>
    pure (if ← structUsedLater cty nP i then .unsupported else .reflexive)
  | other => pure other

/-- `recCtorKinds`' `(List.range c.2).mapM`, from field `i` on. -/
def recCtorKindsFromSpec (T : NIdx) (lps : List NIdx) (nP nIdx : Nat) (cty : EIdx)
    (cbs : List (EIdx × ConLeche.BinderMeta)) : Nat → Nat → AM (List RecFieldKind)
  | 0, _ => pure []
  | m + 1, i => do
    let k0 ← recFieldKind T lps nP nIdx i (cbs.getD (nP + i) default).1
    let k ← recCtorKindAtSpec cty nP i k0
    let rest ← recCtorKindsFromSpec T lps nP nIdx cty cbs m (i + 1)
    pure (k :: rest)

/-- The owed equation: `recCtorKinds` IS the telescope peel, the per-field
walk and the residual test. -/
theorem recCtorKinds_unfold (T : NIdx) (lps : List NIdx) (nP nIdx : Nat)
    (c : IConstantVal × Nat) :
    recCtorKinds T lps nP nIdx c = (do
      match ← stripPis (nP + c.2) c.1.type with
      | some (cbs, cbody) => do
        let ks ← recCtorKindsFromSpec T lps nP nIdx c.1.type cbs c.2 0
        let cargs ← getAppArgs coreWalkFuel cbody
        let resOk ← idxFreeOfSpec T (cargs.drop nP)
        if resOk then pure (some ks)
        else pure (some (ks.map fun _ => .negative))
      | none => pure none) := by
  rw [recCtorKinds]
  refine am_bind_congr _ ?_; intro sp
  rcases sp with _ | ⟨cbs, cbody⟩ <;> (try twin_reduce)
  refine am_bind_congr₂ ?_ ?_
  · rw [List.range_eq_range']
    refine range_mapM_counted _
      (fun m i => recCtorKindsFromSpec T lps nP nIdx c.1.type cbs m i)
      (fun i => rfl) ?_ c.2 0
    intro m i
    rw [recCtorKindsFromSpec]
    twin_reduce
    refine am_bind_congr _ ?_; intro k0
    cases k0 <;> rw [recCtorKindAtSpec.eq_def]
  intro ks
  refine am_bind_congr _ ?_; intro cargs
  refine am_bind_congr₂ ?_ (fun _ => rfl)
  refine list_allM_counted _ (idxFreeOfSpec T) rfl ?_ _
  intro a l
  rw [idxFreeOfSpec]
  twin_reduce
  refine am_bind_congr _ ?_; intro b
  cases b <;> rfl

/-- `structTeleAt`'s `mapM` and `structIhApp`'s `idx.mapM`, from the `k`-th
element on: the field's index expressions moved to the rule frame. -/
def structIdxListSpec (nF o i l m : Nat) : List EIdx → AM (List EIdx)
  | [] => pure []
  | e :: es => do
    let a ← structIdxAt nF o i l m e
    let rest ← structIdxListSpec nF o i l m es
    pure (a :: rest)

/-- `structRuleBodyR`'s `recIdx.mapM`, from the `k`-th position on. -/
def structIhListSpec (recC : NIdx) (rlvls : LsIdx) (pw : ConLeche.PropWhen)
    (nP n nF : Nat) (cty : EIdx) : List Nat → AM (List EIdx)
  | [] => pure []
  | i :: is => do
    let a ← structIhApp recC rlvls pw nP n nF i (← structFieldTeleOf cty nP nF i)
      (← structFieldIdxOf cty nP nF i)
    let rest ← structIhListSpec recC rlvls pw nP n nF cty is
    pure (a :: rest)

/-- `structIhPis`' cons arm past its three reads. -/
def structIhPisAtSpec (nF o nP : Nat) (pw : ConLeche.PropWhen) (cty : EIdx)
    (is : List Nat) (l : Nat) (body : EIdx)
    (tele : List (EIdx × ConLeche.BinderMeta)) (idx' : List EIdx) (motive : EIdx)
    (i m : Nat) : AM EIdx := do
  let fvar ← internE (.bvar (nF - 1 - i + l + m))
  let fapp ← mkAppN fvar (← structTeleVars m)
  let concl ← mkAppN motive (idx' ++ [fapp])
  let dom ← mkPisOf (← structTeleAt nF o i l pw tele) concl
  let rest ← structIhPis nF o nP pw cty is (l + 1) body
  internE (.forallE dom rest ⟨pw⟩)

/-- `structMinorTyR`'s body past the two telescope peels. -/
def structMinorTyCloseSpec (nF o nP : Nat) (pw : ConLeche.PropWhen) (cty : EIdx)
    (recIdx : List Nat) (q2 concl0 : EIdx) : AM (Option EIdx) := do
  let concl ← liftLooseBVarsFast coreWalkFuel recIdx.length 0 concl0
  let inner ← structIhPis nF o nP pw cty recIdx 0 concl
  let lifted ← liftLooseBVarsFast coreWalkFuel o 0 q2
  replacePisPw pw nF lifted inner

/-- `structMinorTyR`'s conclusion stage. -/
def structMinorTyAtSpec (C : NIdx) (lps : List NIdx) (nP nF o : Nat)
    (pw : ConLeche.PropWhen) (cty : EIdx) (recIdx : List Nat) (q2 r2 : EIdx) :
    AM (Option EIdx) := do
  let motive ← internE (.bvar (nF + o - 1))
  let rargs ← getAppArgs coreWalkFuel r2
  let idx ← (rargs.drop nP).mapM fun e => liftLooseBVarsFast coreWalkFuel o nF e
  let spine ← structCtorSpineAt C lps o nP nF
  let concl0 ← mkAppN motive (idx ++ [spine])
  structMinorTyCloseSpec nF o nP pw cty recIdx q2 concl0

/-- `structMinorTyR`'s `(rargs.drop nP).mapM`, from the `i`-th element on. -/
def liftListSpec (amount c : Nat) : List EIdx → AM (List EIdx)
  | [] => pure []
  | e :: es => do
    let a ← liftLooseBVarsFast coreWalkFuel amount c e
    let rest ← liftListSpec amount c es
    pure (a :: rest)

/-- `structMinorsPisR` and `structMinorsLamsR` differ in ONE node; the port
writes them as one function at `isLam : bool` and interns inside each branch
(task #97-P4d-2's **extraction rule 7**).  This is that node. -/
def internBinderSpec (isLam : Bool) (ty body : EIdx) (pw : ConLeche.PropWhen) :
    AM EIdx :=
  if isLam then internE (.lam ty body ⟨pw⟩) else internE (.forallE ty body ⟨pw⟩)

/-- `structMinorsPisR` / `structMinorsLamsR` as ONE recursion at `isLam`, from
the `k`-th constructor on. -/
def structMinorsRSpec (lps : List NIdx) (nP : Nat) (pw : ConLeche.PropWhen) :
    List (NIdx × Nat × EIdx × List Nat) → Nat → EIdx → Bool → AM (Option EIdx)
  | [], _, body, _ => pure (some body)
  | (C, nF, cty, recIdx) :: cs, o, body, isLam => do
    match ← structMinorTyR C lps nP nF o pw cty recIdx with
    | none => pure none
    | some mty => do
      match ← structMinorsRSpec lps nP pw cs (o + 1) body isLam with
      | none => pure none
      | some rest => do pure (some (← internBinderSpec isLam mty rest pw))

/-- `structRecTyR`'s body past the motive type. -/
def structRecTyCloseSpec (lps : List NIdx) (nP nIdx : Nat) (tty : EIdx)
    (ctors : List (NIdx × Nat × EIdx × List Nat)) (pw : ConLeche.PropWhen) (n : Nat)
    (q2 motiveTy majorBody : EIdx) : AM (Option EIdx) := do
  let lifted ← liftLooseBVarsFast coreWalkFuel (n + 1) 0 q2
  match ← replacePisPw pw nIdx lifted majorBody with
  | none => pure none
  | some major => do
    match ← structMinorsPisR lps nP pw ctors 1 major with
    | none => pure none
    | some minors => do
      let body ← internE (.forallE motiveTy minors ⟨pw⟩)
      replacePisPw pw nP tty body

/-- `structRecTyR`'s major-premise stage. -/
def structRecTyAtSpec (T : NIdx) (lps : List NIdx) (nP nIdx : Nat) (tty : EIdx)
    (ctors : List (NIdx × Nat × EIdx × List Nat)) (pw : ConLeche.PropWhen) (n : Nat)
    (q2 motiveTy : EIdx) : AM (Option EIdx) := do
  let fam ← structFamI T lps nP nIdx (n + 1) 0
  let motiveVar ← internE (.bvar (nIdx + n + 1))
  let idxVars ← structPsAt 1 nIdx
  let b0 ← internE (.bvar 0)
  let concl ← mkAppN motiveVar (idxVars ++ [b0])
  let majorBody ← internE (.forallE fam concl ⟨pw⟩)
  structRecTyCloseSpec lps nP nIdx tty ctors pw n q2 motiveTy majorBody

/-- `structRecRhsR`'s body past the rule body. -/
def structRecRhsCloseSpec (lps : List NIdx) (nP : Nat) (tty : EIdx)
    (ctors : List (NIdx × Nat × EIdx × List Nat)) (pw : ConLeche.PropWhen)
    (n nF : Nat) (q2 body motiveTy : EIdx) : AM (Option EIdx) := do
  let lifted ← liftLooseBVarsFast coreWalkFuel (n + 1) 0 q2
  match ← pisToLamsPw pw nF lifted body with
  | none => pure none
  | some inner => do
    match ← structMinorsLamsR lps nP pw ctors 1 inner with
    | none => pure none
    | some minors => do
      let lam ← internE (.lam motiveTy minors ⟨pw⟩)
      pisToLamsPw pw nP tty lam

/-- `structRecRhsR`'s body past the `ctors[j]?` lookup. -/
def structRecRhsAtSpec (T : NIdx) (lps : List NIdx) (nP nIdx : Nat) (tty : EIdx)
    (ctors : List (NIdx × Nat × EIdx × List Nat)) (recC : NIdx) (rlvls : LsIdx)
    (j : Nat) (pw : ConLeche.PropWhen) (n nF : Nat) (cty : EIdx)
    (recIdx : List Nat) (l : LIdx) : AM (Option EIdx) := do
  match ← stripPis nP tty with
  | none => pure none
  | some (_, tq2) => do
    match ← structMotiveTyI T lps nP nIdx l tq2 with
    | none => pure none
    | some motiveTy => do
      match ← stripPis nP cty with
      | none => pure none
      | some (_, q2) => do
        let body ← structRuleBodyR recC rlvls pw nP n nF j recIdx cty
        structRecRhsCloseSpec lps nP tty ctors pw n nF q2 body motiveTy

/-- `nativeRulePrefixOk`'s prefix comparison, from the `i`-th binder on. -/
def bindersResetBeqSpec (bs₁ bs₂ : List (EIdx × ConLeche.BinderMeta)) (o₁ o₂ : Nat) :
    Nat → Nat → AM Bool
  | 0, _ => pure true
  | k + 1, i => do
    match bs₁[o₁ + i]?, bs₂[o₂ + i]? with
    | some b, some t => do
      if (← resetMetaFast coreWalkFuel b.1) == (← resetMetaFast coreWalkFuel t.1) then
        bindersResetBeqSpec bs₁ bs₂ o₁ o₂ k (i + 1)
      else pure false
    | _, _ => pure false

/-- `nativeRulePrefixOk`'s field comparison. -/
def nativeRuleFieldsOkSpec (nP n j nF : Nat)
    (rbs : List (EIdx × ConLeche.BinderMeta)) (mty : EIdx) : AM Bool := do
  let lifted ← liftLooseBVarsFast coreWalkFuel (n - j) 0 mty
  match ← stripPis nF lifted with
  | some (fbs, _) => bindersResetBeqSpec rbs fbs (nP + 1 + n) 0 nF 0
  | none => pure false

/-- `nativeRulesOk`'s per-rule body test. -/
def nativeRuleBodyOkSpec (recC : NIdx) (rlvls : LsIdx) (pw : ConLeche.PropWhen)
    (nP n nF j : Nat) (recIdx : List Nat) (cty rhs : EIdx) : AM Bool := do
  match ← stripLams (nP + 1 + n + nF) rhs with
  | some (_, rbody) => do
    let want ← structRuleBodyR recC rlvls pw nP n nF j recIdx cty
    pure (rbody == (← resetMetaFast coreWalkFuel want))
  | none => pure false

/-- `nativeRulesOk`'s `(List.range n).allM`, from rule `j` on. -/
def nativeRulesOkFromSpec (recC : NIdx) (rlvls : LsIdx) (pw : ConLeche.PropWhen)
    (nP n : Nat) (cs : List (IConstantVal × Nat)) (kinds : List (List RecFieldKind))
    (rhss : List EIdx) (recTy : EIdx) : Nat → Nat → AM Bool
  | 0, _ => pure true
  | m + 1, j => do
    match rhss[j]?, cs[j]?, kinds[j]? with
    | some rhs, some (cA, nF), some ks => do
      if !(ks.length == nF) then pure false else do
      if !(← nativeRuleBodyOkSpec recC rlvls pw nP n nF j (recIdxOf ks) cA.type rhs)
        then pure false else do
      if ← nativeRulePrefixOk recTy nP n j nF rhs then
        nativeRulesOkFromSpec recC rlvls pw nP n cs kinds rhss recTy m (j + 1)
      else pure false
    | _, _, _ => pure false

/-- `nativeRecPinOk`'s `(List.range …).all`, from rule `j` on. -/
def rulesPinOkSpec (rules : List IRecRule) (cs : List (IConstantVal × Nat × Nat)) :
    Nat → Nat → Bool
  | 0, _ => true
  | m + 1, j =>
    match rules[j]?, cs[j]? with
    | some rule, some (cvC, _, nF) =>
      rule.ctor == cvC.name && rule.nfields == nF && rulesPinOkSpec rules cs m (j + 1)
    | _, _ => false

/-- `nativeShape?`'s own `cs.all` pin. -/
def ctorsPinOkSpec (reserved : List NIdx) (cs : List (IConstantVal × Nat × Nat))
    (nP : Nat) (lps : List NIdx) : Bool :=
  cs.all fun c => c.2.1 == nP && c.1.levelParams == lps &&
    reserved.contains c.1.name == false

/-- `nativeShape?`'s small-eliminator arm. -/
def nativeShapeSmallSpec (cvT cvR : IConstantVal) (nP nIdx : Nat) (s : LIdx)
    (isProp : Bool) (ctors : List (IConstantVal × Nat)) (rhss : List EIdx) :
    AM (Option InductiveShape) := do
  let anon ← internNNode .anonymous
  pure (some ⟨cvT, ctors, nP, nIdx, cvR, anon, s, rhss, false, isProp⟩)

/-- `nativeShape?`'s eliminator split. -/
def nativeShapeElimSpec (cvT : IConstantVal) (cs : List (IConstantVal × Nat × Nat))
    (cvR : IConstantVal) (rules : List IRecRule) (nP nIdx : Nat) (s : LIdx) :
    AM (Option InductiveShape) := do
  let z ← zeroLevel
  let isProp := (← lvlEq? s z) == some true
  let ctors := cs.map fun c => (c.1, c.2.2)
  let rhss := rules.map (·.rhs)
  match cvR.levelParams with
  | elim :: relps =>
    if relps == cvT.levelParams && !cvT.levelParams.contains elim then
      pure (some ⟨cvT, ctors, nP, nIdx, cvR, elim, s, rhss, true, isProp⟩)
    else nativeShapeSmallSpec cvT cvR nP nIdx s isProp ctors rhss
  | [] => nativeShapeSmallSpec cvT cvR nP nIdx s isProp ctors rhss

/-- `nativeShape?`'s result-sort read: the declared type's residual when it is
a syntactic telescope ending in a sort, and a PLACEHOLDER (`zeroLevel`) the
install's whnf loop replaces otherwise (con-leche's task #195). -/
def nativeShapeSortSpec (cvT : IConstantVal) (cs : List (IConstantVal × Nat × Nat))
    (cvR : IConstantVal) (rules : List IRecRule) (nP nIdx : Nat) :
    AM (Option InductiveShape) := do
  let s ← match ← stripPis (nP + nIdx) cvT.type with
    | some (_, body) => do
      match ← view body with
      | .sort s => pure s
      | _ => zeroLevel
    | _ => zeroLevel
  nativeShapeElimSpec cvT cs cvR rules nP nIdx s

/-- `nativeShape?`'s body once the block's members are in hand. -/
def nativeShapeAtSpec (nPd : Nat) (cvT : IConstantVal)
    (cs : List (IConstantVal × Nat × Nat)) (cvR : IConstantVal) (mI rP : Nat)
    (rules : List IRecRule) : AM (Option InductiveShape) := do
  match ← nativeCounts? nPd cvT cs mI rP with
  | none => pure none
  | some (nP, nIdx) => do
    let reserved ← reservedBasisNames
    if reserved.contains cvT.name == false && reserved.contains cvR.name == false &&
        ctorsPinOkSpec reserved cs nP cvT.levelParams then
      nativeShapeSortSpec cvT cs cvR rules nP nIdx
    else pure none

/-- The owed equation: `nativeShape?` IS the block match, `sumSplit` and
`nativeShapeAtSpec`. -/
theorem nativeShape_unfold (nPd : Nat) (block : List IConstantInfo) :
    nativeShape? nPd block = (match block with
      | .indInfo cvT _ :: rest =>
        match sumSplit rest with
        | some (cs, cvR, mI, rP, rules) =>
          nativeShapeAtSpec nPd cvT cs cvR mI rP rules
        | none => pure none
      | _ => pure none) := by
  rw [nativeShape?.eq_def]
  rcases block with _ | ⟨ci, rest⟩
  · rfl
  · cases ci
    case indInfo cvT caps =>
      simp only []
      rcases hs : sumSplit rest with _ | ⟨cs, cvR, mI, rP, rules⟩
      · rfl
      · simp only []
        rw [nativeShapeAtSpec.eq_def]
        refine am_bind_congr _ ?_
        intro a
        cases a with
        | none => rfl
        | some q =>
          obtain ⟨nP, nIdx⟩ := q
          refine am_bind_congr _ ?_
          intro reserved
          simp only [ctorsPinOkSpec]
          split
          · rw [nativeShapeSortSpec.eq_def]
            have hK : ∀ (lvl : LIdx), (do
                let z ← zeroLevel
                let isProp := (← lvlEq? lvl z) == some true
                let ctors := cs.map fun c => (c.1, c.2.2)
                let rhss := rules.map (·.rhs)
                let large? : Option NIdx := match cvR.levelParams with
                  | elim :: relps =>
                    if relps == cvT.levelParams && !cvT.levelParams.contains elim then
                      some elim else none
                  | [] => none
                match large? with
                | some elim =>
                  pure (some ⟨cvT, ctors, nP, nIdx, cvR, elim, lvl, rhss, true, isProp⟩)
                | none => do
                  let anon ← internNNode .anonymous
                  pure (some ⟨cvT, ctors, nP, nIdx, cvR, anon, lvl, rhss, false, isProp⟩))
              = nativeShapeElimSpec cvT cs cvR rules nP nIdx lvl := by
              intro lvl
              rw [nativeShapeElimSpec.eq_def]
              refine am_bind_congr _ ?_
              intro z
              refine am_bind_congr _ ?_
              intro v
              rcases hl : cvR.levelParams with _ | ⟨elim, relps⟩
              · simp only []
                rw [nativeShapeSmallSpec.eq_def]
              · simp only []
                by_cases hc :
                    (relps == cvT.levelParams && !cvT.levelParams.contains elim) = true
                · rw [if_pos hc, if_pos hc]
                · rw [if_neg hc, if_neg hc, nativeShapeSmallSpec.eq_def]
            twin_reduce
            refine am_bind_congr _ ?_
            intro sp
            cases sp with
            | none =>
              twin_reduce
              refine am_bind_congr _ ?_
              intro lvl
              exact hK lvl
            | some pr =>
              obtain ⟨fst, body⟩ := pr
              twin_reduce
              refine am_bind_congr _ ?_
              intro v
              cases v <;> twin_reduce <;>
                first
                  | exact hK _
                  | (refine am_bind_congr _ ?_
                     intro lvl
                     exact hK lvl)
          · rfl
    all_goals rfl

/-! # `arena::inductives::native_install` -/

/-- `nativeRawRec`'s `anyM` over the declared field domains, from the cursor
on. -/
def anyDomMentionsSpec (T : NIdx) : List (EIdx × ConLeche.BinderMeta) → AM Bool
  | [] => pure false
  | b :: bs => do
    if ← mentionsConst T b.1 then pure true else anyDomMentionsSpec T bs

/-- `mentionsFvarGo`'s arm dispatch below the probe. -/
def mentionsFvarNodeSpec (q : Nat) (memo : Std.HashMap EIdx Bool) (fuel : Nat) :
    ENodeView → AM (Bool × Std.HashMap EIdx Bool)
  | .fvar idx ty =>
    if idx == q then pure (true, memo) else mentionsFvarGo q memo fuel ty
  | .app f a => do
    match ← mentionsFvarGo q memo fuel f with
    | (true, memo) => pure (true, memo)
    | (false, memo) => mentionsFvarGo q memo fuel a
  | .lam ty b _ => do
    match ← mentionsFvarGo q memo fuel ty with
    | (true, memo) => pure (true, memo)
    | (false, memo) => mentionsFvarGo q memo fuel b
  | .forallE ty b _ => do
    match ← mentionsFvarGo q memo fuel ty with
    | (true, memo) => pure (true, memo)
    | (false, memo) => mentionsFvarGo q memo fuel b
  | .letE t v b => do
    match ← mentionsFvarGo q memo fuel t with
    | (true, memo) => pure (true, memo)
    | (false, memo) => do
      match ← mentionsFvarGo q memo fuel v with
      | (true, memo) => pure (true, memo)
      | (false, memo) => mentionsFvarGo q memo fuel b
  | .proj _ _ sub => mentionsFvarGo q memo fuel sub
  | _ => pure (false, memo)

/-- The owed equation: `mentionsFvarGo` at `fuel + 1` IS the four leaf arms,
the probe, `mentionsFvarNodeSpec` at the view and the insert. -/
theorem mentionsFvarGo_unfold (q : Nat) (memo : Std.HashMap EIdx Bool) (fuel : Nat)
    (h : EIdx) :
    mentionsFvarGo q memo (fuel + 1) h = (do
      match ← view h with
      | .bvar _ | .sort _ | .const _ _ | .lit _ => pure (false, memo)
      | v =>
        match memo[h]? with
        | some r => pure (r, memo)
        | none => do
          let r ← mentionsFvarNodeSpec q memo fuel v
          pure (mentionsFvarIns h r)) := by
  rw [mentionsFvarGo]
  refine am_bind_congr _ ?_
  intro v
  cases v <;> twin_reduce [mentionsFvarNodeSpec] <;>
    (first
      | rfl
      | (cases hm : memo[h]? with
         | some r => rfl
         | none => pair_peel))

/-- `nativeOpenedOk`'s "no later field and not the residual" test. -/
def laterMentionsSpec (q : Nat) : List EIdx → AM Bool
  | [] => pure false
  | y :: ys => do
    if ← mentionsFvar q (← fvarTypeD y) then pure true else laterMentionsSpec q ys

/-- `nativeOpenedOk`'s per-field "unused later" clause. -/
def nativeFieldUnusedLaterSpec (nP : Nat) (xFvs : List EIdx) (xrest : EIdx)
    (i : Nat) : AM Bool := do
  if ← laterMentionsSpec (nP + i) (xFvs.drop (i + 1)) then pure false
  else pure !(← mentionsFvar (nP + i) xrest)

/-- `nativeOpenedOk`'s family-application test, shared by the recursive and
the reflexive arm. -/
def nativeFamAppOkSpec (fe₀ : IFEnv) (nP nIdx : Nat) (fvsP : List EIdx)
    (body hd : EIdx) : AM Bool := do
  let fn ← getAppFn coreWalkFuel body
  let args ← getAppArgs coreWalkFuel body
  if !(fn == hd && args.take nP == fvsP && args.length == nP + nIdx) then pure false
  else idxArgsResolveSpec fe₀ (args.drop nP)

/-- `nativeOpenedOk`'s `.recursive` arm. -/
def nativeFieldRecursiveSpec (fe₀ : IFEnv) (nP nIdx : Nat) (fvsP xFvs : List EIdx)
    (xrest hd : EIdx) (i : Nat) : AM Bool := do
  let x ← unwrapOr xFvs[i]? (.internal "direct rec: field index")
  let xt ← fvarTypeD x
  if ← nativeFamAppOkSpec fe₀ nP nIdx fvsP xt hd then
    nativeFieldUnusedLaterSpec nP xFvs xrest i
  else pure false

/-- `nativeOpenedOk`'s `.reflexive` arm: the field's own telescope, OPENED at
variables at the field's depth (con-leche's task #202). -/
def nativeFieldReflexiveSpec (fe₀ : IFEnv) (nP nIdx : Nat) (fvsP xFvs : List EIdx)
    (xrest hd : EIdx) (i : Nat) : AM Bool := do
  let x ← unwrapOr xFvs[i]? (.internal "direct rec: field index")
  let xt ← fvarTypeD x
  let (tele, _) ← piBinders coreWalkFuel xt
  match ← openPisAtFvarsF tele.length xt (nP + i) with
  | none => pure false
  | some (afvs, body) => do
    if afvs.length == 0 then pure false else do
    if !(← fieldDomsResolveSpec fe₀ afvs) then pure false else do
    if ← nativeFamAppOkSpec fe₀ nP nIdx fvsP body hd then
      nativeFieldUnusedLaterSpec nP xFvs xrest i
    else pure false

/-- `nativeOpenedOk`'s `(List.range nF).allM` from field `i` on. -/
def nativeFieldsAtSpec (fe₀ : IFEnv) (nP nIdx : Nat) (ks : List RecFieldKind)
    (fvsP xFvs : List EIdx) (xrest hd : EIdx) : Nat → Nat → AM Bool
  | 0, _ => pure true
  | m + 1, i => do
    let ok ← match ks.getD i .ordinary with
      | .ordinary => do constsResolveFFast fe₀ (← fvarTypeD (xFvs.getD i default))
      | .recursive => nativeFieldRecursiveSpec fe₀ nP nIdx fvsP xFvs xrest hd i
      | .reflexive => nativeFieldReflexiveSpec fe₀ nP nIdx fvsP xFvs xrest hd i
      | _ => pure false
    if ok then nativeFieldsAtSpec fe₀ nP nIdx ks fvsP xFvs xrest hd m (i + 1)
    else pure false

/-- The owed equation: `nativeOpenedOk` IS the two telescope opens, the
residual test and `nativeFieldsAtSpec`. -/
theorem nativeOpenedOk_unfold (fe₀ : IFEnv) (T : NIdx) (lps : List NIdx)
    (nP nIdx : Nat) (cty : EIdx) (nF : Nat) (ks : List RecFieldKind) :
    nativeOpenedOk fe₀ T lps nP nIdx cty nF ks = (do
      match ← openPisAtFvarsF nP cty 0 with
      | none => pure false
      | some (fvsP, crest) => do
        match ← openPisAtFvarsF nF crest nP with
        | none => pure false
        | some (xFvs, xrest) => do
          let us ← paramLevels lps
          let hd ← internE (.const T us)
          let xargs ← getAppArgs coreWalkFuel xrest
          if !(← idxArgsResolveSpec fe₀ (xargs.drop nP)) then pure false else
          nativeFieldsAtSpec fe₀ nP nIdx ks fvsP xFvs xrest hd nF 0) := by
  sorry

/-- `nativeFieldsOk`'s `(List.range …).allM` from constructor `j` on. -/
def nativeFieldsOkFromSpec (fe₀ : IFEnv) (T : NIdx) (lps : List NIdx)
    (nP nIdx : Nat) : List (IConstantVal × Nat) → List (List RecFieldKind) →
    AM Bool
  | [], _ => pure true
  | cA :: cs, ks :: kss => do
    if !(ks.length == cA.2) then pure false
    else if ← nativeOpenedOk fe₀ T lps nP nIdx cA.1.type cA.2 ks then
      nativeFieldsOkFromSpec fe₀ T lps nP nIdx cs kss
    else pure false
  | _ :: _, [] => pure false

/-- `checkNativeRules`' four-conjunct scoping test. -/
def nativeRuleScopedSpec (feR : IFEnv) (rlps : List NIdx) (rhs : EIdx) : AM Bool := do
  let w1 ← allLevelParamsDefined rlps rhs
  let w2 ← constsResolveFFast feR rhs
  let w3 ← looseBVarsBoundedFast coreWalkFuel 0 rhs
  let w4 ← hasFvarFast coreWalkFuel rhs
  pure (w1 && w2 && w3 && !w4)

/-- `checkNativeRec`'s rule stage: the rule-less recursor is pushed as a
BRACKET (task #97-P6-5's lever 4) and popped afterwards, so the port's `fe`
comes back unchanged — **finding 19**. -/
def checkNativeRecRulesSpec (p : NativeParts) (cvTa : IConstantVal)
    (ctors : List (NIdx × Nat × EIdx × List Nat)) (recTy : EIdx) (fe : IFEnv) :
    AM (IConstantVal × List EIdx) := do
  let cvRa : IConstantVal := ⟨p.cvR.name, p.cvR.levelParams, recTy⟩
  let feR := fe.push (.recInfo cvRa p.majorIdx p.rulePrefix [])
  let rlvls ← paramLevels p.cvR.levelParams
  let rhss ← checkNativeRules feR p.cvR.levelParams p.cvT.name p.cvT.levelParams
    p.elim p.large p.nP p.nIdx cvTa.type ctors p.cvR.name rlvls ctors.length 0
  pure (cvRa, rhss)

/-- `checkNativeRec`'s defeq stage. -/
def checkNativeRecDefeqSpec (mode : ConLeche.CheckMode) (fe : IFEnv)
    (p : NativeParts) (cvTa : IConstantVal)
    (ctors : List (NIdx × Nat × EIdx × List Nat)) (streamTy recTy : EIdx) :
    AM (IConstantVal × List EIdx) := do
  let sty ← inferTypeCore mode fe checkFuel 0 recTy
  let _u ← ensureSortCore mode fe checkFuel 0 sty
  unless ← isDefEqCore mode fe checkFuel 0 streamTy recTy do
    fail (.invalid "direct rec: recursor type is not the generated one")
  checkNativeRecRulesSpec p cvTa ctors recTy fe

/-- `checkNativeRec`'s type stage. -/
def checkNativeRecTySpec (mode : ConLeche.CheckMode) (fe : IFEnv) (p : NativeParts)
    (cvTa : IConstantVal) (ctorsA : List (IConstantVal × Nat)) (streamTy : EIdx) :
    AM (IConstantVal × List EIdx) := do
  let ctors := nativeCtors4 ctorsA p.kinds
  let recTy ← unwrapOr (← structRecTyR p.cvT.name p.cvT.levelParams p.elim p.large
      p.nP p.nIdx cvTa.type ctors)
    (.internal "direct rec: recursor type")
  unless ← nativeRuleScopedSpec fe p.cvR.levelParams recTy do
    fail (.internal "direct rec: recursor type scoping")
  checkNativeRecDefeqSpec mode fe p cvTa ctors streamTy recTy

/-- `recCtorKindsAll`'s cursor, from constructor `i` on. -/
def recCtorKindsAllSpec (T : NIdx) (lps : List NIdx) (nP nIdx : Nat) :
    List (IConstantVal × Nat) → AM (Option (List (List RecFieldKind)))
  | [] => pure (some [])
  | c :: cs => do
    match ← recCtorKinds T lps nP nIdx c with
    | none => pure none
    | some ks => do
      match ← recCtorKindsAllSpec T lps nP nIdx cs with
      | none => pure none
      | some rest => pure (some (ks :: rest))

/-- `checkNativePass`'s tail past the constructors' stage. -/
def checkNativePassKindsSpec (fe₁ : IFEnv) (cvTa : IConstantVal) (pC : NativeParts)
    (ctorsA : List (IConstantVal × Nat)) (sortss : List (List LIdx))
    (isRec : Bool) : AM (NativePass × Bool) := do
  let kinds ← classifyFixKinds pC.cvT.name pC.cvT.levelParams pC.nP pC.nIdx ctorsA
  let p := pC.withKinds kinds
  let settled := (← nativeCaps p) == (← nativeCapsAt pC.toInductiveShape isRec)
  pure (⟨fe₁, cvTa, p, ctorsA, sortss⟩, settled)

/-- `checkNativeTail`'s install stage. -/
def checkNativeTailInstallSpec (mode : ConLeche.CheckMode) (q : NativePass) :
    AM IFEnv := do
  let p := q.p
  let fe₂ := consSumCtors p.nP q.ctorsA q.env₁
  flushCaches
  let (cvRa, rhss) ← checkNativeRec mode fe₂ p q.cvTa q.ctorsA
  let rules ← sumRules fe₂ cvRa.name p.nP p.majorIdx p.rulePrefix cvRa.type
    q.ctorsA rhss
  checkNativeTable p q.ctorsA q.sortss
    (fe₂.push (.recInfo cvRa p.majorIdx p.rulePrefix rules))

/-- `checkNativeTail`'s kind stage. -/
def checkNativeTailKindsSpec (mode : ConLeche.CheckMode) (fe : IFEnv)
    (q : NativePass) : AM IFEnv := do
  let p := q.p
  unless ← nativeFieldsOk fe p.cvT.name p.cvT.levelParams p.nP p.nIdx q.ctorsA
      p.kinds do
    fail (.internal "direct rec: field kinds")
  let rlvls ← paramLevels p.cvR.levelParams
  unless ← nativeRulesOk p.cvR.name rlvls .never p.nP p.ctors.length q.ctorsA
      p.kinds p.rhss p.cvR.type do
    fail (.invalid "direct rec: recursor rules are not the generated ones")
  checkNativeTailInstallSpec mode q

/-- `checkNativeTail`'s index-sort stage. -/
def checkNativeTailSortsSpec (mode : ConLeche.CheckMode) (fe : IFEnv)
    (q : NativePass) : AM IFEnv := do
  let p := q.p
  let tq ← unwrapOr (← openPisAtFvarsF (p.nP + p.nIdx) q.cvTa.type 0)
    (.internal "direct rec: type former telescope")
  let _isorts ← checkStructFieldSortsI mode q.env₁ true false p.resSort p.nP
    (tq.1.drop p.nP) [] p.nIdx
  checkNativeTailKindsSpec mode fe q

/-- The owed equation: `checkNativeTail` IS the elimination restriction and
the three stages. -/
theorem checkNativeTail_unfold (mode : ConLeche.CheckMode) (fe : IFEnv)
    (q : NativePass) :
    checkNativeTail mode fe q = (do
      let neverZero := (← readLevel q.p.resSort).isNeverZero
      if q.p.large && !neverZero && decide (2 ≤ q.p.ctors.length) then
        fail (.invalid "direct rec: large eliminator on a multi-constructor \
          inductive whose sort may be Prop")
      else checkNativeTailSortsSpec mode fe q) := by
  rfl

/-! ## The axiom census

The twelve `_unfold`s this round closed read `[propext, Classical.choice,
Quot.sound]` and nothing else — no `sorryAx` on a closed equation.  Two rows
stand for the twelve: the cheapest family (a `let rec` induction) and the
dearest (a memoised walk under rule 11's peel). -/

/-- info: 'ConRon.Refine2.paramLevels_unfold' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms paramLevels_unfold

/-- info: 'ConRon.Refine2.hasLooseBVarBGo_unfold' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms hasLooseBVarBGo_unfold

/-- info: 'ConRon.Refine2.nativeShape_unfold' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms nativeShape_unfold

end ConRon.Refine2
