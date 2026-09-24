/-
# `ConRon.Refine2.Frontend.SpecInd` — `validateIndD`'s loops, transcribed

**Task #97-T2-LOCKSTEP lane Frontend, ruling F12.**  `validateIndD`
(`Arena/Frontend/ExportC.lean`) is one `do` block with two `for`/`mut` loops,
each able to `return` a verdict from inside; the port writes each loop and
each loop body as its own function (`check_one_ctor`, `order_type_ctors`,
`order_block_ctors`, `check_rec_indices`, `check_one_rec`,
`check_rec_records`, and `k_expected_of` for the `is_K_target` match).

These are their twin sides, in `Refine2/Frontend/Spec.lean`'s pattern (one
transcription per port split, and an `_unfold` saying the twin IS their
composition), transcribed clause for clause — every guard and every `readName`
of a message, in the twin's order.  They keep the twin's own loop encoding:
a `for` loop IS `forIn` over the twin's `MProd (Option _) σ` state, and an
early `return v` out of a loop is `some v` in the state's first component, so
the `_unfold` is a statement about `do` blocks and not about loop semantics.
What the port's loop functions are stated against is exactly these `forIn`s.

`VRes` is `validateIndD`'s own result type; a check that fails carries
`some (.inl verdict)`, one that passes carries `none`.
-/
import ConRon.Refine2.Frontend.Spec

open Aeneas Aeneas.Std Result

namespace ConRon.Refine2.Frontend

open ConRon.Arena
open ConRon.Arena.Frontend
open ConLeche.Frontend (IndTypeRec IndCtorRec IndRecRec)

/-- `validateIndD`'s result type. -/
abbrev VRes := RecordVerdict ⊕ (List IndCtorRec × Nat)

/-- The first loop's body at one listed constructor `n` of type former `T`,
past the two index probes: the `cidx`, `induct` and `numFields` checks. -/
def checkOneCtorD (st : StateD) (fuel : Nat) (T n : NIdx) (c : IndCtorRec)
    (j nPd : Nat) : AM (Option VRes) := do
  if let some ci := c.cidx then
    unless ci == j do
      return some (.inl (.invalid s!"constructor {← readName n} declares cidx {ci}; it is \
        constructor {j} of {← readName T}"))
  if let some iw := c.induct then
    let iwn ← st.name iw
    unless iwn == T do
      return some (.inl (.invalid s!"constructor {← readName n} declares induct \
        {← readName iwn}; it is a constructor of {← readName T}"))
  let cty ← getDeclD st c.cv.type
  let tele ← indPiTeleLen fuel cty
  unless nPd + c.numFields == tele do
    return some (.inl (.invalid s!"constructor {← readName n} declares {c.numFields} \
      fields at {nPd} parameters; its type has {tele} binders"))
  pure none

/-- One step of the first loop's inner `for n in ns`: the two index probes,
the three checks, the push — the twin's loop body as it stands, so that
`validateIndD_unfold` is definitional.  `orderCtorStepD_eq` splits it at
`checkOneCtorD`. -/
def orderCtorStepD (st : StateD) (fuel : Nat) (T : NIdx)
    (ctorIx : Std.HashMap NIdx Nat) (ctsA : Array IndCtorRec) (nPd : Nat)
    (n : NIdx) (j : Nat) (ordered : Array IndCtorRec) :
    AM (ForInStep (MProd (Option VRes) (MProd Nat (Array IndCtorRec)))) := do
  let some k := ctorIx[n]? | return .done ⟨some (.inl (.invalid
    s!"No such constructor {← readName n}")), j, ordered⟩
  let some c := ctsA[k]? | return .done ⟨some (.inl (.invalid
    s!"No such constructor {← readName n}")), j, ordered⟩
  if let some ci := c.cidx then
    unless ci == j do
      return .done ⟨some (.inl (.invalid s!"constructor {← readName n} declares cidx {ci}; \
        it is constructor {j} of {← readName T}")), j, ordered⟩
  if let some iw := c.induct then
    let iwn ← st.name iw
    unless iwn == T do
      return .done ⟨some (.inl (.invalid s!"constructor {← readName n} declares induct \
        {← readName iwn}; it is a constructor of {← readName T}")), j, ordered⟩
  let cty ← getDeclD st c.cv.type
  let tele ← indPiTeleLen fuel cty
  unless nPd + c.numFields == tele do
    return .done ⟨some (.inl (.invalid s!"constructor {← readName n} declares \
      {c.numFields} fields at {nPd} parameters; its type has {tele} binders")), j, ordered⟩
  pure (.yield ⟨none, j + 1, ordered.push c⟩)

/-- The first loop's inner `for n in ns`, at one type former `T`, from
constructor position `j` onto `out`. -/
def orderTypeCtorsD (st : StateD) (fuel : Nat) (T : NIdx)
    (ctorIx : Std.HashMap NIdx Nat) (ctsA : Array IndCtorRec) (nPd : Nat)
    (ns : List NIdx) (j : Nat) (out : Array IndCtorRec) :
    AM (MProd (Option VRes) (MProd Nat (Array IndCtorRec))) :=
  forIn ns ⟨none, j, out⟩ fun n r => orderCtorStepD st fuel T ctorIx ctsA nPd n r.2.1 r.2.2

/-- One step of the first loop, at one `(T, ns)`. -/
def orderBlockStepD (st : StateD) (fuel : Nat) (ctorIx : Std.HashMap NIdx Nat)
    (ctsA : Array IndCtorRec) (nPd : Nat) (tn : NIdx × List NIdx) (out : Array IndCtorRec) :
    AM (ForInStep (MProd (Option VRes) (Array IndCtorRec))) :=
  match tn with
  | (T, ns) => do
    let r ← orderTypeCtorsD st fuel T ctorIx ctsA nPd ns 0 out
    match r.2 with
    | ⟨_, ordered⟩ =>
      match r.1 with
      | none => pure (.yield ⟨none, ordered⟩)
      | some a => pure (.done ⟨some a, ordered⟩)

/-- The first loop, `for tn in tyNames.zip listed`: the constructors in the
block's own order. -/
def orderBlockCtorsD (st : StateD) (fuel : Nat) (ctorIx : Std.HashMap NIdx Nat)
    (ctsA : Array IndCtorRec) (nPd : Nat) (l : List (NIdx × List NIdx))
    (out : Array IndCtorRec) : AM (MProd (Option VRes) (Array IndCtorRec)) :=
  forIn l ⟨none, out⟩ fun tn r => orderBlockStepD st fuel ctorIx ctsA nPd tn r.2

/-- `kExpected?`, official's `is_K_target`. -/
def kExpectedOfD (fuel : Nat) (tyTypes : List EIdx) (listed : List (List NIdx))
    (cts : List IndCtorRec) : AM (Option Bool) :=
  match tyTypes, listed, cts with
  | [ty], [[_]], [c] => do
    let r ← piResultD fuel ty
    match ← view r with
    | .sort s =>
      pure (some (c.numFields == 0 && ConLeche.Level.isEquiv (← readLevel s) .zero == some true))
    | _ => pure none
  | _, _, _ => pure (some false)

/-- One step of the second loop's inner `for tt in tyNames.zip tyTypes`. -/
def recIndexStepD (fuel : Nat) (rn T : NIdx) (numIndices nPd : Nat) (tt : NIdx × EIdx) :
    AM (ForInStep (MProd (Option VRes) PUnit)) := do
  if tt.1 == T then
    match ← piSortTeleLen? fuel tt.2 with
    | some n =>
      if nPd + numIndices == n then pure (.yield ⟨none, PUnit.unit⟩)
      else
        pure (.done ⟨some (.inl (.invalid s!"recursor {← readName rn} declares \
          {numIndices} indices; {← readName T} has {n - nPd} at {nPd} parameters")),
          PUnit.unit⟩)
    | none => pure (.yield ⟨none, PUnit.unit⟩)
  else pure (.yield ⟨none, PUnit.unit⟩)

/-- The second loop's inner `for tt in tyNames.zip tyTypes`: `numIndices` of
`T.rec` against `T`'s own telescope. -/
def checkRecIndicesD (fuel : Nat) (rn T : NIdx) (numIndices nPd : Nat)
    (l : List (NIdx × EIdx)) : AM (MProd (Option VRes) PUnit) :=
  forIn l ⟨none, PUnit.unit⟩ fun tt _ => recIndexStepD fuel rn T numIndices nPd tt

/-- The second loop's body at one recursor record: the four count checks,
the K flag, and `numIndices` against the type former's telescope. -/
def checkOneRecD (st : StateD) (fuel : Nat) (tyNames : List NIdx) (tyTypes : List EIdx)
    (nPd nTypes nCtors : Nat) (kExpected? : Option Bool) (r : IndRecRec) :
    AM (Option VRes) := do
  let rn ← st.name r.cv.name
  unless r.numParams == nPd do
    return some (.inl (.invalid s!"recursor {← readName rn} declares {r.numParams} \
      parameters; the block declares {nPd}"))
  unless r.numMotives == nTypes do
    return some (.inl (.invalid s!"recursor {← readName rn} declares {r.numMotives} \
      motives; the block has {nTypes} inductive types"))
  unless r.numMinors == nCtors do
    return some (.inl (.invalid s!"recursor {← readName rn} declares {r.numMinors} \
      minor premises; the block has {nCtors} constructors"))
  if let some kE := kExpected? then
    unless r.k == kE do
      return some (.inl (.invalid s!"recursor {← readName rn} declares k := {r.k}; \
        the generated recursor of this block is{if kE then "" else " not"} K-like"))
  match ← viewN rn with
  | .str T "rec" =>
    let r ← checkRecIndicesD fuel rn T r.numIndices nPd (tyNames.zip tyTypes)
    pure r.1
  | _ => pure none

/-- The second loop's body at one recursor record, as the twin's loop body
stands (`recStepD_eq` splits it at `checkOneRecD`). -/
def recStepD (st : StateD) (fuel : Nat) (tyNames : List NIdx) (tyTypes : List EIdx)
    (nPd nTypes nCtors : Nat) (kExpected? : Option Bool) (r : IndRecRec) :
    AM (ForInStep (MProd (Option VRes) PUnit)) := do
  let rn ← st.name r.cv.name
  unless r.numParams == nPd do
    return .done ⟨some (.inl (.invalid s!"recursor {← readName rn} declares {r.numParams} \
      parameters; the block declares {nPd}")), PUnit.unit⟩
  unless r.numMotives == nTypes do
    return .done ⟨some (.inl (.invalid s!"recursor {← readName rn} declares {r.numMotives} \
      motives; the block has {nTypes} inductive types")), PUnit.unit⟩
  unless r.numMinors == nCtors do
    return .done ⟨some (.inl (.invalid s!"recursor {← readName rn} declares {r.numMinors} \
      minor premises; the block has {nCtors} constructors")), PUnit.unit⟩
  if let some kE := kExpected? then
    unless r.k == kE do
      return .done ⟨some (.inl (.invalid s!"recursor {← readName rn} declares k := {r.k}; \
        the generated recursor of this block is{if kE then "" else " not"} K-like")),
        PUnit.unit⟩
  match ← viewN rn with
  | .str T "rec" =>
    let r ← checkRecIndicesD fuel rn T r.numIndices nPd (tyNames.zip tyTypes)
    match r.1 with
    | none => pure (.yield ⟨none, PUnit.unit⟩)
    | some a => pure (.done ⟨some a, PUnit.unit⟩)
  | _ => pure (.yield ⟨none, PUnit.unit⟩)

/-- The second loop, `for r in rcs`. -/
def checkRecRecordsD (st : StateD) (fuel : Nat) (tyNames : List NIdx) (tyTypes : List EIdx)
    (nPd nTypes nCtors : Nat) (kExpected? : Option Bool) (rcs : List IndRecRec) :
    AM (MProd (Option VRes) PUnit) :=
  forIn rcs ⟨none, PUnit.unit⟩ fun r _ =>
    recStepD st fuel tyNames tyTypes nPd nTypes nCtors kExpected? r

/-- `kExpectedOfD` with its continuation pushed into its arms, the shape the
twin's `let kExpected? ← match …` elaborates to. -/
theorem kExpectedOfD_bind {β : Type} (fuel : Nat) (tyTypes : List EIdx)
    (listed : List (List NIdx)) (cts : List IndCtorRec) (g : Option Bool → AM β) :
    kExpectedOfD fuel tyTypes listed cts >>= g =
      (match tyTypes, listed, cts with
       | [ty], [[_]], [c] => do
         let r ← piResultD fuel ty
         match ← view r with
         | .sort s => do
           let l ← readLevel s
           g (some (c.numFields == 0 && ConLeche.Level.isEquiv l .zero == some true))
         | _ => g none
       | _, _, _ => g (some false)) := by
  unfold kExpectedOfD
  split
  · simp only [bind_assoc]
    refine bind_congr fun r => bind_congr fun v => ?_
    split <;> simp only [bind_assoc, pure_bind]
  · simp only [pure_bind]

/-- **`validateIndD` IS its transcription composed.** -/
theorem validateIndD_unfold (st : StateD) (tys : List IndTypeRec) (cts : List IndCtorRec)
    (rcs : List IndRecRec) :
    validateIndD st tys cts rcs = (do
      if tys.any (·.isUnsafe) then
        return .inl (.declined "unsafe inductive declaration")
      let nPs := tys.map (·.numParams)
      let nPd := nPs.head?.getD 0
      unless nPs.all (· == nPd) do
        return .inl (.declined "inductive block whose type records disagree on numParams")
      let tyNames ← tys.mapM fun t => st.name t.cv.name
      let tyTypes ← tys.mapM fun t => getDeclD st t.cv.type
      let listed ← tys.mapM fun t => t.ctors.mapM st.name
      let ctorNames ← cts.mapM fun c => st.name c.cv.name
      let flat := listed.flatten
      unless flat.Nodup do
        return .inl (.invalid "duplicate constructor name in an inductive type's ctors")
      unless flat.length == cts.length do
        return .inl (.invalid s!"the inductive block lists {flat.length} constructors \
          and carries {cts.length} constructor records")
      let ctorIx : Std.HashMap NIdx Nat :=
        (ctorNames.foldl (fun (mi : Std.HashMap NIdx Nat × Nat) n =>
          (mi.1.insert n mi.2, mi.2 + 1)) ({}, 0)).1
      let fuel ← storeFuel
      let r ← orderBlockCtorsD st fuel ctorIx cts.toArray nPd (tyNames.zip listed) #[]
      match r.1 with
      | none =>
        let ctsO := r.2.toList
        let kExpected? ← kExpectedOfD fuel tyTypes listed ctsO
        let r2 ← checkRecRecordsD st fuel tyNames tyTypes nPd tys.length ctsO.length
          kExpected? (if tys.any (·.numNested != 0) then [] else rcs)
        match r2.1 with
        | none => pure (.inr (ctsO, nPd))
        | some a => pure a
      | some a => pure a) := by
  simp only [kExpectedOfD_bind]
  rfl

theorem ite_bind' {m : Type → Type} [Monad m] {α β : Type} (c : Prop) [Decidable c]
    (a b : m α) (f : α → m β) :
    (if c then a else b) >>= f = if c then a >>= f else b >>= f := by
  split <;> rfl

/-- The inner loop's step, split at `checkOneCtorD`. -/
theorem orderCtorStepD_eq (st : StateD) (fuel : Nat) (T : NIdx)
    (ctorIx : Std.HashMap NIdx Nat) (ctsA : Array IndCtorRec) (nPd : Nat)
    (n : NIdx) (j : Nat) (ordered : Array IndCtorRec) :
    orderCtorStepD st fuel T ctorIx ctsA nPd n j ordered =
      (match ctorIx[n]? with
      | some k =>
        match ctsA[k]? with
        | some c => do
          match ← checkOneCtorD st fuel T n c j nPd with
          | some a => pure (.done ⟨some a, j, ordered⟩)
          | none => pure (.yield ⟨none, j + 1, ordered.push c⟩)
        | none => do
          pure (.done ⟨some (.inl (.invalid s!"No such constructor {← readName n}")), j, ordered⟩)
      | none => do
        pure (.done ⟨some (.inl (.invalid s!"No such constructor {← readName n}")), j, ordered⟩)) := by
  unfold orderCtorStepD checkOneCtorD
  rcases ctorIx[n]? with _ | k
  · rfl
  dsimp only
  rcases ctsA[k]? with _ | c
  · rfl
  dsimp only
  rcases c with ⟨cv, isU, nF, nP, cidx, induct⟩
  dsimp only
  rcases cidx with _ | ci <;> rcases induct with _ | iw <;>
    simp only [bind_assoc, pure_bind, ite_bind']

/-- The recursor loop's step, split at `checkOneRecD`. -/
theorem recStepD_eq (st : StateD) (fuel : Nat) (tyNames : List NIdx) (tyTypes : List EIdx)
    (nPd nTypes nCtors : Nat) (kExpected? : Option Bool) (r : IndRecRec) :
    recStepD st fuel tyNames tyTypes nPd nTypes nCtors kExpected? r = (do
      match ← checkOneRecD st fuel tyNames tyTypes nPd nTypes nCtors kExpected? r with
      | some a => pure (.done ⟨some a, PUnit.unit⟩)
      | none => pure (.yield ⟨none, PUnit.unit⟩)) := by
  unfold recStepD checkOneRecD
  simp only [bind_assoc]
  refine bind_congr fun rn => ?_
  rcases kExpected? with _ | kE <;>
    simp only [bind_assoc, pure_bind, ite_bind'] <;> split_ifs <;>
    (try simp only [bind_assoc, pure_bind]) <;>
    (try refine bind_congr fun v => ?_) <;> (try split) <;> (try simp only [bind_assoc, pure_bind])
  all_goals exact bind_congr fun x => by rcases x with ⟨_ | _, _⟩ <;> rfl

end ConRon.Refine2.Frontend
