/-
# `ConRon.Refine2.Frontend.Spec` — the twin side of the port's own splits

**Task #97-P5-Frontend**, and `Refine2/Checker/Spec.lean`'s pattern at this
tier (task #97-P5-Checker's finding 11: *"one collected transcription file per
tier, with `_unfold` equations, and no edit to the twin"*).

DESIGN §3.4 splits a Rust function wherever a `let`-bound handle outlives a
`match` arm, wherever an arm would end in a branch, and wherever a `view`'s
loan would still be alive at an intern (extraction rules 5-7).  The frontend
is split that way wherever a twin `do` block has more structure than one Rust
body can carry — `proj_rec::proj_rec_value` alone is six functions for one
48-line block — and the split halves have no twin to be stated against.

This file is the twin side of those halves, written as twin-side `def`s in
`AM`, transcribed from `Arena/Frontend/{ProjRec,ExportC}.lean` clause for
clause, with an `_unfold` equation per family saying that the named twin IS
its transcription composed.  **Nothing under `Arena/` is edited to make the
refinement convenient**, which is the standing rule for a twin (DESIGN §8.4);
a reader checks these against the twin, not against a proof.

The `_unfold`s are `rfl`-shaped in the sense task #97-P5-Checker's §6 means:
each is a `do`-block equation in `StateT AState (Except CheckError)`, which
needs that section's rule-10 reduction discipline.  They are open here for the
same reason they were open there.

## `sorry` count in this file: 10
-/
import ConRon.Refine2.Frontend.NatOpGround

open Aeneas Aeneas.Std Result

namespace ConRon.Refine2.Frontend

open ConRon.Arena
open ConRon.Arena.Frontend
open ConLeche.Frontend (IdTable NameRec LevelRec ExprRec PwRec CVRec HintsRec RuleRec
  IndTypeRec IndCtorRec IndRecRec DeclRec LineRec)

/-! ## `proj_rec::mk_proj_motive` / `mk_proj_minor`

`ProjRec.lean:277-307`, past the peel: the port does `stripPisAll` and the
shape test in the outer function and the arm in the `_at` one. -/

/-- The cited `match bs with | [(d, m)] => … | bs => …` of `mkProjMotive`. -/
def mkProjMotiveAt (pb : ProjBuild) (fuel : Nat) (bs : List (EIdx × ConLeche.BinderMeta)) :
    AM (Option EIdx) := do
  match bs with
  | [(d, m)] =>
    if ← headIs fuel pb.T d then do
      let rl ← liftLooseBVarsFast fuel 1 1 pb.R
      pure (some (← internE (.lam d rl m)))
    else
      pure (some (← internE (.lam d pb.punitC m)))
  | bs => pure (some (← mkLams bs pb.punitC))

/-- The cited `if ← headIs fuel pb.ctor major then … else …` of
`mkProjMinor`, at the spine's last argument. -/
def mkProjMinorAt (pb : ProjBuild) (fuel : Nat)
    (bs : List (EIdx × ConLeche.BinderMeta)) (major : EIdx) : AM (Option EIdx) := do
  if ← headIs fuel pb.ctor major then
    if pb.i < bs.length then do
      let b ← internE (.bvar (bs.length - 1 - pb.i))
      pure (some (← mkLams bs b))
    else pure none
  else pure (some (← mkLams bs pb.punitUnitC))

/-- The `.forallE` arm's `do` block of `buildBinders`, at the binder's domain
and body. -/
def buildBindersAt (kind : ProjBinderKind) (pb : ProjBuild) (fuel : Nat) (k : Nat)
    (dom body : EIdx) : AM (Option (List EIdx × EIdx)) := do
  let t? ← match kind with
    | .motive => mkProjMotive pb fuel dom
    | .minor => mkProjMinor pb fuel dom
  match t? with
  | none => pure none
  | some t => do
    let body' ← instantiate1LiftFast fuel body t 0
    match ← buildBinders kind pb fuel k body' with
    | none => pure none
    | some (ts, rest) => pure (some (t :: ts, rest))

theorem mkProjMotive_unfold (pb : ProjBuild) (fuel : Nat) (dom : EIdx) :
    mkProjMotive pb fuel dom = (do
      let (bs, body) ← stripPisAll fuel dom
      match ← view body with
      | .sort _ => mkProjMotiveAt pb fuel bs
      | _ => pure none) := by sorry

theorem mkProjMinor_unfold (pb : ProjBuild) (fuel : Nat) (dom : EIdx) :
    mkProjMinor pb fuel dom = (do
      let (bs, cod) ← stripPisAll fuel dom
      match (← getAppArgs fuel cod).getLast? with
      | some major => mkProjMinorAt pb fuel bs major
      | none => pure none) := by sorry

theorem buildBinders_unfold (kind : ProjBinderKind) (pb : ProjBuild) (fuel k : Nat)
    (h : EIdx) :
    buildBinders kind pb fuel (k + 1) h = (do
      match ← view h with
      | .forallE dom body _ => buildBindersAt kind pb fuel k dom body
      | _ => pure none) := by sorry

/-! ## `proj_rec::proj_rec_value`, in five

The twin's one 48-line `do` block, cut at its own `let` boundaries.  The
arguments of each split are exactly the values in scope at that boundary. -/

/-- The spine itself, past the major-premise test. -/
def projRecValueApp (o : ProjRecOwner) (lbs : List (EIdx × ConLeche.BinderMeta))
    (us : LsIdx) (params motives minors : List EIdx) : AM (Option EIdx) := do
  let rc ← internE (.const o.recName us)
  let b0 ← internE (.bvar 0)
  let app ← mkAppN rc (params ++ motives ++ minors ++ [b0])
  pure (some (← mkLams lbs app))

/-- The final `match ← view rty3 with | .forallE majDom _ _ => …`. -/
def projRecValueMajor (fuel : Nat) (o : ProjRecOwner)
    (lbs : List (EIdx × ConLeche.BinderMeta)) (us : LsIdx)
    (params motives minors : List EIdx) (rty3 : EIdx) : AM (Option EIdx) := do
  match ← view rty3 with
  | .forallE majDom _ _ =>
    if !(← headIs fuel o.T majDom) then pure none
    else projRecValueApp o lbs us params motives minors
  | _ => pure none

/-- The `ProjBuild` record and the two `buildBinders` runs. -/
def projRecValueBinders (fuel : Nat) (o : ProjRecOwner) (l : LIdx) (r : EIdx) (i : Nat)
    (lbs : List (EIdx × ConLeche.BinderMeta)) (us : LsIdx) (params : List EIdx)
    (rty1 : EIdx) : AM (Option EIdx) := do
  let punitH ← internName ConLeche.punitName
  let punitUH ← internName ConLeche.punitUnitName
  let lsOne ← internLsNode [l]
  let pb : ProjBuild :=
    { T := o.T, ctor := o.ctor, R := r, i := i,
      punitC := ← internE (.const punitH lsOne),
      punitUnitC := ← internE (.const punitUH lsOne) }
  match ← buildBinders .motive pb fuel o.numMotives rty1 with
  | none => pure none
  | some (motives, rty2) =>
    match ← buildBinders .minor pb fuel o.numMinors rty2 with
    | none => pure none
    | some (minors, rty3) =>
      projRecValueMajor fuel o lbs us params motives minors rty3

/-- The recursor's type at the chosen elimination level, its parameters
instantiated at the body frame. -/
def projRecValueAt (fuel : Nat) (o : ProjRecOwner) (l : LIdx) (r : EIdx) (i : Nat)
    (lbs : List (EIdx × ConLeche.BinderMeta)) : AM (Option EIdx) := do
  let ups ← projRecValue.internParamLevels o.lps
  let us ← internLsNode (l :: ups)
  let rty0 ← instLPFast fuel o.recLps us o.recType
  let params ← bvarRange (o.nP + 1) o.nP 0
  match ← instPisOpen fuel rty0 params with
  | none => pure none
  | some rty1 => projRecValueBinders fuel o l r i lbs us params rty1

/-- Past the shape test: `match ← stripPis (o.nP + 1) ty with`. -/
def projRecValueTy (fuel : Nat) (o : ProjRecOwner) (l : LIdx) (ty : EIdx) (i : Nat)
    (lbs : List (EIdx × ConLeche.BinderMeta)) : AM (Option EIdx) := do
  match ← stripPis (o.nP + 1) ty with
  | none => pure none
  | some (_, r) => projRecValueAt fuel o l r i lbs

/-- **The `projRecValue` family's `_unfold`**: the twin IS the five
transcriptions composed. -/
theorem projRecValue_unfold (fuel : Nat) (o : ProjRecOwner) (l : LIdx) (ty val : EIdx)
    (i : Nat) :
    projRecValue fuel o l ty val i = (do
      match ← stripLams (o.nP + 1) val with
      | none => pure none
      | some (lbs, body) =>
        match ← view body with
        | .proj tn bi sub =>
          match ← view sub with
          | .bvar 0 =>
            if tn != o.T || bi != i || !(i < o.nF) then pure none
            else projRecValueTy fuel o l ty i lbs
          | _ => pure none
        | _ => pure none) := by sorry

/-! ## `proj_rec::proj_rec_candidates` and `proj_rec_owners`

The port splits the `filterMap`'s body twice — once at the constructor record
it found, once at the recursor record — for rule 5's reason (both arms read a
`Vec` out of a record and then intern). -/

/-- Past the sort test: the constructor's record, the recursor `T.rec`, and
the elimination level parameter its level list must carry. -/
def projRecCandidateRec (ctors : List (NIdx × Nat × EIdx))
    (recs : List (NIdx × List NIdx × EIdx × Nat × Nat))
    (t : NIdx × List NIdx × EIdx × Nat × Nat × List NIdx × Bool) :
    AM (Option ProjRecOwner) := do
  match t.2.2.2.2.2.1 with
  | [c] =>
    match findCtorRec c ctors with
    | none => pure none
    | some (_, nF, _) => do
      let rn ← internNNode (.str t.1 "rec")
      match findRecRec rn recs with
      | none => pure none
      | some (rn, rlps, rty, nM, nm) =>
        if rlps.length != t.2.1.length + 1 then pure none
        else pure (some ⟨t.1, t.2.1, t.2.2.2.1, c, nF, rn, rlps, rty, nM, nm⟩)
  | _ => pure none

/-- One type record's candidacy: one constructor, zero indices, a sort body
that is not `Prop`.  `Level.isEquiv` runs on the READ-BACK level (DESIGN §8.3
lesson 4). -/
def projRecCandidateAt (ctors : List (NIdx × Nat × EIdx))
    (recs : List (NIdx × List NIdx × EIdx × Nat × Nat))
    (t : NIdx × List NIdx × EIdx × Nat × Nat × List NIdx × Bool) :
    AM (Option ProjRecOwner) := do
  match t.2.2.2.2.2.1 with
  | [_] =>
    if t.2.2.2.2.1 != 0 then pure none else do
      match ← stripPis t.2.2.2.1 t.2.2.1 with
      | none => pure none
      | some (_, body) =>
        match ← view body with
        | .sort s => do
          let sP ← readLevel s
          if ConLeche.Level.isEquiv sP .zero == some true then pure none
          else projRecCandidateRec ctors recs t
        | _ => pure none
  | _ => pure none

/-- The guard that decides whether the rewrite serves the block at all: the
two delegated recognisers and the recursive test, in the twin's own CHEAP
ORDER (`ProjRec.lean`'s deviation 3). -/
def projRecOwnersGuard (fuel : Nat) (block : List IConstantInfo)
    (types : List (NIdx × List NIdx × EIdx × Nat × Nat × List NIdx × Bool))
    (ctors : List (NIdx × Nat × EIdx)) (owners : List ProjRecOwner) :
    AM (List ProjRecOwner) := do
  match owners with
  | [] => pure []
  | _ :: _ => do
    let blockNames := types.map (·.1)
    let recursive := types.any (·.2.2.2.2.2.2) ||
      (← ctorsMentionBlock fuel blockNames ctors)
    if (← structPartsCore? block).isSome && !recursive then pure []
    else if (← nativeParts? ((types.head?.map (·.2.2.2.1)).getD 0) block).isSome
      then pure []
    else pure owners

/-- **`projRecOwners`'s `_unfold`**. -/
theorem projRecOwners_unfold (fuel : Nat) (block : List IConstantInfo)
    (types : List (NIdx × List NIdx × EIdx × Nat × Nat × List NIdx × Bool))
    (ctors : List (NIdx × Nat × EIdx))
    (recs : List (NIdx × List NIdx × EIdx × Nat × Nat)) :
    projRecOwners fuel block types ctors recs = (do
      let owners ← projRecCandidates fuel ctors recs types
      projRecOwnersGuard fuel block types ctors owners) := by sorry

/-- **`projRecCandidates`'s `_unfold`** at a `cons`. -/
theorem projRecCandidates_unfold (fuel : Nat) (ctors : List (NIdx × Nat × EIdx))
    (recs : List (NIdx × List NIdx × EIdx × Nat × Nat))
    (t : NIdx × List NIdx × EIdx × Nat × Nat × List NIdx × Bool)
    (rest : List (NIdx × List NIdx × EIdx × Nat × Nat × List NIdx × Bool)) :
    projRecCandidates fuel ctors recs (t :: rest) = (do
      let tail ← projRecCandidates fuel ctors recs rest
      match ← projRecCandidateAt ctors recs t with
      | none => pure tail
      | some o => pure (o :: tail)) := by sorry

/-! ## `export_c`'s own splits

`note_decl`'s two halves, and the value halves of the two entry writers that
the twin spells inline.  `RefineOld/Frontend/StateDR.lean` needed exactly the
same two escape-hatch definitions for the `Expr`-tree port
(`parseExprRecD` / `parseLevelRecD`, and its `parseExprEntryD_eq` /
`parseLevelEntryD_eq` equivalences). -/

/-- The cited `cvs` of `noteDecl`: the constants one pushed record declares. -/
def noteDeclEntries : IDeclaration → AM (List (NIdx × List NIdx × EIdx × Option Nat))
  | .axiomDecl cv => pure [(cv.name, cv.levelParams, cv.type, none)]
  | .defnDecl cv _ h => pure [(cv.name, cv.levelParams, cv.type, some (hintHeight h))]
  | .thmDecl cv _ => pure [(cv.name, cv.levelParams, cv.type, none)]
  | .opaqueDecl cv _ => pure [(cv.name, cv.levelParams, cv.type, none)]
  | .basisDecl _ => fail (.internal "noteDecl: a basisDecl is not a parser record")
  | .quotDecl _ cv => pure [(cv.name, cv.levelParams, cv.type, none)]
  | .indDecl block _ => block.mapM fun ci => do
      let v ← ci.toConstantVal
      pure (v.name, v.levelParams, v.type, none)

/-- The cited `cvs.foldl` of `noteDecl`. -/
def noteEntries (st : StateD) (es : List (NIdx × List NIdx × EIdx × Option Nat)) :
    StateD :=
  let ct := st.constTypes
  let hs := st.heights
  let st := { st with constTypes := {}, heights := {} }
  let (ct, hs) := es.foldl (fun (ct, hs) (n, lps, ty, h) =>
    (ct.insert n (lps, ty), match h with | some h => hs.insert n h | none => hs)) (ct, hs)
  { st with constTypes := ct, heights := hs }

theorem noteDecl_unfold (st : StateD) (d : IDeclaration) :
    noteDecl st d = (do pure (noteEntries st (← noteDeclEntries d))) := by sorry

/-- The value half of `parseLevelEntryD`, which the twin writes inline. -/
def parseLevelRecD (st : StateD) : ConLeche.Frontend.LevelRec → AM LNodeView
  | .succ u => do pure (.succ (← st.level u))
  | .max a b => do pure (.max (← st.level a) (← st.level b))
  | .imax a b => do pure (.imax (← st.level a) (← st.level b))
  | .param n => do pure (.param (← st.name n))

theorem parseLevelEntryD_unfold (st : StateD) (i : Nat) (r : ConLeche.Frontend.LevelRec) :
    parseLevelEntryD st i r = (do
      st.freshLevel i
      let l ← internLNode (← parseLevelRecD st r)
      pure { st with levels := st.levels.insert i l }) := by sorry

/-- The value half of `parseExprEntryD`, which the twin writes inline. -/
def parseExprRecD (st : StateD) : ConLeche.Frontend.ExprRec → AM EIdx
  | .bvar k => internE (.bvar k)
  | .sort u => do internE (.sort (← st.level u))
  | .const n us => do
    let nm ← st.name n
    let ls ← us.mapM st.level
    let lsh ← internLsNode ls
    internE (.const nm lsh)
  | .app f a => do internE (.app (← st.expr f) (← st.expr a))
  | .lam ty bd pw => do
    internE (.lam (← st.expr ty) (← st.expr bd) ⟨← parsePwD st pw⟩)
  | .forallE ty bd pw => do
    internE (.forallE (← st.expr ty) (← st.expr bd) ⟨← parsePwD st pw⟩)
  | .letE ty vl bd => do
    internE (.letE (← st.expr ty) (← st.expr vl) (← st.expr bd))
  | .proj tn ix s => do internE (.proj (← st.name tn) ix (← st.expr s))
  | .natVal n => internE (.lit (.natVal n))
  | .strVal s => internE (.lit (.strVal s))

theorem parseExprEntryD_unfold (st : StateD) (i : Nat) (r : ConLeche.Frontend.ExprRec) :
    parseExprEntryD st i r = (do
      st.freshExpr i
      let e ← parseExprRecD st r
      pure { st with exprs := st.exprs.insert i e }) := by sorry

/-- The twin's `types ++ ctors ++ recs` of `installIndD`, which the port
factors out as `ind_block_of`. -/
def indBlockOf (st : StateD) (tys : List IndTypeRec) (cts : List IndCtorRec)
    (rcs : List IndRecRec) : AM (List IConstantInfo) := do
  let types ← tys.mapM fun t => do
    pure (IConstantInfo.indInfo (← parseCVD st t.cv) {})
  let ctors ← cts.mapM fun c => do
    pure (IConstantInfo.ctorInfo (← parseCVD st c.cv) c.numParams c.numFields)
  let recs ← rcs.mapM fun r => do
    let rules ← r.rules.mapM (parseRuleD st)
    pure (IConstantInfo.recInfo (← parseCVD st r.cv)
      (r.numParams + r.numMotives + r.numMinors + r.numIndices)
      (r.numParams + r.numMotives + r.numMinors) rules)
  pure (types ++ ctors ++ recs)

/-- The twin's `b.types.foldl` into `indBlocks`. -/
def noteIndBlocks (st : StateD) (b : BlockRec) : StateD :=
  let m := st.indBlocks
  let st := { st with indBlocks := {} }
  { st with indBlocks := b.types.foldl (fun m t => m.insert t.cv.name b) m }

/-- The modeller arm of `installIndD`, which the twin writes inline and the
port splits for the loop-exit reason (task #87 §13 records the same decision
for the `Expr`-tree port: *"no standalone `install_gen_refines`"*, because
con-leche writes the body inline with the post-`noteIndBlocks` state
substituted field by field). -/
def installGen (md : Modeller) (st : StateD) (block : List IConstantInfo) (nPd : Nat)
    (T0 : NIdx) (b : BlockRec) : AM (StateD ⊕ RecordVerdict) := do
  let ctx : Ctx :=
    ⟨fun n => st.constTypes[n]?, fun n => st.heights.getD n 0, fun n => st.indBlocks[n]?⟩
  match ← md.generate ctx b with
  | .error why =>
    if st.inModelCensus then
      return .inl (← pushDecl
        { st with inModelDeclined := st.inModelDeclined.push (T0, why) }
        (.indDecl block nPd))
    else
      return .inr (.declined s!"in-process model of {← readName T0}: {why}")
  | .ok gen => do
    let st1 ← pushGenList st gen T0
    let st1 := { st1 with
      inModelled := st1.inModelled.push T0,
      inModelGen := st1.inModelGen.push (st1.indCount - 1, gen.toArray) }
    return .inl (← pushDecl st1 (.indDecl block nPd))

theorem installIndD_unfold (md : Modeller) (st : StateD) (tys : List IndTypeRec)
    (cts : List IndCtorRec) (rcs : List IndRecRec) (nPd : Nat) :
    installIndD md st tys cts rcs nPd = (do
      let block ← indBlockOf st tys cts rcs
      let st ← registerProjOwners st tys cts rcs block
      let T0 ← match block.head? with
        | some ci => pure ci.name
        | none => internNNode .anonymous
      let b ← blockRecOf st tys cts rcs
      let st := noteIndBlocks st b
      if st.inModel && wants b then installGen md st block nPd T0 b
      else return .inl (← pushDecl st (.indDecl block nPd))) := by sorry

end ConRon.Refine2.Frontend
