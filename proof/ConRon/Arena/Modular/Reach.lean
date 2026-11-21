/-
# `ConRon.Arena.Modular.Reach` — a worker's context (task #166)

The twin of `frontend/modular/reach.rs`, function for function.  The reach's caches are
threaded explicitly (`ReachCache`, returned beside each answer; the Rust's `&mut`), a failure is
the monad's.  A part's region is upstream's `Region × SM`.  Tables, lookups, views and recursor
blocks are made sure of by one function and read by another (`tableGet`, `lookAt`, `viewAt`,
`recLocsAt`), as the Rust reads them in place.  The worklist's stack is a list, its top first.
The inferred flags run at a frozen index `I` (`inferFlags`, after the worker's freeze): the view
of the first context record storing a name is upstream's `ctxPart`.
-/
module

public import ConRon.Arena.Frontend.Olean.Index
public import ConRon.Arena.Frontend.Olean.Present
public import ConRon.Arena.Needs
public import ConRon.Arena.Justify
public import ConRon.Arena.Inductives.StreamRecs
public import ConRon.Arena.Frontend.Compare

@[expose] public section

namespace ConRon.Arena.Modular

open ConLeche
open ConRon.Arena.Frontend.Olean
open ConLeche.Frontend.Olean (OLeanLevel CEntryF CKindF Region Roots ModFiles LoadFlags)

deriving instance Hashable for ConLeche.Frontend.Olean.OLeanLevel

/-! ## What a record reads -/

/-- con-leche: ConLeche/Driver/Reach.lean:90-94 recordReads
The constants' laws' names, in order. -/
def recordReadsConsts : NeedsSt → List IConstantInfo → AM NeedsSt
  | x, [] => pure x
  | x, c :: cs => do recordReadsConsts (← x.const c) cs

/-- con-leche: ConLeche/Driver/Reach.lean:90-94 recordReads
The tables' names, in order. -/
def recordReadsTables : NeedsSt → List IProjTable → AM NeedsSt
  | x, [] => pure x
  | x, t :: ts => do recordReadsTables (← x.table t) ts

/-- con-leche: ConLeche/Driver/Reach.lean:90-94 recordReads
**What a record reads**: its constants' laws' names and its tables'. -/
def recordReads (d : IDeclaration) : AM (List NIdx) := do
  let cs ← declConstants d
  let ts ← declTables d
  let x ← recordReadsConsts NeedsSt.empty cs
  let x ← recordReadsTables x ts
  pure x.acc

/-- con-leche: ConLeche/Modular.lean:98-99 declNames
**The names a record installs**: its constants' names. -/
def declNames (d : IDeclaration) : AM (List NIdx) := do
  pure ((← declConstants d).map (·.name))

/-! ## The validation of a record -/

/-- con-leche: ConLeche/Driver/Reach.lean:104-107 exprOk
**An expression's syntactic clauses**. -/
def exprOk (lps : List NIdx) (k : Nat) (e : EIdx) : AM Bool := do
  if ← hasFvarFast coreWalkFuel e then return false
  if !(← looseBVarsBoundedFast coreWalkFuel k e) then return false
  allLevelParamsDefined lps e

/-- con-leche: ConLeche/Driver/Reach.lean:109-122 nestedOk
`lvls.all (·.allParamsDefined lps)`. -/
def levelsDefined (ps : List Name) : List LIdx → AM Bool
  | [] => pure true
  | l :: ls => do
    let u ← readLevelM l
    if !u.allParamsDefined ps then return false
    levelsDefined ps ls

/-- con-leche: ConLeche/Driver/Reach.lean:109-122 nestedOk
`es.all (exprOk lps k)`. -/
def exprsOk (lps : List NIdx) (k : Nat) : List EIdx → AM Bool
  | [] => pure true
  | e :: es => do
    if !(← exprOk lps k e) then return false
    exprsOk lps k es

/-- con-leche: ConLeche/Driver/Reach.lean:109-122 nestedOk
**A nested rule's datum reads off its recursor's type** (`streamNestedOk`'s match). -/
def nestedOk (lps : List NIdx) (ty : EIdx) (mI rP : Nat) (fire : IRecRuleFire) : AM Bool := do
  match fire with
  | .nested lvls pins =>
    if !(rP ≤ mI) then return false
    let ps ← readNames lps
    if !(← levelsDefined ps lvls) then return false
    if !(← exprsOk lps rP pins) then return false
    streamNestedOk ty mI rP fire
  | _ => pure true

/-- con-leche: ConLeche/Driver/Reach.lean:124-130 ruleOk
A recursor rule's clauses. -/
def ruleOk (lps : List NIdx) (ty : EIdx) (mI rP : Nat) (r : IRecRule) : AM Bool := do
  if !(← exprOk lps 0 r.rhs) then return false
  if !(rP ≤ mI) then return false
  if rP + r.nfields ≥ 2 ^ 64 then return false
  match ← stripLams (rP + r.nfields) r.rhs with
  | none => pure false
  | some _ => nestedOk lps ty mI rP r.fire

/-- con-leche: ConLeche/Driver/Reach.lean:139-147 constOk
`rules.all (ruleOk lps ty mI rP)`. -/
def rulesOk (lps : List NIdx) (ty : EIdx) (mI rP : Nat) : List IRecRule → AM Bool
  | [] => pure true
  | r :: rs => do
    if !(← ruleOk lps ty mI rP r) then return false
    rulesOk lps ty mI rP rs

/-- con-leche: ConLeche/Driver/Reach.lean:132-137 ctorHeadOk
**A constructor's stored family is the one its type concludes in**. -/
def ctorHeadOk (cv : IConstantVal) (induct : NIdx) : AM Bool := do
  let b ← piResult coreWalkFuel cv.type
  let hd ← getAppFn coreWalkFuel b
  if hd.tag == ETag.const then
    match ← viewConstName hd with
    | none => pure false
    | some t => pure (t == induct)
  else pure false

/-- con-leche: ConLeche/Driver/Reach.lean:139-147 constOk
**A constant's syntactic clauses**. -/
def constOk : IConstantInfo → AM Bool
  | .defnInfo cv v _ => do
    if !(← exprOk cv.levelParams 0 cv.type) then return false
    exprOk cv.levelParams 0 v
  | .recInfo cv mI rP _ rules => do
    if !(← exprOk cv.levelParams 0 cv.type) then return false
    rulesOk cv.levelParams cv.type mI rP rules
  | .ctorInfo cv _ _ induct => do
    if !(← exprOk cv.levelParams 0 cv.type) then return false
    ctorHeadOk cv induct
  | .axiomInfo cv => exprOk cv.levelParams 0 cv.type
  | .thmInfo cv => exprOk cv.levelParams 0 cv.type
  | .indInfo cv _ => exprOk cv.levelParams 0 cv.type

/-- con-leche: ConLeche/Driver/Reach.lean:149-152 tableOk
**A table's syntactic clauses**. -/
def tableOk (t : IProjTable) : AM Bool := do
  if t.bodies.size != t.numFields then return false
  if t.numParams + 1 ≥ 2 ^ 64 then return false
  exprsOk t.levelParams (t.numParams + 1) t.bodies.toList

/-- con-leche: ConLeche/Driver/Reach.lean:154-157 recordOk
`(declConstants d).all (fun c => constOk c && litShapeOk c)`. -/
def constsOk : List IConstantInfo → AM Bool
  | [] => pure true
  | c :: cs => do
    if !(← constOk c) then return false
    if !(← litShapeOk c) then return false
    constsOk cs

/-- con-leche: ConLeche/Driver/Reach.lean:154-157 recordOk
`(declTables d).all tableOk`. -/
def tablesOk : List IProjTable → AM Bool
  | [] => pure true
  | t :: ts => do
    if !(← tableOk t) then return false
    tablesOk ts

/-- con-leche: ConLeche/Driver/Reach.lean:154-157 recordOk
**A record validated**. -/
def recordOk (d : IDeclaration) : AM Bool := do
  let cs ← declConstants d
  if !(← constsOk cs) then return false
  tablesOk (← declTables d)

/-! ## The reach's reads -/

/-- con-leche: ConLeche/Driver/Reach.lean:163-167 PartKey
**A part of a view**: a module and a level. -/
structure PartKey where
  mod : NIdx
  level : OLeanLevel
  deriving BEq, Hashable

/-- con-leche: ConLeche/Driver/Reach.lean:163-167 PartKey
The key of a module's private part. -/
def privKey (m : NIdx) : PartKey := ⟨m, .private⟩

/-- con-leche: ConLeche/Driver/Reach.lean:169-172 Spot
**A copy of a name**: the part holding it and its name position there. -/
structure Spot where
  part : PartKey
  pos : NamePosition

/-- con-leche: ConLeche/Driver/Reach.lean:174-185 ReachEnv
What the reach reads its records with, fixed for the run. -/
structure ReachEnv where
  mod : NIdx
  wr : WorkerReads
  own : Std.HashSet NIdx
  copies : Std.HashMap NIdx (Array (NIdx × StmtRec))

/-- con-leche: ConLeche/Driver/Reach.lean:187-211 ReachCache
**The reach's caches**: what it has read of the files. -/
structure ReachCache where
  tables : Std.HashMap PartKey NamePositions := {}
  looks : Std.HashMap PartKey (Std.HashMap NIdx NamePosition) := {}
  parts : Std.HashMap PartKey (Region × SM) := {}
  recBlocks : Std.HashMap PartKey (Std.HashMap NIdx (Array Nat)) := {}
  views : Std.HashMap NIdx (Std.HashMap NIdx Spot) := {}
  located : Std.HashMap NIdx Spot := {}
  completed : Array (NIdx × NIdx) := #[]
  pending : Array (String × NIdx × StmtRec) := #[]
  partners : Array (NIdx × NIdx) := #[]
  searches : Nat := 0

/-- con-leche: ConLeche/Driver/Reach.lean:213-216 viewKeys
**The parts of module `h`'s view**, in order. -/
def viewKeys (h : NIdx) (ld : HeaderLoads) : List PartKey :=
  privKey h :: (ld.order.zip ld.flags).toList.map fun (m, fl) => ⟨m, fl.level⟩

/-- con-leche: ConLeche/Driver/Reach.lean:218-222 viewStep
**One part's names into a view**, the first copy of each name kept. -/
def viewStep (v : Std.HashMap NIdx Spot) (k : PartKey) (t : NamePositions) : Std.HashMap NIdx Spot :=
  t.consts.foldl (fun (v : Std.HashMap NIdx Spot) q =>
    if v.contains q.name then v else v.insert q.name ⟨k, q⟩) v

/-! ## The parts -/

/-- con-leche: ConLeche/Driver/Reach.lean:229-247 tableOf
The index's table of a part: where the module is loaded at that level. -/
def indexTable (wr : WorkerReads) (k : PartKey) : Option NamePositions :=
  match wr.loads.index[k.mod]? with
  | none => none
  | some i => if wr.loads.levelAt i == k.level then wr.index.parts[i]? else none

/-- con-leche: ConLeche/Driver/Reach.lean:229-247 tableOf
**A part's name table, where it is**. -/
def tableGet (wr : WorkerReads) (c : ReachCache) (k : PartKey) : Option NamePositions :=
  match c.tables[k]? with
  | some t => some t
  | none => indexTable wr k

/-- con-leche: none — an internal failure: a cache entry the reach just made sure of is not there -/
def cacheLost : CheckError := .internal "the reach lost a cached table"

/-- con-leche: ConLeche/Driver/Reach.lean:229-247 tableOf
**A part's name table**: the index's, else read once. -/
def tableOf (fs : OleanFs) (pk : OleanPins) (sp : Roots) (env : ReachEnv) (c : ReachCache) (k : PartKey) :
    AM ReachCache := do
  if c.tables.contains k then return c
  if (indexTable env.wr k).isSome then return c
  let t ← readPartNames fs pk sp k.mod k.level
  pure { c with tables := c.tables.insert k t }

/-- con-leche: ConLeche/Driver/Reach.lean:249-260 lookOf
A table's lookup. -/
def lookBuild (t : NamePositions) : Std.HashMap NIdx NamePosition :=
  t.consts.foldl (fun (l : Std.HashMap NIdx NamePosition) q => l.insert q.name q) {}

/-- con-leche: ConLeche/Driver/Reach.lean:249-260 lookOf
**A part's name lookup**, built once. -/
def lookOf (fs : OleanFs) (pk : OleanPins) (sp : Roots) (env : ReachEnv) (c : ReachCache) (k : PartKey) :
    AM ReachCache := do
  if c.looks.contains k then return c
  let c ← tableOf fs pk sp env c k
  match tableGet env.wr c k with
  | none => fail cacheLost
  | some t => pure { c with looks := c.looks.insert k (lookBuild t) }

/-- con-leche: ConLeche/Driver/Reach.lean:249-260 lookOf
A name's position in a part's cached lookup. -/
def lookAt (c : ReachCache) (k : PartKey) (n : NIdx) : AM (Option NamePosition) :=
  match c.looks[k]? with
  | none => fail cacheLost
  | some l => pure l[n]?

/-- con-leche: ConLeche/Driver/Reach.lean:262-282 withPart
**A part taken out of the caches for a read**. -/
def takePart (fs : OleanFs) (pk : OleanPins) (sp : Roots) (c : ReachCache) (k : PartKey) :
    AM (ReachCache × Region × SM) := do
  match c.parts[k]? with
  | some (r, st) => pure ({ c with parts := c.parts.erase k }, r, st)
  | none =>
    let mn ← readName k.mod
    let f ← liftE (readFiles fs sp mn k.level)
    match f.viewRegion k.level with
    | none => fail (← viewError pk mn f k.level)
    | some (r, _) => pure (c, r, {})

/-- con-leche: ConLeche/Driver/Reach.lean:262-282 withPart
**A part put back after a read**: its memo where the read went through, an empty memo where
it did not. -/
def putPart {α : Type} (c : ReachCache) (k : PartKey) (r : Region) (res : SM × Option α) :
    AM (ReachCache × α) := do
  match res with
  | (st, some a) => pure ({ c with parts := c.parts.insert k (r, st) }, a)
  | (_, none) => fail (undecodable (← readName k.mod))

/-- con-leche: ConLeche/Driver/Reach.lean:284-301 loadPart
**A part's region and name table off one read of its files**. -/
def loadPart (fs : OleanFs) (pk : OleanPins) (sp : Roots) (c : ReachCache) (k : PartKey) :
    AM ReachCache := do
  if c.parts.contains k then return c
  let mn ← readName k.mod
  let f ← liftE (readFiles fs sp mn k.level)
  match f.viewRegion k.level with
  | none => fail (← viewError pk mn f k.level)
  | some (r, a) =>
    if c.tables.contains k then return { c with parts := c.parts.insert k (r, {}) }
    match ← namePositionsAt pk r a with
    | none => fail (← viewError pk mn f k.level)
    | some t => pure { c with parts := c.parts.insert k (r, {}), tables := c.tables.insert k t }

/-- con-leche: ConLeche/Driver/Reach.lean:303-309 entriesWith
Several constants with one memo (`entryWith`, in order). -/
def entriesWith (pk : OleanPins) (r : Region) : SM → List Nat → AM (SM × Option (List (CEntryF NIdx EIdx)))
  | st, [] => pure (st, some [])
  | st, l :: ls => do
    match ← entryWith pk r st l with
    | (st, none) => pure (st, none)
    | (st, some e) =>
      match ← entriesWith pk r st ls with
      | (st, none) => pure (st, none)
      | (st, some es) => pure (st, some (e :: es))

/-- con-leche: ConLeche/Driver/Reach.lean:262-282 withPart
`withPart env c k fun r st => entryWith r st l`. -/
def partEntry (fs : OleanFs) (pk : OleanPins) (sp : Roots) (c : ReachCache) (k : PartKey) (l : Nat) :
    AM (ReachCache × CEntryF NIdx EIdx) := do
  let (c, r, st) ← takePart fs pk sp c k
  putPart c k r (← entryWith pk r st l)

/-- con-leche: ConLeche/Driver/Reach.lean:262-282 withPart
`withPart env c k fun r st => entriesWith r st ls`. -/
def partEntries (fs : OleanFs) (pk : OleanPins) (sp : Roots) (c : ReachCache) (k : PartKey) (ls : List Nat) :
    AM (ReachCache × List (CEntryF NIdx EIdx)) := do
  let (c, r, st) ← takePart fs pk sp c k
  putPart c k r (← entriesWith pk r st ls)

/-- con-leche: ConLeche/Driver/Reach.lean:311-314 stmtAt
**A copy's statement and kind**. -/
def stmtAt (fs : OleanFs) (pk : OleanPins) (sp : Roots) (c : ReachCache) (s : Spot) :
    AM (ReachCache × StmtRec × CKindF NIdx Unit) := do
  let (c, r, st) ← takePart fs pk sp c s.part
  putPart c s.part r (← stmtWith pk r st s.pos.loc)

/-- con-leche: ConLeche/Driver/Reach.lean:316-328 privSpot
**A copy in a module's private part**. -/
def privSpot (fs : OleanFs) (pk : OleanPins) (sp : Roots) (env : ReachEnv) (c : ReachCache) (s : Spot) :
    AM (ReachCache × Spot) := do
  if s.part.level == .private then return (c, s)
  let k := privKey s.part.mod
  let c ← lookOf fs pk sp env c k
  match ← lookAt c k s.pos.name with
  | some q => pure (c, ⟨k, q⟩)
  | none => fail (.invalid s!"module {← readName s.part.mod}: its exported part holds \
      {← readName s.pos.name}, its private part does not")

/-! ## A home's view, and a search in it -/

/-- con-leche: ConLeche/Driver/Reach.lean:332-340 viewAdd
One part's names into a view. -/
def viewAddOne (fs : OleanFs) (pk : OleanPins) (sp : Roots) (env : ReachEnv) (c : ReachCache)
    (v : Std.HashMap NIdx Spot) (k : PartKey) : AM (ReachCache × Std.HashMap NIdx Spot) := do
  let c ← tableOf fs pk sp env c k
  match tableGet env.wr c k with
  | none => fail cacheLost
  | some t => pure (c, viewStep v k t)

/-- con-leche: ConLeche/Driver/Reach.lean:332-340 viewAdd
The names of some parts into a view, the first copy kept. -/
def viewAdd (fs : OleanFs) (pk : OleanPins) (sp : Roots) (env : ReachEnv) :
    ReachCache → Std.HashMap NIdx Spot → List PartKey → AM (ReachCache × Std.HashMap NIdx Spot)
  | c, v, [] => pure (c, v)
  | c, v, k :: ks => do
    let (c, v) ← viewAddOne fs pk sp env c v k
    viewAdd fs pk sp env c v ks

/-- con-leche: ConLeche/Driver/Reach.lean:342-357 viewOf
The header fixpoint of module `h`'s own private part. -/
def homeLoads (fs : OleanFs) (pk : OleanPins) (sp : Roots) (env : ReachEnv) (c : ReachCache)
    (k : PartKey) : AM HeaderLoads :=
  match tableGet env.wr c k with
  | none => fail cacheLost
  | some own => headerFixpoint fs pk sp own.header.isModule own.header.imports

/-- con-leche: ConLeche/Driver/Reach.lean:342-357 viewOf
**Module `h`'s view, by name**, built once per home. -/
def viewOf (fs : OleanFs) (pk : OleanPins) (sp : Roots) (env : ReachEnv) (c : ReachCache) (h : NIdx) :
    AM ReachCache := do
  if c.views.contains h then return c
  let k := privKey h
  let c ← tableOf fs pk sp env c k
  let ld ← homeLoads fs pk sp env c k
  let (c, v) ← viewAdd fs pk sp env c {} (viewKeys h ld)
  pure { c with views := c.views.insert h v }

/-- con-leche: ConLeche/Driver/Reach.lean:359-364 locate
A name in a home's cached view. -/
def viewAt (c : ReachCache) (h y : NIdx) : AM (Option Spot) :=
  match c.views[h]? with
  | none => fail cacheLost
  | some v => pure v[y]?

/-- con-leche: ConLeche/Driver/Reach.lean:359-364 locate
**`y` located in `h`'s view.** -/
def locate (fs : OleanFs) (pk : OleanPins) (sp : Roots) (env : ReachEnv) (c : ReachCache) (h y : NIdx) :
    AM (ReachCache × Option Spot) := do
  let c ← viewOf fs pk sp env c h
  let c := { c with searches := c.searches + 1 }
  pure (c, ← viewAt c h y)

/-- con-leche: ConLeche/Driver/Reach.lean:366-372 importerSpot
**The importer's copy of a loaded name**. -/
def importerSpot (pk : OleanPins) (env : ReachEnv) (y : NIdx) : Option (Nat × Spot) := do
  let cp ← env.wr.index.first[y]?
  let q ← env.wr.index.at cp
  let ld := env.wr.loads
  pure (cp.mod, ⟨⟨ld.nameAt pk cp.mod, ld.levelAt cp.mod⟩, q⟩)

/-! ## Agreement -/

/-- con-leche: ConLeche/Driver/Reach.lean:376-382 ProofStatus
**Is a copy a proof**. -/
inductive ProofStatus where
  | yes
  | no
  | infer
  deriving BEq

/-- con-leche: ConLeche/Driver/Reach.lean:384-402 proofStatus
**A copy's proof flag**. -/
def proofStatus (fs : OleanFs) (pk : OleanPins) (sp : Roots) (env : ReachEnv) (c : ReachCache)
    (s : Spot) (k : CKindF NIdx Unit) : AM (ReachCache × ProofStatus) := do
  match k with
  | .thm .. => pure (c, .yes)
  | .defn .. => pure (c, .infer)
  | .opaq .. => pure (c, .infer)
  | .ax _ =>
    if s.part.level == .private then return (c, .infer)
    let (c, p) ← privSpot fs pk sp env c s
    if p.pos.tag == 2 then pure (c, .yes)
    else if p.pos.tag == 0 || p.pos.tag == 1 || p.pos.tag == 3 then pure (c, .infer)
    else pure (c, .no)
  | _ => pure (c, .no)

/-- con-leche: ConLeche/Driver/Reach.lean:404-406 partnerReads
The names a statement reads, each paired with a home, onto `acc`. -/
def partnerReads (acc : Array (NIdx × NIdx)) (h : NIdx) (ty : EIdx) : AM (Array (NIdx × NIdx)) := do
  let x ← NeedsSt.empty.expr ty
  pure (x.acc.foldl (fun acc y => acc.push (h, y)) acc)

/-- con-leche: ConLeche/Driver/Reach.lean:408-440 agreeCheck
`s!"name capture at {y}, read by module {h}"`, the names as the Rust's `name_text` renders
them (`nameText`: `?` for a dangling handle), so the message of a recorded statement cannot
fail. -/
def captureWhat (h y : NIdx) : AM String := do
  pure s!"name capture at {← Frontend.nameText y}, read by module {← Frontend.nameText h}"

/-- con-leche: ConLeche/Driver/Reach.lean:408-440 agreeCheck
The copies of `y` of two modules are not one constant. -/
def agreeBad (h y m₁ m₂ : NIdx) : AM CheckError := do
  pure (.invalid s!"{← captureWhat h y}: the copies of {← readName y} of modules \
    {← readName m₁} and {← readName m₂} are not one constant (not two proofs of one statement)")

/-- con-leche: ConLeche/Driver/Reach.lean:408-440 agreeCheck
Whether a status is `no` (`yes := false`) or `yes`. -/
def statusIs (p : ProofStatus) (yes : Bool) : Bool :=
  match p with
  | .yes => yes
  | .no => !yes
  | .infer => false

/-- con-leche: ConLeche/Driver/Reach.lean:408-440 agreeCheck
**Two copies of `y` agree**. -/
def agreeCheck (fs : OleanFs) (pk : OleanPins) (sp : Roots) (env : ReachEnv) (c : ReachCache)
    (h y : NIdx) (s₁ s₂ : Spot) : AM ReachCache := do
  if s₁.part.mod == s₂.part.mod then return c
  if s₂.pos.skipped then
    fail (.invalid s!"{← captureWhat h y}: its copy of {← readName y}, of module \
      {← readName s₂.part.mod}, is unsafe or partial")
  let (c, cv₁, k₁) ← stmtAt fs pk sp c s₁
  let (c, cv₂, k₂) ← stmtAt fs pk sp c s₂
  if !(cv₁.levelParams == cv₂.levelParams && cv₁.type == cv₂.type) then
    fail (← agreeBad h y s₁.part.mod s₂.part.mod)
  let (c, p₁) ← proofStatus fs pk sp env c s₁ k₁
  let (c, p₂) ← proofStatus fs pk sp env c s₂ k₂
  if statusIs p₁ false || statusIs p₂ false then fail (← agreeBad h y s₁.part.mod s₂.part.mod)
  let c := { c with partners := ← partnerReads c.partners s₂.part.mod cv₂.type }
  if !(statusIs p₁ true || statusIs p₂ true) then
    pure { c with pending := c.pending.push (← captureWhat h y, y, cv₁) }
  else pure c

/-- con-leche: ConLeche/Driver/Reach.lean:442-476 clashAgree
A clash's copies the index locates, as spots with their statements and kinds. -/
def clashSpots (pk : OleanPins) (env : ReachEnv) (cl : Clash) : List (Spot × StmtRec × CKindF NIdx Unit) :=
  let ld := env.wr.loads
  cl.copies.toList.filterMap fun (cp, cv, k) =>
    (env.wr.index.at cp).map fun q => ((⟨⟨ld.nameAt pk cp.mod, ld.levelAt cp.mod⟩, q⟩ : Spot), cv, k)

/-- con-leche: ConLeche/Driver/Reach.lean:442-476 clashAgree
`statuses`: whether one spot is `no`, one `yes`. -/
def clashStatuses (fs : OleanFs) (pk : OleanPins) (sp : Roots) (env : ReachEnv) :
    ReachCache → Bool → Bool → List (Spot × StmtRec × CKindF NIdx Unit) → AM (ReachCache × Bool × Bool)
  | c, no, yes, [] => pure (c, no, yes)
  | c, no, yes, (s, _, k) :: rest => do
    let (c, p) ← proofStatus fs pk sp env c s k
    clashStatuses fs pk sp env c (no || statusIs p false) (yes || statusIs p true) rest

/-- con-leche: ConLeche/Driver/Reach.lean:442-476 clashAgree
One clash: its copies must be proofs of one statement; its name onto `acc`. -/
def clashAgreeOne (fs : OleanFs) (pk : OleanPins) (sp : Roots) (env : ReachEnv) (c : ReachCache)
    (cl : Clash) (acc : Array NIdx) : AM (ReachCache × Array NIdx) := do
  let spots := clashSpots pk env cl
  let (c, no, yes) ← clashStatuses fs pk sp env c false false spots
  if no then
    let ms ← spots.mapM fun s => readName s.1.part.mod
    fail (.invalid s!"the loaded modules {ms} store {← readName cl.name}, not as one constant \
      (not proofs of one statement)")
  if yes then return (c, acc.push cl.name)
  match spots with
  | (_, cv, _) :: _ =>
    let why := s!"two loaded modules store {← Frontend.nameText cl.name}"
    pure ({ c with pending := c.pending.push (why, cl.name, cv) }, acc.push cl.name)
  | [] => pure (c, acc)

/-- con-leche: ConLeche/Driver/Reach.lean:442-476 clashAgree
**The clash rule**; every clashing name returned, to be reached. -/
def clashAgree (fs : OleanFs) (pk : OleanPins) (sp : Roots) (env : ReachEnv) :
    ReachCache → List Clash → Array NIdx → AM (ReachCache × Array NIdx)
  | c, [], acc => pure (c, acc)
  | c, cl :: cls, acc => do
    let (c, acc) ← clashAgreeOne fs pk sp env c cl acc
    clashAgree fs pk sp env c cls acc

/-! ## The capture check -/

/-- con-leche: ConLeche/Driver/Reach.lean:480-486 inExported
**Is `y` in module `m`'s exported part** (`m` loaded at `level`). -/
def inExported (fs : OleanFs) (pk : OleanPins) (sp : Roots) (env : ReachEnv) (c : ReachCache)
    (m : NIdx) (level : OLeanLevel) (y : NIdx) : AM (ReachCache × Bool) := do
  if level == .exported then return (c, true)
  let k : PartKey := ⟨m, .exported⟩
  let c ← lookOf fs pk sp env c k
  pure (c, (← lookAt c k y).isSome)

/-- con-leche: ConLeche/Driver/Reach.lean:488-531 captureOne
Whether `h`'s public-import closure holds the module at load position `i`. -/
def pubHas (env : ReachEnv) (h : NIdx) (i : Nat) : Bool :=
  match env.wr.loads.index[h]? with
  | some hi => ((env.wr.pub[hi]?).map (·.has i)).getD false
  | none => false

/-- con-leche: ConLeche/Driver/Reach.lean:488-531 captureOne
`module {h} reads {y}, which {what}`. -/
def readsWhich (h y : NIdx) (what : String) : AM CheckError := do
  pure (.invalid s!"module {← readName h} reads {← readName y}, which {what}")

/-- con-leche: ConLeche/Driver/Reach.lean:488-531 captureOne
A located or loaded copy `s₁` of `y` against the copy `h`'s view holds. -/
def captureAgainst (fs : OleanFs) (pk : OleanPins) (sp : Roots) (env : ReachEnv) (c : ReachCache)
    (h y : NIdx) (s₁ : Spot) : AM ReachCache := do
  match ← locate fs pk sp env c h y with
  | (_, none) => fail (← readsWhich h y "its view does not hold")
  | (c, some s₂) => agreeCheck fs pk sp env c h y s₁ s₂

/-- con-leche: ConLeche/Driver/Reach.lean:488-531 captureOne
A name's located copy. -/
def locatedAt (c : ReachCache) (y : NIdx) : Option Spot := c.located[y]?

/-- con-leche: ConLeche/Driver/Reach.lean:488-531 captureOne
**The capture check of one read** `y` of a record of home `h`, and the completion of a name the
index lacks. -/
def captureOne (fs : OleanFs) (pk : OleanPins) (sp : Roots) (env : ReachEnv) (c : ReachCache)
    (h y : NIdx) : AM ReachCache := do
  if env.own.contains y then
    fail (.invalid s!"name capture: module {← readName h} reads {← readName y}, which \
      {← readName env.mod} declares")
  match importerSpot pk env y with
  | some (i, s₁) =>
    if s₁.part.mod == h then return c
    let (c, short) ← if pubHas env h i then inExported fs pk sp env c s₁.part.mod s₁.part.level y
      else pure (c, false)
    if short then return c
    captureAgainst fs pk sp env c h y s₁
  | none =>
    match locatedAt c y with
    | some s₁ =>
      if s₁.part.mod == h then return c
      captureAgainst fs pk sp env c h y s₁
    | none =>
      match ← locate fs pk sp env c h y with
      | (_, none) => fail (← readsWhich h y "no module of its view holds")
      | (c, some s) =>
        let (c, p) ← privSpot fs pk sp env c s
        pure { c with located := c.located.insert y p, completed := c.completed.push (y, h) }

/-- con-leche: ConLeche/Driver/Reach.lean:533-558 storedNamesOk
`a record read from module {h} stores {n}, which the context reads from module {k}`. -/
def storedBad (h n k : NIdx) : AM CheckError := do
  pure (.invalid s!"a record read from module {← readName h} stores {← readName n}, which the \
    context reads from module {← readName k}")

/-- con-leche: ConLeche/Driver/Reach.lean:533-558 storedNamesOk
One name a record of home `h` stores, against the importer's copies. -/
def storedNameOk (fs : OleanFs) (pk : OleanPins) (sp : Roots) (env : ReachEnv) (c : ReachCache)
    (h n : NIdx) : AM ReachCache := do
  match importerSpot pk env n with
  | some (_, s) => if s.part.mod == h then pure c else fail (← storedBad h n s.part.mod)
  | none =>
    match locatedAt c n with
    | some s => if s.part.mod == h then pure c else fail (← storedBad h n s.part.mod)
    | none =>
      let k := privKey h
      let c ← lookOf fs pk sp env c k
      match ← lookAt c k n with
      | some q => pure { c with located := c.located.insert n ⟨k, q⟩ }
      | none => fail (.invalid s!"module {← readName h}: a record of its private part stores \
          {← readName n}, which its private part does not hold")

/-- con-leche: ConLeche/Driver/Reach.lean:533-558 storedNamesOk
**The names a record stores, against the importer's copies**. -/
def storedNamesOk (fs : OleanFs) (pk : OleanPins) (sp : Roots) (env : ReachEnv) (h : NIdx) :
    ReachCache → List NIdx → AM ReachCache
  | c, [] => pure c
  | c, n :: ns => do
    let c ← storedNameOk fs pk sp env c h n
    storedNamesOk fs pk sp env h c ns

/-- con-leche: ConLeche/Driver/Reach.lean:560-566 clashPartners
One stored name's copies, if it clashes, each statement's names as reads of the copy's
module. -/
def clashPartnersOne (env : ReachEnv) (acc : Array (NIdx × NIdx)) (n : NIdx) : AM (Array (NIdx × NIdx)) :=
  match env.copies[n]? with
  | none => pure acc
  | some cs => cs.toList.foldlM (fun acc (k, cv) => partnerReads acc k cv.type) acc

/-- con-leche: ConLeche/Driver/Reach.lean:560-566 clashPartners
**Every copy of a clashing name the context stores**, onto `acc`. -/
def clashPartners (env : ReachEnv) (acc : Array (NIdx × NIdx)) (ns : List NIdx) : AM (Array (NIdx × NIdx)) :=
  ns.foldlM (clashPartnersOne env) acc

/-- con-leche: ConLeche/Driver/Reach.lean:568-575 captureAll
The capture check of every read of a record. -/
def captureAll (fs : OleanFs) (pk : OleanPins) (sp : Roots) (env : ReachEnv) (h : NIdx) :
    ReachCache → List NIdx → AM ReachCache
  | c, [] => pure c
  | c, y :: ys => do
    let c ← captureOne fs pk sp env c h y
    captureAll fs pk sp env h c ys

/-- con-leche: ConLeche/Driver/Reach.lean:577-584 capturePairs
**The partners' reads checked**. -/
def capturePairs (fs : OleanFs) (pk : OleanPins) (sp : Roots) (env : ReachEnv) :
    ReachCache → List (NIdx × NIdx) → AM ReachCache
  | c, [] => pure c
  | c, (h, y) :: ps => do
    let c ← captureOne fs pk sp env c h y
    capturePairs fs pk sp env c ps

/-! ## A record read -/

/-- con-leche: ConLeche/Driver/Reach.lean:588-595 recBlocksAt
One recursor's location onto the block of its first member. -/
def recBlocksAdd (m : Std.HashMap NIdx (Array Nat)) (l : Nat) (k : CKindF NIdx Unit) :
    Std.HashMap NIdx (Array Nat) :=
  match k with
  | .recur (a :: _) .. => m.insert a (((m[a]?).getD #[]).push l)
  | _ => m

/-- con-leche: ConLeche/Driver/Reach.lean:588-595 recBlocksAt
**A part's recursors' locations by their block's first member**, in the part's order. -/
def recBlocksAt (pk : OleanPins) (r : Region) :
    Std.HashMap NIdx (Array Nat) → List NamePosition → AM (Option (Std.HashMap NIdx (Array Nat)))
  | m, [] => pure (some m)
  | m, q :: qs => do
    if q.tag == 7 then
      match ← kindNamesAt pk r q.loc with
      | none => pure none
      | some k => recBlocksAt pk r (recBlocksAdd m q.loc k) qs
    else recBlocksAt pk r m qs

/-- con-leche: ConLeche/Driver/Reach.lean:597-608 recBlocksOf
A part's recursors' locations by their block's first member, read once. -/
def recBlocksOf (fs : OleanFs) (pk : OleanPins) (sp : Roots) (env : ReachEnv) (c : ReachCache)
    (k : PartKey) : AM ReachCache := do
  if c.recBlocks.contains k then return c
  let c ← tableOf fs pk sp env c k
  let (c, r, st) ← takePart fs pk sp c k
  let res ← match tableGet env.wr c k with
    | none => fail cacheLost
    | some t => recBlocksAt pk r {} t.consts.toList
  let (c, m) ← putPart c k r (st, res)
  pure { c with recBlocks := c.recBlocks.insert k m }

/-- con-leche: ConLeche/Driver/Reach.lean:610-614 groupCtorNames
The constructors a group's types list. -/
def groupCtorNames (tys : List (CEntryF NIdx EIdx)) : List NIdx :=
  tys.flatMap fun t => match t.kind with
    | .induct _ _ _ cs .. => cs
    | _ => []

/-- con-leche: ConLeche/Driver/Reach.lean:616-618 groupRecLocs
The locations of a group's recursors in a part, by its first member. -/
def groupRecLocs (rb : Std.HashMap NIdx (Array Nat)) (all : List NIdx) : List Nat :=
  ((all.head?.bind (rb[·]?)).getD #[]).toList

/-- con-leche: ConLeche/Driver/Reach.lean:620-627 groupMerged
Whether a constant is kept among a group's rest. -/
def groupKeeps (e : CEntryF NIdx EIdx) (all : List NIdx) : Bool :=
  match e.kind with
  | .recur all' .. => all' == all
  | _ => true

/-- con-leche: ConLeche/Driver/Reach.lean:620-627 groupMerged
A group's constants as a merge. -/
def groupMerged (pk : OleanPins) (t : CEntryF NIdx EIdx) (tys rest : List (CEntryF NIdx EIdx))
    (all : List NIdx) : Merged :=
  mergedOfList pk ((t :: tys ++ rest.filter (groupKeeps · all)).map (fun c => { c })).toArray

/-- con-leche: ConLeche/Driver/Reach.lean:629-667 groupAt
The locations of some names in a part's lookup, `none` where one is missing. -/
def lookLocs (c : ReachCache) (k : PartKey) (ns : List NIdx) : AM (Option (List Nat)) :=
  match c.looks[k]? with
  | none => fail cacheLost
  | some l => pure (ns.mapM fun n => (l[n]?).map (·.loc))

/-- con-leche: ConLeche/Driver/Reach.lean:629-667 groupAt
A group's recursors' locations in a cached part. -/
def recLocsAt (c : ReachCache) (k : PartKey) (all : List NIdx) : AM (List Nat) :=
  match c.recBlocks[k]? with
  | none => fail cacheLost
  | some rb => pure (groupRecLocs rb all)

/-- con-leche: ConLeche/Driver/Reach.lean:629-667 groupAt
**Type `n`'s group, read from one part**: `none` where the part lacks a member or a
constructor. -/
def groupAt (fs : OleanFs) (pk : OleanPins) (sp : Roots) (env : ReachEnv) (c : ReachCache)
    (k : PartKey) (n : NIdx) : AM (ReachCache × Option IDeclaration) := do
  let c ← loadPart fs pk sp c k
  let c ← lookOf fs pk sp env c k
  let some q ← lookAt c k n | return (c, none)
  let (c, t) ← partEntry fs pk sp c k q.loc
  let all ← match t.kind with
    | .induct _ _ all .. => pure all
    | _ => fail (.invalid s!"module {← readName k.mod}: {← readName n} is not an inductive type")
  let some mqs ← lookLocs c k all | return (c, none)
  let (c, tys) ← partEntries fs pk sp c k mqs
  let some cqs ← lookLocs c k (groupCtorNames tys) | return (c, none)
  let c ← recBlocksOf fs pk sp env c k
  let rl ← recLocsAt c k all
  let (c, rest) ← partEntries fs pk sp c k (cqs ++ rl)
  let d ← groupRecord pk (groupMerged pk t tys rest all) n
  pure (c, some d)

/-- con-leche: ConLeche/Driver/Reach.lean:669-676 groupOfKind
The type whose group presents a copy of `x` of kind `k`. -/
def groupOfKind (x : NIdx) : CKindF NIdx Unit → Option NIdx
  | .induct .. => some x
  | .ctor ind .. => some ind
  | .recur all .. => some (all.headD x)
  | _ => none

/-- con-leche: ConLeche/Driver/Reach.lean:678-691 stmtRecord
A statement as an axiom's record. -/
def axiomOf (cv : StmtRec) : IDeclaration := .axiomDecl ⟨cv.name, cv.levelParams, cv.type⟩

/-- con-leche: ConLeche/Driver/Reach.lean:678-691 stmtRecord
**A copy presented as its statement**. -/
def stmtRecord (fs : OleanFs) (pk : OleanPins) (sp : Roots) (env : ReachEnv) (c : ReachCache)
    (s : Spot) (cv : StmtRec) : AM (ReachCache × IDeclaration × NIdx) := do
  let h := s.part.mod
  let ops ← reduceOpNames
  if !ops.contains cv.name then return (c, axiomOf cv, h)
  let (c, p) ← privSpot fs pk sp env c s
  if p.pos.tag == 0 || p.pos.tag == 3 then pure (c, axiomOf cv, h)
  else fail (.invalid s!"module {← readName h} declares {← readName cv.name}, a compiler-trust \
    name, as neither an opaque constant nor an axiom")

/-- con-leche: ConLeche/Driver/Reach.lean:693-729 readRecord
The copy presenting `x`: the importer's, else a completion's located copy (`true`). -/
def recordSpot (pk : OleanPins) (env : ReachEnv) (c : ReachCache) (x : NIdx) : Option (Spot × Bool) :=
  match importerSpot pk env x with
  | some (_, s) => some (s, false)
  | none => (locatedAt c x).map (·, true)

/-- con-leche: ConLeche/Driver/Reach.lean:693-729 readRecord
**The record presenting `x`, and its home**. -/
def readRecord (fs : OleanFs) (pk : OleanPins) (sp : Roots) (env : ReachEnv) (c : ReachCache)
    (x : NIdx) : AM (ReachCache × IDeclaration × NIdx) := do
  let some (s, completed) := recordSpot pk env c x
    | fail (.internal s!"the reach pushed {← readName x}, which nothing locates")
  let h := s.part.mod
  if s.pos.skipped then
    fail (.invalid s!"a context record reads {← readName x} of {← readName h}, which is unsafe \
      or partial")
  let (c, cv, k) ← stmtAt fs pk sp c s
  match groupOfKind x k with
  | some n =>
    match ← groupAt fs pk sp env c (privKey h) n with
    | (c, some d) => pure (c, d, h)
    | (_, none) => fail (.invalid s!"module {← readName h}: the group of {← readName n} lacks a \
        member or a constructor")
  | none =>
    match k with
    | .defn .. =>
      if completed then return ← stmtRecord fs pk sp env c s cv
      let (c, e) ← partEntry fs pk sp c s.part s.pos.loc
      pure (c, ← recordOfEntry e, h)
    | .quot q => pure (c, ← recordOfEntry ⟨cv.name, cv.levelParams, cv.type, .quot q⟩, h)
    | _ => stmtRecord fs pk sp env c s cv

/-! ## The worklist -/

/-- con-leche: ConLeche/Driver/Reach.lean:735-744 ReachLog
**The reach's logical state**; the stack's top first. -/
structure ReachLog where
  seen : Std.HashSet NIdx
  stored : Std.HashSet NIdx
  ctx : Array IDeclaration
  homes : Array NIdx
  reads : Array (List NIdx)
  stack : List NIdx

/-- con-leche: ConLeche/Driver/Reach.lean:746-752 pushNames
Push the names not seen yet. -/
def pushNames (seen : Std.HashSet NIdx) (stack : List NIdx) : List NIdx → Std.HashSet NIdx × List NIdx
  | [] => (seen, stack)
  | y :: ys =>
    if seen.contains y then pushNames seen stack ys
    else pushNames (seen.insert y) (y :: stack) ys

/-- con-leche: ConLeche/Driver/Reach.lean:754-758 ReachLog.add
**A record added**: its names `ns` stored, what it reads (`rd`) pushed. -/
def ReachLog.add (L : ReachLog) (d : IDeclaration) (h : NIdx) (ns rd : List NIdx) : ReachLog :=
  let (seen, stack) := pushNames L.seen L.stack rd
  { seen, stored := ns.foldl (fun s n => s.insert n) L.stored,
    ctx := L.ctx.push d, homes := L.homes.push h, reads := L.reads.push rd, stack }

/-- con-leche: ConLeche/Driver/Reach.lean:760-763 ReachLog.init
**The worklist's start**. -/
def ReachLog.init (rs : List NIdx) : ReachLog :=
  let p := pushNames {} [] rs
  { seen := p.1, stored := {}, ctx := #[], homes := #[], reads := #[], stack := p.2 }

/-- con-leche: ConLeche/Driver/Reach.lean:765-776 missingError
Why the record read for `x` does not store it (`ns`: its names). -/
def missingError (d : IDeclaration) (ns : List NIdx) (x h : NIdx) : AM CheckError := do
  let xs ← readName x
  let hs ← readName h
  match d with
  | .indDecl .. =>
    if ns.isEmpty then
      pure (.notImplemented s!"the inductive group of {xs}, read from {hs}: a group the \
        recogniser does not read")
    else pure (.invalid s!"the group read for {xs} from {hs} does not declare it")
  | .axiomDecl cv =>
    if cv.name == (← pinSorryAx) then pure (.notImplemented s!"a context record reads {xs} (sorryAx)")
    else pure (.invalid s!"the record read for {xs} from {hs} does not declare it")
  | _ => pure (.invalid s!"the record read for {xs} from {hs} does not declare it")

/-- con-leche: ConLeche/Driver/Reach.lean:778-782 clashCopiesOf
**The copies of every name two loaded modules hold**, by name. -/
def clashCopiesOf (pk : OleanPins) (wr : WorkerReads) : Std.HashMap NIdx (Array (NIdx × StmtRec)) :=
  wr.clashes.foldl (fun m cl =>
    m.insert cl.name (cl.copies.map fun (cp, cv, _) => (wr.loads.nameAt pk cp.mod, cv))) {}

/-- con-leche: ConLeche/Driver/Reach.lean:784-787 inRecord
A failed read of the record of `x`, read from `h`, names the record. -/
def inRecord (x h : NIdx) : CheckError → AM CheckError
  | .invalid m => do pure (.invalid s!"the record of {← readName x}, read from {← readName h}: {m}")
  | e => pure e

/-- con-leche: none — an action's failure as a value -/
def catchE {α : Type} (x : AM α) : AM (Except CheckError α) := fun s =>
  match x s with
  | .ok (a, s') => .ok (.ok a, s')
  | .error e => .ok (.error e, s)

/-- con-leche: ConLeche/Driver/Reach.lean:789-826 reachGo
Whether a record stores a name already stored. -/
def anyStored (stored : Std.HashSet NIdx) (ns : List NIdx) : Bool := ns.any stored.contains

/-- con-leche: ConLeche/Driver/Reach.lean:789-826 reachGo
The worklist's step at an empty stack: the partners' reads checked and pushed. -/
def reachPartners (fs : OleanFs) (pk : OleanPins) (sp : Roots) (env : ReachEnv) (L : ReachLog)
    (c : ReachCache) : AM (ReachLog × ReachCache) := do
  let ps := c.partners.toList
  let c ← capturePairs fs pk sp env { c with partners := #[] } ps
  let (seen, stack) := pushNames L.seen [] (ps.map (·.2))
  pure ({ L with seen, stack }, c)

/-- con-leche: ConLeche/Driver/Reach.lean:789-826 reachGo
The worklist's step at a name `x` popped (`L.stack` already without it). -/
def reachRead (fs : OleanFs) (pk : OleanPins) (sp : Roots) (env : ReachEnv) (L : ReachLog)
    (c : ReachCache) (x : NIdx) : AM (ReachLog × ReachCache) := do
  if L.stored.contains x then return (L, c)
  let (c, d, h) ← readRecord fs pk sp env c x
  let ns ← declNames d
  if !ns.contains x then fail (← missingError d ns x h)
  if anyStored L.stored ns then
    fail (.invalid s!"two context records store a name of {← readName x}'s record (of {← readName h})")
  let rd ← recordReads d
  let c ← match ← catchE (captureAll fs pk sp env h c rd) with
    | .ok c => pure c
    | .error e => fail (← inRecord x h e)
  let c ← storedNamesOk fs pk sp env h c ns
  let L := L.add d h ns rd
  pure (L, { c with partners := ← clashPartners env c.partners ns })

/-- con-leche: ConLeche/Driver/Reach.lean:789-826 reachGo
**The reach's worklist**; each step spends one fuel. -/
def reachGo (fs : OleanFs) (pk : OleanPins) (sp : Roots) (env : ReachEnv) :
    Nat → ReachLog → ReachCache → AM (ReachLog × ReachCache)
  | fuel, L, c =>
    match L.stack with
    | [] =>
      if c.partners.isEmpty then pure (L, c) else
      match fuel with
      | 0 => fail (.internal "the reach ran out of steps")
      | fuel + 1 => do
        let (L, c) ← reachPartners fs pk sp env L c
        reachGo fs pk sp env fuel L c
    | x :: rest =>
      match fuel with
      | 0 => fail (.internal "the reach ran out of steps")
      | fuel + 1 => do
        let (L, c) ← reachRead fs pk sp env { L with stack := rest } c x
        reachGo fs pk sp env fuel L c

/-! ## The validation and the flags -/

/-- con-leche: ConLeche/Driver/Reach.lean:830-837 validateCtx
The malformed record named, with its home. -/
def validateBad (d : IDeclaration) (h : Option NIdx) : AM CheckError := do
  match h with
  | none => pure (.internal "a malformed context record not found")
  | some h =>
    pure (.invalid s!"the record {← declLabel d} of module {← readName h} is malformed (a free or \
      loose bound variable, an undeclared universe parameter, a nested rule's datum, a table's \
      bodies or a literal's shape)")

/-- con-leche: ConLeche/Driver/Reach.lean:830-837 validateCtx
**Every context record validated**, the first failure named. -/
def validateCtx (ds : List IDeclaration) (hs : Array NIdx) (i : Nat) : AM Unit :=
  match ds with
  | [] => pure ()
  | d :: ds => do
    if ← recordOk d then validateCtx ds hs (i + 1)
    else fail (← validateBad d hs[i]?)

/-- con-leche: ConLeche/Driver/Reach.lean:839-843 typeIsPropC
**Is a statement's type a proposition**, by the kernel's inference at `fe`. -/
def typeIsPropC (fe : IFEnv) (cv : StmtRec) : AM Bool := do
  let jsty ← inferTypeCore .verified fe checkFuel 0 cv.type
  let u ← ensureSortCore .verified fe checkFuel 0 jsty
  let z ← zeroLevel
  liftFueled "level comparison" (← lvlEq? u z)

/-- con-leche: ConLeche/Driver/Reach.lean:845-848 ctxPart
**Each context name's first record**, by its position. -/
def firstOwner (ds : List IDeclaration) : AM (Std.HashMap NIdx Nat) := do
  let (m, _) ← ds.foldlM (fun (acc : Std.HashMap NIdx Nat × Nat) d => do
    let ns ← declNames d
    pure (ns.foldl (fun m n => if m.contains n then m else m.insert n acc.2) acc.1, acc.2 + 1))
    ({}, 0)
  pure m

/-- con-leche: ConLeche/Driver/Reach.lean:845-848 ctxPart
The position whose view is the part of the context below `y`. -/
def partPos (m : Std.HashMap NIdx Nat) (n : Nat) (y : NIdx) : Nat := m[y]?.getD n

/-- con-leche: ConLeche/Driver/Reach.lean:850-865 inferFlags
One recorded statement inferred. -/
def inferOne (fe : IFEnv) (what : String) (y : NIdx) (cv : StmtRec) : AM Unit := do
  let ok ← if ← exprOk cv.levelParams 0 cv.type then constsResolveFFast fe cv.type else pure false
  if !ok then fail (.invalid s!"the statement of {← readName y} reads a name the context does not \
    store before it")
  if ← typeIsPropC fe cv then pure ()
  else fail (.invalid s!"{what}: the copies of {← readName y} of two modules are not one constant \
    (its type is not a proposition)")

/-- con-leche: ConLeche/Driver/Reach.lean:850-865 inferFlags
The recorded statements inferred, each in its own bracket. -/
def inferAll (I : IStreamIndex) (owner : Std.HashMap NIdx Nat) (n : Nat) :
    List (String × NIdx × StmtRec) → AM Unit
  | [] => pure ()
  | (what, y, cv) :: rest => do
    enterScratch
    inferOne (I.view (partPos owner n y)) what y cv
    dropScratch
    inferAll I owner n rest

/-- con-leche: ConLeche/Driver/Reach.lean:850-865 inferFlags
**The inferred flags**, at the frozen index `I` of `ctx ++ own`. -/
def inferFlags (I : IStreamIndex) (ctx : Array IDeclaration) (pending : Array (String × NIdx × StmtRec)) :
    AM Unit := do
  if pending.isEmpty then return ()
  enterScratch
  let owner ← firstOwner ctx.toList
  dropScratch
  inferAll I owner ctx.size pending.toList

/-! ## The read order -/

/-- con-leche: ConLeche/Driver/Reach.lean:869-872 ownerMap
**Each context name's record**, by its position (the last record kept). -/
def ownerMap (ds : List IDeclaration) : AM (Std.HashMap NIdx Nat) := do
  let (m, _) ← ds.foldlM (fun (acc : Std.HashMap NIdx Nat × Nat) d => do
    let ns ← declNames d
    pure (ns.foldl (fun m n => m.insert n acc.2) acc.1, acc.2 + 1)) ({}, 0)
  pure m

/-- con-leche: ConLeche/Driver/Reach.lean:874-877 SortSt
**The read order's state**. -/
structure SortSt where
  order : Array Nat := #[]
  placed : Std.HashSet Nat := {}

/-- con-leche: ConLeche/Driver/Reach.lean:879-901 sortVisit
The records at positions `i` and `j` read each other through `y`. -/
def sortCycle (ds : Array IDeclaration) (i j : Nat) (y : NIdx) : AM CheckError := do
  let a ← match ds[i]? with | some d => declLabel d | none => pure ""
  let b ← match ds[j]? with | some d => declLabel d | none => pure ""
  pure (.invalid s!"the context records {a} and {b} read each other (through {← readName y})")

mutual
/-- con-leche: ConLeche/Driver/Reach.lean:879-901 sortVisit
**The record at position `i` placed after its reads** `ys` (a post-order walk). -/
def sortVisit (ds : Array IDeclaration) (rds : Array (List NIdx)) (owner : Std.HashMap NIdx Nat) :
    Nat → Nat → Std.HashSet Nat → List NIdx → SortSt → AM SortSt
  | 0, _, _, _, _ => fail (.internal "the read order ran out of steps")
  | fuel + 1, i, path, ys, st => do
    let st ← sortVisitList ds rds owner fuel i path ys st
    pure { order := st.order.push i, placed := st.placed.insert i }

/-- con-leche: ConLeche/Driver/Reach.lean:879-901 sortVisit
The reads of record `i`, in order, at depth fuel `fuel + 1`. -/
def sortVisitList (ds : Array IDeclaration) (rds : Array (List NIdx)) (owner : Std.HashMap NIdx Nat)
    (fuel i : Nat) (path : Std.HashSet Nat) : List NIdx → SortSt → AM SortSt
  | [], st => pure st
  | y :: ys, st => do
    match owner[y]? with
    | none => fail (.internal s!"a context record reads {← readName y}, which no context record stores")
    | some j =>
      if j == i || st.placed.contains j then sortVisitList ds rds owner fuel i path ys st
      else if path.contains j then fail (← sortCycle ds i j y)
      else
        let st ← sortVisit ds rds owner fuel j (path.insert j) (rds.getD j []) st
        sortVisitList ds rds owner fuel i path ys st
end

/-- con-leche: ConLeche/Driver/Reach.lean:903-912 sortFrom
Every record placed, in position order, each after its reads. -/
def sortFrom (ds : Array IDeclaration) (rds : Array (List NIdx)) (owner : Std.HashMap NIdx Nat)
    (fuel : Nat) : List Nat → SortSt → AM SortSt
  | [], st => pure st
  | i :: is, st => do
    if st.placed.contains i then sortFrom ds rds owner fuel is st else
    let st ← sortVisit ds rds owner fuel i (({} : Std.HashSet Nat).insert i) (rds.getD i []) st
    sortFrom ds rds owner fuel is st

/-- con-leche: ConLeche/Driver/Reach.lean:914-918 readOrder
**The context's records in read order**. -/
def readOrder (ds : Array IDeclaration) (rds : Array (List NIdx)) : AM (Array Nat) := do
  let owner ← ownerMap ds.toList
  pure (← sortFrom ds rds owner (ds.size + 1) (List.range ds.size) {}).order

/-! ## The reach -/

/-- con-leche: ConLeche/Driver/Reach.lean:922-929 Reach
**What the reach gives**: the context's records with their homes, the completed names with
the homes that located them, its counts, and the statements `inferFlags` infers. -/
structure Reach where
  ctx : Array IDeclaration
  homes : Array NIdx
  completed : Array (NIdx × NIdx)
  searches : Nat
  inferred : Nat
  pending : Array (String × NIdx × StmtRec)

/-- con-leche: ConLeche/Driver/Reach.lean:937-968 reachWith
The roots and the clashing names, the own names left out. -/
def reachRoots (own : Std.HashSet NIdx) (roots extra : Array NIdx) : List NIdx :=
  (roots ++ extra).toList.filter (!own.contains ·)

/-- con-leche: ConLeche/Driver/Reach.lean:937-968 reachWith
The records at the read order's positions, with their homes. -/
def inReadOrder (L : ReachLog) (o : Array Nat) : Array IDeclaration × Array NIdx :=
  o.foldl (fun (acc : Array IDeclaration × Array NIdx) j =>
    match L.ctx[j]?, L.homes[j]? with
    | some d, some h => (acc.1.push d, acc.2.push h)
    | _, _ => acc) (#[], #[])

/-- con-leche: ConLeche/Driver/Reach.lean:937-968 reachWith
**The reach of module `m`** from the names its own records read: upstream's `reachWith` up to
its flags step, which is `inferFlags`, run after the worker's freeze. -/
def reach (fs : OleanFs) (pk : OleanPins) (sp : Roots) (m : NIdx) (wr : WorkerReads)
    (own : Std.HashSet NIdx) (roots : Array NIdx) : AM Reach := do
  let env : ReachEnv := { mod := m, wr, own, copies := clashCopiesOf pk wr }
  let (c, extra) ← clashAgree fs pk sp env {} wr.clashes.toList #[]
  let rs := reachRoots own roots extra
  match rs.find? (!wr.index.first.contains ·) with
  | some x => fail (← readsWhich m x "no module it loads holds")
  | none =>
    let fuel := wr.index.first.size + wr.index.more.size + (1 <<< 24)
    let (L, c) ← reachGo fs pk sp env fuel (ReachLog.init rs) c
    let o ← readOrder L.ctx L.reads
    let (ctx, homes) := inReadOrder L o
    validateCtx ctx.toList homes 0
    pure { ctx, homes, completed := c.completed, searches := c.searches,
           inferred := c.pending.size, pending := c.pending }

end ConRon.Arena.Modular
