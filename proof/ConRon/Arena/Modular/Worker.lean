/-
# `ConRon.Arena.Modular.Worker` — the worker: one module checked against its context (task #166)

The twin of `frontend/modular/worker.rs`, con-leche's `ConLeche/Driver/Worker.lean`: the home
(`homeOf`), the reads (`workerReads`), the own records (`ownRecords`), the reach's roots
(`rootsAt`), the reach, the context's names distinct, a compared challenge's copies
(`copiesOk`) and holes (`ownHolesOk`), and the ground hoist, in `workerRead`.  The Rust's
helpers are twinned one for one.  A name set is `Std.HashSet NIdx`; the load's constants are
indexed by name for `ownUses` (`ownUsesOf`, upstream's `find?`); a copied block's recursors read
against one layer of every context constant (`ctxLayer`, upstream's `ctxConst`).
-/
module

public import ConRon.Arena.Modular.Reach
public import ConRon.Arena.Frontend.NatOpGround
public import ConRon.Arena.Frontend.Olean.Records
public import ConRon.Arena.Frontend.Olean.Group
public import ConRon.Arena.Frontend.Olean.Module
public import ConRon.Arena.Frontend.Compare
public import ConRon.Arena.Inductives.IotaRead
public import ConRon.Arena.Inductives.Positivity

@[expose] public section

namespace ConRon.Arena.Modular

open ConLeche
open ConRon.Arena.Frontend.Olean
open ConRon.Arena.Frontend (recKey recKind)
open ConLeche.Frontend.Olean (Expo OLeanLevel Roots)

/-- con-leche: ConLeche/Frontend/Olean/Files.lean:385-394 homeOf
**A module's home**: its private view loaded (`loadView` at module index 0) and its three
parts checked against each other (`checkViews`). -/
def homeOf (pk : OleanPins) (m : NIdx) (f : ConLeche.Frontend.Olean.ModFiles) : AM (Loaded × Array Expo) := do
  let l ← loadView pk 0 m f
  let expo ← checkViews pk m f l
  pure (l, expo)

/-- con-leche: ConLeche/Driver/Worker.lean:44-51 ownRecords
`l.constants.toList.filter (!·.skipped)`. -/
def unskipped (cs : Array CEntry) : Array CEntry := cs.filter (!·.skipped)

/-- con-leche: ConLeche/Driver/Worker.lean:44-51 ownRecords
**A module's own records**: its loaded constants, unsafe and partial ones left out, their
inductive groups checked (`blocksOk`), emitted from every one of them. -/
def ownRecords (pk : OleanPins) (l : Loaded) : AM (Except (CheckError × Nat) (Array IDeclaration)) := do
  let mg := mergedOfList pk (unskipped l.constants)
  blocksOk pk mg
  match ← declsOf (← emitAll pk mg mg.order) with
  | .error e => pure (.error e)
  | .ok p => pure (.ok p.decls)

/-- con-leche: ConLeche/Driver/Worker.lean:53-66 pinGround
`go`: one expression's constants into the walk's visited set and names. -/
def groundGo (x : Std.HashSet EIdx × Array NIdx) (e : EIdx) : AM (Std.HashSet EIdx × Array NIdx) :=
  ConRon.Arena.Frontend.usedConstsGo x.1 x.2 coreWalkFuel e

/-- con-leche: ConLeche/Driver/Worker.lean:53-66 pinGround
`es.foldl go x`. -/
def groundGoAll (x : Std.HashSet EIdx × Array NIdx) (es : List EIdx) :
    AM (Std.HashSet EIdx × Array NIdx) :=
  es.foldlM groundGo x

/-- con-leche: ConLeche/Driver/Worker.lean:53-66 pinGround
One statement: `go (st.1.foldl go x) st.2`. -/
def groundStmt (x : Std.HashSet EIdx × Array NIdx) (st : List EIdx × EIdx) :
    AM (Std.HashSet EIdx × Array NIdx) := do
  groundGo (← groundGoAll x st.1) st.2

/-- con-leche: ConLeche/Driver/Worker.lean:53-66 pinGround
The certificates' statements. -/
def groundStmts (x : Std.HashSet EIdx × Array NIdx) (c : NIdx) :
    AM (Std.HashSet EIdx × Array NIdx) := do
  (← divModCertStmts c).foldlM groundStmt x

/-- con-leche: ConLeche/Driver/Worker.lean:53-66 pinGround
One pin variant: its pinned defining expression, its certificates' proofs, then each type
pin's name and type. -/
def groundVariant (x : Std.HashSet EIdx × Array NIdx) (ps : INatOpPinSet) (c : NIdx) :
    AM (Std.HashSet EIdx × Array NIdx) := do
  let x ← groundGo x (← divModDeclPin ps c)
  let x ← groundGoAll x (← divModCertProofs ps c)
  (← divModTypePins ps c).foldlM (fun x p => groundGo (x.1, x.2.push p.1) p.2) x

/-- con-leche: ConLeche/Driver/Worker.lean:53-66 pinGround
**A certified operation's pin ground**, over every pin variant of `pins`; empty at every other
name. -/
def pinGround (pins : List INatOpPinSet) (c : NIdx) : AM (Array NIdx) := do
  if !(← natDivModNames).contains c then return #[]
  let eq ← pinEq
  let x ← groundStmts ({}, #[eq]) c
  pure (← pins.foldlM (fun x ps => groundVariant x ps c) x).2

/-- con-leche: ConLeche/Driver/Worker.lean:68-86 ownRoots
`fp`: every name a loaded constant's fast path reads. -/
def footprints (cs : Array CEntry) : AM (Std.HashSet NIdx) :=
  cs.foldlM (fun s c => do pure ((← pinFootprint c.c.name).foldl (fun s n => s.insert n) s)) {}

/-- con-leche: ConLeche/Driver/Worker.lean:68-86 ownRoots
`xs.filter (fun x => ix.first.contains x || !fp.contains x)` pushed onto `out`. -/
def pushUnpinned (out : Array NIdx) (ix : NameIndex) (fp : Std.HashSet NIdx) (xs : Array NIdx) :
    Array NIdx :=
  out ++ xs.filter fun x => ix.first.contains x || !fp.contains x

/-- con-leche: ConLeche/Driver/Worker.lean:68-86 ownRoots
`xs.filter ix.first.contains` pushed onto `out`. -/
def pushLoaded (out : Array NIdx) (ix : NameIndex) (xs : Array NIdx) : Array NIdx :=
  out ++ xs.filter ix.first.contains

/-- con-leche: ConLeche/Driver/Worker.lean:68-86 ownRoots
What each own record reads, filtered (`pushUnpinned`). -/
def recordsRoots (ix : NameIndex) (fp : Std.HashSet NIdx) (ds : Array IDeclaration) :
    AM (Array NIdx) :=
  ds.foldlM (fun out d => do pure (pushUnpinned out ix fp (← recordReads d).toArray)) #[]

/-- con-leche: ConLeche/Driver/Worker.lean:68-86 ownRoots
The pin ground of each own constant, filtered (`pushLoaded`), onto `out`. -/
def groundRoots (pins : List INatOpPinSet) (ix : NameIndex) (cs : Array CEntry) (out : Array NIdx) :
    AM (Array NIdx) :=
  cs.foldlM (fun out c => do
    if c.skipped then pure out else pure (pushLoaded out ix (← pinGround pins c.c.name))) out

/-- con-leche: ConLeche/Driver/Worker.lean:68-86 ownRoots
**The reach's roots**: what each own record reads, what each own constant's load read, and the
pin ground of each own certified operation that a loaded module holds.  `cs`: the load's
constants. -/
def ownRoots (pins : List INatOpPinSet) (ix : NameIndex) (cs : Array CEntry)
    (ds : Array IDeclaration) : AM (Array NIdx) := do
  let fp ← footprints cs
  let out ← recordsRoots ix fp ds
  let out := cs.foldl (fun out c => if c.skipped then out else pushUnpinned out ix fp c.uses) out
  groundRoots pins ix cs out

/-- con-leche: ConLeche/Driver/Worker.lean:88-95 ownUses
The index of a load's constants by name, the first of each. -/
def ownUsesAt (cs : Array CEntry) : Std.HashMap NIdx Nat :=
  (cs.foldl (fun (acc : Std.HashMap NIdx Nat × Nat) c =>
    (if acc.1.contains c.c.name then acc.1 else acc.1.insert c.c.name acc.2, acc.2 + 1))
    ({}, 0)).1

/-- con-leche: ConLeche/Driver/Worker.lean:88-95 ownUses
A theorem's load-read names: the first constant of its name's `uses`. -/
def ownUsesThm (cs : Array CEntry) (at_ : Std.HashMap NIdx Nat) (n : NIdx) : Option (Array NIdx) :=
  match at_[n]? with
  | some i => (cs[i]?).map (·.uses)
  | none => none

/-- con-leche: ConLeche/Driver/Worker.lean:88-95 ownUses
**What an own theorem's record mentions**, which its reference does not say: what the load
read off the file (the Rust's `impl UsedConsts for OwnUses`). -/
def ownUsesOf (cs : Array CEntry) (at_ : Std.HashMap NIdx Nat) (d : IDeclaration) :
    AM (Array NIdx) :=
  match d with
  | .thmDecl cv _ =>
    match ownUsesThm cs at_ cv.name with
    | some u => pure u
    | none => ConRon.Arena.Frontend.IDeclaration.usedConsts d
  | _ => ConRon.Arena.Frontend.IDeclaration.usedConsts d

/-- con-leche: ConLeche/Driver/Worker.lean:97-99 ownNames
**A module's own names**: every constant of its private view. -/
def ownNames (cs : Array CEntry) : Std.HashSet NIdx := cs.foldl (fun s c => s.insert c.c.name) {}

/-- con-leche: ConLeche/Driver/Worker.lean:101-104 namesNodupGo
**No name twice**, one hash set along the list. -/
def namesNodupGo (s : Std.HashSet NIdx) : List NIdx → Bool × Std.HashSet NIdx
  | [] => (true, s)
  | n :: ns => if s.contains n then (false, s) else namesNodupGo (s.insert n) ns

/-- con-leche: ConLeche/Driver/Worker.lean:301-344 workerRead
`namesNodupGo {} (r.ctx.toList.flatMap Modular.declNames)`, record by record. -/
def ctxNamesNodupGo (s : Std.HashSet NIdx) : List IDeclaration → AM Bool
  | [] => pure true
  | d :: ds => do
    let (ok, s) := namesNodupGo s (← declNames d)
    if ok then ctxNamesNodupGo s ds else pure false

/-- con-leche: ConLeche/Driver/Worker.lean:301-344 workerRead
The context's names distinct. -/
def ctxNamesNodup (ctx : Array IDeclaration) : AM Bool := ctxNamesNodupGo {} ctx.toList

/-- con-leche: ConLeche/Driver/Worker.lean:125-126 loadedRec
`ns.any ix.first.contains`. -/
def anyLoaded (ix : NameIndex) (ns : List NIdx) : Bool := ns.any ix.first.contains

/-- con-leche: ConLeche/Driver/Worker.lean:125-126 loadedRec
**A record some name of which a loaded module stores.** -/
def loadedRec (ix : NameIndex) (d : IDeclaration) : AM Bool := do
  pure (anyLoaded ix (← declNames d))

/-- con-leche: ConLeche/Driver/Worker.lean:128-136 ownRecs
The emitted records some name of which is loaded (`want`), or none is. -/
def recsLoaded (ix : NameIndex) (ds : Array IDeclaration) (want : Bool) : AM (Array IDeclaration) :=
  ds.foldlM (fun out d => do if (← loadedRec ix d) == want then pure (out.push d) else pure out) #[]

/-- con-leche: ConLeche/Driver/Worker.lean:128-131 ownRecs
**The own records** of a worker that adds the imports `x`, before the hoist. -/
def ownRecs (x : Array ImportRec) (ix : NameIndex) (ds : Array IDeclaration) :
    AM (Array IDeclaration) :=
  if x.isEmpty then pure ds else recsLoaded ix ds false

/-- con-leche: ConLeche/Driver/Worker.lean:133-136 copyRecs
**The copies**: none, but at a compared challenge, the emitted records some name of which is
loaded. -/
def copyRecs (x : Array ImportRec) (ix : NameIndex) (ds : Array IDeclaration) :
    AM (Array IDeclaration) :=
  if x.isEmpty then pure #[] else recsLoaded ix ds true

/-- con-leche: ConLeche/Driver/Worker.lean:138-142 ownNamesOf
**The own names** of a worker that adds the imports `x`. -/
def ownNamesOf (x : Array ImportRec) (ix : NameIndex) (cs : Array CEntry) : Std.HashSet NIdx :=
  if x.isEmpty then ownNames cs
  else cs.foldl (fun s c => if ix.first.contains c.c.name then s else s.insert c.c.name) {}

/-- con-leche: ConLeche/Driver/Worker.lean:144-154 rootsAt
`l.constants.filter (!ix.first.contains ·.name)`. -/
def unloadedConstants (ix : NameIndex) (cs : Array CEntry) : Array CEntry :=
  cs.filter fun c => !ix.first.contains c.c.name

/-- con-leche: ConLeche/Driver/Worker.lean:144-154 rootsAt
**The reach's roots** of a worker that adds the imports `x`. -/
def rootsAt (pins : List INatOpPinSet) (x : Array ImportRec) (ix : NameIndex) (cs : Array CEntry)
    (ds : Array IDeclaration) : AM (Array NIdx) := do
  if x.isEmpty then return ← ownRoots pins ix cs ds
  let own ← recsLoaded ix ds false
  let out ← ownRoots pins ix (unloadedConstants ix cs) own
  let copies ← recsLoaded ix ds true
  copies.foldlM (fun out d => do pure (out ++ (← declNames d).toArray)) out

/-- con-leche: ConLeche/Driver/Worker.lean:156-163 copyStmt?
`Expr.mentionsAnyConstC [sorryAxName] v`. -/
def usesSorry (v : EIdx) : AM Bool := do
  mentionsAnyConst [← pinSorryAx] v

/-- con-leche: ConLeche/Driver/Worker.lean:156-163 copyStmt?
**The statement a copy may be read by.** -/
def copyStmt : IDeclaration → AM (Option IConstantVal)
  | .axiomDecl cv => pure (some cv)
  | .defnDecl cv v _ => do if ← usesSorry v then pure (some cv) else pure none
  | .opaqueDecl cv _ => pure (some cv)
  | .thmDecl cv _ => pure (some cv)
  | _ => pure none

/-- con-leche: ConLeche/Driver/Worker.lean:165-170 sameDefUpToLevels
**A definition of the challenge, the loaded one** up to the names of its level parameters. -/
def sameDefUpToLevels (c c' : IConstantInfo) : AM Bool := do
  let ps := c.toConstantVal.levelParams
  let ps' := c'.toConstantVal.levelParams
  if ps == ps' then pure (c == c')
  else if levelsRenaming ps ps' then pure ((← c'.atLps ps) == c)
  else pure false

/-- con-leche: ConLeche/Driver/Worker.lean:172-175 copyRecEq
**Two blocks, the same record.** -/
def copyRecEq : IDeclaration → IDeclaration → Bool
  | .indDecl b n, .indDecl b' n' => n == n' && b == b'
  | _, _ => false

/-- con-leche: ConLeche/Driver/Worker.lean:177-189 blockReadB
**A block the kernel's reader reads**, its constructors' names distinct and in the block's
order; true for any other record. -/
def blockReadB : IDeclaration → AM Bool
  | .indDecl block nP => do
    match ← readBlock nP block with
    | .error _ => pure false
    | .ok p =>
      let names := p.allCtors.map (·.1.name)
      if !(namesNodupGo {} names).1 then return false
      match blockSplit block with
      | some (_, cs, _) => pure (names == cs.map (·.1.name))
      | none => pure true
  | _ => pure true

/-- con-leche: ConLeche/Driver/Worker.lean:191-195 ctxConst
**The context's constants, one layer**: every constant of every context record pushed, in
order, over the empty base. -/
def ctxLayer (ctx : Array IDeclaration) : AM IFEnv :=
  ctx.foldlM (fun fe d => do pure ((← declConstants d).foldl IFEnv.push fe))
    ⟨⟨[], []⟩, {}, {}, {}, false, false⟩

/-- con-leche: ConLeche/Driver/Worker.lean:197-207 copyReadsB
**A copied block's recursors read their ι equations off their own types**, against the
context's constants `fe`; true for any other record. -/
def copyReadsB (fe : IFEnv) : IDeclaration → AM Bool
  | .indDecl block nP => do
    match ← readBlock nP block with
    | .error _ => pure false
    | .ok p => recsRead fe (← blockRecs p p.recs)
  | _ => pure true

/-- con-leche: ConLeche/Driver/Worker.lean:209-241 copyCheck
`cs.find? (·.toConstantVal.name == n)`. -/
def findNamed (cs : List IConstantInfo) (n : NIdx) : Option IConstantInfo := cs.find? (·.name == n)

/-- con-leche: ConLeche/Driver/Worker.lean:209-241 copyCheck
`(declConstants e).find? (·.toConstantVal.name == n)`. -/
def findConstant (e : IDeclaration) (n : NIdx) : AM (Option IConstantInfo) := do
  pure (findNamed (← declConstants e) n)

/-- con-leche: ConLeche/Driver/Worker.lean:209-241 copyCheck
A copied block: the same record, read by the kernel's reader, its recursors reading. -/
def copyIndOk (fe : IFEnv) (d e : IDeclaration) : AM Bool := do
  if !copyRecEq d e then return false
  if !(← blockReadB d) then return false
  copyReadsB fe d

/-- con-leche: ConLeche/Driver/Worker.lean:209-241 copyCheck
The comparison of a copy with the context's record `e` (at home `h`) that holds its name `n`. -/
def copyAgainst (fe : IFEnv) (m src n : NIdx) (e : IDeclaration) (h : NIdx) (d : IDeclaration) :
    AM Unit := do
  let ci ← findConstant e n
  let cs ← copyStmt d
  match cs with
  | some cv =>
    match ci with
    | some ci =>
      if ← ConRon.Arena.sameCvUpToLevels cv ci.toConstantVal then pure ()
      else fail (.invalid s!"{← readName n}: the constant of {← readName h} is not of the \
        statement of {← readName m}'s {recKind d}")
    | none => fail (.internal s!"{← readName n}: the context's record does not declare it")
  | none =>
    match d with
    | .defnDecl cv v hint =>
      match ci with
      | some ci =>
        if ← sameDefUpToLevels (.defnInfo cv v hint) ci then pure ()
        else fail (.invalid s!"{← readName n}: the constant of {← readName h} is not \
          {← readName m}'s definition")
      | none => fail (.internal s!"{← readName n}: the context's record does not declare it")
    | .indDecl .. =>
      if ← copyIndOk fe d e then pure ()
      else fail (.invalid s!"{← readName n}: the constants of {← readName h} are not \
        {← readName m}'s inductive type")
    | _ =>
      match ci with
      | none => fail (.internal s!"{← readName n}: the context's record does not declare it")
      | some _ => fail (.invalid s!"module {← readName m} declares {← readName n}, which the \
          module {← readName src} it loads stores")

/-- con-leche: ConLeche/Driver/Worker.lean:209-241 copyCheck
**A copy against the loaded constants of its names.** -/
def copyCheck (pk : OleanPins) (m : NIdx) (ld : HeaderLoads) (ix : NameIndex) (r : Reach)
    (owner : Std.HashMap NIdx Nat) (fe : IFEnv) (d : IDeclaration) : AM Unit := do
  let n := (recKey d).getD pk.anon
  let src := match ix.first[n]? with
    | some c => ld.nameAt pk c.mod
    | none => pk.anon
  let qs ← pinQuotSound
  let sa ← pinSorryAx
  if n == qs || n == sa then
    let what := if n == qs then "the quotient's axiom" else "the placeholder axiom"
    fail (.notImplemented s!"{← readName n}: a hole at {what}, which installs no axiom of its \
      own; con-leche cannot fill it")
  if !(← basisNamesOk d) then
    fail (.invalid s!"module {← readName m} declares {← readName n}, a name the checker reserves")
  match owner[n]? with
  | none => fail (.internal s!"{← readName n}: the context does not hold the loaded constant")
  | some k =>
    match r.ctx[k]? with
    | some e => copyAgainst fe m src n e (r.homes.getD k pk.anon) d
    | none => fail (.internal s!"{← readName n}: the context does not hold the loaded constant")

/-- con-leche: ConLeche/Driver/Worker.lean:243-249 isHoleRec
**A hole** (`uses`, what a theorem's value read off the file). -/
def isHoleRec (uses : IDeclaration → AM (Array NIdx)) : IDeclaration → AM Bool
  | .axiomDecl cv => do pure !(← builtinAxiomName cv.name)
  | .defnDecl _ v _ => usesSorry v
  | .opaqueDecl _ v => usesSorry v
  | d@(.thmDecl ..) => do
    let us ← uses d
    pure (us.contains (← pinSorryAx))
  | _ => pure false

/-- con-leche: ConLeche/Driver/Worker.lean:251-258 ownHoleOk
**A hole of the challenge's own records**: the solution does not fill it. -/
def ownHoleOk (pk : OleanPins) (uses : IDeclaration → AM (Array NIdx)) (m : NIdx)
    (d : IDeclaration) : AM Unit := do
  if ← isHoleRec uses d then
    fail (.invalid s!"{← readName ((recKey d).getD pk.anon)}: a hole of {← readName m} no loaded \
      module fills (the solution has no constant of this name)")

/-- con-leche: ConLeche/Driver/Worker.lean:260-264 copiesOk
Some record an inductive block. -/
def anyInd (ds : Array IDeclaration) : Bool :=
  ds.any fun d => match d with
    | .indDecl .. => true
    | _ => false

/-- con-leche: ConLeche/Driver/Worker.lean:260-264 copiesOk
**Every copy against the loaded constants of its names**; the context's layer built only where
a copy is an inductive block. -/
def copiesOk (pk : OleanPins) (m : NIdx) (x : Array ImportRec) (wr : WorkerReads) (r : Reach)
    (ds : Array IDeclaration) : AM Unit := do
  let owner ← ownerMap r.ctx.toList
  let cs ← copyRecs x wr.index ds
  let fe ← if anyInd cs then ctxLayer r.ctx else pure ⟨⟨[], []⟩, {}, {}, {}, false, false⟩
  cs.toList.forM (copyCheck pk m wr.loads wr.index r owner fe)

/-- con-leche: ConLeche/Driver/Worker.lean:266-270 ownHolesOk
**No hole among the own records** of a compared challenge. -/
def ownHolesOk (pk : OleanPins) (uses : IDeclaration → AM (Array NIdx)) (m : NIdx)
    (x : Array ImportRec) (ix : NameIndex) (ds : Array IDeclaration) : AM Unit := do
  if x.isEmpty then return
  (← recsLoaded ix ds false).toList.forM (ownHoleOk pk uses m)

/-- con-leche: ConLeche/Driver/Worker.lean:272-290 WorkerRead
**What a worker has read and checked before its jobs.** -/
structure WorkerRead where
  home : Loaded
  expo : Array Expo
  reads : WorkerReads
  emitted : Array IDeclaration
  own : Array IDeclaration
  reach : Reach
  hoisted : Array NIdx
  pins : OleanPins
  values : Array ModRef
  start : Nat

/-- con-leche: ConLeche/Driver/Worker.lean:301-344 workerRead
Phase 4 and the hoist, over the load's constants `cs` and the emitted records `ds`. -/
def workerReach (fs : OleanFs) (pk : OleanPins) (sp : Roots) (pins : List INatOpPinSet) (m : NIdx)
    (x : Array ImportRec) (wr : WorkerReads) (cs : Array CEntry) (ds : Array IDeclaration) :
    AM (Reach × Array IDeclaration × Array NIdx) := do
  let uses := ownUsesOf cs (ownUsesAt cs)
  ownHolesOk pk uses m x wr.index ds
  let roots ← rootsAt pins x wr.index cs ds
  let r ← reach fs pk sp m wr (ownNamesOf x wr.index cs) roots
  if !(← ctxNamesNodup r.ctx) then
    fail (.invalid "a context record declares one of its names twice")
  copiesOk pk m x wr r ds
  let recs ← ownRecs x wr.index ds
  let (own, hoisted) ← ConRon.Arena.Frontend.hoistNatOpGround uses recs
  pure (r, own, hoisted)

/-- con-leche: ConLeche/Driver/Worker.lean:301-344 workerRead
**Phases 1–4 of the worker at module `m`**; `x` the imports a run adds to its header; `pins`
the run's interned pin variants.  A failure carries the position of the record it names. -/
def workerRead (fs : OleanFs) (sp : Roots) (pins : List INatOpPinSet) (m : NIdx)
    (x : Array ImportRec) : AM (Except (CheckError × Nat) WorkerRead) := do
  let pk ← oleanPins
  let f ← liftE (readFiles fs sp (← readName m) .private)
  let (l, expo) ← homeOf pk m f
  let wr ← workerReads fs pk sp m x
  if !x.isEmpty && wr.loads.index.contains m then
    fail (.invalid s!"the module {← readName m} is loaded by the imports added to its header: \
      the solution's closure holds the challenge")
  match ← ownRecords pk l with
  | .error e => pure (.error e)
  | .ok ds =>
    let (r, own, hoisted) ← workerReach fs pk sp pins m x wr l.constants ds
    pure (.ok { home := { l with frontier := {} }, expo, reads := wr, emitted := ds, own,
                reach := r, hoisted, pins := pk, values := #[⟨m, l.frontier⟩],
                start := r.ctx.size })

/-- con-leche: ConLeche/Driver/Worker.lean:371-413 checkModuleG
**The jobs' records**: the context's, then the own records. -/
def workerDecls (w : WorkerRead) : Array IDeclaration := w.reach.ctx ++ w.own

end ConRon.Arena.Modular
