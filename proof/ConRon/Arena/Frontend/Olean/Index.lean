/-
# `ConRon.Arena.Frontend.Olean.Index` — the names a module's environment holds (task #166)

The twin of `olean/index.rs`.  `Copy` is upstream's own: two numbers.  The loaded parts'
tables and the copies' statements are read in order (`parMapExcept` is the sequential map).
`clashCopies` keeps each name's entry by its position in the list (as the Rust), where upstream
keeps a table of copies beside the names' order (`ccOrderStep`): the same list.
-/
module

public import ConLeche.Frontend.Olean.Index
public import ConRon.Arena.Frontend.Olean.Levels
public import ConRon.Arena.Frontend.Olean.Merge

@[expose] public section

namespace ConRon.Arena.Frontend.Olean

open ConLeche
open ConLeche.Frontend.Olean (Copy LoadFlags CKindF Roots OLeanLevel)

/-- con-leche: ConLeche/Frontend/Olean/Index.lean:42-49 NameIndex
**The name index** of the loaded parts. -/
structure NameIndex where
  parts : Array NamePositions
  first : Std.HashMap NIdx Copy
  more : Array (NIdx × Copy)

/-- con-leche: ConLeche/Frontend/Olean/Index.lean:51-53 NameIndex.at
The name position of a copy. -/
def NameIndex.at (ix : NameIndex) (c : Copy) : Option NamePosition :=
  (ix.parts[c.mod]?).bind (·.consts[c.pos]?)

/-- con-leche: ConLeche/Frontend/Olean/Index.lean:55-66 nameIndexOf
**The index of some modules' name positions**, in their order. -/
def nameIndexOf (parts : Array NamePositions) : NameIndex :=
  let (first, more, _) := parts.foldl (fun (acc : Std.HashMap NIdx Copy × Array (NIdx × Copy) × Nat) p =>
    let (first, more, i) := acc
    let (first, more, _) := p.consts.foldl (fun (acc : Std.HashMap NIdx Copy × Array (NIdx × Copy) × Nat) q =>
      let (first, more, k) := acc
      if first.contains q.name then (first, more.push (q.name, ⟨i, k⟩), k + 1)
      else (first.insert q.name ⟨i, k⟩, more, k + 1)) (first, more, 0)
    (first, more, i + 1)) ({}, #[], 0)
  { parts, first, more }

/-- con-leche: ConLeche/Frontend/Olean/Index.lean:68-72 Clash
**A name two loaded modules hold**: its copies in the load order, each with its statement and
its kind (expressions left out). -/
structure Clash where
  name : NIdx
  copies : Array (Copy × StmtRec × CKindF NIdx Unit)

/-- con-leche: ConLeche/Frontend/Olean/Index.lean:110-111 HeaderLoads.nameAt
A module's name for messages. -/
def HeaderLoads.nameAt (pk : OleanPins) (ld : HeaderLoads) (i : Nat) : NIdx :=
  (ld.order[i]?).getD pk.anon

/-- con-leche: ConLeche/Frontend/Olean/Index.lean:76-91 readInfosOf
A module's level in the load order. -/
def HeaderLoads.levelAt (ld : HeaderLoads) (i : Nat) : OLeanLevel :=
  ((ld.flags[i]?).getD default).level

/-- con-leche: ConLeche/Frontend/Olean/Index.lean:76-91 readInfosOf
**The statements and kinds of some copies** of module `i`, read together. -/
def readInfosOf (fs : OleanFs) (pk : OleanPins) (sp : Roots) (ld : HeaderLoads) (ix : NameIndex)
    (i : Nat) (cs : Array Copy) : AM (Array (Copy × StmtRec × CKindF NIdx Unit)) := do
  let m := ld.nameAt pk i
  let level := ld.levelAt i
  let locs := cs.toList.filterMap fun c => (ix.at c).map (·.loc)
  let mn ← readName m
  let f ← liftE (readFiles fs sp mn level)
  let some ss ← readStmts pk f level locs | fail (undecodable mn)
  let some ks ← readKinds pk f level locs | fail (undecodable mn)
  if ss.length == cs.size && ks.length == cs.size then
    pure (cs.zip (ss.zip ks).toArray)
  else fail (undecodable mn)

/-- con-leche: ConLeche/Frontend/Olean/Index.lean:93-97 byModule
Copies grouped by module, the modules ascending. -/
def byModule (cs : Array Copy) : Array (Nat × Array Copy) :=
  let top := cs.foldl (fun t c => max t (c.mod + 1)) 0
  let buckets := cs.foldl (fun (b : Array (Array Copy)) c => b.modify c.mod (·.push c))
    (Array.replicate top #[])
  (buckets.zipIdx.filter (·.1.size > 0)).map fun (a, k) => (k, a)

/-- con-leche: ConLeche/Frontend/Olean/Index.lean:99-106 readInfos
**The statements and kinds of some copies**, module by module, in order. -/
def readInfos (fs : OleanFs) (pk : OleanPins) (sp : Roots) (ld : HeaderLoads) (ix : NameIndex)
    (cs : Array Copy) : AM (Std.HashMap Copy (StmtRec × CKindF NIdx Unit)) := do
  let rs ← (byModule cs).toList.mapM fun (i, cs) => readInfosOf fs pk sp ld ix i cs
  pure (rs.foldl (fun m r => r.foldl (fun m (c, s, k) => m.insert c (s, k)) m) {})

/-- con-leche: ConLeche/Frontend/Olean/Index.lean:194-242 workerReads
**`isPropCheap`'s `headTy` at the clash rule**, as a table over the heads' names: a head `c`'s
name, the type of its name's first copy among the statements read (upstream's
`fun n => (ix.first[n]?).bind fun c => (hinfos[c]?).map (·.1.type)`, at the names of the heads). -/
def headTysOf (ix : NameIndex) (infos : Std.HashMap Copy (StmtRec × CKindF NIdx Unit)) (heads : Array Copy) :
    Std.HashMap NIdx EIdx :=
  heads.foldl (fun m c =>
    match ix.at c with
    | none => m
    | some q =>
      match (ix.first[q.name]?).bind (infos[·]?) with
      | some x => m.insert q.name x.1.type
      | none => m) {}

/-- con-leche: ConLeche/Frontend/Olean/Index.lean:113-127 clashOk
**Lean's clash rule over one name's copies**, in the load order. -/
def clashOk (pk : OleanPins) (ld : HeaderLoads) (headTy : NIdx → Option EIdx) (c : Clash) : AM Unit := do
  match c.copies.toList with
  | [] => pure ()
  | k :: rest =>
    let _ ← rest.foldlM (fun (kept : Copy × StmtRec × CKindF NIdx Unit) next => do
      let (_, cv₁, k₁) := next
      let (_, cv₂, k₂) := kept
      if ← subsumesF pk headTy cv₁ k₁ cv₂ k₂ then pure next
      else if ← subsumesF pk headTy cv₂ k₂ cv₁ k₁ then pure kept
      else fail (.invalid s!"modules {← readName (ld.nameAt pk kept.1.mod)} and \
        {← readName (ld.nameAt pk next.1.mod)} store different constants named \
        {← readName c.name}, and both are loaded")) k
    pure ()

/-- con-leche: ConLeche/Frontend/Olean/Index.lean:129-135 freshOk
**Freshness**: no constant of the module's own part bears a loaded name. -/
def freshOk (pk : OleanPins) (m : NIdx) (ld : HeaderLoads) (ix : NameIndex) (own : NamePositions) :
    AM Unit := do
  match own.consts.find? (ix.first.contains ·.name) with
  | none => pure ()
  | some q =>
    let src := ((ix.first[q.name]?).map fun c => ld.nameAt pk c.mod).getD pk.anon
    fail (.invalid s!"module {← readName m} declares {← readName q.name}, which the module \
      {← readName src} it loads stores")

/-- con-leche: ConLeche/Frontend/Olean/Index.lean:137-146 importsModulesOk
**Lean's refusal of a classic import from a module**. -/
def importsModulesOk (m : NIdx) (isModule : Bool) (ld : HeaderLoads) (ix : NameIndex)
    (imports : Array ImportRec) : AM Unit := do
  if !isModule then pure () else
  match imports.find? fun i => match ld.index[i.module]? with
    | some k => !((ix.parts[k]?).any (·.header.isModule))
    | none => false with
  | some i => fail (.invalid s!"module {← readName m} of the module system imports \
      {← readName i.module}, which is not")
  | none => pure ()

/-- con-leche: ConLeche/Frontend/Olean/Index.lean:150-161 WorkerReads
**What a worker reads before its own records.** -/
structure WorkerReads where
  own : NamePositions
  loads : HeaderLoads
  pub : Array ConLeche.Frontend.Olean.ModSet
  index : NameIndex
  clashes : Array Clash

/-- con-leche: ConLeche/Frontend/Olean/Index.lean:179-185 clashCopies
**The doubly held names, each with all its copies, in the load order**: the names in the order of
their second copies, each with its first copy and then its later ones. -/
def clashCopies (ix : NameIndex) : Array (NIdx × Array Copy) :=
  (ix.more.foldl (fun (acc : Std.HashMap NIdx Nat × Array (NIdx × Array Copy)) (n, c) =>
    let (at_, out) := acc
    match at_[n]? with
    | some k => (at_, out.modify k fun (n', cs) => (n', cs.push c))
    | none => (at_.insert n out.size, out.push (n, #[(ix.first[n]?).getD c, c]))) ({}, #[])).2

/-- con-leche: ConLeche/Frontend/Olean/Index.lean:187-192 NamePositions.withImports
**A worker's own part with imports added**: the header's imports followed by `x`, and no
constant of its own.  Without imports to add, the part itself. -/
def NamePositions.withImports (own : NamePositions) (x : Array ImportRec) : NamePositions :=
  if x.isEmpty then own
  else { header := { own.header with imports := own.header.imports ++ x }, consts := #[] }

/-- con-leche: ConLeche/Frontend/Olean/Index.lean:194-242 workerReads
The heads `isPropCheap` asks the type of, at the axiom/axiom pairs. -/
def clashHeads (ix : NameIndex) (clashes : Array Clash) : AM (Array Copy) :=
  clashes.foldlM (fun (acc : Array Copy) cl => do
    match cl.copies[0]? with
    | some (_, cv, .ax _) =>
      match (← isPropCheapHeadOf cv.type).bind (ix.first[·]?) with
      | some c => pure (acc.push c)
      | none => pure acc
    | _ => pure acc) #[]

/-- con-leche: ConLeche/Frontend/Olean/Index.lean:194-242 workerReads
**Phases 1 and 2 of a worker at module `m`**: its own part's header and names; the header
fixpoint; each loaded module's public-import closure; the name index of the loaded parts;
Lean's refusal of a classic import from a module, the clash rule over every loaded name and
freshness.  `x`: imports added to the header. -/
def workerReads (fs : OleanFs) (pk : OleanPins) (sp : Roots) (m : NIdx) (x : Array ImportRec) :
    AM WorkerReads := do
  let own := (← readPartNames fs pk sp m .private).withImports x
  let ld ← headerFixpoint fs pk sp own.header.isModule own.header.imports
  let parts ← (ld.order.zip ld.flags).toList.mapM fun (n, fl) => readPartNames fs pk sp n fl.level
  let ix := nameIndexOf parts.toArray
  importsModulesOk m own.header.isModule ld ix own.header.imports
  let cc := clashCopies ix
  let infos ← readInfos fs pk sp ld ix (cc.flatMap (·.2))
  let clashes : Array Clash := cc.map fun (n, cs) =>
    { name := n, copies := cs.filterMap fun c => (infos[c]?).map fun (s, k) => (c, s, k) }
  let heads ← clashHeads ix clashes
  let hinfos ← readInfos fs pk sp ld ix heads
  let headTys := headTysOf ix hinfos heads
  clashes.toList.forM (clashOk pk ld (headTys[·]?))
  freshOk pk m ld ix own
  pure { own, loads := ld, pub := pubClosures ld, index := ix, clashes }

end ConRon.Arena.Frontend.Olean
