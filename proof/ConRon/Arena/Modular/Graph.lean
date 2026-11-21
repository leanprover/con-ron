/-
# `ConRon.Arena.Modular.Graph` — the import graph of a closure, checked (task #166)

The twin of `frontend/modular/graph.rs`.  `rankLt` is upstream's own.  `kahn`, `ranksOf` and
`cycleOf` are the Rust's loops, written as folds and recursions over arrays of numbers: what is
proved of the check is the validation (`verdict`), which reads neither (Theorem 1,
`Bridge/Modular/Graph.lean`), so they need not be upstream's definitions.  The closure's names are handles; a rank function is two
tables (`indexOf`, `ranksOf`) read by `rankOf`, as upstream's `rankOf idx rank` is.  The imports
a run adds are the pair `cmp` (challenge, solution), `none` for none.  Headers are read in order
(`parMapExcept` is the sequential map); no `Roots` cache.
-/
module

public import ConLeche.Driver.Graph
public import ConRon.Arena.Frontend.Olean.Levels

@[expose] public section

namespace ConRon.Arena.Modular

open ConLeche
open ConRon.Arena.Frontend.Olean
open ConLeche.Frontend.Olean (Roots RootAt modFile)
open ConLeche.Driver.Graph (rankLt)

/-- con-leche: ConLeche/Driver/Graph.lean:33-34 Node
A module of the closure: its name and its imports, off its header. -/
abbrev Node := NIdx × Array ImportRec

/-- con-leche: ConLeche/Driver/Graph.lean:38-40 solutionImport
**The import a compared run adds to the challenge's header**: the solution, `import all`. -/
def solutionImport (S : NIdx) : ImportRec :=
  { module := S, importAll := true, isExported := false, isMeta := false }

/-- con-leche: ConLeche/Driver/Graph.lean:42-45 cmpExtra
**The imports a modular run adds to a header**: the solution to the challenge's, none to any
other module's; `none`: no import added anywhere. -/
def cmpExtra (cmp : Option (NIdx × NIdx)) (m : NIdx) : Array ImportRec :=
  match cmp with
  | some (C, S) => if m == C then #[solutionImport S] else #[]
  | none => #[]

/-- con-leche: none — an action's failure as a value, the state it was started in kept -/
def AM.catchAt {α : Type} (x : AM α) : AM (Except CheckError α) := fun s =>
  match x s with
  | .ok (a, s') => .ok (.ok a, s')
  | .error e => .ok (.error e, s)

/-- con-leche: ConLeche/Driver/Graph.lean:48-58 missingOn
Whether one of a module's files is at a directory. -/
def fileAt (fs : OleanFs) (d : System.FilePath) (n : Name) (ext : String) : AM Bool :=
  liftE (pathExistsE fs (modFile d n ext))

/-- con-leche: ConLeche/Driver/Graph.lean:48-58 missingOn
Whether the search path has none of `m`'s files. -/
def missingOn (fs : OleanFs) (sp : Roots) (m : NIdx) : AM Bool := do
  let n ← readName m
  match lookAt fs sp.path sp.fallback n.root with
  | .missing => pure true
  | .dir d =>
    if ← fileAt fs d n "olean" then return false
    if ← fileAt fs d n "olean.server" then return false
    return !(← fileAt fs d n "olean.private")
  | _ => pure false

/-- con-leche: ConLeche/Driver/Graph.lean:60-70 hdrOf
**A module's imports**, read off its header, followed by the imports the run adds to it; a
module the search path does not have is invalid input. -/
def hdrOf (fs : OleanFs) (pk : OleanPins) (sp : Roots) (cmp : Option (NIdx × NIdx)) (m : NIdx) :
    AM Node := do
  match ← AM.catchAt (moduleImports fs pk sp m) with
  | .ok imps => pure (m, imps ++ cmpExtra cmp m)
  | .error e =>
    if ← missingOn fs sp m then
      fail (.invalid s!"module {← readName m}: no .olean on the search path")
    else fail e

/-- con-leche: ConLeche/Driver/Graph.lean:72-80 expand
One level of the walk: the modules read, in order, and the imports not yet seen, the next
level. -/
def expand (seen : Std.HashSet NIdx) (out : Array Node) (next : Array NIdx) :
    List Node → Std.HashSet NIdx × Array Node × Array NIdx
  | [] => (seen, out, next)
  | (m, imps) :: rest =>
    let (seen, next) := imps.foldl (fun (s, nx) i =>
      if s.contains i.module then (s, nx) else (s.insert i.module, nx.push i.module)) (seen, next)
    expand seen (out.push (m, imps)) next rest

/-- con-leche: ConLeche/Driver/Graph.lean:82-97 closureLevels
**The closure, level by level**: a level's headers read in order, the modules first met there
the next level.  `fuel` bounds the levels. -/
def closureLevels (fs : OleanFs) (pk : OleanPins) (sp : Roots) (cmp : Option (NIdx × NIdx)) :
    Nat → List NIdx → Std.HashSet NIdx → Array Node → AM (Array Node)
  | _, [], _, out => pure out
  | 0, _ :: _, _, _ => fail (.internal "the closure's walk ran out of steps")
  | fuel + 1, lvl@(_ :: _), seen, out => do
    let rs ← lvl.mapM (hdrOf fs pk sp cmp)
    let (seen, out, next) := expand seen out #[] rs
    closureLevels fs pk sp cmp fuel next.toList seen out

/-- con-leche: ConLeche/Driver/Graph.lean:102-106 dedup
The roots, each once, in order, and the set of them. -/
def dedup (xs : List NIdx) : List NIdx × Std.HashSet NIdx :=
  let (s, acc) := xs.foldl (fun (s, acc) x =>
    if s.contains x then (s, acc) else (s.insert x, acc.push x)) (({} : Std.HashSet NIdx), #[])
  (acc.toList, s)

/-- con-leche: ConLeche/Driver/Graph.lean:110-115 indexOf
Each module's position in the closure. -/
def indexOf (C : Array Node) : Std.HashMap NIdx Nat :=
  (C.foldl (fun (acc : Std.HashMap NIdx Nat × Nat) e => (acc.1.insert e.1 acc.2, acc.2 + 1)) ({}, 0)).1

/-- con-leche: ConLeche/Driver/Graph.lean:117-120 depsOf
Each module's imports, by position (an import outside the closure left out). -/
def depsOf (idx : Std.HashMap NIdx Nat) (C : Array Node) : Array (Array Nat) :=
  C.map fun e => e.2.filterMap fun i => idx[i.module]?

/-- con-leche: ConLeche/Driver/Graph.lean:122-146 kahn
`users`: each position's importers, an importer once per edge. -/
def kahnUsers (deps : Array (Array Nat)) : Array (Array Nat) :=
  (List.range deps.size).foldl (fun users x =>
    (deps[x]?.getD #[]).foldl (fun users j => users.modify j (·.push x)) users)
    (Array.replicate deps.size #[])

/-- con-leche: ConLeche/Driver/Graph.lean:122-146 kahn
The worklist's start: each position's number of import edges, and the positions with none. -/
def kahnStart (deps : Array (Array Nat)) : Array Nat × Array Nat :=
  (List.range deps.size).foldl (fun (acc : Array Nat × Array Nat) k =>
    let d := deps[k]?.getD #[]
    (acc.1.push d.size, if d.size == 0 then acc.2.push k else acc.2)) (#[], #[])

/-- con-leche: ConLeche/Driver/Graph.lean:122-146 kahn
One release: an importer `y` of the module taken waits on one edge less, and is queued when it
waits on none. -/
def kahnRelease (acc : Array Nat × Array Nat) (y : Nat) : Array Nat × Array Nat :=
  let (wait, q) := acc
  if y < wait.size then
    let w := wait[y]!
    (if w > 0 then wait.set! y (w - 1) else wait, if w == 1 then q.push y else q)
  else (wait, q)

/-- con-leche: ConLeche/Driver/Graph.lean:122-146 kahn
The worklist from position `i` of the queue, at most `t` more steps. -/
def kahnGo (users : Array (Array Nat)) : Nat → Nat → Array Nat → Array Nat → Array Nat
  | 0, _, _, q => q
  | t + 1, i, wait, q =>
    if h : i < q.size then
      let (wait, q) := (users[q[i]]?.getD #[]).foldl kahnRelease (wait, q)
      kahnGo users t (i + 1) wait q
    else q

/-- con-leche: ConLeche/Driver/Graph.lean:122-146 kahn
**Kahn's worklist**: the positions in an order where each comes after everything it imports; on
a cyclic graph, the part of it that waits on no cycle. -/
def kahn (deps : Array (Array Nat)) : Array Nat :=
  let (wait, q) := kahnStart deps
  kahnGo (kahnUsers deps) deps.size 0 wait q

/-- con-leche: ConLeche/Driver/Graph.lean:148-153 ranksOf
**The ranks**: a position's place in the order, `none` for a position the order lacks. -/
def ranksOf (n : Nat) (ord : Array Nat) : Array (Option Nat) :=
  (List.range ord.size).foldl (fun r t => r.set! (ord[t]?.getD 0) (some t)) (Array.replicate n none)

/-- con-leche: ConLeche/Driver/Graph.lean:159-180 cycleOf
The positions `ord` lists, marked. -/
def doneOf (n : Nat) (ord : Array Nat) : Array Bool :=
  ord.foldl (fun d p => d.set! p true) (Array.replicate n false)

/-- con-leche: ConLeche/Driver/Graph.lean:159-180 cycleOf
The first position the order lacks. -/
def cycleStart (n : Nat) (done : Array Bool) : Option Nat :=
  (List.range n).find? fun k => !(done[k]?.getD false)

/-- con-leche: ConLeche/Driver/Graph.lean:159-180 cycleOf
The first import of `x` outside the order. -/
def cycleNext (deps : Array (Array Nat)) (done : Array Bool) (x : Nat) : Option Nat :=
  (deps[x]?.getD #[]).find? fun y => !(done[y]?.getD false)

/-- con-leche: ConLeche/Driver/Graph.lean:159-180 cycleOf
One step of the walk at `x`: a repeat (its first visit's place on the path), or `x` on the path
and the next module. -/
inductive CycleStep where
  | repeat (p : Nat)
  | next (y : Option Nat)

/-- con-leche: ConLeche/Driver/Graph.lean:159-180 cycleOf
`if let some p := at?[x]! then … ; at? := at?.set! x (some path.size); path := path.push x`. -/
def cycleStep (deps : Array (Array Nat)) (done : Array Bool) (at_ : Array (Option Nat))
    (path : Array Nat) (x : Nat) : CycleStep × Array (Option Nat) × Array Nat :=
  match at_[x]? with
  | some (some p) => (.repeat p, at_, path)
  | some none => (.next (cycleNext deps done x), at_.set! x (some path.size), path.push x)
  | none => (.next (cycleNext deps done x), at_, path.push x)

/-- con-leche: ConLeche/Driver/Graph.lean:159-180 cycleOf
The walk, at most `t` steps: the repeat's place, and the path. -/
def cycleWalk (deps : Array (Array Nat)) (done : Array Bool) :
    Nat → Array (Option Nat) → Array Nat → Nat → Option Nat × Array Nat
  | 0, _, path, _ => (none, path)
  | t + 1, at_, path, x =>
    match cycleStep deps done at_ path x with
    | (.repeat p, _, path) => (some p, path)
    | (.next (some y), at_, path) => cycleWalk deps done t at_ path y
    | (.next none, _, path) => (none, path)

/-- con-leche: ConLeche/Driver/Graph.lean:159-180 cycleOf
**A cycle**, given the order: from the first module outside it, an import outside it, until a
module repeats; the modules from its first visit on, in import order. -/
def cycleOf (deps : Array (Array Nat)) (ord : Array Nat) : Option (List Nat) :=
  let n := deps.size
  let done := doneOf n ord
  match cycleStart n done with
  | none => none
  | some s =>
    match cycleWalk deps done (n + 1) (Array.replicate n none) #[] s with
    | (some p, path) => some (path.extract p path.size).toList
    | (none, path) => some path.toList

/-- con-leche: ConLeche/Driver/Graph.lean:155-157 rankOf
A module's rank, by name. -/
def rankOf (idx : Std.HashMap NIdx Nat) (rank : Array (Option Nat)) (m : NIdx) : Option Nat :=
  (idx[m]?).bind fun k => (rank[k]?).join

/-- con-leche: ConLeche/Driver/Graph.lean:184-186 namesOf
The closure's names. -/
def namesOf (C : List Node) : Std.HashSet NIdx :=
  C.foldl (fun s e => s.insert e.1) {}

/-- con-leche: ConLeche/Driver/Graph.lean:193-195 edgeOk
An import of `m` goes to a module of the closure of a smaller rank. -/
def edgeOk (pos : Std.HashSet NIdx) (rk : NIdx → Option Nat) (m : NIdx) (i : ImportRec) : Bool :=
  pos.contains i.module && rankLt (rk i.module) (rk m)

/-- con-leche: ConLeche/Driver/Graph.lean:197-211 verdict
**What the verdict finds wrong**: a root outside the closure, a module of it with no rank, two
with one rank, an import edge not to a smaller rank (its module and its import's).  The error
apart (`Fault.error`), as the Rust's. -/
inductive Fault where
  | root (r : NIdx)
  | unranked (m : NIdx)
  | twice
  | edge (m : NIdx) (i : Option NIdx)

/-- con-leche: ConLeche/Driver/Graph.lean:197-211 verdict
**The verdict on a closure and a numbering**: `none` when every root is in the closure, every
module of it has a rank, no two the same, and every import edge goes to a module of the closure
of a smaller rank; else the first thing wrong. -/
def verdict (roots : List NIdx) (C : List Node) (rk : NIdx → Option Nat) : Option Fault :=
  let pos := namesOf C
  if let some r := roots.find? (!pos.contains ·) then some (.root r)
  else if let some (m, _) := C.find? (fun e => (rk e.1).isNone) then some (.unranked m)
  else if !ConLeche.Frontend.Olean.distinctGo (C.map fun e => rk e.1) {} then some .twice
  else if let some (m, imps) := C.find? (fun e => !e.2.all (edgeOk pos rk e.1)) then
    some (.edge m ((imps.find? (!edgeOk pos rk m ·)).map (·.module)))
  else none

/-- con-leche: ConLeche/Driver/Graph.lean:197-211 verdict
A fault's error, upstream's message. -/
def Fault.error : Fault → AM CheckError
  | .root r => do pure (.internal s!"the root {← readName r} is not in the closure")
  | .unranked m => do pure (.internal s!"the module {← readName m} of the closure has no rank")
  | .twice => pure (.internal "two modules of the closure have the same rank")
  | .edge m i => do
    let iN ← match i with
      | some i => readName i
      | none => pure Name.anonymous
    pure (.invalid s!"the import {← readName m} → {iN} does not go to a smaller rank")

/-- con-leche: ConLeche/Driver/Graph.lean:215-218 cycleMsg
A cycle's message: its modules in import order, the first repeated at the end. -/
def cycleMsg (C : Array Node) (cyc : List Nat) : AM String := do
  let names ← cyc.mapM fun k => match C[k]? with
    | some e => do pure (toString (← readName e.1))
    | none => pure (toString Name.anonymous)
  pure (" → ".intercalate (names ++ names.take 1))

/-- con-leche: ConLeche/Driver/Graph.lean:220-238 graphOf
**The roots' closure, its graph checked**: walk the closure's headers, compute an order,
validate it; the closure, or the first thing wrong. -/
def graphOf (fs : OleanFs) (pk : OleanPins) (sp : Roots) (roots : List NIdx)
    (cmp : Option (NIdx × NIdx)) : AM (Array Node) := do
  let (lvl, seen) := dedup roots
  let C ← closureLevels fs pk sp cmp ConLeche.Driver.Graph.levelFuel lvl seen #[]
  let idx := indexOf C
  let deps := depsOf idx C
  let ord := kahn deps
  if let some cyc := cycleOf deps ord then
    fail (.invalid s!"import cycle: {← cycleMsg C cyc}")
  match verdict roots C.toList (rankOf idx (ranksOf C.size ord)) with
  | some f => fail (← f.error)
  | none => pure C

end ConRon.Arena.Modular
