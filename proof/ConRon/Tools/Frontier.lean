/-
# The `sorry` frontier of a theorem (task #97-FRONTIER)

`#sorry_frontier T₁ … Tₙ` walks the dependency closure of the given
constants — the closure `#print axioms` walks: every constant mentioned by a
type or a value, transitively, inductives through their constructors — and
reports

* the **frontier**: every declaration of the closure whose OWN type or value
  mentions `sorryAx` (not merely through a dependency), grouped by its
  *owner* — the nearest name with a source range, so `foo.proof_3`,
  `foo._unary` and `foo.match_2` are all `foo` — with module and line;
* each frontier item's **fan-in**: how many (owner-level) declarations of the
  closure reach `sorryAx` ONLY through it — closing it alone clears them —
  and its **reach**: how many reach `sorryAx` through it at all;
* every **non-standard axiom** of the closure (anything but `propext`,
  `Classical.choice`, `Quot.sound` and `sorryAx`), with the declarations
  that use it directly.  There should be none; the report says so loudly.

`ConRon.Tools.Frontier.report` is the same analysis for `scripts/frontier.sh`:
it also writes TSV files and a summary, and lists the **dead weight** — the
declarations with a direct `sorry` in the given module scopes (by default
`ConRon.Bridge`/`ConRon.Refine2`) that are NOT on the frontier.

**Pruning.**  The closure contains Mathlib, and walking it is pointless: the
traversal only DESCENDS into a constant whose axiom set (Lean's own
`collectAxioms`, which for an imported constant is a lookup in the
per-module table Lean computes when it writes the `.olean`) contains
`sorryAx` or a non-standard axiom.  Every other constant is proved clean by
one lookup and never opened.  So the cost is the sorry-tainted part of the
closure, not the closure.

This module depends on Lean core only, so every library of the project can
import it.
-/
import Lean

open Lean Meta Elab Command

namespace ConRon.Tools.Frontier

/-- The axioms a closure may use without comment. -/
def standardAxioms : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]

def isInterestingAxiom (a : Name) : Bool :=
  a == ``sorryAx || !standardAxioms.contains a

/-- Configuration of `report`. -/
structure Cfg where
  /-- Directory for `<tag>.frontier.tsv`, `<tag>.dead.tsv`, `<tag>.summary.txt`. -/
  outDir : Option System.FilePath := none
  /-- File-name stem. -/
  tag : String := "frontier"
  /-- Module prefixes whose direct `sorry`s are checked for dead weight. -/
  deadScope : Array Name := #[`ConRon.Bridge, `ConRon.Refine2]
  /-- How many frontier items the human summary lists. -/
  top : Nat := 20
  deriving Inhabited

/-- One frontier item: an owner with at least one direct `sorryAx`. -/
structure Item where
  owner : Name
  module : Name
  line : Nat
  /-- The closure constants of this owner whose own term mentions `sorryAx`. -/
  members : Array Name
  fanIn : Nat := 0
  reach : Nat := 0
  /-- Lines of the item's module (0 when its file is not found). -/
  modLines : Nat := 0
  /-- Direct-`sorry` owners of the item's module that are NOT on the frontier. -/
  deadInModule : Nat := 0
  /-- The same for its lane (the module's parent, `ConRon.Refine2.Checker`). -/
  deadInLane : Nat := 0
  deriving Inhabited

structure Result where
  roots : Array Name
  /-- The union of the roots' axioms. -/
  axioms : Array Name
  /-- Non-standard axioms, each with the closure constants using it directly. -/
  nonStd : Array (Name × Array Name)
  /-- Owner-level declarations of the closure that reach `sorryAx`. -/
  tainted : Nat
  /-- Constants the traversal opened (the sorry-tainted part of the closure). -/
  opened : Nat
  /-- The frontier, sorted by fan-in, then reach. -/
  items : Array Item
  /-- Dead weight: direct-`sorry` owners in the scope and not on the frontier. -/
  dead : Array Item := #[]
  /-- Milliseconds spent on the frontier (1-5) and on the dead-weight scan (6). -/
  frontierMs : Nat := 0
  deadMs : Nat := 0
  deriving Inhabited

/-- The module declaring `n`.  `modNames` is `env.header.moduleNames`, passed
in because that is COMPUTED on every call (an `Array.map` over every module):
calling it per constant cost 16 s over a Mathlib-sized environment. -/
def moduleOf (env : Environment) (modNames : Array Name) (n : Name) : Name :=
  match env.getModuleIdxFor? n with
  | some idx => modNames[idx.toNat]!
  | none => env.mainModule

/-- The lane of a module: its parent (`ConRon.Refine2.Checker.Top` ↦
`ConRon.Refine2.Checker`). -/
def laneOf (m : Name) : Name := m.getPrefix

def isProjectModule (m : Name) : Bool :=
  (`ConRon).isPrefixOf m || (`ConLeche).isPrefixOf m

/-- The constants a declaration's own type and value mention (the edges
`CollectAxioms` follows). -/
def usedConsts (ci : ConstantInfo) : Array Name :=
  let s : NameSet := {}
  let add (s : NameSet) (e : Expr) : NameSet := e.getUsedConstants.foldl (·.insert ·) s
  let s := add s ci.type
  let s := match ci with
    | .defnInfo v => add s v.value
    | .thmInfo v => add s v.value
    | .opaqueInfo v => add s v.value
    | .inductInfo v => v.ctors.foldl (·.insert ·) s
    | _ => s
  s.toArray

/-- Does the declaration's own type or value mention `sorryAx`?  (A direct
scan: cheaper than `collectAxioms` for a declaration nothing has asked about.) -/
def mentionsSorry (ci : ConstantInfo) : Bool :=
  let has (e : Expr) := (e.find? (·.isConstOf ``sorryAx)).isSome
  has ci.type || match ci with
    | .defnInfo v => has v.value
    | .thmInfo v => has v.value
    | .opaqueInfo v => has v.value
    | _ => false

/-- The owner of `n`: `n` itself when it has a source range, else the nearest
prefix that does (`foo.proof_3` ↦ `foo`), else `n`. -/
partial def ownerOf (n : Name) : CoreM Name := do
  if (← findDeclarationRanges? n).isSome then return n
  let rec go (p : Name) : CoreM (Option Name) := do
    if p.isAnonymous then return none
    if (← getEnv).contains p then
      if (← findDeclarationRanges? p).isSome then return some p
    go p.getPrefix
  return (← go n.getPrefix).getD n

def lineOf (n : Name) : CoreM Nat := do
  return match ← findDeclarationRanges? n with
    | some r => r.range.pos.line
    | none => 0

def moduleFile (m : Name) : String :=
  (m.toString.replace "." "/") ++ ".lean"

def perModuleMap (items : Array Item) : Std.HashMap Name Nat :=
  items.foldl (fun m i => m.insert i.module (m.getD i.module 0 + 1)) {}

structure Node where
  owner : Name := .anonymous
  direct : Bool := false
  /-- Non-standard axioms used directly. -/
  directAx : Array Name := #[]
  children : Array Name := #[]
  deriving Inhabited

/-- The analysis.  See the module doc. -/
def analyze (roots : Array Name) (cfg : Cfg := {}) : CoreM Result := do
  let t0 ← IO.monoMsNow
  let env := (← getEnv).setExporting false
  let modNames := env.header.moduleNames
  let axCache ← IO.mkRef ({} : Std.HashMap Name (Array Name))
  let getAx (n : Name) : CoreM (Array Name) := do
    if let some a := (← axCache.get)[n]? then return a
    let a ← collectAxioms n
    axCache.modify (·.insert n a)
    return a
  -- 1. discovery: open only the constants whose axioms are interesting.
  let mut nodes : Std.HashMap Name Node := {}
  let mut seen : Std.HashSet Name := {}
  let mut work := roots
  let mut rootAx : NameSet := {}
  for r in roots do
    for a in ← getAx r do rootAx := rootAx.insert a
  while !work.isEmpty do
    let n := work.back!
    work := work.pop
    if seen.contains n then continue
    seen := seen.insert n
    let some ci := env.find? n | continue
    if ci matches .axiomInfo _ then continue
    let axs ← getAx n
    unless axs.any isInterestingAxiom do continue
    let used := usedConsts ci
    let mut node : Node := { direct := used.contains ``sorryAx }
    for c in used do
      if c == n then continue
      match env.find? c with
      | some (.axiomInfo _) =>
        if c != ``sorryAx && isInterestingAxiom c then
          node := { node with directAx := node.directAx.push c }
      | some _ =>
        node := { node with children := node.children.push c }
        unless seen.contains c do work := work.push c
      | none => pure ()
    nodes := nodes.insert n node
  -- 2. owners, and the frontier owners' bit positions.
  let mut ownerIdx : Std.HashMap Name Nat := {}
  let mut owners : Array Name := #[]
  let mut members : Array (Array Name) := #[]
  for (n, node) in nodes.toArray.qsort (fun a b => Name.lt a.1 b.1) do
    let o ← ownerOf n
    nodes := nodes.insert n { node with owner := o }
    if node.direct then
      match ownerIdx[o]? with
      | some i => members := members.modify i (·.push n)
      | none =>
        ownerIdx := ownerIdx.insert o owners.size
        owners := owners.push o
        members := members.push #[n]
  let width := (owners.size + 63) / 64
  let zero : Array UInt64 := Array.replicate width 0
  let orB (a b : Array UInt64) : Array UInt64 := Id.run do
    let mut r := a
    for i in [:width] do r := r.set! i (a[i]! ||| b[i]!)
    return r
  -- 3. post-order over the tainted graph (iterative: the chains are deep),
  --    bits(n) = {owner n | n direct} ∪ ⋃ bits(child); a cycle edge
  --    (inductive ↔ constructor) contributes nothing.
  let mut bits : Std.HashMap Name (Array UInt64) := {}
  let mut onStack : Std.HashSet Name := {}
  for r in roots do
    unless nodes.contains r do continue
    let mut stack : Array (Name × Nat) := #[(r, 0)]
    onStack := onStack.insert r
    while !stack.isEmpty do
      let (n, i) := stack.back!
      let node : Node := nodes.getD n default
      if h : i < node.children.size then
        stack := stack.set! (stack.size - 1) (n, i + 1)
        let c := node.children[i]
        if nodes.contains c && !bits.contains c && !onStack.contains c then
          stack := stack.push (c, 0)
          onStack := onStack.insert c
      else
        stack := stack.pop
        onStack := onStack.erase n
        let mut b := zero
        if node.direct then
          let k := ownerIdx[node.owner]!
          b := b.set! (k / 64) (b[k / 64]! ||| ((1 : UInt64) <<< (k % 64).toUInt64))
        for c in node.children do
          if let some cb := bits[c]? then b := orB b cb
        bits := bits.insert n b
  -- 4. aggregate to owners; fan-in and reach.
  let mut ownerBits : Std.HashMap Name (Array UInt64) := {}
  for (n, node) in nodes do
    if let some b := bits[n]? then
      if b.any (· != 0) then
        ownerBits := ownerBits.insert node.owner (orB (ownerBits.getD node.owner zero) b)
  let mut fanIn := Array.replicate owners.size 0
  let mut reach := Array.replicate owners.size 0
  for (o, b) in ownerBits do
    let mut cnt := 0
    let mut last := 0
    for w in [:width] do
      let x := b[w]!
      if x != 0 then
        for j in [:64] do
          if (x >>> j.toUInt64) &&& 1 == 1 then
            cnt := cnt + 1
            last := w * 64 + j
            reach := reach.modify (w * 64 + j) (· + 1)
    if cnt == 1 && owners[last]! != o then
      fanIn := fanIn.modify last (· + 1)
  let mut items : Array Item := #[]
  for i in [:owners.size] do
    let o := owners[i]!
    items := items.push { owner := o, module := moduleOf env modNames o, line := ← lineOf o,
                          members := members[i]!, fanIn := fanIn[i]!, reach := reach[i]! }
  items := items.qsort fun a b =>
    a.fanIn > b.fanIn || (a.fanIn == b.fanIn &&
      (a.reach > b.reach || (a.reach == b.reach && Name.lt a.owner b.owner)))
  -- 5. non-standard axioms and their direct users.
  let mut nonStd : Array (Name × Array Name) := #[]
  for a in rootAx.toArray.qsort Name.lt do
    if a == ``sorryAx || standardAxioms.contains a then continue
    let users := nodes.toArray.filterMap fun (n, node) =>
      if node.directAx.contains a then some n else none
    nonStd := nonStd.push (a, users.qsort Name.lt)
  let t1 ← IO.monoMsNow
  -- 6. dead weight: direct sorries in the scope, off the frontier.  Walk the
  --    scope modules' own constant arrays, not the environment.
  let mut dead : Array Item := #[]
  unless cfg.deadScope.isEmpty do
    let inScope (m : Name) := cfg.deadScope.any (·.isPrefixOf m)
    let mut deadOwners : Std.HashMap Name (Array Name) := {}
    let mut cands : Array ConstantInfo := #[]
    for h : i in [:modNames.size] do
      if inScope modNames[i] then
        if let some md := env.header.moduleData[i]? then
          cands := cands ++ md.constants
    for ci in env.constants.map₂.toList.map (·.2) do  -- the current file's own
      if inScope env.mainModule then cands := cands.push ci
    for ci in cands do
      if ci matches .axiomInfo _ then continue
      unless mentionsSorry ci do continue
      let o ← ownerOf ci.name
      if ownerIdx.contains o then continue
      deadOwners := deadOwners.insert o ((deadOwners.getD o #[]).push ci.name)
    for (o, ms) in deadOwners do
      dead := dead.push { owner := o, module := moduleOf env modNames o, line := ← lineOf o,
                          members := ms.qsort Name.lt }
    dead := dead.qsort fun a b =>
      Name.lt a.module b.module || (a.module == b.module && a.line < b.line)
  -- 7. each frontier item's context: how big is its module, and how much
  --    `sorry` sits in its module and lane OUTSIDE the closure (a sorried
  --    top-level statement hides the subtree its proof will need).
  let byMod := perModuleMap dead
  let byLane := dead.foldl (fun m i => m.insert (laneOf i.module) (m.getD (laneOf i.module) 0 + 1))
    ({} : Std.HashMap Name Nat)
  let mut lines : Std.HashMap Name Nat := {}
  for i in items do
    unless lines.contains i.module do
      let f : System.FilePath := moduleFile i.module
      let n ← (do return (← IO.FS.readFile f).splitOn "\n" |>.length) <|> pure 0
      lines := lines.insert i.module n
  items := items.map fun i => { i with
    modLines := lines.getD i.module 0, deadInModule := byMod.getD i.module 0,
    deadInLane := byLane.getD (laneOf i.module) 0 }
  let t2 ← IO.monoMsNow
  return { roots, axioms := rootAx.toArray.qsort Name.lt, nonStd,
           frontierMs := t1 - t0, deadMs := t2 - t1,
           tainted := ownerBits.size, opened := nodes.size, items, dead }

/-- Counts per module, largest first. -/
def perModule (items : Array Item) : Array (Name × Nat) :=
  (perModuleMap items).toArray.qsort fun a b => a.2 > b.2 || (a.2 == b.2 && Name.lt a.1 b.1)

def pad (s : String) (n : Nat) : String :=
  "".pushn ' ' (n - s.length) ++ s

/-- The one line `scripts/gates.sh` prints per root. -/
def summaryLine (r : Result) : String :=
  let roots := ", ".intercalate (r.roots.map toString).toList
  let top := match r.items[0]? with
    | some i => s!"; top {i.owner} (fan-in {i.fanIn}, reach {i.reach})"
    | none => ""
  let ax := if r.nonStd.isEmpty then "" else
    s!"; !!! {r.nonStd.size} NON-STANDARD AXIOM(S): " ++
      ", ".intercalate (r.nonStd.map (toString ·.1)).toList
  s!"frontier {roots}: {r.items.size} items in {(perModule r.items).size} modules, " ++
    s!"{r.tainted} tainted decls{top}; dead weight {r.dead.size}{ax}"

/-- The human report. -/
def render (r : Result) (top : Nat := 20) (showDead := true) : String := Id.run do
  let mut out := summaryLine r ++ "\n"
  out := out ++ s!"  axioms: {r.axioms.toList}\n"
  if r.nonStd.isEmpty then
    out := out ++ "  non-standard axioms: none\n"
  else
    for (a, users) in r.nonStd do
      out := out ++ s!"  !!! NON-STANDARD AXIOM {a} — used directly by {users.toList}\n"
  let outside := r.items.filter (!isProjectModule ·.module)
  unless outside.isEmpty do
    out := out ++ s!"  !!! {outside.size} frontier item(s) OUTSIDE ConRon/ConLeche: " ++
      s!"{(outside.map (·.owner)).toList}\n"
  out := out ++ s!"  opened {r.opened} constants (the sorry-tainted part of the closure)\n"
  out := out ++ "  per module:\n"
  for (m, k) in perModule r.items do
    out := out ++ s!"    {pad (toString k) 4}  {moduleFile m}\n"
  out := out ++ s!"  top {min top r.items.size} by fan-in — fan-in, reach; then the item's " ++
    "module: lines, and the direct-sorry decls OFF the frontier in that module / its lane " ++
    "(large = the item is a sorried top whose subtree is not yet in the closure):\n"
  for i in r.items[:top] do
    out := out ++ s!"    {pad (toString i.fanIn) 5} {pad (toString i.reach) 5}  " ++
      s!"{pad (toString i.modLines) 5}L {pad (toString i.deadInModule) 4} {pad (toString i.deadInLane) 4}  " ++
      s!"{i.owner}  {moduleFile i.module}:{i.line}\n"
  if showDead then
    out := out ++ s!"  dead weight: {r.dead.size} direct-sorry decls off the frontier, per module:\n"
    for (m, k) in perModule r.dead do
      out := out ++ s!"    {pad (toString k) 4}  {moduleFile m}\n"
  return out

def tsvItems (items : Array Item) (withCounts : Bool) : String := Id.run do
  let mut out := if withCounts then
      "fan_in\treach\tmodule_lines\tdead_in_module\tdead_in_lane\towner\tfile\tline\tmembers\n"
    else "owner\tfile\tline\tmembers\n"
  for i in items do
    let ms := ",".intercalate (i.members.map toString).toList
    let row := s!"{i.owner}\t{moduleFile i.module}\t{i.line}\t{ms}\n"
    out := out ++ (if withCounts then
      s!"{i.fanIn}\t{i.reach}\t{i.modLines}\t{i.deadInModule}\t{i.deadInLane}\t" else "") ++ row
  return out

/-- `scripts/frontier.sh`'s entry point: analyse, write the files, return the
summary text. -/
def report (roots : Array Name) (cfg : Cfg := {}) : CoreM String := do
  let t0 ← IO.monoMsNow
  let r ← analyze roots cfg
  let t1 ← IO.monoMsNow
  let text := render r cfg.top ++
    s!"  analysis time: {t1 - t0} ms (frontier {r.frontierMs} ms, dead weight {r.deadMs} ms)\n"
  if let some d := cfg.outDir then
    IO.FS.createDirAll d
    IO.FS.writeFile (d / s!"{cfg.tag}.frontier.tsv") (tsvItems r.items true)
    IO.FS.writeFile (d / s!"{cfg.tag}.dead.tsv") (tsvItems r.dead false)
    IO.FS.writeFile (d / s!"{cfg.tag}.summary.txt") text
    IO.FS.writeFile (d / s!"{cfg.tag}.line.txt") (summaryLine r ++ "\n")
  return text

/-- `#sorry_frontier T₁ … Tₙ`: the frontier of the given theorems (no dead
weight — that needs the whole tier imported, which is `scripts/frontier.sh`'s
job). -/
syntax (name := sorryFrontierCmd) "#sorry_frontier" (ppSpace ident)+ : command

@[command_elab sorryFrontierCmd] def elabSorryFrontier : CommandElab := fun stx => do
  let roots ← liftCoreM <| stx[1].getArgs.mapM realizeGlobalConstNoOverloadWithInfo
  let r ← liftCoreM <| analyze roots { deadScope := #[] }
  logInfo (render r (showDead := false))

end ConRon.Tools.Frontier
