/-
# `ConRon.Arena.Frontend.Olean.Lazy` — a module's load, its theorems' values left in the file (upstream task #481)

The twin of `olean/lazy.rs`.  The pure helpers over bytes are upstream's own:
`usesNames`, `kindCode`, `kindOfCode`, `lazyRoots`, `refBase`, `refModule`, `refLoc`.
**The two DAG walks are the Rust's** (`usesGo`, `frontierWalk`): upstream's are
`partial`, so they carry `closureFuel` here as in the Rust, a walk's stack a `List`
with its top at the head (the Rust's `Vec` and its top index).  Spent fuel is a failed
read in `usesGo` and the frontier as it stands in `frontierWalk`, as the Rust's.  What
is twinned besides holds a value: the names a constant mentions, the stored constant,
a theorem's reference (an interned `bvar`), the frontier, and the load around them.
-/
module

public import ConLeche.Frontend.Olean.Lazy
public import ConLeche.Frontend.Olean.Closure
public import ConRon.Arena.Frontend.Olean.View

@[expose] public section

namespace ConRon.Arena.Frontend.Olean

open ConLeche
open ConLeche.Frontend.Olean (Region CEntryF CKindF ModSkel ModFiles OLeanLevel kName kLevel kExpr
  kLevels marked mark marksAt maxLoc zeros moduleSkel usesNames usesNat usesStr lazyRoots
  refBase kindCode kindOfCode kidTable closureFuel Table Table.add)

/-- con-leche: ConLeche/Frontend/Olean/Lazy.lean:51-59 pushKid
The kid in field `i` of the expression object at `g`, onto a walk's stack (its head
the top); `none` where the field does not point below `g`. -/
@[inline] def pushKid (r : Region) (g i : Nat) : Option (List Nat) → Option (List Nat)
  | none => none
  | some st =>
    match r.down g (r.fld g i) with
    | some c => some (c :: st)
    | none => none

/-- con-leche: ConLeche/Frontend/Olean/Lazy.lean:61-104 usesGo
**The DAG walk of what an expression mentions**: each object once in a walk (`stamps`,
by slot, holds the walk that saw it last), left to right, every constant's name field
into `out`, as it stands in the file, and `usesNat`/`usesStr` at a literal.  `none` at
an object no expression is stored as, and where the fuel runs out (one per pop). -/
def usesGo (r : Region) (stamps : Array Nat) (stamp : Nat) (out : Array UInt64) :
    Nat → List Nat → Option (Array Nat × Array UInt64)
  | _, [] => some (stamps, out)
  | 0, _ :: _ => none
  | fuel + 1, g :: stack =>
    let s := g / 8
    if stamps[s]! == stamp then usesGo r stamps stamp out fuel stack else
    let stamps := stamps.set! s stamp
    if !r.fits g then none else
    match r.tag g, r.nobjs g with
    | 0, 1 | 3, 1 => usesGo r stamps stamp out fuel stack
    | 4, 2 => usesGo r stamps stamp (out.push (r.fld g 0)) fuel stack
    | 5, 2 =>
      match pushKid r g 0 (pushKid r g 1 (some stack)) with
      | some st => usesGo r stamps stamp out fuel st
      | none => none
    | 6, 3 | 7, 3 =>
      match pushKid r g 1 (pushKid r g 2 (some stack)) with
      | some st => usesGo r stamps stamp out fuel st
      | none => none
    | 8, 4 =>
      match pushKid r g 1 (pushKid r g 2 (pushKid r g 3 (some stack))) with
      | some st => usesGo r stamps stamp out fuel st
      | none => none
    | 9, 1 =>
      match r.down g (r.fld g 0) with
      | some c =>
        if r.isCtor c 0 1 then usesGo r stamps stamp (out.push usesNat) fuel stack
        else if r.isCtor c 1 1 then usesGo r stamps stamp (out.push usesStr) fuel stack
        else none
      | none => none
    | 10, 2 =>
      match pushKid r g 1 (some stack) with
      | some st => usesGo r stamps stamp out fuel st
      | none => none
    | 11, 3 =>
      match pushKid r g 2 (some stack) with
      | some st => usesGo r stamps stamp out fuel st
      | none => none
    | _, _ => none

/-- con-leche: ConLeche/Frontend/Olean/Lazy.lean:106-116 usesRoots
One constant's expressions, in order, one walk, each root with the walk's fuel. -/
def usesRoots (r : Region) (stamps : Array Nat) (stamp : Nat) (out : Array UInt64) :
    List UInt64 → Option (Array Nat × Array UInt64)
  | [] => some (stamps, out)
  | v :: vs =>
    match r.loc v with
    | none => none
    | some g =>
      match usesGo r stamps stamp out closureFuel [g] with
      | none => none
      | some (stamps, out) => usesRoots r stamps stamp out vs

/-- con-leche: ConLeche/Frontend/Olean/Lazy.lean:118-126 usesOf
**What each constant mentions**, as `usesGo` writes it: its statement and its values
(`CEntryF.exprs`), a walk of its own per constant. -/
def usesOf (r : Region) (stamps : Array Nat) (stamp : Nat) :
    List (CEntryF UInt64 UInt64) → Array (Array UInt64) → Option (Array (Array UInt64))
  | [], outs => some outs
  | c :: cs, outs =>
    match usesRoots r stamps stamp #[] c.exprs with
    | none => none
    | some (stamps, out) => usesOf r stamps (stamp + 1) cs (outs.push out)

/-- con-leche: ConLeche/Frontend/Olean/Lazy.lean:134-137 addUse
A name once, in first-visit order. -/
@[inline] def addUse (x : Std.HashSet NIdx × Array NIdx) (n : NIdx) :
    Std.HashSet NIdx × Array NIdx :=
  if x.1.contains n then x else (x.1.insert n, x.2.push n)

/-- con-leche: ConLeche/Frontend/Olean/Lazy.lean:139-150 usesRead
**What a constant mentions, as names**: in first-visit order, each once, and the
literal dependencies lean4export adds (the reader's pins).  Where a name does not
read, it is left out. -/
def usesRead (pk : OleanPins) (nm : UInt64 → Option NIdx) (out : Array UInt64) : Array NIdx :=
  (out.foldl (fun x v =>
    if v == usesNat then addUse x pk.nNat
    else if v == usesStr then addUse (addUse x pk.nCharOfNat) pk.nStringOfList
    else match nm v with
      | some n => addUse x n
      | none => x) ((Std.HashSet.emptyWithCapacity 64 : Std.HashSet NIdx), #[])).2

/-- con-leche: ConLeche/Frontend/Olean/Lazy.lean:164-168 CEntry
**One stored constant**, as the merge and the emitter need it: the constant read (a
theorem's value its reference) and the constants it mentions.  Deviation: upstream's
`uses` is a `Subarray` of one array per module (`usesFlat`, con-leche task #489), so that
Lean's allocator frees what the emission has read in one piece; the sequence is the same,
and this keeps an array per constant, as the Rust, which has no shared slice short of an
`Rc`. -/
structure CEntry where
  c : CEntryF NIdx EIdx
  uses : Array NIdx := #[]

/-- con-leche: ConLeche/Frontend/Olean/Lazy.lean:172-173 CEntry.skipped
`CKindF.skipped` of a stored constant. -/
@[inline] def CEntry.skipped (c : CEntry) : Bool := c.c.kind.skipped

/-- con-leche: ConLeche/Frontend/Olean/Lazy.lean:175-180 Loaded
**A loaded module**: its constants at the private level, and the frontier its
theorems' values are read over. -/
structure Loaded where
  name : NIdx
  constants : Array CEntry
  frontier : Frontier

/-- con-leche: ConLeche/Frontend/Olean/Lazy.lean:187-190 valueRef
**A theorem's value, until its check reads it**: the value at location `g` of module
`i` of the closure's order, as an expression. -/
def valueRef (i g : Nat) : AM EIdx := internE (.bvar (g * refBase + i))

/-- con-leche: ConLeche/Frontend/Olean/Lazy.lean:204-216 lazyEntry
**A constant read, a theorem's value as its reference.**  As the Rust, `g` must be
below `refBase` too (its code is a word). -/
def lazyEntry (pk : OleanPins) (r : Region) (st : DS) (i : Nat) (s : CEntryF UInt64 UInt64) :
    AM (Option (CEntryF NIdx EIdx)) := do
  match s.kind with
  | .thm v all =>
    unless i < refBase do return none
    let some g := r.loc v | return none
    unless g < refBase do return none
    let some name := st.nameOf pk r s.name | return none
    let some lps := s.levelParams.mapM (st.nameOf pk r) | return none
    let some type := st.exprOf r s.type | return none
    let some all := all.mapM (st.nameOf pk r) | return none
    pure (some ⟨name, lps, type, .thm (← valueRef i g) all⟩)
  | _ => entryMap (st.read pk r) s

/-- con-leche: ConLeche/Frontend/Olean/Lazy.lean:218-231 lazyEntries
`lazyEntry` of every constant, each with what it mentions (`outs`, by position). -/
def lazyEntries (pk : OleanPins) (r : Region) (st : DS) (i : Nat) (outs : Array (Array UInt64)) :
    Nat → List (CEntryF UInt64 UInt64) → AM (Option (List CEntry))
  | _, [] => pure (some [])
  | k, s :: ss => do
    match ← lazyEntry pk r st i s with
    | none => pure none
    | some e =>
      match ← lazyEntries pk r st i outs (k + 1) ss with
      | none => pure none
      | some es => pure (some ({ c := e, uses := usesRead pk (st.nameOf pk r) (outs.getD k #[]) } :: es))

/-- con-leche: ConLeche/Frontend/Olean/Lazy.lean:243-266 frontierWalk
**The objects the load read that the values reach directly**: a walk from the values
over what the load did not read (each object once, `seen`), stopping at what it did
(`env`), which goes into `fr`.  Entries are a location and a kind's code.  Spent fuel
(one per pop) leaves `fr` as it is: the frontier is a matter of speed alone. -/
def frontierWalk (r : Region) (env : ByteArray) (seen fr : ByteArray) :
    Nat → List Nat → ByteArray
  | _, [] => fr
  | 0, _ :: _ => fr
  | fuel + 1, e :: stack =>
    let g := e / 8 * 8
    let k := kindOfCode (e % 8)
    let s := g / 8
    if marked env k s then frontierWalk r env seen (mark fr k s) fuel stack
    else if marked seen k s then frontierWalk r env seen fr fuel stack
    else
      let seen := mark seen k s
      match kidTable k (r.tag g) (r.nobjs g) with
      | none => frontierWalk r env seen fr fuel stack
      | some fs =>
        let stack := fs.foldl (fun st (f : Nat × UInt8 × Bool) =>
          if f.2.2 && r.fld g f.1 == 1 then st
          else match r.down g (r.fld g f.1) with
            | some c => (c + kindCode f.2.1) :: st
            | none => st) stack
        frontierWalk r env seen fr fuel stack

/-- con-leche: ConLeche/Frontend/Olean/Lazy.lean:273-282 frontierStep
Slot `p` of `fr`, where the marks `m` hold it too, into the frontier. -/
@[inline] def frontierStep (m fr : ByteArray) (st : DS) (p : Nat) (b : Frontier) : Frontier :=
  if marksAt fr p == 0 then b else
  let c := 8 * p
  let { names, levels, lists, exprs } := b
  let names := if marked fr kName p && marked m kName p then
    names.add c (st.names.getD p default) else names
  let levels := if marked fr kLevel p && marked m kLevel p then
    levels.add c (st.levels.getD p default) else levels
  let lists := if marked fr kLevels p && marked m kLevels p then
    lists.add c (st.lists.getD p default) else lists
  let exprs := if marked fr kExpr p && marked m kExpr p then
    exprs.add c (st.exprs.getD p default) else exprs
  { names, levels, lists, exprs }

/-- con-leche: ConLeche/Frontend/Olean/Lazy.lean:284-288 frontierOf
**The frontier**: the slots from `p` to `n` of `fr` that the marks `m` hold, with
their values in the passes' memo.  Ascending, so each table's keys are. -/
def frontierOf (m fr : ByteArray) (st : DS) (n p : Nat) (b : Frontier) : Frontier :=
  if p < n then frontierOf m fr st n (p + 1) (frontierStep m fr st p b) else b
termination_by n - p

/-- con-leche: ConLeche/Frontend/Olean/Lazy.lean:292-311 loadAt
The name and expression roots of the load. -/
def loadRoots (sk : ModSkel) (skels : List (CEntryF UInt64 UInt64)) : List UInt64 × List UInt64 :=
  (sk.imports.map (·.module) ++ skels.flatMap CEntryF.names, skels.flatMap CEntryF.exprs)

/-- con-leche: ConLeche/Frontend/Olean/Lazy.lean:292-311 loadAt
The imports read off the memo, against those at the start of `M.olean`. -/
def loadImports (pk : OleanPins) (r : Region) (st : DS) (sk : ModSkel) (f : ModFiles) : AM Bool := do
  let some imports := sk.imports.mapM (fun i => i.mapM (st.nameOf pk r)) | return false
  match ← importsPre pk f.exported.bytes with
  | some pre => pure (pre == imports.toArray)
  | none => pure false

/-- con-leche: ConLeche/Frontend/Olean/Lazy.lean:292-311 loadAt
The values' locations, each with the expression kind's code: the walk's start. -/
def valueRoots (r : Region) (skels : List (CEntryF UInt64 UInt64)) : List Nat :=
  skels.filterMap fun c => match c.kind with
    | .thm v _ => (r.loc v).map (· + kindCode kExpr)
    | _ => none

/-- con-leche: ConLeche/Frontend/Olean/Lazy.lean:292-311 loadAt
**The load of a module's private view**, everything but its theorems' values.
`none` where the part of the view it reads does not read: `viewError` says why. -/
def loadAt (pk : OleanPins) (i : Nat) (m : NIdx) (f : ModFiles) : AM (Option Loaded) := do
  let some (r, a) := f.viewRegion .private | return none
  unless ← constNamesOk pk r a do return none
  let some sk := moduleSkel r a | return none
  let some skels ← constsSkel r sk.consts | return none
  let (namesB, exprsAll) := loadRoots sk skels
  let n := maxLoc r exprsAll (maxLoc r namesB 0) / 8 + 1
  let some outs := usesOf r (Array.replicate n 0) 1 skels (Array.mkEmpty skels.length) | return none
  let some (nm, ms, st) ← runMarked pk r (namesB ++ usesNames outs) (skels.flatMap lazyRoots)
    | return none
  unless ← loadImports pk r st sk f do return none
  let some cs ← lazyEntries pk r st i outs 0 skels | return none
  let fr := frontierWalk r ms (zeros n) (zeros n) closureFuel (valueRoots r skels).reverse
  pure (some { name := m, constants := cs.toArray, frontier := frontierOf ms fr st nm 0 {} })

/-- con-leche: ConLeche/Frontend/Olean/Lazy.lean:313-317 loadView
**The load, with the reason where it does not read.** -/
def loadView (pk : OleanPins) (i : Nat) (m : NIdx) (f : ModFiles) : AM Loaded := do
  match ← loadAt pk i m f with
  | some l => pure l
  | none => fail (← viewError pk (← readName m) f .private)

end ConRon.Arena.Frontend.Olean
