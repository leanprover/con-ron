/-
# `ConRon.Arena.Frontend.Olean.Files` — from the file system (task #142)

The twin of `olean/files.rs`.

**The seam: `OleanFs`**, a record of pure functions, the operations of upstream's
`CheckerIO` class the reader uses.  The Rust's trait takes `&self`, so its
extraction is a function of its arguments (`Self → … → Result`); this record is
the same six functions.  That is what keeps Theorem 2 lockstep: the twin takes
the operations abstractly and the lane relates an instance of the trait to a
value of this record, answer for answer.  It is also upstream's model of one
snapshot (`CheckerIO`'s `ModelIO`), so that the hypothesis a later theorem states
of the binary is "these answers are one snapshot's".

The binary's value (`Arena/Main.lean`, `stdFs`) wraps `IO` in `unsafeBaseIO`, outside
every theorem.

`modDir`, `modFile`, `Name.root`, `parseModName`, `parseConstName`, `RootAt`, `oneEach`,
`Located`, `locatedOf`, `moduleSkel`, `hdrWalk` are upstream's own, over values; a module's
name is read back from its handle (`readName`) for them.
-/
module

public import ConLeche.Frontend.Olean.Files
public import ConRon.Arena.Frontend.Olean.Module

@[expose] public section

namespace ConRon.Arena.Frontend.Olean

open ConLeche
open ConLeche.Frontend.Olean (Located RootAt Roots oneEach locatedOf modDir modFile hdrWalk HdrWalk dataStart
  OLeanLevel ModFiles Part Region moduleSkel Expo)

/-- con-leche: ConLeche/Frontend/CheckerIO.lean:137-184 CheckerIO
**The checker's file reads**: a failure is the operation's message; and the read's
heartbeat (upstream's `ReadNotes`, task #484), two `liftIO` actions that change
nothing a read returns: the unit, here. -/
structure OleanFs where
  /-- whether the path names something -/
  pathExists : System.FilePath → Except String Bool
  /-- whether the path names a directory (through symbolic links) -/
  isDir : System.FilePath → Except String Bool
  /-- the path with every symbolic link resolved, absolute -/
  realPath : System.FilePath → Except String System.FilePath
  /-- a regular file's bytes -/
  readBinFile : System.FilePath → Except String ByteArray
  /-- a positional read.  Deviation: the class opens a handle (`openRead`) and reads it
  forward (`read`), since Lean's handles have no positional read; Rust's do, so the read
  keeps no state, and the reads `readHdrBytes` makes, at `0, csz, 2·csz, …`, are the
  handle's in order -/
  readRange : System.FilePath → Nat → Nat → Except String ByteArray
  /-- the size of a regular file in bytes -/
  fileSize : System.FilePath → Except String Nat
  /-- `ReadNotes.say`: one line of the heartbeat -/
  readNotesSay : String → Unit := fun _ => ()
  /-- `ReadNotes.moduleLoaded total size` -/
  readNotesModuleLoaded : Nat → Nat → Unit := fun _ _ => ()

instance : Inhabited OleanFs :=
  ⟨{ pathExists := fun _ => .error "", isDir := fun _ => .error "", realPath := fun _ => .error "", readBinFile := fun _ => .error "",
     readRange := fun _ _ _ => .error "", fileSize := fun _ => .error "" }⟩

/-- con-leche: none — the Rust's `region::display_path`: a path for a message -/
def displayPathF (s : String) : String :=
  if s.any fun c => c == '\\' || c == '"' || Display.unsafeChar c then Display.str s else s

/-- con-leche: ConLeche/Frontend/Olean/Region.lean:96-119 Part.ofBytes
**The header, validated.**  The Rust's cap on a file's size, then upstream's own. -/
def partOfBytes (path : String) (b : ByteArray) : Except CheckError Part :=
  if 2 ^ 60 ≤ b.size then
    .error (.native s!"{displayPathF path}: an .olean file past the port's size limit")
  else
    match Part.ofBytes (displayPathF path) b with
    | .ok p => .ok p
    | .error e => .error (toArenaError e)

/-- con-leche: ConLeche/Frontend/Olean/Files.lean:116-120 holdsRoot
**Whether a directory holds a root**, as Lean asks it: a directory of the root's name, or a
file of that name with `.olean`. -/
def holdsRoot (fs : OleanFs) (r : Name) (d : System.FilePath) : Except String Bool := do
  if ← fs.isDir (modDir d r) then return true
  fs.pathExists (modFile d r "olean")

/-- con-leche: ConLeche/Frontend/Olean/Files.lean:127-138 rootHits
**Where a root's modules are on the search path**: the directories holding the root; where two
or more do, their real paths compared, so that a directory listed twice, or reached through a
symbolic link, is one location. -/
def rootHits (fs : OleanFs) (sp : List System.FilePath) (r : Name) : Except String RootAt := do
  let held ← sp.mapM fun d => return (d, ← holdsRoot fs r d)
  match (held.filter (·.2)).map (·.1) with
  | [] => return .missing
  | [d] => return .dir d
  | hits@(d :: _) =>
    match oneEach (← hits.mapM fun d => return (d, ← fs.realPath d)) with
    | [_] => return .dir d
    | locs => return .twice locs

/-- con-leche: ConLeche/Frontend/Olean/Files.lean:140-142 rootAt
`rootHits`, a failed operation its answer's reason. -/
def rootAt (fs : OleanFs) (sp : List System.FilePath) (r : Name) : RootAt :=
  match rootHits fs sp r with
  | .ok a => a
  | .error e => .failed e

/-- con-leche: ConLeche/Frontend/Olean/Files.lean:144-148 lookNext
The fallback's turn: where the path holds no directory of the root, the fallback's answer. -/
def lookNext (fs : OleanFs) (fallback : List System.FilePath) (r : Name) : RootAt → RootAt
  | .missing => rootAt fs fallback r
  | a => a

/-- con-leche: ConLeche/Frontend/Olean/Files.lean:150-154 lookAt
**Where a root's modules are, on a path and its fallback**: on the path, and where no
directory of it holds the root, on the fallback. -/
def lookAt (fs : OleanFs) (path fallback : List System.FilePath) (r : Name) : RootAt :=
  lookNext fs fallback r (rootAt fs path r)

/-- con-leche: ConLeche/Frontend/Olean/Files.lean:182-202 findModule
**Find a module, as Lean does, strictly**: the one directory holding its root, on the path or
else on the fallback (`lookAt`), or why there is none (`locatedOf`).  Each read looks the root
up: the lookup's map of resolved roots (`Roots.resolve`) is a cache over one snapshot, where
the lookup answers the same each time (`findModule_rev`); the twin reads `sp.path` and
`sp.fallback` only, as the Rust's `files::Roots` holds no map. -/
def findModule (fs : OleanFs) (sp : Roots) (m : Name) : Except CheckError Located :=
  match locatedOf m (lookAt fs sp.path sp.fallback m.root) with
  | .ok l => .ok l
  | .error e => .error (toArenaError e)

/-- con-leche: ConLeche/Frontend/Olean/Files.lean:204-218 oleanFailed
**Why a module's `.olean` cannot be read at its location**: it is not there, with or without
parts beside it, or it is there and cannot be read.  A failed `pathExists` is its message. -/
def oleanFailed (fs : OleanFs) (loc : Located) (m : Name) : CheckError :=
  match fs.pathExists (modFile loc.dir m "olean") with
  | .error e => .internal e
  | .ok true => .internal s!"module {m}: {displayPathF (modFile loc.dir m "olean").toString} cannot be read"
  | .ok false =>
    match fs.pathExists (modFile loc.dir m "olean.server"),
        fs.pathExists (modFile loc.dir m "olean.private") with
    | .error e, _ => .internal e
    | _, .error e => .internal e
    | .ok s, .ok p =>
      let held := (if s then ["olean.server"] else []) ++ (if p then ["olean.private"] else [])
      if held.isEmpty then
        .internal s!"module {m}: no {m}.olean in {displayPathF loc.dir.toString}, the \
          search-path directory holding its root {m.root}"
      else
        .internal s!"module {m}: {" and ".intercalate (held.map (s!"{m}." ++ ·))} without \
          {m}.olean in {displayPathF loc.dir.toString}"

/-- con-leche: ConLeche/Frontend/Olean/Files.lean:232-238 partFailed
Why a part of a module of the module system cannot be read at its location. -/
def partFailed (fs : OleanFs) (loc : Located) (m : Name) (ext : String) : CheckError :=
  match fs.pathExists (modFile loc.dir m ext) with
  | .error e => .internal e
  | .ok true => .internal s!"module {m}: {displayPathF (modFile loc.dir m ext).toString} cannot be read"
  | .ok false => .internal s!"module {m}: a module of the module system without its {m}.{ext} \
      in {displayPathF loc.dir.toString}"

/-- con-leche: ConLeche/Frontend/Olean/Files.lean:220-224 readPart
con-leche: ConLeche/Frontend/Olean/Files.lean:226-230 readPartOr
**Read and validate one of a module's files**, `absent` saying why where it cannot be
read. -/
def readPartOr (fs : OleanFs) (p : System.FilePath) (absent : Unit → CheckError) :
    Except CheckError Part :=
  match fs.readBinFile p with
  | .error _ => .error (absent ())
  | .ok b => partOfBytes p.toString b

/-- con-leche: ConLeche/Frontend/Olean/Files.lean:244-251 hdrStep
`hdrWalk acc dataStart` ran off the bytes read. -/
def hdrShort (acc : ByteArray) : Bool :=
  match hdrWalk acc dataStart with
  | .short => true
  | _ => false

/-- con-leche: ConLeche/Frontend/Olean/Files.lean:240-242 hdrChunk
The header read's chunk size, as a number (upstream's is a `USize`). -/
def hdrChunkN : Nat := 4096

/-- con-leche: ConLeche/Frontend/CheckerIO.lean:188-203 foldReads
The reads of the header: forward in `hdrChunk` reads until the walk to the imports
array is inside what was read, or the end of the file. -/
def readHdrBytes (fs : OleanFs) (p : System.FilePath) (size : Nat) (off : Nat) (acc : ByteArray) :
    Except CheckError ByteArray :=
  if _h : off < size then
    match fs.readRange p off hdrChunkN with
    | .error e => .error (.internal e)
    | .ok c =>
      let acc := acc ++ c
      if hdrShort acc then readHdrBytes fs p size (min (off + hdrChunkN) size) acc
      else .ok acc
  else .ok acc
termination_by size - off
decreasing_by
  simp only [hdrChunkN]
  omega

/-- con-leche: ConLeche/Frontend/Olean/Files.lean:253-255 hdrFin
The header validated and the imports decoded from the bytes read. -/
def hdrFin (pk : OleanPins) (m : Name) (path : String) (acc : ByteArray) : AM (Array ImportRec) := do
  match partOfBytes path acc with
  | .error e => fail e
  | .ok _ =>
    match ← importsPre pk acc with
    | some imps => pure imps
    | none => fail (undecodable m)

/-- con-leche: ConLeche/Frontend/Olean/Files.lean:257-271 readImportsAt
**A module's imports, read off the start of its exported `.olean`** at its location.  A file
that cannot be read is `oleanFailed`'s error. -/
def readImportsAt (fs : OleanFs) (pk : OleanPins) (loc : Located) (m : Name) :
    AM (Array ImportRec) := do
  let p := modFile loc.dir m "olean"
  match fs.fileSize p with
  | .error _ => fail (oleanFailed fs loc m)
  | .ok size =>
    match readHdrBytes fs p size 0 .empty with
    | .error _ => fail (oleanFailed fs loc m)
    | .ok acc => hdrFin pk m p.toString acc

/-- con-leche: ConLeche/Frontend/Olean/Files.lean:273-279 moduleImports
**A module's imports**, off the start of its exported `.olean`, located on the search
path. -/
def moduleImports (fs : OleanFs) (pk : OleanPins) (sp : Roots) (m : NIdx) :
    AM (Array ImportRec) := do
  let mn ← readName m
  match findModule fs sp mn with
  | .error e => fail e
  | .ok loc => readImportsAt fs pk loc mn

/-- con-leche: ConLeche/Frontend/Olean/Files.lean:281-295 outsideOrEscaping
**An `M.olean` that is not a module of the module system, with a part beside it.**  Where
`M.olean` does not read on its own, it is a malformed exported part (`.invalid`, exit 1): an
exported part must not point into its `.olean.server` or `.olean.private`.  Otherwise it is a
module outside the module system with a stray part beside it. -/
def outsideOrEscaping (loc : Located) (m : Name) (ex : Part) (hasPrivate : Bool) : CheckError :=
  if (moduleSkel (Region.single ex) ex.moduleDataAddr).isNone then
    .invalid s!"module {m}: its exported part {m}.olean does not read on its own (an \
      exported part must not point outside its file, into its .olean.server or .olean.private), \
      in {displayPathF loc.dir.toString}"
  else
    .internal s!"module {m}: a module outside the module system (its {m}.olean), with \
      {if hasPrivate then s!"{m}.olean.private" else s!"{m}.olean.server"} beside it \
      in {displayPathF loc.dir.toString}"

/-- con-leche: none — a failed `pathExists`, its message -/
def pathExistsE (fs : OleanFs) (p : System.FilePath) : Except CheckError Bool :=
  match fs.pathExists p with
  | .error e => .error (.internal e)
  | .ok b => .ok b

/-- con-leche: ConLeche/Frontend/Olean/Files.lean:297-325 readFilesAt
**The files of a module a view reads at its location**, each validated.  A part beside a
classic `.olean` is no part of it, and a module of the module system has all three: reading
the parts a view needs says whether they are there, and a server view asks for the private
part's existence besides. -/
def readFilesAt (fs : OleanFs) (loc : Located) (m : Name) (level : OLeanLevel) :
    Except CheckError ModFiles := do
  let bad (what : String) : CheckError := .internal s!"module {m}: {what}"
  let ex ← readPartOr fs (modFile loc.dir m "olean") fun _ => oleanFailed fs loc m
  if level == .exported then return { exported := ex }
  if !(ModFiles.isModule { exported := ex }) then
    let hasServer ← pathExistsE fs (modFile loc.dir m "olean.server")
    let hasPrivate ← pathExistsE fs (modFile loc.dir m "olean.private")
    if hasServer || hasPrivate then
      throw (outsideOrEscaping loc m ex hasPrivate)
    return { exported := ex }
  let s ← readPartOr fs (modFile loc.dir m "olean.server") fun _ =>
    partFailed fs loc m "olean.server"
  if level == .server then
    if !(← pathExistsE fs (modFile loc.dir m "olean.private")) then
      throw (bad s!"a module of the module system without its {m}.olean.private in \
        {displayPathF loc.dir.toString}")
    return { exported := ex, server := some s }
  let p ← readPartOr fs (modFile loc.dir m "olean.private") fun _ =>
    partFailed fs loc m "olean.private"
  return { exported := ex, server := some s, «private» := some p }

/-- con-leche: ConLeche/Frontend/Olean/Files.lean:327-333 readFiles
**The files of a module a view reads**, located on the search path (`findModule`), then read
at that location (`readFilesAt`). -/
def readFiles (fs : OleanFs) (sp : Roots) (m : Name) (level : OLeanLevel) :
    Except CheckError ModFiles := do
  let loc ← findModule fs sp m
  readFilesAt fs loc m level

/-- con-leche: none — a pure failure, in `AM` -/
@[inline] def liftE {α : Type} : Except CheckError α → AM α
  | .ok a => pure a
  | .error e => fail e

/-- con-leche: ConLeche/Frontend/Olean/Files.lean:335-343 readView
**One view of a module**, located on the search path. -/
def readView (fs : OleanFs) (pk : OleanPins) (sp : Roots) (m : NIdx)
    (level : OLeanLevel) : AM ModDecoded := do
  let mn ← readName m
  let f ← liftE (readFiles fs sp mn level)
  match ← parseView pk f level with
  | some d => pure d
  | none => fail (← viewError pk mn f level)

/-- con-leche: ConLeche/Frontend/Olean/Files.lean:345-350 namesOf
**A part's name positions, off its files** (`readNamePositions`, with the reason where they do
not read). -/
def namesOf (pk : OleanPins) (m : Name) (f : ModFiles) (level : OLeanLevel) : AM NamePositions := do
  match ← readNamePositions pk f level with
  | some ps => pure ps
  | none => fail (← viewError pk m f level)

/-- con-leche: ConLeche/Frontend/Olean/Files.lean:352-357 readPartNamesAt
**One part's name positions**, read off its files at their location. -/
def readPartNamesAt (fs : OleanFs) (pk : OleanPins) (loc : Located) (m : Name) (level : OLeanLevel) :
    AM NamePositions := do
  let f ← liftE (readFilesAt fs loc m level)
  namesOf pk m f level

/-- con-leche: ConLeche/Frontend/Olean/Files.lean:359-364 readPartNames
**One part's name positions**, located on the search path. -/
def readPartNames (fs : OleanFs) (pk : OleanPins) (sp : Roots) (m : NIdx) (level : OLeanLevel) :
    AM NamePositions := do
  let mn ← readName m
  match findModule fs sp mn with
  | .error e => fail e
  | .ok loc => readPartNamesAt fs pk loc mn level

/-- con-leche: ConLeche/Frontend/Olean/Files.lean:396-413 readAllViews
**All three views of a module, each parsed whole, and the home's check of them**
(`checkViews` over the load): for the tools that compare the views. -/
def readAllViews (fs : OleanFs) (pk : OleanPins) (sp : Roots) (m : NIdx) :
    AM (AllViews × Array Expo) := do
  let mn ← readName m
  let f ← liftE (readFiles fs sp mn .private)
  match ← parseAllViews pk f with
  | none =>
    let level ←
      match ← parseView pk f .exported with
      | none => pure OLeanLevel.exported
      | some _ =>
        match ← parseView pk f .server with
        | none => pure OLeanLevel.server
        | some _ => pure OLeanLevel.private
    fail (← viewError pk mn f level)
  | some v =>
    let l ← loadView pk 0 m f
    let expo ← checkViews pk m f l
    pure (v, expo)

end ConRon.Arena.Frontend.Olean
