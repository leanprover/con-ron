/-
# `ConRon.Arena.Frontend.Olean.Files` — from the file system (task #142)

The twin of `olean/files.rs`.

**The seam: `OleanFs`**, a record of pure functions, the operations of upstream's
`CheckerIO` class the reader uses.  The Rust's trait takes `&self`, so its
extraction is a function of its arguments (`Self → … → Result`); this record is
the same five functions.  That is what keeps Theorem 2 lockstep: the twin takes
the operations abstractly and the lane relates an instance of the trait to a
value of this record, answer for answer.  It is also upstream's model of one
snapshot (`CheckerIO`'s `ModelIO`), so that the hypothesis a later theorem states
of the binary is "these answers are one snapshot's".

The binary's value (`Arena/Main.lean`, `stdFs`) wraps `IO` in `unsafeBaseIO`, outside
every theorem.

`modFile`, `parseModName`, `parseConstName`, `Located`, `partExts`, `locateOf`,
`hdrWalk` are upstream's own, over values; a module's name is read back from its
handle (`readName`) for them.
-/
module

public import ConLeche.Frontend.Olean.Files
public import ConRon.Arena.Frontend.Olean.Module

@[expose] public section

namespace ConRon.Arena.Frontend.Olean

open ConLeche
open ConLeche.Frontend.Olean (Located modFile partExts locateOf hdrWalk HdrWalk dataStart OLeanLevel ModFiles Part
  Expo)

/-- con-leche: ConLeche/Frontend/CheckerIO.lean:117-159 CheckerIO
-- con-leche: CHANGED since 7cb7a45c — re-port, re-test, re-prove Files.OleanFs_bridge, then delete this line
**The checker's file reads**: a failure is the operation's message. -/
structure OleanFs where
  /-- whether the path names something -/
  pathExists : System.FilePath → Except String Bool
  /-- the path with every symbolic link resolved, absolute -/
  realPath : System.FilePath → Except String System.FilePath
  /-- a regular file's bytes -/
  readBinFile : System.FilePath → Except String ByteArray
  /-- a positional read -/
  readRange : System.FilePath → Nat → Nat → Except String ByteArray
  /-- the size of a regular file in bytes -/
  fileSize : System.FilePath → Except String Nat

instance : Inhabited OleanFs :=
  ⟨⟨fun _ => .error "", fun _ => .error "", fun _ => .error "", fun _ _ _ => .error "", fun _ => .error ""⟩⟩

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

/-- con-leche: ConLeche/Frontend/Olean/Files.lean:87-96 locateIn
The real paths of a module's three files in one directory, `none` where absent. -/
def locateIn (fs : OleanFs) (m : Name) (d : System.FilePath) :
    Except String (System.FilePath × List (Option String)) := do
  let files ← partExts.mapM fun e => do
    let p := modFile d m e
    if ← fs.pathExists p then
      return some (← fs.realPath p).toString
    else return none
  return (d, files)

/-- con-leche: ConLeche/Frontend/Olean/Files.lean:98-103 locateHits
**The search path's directories holding any of module `m`'s files**, in order. -/
def locateHits (fs : OleanFs) (sp : List System.FilePath) (m : Name) :
    Except String (Array (System.FilePath × List (Option String))) := do
  let hs ← sp.mapM (locateIn fs m)
  return (hs.filter fun h => h.2.any (·.isSome)).toArray

/-- con-leche: ConLeche/Frontend/Olean/Files.lean:139-160 findModule
**Find a module, strictly.** -/
def findModule (fs : OleanFs) (sp : List System.FilePath) (m : Name) : Except CheckError Located :=
  match locateHits fs sp m with
  | .ok hits =>
    match locateOf m hits with
    | .ok l => .ok l
    | .error e => .error (toArenaError e)
  | .error e => .error (.internal s!"module {m}: locating its files: {e}")

/-- con-leche: ConLeche/Frontend/Olean/Files.lean:162-166 readPart
Read and validate one file. -/
def readPart (fs : OleanFs) (p : System.FilePath) : Except CheckError Part :=
  match fs.readBinFile p with
  | .error e => .error (.internal e)
  | .ok b => partOfBytes p.toString b

/-- con-leche: ConLeche/Frontend/Olean/Files.lean:172-179 hdrStep
`hdrWalk acc dataStart` ran off the bytes read. -/
def hdrShort (acc : ByteArray) : Bool :=
  match hdrWalk acc dataStart with
  | .short => true
  | _ => false

/-- con-leche: ConLeche/Frontend/Olean/Files.lean:168-170 hdrChunk
The header read's chunk size, as a number (upstream's is a `USize`). -/
def hdrChunkN : Nat := 4096

/-- con-leche: ConLeche/Frontend/CheckerIO.lean:163-177 foldReads
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

/-- con-leche: ConLeche/Frontend/Olean/Files.lean:181-183 hdrFin
The header validated and the imports decoded from the bytes read. -/
def hdrFin (pk : OleanPins) (m : Name) (path : String) (acc : ByteArray) : AM (Array ImportRec) := do
  match partOfBytes path acc with
  | .error e => fail e
  | .ok _ =>
    match ← importsPre pk acc with
    | some imps => pure imps
    | none => fail (undecodable m)

/-- con-leche: ConLeche/Frontend/Olean/Files.lean:185-197 readImportsAt
**A module's imports, read off the start of its exported `.olean`** at its location. -/
def readImportsAt (fs : OleanFs) (pk : OleanPins) (loc : Located) (m : Name) :
    AM (Array ImportRec) := do
  let p := modFile loc.dir m "olean"
  match fs.fileSize p with
  | .error e => fail (.internal e)
  | .ok size =>
    match readHdrBytes fs p size 0 .empty with
    | .error e => fail e
    | .ok acc => hdrFin pk m p.toString acc

/-- con-leche: ConLeche/Frontend/Olean/Files.lean:199-205 moduleImports
**A module's imports**, off the start of its exported `.olean`, located on the search
path. -/
def moduleImports (fs : OleanFs) (pk : OleanPins) (sp : List System.FilePath) (m : NIdx) :
    AM (Array ImportRec) := do
  let mn ← readName m
  match findModule fs sp mn with
  | .error e => fail e
  | .ok loc => readImportsAt fs pk loc mn

/-- con-leche: ConLeche/Frontend/Olean/Files.lean:207-236 readFiles
**The files of a module a view reads**, each validated, located on the search path.
A part beside a classic `.olean` is no part of it, and a module of the module system
has all three. -/
def readFiles (fs : OleanFs) (sp : List System.FilePath) (m : Name) (level : OLeanLevel) :
    Except CheckError ModFiles := do
  let loc ← findModule fs sp m
  let bad (what : String) : CheckError := .internal s!"module {m}: {what}"
  let ex ← readPart fs (modFile loc.dir m "olean")
  if level == .exported then return { exported := ex }
  if !(ModFiles.isModule { exported := ex }) then
    if loc.hasServer || loc.hasPrivate then
      throw (bad s!"a module outside the module system (its {m}.olean), with \
        {if loc.hasPrivate then s!"{m}.olean.private" else s!"{m}.olean.server"} beside it \
        in {displayPathF loc.dir.toString}")
    return { exported := ex }
  if !loc.hasServer then
    throw (bad s!"a module of the module system without its {m}.olean.server in {displayPathF loc.dir.toString}")
  if !loc.hasPrivate then
    throw (bad s!"a module of the module system without its {m}.olean.private in {displayPathF loc.dir.toString}")
  let s ← readPart fs (modFile loc.dir m "olean.server")
  if level == .server then return { exported := ex, server := some s }
  let p ← readPart fs (modFile loc.dir m "olean.private")
  return { exported := ex, server := some s, «private» := some p }

/-- con-leche: none — a pure failure, in `AM` -/
@[inline] def liftE {α : Type} : Except CheckError α → AM α
  | .ok a => pure a
  | .error e => fail e

/-- con-leche: ConLeche/Frontend/Olean/Files.lean:238-246 readView
**One view of a module**, located on the search path. -/
def readView (fs : OleanFs) (pk : OleanPins) (sp : List System.FilePath) (m : NIdx)
    (level : OLeanLevel) : AM ModDecoded := do
  let mn ← readName m
  let f ← liftE (readFiles fs sp mn level)
  match ← parseView pk f level with
  | some d => pure d
  | none => fail (← viewError pk mn f level)

/-- con-leche: ConLeche/Frontend/Olean/Files.lean:248-261 readAllViews
**All three views of a module, checked against each other**: its home's read. -/
def readAllViews (fs : OleanFs) (pk : OleanPins) (sp : List System.FilePath) (m : NIdx) :
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
    let expo ← checkViews pk mn f v
    pure (v, expo)

end ConRon.Arena.Frontend.Olean
