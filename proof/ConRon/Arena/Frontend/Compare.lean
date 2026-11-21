/-
# `ConRon.Arena.Frontend.Compare` — a challenge and its solution, the pure parts (task #165)

The twin of `frontend/compare.rs`: the name a record is found under (`recKey`), its kind for
the messages (`recKind`), a theorem read as the hole it is (`holeRecord`, `holeRecordsGo`), and
a `--constant` name that is no declaration of the challenge module
(`foreignConstant`, over the homes the challenge's read reports, `homesOf`).  `recKey` of an
inductive block with no type is `none`, upstream's `.anonymous` (the Rust's note); names are
compared by handle.
-/
module

public import ConRon.Arena.Env
public import ConRon.Arena.Monad
public import ConRon.Arena.Justify

@[expose] public section

namespace ConRon.Arena.Frontend

open ConLeche

/-- con-leche: ConLeche/Driver/Compare.lean:48-52 recKey
**The name a record is found under**: its constant's, an inductive block's first (`none` for a
block with no type). -/
def recKey : IDeclaration → Option NIdx
  | .axiomDecl cv | .defnDecl cv _ _ | .thmDecl cv _ | .opaqueDecl cv _ | .quotDecl _ cv =>
    some cv.name
  | .indDecl b _ => b.head?.map (·.name)

/-- con-leche: ConLeche/Driver/Compare.lean:54-61 recKind
A record's kind, for the messages. -/
def recKind : IDeclaration → String
  | .axiomDecl _ => "axiom"
  | .defnDecl .. => "definition"
  | .thmDecl .. => "theorem"
  | .opaqueDecl .. => "opaque constant"
  | .quotDecl .. => "quotient constant"
  | .indDecl .. => "inductive type"

/-- con-leche: ConLeche/Driver/Compare.lean:63-70 holeRecord
**A theorem read as the hole it is** (`--olean --compare`): a theorem whose file says its value
uses `sorryAx` (`used`, the read's used constants: `OleanRead.usedOf`) is the axiom of its
statement; a theorem at a built-in axiom's name keeps its own check, every other record is itself. -/
def holeRecord (used : IDeclaration → AM (Array NIdx)) (d : IDeclaration) : AM IDeclaration :=
  match d with
  | .thmDecl cv _ => do
    if ← builtinAxiomName cv.name then pure d
    else
      let us ← used d
      let sa ← pinSorryAx
      if us.contains sa then pure (.axiomDecl cv) else pure d
  | _ => pure d

/-- con-leche: ConLeche/Driver/Compare.lean:132-138 chalRecords
The cited `recs.map (holeRecord uses)`: every record through `holeRecord`, onto `out`. -/
def holeRecordsGo (used : IDeclaration → AM (Array NIdx)) (out : List IDeclaration) :
    List IDeclaration → AM (List IDeclaration)
  | [] => pure out
  | d :: ds => do
    let d' ← holeRecord used d
    holeRecordsGo used (out ++ [d']) ds

/-- con-leche: ConLeche/Driver/Compare.lean:103-110 foreignConstant
`homes[c]? != some challenge`: `c` is not a declaration of the challenge module. -/
def foreignAt (homes : Std.HashMap NIdx NIdx) (challenge c : NIdx) : Bool :=
  homes[c]? != some challenge

/-- con-leche: none — the Rust's `view::name_text`: a name for a message, `?` for a dangling
handle -/
def nameText (h : NIdx) : AM String := do
  match denoteN (← get).store.ns h with
  | some x => pure (toString x)
  | none => pure "?"

/-- con-leche: ConLeche/Driver/Compare.lean:103-110 foreignConstant
`(← r.constants).find? (homes[·]? != some r.challenge)`: the first named constant that is no
declaration of the challenge module. -/
def foreignOf (constants : Option (Array NIdx)) (challenge : NIdx)
    (homes : Std.HashMap NIdx NIdx) : Option NIdx :=
  constants.bind (·.find? (foreignAt homes challenge))

/-- con-leche: ConLeche/Driver/Compare.lean:103-110 foreignConstant
**A `--constant` name that is no declaration of the challenge module**, and why; `homes` the
challenge closure's (`homesOf`). -/
def foreignConstant (constants : Option (Array NIdx)) (challenge : NIdx)
    (homes : Std.HashMap NIdx NIdx) : AM (Option String) :=
    match foreignOf constants challenge homes with
    | none => pure none
    | some c => do
      let t := s!"--constant={← nameText c}: not a declaration of the challenge module \
        {← nameText challenge}"
      match homes[c]? with
      | some h => pure (some (t ++ s!" (it is {← nameText h}'s)"))
      | none => pure (some (t ++ " (no module of its closure declares it)"))

end ConRon.Arena.Frontend
