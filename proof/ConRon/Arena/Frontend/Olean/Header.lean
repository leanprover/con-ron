/-
# `ConRon.Arena.Frontend.Olean.Header` — imports off the start of a file (task #142)

The twin of `olean/header.rs`.  `HdrWalk`, `wordUp`, `hdrAdv` and `hdrWalk` are
upstream's own: they read bytes.  What names an import interns.
-/
module

public import ConLeche.Frontend.Olean.Header
public import ConRon.Arena.Frontend.Olean.Spec

@[expose] public section

namespace ConRon.Arena.Frontend.Olean

open ConLeche
open ConLeche.Frontend.Olean (Region ImportF importSkel hdrWalk dataStart rdU64 tagArray rdU8 Part)

/-- con-leche: ConLeche/Frontend/Olean/Header.lean:67-73 importsIn
`imps.mapM fun i => importSkel r i >>= ImportF.mapM (nameP r)`. -/
def importsRead (pk : OleanPins) (r : Region) (imps : Array Nat) : AM (Option (Array ImportRec)) :=
  (imps.mapM (m := OptionT AM) fun i => do
    let sk ← OptionT.mk (pure (importSkel r i))
    sk.mapM (m := OptionT AM) fun v => OptionT.mk (nameP pk r v)).run

/-- con-leche: ConLeche/Frontend/Olean/Header.lean:67-73 importsIn
The imports array at location `c` of a region, decoded. -/
def importsIn (pk : OleanPins) (r : Region) (c : Nat) : AM (Option (Array ImportRec)) :=
  if r.tag c == tagArray then
    let n := (rdU64 r.bytes (c + 8)).toNat
    if c + 24 + 8 * n ≤ r.fileEnd c then
      match r.objArrayGo c (c + 24) n 0 (Array.mkEmpty n) with
      | none => pure none
      | some imps => importsRead pk r imps
    else pure none
  else pure none

/-- con-leche: ConLeche/Frontend/Olean/Header.lean:75-83 importsPre
**A module's imports from the start of its exported file**: the walk to the imports
array, and the array decoded in the region of the bytes up to its end. -/
def importsPre (pk : OleanPins) (b : ByteArray) : AM (Option (Array ImportRec)) :=
  match hdrWalk b dataStart with
  | .found c e =>
    let pre := b.extract 0 e
    importsIn pk (Region.single ⟨rdU64 pre 80, pre⟩) c
  | _ => pure none

end ConRon.Arena.Frontend.Olean
