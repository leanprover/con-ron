/-
# `ConRon.Arena.Frontend.Olean.Fast` — the fast decoder (task #142)

The twin of `olean/fast.rs`.  **The mark pass is upstream's own**: `zeros`, the kinds,
`marksAt`, `mark`, `markPtr`, `markName`, `markLevel`, `markLevels`, `markExpr`,
`markSlot`, `markPass`, `failedM`, `markRoot`, `maxLoc`, `CEntryF.names`,
`CEntryF.exprs` read bytes and hold pointers.  What is twinned holds a value: the
memo, the upward sweep, `runPasses` around them, and `parseMany`.

**The memo holds handles.**  `DS`'s arrays are `Array NIdx`, ...; the filler is
`default`, the word `0`, never read before the object below it is built.
-/
module

public import ConLeche.Frontend.Olean.Fast
public import ConRon.Arena.Frontend.Olean.Spec

@[expose] public section

namespace ConRon.Arena.Frontend.Olean

open ConLeche
open ConLeche.Frontend.Olean (Region CEntryF ModSkel kName kLevel kExpr kLevels marked marksAt markRoot maxLoc
  markPass failedM zeros moduleSkel constSkel ImportF)

/-- con-leche: ConLeche/Frontend/Olean/Fast.lean:89-94 DS
The decoder's values, per slot, one array per kind. -/
structure DS where
  names : Array NIdx
  levels : Array LIdx
  exprs : Array EIdx
  lists : Array LsIdx

/-- con-leche: ConLeche/Frontend/Olean/Fast.lean:96-102 DS.fresh
Fresh values for `n` slots. -/
def DS.fresh (n : Nat) : DS :=
  ⟨Array.replicate n default, Array.replicate n default, Array.replicate n default,
   Array.replicate n default⟩

/-- con-leche: ConLeche/Frontend/Olean/Fast.lean:104-106 DS.setName -/
@[inline] def DS.setName (st : DS) (s : Nat) (v : NIdx) : DS :=
  let { names, levels, exprs, lists } := st
  { names := names.set! s v, levels, exprs, lists }

/-- con-leche: ConLeche/Frontend/Olean/Fast.lean:108-110 DS.setLevel -/
@[inline] def DS.setLevel (st : DS) (s : Nat) (v : LIdx) : DS :=
  let { names, levels, exprs, lists } := st
  { names, levels := levels.set! s v, exprs, lists }

/-- con-leche: ConLeche/Frontend/Olean/Fast.lean:112-114 DS.setExpr -/
@[inline] def DS.setExpr (st : DS) (s : Nat) (v : EIdx) : DS :=
  let { names, levels, exprs, lists } := st
  { names, levels, exprs := exprs.set! s v, lists }

/-- con-leche: ConLeche/Frontend/Olean/Fast.lean:116-118 DS.setLevels -/
@[inline] def DS.setLevels (st : DS) (s : Nat) (v : LsIdx) : DS :=
  let { names, levels, exprs, lists } := st
  { names, levels, exprs, lists := lists.set! s v }

/-- con-leche: ConLeche/Frontend/Olean/Fast.lean:121 DS.nameV
The memoized values of the object at a location, as the node functions' `sub`. -/
@[inline] def DS.sub (st : DS) : Sub where
  name c := some (st.names.getD (c / 8) default)
  level c := some (st.levels.getD (c / 8) default)
  levels c := some (st.lists.getD (c / 8) default)
  expr c := some (st.exprs.getD (c / 8) default)

/-- con-leche: ConLeche/Frontend/Olean/Fast.lean:232-241 buildKind
One marked slot: each marked kind's node function, its value into the memo.
`AM`'s `none` stops the sweep at once. -/
def buildSlot (pk : OleanPins) (r : Region) (m : ByteArray) (st : DS) (p : Nat) : AM (Option DS) := do
  let g := 8 * p
  let st ←
    if marked m kName p then
      match ← nameNode pk r g st.sub with
      | none => return none
      | some v => pure (st.setName p v)
    else pure st
  let st ←
    if marked m kLevel p then
      match ← levelNode pk r g st.sub with
      | none => return none
      | some v => pure (st.setLevel p v)
    else pure st
  let st ←
    if marked m kLevels p then
      match ← levelsNode pk r g st.sub with
      | none => return none
      | some v => pure (st.setLevels p v)
    else pure st
  if marked m kExpr p then
    match ← exprNode pk r g st.sub with
    | none => return none
    | some v => pure (some (st.setExpr p v))
  else pure (some st)

/-- con-leche: ConLeche/Frontend/Olean/Fast.lean:243-255 buildPass
**The upward sweep** over the slots from `p` to `n`. -/
def buildPass (pk : OleanPins) (r : Region) (m : ByteArray) (n : Nat) (st : DS) (p : Nat) :
    AM (Option DS) := do
  if p < n then
    if marksAt m p != 0 then
      match ← buildSlot pk r m st p with
      | none => pure none
      | some st => buildPass pk r m n st (p + 1)
    else buildPass pk r m n st (p + 1)
  else pure (some st)
termination_by n - p

/-- con-leche: ConLeche/Frontend/Olean/Fast.lean:271-282 runMarked
**Both passes** from the given name and expression roots: how many slots the memo
has, the marks and the memo. -/
def runMarked (pk : OleanPins) (r : Region) (names exprs : List UInt64) :
    AM (Option (Nat × ByteArray × DS)) := do
  let n := maxLoc r exprs (maxLoc r names 0) / 8 + 1
  match names.foldlM (markRoot r kName true) (zeros n) with
  | none => pure none
  | some m =>
    match exprs.foldlM (markRoot r kExpr false) m with
    | none => pure none
    | some m =>
      let m := markPass r m n
      if failedM m then pure none
      else
        match ← buildPass pk r m n (DS.fresh n) 0 with
        | some st => pure (some (n, m, st))
        | none => pure none

/-- con-leche: ConLeche/Frontend/Olean/Fast.lean:284-288 runPasses
**Both passes**: the memo. -/
def runPasses (pk : OleanPins) (r : Region) (names exprs : List UInt64) : AM (Option DS) := do
  match ← runMarked pk r names exprs with
  | some (_, _, st) => pure (some st)
  | none => pure none

/-- con-leche: ConLeche/Frontend/Olean/Fast.lean:290-295 DS.nameOf
A root's value, from the memo. -/
@[inline] def DS.nameOf (pk : OleanPins) (r : Region) (st : DS) (v : UInt64) : Option NIdx :=
  if v == 1 then some pk.anon
  else match r.loc v with
    | some c => some (st.names.getD (c / 8) default)
    | none => none

/-- con-leche: ConLeche/Frontend/Olean/Fast.lean:297-300 DS.exprOf -/
@[inline] def DS.exprOf (r : Region) (st : DS) (v : UInt64) : Option EIdx :=
  match r.loc v with
  | some c => some (st.exprs.getD (c / 8) default)
  | none => none

/-- con-leche: ConLeche/Frontend/Olean/Fast.lean:290-295 DS.nameOf
The memo as a pointer read. -/
@[inline] def DS.read (pk : OleanPins) (r : Region) (st : DS) : PtrRead where
  rdName v := pure (st.nameOf pk r v)
  rdExpr v := pure (st.exprOf r v)

/-- con-leche: ConLeche/Frontend/Olean/Fast.lean:320-325 ModSkel.read
A module's value from its skeletons, given what its pointers stand for. -/
def ModSkel.read (rd : PtrRead) (sk : ModSkel) (cs : List (CEntryF UInt64 UInt64)) :
    AM (Option ModDecoded) :=
  (do
    let imports ← sk.imports.mapM (m := OptionT AM) fun i =>
      i.mapM (m := OptionT AM) fun v => OptionT.mk (rd.rdName v)
    let constants ← cs.mapM (m := OptionT AM) fun c => OptionT.mk (entryMap rd c)
    pure ⟨sk.isModule, imports.toArray, constants.toArray⟩ : OptionT AM ModDecoded).run

/-- con-leche: ConLeche/Frontend/Olean/Fast.lean:327-337 parseMany
`addrs.all (constNamesOk r)`. -/
def allConstNamesOk (pk : OleanPins) (r : Region) : List UInt64 → AM Bool
  | [] => pure true
  | a :: as => do
    if ← constNamesOk pk r a then allConstNamesOk pk r as else pure false

/-- con-leche: ConLeche/Frontend/Olean/Fast.lean:327-337 parseMany
`sk.consts.mapM (constSkel r)`, each skeleton's numbers checked to fit. -/
def constsSkel (r : Region) : List Nat → AM (Option (List (CEntryF UInt64 UInt64)))
  | [] => pure (some [])
  | c :: cs => do
    match constSkel r c with
    | none => pure none
    | some s =>
      skelFits s
      match ← constsSkel r cs with
      | none => pure none
      | some rest => pure (some (s :: rest))

/-- con-leche: ConLeche/Frontend/Olean/Fast.lean:327-337 parseMany
`addrs.mapM (moduleSkel r)`, and each module's constants' skeletons. -/
def manySkels (r : Region) : List UInt64 →
    AM (Option (List (ModSkel × List (CEntryF UInt64 UInt64))))
  | [] => pure (some [])
  | a :: as => do
    match moduleSkel r a with
    | none => pure none
    | some sk =>
      match ← constsSkel r sk.consts with
      | none => pure none
      | some cs =>
        match ← manySkels r as with
        | none => pure none
        | some rest => pure (some ((sk, cs) :: rest))

/-- con-leche: ConLeche/Frontend/Olean/Fast.lean:327-337 parseMany
**The `ModuleData`s at some addresses of a region, each object read once**. -/
def parseMany (pk : OleanPins) (r : Region) (addrs : List UInt64) : AM (Option (List ModDecoded)) := do
  unless ← allConstNamesOk pk r addrs do return none
  match ← manySkels r addrs with
  | none => pure none
  | some ms =>
    let sks := ms.map (·.1)
    let skels := ms.map (·.2)
    let names :=
      sks.flatMap (fun sk => sk.imports.map (·.module)) ++ skels.flatten.flatMap CEntryF.names
    let exprs := skels.flatten.flatMap CEntryF.exprs
    match ← runPasses pk r names exprs with
    | none => pure none
    | some st =>
      (ms.mapM (m := OptionT AM) fun p =>
        OptionT.mk (ModSkel.read (st.read pk r) p.1 p.2)).run

/-- con-leche: ConLeche/Frontend/Olean/Fast.lean:339-343 parseAt
**The `ModuleData` at one address**, fast. -/
def parseAt (pk : OleanPins) (r : Region) (addr : UInt64) : AM (Option ModDecoded) := do
  match ← parseMany pk r [addr] with
  | some [d] => pure (some d)
  | _ => pure none

/-- con-leche: ConLeche/Frontend/Olean/Fast.lean:345-351 stmtsFast
**The statements of some constants, read once**: both passes from the chosen
constants' roots alone. -/
def stmtsFast (pk : OleanPins) (r : Region) (sks : List (CEntryF UInt64 UInt64)) :
    AM (Option (List StmtRec)) := do
  match ← runPasses pk r (sks.flatMap fun s => s.name :: s.levelParams) (sks.map (·.type)) with
  | none => pure none
  | some st =>
    pure <| sks.mapM fun s => do
      pure ⟨← st.nameOf pk r s.name, ← s.levelParams.mapM (st.nameOf pk r), ← st.exprOf r s.type⟩

end ConRon.Arena.Frontend.Olean
