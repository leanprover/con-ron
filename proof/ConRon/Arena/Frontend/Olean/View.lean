/-
# `ConRon.Arena.Frontend.Olean.View` — a module's views (task #142)

The twin of `olean/view.rs`.  `OLeanLevel`, `ModFiles`, `ModFiles.isModule`,
`ModFiles.viewRegion`, `ModFiles.upTo` are upstream's own: files and bytes.
`decodeModuleSpec` is `noncomputable` upstream and Theorem 1 cites it.
-/
module

public import ConLeche.Frontend.Olean.View
public import ConRon.Arena.Frontend.Olean.Header
public import ConRon.Arena.Frontend.Olean.Reads

@[expose] public section

namespace ConRon.Arena.Frontend.Olean

open ConLeche
open ConLeche.Frontend.Olean (Region CEntryF OLeanLevel ModFiles Part)

/-- con-leche: ConLeche/Frontend/Olean/View.lean:87-92 parseView
`unless importsPre f.exported.bytes == some d.imports do none`, with `d`. -/
def checkImportsPre (pk : OleanPins) (f : ModFiles) (d : ModDecoded) : AM (Option ModDecoded) := do
  match ← importsPre pk f.exported.bytes with
  | some pre => if pre == d.imports then pure (some d) else pure none
  | none => pure none

/-- con-leche: ConLeche/Frontend/Olean/View.lean:87-92 parseView
**One view**, fast: what it reaches, each object once. -/
def parseView (pk : OleanPins) (f : ModFiles) (level : OLeanLevel) : AM (Option ModDecoded) := do
  match f.viewRegion level with
  | none => pure none
  | some (r, a) =>
    match ← parseAt pk r a with
    | none => pure none
    | some d => checkImportsPre pk f d

/-- con-leche: ConLeche/Frontend/Olean/View.lean:94-98 AllViews
All three views of a module. -/
structure AllViews where
  exported : ModDecoded
  server : ModDecoded
  «private» : ModDecoded

/-- con-leche: ConLeche/Frontend/Olean/View.lean:100-123 parseAllViews
The module-system arm: one memo over all three files. -/
def parseAllViewsModule (pk : OleanPins) (f : ModFiles) (s p : Part) : AM (Option AllViews) := do
  let ae := f.exported.moduleDataAddr
  let as' := s.moduleDataAddr
  let ap := p.moduleDataAddr
  unless ((Region.single f.exported).loc ae).isSome do return none
  match Region.ofParts #[f.exported, s] with
  | .error _ => return none
  | .ok r2 =>
    unless (r2.loc as').isSome do return none
    match Region.ofParts #[f.exported, s, p] with
    | .error _ => return none
    | .ok r =>
      match ← parseMany pk r [ae, as', ap] with
      | some [de, ds, dp] =>
        match ← importsPre pk f.exported.bytes with
        | some pre =>
          if pre == de.imports && pre == ds.imports && pre == dp.imports then
            pure (some ⟨de, ds, dp⟩)
          else pure none
        | none => pure none
      | _ => pure none

/-- con-leche: ConLeche/Frontend/Olean/View.lean:100-123 parseAllViews
**All three views, each object once**, whatever views reach it. -/
def parseAllViews (pk : OleanPins) (f : ModFiles) : AM (Option AllViews) := do
  if f.isModule then
    match f.server, f.private with
    | some s, some p => parseAllViewsModule pk f s p
    | _, _ => pure none
  else
    match ← parseView pk f .exported with
    | none => pure none
    | some d => pure (some ⟨d, d, d⟩)

/-- con-leche: ConLeche/Frontend/Olean/View.lean:125-129 AllViews.at
A view at a level. -/
def AllViews.at (v : AllViews) : OLeanLevel → ModDecoded
  | .exported => v.exported
  | .server => v.server
  | .private => v.private

/-- con-leche: ConLeche/Frontend/Olean/View.lean:146-150 readNamePositions
**Per constant of a view, its position, name, kind and filter.** -/
def readNamePositions (pk : OleanPins) (f : ModFiles) (level : OLeanLevel) :
    AM (Option NamePositions) := do
  match f.viewRegion level with
  | none => pure none
  | some (r, a) => namePositionsAt pk r a

/-- con-leche: ConLeche/Frontend/Olean/View.lean:152-155 readEntry
**The constant at a position of a view**, read with a memo of its own. -/
def readEntry (pk : OleanPins) (f : ModFiles) (level : OLeanLevel) (c : Nat) :
    AM (Option (CEntryF NIdx EIdx)) := do
  match f.viewRegion level with
  | none => pure none
  | some (r, _) => entryAt pk r c

/-- con-leche: ConLeche/Frontend/Olean/View.lean:157-160 readStmts
**The statements of the constants at some positions of a view**, read together. -/
def readStmts (pk : OleanPins) (f : ModFiles) (level : OLeanLevel) (cs : List Nat) :
    AM (Option (List StmtRec)) := do
  match f.viewRegion level with
  | none => pure none
  | some (r, _) => stmtsAt pk r cs

/-- con-leche: ConLeche/Frontend/Olean/View.lean:164-167 undecodable
The module's files do not decode. -/
def undecodable (m : Name) : CheckError :=
  .internal s!"module {m}: malformed .olean data (an object of the wrong shape, or a \
    pointer that does not point below its object)"

/-- con-leche: ConLeche/Frontend/Olean/View.lean:169-181 viewError
Why a view does not read. -/
def viewError (pk : OleanPins) (m : Name) (f : ModFiles) (level : OLeanLevel) : AM CheckError := do
  match f.viewRegion level with
  | none => pure (.internal s!"module {m}: the .olean files of a module overlap")
  | some (r, a) =>
    if ← constNamesOk pk r a then
      match ← parseAt pk r a with
      | some _ =>
        pure (.internal s!"module {m}: the {repr level} part's imports are not those at the \
          start of its .olean")
      | none => pure (undecodable m)
    else
      pure (.internal s!"module {m}: the {repr level} part's name table (constNames) does not list \
        its constants' names, each once")

end ConRon.Arena.Frontend.Olean
