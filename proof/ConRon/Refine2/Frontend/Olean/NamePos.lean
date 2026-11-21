/-
# `ConRon.Refine2.Frontend.Olean.NamePos` — `reads::NamePosition`/`NamePositions`, as the twin's

**Task #166, Theorem 2.**  The abstraction of a module's name positions (`reads.rs`'s
`ModHeader`, `NamePosition`, `NamePositions`) to the twin's (`Arena/Frontend/Olean/Reads.lean`),
and the projections of the abstraction.
-/
import ConRon.Refine2.Frontend.Olean.View
import ConRon.Arena.Frontend.Olean.Reads

open Aeneas Aeneas.Std Result
open ConRon.Generated

namespace ConRon.Refine2.Frontend.Olean

open ConRon.Arena

/-- `reads::NamePosition`, as the twin's. -/
def absNamePosition (p : frontend.olean.reads.NamePosition) : Arena.Frontend.Olean.NamePosition :=
  ⟨p.loc.val, absNIdx p.name, p.tag.val, p.skipped⟩

/-- `reads::ModHeader`, as the twin's. -/
def absModHeader (h : frontend.olean.reads.ModHeader) : Arena.Frontend.Olean.ModHeader :=
  ⟨h.is_module, absImports h.imports⟩

/-- `reads::NamePositions`, as the twin's. -/
def absNamePositions (p : frontend.olean.reads.NamePositions) : Arena.Frontend.Olean.NamePositions :=
  ⟨absModHeader p.header, (p.consts.val.map absNamePosition).toArray⟩

@[simp] theorem absNamePosition_loc (p : frontend.olean.reads.NamePosition) :
    (absNamePosition p).loc = p.loc.val := rfl
@[simp] theorem absNamePosition_name (p : frontend.olean.reads.NamePosition) :
    (absNamePosition p).name = absNIdx p.name := rfl
@[simp] theorem absNamePosition_tag (p : frontend.olean.reads.NamePosition) :
    (absNamePosition p).tag = p.tag.val := rfl
@[simp] theorem absNamePosition_skipped (p : frontend.olean.reads.NamePosition) :
    (absNamePosition p).skipped = p.skipped := rfl
@[simp] theorem absModHeader_isModule (h : frontend.olean.reads.ModHeader) :
    (absModHeader h).isModule = h.is_module := rfl
@[simp] theorem absModHeader_imports (h : frontend.olean.reads.ModHeader) :
    (absModHeader h).imports = absImports h.imports := rfl
@[simp] theorem absNamePositions_header (p : frontend.olean.reads.NamePositions) :
    (absNamePositions p).header = absModHeader p.header := rfl
@[simp] theorem absNamePositions_consts (p : frontend.olean.reads.NamePositions) :
    (absNamePositions p).consts = (p.consts.val.map absNamePosition).toArray := rfl

/-- The `i`-th position, abstracted. -/
theorem absNamePositions_consts_getElem? (p : frontend.olean.reads.NamePositions) (i : Nat) :
    (absNamePositions p).consts[i]? = (p.consts.val[i]?).map absNamePosition := by
  simp

@[simp] theorem absNamePositions_consts_size (p : frontend.olean.reads.NamePositions) :
    (absNamePositions p).consts.size = p.consts.val.length := by
  simp

end ConRon.Refine2.Frontend.Olean
