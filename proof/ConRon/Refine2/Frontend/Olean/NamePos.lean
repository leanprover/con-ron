/-
# `ConRon.Refine2.Frontend.Olean.NamePos` — `reads::NamePosition`/`NamePositions`, as the twin's

**Task #166, Theorem 2.**  The abstraction of a module's name positions (`reads.rs`'s
`ModHeader`, `NamePosition`, `NamePositions`) to the twin's (`Arena/Frontend/Olean/Reads.lean`),
and the projections of the abstraction; `spec::StmtRec` as the twin's `StmtRec`, and a kind with
its expressions left out (`CKindF<NIdx, ()>`) against the twin's (`KindNamesRel`).
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

/-! ## A statement, a kind's names -/

/-- `spec::StmtRec`, as the twin's. -/
def absStmtRec (c : frontend.olean.spec.StmtRec) : Arena.Frontend.Olean.StmtRec :=
  ⟨absNIdx c.name, c.level_params.val.map absNIdx, absEIdx c.ty⟩

@[simp] theorem absStmtRec_name (c : frontend.olean.spec.StmtRec) :
    (absStmtRec c).name = absNIdx c.name := rfl
@[simp] theorem absStmtRec_levelParams (c : frontend.olean.spec.StmtRec) :
    (absStmtRec c).levelParams = c.level_params.val.map absNIdx := rfl
@[simp] theorem absStmtRec_type (c : frontend.olean.spec.StmtRec) :
    (absStmtRec c).type = absEIdx c.ty := rfl

/-- **A kind with its expressions left out**, against the twin's. -/
abbrev KindNamesRel : frontend.olean.spec.CKindF arena.handle.NIdx Unit →
    ConLeche.Frontend.Olean.CKindF NIdx Unit → Prop :=
  KindRel absNIdx (fun _ => ()) ValRel

end ConRon.Refine2.Frontend.Olean
