/-
# `ConRon.Refine2.Frontend.Olean.FsRel` — the file seam of the reader

**Task #142, Theorem 2.**  The reader's one hypothesis about the file system, the model
being `Source.lean`'s `ReadsAs` at the stream parser.  The trait `OleanFs`'s instance
extracts as five plain functions, the twin's `OleanFs` is five pure functions, and all
Theorem 2 needs of the two is that they answer alike, at the paths the reader asks.

**A path is not compared.**  The Rust and the twin compute the path of a module's file
each its own way (`files::mod_file`; upstream's `modFile`, over `System.FilePath`, whose
separator is the opaque `System.Platform.isWindows`'s).  So `PathRel p q` pairs the two
spellings of one request: `p` is what `mod_file` answers for a directory, a module and an
extension, and `q` what `modFile` answers for the same three.  Those are the only paths
the reader's five operations are asked at.

Only the instance's `Ok` answers are related: a failing read gives the Rust no accept, so
that a transient I/O error falsifies nothing.  What a real path answers is compared as a string (it decides a location), so it must be a sequence of
code points (`StrWF`); `read_bin_file` and `read_range` answer bytes.
-/
import ConRon.Generated
import ConRon.Refine.Abs
import ConRon.Refine2.Frontend.Abs
import ConRon.Arena.Frontend.Olean.Files

open Aeneas Aeneas.Std Result
open ConRon.Generated

namespace ConRon.Refine2.Frontend.Olean

/-- **The two spellings of one module file**: `p` is what the Rust's `mod_file` computes
and `q` what upstream's `modFile` computes, for the same directory, name and extension. -/
def PathRel (p : alloc.vec.Vec Std.U32) (q : System.FilePath) : Prop :=
  ∃ (pers : arena.store.PersTier) (ar : arena.store.EStore) (dir : alloc.vec.Vec Std.U32)
    (m : arena.handle.NIdx) (ext : alloc.vec.Vec Std.U32) (n : kernel.name.Name),
    frontend.olean.files.mod_file pers ar dir m ext = ok (.Ok p) ∧
    arena.env.read_name pers ar m = ok (.Ok n) ∧
    q = ConLeche.Frontend.Olean.modFile ⟨ConRon.Refine.absString dir⟩ (ConRon.Refine.absName n)
      (ConRon.Refine.absString ext)

/-- **`OleanFs`'s instance at `fsv` and the twin's record answer alike** where the instance
answers: at every pair of spellings, the same `Bool`, real path, bytes and size.  A failing
read of the instance claims nothing of the record: it gives the Rust no accept, and an accept
is what the theorems above the file tier relate. -/
structure FsRel {F : Type} (inst : frontend.olean.files.OleanFs F) (fsv : F)
    (fs : Arena.Frontend.Olean.OleanFs) : Prop where
  pathExists : ∀ {p q}, PathRel p q → ∀ b, inst.path_exists fsv p = ok (.Ok b) →
    fs.pathExists q = .ok b
  realPath : ∀ {p q}, PathRel p q → ∀ r, inst.real_path fsv p = ok (.Ok r) →
    fs.realPath q = .ok ⟨ConRon.Refine.absString r⟩ ∧ ConRon.Refine.StrWF r
  readBinFile : ∀ {p q}, PathRel p q → ∀ b, inst.read_bin_file fsv p = ok (.Ok b) →
    fs.readBinFile q = .ok (absBytes (alloc.vec.Vec.deref b))
  readRange : ∀ {p q}, PathRel p q → ∀ off len b, inst.read_range fsv p off len = ok (.Ok b) →
    fs.readRange q off.val len.val = .ok (absBytes (alloc.vec.Vec.deref b))
  fileSize : ∀ {p q}, PathRel p q → ∀ s, inst.file_size fsv p = ok (.Ok s) →
    fs.fileSize q = .ok s.val

/-- The search path of the command line, as the twin's. -/
def absSearchPath (dirs : alloc.vec.Vec (alloc.vec.Vec Std.U32)) : List System.FilePath :=
  dirs.val.map fun d => ⟨ConRon.Refine.absString d⟩

end ConRon.Refine2.Frontend.Olean
