/-
# `ConRon.Refine2.Frontend.Olean.FsRel` — the file seam of the reader

**Task #142, Theorem 2.**  The reader's one hypothesis about the file system, the model
being `Source.lean`'s `ReadsAs` at the stream parser.  The trait `CheckerFs`'s instance
extracts as five plain functions, the twin's `OleanFs` is five pure functions, and all
Theorem 2 needs of the two is that they answer alike, at the paths the reader asks.

**A path is not compared.**  The Rust and the twin compute the path of a module's file
or directory each its own way (`files::mod_file_of`, `files::mod_dir_of`; upstream's
`modFile`, `modDir`, over `System.FilePath`, whose separator is the opaque
`System.Platform.isWindows`'s).  So `PathRel p q` pairs the two spellings of one request: `p`
is what `mod_file_of` (or `mod_dir_of`) answers for a directory, a name and an extension, and
`q` what `modFile` (or `modDir`) answers for the same; or `p` is a directory of the search
path itself, spelled as given, and `q` its string.  Those are the only paths the reader's six
operations are asked at.

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

/-- **The two spellings of one request**: `p` is what the Rust's `mod_file_of` computes and
`q` what upstream's `modFile` computes, for the same directory, name and extension; or the
same of `mod_dir_of` and `modDir`; or `p` names a directory as given and `q` is its string. -/
def PathRel (p : alloc.vec.Vec Std.U32) (q : System.FilePath) : Prop :=
  (∃ (dir : alloc.vec.Vec Std.U32) (n : kernel.name.Name) (ext : alloc.vec.Vec Std.U32),
    frontend.olean.files.mod_file_of dir n ext = ok p ∧
    q = ConLeche.Frontend.Olean.modFile ⟨ConRon.Refine.absString dir⟩ (ConRon.Refine.absName n)
      (ConRon.Refine.absString ext)) ∨
  (∃ (dir : alloc.vec.Vec Std.U32) (n : kernel.name.Name),
    frontend.olean.files.mod_dir_of dir n = ok p ∧
    q = ConLeche.Frontend.Olean.modDir ⟨ConRon.Refine.absString dir⟩ (ConRon.Refine.absName n)) ∨
  q = ⟨ConRon.Refine.absString p⟩

/-- **`CheckerFs`'s instance at `fsv` and the twin's record answer alike** where the instance
answers: at every pair of spellings, the same `Bool`s, real path, bytes and size.  A failing
read of the instance claims nothing of the record: it gives the Rust no accept, and an accept
is what the theorems above the file tier relate. -/
structure FsRel {F : Type} (inst : frontend.checker_io.CheckerFs F) (fsv : F)
    (fs : Arena.Frontend.Olean.OleanFs) : Prop where
  pathExists : ∀ {p q}, PathRel p q → ∀ b, inst.path_exists fsv p = ok (.Ok b) →
    fs.pathExists q = .ok b
  isDir : ∀ {p q}, PathRel p q → ∀ b, inst.is_dir fsv p = ok (.Ok b) →
    fs.isDir q = .ok b
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

/-- A lookup, as the twin's: its search path and its fallback, no root resolved. -/
def absRoots (sp : frontend.olean.files.Roots) : ConLeche.Frontend.Olean.Roots :=
  { path := absSearchPath sp.path, fallback := absSearchPath sp.fallback }

end ConRon.Refine2.Frontend.Olean
