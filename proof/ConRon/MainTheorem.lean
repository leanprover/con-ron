import ConRon.MainTheorem.Driver
import ConRon.MainTheorem.Model
import ConRon.MainTheorem.CompareJson
import ConRon.MainTheorem.Oleans
import ConRon.MainTheorem.Modular
import ConRon.MainTheorem.Conclusions
import ConRon.MainTheorem.CompareOleans
import ConRon.MainTheorem.CompareModular

/-!
# `ConRon.MainTheorem` — the main theorems about the binary (task #171, DESIGN.md §3.9)

The twin of `ConLeche/MainTheorem.lean`: the same theorem names, in the same order, with the
same statements word for word, but con-leche's run premise `ModelIO.CanGive (Driver.runArgs
args) fs 0` is con-ron's `ConRon.CanGive args fs 0` (`MainTheorem/Model.lean`): the extracted
driver `driver::cli::run_args` exits 0 on the argument list `args` at the MODEL instance of the
trait `CheckerIo`, `Model.snapshotIo fs`, from some oracle.  The model is con-ron's `ModelIO`:
its file operations answer from the snapshot `fs` (a failure where `fs` has no answer, and at a
path that is not a well-formed string); every escape that answers a value (the help's and the
scheduler's exit codes, the hardware thread count, the copies' error) takes its answer from the
oracle, so any value of its type is possible; the worker map folds each job over the claims the
oracle picks; the code map runs every job; the notifications do nothing.  That the model
answers as `fs` and keeps the two maps' contracts are theorems about it
(`Model.snapshotIo_answersAs`, `snapshotIo_poolSound`, `snapshotIo_codesSound`), which the walks
use through the instance-generic `CanGiveConforming` (`CanGive.conforming`).

**What is proved, and what is trusted** (con-leche's `ConLeche/Frontend/CheckerIO.lean`, its
module doc, says the same of its binary; OVERVIEW §3.1 is this paragraph's table).  The
theorems say: every run of the model that exits 0 implies the statement.  The binary's `main`
(`crates/con-ron/src/bin/con-ron.rs`) is the argument list's code points (an argument that is
not UTF-8 is exit 3), the checking thread, the same generic `run_args` at the binary's instance
`StdIo` (`crates/con-ron/src/std_io.rs`), the flush and the exit with the code `run_args`
returned; those lines are read, not proved.  The code is computed by the extracted driver and
returned outside every escape.  A run of the binary that exits 0 is one of the model's runs,
with that code, if

1. every file operation the run PERFORMS answered as one snapshot `fs` of the files: the same
   value where the model has one, and a failure where the model fails (`StdIo` fails at a path
   with a code point that is not a character, at a real path that is not valid UTF-8, at a size
   its file's contents do not end at, and at a path whose file was replaced between two
   openings of it; it reads every byte range through the run's one handle of the file, up to
   where a read finds the end).  Those checks catch a path replaced by another file, not a file
   rewritten in place: that the files do not change during the run is assumed, as con-leche
   assumes it, not enforced;
   and on the binary's platform the Rust's spelling of a module's file (`files::mod_file_of`) is
   upstream's (`modFile`), which the logic cannot decide (`System.FilePath`'s `/` reads the
   opaque `System.Platform.isWindows`), so the model also fails where they would differ;
2. the escapes and notifications do not change what the file operations see (none writes a file
   a check reads: they print, read the clock, count threads, keep what the run built, and start
   the scheduler, whose workers only read) and do not end the process with exit code 0;
3. the two maps' actual runs are some oracle's: the worker map (`pool::parallel_all`) runs each
   worker from the job's first state over the positions it claims, in increasing order, every
   position claimed, and answers `Ok` only when every step did, which is an argument about its
   control flow; the code map runs every module's step and answers their codes in order; and
4. Rust, its standard library and Aeneas run and model the code as written.

The argument is then con-leche's: the extracted code is the same at both instances; at every file
operation the run performs, the binary's answer is, by (1) and (2), the model's; at every escape
the binary's answer is SOME value of its type, and the model has an oracle that gives it (the
oracle is chosen after the run, answer by answer); at each map, by (3), an oracle's claims give
the binary's answer.  So, by induction along the run, a run of the binary that reaches the exit
with 0 is one of the model's runs, and what is proved of all of those holds of it.  Calls the run
does not perform constrain nothing.

What differs from con-leche: an ORACLE in the instance's state where con-leche has a
non-determinism monad (Aeneas models a trait method as a function, so "any outcome" is "the
oracle's", the oracle existentially chosen); and POSITIONAL reads (`read_range`) where con-leche
opens a handle and reads it forward (the model's `ModelIO.read` slices the file from the
handle's position; con-ron's slice is at the offset the reader passes, the reader's own
position).  One `&self` escape answers a value, `worker_copies`, inside the code map where the
instance is shared: in the model its answer is the oracle's function of its arguments, so it
claims that two calls with the same arguments at one state agree, which the binary's
(deterministic in its arguments) does; and it can only turn an accept into a failure.

**Several processes.**  `main_modular`, `main_modular_compare` and
`main_modular_compare_no_False` are about several runs of the binary: they assume (1) to (4) of
every run, with one snapshot for all of them, as con-leche's do.

**The proofs.**  Each theorem is a walk of the extracted driver and a conclusion.  The walk
(`MainTheorem/Driver.lean`, `CompareJson.lean`, `Oleans.lean`, `Modular.lean`,
`CompareOleans.lean`, `CompareModular.lean`, over the argument parses of `Args.lean`,
`ModArgs.lean` and `CmpArgs.lean`) inverts `run_args` at the theorem's argument list, one
lemma per driver function, down to the calls of the verified stages, and hands them to the
staged lemmas of `MainTheorem/Stages.lean`: one premise per call, Theorem 2 (the Rust refines the
twin), then Theorem 1 (the twin refines con-leche's pure checker).  `MainTheorem/Conclusions.lean`
turns the staged conclusions into con-leche's words with con-leche's own soundness theorems:

| theorem | the walk | the conclusion |
|---|---|---|
| `main_json_model`, `main_no_False` | `json_stages_of_canGive` | `json_model_of_stages`, `json_no_False_of_stages` |
| `main_compare_json_model` | `compare_json_stages_of_canGive` | `compare_json_model_of_stages` |
| `main_oleans` | `oleans_of_canGive` | `oleans_model_of_stages_dec` |
| `main_compare_model` | `compare_of_canGive` | `compare_model_of_stages_dec` |
| `main_modular`, `main_modular_one` | `modular_of_canGive`, `modular_one_of_canGive` | `Stages.model_modular_of` |
| `main_modular_compare`, `main_modular_compare_one`, `main_modular_compare_no_False` | `modular_cmp_facts_of_canGive`, `modular_cmp_one_of_canGive` | `cmp_family`, `cmp_no_False` |

The proofs use the axioms `propext`, `Classical.choice`, `Quot.sound` and
`PINS_TEXT._native.decide.ax_1`, the one Aeneas spends on the embedded pin text's definition,
and no other (the census at the end of this file).
-/

open ConLeche (IsModel constantsOf jsonWithTheoremFalse FS)
open ConLeche.Frontend (parseChunks)

namespace ConRon.MainTheorem

universe w

/-- con-leche: ConLeche/MainTheorem.lean:45-49 main_json_model —
**An accepted file's records have a model**: an exit 0 of `-- <file>` read the file as
records that have a model in every set theory. -/
theorem main_json_model (V : Type w) [ConLeche.SetTheory V] {file : String} {fs : FS}
    {b : ByteArray}
    (h : ConRon.CanGive ["--", file] fs 0) (hb : fs.file file = some b) :
    ∃ r, parseChunks [b] = .ok r ∧ ∃ model, IsModel V model (· ∈ constantsOf r.decls.toList) :=
  have ⟨h1, h2, hreads, h3, h4, hpins, h5, h6, h7, h8, hcat⟩ :=
    ConRon.json_stages_of_canGive h.conforming hb
  json_model_of_stages V h1 h2 hreads hcat h3 h4 hpins h5 h6 h7 h8

/-- con-leche: ConLeche/MainTheorem.lean:51-57 main_no_False —
**No accepted file declares a theorem of type `False`**: no exit 0 of `-- <file>` reads a
`jsonWithTheoremFalse` file. -/
theorem main_no_False (V : Type w) [ConLeche.SetTheory V] {file : String} {fs : FS}
    {b : ByteArray}
    (h : ConRon.CanGive ["--", file] fs 0) (hb : fs.file file = some b)
    (hF : jsonWithTheoremFalse [b]) : False :=
  have ⟨h1, h2, hreads, h3, h4, hpins, h5, h6, h7, h8, hcat⟩ :=
    ConRon.json_stages_of_canGive h.conforming hb
  json_no_False_of_stages V hcat hF h1 h2 hreads h3 h4 hpins h5 h6 h7 h8

/-- con-leche: ConLeche/MainTheorem.lean:60-67 main_compare_json_model —
**An accepted comparison's challenge file has a model**: an exit 0 of `--compare -- <c> <s>`
read the file `c` as records that have a model in every set theory. -/
theorem main_compare_json_model (V : Type w) [ConLeche.SetTheory V] {c s : String} {fs : FS}
    (h : ConRon.CanGive ["--compare", "--", c, s] fs 0) :
    ∃ bC rC, fs.file c = some bC ∧ parseChunks [bC] = .ok rC ∧
      ∃ model, IsModel V model (· ∈ constantsOf rC.decls.toList) :=
  have ⟨bC, hbC, ⟨h1, h2, hreadsC, hreadsS, hcat, h3, h3S, hdup, h4S, hpins, h5, h6S, h7S, h8S,
    h4, hside, hsol, h6, h7, h8⟩⟩ := ConRon.compare_json_stages_of_canGive h.conforming
  have ⟨rC, hp, hm⟩ := compare_json_model_of_stages V h1 h2 hreadsC hreadsS hcat h3 h3S hdup h4S
    hpins h5 h6S h7S h8S h4 hside hsol h6 h7 h8
  ⟨bC, rC, hbC, hp, hm⟩

open ConLeche ConLeche.Frontend in
/-- con-leche: ConLeche/MainTheorem.lean:77-81 main_oleans —
**An accepted module's closure has a model**: every exit 0 of `--olean --search-path=<dirs>
-- <root>` has a model of the constants of the modules `root` imports, itself included. -/
theorem main_oleans (V : Type w) [SetTheory V] {dirs root : String} {r : Name} {fs : FS}
    (hr : Olean.parseModName root = some r)
    (h : ConRon.CanGive ["--olean", "--search-path=" ++ dirs, "--", root] fs 0) :
    ∃ model, IsModel V model (Olean.closureConstants (Driver.searchPathOf dirs) fs #[r]) :=
  oleans_of_canGive V hr h.conforming

open ConLeche ConLeche.Frontend in
/-- con-leche: ConLeche/MainTheorem.lean:88-95 main_compare_model —
**An accepted comparison's challenge closure has a model**: every exit 0 of `--olean
--compare --trusted-search-path=<T> --search-path=<D> -- <c> <s>` has a model of the constants
of the challenge's closure, read through the challenge's directories, on every snapshot that
agrees with the run's there. -/
theorem main_compare_model (V : Type w) [SetTheory V] {T D c s : String} {C S : Name} {fs : FS}
    (hc : Olean.parseModName c = some C) (hs : Olean.parseModName s = some S)
    (h : ConRon.CanGive ["--olean", "--compare", "--trusted-search-path=" ++ T,
      "--search-path=" ++ D, "--", c, s] fs 0) :
    ∀ fs', FS.AgreeUnder (Driver.trustedOr (Driver.searchPathOf T) (Driver.searchPathOf D)) fs fs' →
      ∃ model, IsModel V model (Olean.closureConstants
        (Driver.trustedOr (Driver.searchPathOf T) (Driver.searchPathOf D)) fs' #[C]) :=
  compare_of_canGive V hc hs h.conforming

open ConLeche ConLeche.Frontend in
/-- con-leche: ConLeche/MainTheorem.lean:109-122 main_modular —
**An accepted modular check has a family of models**: on a snapshot where `--check-graph
--search-path=<dirs> -- <root>` exits 0 and every module of the headers' closure of `root` has
an exit 0 of `--olean --module`, every module of the closure has a model of its constants, and
the models agree on what the modules see of each other. -/
theorem main_modular (V : Type w) [SetTheory V] {dirs root : String} {r : Name} {fs : FS}
    (hr : Olean.parseModName root = some r)
    (h : ConRon.CanGive ["--check-graph", "--search-path=" ++ dirs, "--", root] fs 0)
    (hwork : ∀ m', Olean.HdrClosure (Driver.searchPathOf dirs) fs [r] m' → ∃ root',
      Olean.parseModName root' = some m' ∧
        ConRon.CanGive ["--olean", "--module", "--search-path=" ++ dirs, "--", root'] fs 0) :
    ∃ model : Name → (Name → List Nat → V),
      (∀ m, Olean.InClosure (Driver.searchPathOf dirs) fs #[r] m →
        IsModel V (model m) (Olean.moduleConstants (Driver.searchPathOf dirs) fs m)) ∧
      (∀ m n m', Olean.InClosure (Driver.searchPathOf dirs) fs #[r] m →
        Olean.Sees (Driver.searchPathOf dirs) fs m n m' → model m n = model m' n) :=
  modular_of_canGive V hr h.conforming
    fun m hm => (hwork m hm).imp fun _ h => ⟨h.1, h.2.conforming⟩

open ConLeche ConLeche.Frontend in
/-- con-leche: ConLeche/MainTheorem.lean:126-135 main_modular_one —
**The same, in one process**: every exit 0 of `--olean --modular --search-path=<dirs>
-- <root>` has the family of models of `main_modular`. -/
theorem main_modular_one (V : Type w) [SetTheory V] {dirs root : String} {r : Name} {fs : FS}
    (hr : Olean.parseModName root = some r)
    (h : ConRon.CanGive ["--olean", "--modular", "--search-path=" ++ dirs, "--", root] fs 0) :
    ∃ model : Name → (Name → List Nat → V),
      (∀ m, Olean.InClosure (Driver.searchPathOf dirs) fs #[r] m →
        IsModel V (model m) (Olean.moduleConstants (Driver.searchPathOf dirs) fs m)) ∧
      (∀ m n m', Olean.InClosure (Driver.searchPathOf dirs) fs #[r] m →
        Olean.Sees (Driver.searchPathOf dirs) fs m n m' → model m n = model m' n) :=
  modular_one_of_canGive V hr h.conforming

open ConLeche ConLeche.Frontend in
/-- con-leche: ConLeche/MainTheorem.lean:143-161 main_modular_compare —
**An accepted modular comparison's challenge closure has a family of models**: on a
snapshot where every command `--schedule-commands --compare` prints for the challenge `C` and
its solution `S` exits 0 (the graph check, a worker at every module of the headers' closure of
`C` and `S` but `C`, the compare worker at `C`), on every snapshot that agrees with it under the
challenge's directories, the family of `main_modular` for the closure of `C`. -/
theorem main_modular_compare (V : Type w) [SetTheory V] {T D c s : String} {C S : Name}
    {fs : FS} (hc : Olean.parseModName c = some C) (hs : Olean.parseModName s = some S)
    (hgraph : ConRon.CanGive ["--check-graph", "--compare",
      "--trusted-search-path=" ++ T, "--search-path=" ++ D, "--", c, s] fs 0)
    (hwork : ∀ m, Olean.HdrClosure
        (⟨C, S, Driver.searchPathOf T, Driver.searchPathOf D, none⟩ : Driver.CmpReq).solRoots fs
        [C, S] m → m ≠ C →
      ∃ root', Olean.parseModName root' = some m ∧ ConRon.CanGive
        ["--olean", "--module", "--trusted-search-path=" ++ T, "--search-path=" ++ D, "--",
          root'] fs 0)
    (hcmp : ConRon.CanGive ["--olean", "--module", "--compare",
      "--trusted-search-path=" ++ T, "--search-path=" ++ D, "--", c, s] fs 0) :
    let sp := Driver.trustedOr (Driver.searchPathOf T) (Driver.searchPathOf D)
    ∀ fs', FS.AgreeUnder sp fs fs' →
      ∃ model : Name → (Name → List Nat → V),
        (∀ m, Olean.InClosure sp fs' #[C] m → IsModel V (model m) (Olean.moduleConstants sp fs' m)) ∧
        (∀ m n m', Olean.InClosure sp fs' #[C] m → Olean.Sees sp fs' m n m' →
          model m n = model m' n) :=
  have ⟨_, _, good, hC, edges, inj, hhdr, acc⟩ :=
    modular_cmp_facts_of_canGive hc hs hgraph.conforming
      (fun m hm hne => (hwork m hm hne).imp fun _ h => ⟨h.1, h.2.conforming⟩) hcmp.conforming
  cmp_family V good hC edges inj hhdr acc

open ConLeche ConLeche.Frontend in
/-- con-leche: ConLeche/MainTheorem.lean:166-176 main_modular_compare_one —
**The same, in one process**: every exit 0 of `--olean --modular --compare` has the family
of `main_modular_compare`. -/
theorem main_modular_compare_one (V : Type w) [SetTheory V] {T D c s : String} {C S : Name}
    {fs : FS} (hc : Olean.parseModName c = some C) (hs : Olean.parseModName s = some S)
    (h : ConRon.CanGive ["--olean", "--modular", "--compare",
      "--trusted-search-path=" ++ T, "--search-path=" ++ D, "--", c, s] fs 0) :
    let sp := Driver.trustedOr (Driver.searchPathOf T) (Driver.searchPathOf D)
    ∀ fs', FS.AgreeUnder sp fs fs' →
      ∃ model : Name → (Name → List Nat → V),
        (∀ m, Olean.InClosure sp fs' #[C] m → IsModel V (model m) (Olean.moduleConstants sp fs' m)) ∧
        (∀ m n m', Olean.InClosure sp fs' #[C] m → Olean.Sees sp fs' m n m' →
          model m n = model m' n) :=
  modular_cmp_one_of_canGive V hc hs h.conforming

open ConLeche ConLeche.Frontend in
/-- con-leche: ConLeche/MainTheorem.lean:183-199 main_modular_compare_no_False —
**No accepted modular comparison's challenge module holds a constant of type `False`**: no
snapshot where every command of `main_modular_compare` exits 0 has a constant of type `False` in
the challenge module `C`, read through the challenge's directories.  This covers what `C` sees
through its solution too, which the family of `main_modular_compare` does not. -/
theorem main_modular_compare_no_False (V : Type w) [SetTheory V] {T D c s : String}
    {C S : Name} {fs : FS} {ci : ConstantInfo}
    (hc : Olean.parseModName c = some C) (hs : Olean.parseModName s = some S)
    (hgraph : ConRon.CanGive ["--check-graph", "--compare",
      "--trusted-search-path=" ++ T, "--search-path=" ++ D, "--", c, s] fs 0)
    (hwork : ∀ m, Olean.HdrClosure
        (⟨C, S, Driver.searchPathOf T, Driver.searchPathOf D, none⟩ : Driver.CmpReq).solRoots fs
        [C, S] m → m ≠ C →
      ∃ root', Olean.parseModName root' = some m ∧ ConRon.CanGive
        ["--olean", "--module", "--trusted-search-path=" ++ T, "--search-path=" ++ D, "--",
          root'] fs 0)
    (hcmp : ConRon.CanGive ["--olean", "--module", "--compare",
      "--trusted-search-path=" ++ T, "--search-path=" ++ D, "--", c, s] fs 0)
    (hci : Olean.InModulePart (Driver.trustedOr (Driver.searchPathOf T) (Driver.searchPathOf D))
      fs C .private ci)
    (hty : ci.type = .const falseName []) : False :=
  have ⟨_, _, good, hC, edges, inj, hhdr, acc⟩ :=
    modular_cmp_facts_of_canGive hc hs hgraph.conforming
      (fun m hm hne => (hwork m hm hne).imp fun _ h => ⟨h.1, h.2.conforming⟩) hcmp.conforming
  cmp_no_False good hC edges inj hhdr acc V (.root (by simp)) hci hty

end ConRon.MainTheorem

/-! ## The census: con-leche's three axioms, and the one Aeneas spends on the embedded pin text -/

/-- info: 'ConRon.MainTheorem.main_json_model' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 ConRon.Generated.kernel.pins_text.PINS_TEXT._native.decide.ax_1] -/
#guard_msgs in #print axioms ConRon.MainTheorem.main_json_model

/-- info: 'ConRon.MainTheorem.main_no_False' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 ConRon.Generated.kernel.pins_text.PINS_TEXT._native.decide.ax_1] -/
#guard_msgs in #print axioms ConRon.MainTheorem.main_no_False

/-- info: 'ConRon.MainTheorem.main_compare_json_model' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 ConRon.Generated.kernel.pins_text.PINS_TEXT._native.decide.ax_1] -/
#guard_msgs in #print axioms ConRon.MainTheorem.main_compare_json_model

/-- info: 'ConRon.MainTheorem.main_oleans' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 ConRon.Generated.kernel.pins_text.PINS_TEXT._native.decide.ax_1] -/
#guard_msgs in #print axioms ConRon.MainTheorem.main_oleans

/-- info: 'ConRon.MainTheorem.main_compare_model' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 ConRon.Generated.kernel.pins_text.PINS_TEXT._native.decide.ax_1] -/
#guard_msgs in #print axioms ConRon.MainTheorem.main_compare_model

/-- info: 'ConRon.MainTheorem.main_modular' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 ConRon.Generated.kernel.pins_text.PINS_TEXT._native.decide.ax_1] -/
#guard_msgs in #print axioms ConRon.MainTheorem.main_modular

/-- info: 'ConRon.MainTheorem.main_modular_one' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 ConRon.Generated.kernel.pins_text.PINS_TEXT._native.decide.ax_1] -/
#guard_msgs in #print axioms ConRon.MainTheorem.main_modular_one

/-- info: 'ConRon.MainTheorem.main_modular_compare' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 ConRon.Generated.kernel.pins_text.PINS_TEXT._native.decide.ax_1] -/
#guard_msgs in #print axioms ConRon.MainTheorem.main_modular_compare

/-- info: 'ConRon.MainTheorem.main_modular_compare_one' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 ConRon.Generated.kernel.pins_text.PINS_TEXT._native.decide.ax_1] -/
#guard_msgs in #print axioms ConRon.MainTheorem.main_modular_compare_one

/-- info: 'ConRon.MainTheorem.main_modular_compare_no_False' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 ConRon.Generated.kernel.pins_text.PINS_TEXT._native.decide.ax_1] -/
#guard_msgs in #print axioms ConRon.MainTheorem.main_modular_compare_no_False
