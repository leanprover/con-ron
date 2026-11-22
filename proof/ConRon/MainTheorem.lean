import ConRon.MainTheorem.Driver
import ConRon.MainTheorem.CompareJson
import ConRon.MainTheorem.Oleans
import ConRon.MainTheorem.Modular
import ConRon.MainTheorem.Conclusions
import ConRon.MainTheorem.CompareOleans
import ConRon.MainTheorem.CompareModular

/-!
# `ConRon.MainTheorem` — the main theorems about the binary (task #171, DESIGN.md §3.9)

The twin of `ConLeche/MainTheorem.lean`: the same theorem names, the same conclusions, with
con-leche's run premise `ModelIO.CanGive (Driver.runArgs args) fs 0` replaced by con-ron's
`ConRon.CanGive args fs 0` (`MainTheorem/Driver.lean`): the extracted driver
`driver::cli::run_args` exits 0 at an IO instance whose file operations answer as `fs` at every
state (`AnswersAs`) and whose worker map keeps the pool's contract (`PoolSound`).

What a run of the binary must satisfy to be one of `CanGive`'s is OVERVIEW §8.2's driver row:
`crates/con-ron/src/std_io.rs`'s answers are one snapshot's, its escapes write no file and do
not end the process, its pool keeps `ParallelAll`, and `main` does what it says (the argument
list's code points, the checking thread, `run_args`, the flush, the exit with its code).

**Slice 1: `-- <file>`.**  `json_stages_of_canGive` takes an exit 0 at `["--", file]` to every
step premise of the capstone (`JsonStages`); lane C's `json_model_of_stages` and
`json_no_False_of_stages` (`MainTheorem/Conclusions.lean`) take those to con-leche's
conclusions.  The two theorems below are con-leche's `main_json_model` and `main_no_False`,
word for word but the run premise.

**Slice 3a: `--compare -- <c> <s>`.**  `compare_json_stages_of_canGive`
(`MainTheorem/CompareJson.lean`) takes an exit 0 at `["--compare", "--", c, s]` to the file `c`
in the snapshot and every step premise of the compared capstone (`CompareJsonStages`); lane C's
`compare_json_model_of_stages` takes those to con-leche's conclusion: `main_compare_json_model`.

**Slice 2: `--olean`, `--check-graph`, `--olean --module`, `--olean --modular`.**
`oleans_of_canGive` (`MainTheorem/Oleans.lean`) takes an exit 0 at `["--olean",
"--search-path=" ++ dirs, "--", root]` to the `--olean` capstone's step premises, the root to
`parseModName root` and the search path to `searchPathOf dirs` (`MainTheorem/Args.lean`):
`main_oleans`.  `modular_of_canGive` and `modular_one_of_canGive` (`MainTheorem/Modular.lean`)
take the graph check's and each module worker's exits 0 (each its own run, at its own instance,
all on the one snapshot `fs`), or `--olean --modular`'s, to con-leche's family of models:
`main_modular` and `main_modular_one`.

**Slice 3b: the compared `.olean` runs.**  `compare_of_canGive`
(`MainTheorem/CompareOleans.lean`) takes an exit 0 at `["--olean", "--compare",
"--trusted-search-path=" ++ T, "--search-path=" ++ D, "--", c, s]` to the compared capstone's
step premises, the challenge read through `trustedOr (searchPathOf T) (searchPathOf D)`:
`main_compare_model`.  `modular_cmp_facts_of_canGive` and `modular_cmp_one_of_canGive`
(`MainTheorem/CompareModular.lean`) take the compared graph check's, every worker's and the
compare worker's exits 0, or `--olean --modular --compare`'s, to con-leche's family of models
(`cmp_family`, upstream's `compare_sees_isModel`) and to the challenge's having no constant of
type `False` (`cmp_no_False`): `main_modular_compare`, `main_modular_compare_one`,
`main_modular_compare_no_False`.
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
  have ⟨h1, h2, hreads, h3, h4, hpins, h5, h6, h7, h8, hcat⟩ := ConRon.json_stages_of_canGive h hb
  json_model_of_stages V h1 h2 hreads hcat h3 h4 hpins h5 h6 h7 h8

/-- con-leche: ConLeche/MainTheorem.lean:51-57 main_no_False —
**No accepted file declares a theorem of type `False`**: no exit 0 of `-- <file>` reads a
`jsonWithTheoremFalse` file. -/
theorem main_no_False (V : Type w) [ConLeche.SetTheory V] {file : String} {fs : FS}
    {b : ByteArray}
    (h : ConRon.CanGive ["--", file] fs 0) (hb : fs.file file = some b)
    (hF : jsonWithTheoremFalse [b]) : False :=
  have ⟨h1, h2, hreads, h3, h4, hpins, h5, h6, h7, h8, hcat⟩ := ConRon.json_stages_of_canGive h hb
  json_no_False_of_stages V hcat hF h1 h2 hreads h3 h4 hpins h5 h6 h7 h8

/-- con-leche: ConLeche/MainTheorem.lean:60-67 main_compare_json_model —
**An accepted comparison's challenge file has a model**: an exit 0 of `--compare -- <c> <s>`
read the file `c` as records that have a model in every set theory. -/
theorem main_compare_json_model (V : Type w) [ConLeche.SetTheory V] {c s : String} {fs : FS}
    (h : ConRon.CanGive ["--compare", "--", c, s] fs 0) :
    ∃ bC rC, fs.file c = some bC ∧ parseChunks [bC] = .ok rC ∧
      ∃ model, IsModel V model (· ∈ constantsOf rC.decls.toList) :=
  have ⟨bC, hbC, ⟨h1, h2, hreadsC, hreadsS, hcat, h3, h3S, hdup, h4S, hpins, h5, h6S, h7S, h8S,
    h4, hside, hsol, h6, h7, h8⟩⟩ := ConRon.compare_json_stages_of_canGive h
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
  oleans_of_canGive V hr h

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
  compare_of_canGive V hc hs h

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
  modular_of_canGive V hr h hwork

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
  modular_one_of_canGive V hr h

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
    modular_cmp_facts_of_canGive hc hs hgraph hwork hcmp
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
  modular_cmp_one_of_canGive V hc hs h

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
    modular_cmp_facts_of_canGive hc hs hgraph hwork hcmp
  cmp_no_False good hC edges inj hhdr acc V (.root (by simp)) hci hty

end ConRon.MainTheorem
