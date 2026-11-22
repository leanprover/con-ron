import ConRon.MainTheorem.Driver
import ConRon.MainTheorem.CompareJson
import ConRon.MainTheorem.Conclusions

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

end ConRon.MainTheorem
