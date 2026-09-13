# Working on con-ron

Read `DESIGN.md` first: it holds the design decisions, the plan, the
iteration protocol and the task log.  Keep it current; append a task
section for every task you land.

* Environment: `direnv` + `flake.nix` provide `cargo`/`rustc` (Charon's
  pinned nightly), `charon`, `aeneas`.  Lean comes from the system `elan`.
* `vendor/con-leche` (pinned submodule) is the source of truth for what to
  port: one Rust module per Lean file, functions in the same order, each with
  a doc comment naming its source line.  `vendor/aeneas` holds the Aeneas
  docs (`documentation/*.md`, `documentation/skills/*`) and its Lean library.
* Rust style rules for Aeneas are in `DESIGN.md` §3.4 and enforced by
  `scripts/lint-rust-style.sh` and `scripts/provenance.py check`
  (DESIGN.md §3.7).
* **`scripts/gates.sh` is the one command every task must run before
  committing**: `cargo build`, `cargo test`, the style lint, the provenance
  check, `scripts/extract.sh --check` and `cd proof && lake build`, in that
  order, one OK/FAIL line each, stopping at the first failure.
* The Lean model of the crate is *committed*, under `proof/ConRon/Generated/`;
  regenerate it with `scripts/extract.sh` whenever `crates/con-ron-core`
  changes, and commit the result in the same commit.
* Large artifacts (exports, scratch builds) go to `_tmp/` (gitignored).
  Use `timeout` on every checker run and **always** `ulimit -v` on a checker
  run: this machine kills the whole user session at 50 GB.  The limit for a
  con-ron run is at most 3× what con-leche needs on the same input
  (`_tmp/corpus/baseline.md`: `Init` 0.5 GB, `Init+Std+Lean` 1.3 GB, Mathlib
  8.6 GB); if con-ron exceeds it, that is a bug to investigate and fix before
  running anything larger — never raise the limit instead.
* **Measuring**: this machine is shared and you do not see every process.
  The measure of record is `perf stat -e instructions:u,cycles:u`; wall
  time is secondary and only meaningful from several runs of a benchmark
  small enough to repeat (`Init`, the fixtures) — never from one run of a
  large one. Report the spread when you report wall time.
* **Shared state between agent worktrees.** `_tmp/` is one directory shared
  through a symlink by every worktree: never rebuild, clean or re-copy
  `_tmp/aeneas-lean` (the patched Aeneas library and Mathlib) from a worktree
  — if `proof/.lake/packages` is missing, symlink it to the main tree's
  `_tmp/aeneas-lean/.lake/packages` and nothing else; `extract.sh` and
  `gates.sh` key their scratch and log directories by checkout for the same
  reason.  Never edit the main tree's `vendor/con-leche` from an agent: it
  is what the main tree's proof build reads.
* Commit often; the maintainer pushes and opens PRs.
