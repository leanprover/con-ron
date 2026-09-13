# Working on con-ron

Read `DESIGN.md` first: it holds the design decisions, the plan, the
iteration protocol and the task log.  Keep it current; append a task
section for every task you land.

* Environment: `direnv` + `flake.nix` provide `cargo`/`rustc` (Charon's
  pinned nightly), `charon`, `aeneas`.  Lean comes from the system `elan`.
* `vendor/con-leche` (a vendored `git subtree`, squashed; its upstream commit
  is the first word of `vendor/CON_LECHE_PIN`) is the source of truth for
  what to port: one Rust module per Lean file, functions in the same order,
  each with a doc comment naming its source line.  `vendor/aeneas` holds the
  Aeneas docs (`documentation/*.md`, `documentation/skills/*`) and its Lean
  library.
* Rust style rules for Aeneas are in `DESIGN.md` §3.4 and enforced by
  `scripts/lint-rust-style.sh` and `scripts/provenance.py check`
  (DESIGN.md §3.7).
* **`scripts/gates.sh` is the one command every task must run before
  committing**: `cargo build`, `cargo test`, the style lint, the provenance
  check, the OVERVIEW link gate, the pin check, `scripts/extract.sh --check`
  and `cd proof && lake build`, in that order, one OK/FAIL line each,
  stopping at the first failure.  On a many-core machine the first build of
  the vendored con-leche can exhaust memory; cap the parallelism with
  `LAKE_JOBS=N scripts/gates.sh`.
* The Lean model of the crate is *committed*, under `proof/ConRon/Generated/`;
  regenerate it with `scripts/extract.sh` whenever `crates/con-ron-core`
  changes, and commit the result in the same commit.
* Large artifacts (exports, scratch builds) go to `_tmp/` (gitignored).
  Run every checker under `timeout` and **always** under `ulimit -v`: a
  runaway checker must die rather than take the machine down.  The budget for
  a con-ron run is at most 3× what con-leche needs on the same input
  (measured: `Init` 0.5 GB, `Init+Std+Lean` 1.3 GB, Mathlib 8.6 GB); if
  con-ron exceeds it, that is a bug to investigate and fix before running
  anything larger — never raise the limit instead.
* **Measuring**: the measure of record is
  `perf stat -e instructions:u,cycles:u`, which does not depend on what else
  the machine is doing.  Wall time is secondary and only meaningful from
  several runs of a benchmark small enough to repeat (`Init`, the fixtures) —
  never from one run of a large one.  Report the spread when you report wall
  time.
* **Shared state between agent worktrees.** `_tmp/` is one directory shared
  through a symlink by every worktree: never rebuild, clean or re-copy
  `_tmp/aeneas-lean` (the patched Aeneas library and Mathlib) from a worktree
  — if `proof/.lake/packages` is missing, symlink it to the main tree's
  `_tmp/aeneas-lean/.lake/packages` and nothing else; `extract.sh` and
  `gates.sh` key their scratch and log directories by checkout for the same
  reason.  Never edit the main tree's `vendor/con-leche` from an agent: it
  is what the main tree's proof build reads.
* **Disk.** Landing an agent branch is three steps: merge it, run the gates
  on master, then `scripts/drop-worktree.sh <its worktree path>` — which
  removes exactly that worktree, its branch and its per-checkout scratch
  under `_tmp/`, and refuses a branch that is not merged.  Nothing sweeps
  worktrees automatically (an agent may be working in one).  Task scratch
  under `_tmp/` is deleted once its numbers are in DESIGN.md; the corpus and
  `_tmp/aeneas-lean` stay.
* Commit often; the maintainer pushes and opens PRs.
