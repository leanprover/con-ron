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
  `scripts/lint-rust-style.sh`.
* Large artifacts (exports, scratch builds) go to `_tmp/` (gitignored).
  Use `timeout` on every checker run and `ulimit -v` when a run may OOM.
* Commit often; the maintainer pushes and opens PRs.
