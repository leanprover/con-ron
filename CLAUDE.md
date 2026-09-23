# Working on con-ron

Read `DESIGN.md` first: it holds the design decisions, the plan, the
iteration protocol and the task log.  Keep it current; append a task
section for every task you land.

* Environment: `direnv` + `flake.nix` provide `cargo`/`rustc` (Charon's
  pinned nightly), `charon`, `aeneas`.  Lean comes from the system `elan`.
* con-leche is the source of truth for what to port: one Rust module per
  Lean file, functions in the same order, each with a doc comment naming
  its source line.  It is a plain `lake` dependency of `proof/` (task #91;
  a vendored `git subtree` for tasks #74–#90, a submodule before that) —
  pinned by `rev` in `proof/lakefile.toml`, resolved from
  `proof/lake-manifest.json`.  `scripts/provenance.py dir` prints its
  checked-out package directory (ordinarily
  `proof/.lake/packages/con-leche`, but never hard-code that: the packages
  directory lives under the shared `_tmp/aeneas-lean/.lake/packages`, and
  `dir` is what every script uses to find it).  It needs `lake update
  con-leche` in `proof/` (once `lakefile.toml` is in place) before anything
  can read it.  `vendor/aeneas` holds the Aeneas docs (`documentation/*.md`,
  `documentation/skills/*`) and its Lean library, and is still a submodule.
* Rust style rules for Aeneas are in `DESIGN.md` §3.4 and enforced by
  `scripts/lint-rust-style.sh` and `scripts/provenance.py check`
  (DESIGN.md §3.7).
* **Gate latency: build the MODULE in the inner loop, the gates at the end.**
  `scripts/gates.sh` is the *landing* gate, not the edit loop.  An agent
  filling in a `sorry` has changed one module: `lake build
  ConRon.Refine2.Specs` (or whichever) is what tells it whether the proof
  went through, and it costs seconds where the full gates cost minutes —
  `extract-check` alone is 100–300 s, and a merge that moves
  `Generated/Funs.lean` costs ~1 000 s of `Core/Eqns.lean` re-derivation.
  Run the module build after every edit, the whole-target build
  (`lake build`, `lake build ConRonBridge`, `lake build ConRonRefine2`) when
  a file is finished, and `scripts/gates.sh` once before reporting.  Never
  run the gates to check a single proof.
* **`scripts/gates.sh` is the one command every task must run before
  committing**: `cargo build`, `cargo test`, the style lint, the provenance
  check, the OVERVIEW link gate, the pin check, `scripts/extract.sh --check`
  and `cd proof && lake build`, in that order, one OK/FAIL line each,
  stopping at the first failure.  On a many-core machine con-leche's first
  build can exhaust memory; cap the parallelism with `LAKE_JOBS=N
  scripts/gates.sh`.
* The Lean model of the crate is *committed*, under `proof/ConRon/Generated/`;
  regenerate it with `scripts/extract.sh` whenever `crates/con-ron-core`
  changes, and commit the result in the same commit.
* `lake build` and `ulimit -v` do not mix: Lean reserves address space per
  thread, and under `ulimit -v 60000000` the build aborts with "failed to
  create thread" on the Mathlib-side modules even at `LEAN_NUM_THREADS=1`.
  Run Lean builds with no `ulimit -v` (or 200 GB), `LEAN_NUM_THREADS=1`
  when a module aborts, `LAKE_JOBS=4`; the `ulimit` rule below is for
  CHECKER runs, not for `lake`.
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
* **A new worktree should copy the build, not rebuild it.**  A fresh
  worktree with no `proof/.lake/build` pays ~17 minutes and 6 GB
  re-deriving `Refine2/Core/Eqns.lean`'s 109 `partial_fixpoint` equations.
  `cp -a --reflink=auto <a tree that has it>/proof/.lake/build
  proof/.lake/build` is instantaneous on this filesystem.  Do it before the
  first `lake build` in any new worktree.  It needs a *source tree that
  still has the build*, which is why the shared Lake cache below is the
  better answer when it has been seeded.
* **The shared Lake artifact cache** (task #97-CACHE).  Lake 5 keeps a
  content-addressed local cache keyed by each module's *input hash* — source
  bytes, import artifact hashes, toolchain, options, module name — with **no
  absolute path in the key**, so one cache serves every worktree, every
  branch, and survives a worktree being deleted.  `flake.nix` points
  `LAKE_CACHE_DIR` at `$CON_RON_ROOT/_tmp/lake-cache`, which is the shared
  `_tmp/`, so all worktrees already read the same cache; Lake's own default
  (`$ELAN_HOME/toolchains/<tc>/lake/cache`) is a separate bind mount in the
  sandbox and would *copy* instead of hard-link, so do not use it.
  * **Reading is automatic and free**: a fresh worktree restores every
    module the cache has, hard-linked into `proof/.lake/build` (0 bytes of
    disk), in seconds.  An empty cache changes nothing.
  * **Writing is opt-in.**  Seeding it is one build, run from a tree that
    already has the artifacts: `LAKE_ARTIFACT_CACHE=true
    LAKE_RESTORE_ARTIFACTS=true lake build <target>` — this re-elaborates
    nothing when the tree is up to date, it just hard-links what is already
    there into the cache.  **Do this after building
    `Refine2/Core/Eqns.lean`**; that one module is the whole prize.
  * `lake cache get`/`put` are for *remote* services (Reservoir/S3) and are
    irrelevant here.  `lake cache clean` (or `rm -rf _tmp/lake-cache`) is
    the only GC there is: the cache pins every artifact ever written to it,
    so it grows across bumps and wants an occasional sweep.
  * **Caveat for the shared `_tmp/aeneas-lean`**: a writable-cache build
    also caches the *dependency* packages in the target's import closure,
    which chmods their build files to `r--r--r--` and rewrites their
    `.hash` files.  That is Lake's normal behaviour and is harmless, but it
    is a write to shared state — so seed from a tree whose packages are its
    own, or accept it deliberately; never turn `LAKE_ARTIFACT_CACHE` on
    project-wide without saying so.
* **Shared state between agent worktrees.** `_tmp/` is one directory shared
  through a symlink by every worktree: never rebuild, clean or re-copy
  `_tmp/aeneas-lean` (the patched Aeneas library and Mathlib) from a worktree
  — if `proof/.lake/packages` is missing, symlink it to the main tree's
  `_tmp/aeneas-lean/.lake/packages` and nothing else; `extract.sh` and
  `gates.sh` key their scratch and log directories by checkout for the same
  reason.  Since task #91 this extends to con-leche: its lake package
  directory lives under that same shared `_tmp/aeneas-lean/.lake/packages`,
  so `lake update con-leche` in one worktree's `proof/` moves the checkout
  every other worktree reads.  Never edit it directly from an agent.  A
  bump campaign (editing the `rev` in `lakefile.toml` and running `lake
  update con-leche` repeatedly while reconciling) must give that worktree
  its own packages directory instead of the shared symlink — copy
  `_tmp/aeneas-lean` once (`AENEAS_LEAN_DEST` in `scripts/setup-aeneas-lean.sh`
  supports a private destination) rather than sharing it for the campaign's
  duration, and only merge the result back through the normal commit, not
  by touching the shared directory.
* **`lake env lean <file>` does not inherit `proof/lakefile.toml`'s
  `weak.backward.do.legacy = true`**, so it runs a *different* `do`
  elaborator: join points land elsewhere, and a proof that passes under
  `lake build` can fail under it and vice versa.  It presents as a green
  theorem in an untouched file suddenly failing, and cost one agent an hour
  of bisection.  Iterate with `lake build <module>`, or with
  `lake env lean -Dbackward.isDefEq.respectTransparency=false
  -Dbackward.do.legacy=true <file>`.
* **An agent's `cd` does not persist between tool calls.**  `cd <main tree>
  && python3 …` in one call edits the MAIN TREE, and the next call's
  `git commit` then runs back in the worktree — so the edit lands on the
  integration branch and the commit message ends up on something else.
  That is how `a0a0c6a9` arrived on `arena` from a running agent (task
  #97-P3-Core round 3, diagnosed by the agent itself).  Never reach out of
  the worktree: do every edit with a path relative to the worktree, and if
  a file genuinely belongs to another checkout, say so in the report
  instead of editing it.
* **Agents land their own branches** (maintainer's instruction, 2026-09-23:
  keeps the coordinator's context tidy).  When the round is done: merge the
  integration branch (`arena` during the campaign) into your branch, run
  `scripts/gates.sh`, then `scripts/land.sh <your worktree path>` — it
  fast-forwards the main tree and drops your worktree.  If it is not a
  fast-forward, merge again, re-run the gates the delta can touch, retry.
  `land.sh` is the one sanctioned write to the main tree from an agent;
  everything else still stays inside your worktree.  Then send the
  coordinator a short report: the landed commit, counts, findings, and every
  ruling you need.
* **Landing a branch (merge discipline).**  The *agent* merges master into
  its branch and runs the gates there; the landing is then a fast-forward
  merge of that branch into master.  If master moved in between so the
  merge is not a fast-forward, the agent merges master again and re-runs
  the gates — unless what moved on master since the last gated state is
  clearly irrelevant (documentation only, a script the gates do not run),
  in which case skip the gates, or the gates the change cannot touch, to
  keep development velocity.  The gates are not run a second time on master
  after a fast-forward.  Landing then finishes with
  `scripts/drop-worktree.sh <its worktree path>` — which removes exactly
  that worktree, its branch and its per-checkout scratch under `_tmp/`, and
  refuses a branch that is not merged.  Nothing sweeps
  worktrees automatically (an agent may be working in one).  Task scratch
  under `_tmp/` is deleted once its numbers are in DESIGN.md; the corpus and
  `_tmp/aeneas-lean` stay.

  **A landing is three steps, not two: merge, drop the worktree, STOP THE
  AGENT.**  A finished agent is still a live subagent holding its context;
  nothing sweeps them, and in every view except an explicit listing a finished
  agent looks exactly like a working one, so the step is invisible when it is
  skipped and they pile up.  `scripts/drop-worktree.sh` prints the agent id to
  stop as its last line — do it then, not in a later sweep.  The same goes for
  the scratch: the script deletes `_tmp/{gates,extract,extract-check}-<key>`,
  and skipping it once cost 13 GB of orphans on a shared machine.
* Commit often; the maintainer pushes and opens PRs.
