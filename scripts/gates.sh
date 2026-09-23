#!/usr/bin/env bash
# THE gate.  Run this before every commit (DESIGN.md §7, CLAUDE.md).
#
#   scripts/gates.sh
#
# Runs, in order, and stops at the first failure:
#   1. cargo build                          the crate compiles, warning-free
#   2. cargo test                           the unit tests pass
#   3. scripts/lint-rust-style.sh           the Aeneas subset (§3.4), both crates
#   4. scripts/provenance.py check          every item cites con-leche (§3.7)
#   5. scripts/provenance-selftest.py        the gate's Lean parser, on its fixture
#   6. scripts/twin-lines.py check          every `Lean twin:` line names a
#                                           declaration of `proof/ConRon/**` at
#                                           its current lines (§3.7)
#   7. scripts/overview-links.sh            OVERVIEW.md/DESIGN.md line anchors
#   8. scripts/holes.sh --check             OVERVIEW.md §8.1 == the model's holes
#   9. scripts/gen-pins.sh --check          embedded pin text == natOpPinSets
#  10. scripts/gen-prelude.sh --check       embedded prelude text == con-leche's
#  11. scripts/gen-prelude-lean.sh --check  (B)'s embedded prelude bytes, ditto
#  12. scripts/extract.sh --check           committed generated Lean == crate
#  13. cd proof && lake build               the default targets elaborate
#  14. cd proof && lake build ConRonRefine2  Theorem 2's tier (not a default target)
#  15. cd proof && lake build ConRonBridge   Theorem 1's tier (ditto)
#  16. cd proof && lake build ConRonCapstone the composition, the two root theorems
#      (LAKE_JOBS=N caps lake's parallelism through LEAN_NUM_THREADS — Lake 5
#      has no jobs flag: on a many-core machine the first build of the
#      vendored con-leche can exhaust memory, task #74)
#
# One OK/FAIL line per gate; non-zero exit on the first failure.  Full output
# of every gate goes to `_tmp/gates/<n>-<name>.log`.
set -uo pipefail

root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
# Per-checkout log dir: `_tmp` is shared between agent worktrees (a symlink),
# and concurrent gate runs must not overwrite each other's logs.
logdir="$root/_tmp/gates-$(printf '%s' "$root" | sha256sum | cut -c1-12)"
rm -rf "$logdir"
mkdir -p "$logdir"
n=0

run() { # run <name> <cmd...>
  n=$((n + 1))
  local name=$1; shift
  local log="$logdir/$n-$name.log"
  local start end
  start=$(date +%s)
  if "$@" > "$log" 2>&1; then
    end=$(date +%s)
    printf 'OK   %-22s (%ds)\n' "$name" "$((end - start))"
  else
    local rc=$?
    end=$(date +%s)
    printf 'FAIL %-22s (%ds, exit %d) -- %s\n' "$name" "$((end - start))" "$rc" "$log"
    echo "--- last 40 lines ---"
    tail -40 "$log"
    exit 1
  fi
}

# `cargo build`/`cargo test` must be warning-free (§7), which `cargo` does not
# enforce by itself: `-D warnings` does.
run cargo-build   env RUSTFLAGS="-D warnings" cargo build --manifest-path "$root/Cargo.toml"
run cargo-test    env RUSTFLAGS="-D warnings" cargo test  --manifest-path "$root/Cargo.toml"
run lint-rust     "$root/scripts/lint-rust-style.sh" "$root/crates/con-ron-core/src"
run provenance    python3 "$root/scripts/provenance.py" check
run provenance-self python3 "$root/scripts/provenance-selftest.py"
# The other half of the same ledger: `provenance` checks what the Rust was
# ported FROM (con-leche, a pinned tree), `twin-lines` what it is a port OF
# (`proof/ConRon/**`, OUR tree, which every task edits — so its ranges rot
# faster).  Task #97-TWIN.
run twin-lines    python3 "$root/scripts/twin-lines.py" check
run overview-links "$root/scripts/overview-links.sh"
run holes         "$root/scripts/holes.sh" --check
run gen-pins      "$root/scripts/gen-pins.sh" --check
run gen-prelude   "$root/scripts/gen-prelude.sh" --check
run gen-prelude-lean "$root/scripts/gen-prelude-lean.sh" --check
run extract-check "$root/scripts/extract.sh" --check
run lake-build    env -C "$root/proof" ${LAKE_JOBS:+LEAN_NUM_THREADS="$LAKE_JOBS"} lake build
# `ConRonRefine2` is deliberately NOT a default target (a half-built P5 tier
# must not block `lake build`), which means the line above never elaborates a
# single module of `ConRon/Refine2/**`.  Until task #97-P5-Mut found this, a
# green gate run said nothing whatsoever about a Theorem-2 lane.  It is its
# own step so the OK/FAIL line names it.
run lake-refine2  env -C "$root/proof" ${LAKE_JOBS:+LEAN_NUM_THREADS="$LAKE_JOBS"} lake build ConRonRefine2
# **And `ConRonBridge` is not a default target either** — same hole, one tier
# over, found by task #97-P3-Ind round 5 when a green gate run was followed by
# a broken `lake build ConRonBridge`.  Every P3 brief has had to ask for the
# target by hand for exactly this reason; now the gate does it, so a green run
# means Theorem 1's spec layer elaborates too.
run lake-bridge   env -C "$root/proof" ${LAKE_JOBS:+LEAN_NUM_THREADS="$LAKE_JOBS"} lake build ConRonBridge
# **The composition** (task #97-COMPOSE): `ConRon/Capstone.lean`, the one
# module importing both theorems, states `ConRon.Capstone.model_exists` and
# `ConRon.Capstone.no_False_declaration` for the Rust pipeline.  Its own
# library, not a default target, for the reason the two above are not; its
# `#guard_msgs` census is what fails if a seam moves.
run lake-capstone env -C "$root/proof" ${LAKE_JOBS:+LEAN_NUM_THREADS="$LAKE_JOBS"} lake build ConRonCapstone

echo "gates: all $n OK"

# The standing progress report (DESIGN.md §7), printed after a green run so
# every landing shows where the port and the proof stand.
echo
python3 "$root/scripts/progress.py" --summary
# The arena's own ledger (task #97-CENSUS): `progress.py` above is the OLD
# tower's report — it credits a con-leche declaration when `Refine/<M>.lean`
# states `f_refines`, and that tree is retired.  This one counts the TWINS of
# `proof/ConRon/Arena/**` against Theorem 1 (`Bridge/**`) and Theorem 2
# (`Refine2/**`).  A REPORT, never a FAIL: it runs after the gates and its
# exit code is ignored on purpose.
python3 "$root/scripts/arena-census.py" --summary || true
python3 "$root/scripts/loc.py" --summary
