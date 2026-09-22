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
#  13. cd proof && lake build               the whole proof library elaborates
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

echo "gates: all $n OK"

# The standing progress report (DESIGN.md §7), printed after a green run so
# every landing shows where the port and the proof stand.
echo
python3 "$root/scripts/progress.py" --summary
python3 "$root/scripts/loc.py" --summary
