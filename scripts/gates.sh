#!/usr/bin/env bash
# THE gate.  Run this before every commit (DESIGN.md §7, CLAUDE.md).
#
#   scripts/gates.sh
#
# Runs, in order, and stops at the first failure:
#   1. cargo build                          the crate compiles, warning-free
#   2. cargo test                           the unit tests pass
#   3. scripts/lint-rust-style.sh           the Aeneas subset (§3.4)
#   4. scripts/provenance.py check          every item cites con-leche (§3.7)
#   5. scripts/gen-pins.sh --check          embedded pin text == natOpPinSets
#   6. scripts/extract.sh --check           committed generated Lean == crate
#   7. cd proof && lake build               the whole proof library elaborates
#
# One OK/FAIL line per gate; non-zero exit on the first failure.  Full output
# of every gate goes to `_tmp/gates/<n>-<name>.log`.
set -uo pipefail

root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
logdir="$root/_tmp/gates"
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
run gen-pins      "$root/scripts/gen-pins.sh" --check
run extract-check "$root/scripts/extract.sh" --check
run lake-build    env -C "$root/proof" lake build

echo "gates: all $n OK"

# The standing progress report (DESIGN.md §7), printed after a green run so
# every landing shows where the port and the proof stand.
echo
python3 "$root/scripts/progress.py" --summary
