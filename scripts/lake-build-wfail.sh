#!/usr/bin/env bash
# `lake build` in `proof/`, failing on any warning from OUR sources (task #102).
#
#   scripts/lake-build-wfail.sh [lake build args…]
#
# Lake's own `--wfail` cannot be used: it also fails on the warnings Lake
# REPLAYS from dependency modules' logs, and Aeneas logs ~350 of them
# (`AeneasMeta/Async/Test.lean`, `Aeneas/Data/Coinductive/*`, …) that are not
# ours to fix.  `warningAsError` in `proof/lakefile.toml`'s `leanOptions` is
# scoped to our package, but it would make every warning an ERROR in the inner
# loop too — a lane's work-in-progress `sorry` would stop its module (and
# everything downstream) from building.  So the build runs as usual and this
# script fails afterwards if a warning names a `.lean` file of `proof/` itself.
#
# Exempt: `declaration uses 'sorry'` in a *Test* file (the no-stray-sorry rule
# allows `sorry` there and nowhere else).
#
# Limitation (task #101): a module restored from the shared Lake cache comes
# back with an EMPTY log, so only modules this build compiled are checked —
# which are exactly the ones the change under test touched, and their
# dependents.
set -uo pipefail
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
out=$(mktemp)
trap 'rm -f "$out"' EXIT
env -C "$root/proof" lake build "$@" 2>&1 | tee "$out"
rc=${PIPESTATUS[0]}
[ "$rc" -eq 0 ] || exit "$rc"
ours=$(grep -E '^warning: [^ :]+\.lean:[0-9]+:[0-9]+: ' "$out" | while IFS= read -r line; do
  f=${line#warning: }; f=${f%%.lean:*}.lean
  [ -f "$root/proof/$f" ] || continue
  case "$f:$line" in *Test*:*"declaration uses 'sorry'"*) continue;; esac
  printf '%s\n' "$line"
done)
if [ -n "$ours" ]; then
  echo
  echo "lake-build-wfail: $(printf '%s\n' "$ours" | wc -l) warning(s) from proof/'s own sources:"
  printf '%s\n' "$ours"
  exit 1
fi
