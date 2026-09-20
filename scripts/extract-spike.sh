#!/usr/bin/env bash
# Extract `crates/arena-spike` to Lean, through Charon and Aeneas, into
# `proof/ConRon/Arena/Spike/Generated/` (task #97s, DESIGN.md §8.6 experiments
# C and D).  A copy of `scripts/extract.sh`'s invocation, pointed at the
# spike's throw-away crate; no hole checking and no `--check` mode, because
# the spike is a measurement rather than a deliverable.
set -euo pipefail

root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
crate_dir="$root/crates/arena-spike"
crate="arena_spike"
subdir="ConRon/Arena/Spike/Generated"
namespace="ConRon.Arena.Spike.Generated"
committed="$root/proof/$subdir"

ckey=$(printf '%s' "$root" | sha256sum | cut -c1-12)
work="$root/_tmp/extract-spike-$ckey"
rm -rf "$work"
mkdir -p "$work/llbc" "$work/lean"

echo "extract-spike: charon cargo --preset=aeneas ($crate_dir)"
( cd "$crate_dir" && charon cargo --preset=aeneas --dest-file "$work/llbc/$crate.llbc" )

echo "extract-spike: aeneas -backend lean -split-files -loops-to-rec"
aeneas -backend lean -split-files -loops-to-rec \
  -dest "$work/lean" -subdir "$subdir" -namespace "$namespace" \
  -no-progress-bar "$work/llbc/$crate.llbc"

out="$work/lean/$subdir"
mkdir -p "$committed"
for f in "$out"/*.lean; do cp "$f" "$committed/"; done
echo "extract-spike: wrote $(ls "$committed" | wc -l) files to proof/$subdir"
