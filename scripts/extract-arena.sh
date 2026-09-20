#!/usr/bin/env bash
# Extract `crates/arena-core` to Lean, through Charon and Aeneas, into
# `proof/ConRon/ArenaGen/` (task #97 P4a, DESIGN.md §8.5).  A copy of
# `scripts/extract.sh`'s invocation pointed at the arena crate.
#
#   scripts/extract-arena.sh            write into proof/ConRon/ArenaGen/
#   scripts/extract-arena.sh --dry      leave the output in _tmp/ and only
#                                       report the hole list and the line count
#
# P4a runs it `--dry`: the generated model is NOT committed yet (the crate is
# still growing, module by module, through P4b), and the point of the run is
# to confirm that the crate is inside Aeneas's subset and to price the crate
# boundary.  `charon cargo` does not descend into a path dependency, so every
# `con_ron_core::…` item this crate calls comes out as an `@[rust_fun]` /
# `@[rust_type]` axiom; the boundary disappears when DESIGN.md §8.6's swap
# merges the two crates.
set -euo pipefail

root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
crate_dir="$root/crates/arena-core"
crate="arena_core"
subdir="ConRon/ArenaGen"
namespace="ConRon.ArenaGen"
committed="$root/proof/$subdir"

dry=0
case "${1-}" in
  "") ;;
  --dry) dry=1 ;;
  *) echo "usage: $0 [--dry]" >&2; exit 2 ;;
esac

ckey=$(printf '%s' "$root" | sha256sum | cut -c1-12)
work="$root/_tmp/extract-arena-$ckey"
rm -rf "$work"
mkdir -p "$work/llbc" "$work/lean"

echo "extract-arena: charon cargo --preset=aeneas ($crate_dir)"
( cd "$crate_dir" && charon cargo --preset=aeneas --dest-file "$work/llbc/$crate.llbc" )

echo "extract-arena: aeneas -backend lean -split-files -loops-to-rec"
aeneas -backend lean -split-files -loops-to-rec \
  -dest "$work/lean" -subdir "$subdir" -namespace "$namespace" \
  -no-progress-bar "$work/llbc/$crate.llbc"

out="$work/lean/$subdir"
echo "extract-arena: generated $(cat "$out"/Types.lean "$out"/Funs.lean | wc -l) lines of model"
echo "extract-arena: $(grep -c '^axiom' "$out"/TypesExternal_Template.lean || true) type hole(s), $(grep -c '^axiom' "$out"/FunsExternal_Template.lean || true) function hole(s)"

if [ "$dry" -eq 1 ]; then
  echo "extract-arena: --dry, left in $work"
else
  mkdir -p "$committed"
  for f in Types.lean Funs.lean TypesExternal_Template.lean FunsExternal_Template.lean; do
    cp "$out/$f" "$committed/"
  done
  echo "extract-arena: wrote 4 files to proof/$subdir"
fi
