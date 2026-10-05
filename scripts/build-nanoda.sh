#!/usr/bin/env bash
# scripts/build-nanoda.sh -- the nanoda baseline binary of OVERVIEW section 9
# (task #114), exactly as DESIGN.md "Task #97-P6-3" built it by hand:
#
#   * upstream `ammkrn/nanoda_lib` at commit 4c544ed (the one section 8.1's
#     research report surveyed), cloned into $NANODA's build directory;
#   * an empty `[workspace]` table appended to its `Cargo.toml` (`_tmp/` is
#     inside the con-ron checkout, so Cargo would otherwise find con-ron's
#     workspace and refuse; the table also restores nanoda's own
#     `[profile.release]`).  This is why `identity.json` calls the build dirty;
#   * `cargo build --release` with the dev shell's toolchain.
#
# The binary lands at $NANODA, whose default is `scripts/bench-baselines.sh`'s:
# `_tmp/t97/nanoda-build/target/release/nanoda_bin`.  Idempotent: nothing is
# done when that binary exists and its tree is at the commit.  A tree at
# another commit (or without a binary) is removed and rebuilt.
#
# Usage: scripts/build-nanoda.sh
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
NANODA="${NANODA:-$ROOT/_tmp/t97/nanoda-build/target/release/nanoda_bin}"
NANODA_URL="${NANODA_URL:-https://github.com/ammkrn/nanoda_lib}"
NANODA_COMMIT=4c544ed4099c8227f07d5de77ad1e69fb0740a27
SRC="${NANODA%/target/release/nanoda_bin}"
[[ $SRC != "$NANODA" ]] || { echo "build-nanoda.sh: \$NANODA must end in /target/release/nanoda_bin" >&2; exit 2; }

if [[ -x $NANODA ]] && [[ $(git -C "$SRC" rev-parse HEAD 2>/dev/null) == "$NANODA_COMMIT" ]]; then
  echo "build-nanoda.sh: $NANODA is there (nanoda ${NANODA_COMMIT:0:7})" >&2
  exit 0
fi

echo "== building nanoda ${NANODA_COMMIT:0:7} in $SRC" >&2
rm -rf "$SRC"
mkdir -p "$(dirname "$SRC")"
git clone --quiet "$NANODA_URL" "$SRC"
git -C "$SRC" checkout --quiet --detach "$NANODA_COMMIT"
printf '\n[workspace]\n' >> "$SRC/Cargo.toml"
(cd "$SRC" && cargo build --release)
[[ -x $NANODA ]] || { echo "build-nanoda.sh: cargo did not produce $NANODA" >&2; exit 1; }
