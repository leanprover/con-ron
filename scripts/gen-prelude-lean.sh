#!/usr/bin/env bash
# Regenerate the embedded lean4export text of con-leche's built-in prelude
# into `proof/ConRon/Arena/Frontend/PreludeText.lean` (task #97e part 2, the
# `gen-prelude.sh` idiom of task #84 applied to (B), the Lean arena checker).
#
#   scripts/gen-prelude-lean.sh            rewrite the committed file in place
#   scripts/gen-prelude-lean.sh --check    regenerate into `_tmp/` and diff;
#                                          non-zero on any difference.  This is
#                                          the freshness rule "the embedded
#                                          text is con-leche's own committed
#                                          prelude at the pinned con-leche
#                                          commit".
#
# The source of truth is con-leche's own committed file, the one its
# `builtinPreludeText` reads with `include_str`:
#
#   pins/<toolchain>.prelude.ndjson
#
# in con-leche's own tree -- a plain lake dependency of proof/ since task
# #91, so its directory is resolved through `provenance.py dir`, not a
# fixed repository-relative path.
#
# **Why a constant and not `include_str`.**  Task #97e part 1's
# `Frontend/Prelude.lean` reached the file through the lake package directory,
# which makes that module's `.olean` depend on a path outside the repository.
# That is exactly the objection `scripts/gen-prelude.sh` answered for the Rust
# port at task #84; this is the same answer for (B).  The generated module's
# own note has the rest, including why it mirrors the Rust's 67-chunk
# splitting (to be one-to-one with its twin) and why the chunks are BYTES and
# not strings (a 256-byte boundary may fall inside a multi-byte character).
set -euo pipefail

root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
out="$root/proof/ConRon/Arena/Frontend/PreludeText.lean"

# Bytes per chunk.  The Rust twin's, verbatim
# (`crates/con-ron-core/src/frontend/prelude_text.rs`), so the two files split
# the prelude at the same offsets.
CHUNK=256

check=0
case "${1-}" in
  "") ;;
  --check) check=1 ;;
  *) echo "usage: $0 [--check]" >&2; exit 2 ;;
esac
[ "$#" -le 1 ] || { echo "usage: $0 [--check]" >&2; exit 2; }

cl="$(python3 "$root/scripts/provenance.py" dir)" || exit 1

# The toolchain the pinned con-leche uses, which names the prelude file:
# `Frontend/Prelude.lean`'s `include_str` path is the authority, so read it
# from there rather than guessing.
src_rel=$(sed -n 's|.*include_str "\.\./\.\./\(pins/[^"]*\)".*|\1|p' \
  "$cl/ConLeche/Frontend/Prelude.lean" | head -1)
[ -n "$src_rel" ] || {
  echo "error: could not read the include_str path out of con-leche's Frontend/Prelude.lean" >&2
  exit 1; }
src="$cl/$src_rel"
[ -s "$src" ] || { echo "error: $src is missing or empty" >&2; exit 1; }

# Per-checkout scratch: `_tmp` is shared between agent worktrees (a symlink),
# and concurrent runs must not overwrite each other's files.
work="$root/_tmp/gen-prelude-lean-$(printf '%s' "$root" | sha256sum | cut -c1-12)"
rm -rf "$work"
mkdir -p "$work"

echo "gen-prelude-lean: con-leche/$src_rel"

python3 "$root/scripts/gen-prelude-lean.py" "$src" "$src_rel" "$CHUNK" \
  > "$work/PreludeText.lean"

lines=$(wc -l < "$src")
bytes=$(wc -c < "$src")

if [ "$check" -eq 1 ]; then
  if ! diff -u "$out" "$work/PreludeText.lean" > "$work/PreludeText.lean.diff" 2>&1; then
    echo "gen-prelude-lean --check: Arena/Frontend/PreludeText.lean differs from con-leche's prelude:" >&2
    sed -n '1,20p' "$work/PreludeText.lean.diff" >&2
    echo "gen-prelude-lean --check: FAIL -- run scripts/gen-prelude-lean.sh and commit the result" >&2
    exit 1
  fi
  echo "gen-prelude-lean --check: OK (embedded bytes = $src_rel at the pinned commit, $lines records, $bytes bytes)"
else
  cp "$work/PreludeText.lean" "$out"
  echo "gen-prelude-lean: wrote proof/ConRon/Arena/Frontend/PreludeText.lean ($lines lines, $bytes bytes of text)"
fi
