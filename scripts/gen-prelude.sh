#!/usr/bin/env bash
# Regenerate the embedded lean4export text of con-leche's built-in prelude
# into `crates/con-ron-core/src/frontend/prelude_text.rs` (task #84, the
# `gen-pins.sh` idiom of task #43).
#
#   scripts/gen-prelude.sh            rewrite the committed file in place
#   scripts/gen-prelude.sh --check    regenerate into `_tmp/` and diff;
#                                     non-zero on any difference.  This is the
#                                     freshness rule "the embedded text is
#                                     con-leche's own committed prelude at the
#                                     pinned con-leche commit".
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
# **Why a generated constant and not `include_str!`.**  The unverified port
# used `include_str!(concat!(env!("CARGO_MANIFEST_DIR"), "/../../vendor/..."))`,
# which makes the *verified* crate's build depend on a path outside itself --
# on a submodule that may be absent, and on a file no reader of
# `crates/con-ron-core` can see.  `kernel/pins_text.rs` settled the question
# for the pin list at task #43 and this follows it: the data is committed
# inside the crate, a script regenerates it from con-leche, and a gate says
# the two agree.  The extraction then has nothing to resolve.
#
# **Why chunked byte arrays and not one `&str`.**  Both obvious shapes fail,
# and task #84 measured each; the generated module's own note has the detail.
# A `&str` constant comes out of Aeneas as `toStr "..."` with the double
# quotes inside it UNESCAPED (AENEAS_FINDINGS's F17), and an ndjson stream is
# nothing but quotes; a single `[u8; 16922]` comes out as an
# element-by-element `Array.make` that Lean cannot elaborate inside a million
# heartbeats.  `CHUNK` below is a size that does elaborate.
#
# The wrapping is byte-exact: the concatenation of the chunks is the ndjson
# file, byte for byte, including its final newline, so the parse of it is the
# parse `con-ron` would do on that file.  The prelude's two non-ASCII entries
# are simply their UTF-8 bytes, which is what the scanner reads.
set -euo pipefail

root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
out="$root/crates/con-ron-core/src/frontend/prelude_text.rs"

# Bytes per chunk.  Small enough that Lean elaborates each `Array.make`
# without a heartbeat cap in sight (the rest of the model's largest array is
# 72 elements), large enough that the module stays readable.
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

work="$root/_tmp/gen-prelude"
rm -rf "$work"
mkdir -p "$work"

echo "gen-prelude: con-leche/$src_rel"

python3 "$root/scripts/gen-prelude.py" "$src" "$src_rel" "$CHUNK" \
  > "$work/prelude_text.rs"

lines=$(wc -l < "$src")
bytes=$(wc -c < "$src")

if [ "$check" -eq 1 ]; then
  if ! diff -u "$out" "$work/prelude_text.rs" > "$work/prelude_text.rs.diff" 2>&1; then
    echo "gen-prelude --check: frontend/prelude_text.rs differs from con-leche's prelude:" >&2
    sed -n '1,20p' "$work/prelude_text.rs.diff" >&2
    echo "gen-prelude --check: FAIL -- run scripts/gen-prelude.sh and commit the result" >&2
    exit 1
  fi
  echo "gen-prelude --check: OK (embedded text = $src_rel at the pinned commit, $lines records, $bytes bytes)"
else
  cp "$work/prelude_text.rs" "$out"
  echo "gen-prelude: wrote crates/con-ron-core/src/frontend/prelude_text.rs ($lines lines, $bytes bytes of text)"
fi
