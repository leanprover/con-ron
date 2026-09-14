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
#                                     vendored tree's commit".
#
# The source of truth is con-leche's own committed file, the one its
# `builtinPreludeText` reads with `include_str`:
#
#   vendor/con-leche/pins/<toolchain>.prelude.ndjson
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
# The wrapping is byte-exact: the value of `PRELUDE_TEXT` is the ndjson file,
# byte for byte, including its final newline, so `parse_chunks` on it is the
# parse `con-ron` would do on that file.  Aeneas models a `&str` as
# `Slice U8` with `toStr s = s.toByteArray` (`Aeneas/Std/String.lean`), i.e.
# the UTF-8 bytes, so the two non-ASCII lines of the prelude (`α`, `β`) are
# the bytes the scanner reads and the model reads the same ones.
set -euo pipefail

root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
out="$root/crates/con-ron-core/src/frontend/prelude_text.rs"

check=0
case "${1-}" in
  "") ;;
  --check) check=1 ;;
  *) echo "usage: $0 [--check]" >&2; exit 2 ;;
esac
[ "$#" -le 1 ] || { echo "usage: $0 [--check]" >&2; exit 2; }

# The toolchain the vendored con-leche pins, which names the prelude file:
# `Frontend/Prelude.lean`'s `include_str` path is the authority, so read it
# from there rather than guessing.
src_rel=$(sed -n 's|.*include_str "\.\./\.\./\(pins/[^"]*\)".*|\1|p' \
  "$root/vendor/con-leche/ConLeche/Frontend/Prelude.lean" | head -1)
[ -n "$src_rel" ] || {
  echo "error: could not read the include_str path out of con-leche's Frontend/Prelude.lean" >&2
  exit 1; }
src="$root/vendor/con-leche/$src_rel"
[ -s "$src" ] || { echo "error: $src is missing or empty" >&2; exit 1; }

work="$root/_tmp/gen-prelude"
rm -rf "$work"
mkdir -p "$work"

echo "gen-prelude: vendor/con-leche/$src_rel"

emit() {
  cat <<EOF
//! The embedded lean4export text of con-leche's built-in prelude
//! (\`ConLeche/Frontend/Prelude.lean:57-62\`, task #84).
//!
//! con-leche: ConLeche/Frontend/Prelude.lean:57-62 builtinPreludeText
//!
//! **Generated file — do not edit.**  Written by \`scripts/gen-prelude.sh\`
//! from con-leche's own committed \`$src_rel\`, the file its
//! \`builtinPreludeText\` reads with \`include_str\`.
//! \`scripts/gen-prelude.sh --check\` is the freshness gate, and
//! \`scripts/gates.sh\` runs it.
//!
//! The module-level citation above covers the one item in the file: the whole
//! module is one Lean declaration's value (DESIGN.md §3.7, the
//! \`basis_tables.rs\` rule of task #22, as \`kernel/pins_text.rs\` does).
//!
//! **Why a constant in the crate and not \`include_str!\`.**  The unverified
//! port read the file out of \`vendor/\` at compile time, which makes the
//! verified crate's build depend on a path outside itself and hides the data
//! from anyone reading \`crates/con-ron-core\`.  \`kernel/pins_text.rs\`
//! settled that question at task #43; this follows it.
//!
//! **Why \`&str\`.**  Aeneas renders a \`&str\` constant as one Lean string
//! literal and a \`b"..."\` byte constant as an element-by-element array
//! literal that Lean cannot elaborate at size (task #43).
//! \`frontend::prelude::builtin_prelude_e\` therefore takes
//! \`PRELUDE_TEXT.as_bytes()\`; \`Str\` is \`Slice U8\` and \`toStr\` is the
//! string's UTF-8 bytes, so the model reads exactly the bytes the binary does.

/// con-leche: ConLeche/Frontend/Prelude.lean:57-62 builtinPreludeText
/// The committed prelude for the pinned toolchain (con-leche's
/// \`lean-toolchain\`), verbatim: the \`meta\` header, the name, level and
/// expression table entries, and the declaration records of the six pinned
/// basis blocks, \`Bool\` and \`And\`.  \`frontend::prelude::builtin_prelude_e\`
/// is the parse of it.
pub const PRELUDE_TEXT: &str = "\\
EOF
  sed -e 's/\\/\\\\/g' -e 's/"/\\"/g' "$src"
  echo '";'
}

emit > "$work/prelude_text.rs"
lines=$(wc -l < "$src")
bytes=$(wc -c < "$src")

if [ "$check" -eq 1 ]; then
  if ! diff -u "$out" "$work/prelude_text.rs" > "$work/prelude_text.rs.diff" 2>&1; then
    echo "gen-prelude --check: frontend/prelude_text.rs differs from con-leche's prelude:" >&2
    sed -n '1,20p' "$work/prelude_text.rs.diff" >&2
    echo "gen-prelude --check: FAIL -- run scripts/gen-prelude.sh and commit the result" >&2
    exit 1
  fi
  echo "gen-prelude --check: OK (embedded text = $src_rel at the vendored commit, $lines records, $bytes bytes)"
else
  cp "$work/prelude_text.rs" "$out"
  echo "gen-prelude: wrote crates/con-ron-core/src/frontend/prelude_text.rs ($lines lines, $bytes bytes of text)"
fi
