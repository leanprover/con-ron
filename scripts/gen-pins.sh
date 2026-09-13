#!/usr/bin/env bash
# Regenerate the embedded `con-ron-pins/1` text of con-leche's `natOpPinSets`
# into `crates/con-ron-core/src/kernel/pins_text.rs` (DESIGN.md §3, task #43).
#
#   scripts/gen-pins.sh            rewrite the committed file in place
#   scripts/gen-pins.sh --check    regenerate into `_tmp/` and diff; non-zero
#                                  on any difference.  This is the freshness
#                                  rule "the embedded text is con-leche's own
#                                  `natOpPinSets` at the vendored tree's
#                                  commit" -- the pin analogue of
#                                  `scripts/extract.sh --check`.
#
# The source of truth is con-leche itself: `lake exe con-ron-dump-pins`
# (task #31) writes `ConLeche.natOpPinSets` in the format
# `proof/ConRon/Dump/FORMAT.md` §7 specifies, and this script wraps those
# bytes in a Rust `&str` constant.  The wrapping is byte-exact: the text of
# `PINS_TEXT` is the dump file, character for character, so
# `kernel::pins_decode::decode` on it is the same decode
# `con-ron-check --pins FILE` used to do on the file.
#
# Why a `&str` and not a `&[u8]` (task #43's measurement): Aeneas renders a
# `&str` constant as ONE Lean string literal (`toStr "..."`, 0.4 s, 560 KB of
# generated Lean) and a `b"..."` byte constant as a 532 456-element array
# literal (169 s in Aeneas, 4 MB of Lean, and Lean itself then dies of
# `std::bad_alloc` elaborating it).  The cost of the `&str` is one new
# external, `core::str::{str}::as_bytes`, modeled exactly in
# `proof/ConRon/Generated/FunsExternal.lean` (`Str := Slice U8`, so it is the
# identity).
set -euo pipefail

root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
out="$root/crates/con-ron-core/src/kernel/pins_text.rs"

check=0
case "${1-}" in
  "") ;;
  --check) check=1 ;;
  *) echo "usage: $0 [--check]" >&2; exit 2 ;;
esac
[ "$#" -le 1 ] || { echo "usage: $0 [--check]" >&2; exit 2; }

work="$root/_tmp/gen-pins"
rm -rf "$work"
mkdir -p "$work"

echo "gen-pins: lake exe con-ron-dump-pins (con-leche's natOpPinSets)"
( cd "$root/proof" && lake exe con-ron-dump-pins --no-roundtrip "$work/pins.dump" ) \
  | sed 's/^/  /'
[ -s "$work/pins.dump" ] || { echo "error: no pin dump written" >&2; exit 1; }

# The Rust source.  A multi-line string literal, one dump line per source
# line, so that a con-leche bump shows as a line diff and not as one 532 KB
# line.  Only `\` and `"` need escaping: every other byte of the format is a
# printable ASCII character, a space or the newline (FORMAT.md §3's escape is
# what makes that true), and the literal's value is therefore the dump's bytes
# exactly, including the final newline.
emit() {
  cat <<'EOF'
//! The embedded `con-ron-pins/1` text of con-leche's `natOpPinSets`
//! (DESIGN.md §3, task #43).
//!
//! con-leche: ConLeche/Kernel/NatOpPins.lean:62-65 _
//!
//! **Generated file — do not edit.**  Written by `scripts/gen-pins.sh` from
//! con-leche's own value: `lake exe con-ron-dump-pins` writes
//! `ConLeche.natOpPinSets` in the text format `proof/ConRon/Dump/FORMAT.md`
//! §7 specifies, and the script wraps those bytes in the constant below.
//! `scripts/gen-pins.sh --check` is the freshness gate, and
//! `scripts/gates.sh` runs it.
//!
//! The module-level citation above covers the one item in the file: the whole
//! module is one Lean declaration's value (DESIGN.md §3.7, the
//! `basis_tables.rs` rule of task #22).
//!
//! **Why the text and not generated Rust.**  `natOpPinSets` is a 26 512-node
//! `Expr` DAG; as generated constructor calls it is what task #22 measured
//! Charon OOM on, which is why task #31 made the pin list a *runtime*
//! parameter read from a file by the unverified driver.  A text constant
//! decoded by a *verified* decoder (`kernel::pins_decode`) puts the data back
//! inside the theorem's reach: the driver no longer supplies it, so the
//! statement of `check_decls_refines` no longer carries a hypothesis about
//! what the pins are.  Task #43's measurement of how far that reach actually
//! goes in the Lean kernel is in DESIGN.md.
//!
//! **Why `&str`.**  Aeneas renders a `&str` constant as one Lean string
//! literal and a `b"..."` byte constant as a 532 456-element array literal
//! that Lean cannot elaborate (task #43: `std::bad_alloc`).  The decoder
//! therefore takes `PINS_TEXT.as_bytes()`.

/// con-leche: ConLeche/Kernel/NatOpPins.lean:62-65 _
/// (The range is `#load_natop_pins`, the command that produces
/// `natOpPinSets` out of the committed `pins/*.json` while `NatOpPins.lean`
/// elaborates: the declaration has no source line of its own, hence `_`.)
/// The `con-ron-pins/1` dump of con-leche's `natOpPinSets`, verbatim: 3 `S`
/// records (one per pinned toolchain), the `N`/`L`/`W`/`E` records of the DAG
/// they share, and the `end <count>` footer.  `kernel::pins_decode::decode`
/// is the inverse.
pub const PINS_TEXT: &str = "\
EOF
  sed -e 's/\\/\\\\/g' -e 's/"/\\"/g' "$work/pins.dump"
  echo '";'
}

emit > "$work/pins_text.rs"
lines=$(wc -l < "$work/pins.dump")
bytes=$(wc -c < "$work/pins.dump")

if [ "$check" -eq 1 ]; then
  if ! diff -u "$out" "$work/pins_text.rs" > "$work/pins_text.rs.diff" 2>&1; then
    echo "gen-pins --check: kernel/pins_text.rs differs from con-leche's natOpPinSets:" >&2
    sed -n '1,20p' "$work/pins_text.rs.diff" >&2
    echo "gen-pins --check: FAIL -- run scripts/gen-pins.sh and commit the result" >&2
    exit 1
  fi
  echo "gen-pins --check: OK (embedded text = natOpPinSets at the vendored commit, $lines records, $bytes bytes)"
else
  cp "$work/pins_text.rs" "$out"
  echo "gen-pins: wrote crates/con-ron-core/src/kernel/pins_text.rs ($lines lines, $bytes bytes of text)"
fi
