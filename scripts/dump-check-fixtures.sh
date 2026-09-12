#!/usr/bin/env bash
# Run the RUST reader (`con-ron-dump-check`, task #19) over every
# `con-ron-decls/1` dump that `scripts/dump-fixtures.sh` produced -- the other
# half of DESIGN.md §3.6's seam: the Lean side writes and validates the dumps,
# this says the Rust side reads them.
#
#   scripts/dump-check-fixtures.sh                  parse + byte-exact re-dump
#   scripts/dump-check-fixtures.sh --no-roundtrip   parse only
#   scripts/dump-check-fixtures.sh --verbose        one line per fixture
#
# Every dump must parse, and -- unless `--no-roundtrip` -- the crate's own
# writer must reproduce the input byte for byte, which pins every id, every
# list length, every escape and the whole emission order to
# `proof/ConRon/Dump/Write.lean`.  Non-zero exit on any failure.
#
# The dumps come from `scripts/dump-fixtures.sh` (task #10), which needs the
# Lean build:
#
#   scripts/setup-aeneas-lean.sh && (cd proof && lake build con-ron-dump)
#   scripts/dump-fixtures.sh --no-check
#
# If $OUT holds no dump yet, this script runs that sweep itself.
set -uo pipefail
cd "$(dirname "$0")/.."
root="$PWD"

OUT="${OUT:-$root/_tmp/dump-fixtures}"
BIN="$root/target/release/con-ron-dump-check"
FLAGS=(--roundtrip --quiet)
TO="${TO:-600}"

for a in "$@"; do
  case "$a" in
    --no-roundtrip) FLAGS=(--quiet);;
    --verbose) FLAGS=("${FLAGS[@]/--quiet/}");;
    *) echo "usage: $0 [--no-roundtrip] [--verbose]" >&2; exit 2;;
  esac
done

echo "building con-ron-dump-check (release)"
cargo build --release -p con-ron-dump || exit 2
[ -x "$BIN" ] || { echo "error: $BIN missing" >&2; exit 2; }

mapfile -t files < <(find "$OUT" -name '*.decls' 2>/dev/null | sort)
if [ "${#files[@]}" -eq 0 ]; then
  echo "no dumps under $OUT -- running scripts/dump-fixtures.sh --no-check" >&2
  "$root/scripts/dump-fixtures.sh" --no-check || true
  mapfile -t files < <(find "$OUT" -name '*.decls' 2>/dev/null | sort)
fi
[ "${#files[@]}" -gt 0 ] || {
  echo "error: still no dumps under $OUT (build proof/ first; see the header)" >&2
  exit 2; }

echo "reading ${#files[@]} dumps with the Rust reader"
timeout "$TO" "$BIN" "${FLAGS[@]}" "${files[@]}"
rc=$?
if [ "$rc" = 124 ]; then
  echo "dump-check-fixtures: TIMEOUT after ${TO}s" >&2
elif [ "$rc" = 0 ]; then
  echo "dump-check-fixtures: OK"
else
  echo "dump-check-fixtures: FAIL (exit $rc)" >&2
fi
exit $rc
