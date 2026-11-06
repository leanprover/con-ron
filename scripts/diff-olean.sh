#!/usr/bin/env bash
# THE OLEAN DIFFERENTIAL (task #142): upstream's `tests/olean.sh` case table (109
# cases: exit codes and messages as pinned upstream, the verdicts pinned both ways
# included) against a binary that speaks con-leche's command line.
#
#   usage: scripts/diff-olean.sh [--lean] [--bin=PATH] [--cmp=PATH] [--upstream=PATH]
#                                [--compare] [--keep]
#
#   (default)      target/release/con-ron and target/release/olean-compare
#   --lean         proof/.lake/build/bin/con-ron-lean and con-ron-lean-olean-compare,
#                  each case's limit 900 s: seven cases check all of `Init`, minutes
#                  on the twin, where upstream's table allows 60 s
#   --upstream=P   also run con-leche's own binary P on the table and diff every
#                  case's verdict line against it (names of the binaries and the
#                  `t=` field normalised)
#   --compare      after the table, record for record against lean4export: `Init`
#                  whole and the cone of one `--constant` (upstream's
#                  tests/olean-compare.sh), by `_tmp/lean4export`'s exporter
#
# **Nothing of the shared con-leche checkout is written.**  The sources and the script
# are copied to `_tmp/diff-olean-<key>/`, where upstream's `tests/olean/build.sh`
# compiles the fixtures with the toolchain's own `lean`, and the table runs there with
# `lake build olean-compare` taken out.  Keyed by checkout, like every scratch.
set -u
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
ckey=$(printf '%s' "$root" | sha256sum | cut -c1-12)
W="$root/_tmp/diff-olean-$ckey"
BIN="$root/target/release/con-ron"
CMP="$root/target/release/olean-compare"
UP=""
COMPARE=0
KEEP=0
CASE_T=60
for a in "$@"; do
  case "$a" in
    --lean) BIN="$root/proof/.lake/build/bin/con-ron-lean"; CMP="$root/proof/.lake/build/bin/con-ron-lean-olean-compare"; CASE_T=900 ;;
    --bin=*) BIN="${a#--bin=}" ;;
    --cmp=*) CMP="${a#--cmp=}" ;;
    --upstream=*) UP="${a#--upstream=}" ;;
    --compare) COMPARE=1 ;;
    --keep) KEEP=1 ;;
    *) echo "usage: scripts/diff-olean.sh [--lean] [--bin=PATH] [--cmp=PATH] [--upstream=PATH] [--compare] [--keep]" >&2; exit 2 ;;
  esac
done
CL="$(python3 "$root/scripts/provenance.py" dir)"
[ -d "$CL/tests/olean/src" ] || { echo "diff-olean: no con-leche package ($CL)" >&2; exit 2; }
[ -x "$BIN" ] || { echo "diff-olean: no binary $BIN" >&2; exit 2; }

# The fixtures, once per pin: `build.sh` in a copy, with the toolchain of `proof/`.
PIN=$(python3 - "$root/proof/lake-manifest.json" <<'PY'
import json,sys
for p in json.load(open(sys.argv[1]))["packages"]:
    if p["name"].strip("«»") == "con-leche": print(p["rev"])
PY
)
if [ ! -f "$W/.pin" ] || [ "$(cat "$W/.pin")" != "$PIN" ]; then
  rm -rf "$W"; mkdir -p "$W/tests/mode" "$W/tmp"
  cp -r "$CL/tests/olean" "$W/tests/olean"
  cp "$CL/tests/olean.sh" "$W/tests/olean.sh"
  cp "$CL/tests/mode/split_good.ndjson" "$W/tests/mode/"
  cp "$root/proof/lean-toolchain" "$W/lean-toolchain"
  ( cd "$W" && bash tests/olean/build.sh > build.log 2>&1 ) || { echo "diff-olean: the fixtures' build failed, $W/build.log" >&2; exit 2; }
  # the table's own build of olean-compare is this script's: the tool is passed in
  sed -i -e 's/^lake build olean-compare >\/dev\/null || exit 3$/true/' \
    -e 's/timeout 60 "\$BIN"/timeout "${CASE_T:-60}" "$BIN"/' "$W/tests/olean.sh"
  echo "$PIN" > "$W/.pin"
fi

run() { # <bin> <cmp> <log>
  ( cd "$W" && OLEAN_VERBOSE=1 TMPDIR="$W/tmp" CASE_T="$4" BIN="$1" CMP="$2" timeout 7200 bash tests/olean.sh > "$3" 2>&1 )
}
LOG="$W/ours.log"
run "$BIN" "$CMP" "$LOG" "$CASE_T"; rc=$?
grep -E '^OLEAN FAIL|olean gate:' "$LOG" | cut -c1-200

if [ -n "$UP" ]; then
  UPC="$(dirname "$UP")/olean-compare"
  run "$UP" "$UPC" "$W/upstream.log" 60
  norm() { sed -E 's/con-(ron|ron-lean|leche): //; s/ t=[0-9.]+s$//; /^con-leche: stats:/d; /stats:/d' "$1"; }
  norm "$LOG" > "$W/ours.norm"; norm "$W/upstream.log" > "$W/upstream.norm"
  if cmp -s "$W/ours.norm" "$W/upstream.norm"; then
    echo "diff-olean: every verdict line agrees with upstream's"
  else
    n=$(diff "$W/ours.norm" "$W/upstream.norm" | grep -c '^[<>]')
    echo "diff-olean: $n lines differ from upstream's ($W/ours.norm, $W/upstream.norm)"
    diff "$W/ours.norm" "$W/upstream.norm" | head -60 | cut -c1-220
  fi
fi

if [ "$COMPARE" = 1 ] && [ -z "${BIN##*con-ron}" ]; then
  # the exporter at proof/'s toolchain: a copy of `_tmp/lean4export`, built once
  L4E="$W/lean4export/.lake/build/bin/lean4export"
  if [ ! -x "$L4E" ]; then
    mkdir -p "$W/lean4export"
    S="$root/_tmp/lean4export"
    cp -a "$S/Export" "$S/Export.lean" "$S/Main.lean" "$S/lakefile.toml" "$S/lake-manifest.json" "$W/lean4export/"
    cp "$root/proof/lean-toolchain" "$W/lean4export/lean-toolchain"
    ( cd "$W/lean4export" && timeout 600 lake build > build.log 2>&1 )
  fi
  if [ ! -x "$L4E" ]; then
    echo "diff-olean: no lean4export (from $root/_tmp/lean4export)" >&2; rc=3
  else
    TLIB="$(dirname "$(dirname "$(cd "$root/proof" && elan which lean)")")/lib/lean"
    LEAN_PATH="$TLIB" timeout 1200 "$L4E" Init > "$W/init.ndjson" || rc=3
    timeout 1200 "$CMP" "$W/init.ndjson" "$TLIB" Init > "$W/compare.txt" 2>&1; e=$?
    tail -1 "$W/compare.txt"
    [ $e = 0 ] || { head -40 "$W/compare.txt"; echo "OLEAN-COMPARE FAIL"; rc=1; }
    LEAN_PATH="$TLIB" timeout 600 "$L4E" Init -- Nat.add_comm > "$W/init.ndjson" || rc=3
    timeout 600 "$CMP" --constant=Nat.add_comm "$W/init.ndjson" "$TLIB" Init > "$W/compare.txt" 2>&1; e=$?
    tail -1 "$W/compare.txt"
    [ $e = 0 ] || { head -40 "$W/compare.txt"; echo "OLEAN-COMPARE FAIL (--constant)"; rc=1; }
    rm -f "$W/init.ndjson"
  fi
fi
[ "$KEEP" = 1 ] || rm -rf "$W/tmp"
exit $rc
