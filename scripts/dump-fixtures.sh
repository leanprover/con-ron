#!/usr/bin/env bash
# Run `lake exe con-ron-dump` (DESIGN.md §3.6, task #10) over con-leche's whole
# fixture corpus and report, per fixture:
#
#   * whether the `con-ron-decls/1` round trip is exact (structural equality of
#     the `List DeclC`, byte-identity of a re-dump, and the same verdict from
#     `checkDecls .verified` on both lists) -- the tool's own exit code, and
#   * whether the verdict agrees with con-leche's pinned expectation in
#     tests/{arena,e2e,annot}-expected.txt (the tool prints `verdict-exit <n>`
#     using con-leche's own exit-code mapping).
#
# Fixtures are enumerated exactly as vendor/con-leche/tests/arena.sh does:
# from the three expectation files, with the gzipped e2e streams gunzipped to
# scratch and the arena tarball extracted to $ARENA_DIR.
#
# It also writes, ONCE, the `Nat`-operation pin dump `$OUT/pins.dump`
# (`lake exe con-ron-dump-pins`, task #31): the pin variants are per toolchain,
# not per stream, so one file serves the whole corpus and
# `scripts/diff-fixtures.sh` hands it to every `con-ron-check` run with
# `--pins`.  Without it 17 fixtures decline for the empty pin table.
#
# A frontend DECLINE or INVALID is reported, never hidden: those fixtures get
# no round trip (there is no declaration list) and are counted separately.
#
# Usage: scripts/dump-fixtures.sh [--no-check] [--timeout SECS]
#   --no-check   skip the two `checkDecls` runs (round trip only, much faster)
set -u
cd "$(dirname "$0")/.."
root="$PWD"

CL="$root/vendor/con-leche"
BIN="$root/proof/.lake/build/bin/con-ron-dump"
PINBIN="$root/proof/.lake/build/bin/con-ron-dump-pins"
OUT="${OUT:-$root/_tmp/dump-fixtures}"
ARENA_DIR="${ARENA_DIR:-$root/_tmp/arena-tests}"
TO=600
EXTRA=""

for a in "$@"; do
  case "$a" in
    --no-check) EXTRA="--no-check";;
    --timeout=*) TO="${a#--timeout=}";;
    *) echo "usage: $0 [--no-check] [--timeout=SECS]" >&2; exit 2;;
  esac
done

[ -x "$BIN" ] || { echo "error: $BIN missing (cd proof && lake build con-ron-dump)" >&2; exit 2; }
[ -x "$PINBIN" ] || { echo "error: $PINBIN missing (cd proof && lake build con-ron-dump-pins)" >&2; exit 2; }
mkdir -p "$OUT"

# The pin dump, once for the whole corpus (task #31).  Its own round trip is
# checked by the tool; a failure here is fatal, because every verdict below
# would then be taken against the wrong pin list.
pins_rc=0
timeout "$TO" "$PINBIN" "$OUT/pins.dump" || pins_rc=$?
[ "$pins_rc" = 0 ] || { echo "error: con-ron-dump-pins failed (exit $pins_rc)" >&2; exit 2; }

if [ ! -d "$ARENA_DIR/good" ]; then
  echo "extracting the vendored arena snapshot to $ARENA_DIR" >&2
  mkdir -p "$ARENA_DIR"
  tar -xzf "$CL/tests/arena/lean-arena-tests.tar.gz" -C "$ARENA_DIR" || exit 2
fi

pass=0 fail=0 declined=0 invalid=0 parseerr=0 timedout=0 other=0
vmatch=0 vdiff=0
bytes_total=0
log="$OUT/run.log"
: > "$log"

run_one() { # <suite> <label> <path> <expected-exit>
  local suite=$1 label=$2 path=$3 want=$4
  local dest="$OUT/$suite/$(echo "$label" | tr '/' '_').decls"
  mkdir -p "$(dirname "$dest")"
  local o rc
  o=$(timeout "$TO" "$BIN" $EXTRA "$path" "$dest" 2>&1)
  rc=$?
  printf '=== %s %s (expected exit %s)\n%s\n' "$suite" "$label" "$want" "$o" >> "$log"
  case $rc in
    0) pass=$((pass+1));;
    1) fail=$((fail+1)); echo "ROUND-TRIP FAIL $suite/$label";;
    2) if printf '%s' "$o" | grep -q DECLINED; then
         declined=$((declined+1))
       else
         invalid=$((invalid+1))
       fi;;
    3) if printf '%s' "$o" | grep -q "PARSE ERROR"; then
         parseerr=$((parseerr+1))
       else
         other=$((other+1)); echo "ERROR(3) $suite/$label"
       fi;;
    124) timedout=$((timedout+1)); echo "TIMEOUT $suite/$label";;
    *) other=$((other+1)); echo "ERROR($rc) $suite/$label";;
  esac
  local got
  got=$(printf '%s' "$o" | sed -n 's/^  verdict-exit \([0-9]*\)$/\1/p')
  if [ -n "$got" ]; then
    if [ "$got" = "$want" ]; then vmatch=$((vmatch+1))
    else vdiff=$((vdiff+1)); echo "VERDICT $suite/$label: con-leche expects $want, dump tool got $got"; fi
  fi
  if [ -f "$dest" ]; then
    bytes_total=$((bytes_total + $(stat -c %s "$dest")))
  fi
}

# --- arena ----------------------------------------------------------
while read -r exp rel; do
  case "$exp" in ''|'#'*) continue;; esac
  run_one arena "$rel" "$ARENA_DIR/$rel" "$exp"
done < "$CL/tests/arena-expected.txt"

# --- e2e ------------------------------------------------------------
while read -r exp rel; do
  case "$exp" in ''|'#'*) continue;; esac
  src="$CL/tests/e2e/$rel"
  if [ ! -f "$src" ] && [ -f "$src.gz" ]; then
    tmpf="$OUT/gunzipped-$(basename "$rel")"
    gunzip -c "$src.gz" > "$tmpf" || { echo "GUNZIP FAIL $rel"; other=$((other+1)); continue; }
    src="$tmpf"
  fi
  run_one e2e "$rel" "$src" "$exp"
done < "$CL/tests/e2e-expected.txt"

# --- annot ----------------------------------------------------------
while read -r exp rel; do
  case "$exp" in ''|'#'*) continue;; esac
  run_one annot "$rel" "$CL/tests/annot/$rel" "$exp"
done < "$CL/tests/annot-expected.txt"

total=$((pass+fail+declined+invalid+parseerr+timedout+other))
echo
echo "fixtures            $total"
echo "  round trip exact  $pass"
echo "  round trip FAILED $fail"
echo "  frontend declined $declined   (no declaration list; nothing to dump)"
echo "  frontend invalid  $invalid"
echo "  frontend parse er $parseerr"
echo "  timed out         $timedout"
echo "  other errors      $other"
echo "verdict vs tests/*-expected.txt: $vmatch agree, $vdiff differ"
echo "total dump bytes    $bytes_total"
echo "log                 $log"
[ "$fail" = 0 ] && [ "$timedout" = 0 ] && [ "$other" = 0 ] && [ "$vdiff" = 0 ]
