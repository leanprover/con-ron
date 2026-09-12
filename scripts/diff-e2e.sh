#!/usr/bin/env bash
# THE END-TO-END DIFFERENTIAL (DESIGN.md task #37): `con-ron FILE.ndjson` on
# every fixture, against con-leche's pinned expectation.
#
#   usage: scripts/diff-e2e.sh [--trusted] [--verbose] [--timeout=SECS]
#                              [--only=REGEX] [--no-pins] [--progress]
#
# This is `scripts/diff-fixtures.sh` (task #28) one step further up: that
# script runs `con-ron-check` on the *dump* con-leche's frontend produced, so
# it tests the checker alone; this one runs the whole binary on the raw
# NDJSON, so it tests con-ron's own frontend AND checker together against
# `vendor/con-leche/tests/{arena,e2e,annot}-expected.txt`.  The expectation
# files' format is "<exit-code> <fixture>" with `#` comments -- the exit code
# is the WHOLE expectation, there is no declaration name and no fold position
# in them.
#
# Two things `diff-fixtures.sh` had to supply by hand are supplied by the
# frontend here, which is the point of the script:
#
#   * the TAINT-SKIP decline (`Main.lean:637-645,749-753`) -- an accepting
#     fold over a stream the frontend skipped declarations in is still a
#     decline.  `diff-fixtures.sh` names the three affected fixtures in a
#     `taint_of` table because the skip count is frontend state the dump does
#     not carry; con-ron's own frontend has it.
#   * the frontend's own verdicts: a stream con-leche's frontend declines or
#     rejects before the fold has no dump at all, so `diff-fixtures.sh`
#     SKIPS 33 fixtures.  Here they are checked like any other.
#
# `--pins` (on by default, `--no-pins` to drop it) is DESIGN.md §3.6's
# pin-list parameter, read from `$OUT/pins.dump` as `diff-fixtures.sh` reads
# it; without it the 17 fixtures that define `Nat.div` decline for an empty
# pin table.
#
# A fixture con-ron declines because it needs the IN-PROCESS MODELLER is
# reported `INMODEL` and counted separately (task #38).
#
# ONE fixture is expected to TIME OUT, and it is a finding rather than a flake:
# `e2e/tower_beqpair.ndjson` is exponential in `con-ron-core`'s `expr::beq`,
# whose pair memo is keyed on the two nodes' hash words (task #11's deviation)
# where con-leche keys it on their addresses.  DESIGN.md's task-#37 entry has
# the measurement and the options; until it is fixed, pass `--timeout=60` to
# keep the sweep short.
#
# A run is otherwise green when `differ` and `other` are both zero.
set -u
cd "$(dirname "$0")/.."
root="$PWD"

CL="$root/vendor/con-leche"
OUT="${OUT:-$root/_tmp/dump-fixtures}"
ARENA_DIR="${ARENA_DIR:-$root/_tmp/arena-tests}"
TO=600
MODE=--verified
verbose=0
only=""
use_pins=1
progress=""

for a in "$@"; do
  case "$a" in
    --trusted) MODE=--trusted ;;
    --verbose) verbose=1 ;;
    --no-pins) use_pins=0 ;;
    --progress) progress=--progress=1000 ;;
    --timeout=*) TO=${a#--timeout=} ;;
    --only=*) only=${a#--only=} ;;
    *) echo "usage: $0 [--trusted] [--verbose] [--no-pins] [--progress] [--timeout=SECS] [--only=REGEX]" >&2; exit 2 ;;
  esac
done

cargo build --release -p con-ron >"$root/_tmp/diff-e2e-build.log" 2>&1 || {
  echo "diff-e2e: cargo build failed, see _tmp/diff-e2e-build.log" >&2; exit 3; }
BIN="$root/target/release/con-ron"
[ -x "$BIN" ] || { echo "diff-e2e: $BIN is not executable" >&2; exit 3; }

if [ ! -d "$ARENA_DIR/good" ]; then
  echo "extracting the vendored arena snapshot to $ARENA_DIR" >&2
  mkdir -p "$ARENA_DIR"
  tar -xzf "$CL/tests/arena/lean-arena-tests.tar.gz" -C "$ARENA_DIR" || exit 3
fi

pinargs=""
if [ "$use_pins" -eq 1 ]; then
  if [ -f "$OUT/pins.dump" ]; then
    pinargs="--pins $OUT/pins.dump"
  else
    echo "diff-e2e: $OUT/pins.dump missing; run scripts/dump-fixtures.sh (or pass --no-pins)" >&2
    exit 3
  fi
fi

WORK="$root/_tmp/diff-e2e"
rm -rf "$WORK"; mkdir -p "$WORK"
log="${LOG:-$root/_tmp/diff-e2e.log}"
: >"$log"

total=0; agree=0; differ=0; inmodel=0; timedout=0; other=0

# `vendor/con-leche/tests/trusted-expected.txt` ("<exit> <suite> <fixture>")
# overrides the certified expectation under `--trusted`, as in
# `diff-fixtures.sh`.
want_for() {
  local suite=$1 fix=$2 cert=$3 line
  [ "$MODE" = --trusted ] || { echo "$cert"; return; }
  line=$(awk -v s="$suite" -v f="$fix" '
    /^#/ || /^[[:space:]]*$/ { next }
    $2 == s && $3 == f { print $1; exit }' "$CL/tests/trusted-expected.txt")
  if [ -n "$line" ]; then echo "$line"; else echo "$cert"; fi
}

one() { # one <suite> <label> <stream> <expected-exit>
  local suite=$1 label=$2 path=$3 want=$4
  if [ -n "$only" ] && ! printf '%s' "$suite/$label" | grep -qE "$only"; then return; fi
  total=$((total + 1))
  want=$(want_for "$suite" "$label" "$want")
  local out rc
  out=$(timeout "$TO" "$BIN" "$MODE" $pinargs $progress "$path" 2>&1); rc=$?
  printf '=== %s/%s (expect %s)\n%s\n  exit %s\n' "$suite" "$label" "$want" "$out" "$rc" >>"$log"
  if [ "$rc" = 124 ]; then
    timedout=$((timedout + 1)); echo "TIMEOUT $suite/$label (after ${TO}s, expected $want)"
  elif [ "$rc" = "$want" ]; then
    agree=$((agree + 1))
    [ "$verbose" -eq 1 ] && echo "ok      $suite/$label ($rc)"
  elif [ "$rc" = 2 ] && printf '%s' "$out" | grep -q "task #38"; then
    inmodel=$((inmodel + 1))
    echo "INMODEL $suite/$label: con-leche expects $want; the block needs the modeller"
  else
    differ=$((differ + 1))
    echo "DIFFER  $suite/$label: con-leche expects $want, con-ron got $rc"
    printf '%s' "$out" | head -2 | sed 's/^/          /'
  fi
}

t0=$(date +%s)

while read -r exp rel; do
  case "$exp" in ''|'#'*) continue;; esac
  [ -n "$rel" ] || continue
  one arena "$rel" "$ARENA_DIR/$rel" "$exp"
done <"$CL/tests/arena-expected.txt"

while read -r exp rel; do
  case "$exp" in ''|'#'*) continue;; esac
  [ -n "$rel" ] || continue
  src="$CL/tests/e2e/$rel"
  if [ ! -f "$src" ] && [ -f "$src.gz" ]; then
    src="$WORK/gunzipped-$(basename "$rel")"
    gunzip -c "$CL/tests/e2e/$rel.gz" >"$src" || { echo "GUNZIP FAIL $rel"; other=$((other+1)); continue; }
  fi
  one e2e "$rel" "$src" "$exp"
done <"$CL/tests/e2e-expected.txt"

while read -r exp rel; do
  case "$exp" in ''|'#'*) continue;; esac
  [ -n "$rel" ] || continue
  one annot "$rel" "$CL/tests/annot/$rel" "$exp"
done <"$CL/tests/annot-expected.txt"

t1=$(date +%s)
echo
echo "diff-e2e ($MODE${pinargs:+, with pins}): $total fixtures"
echo "  agree               $agree"
echo "  DIFFER              $differ"
echo "  needs the modeller  $inmodel   (task #38)"
echo "  timed out           $timedout"
echo "  other errors        $other"
echo "  $((t1 - t0))s; log: $log"
[ "$differ" -eq 0 ] && [ "$timedout" -eq 0 ] && [ "$other" -eq 0 ]
