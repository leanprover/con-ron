#!/usr/bin/env bash
# The differential run (DESIGN.md §3.6, task #28): con-ron's verdict on every
# fixture dump against con-leche's pinned expectation.
#
#   usage: scripts/diff-fixtures.sh [--trusted] [--verbose] [--stats]
#                                   [--timeout=SECS] [--only=REGEX]
#
# Inputs
#   * the dumps `scripts/dump-fixtures.sh` wrote (task #10), one per fixture
#     that con-leche's frontend parsed, under `$OUT` (default
#     `_tmp/dump-fixtures/{arena,e2e,annot}/<label with / as _>.decls`);
#   * con-leche's expectation files `vendor/con-leche/tests/{arena,e2e,annot}
#     -expected.txt`, whose line format is "<exit-code> <fixture>" with `#`
#     comments — the exit code is the WHOLE expectation, there is no
#     declaration name and no fold position in them (so the position
#     `con-ron-check` prints is compared against nothing here);
#   * `vendor/con-leche/tests/trusted-expected.txt` ("<exit> <suite>
#     <fixture>"), the `--trusted` overrides, read only for `--trusted`.
#
# For each expectation line the dump is run through `con-ron-check` and the
# exit code compared.  A fixture with no dump is SKIPPED with a note: those
# are the 33 streams con-leche's own frontend declines or rejects before the
# fold (task #10), so there is no declaration list to check and nothing about
# the port is being tested.
#
# One driver rule of `vendor/con-leche/Main.lean` lives here rather than in
# the core, because its datum is frontend state the dump does not carry:
#
#   * the TAINT-SKIP decline (`Main.lean:637-645,749-753`): an accepting fold
#     over a stream the frontend skipped declarations in, for a tolerated
#     axiom, is still a decline.  `res.taintSkipped.size` is not in the dump
#     (task #10's surprise 9), so the three fixtures that have skips are
#     named in `taint_of` below and run with `--taint-skipped`.
#
# This script is deliberately NOT in `scripts/gates.sh`: it needs the Lean
# build and the arena tarball, the same reason `dump-check-fixtures.sh` is
# not (task #19).
set -u
cd "$(dirname "$0")/.."
root=$PWD

OUT="${OUT:-$root/_tmp/dump-fixtures}"
TO=600
MODE=--verified

verbose=0
stats=0
only=""
for a in "$@"; do
  case "$a" in
    --trusted) MODE=--trusted ;;
    --verbose) verbose=1 ;;
    --stats) stats=1 ;;
    --timeout=*) TO=${a#--timeout=} ;;
    --only=*) only=${a#--only=} ;;
    *) echo "usage: scripts/diff-fixtures.sh [--trusted] [--verbose] [--stats] [--timeout=SECS] [--only=REGEX]" >&2; exit 2 ;;
  esac
done

# The streams whose frontend skipped declarations for a tolerated axiom, and
# the skip count con-leche reports for each.  Their verdict is 2 by the driver
# rule above even though the fold accepts; task #10's surprise 9 pinned the
# same three.  `tolerated_axiom_use` and `taint_skip_continue` really do
# depend on the rule here; `sorry_use` declines earlier, in the fold, for the
# empty Nat-operation pin table.
taint_of() { # taint_of <fixture>
  case "$1" in
    sorry_use.ndjson|tolerated_axiom_use.ndjson|taint_skip_continue.ndjson) echo 1 ;;
    *) echo 0 ;;
  esac
}

cargo build --release -p con-ron-dump >"$root/_tmp/diff-fixtures-build.log" 2>&1 || {
  echo "diff-fixtures: cargo build failed, see _tmp/diff-fixtures-build.log" >&2; exit 3; }
BIN="$root/target/release/con-ron-check"
[ -x "$BIN" ] || { echo "diff-fixtures: $BIN is not executable" >&2; exit 3; }

if [ ! -d "$OUT" ] || [ -z "$(find "$OUT" -name '*.decls' -print -quit 2>/dev/null)" ]; then
  echo "diff-fixtures: no dumps under $OUT; running scripts/dump-fixtures.sh --no-check" >&2
  "$root/scripts/dump-fixtures.sh" --no-check || {
    echo "diff-fixtures: dump-fixtures.sh failed" >&2; exit 3; }
fi

log="$root/_tmp/diff-fixtures.log"
: >"$log"

total=0; agree=0; differ=0; skipped=0; timedout=0

# want_for <suite> <fixture> <certified-code> — the trusted sweep's override
# if there is one, else the certified expectation.
want_for() {
  local suite=$1 fix=$2 cert=$3 line
  [ "$MODE" = --trusted ] || { echo "$cert"; return; }
  line=$(awk -v s="$suite" -v f="$fix" '
    /^#/ || /^[[:space:]]*$/ { next }
    $2 == s && $3 == f { print $1; exit }' vendor/con-leche/tests/trusted-expected.txt)
  if [ -n "$line" ]; then echo "$line"; else echo "$cert"; fi
}

run_suite() { # run_suite <suite> <expected-file>
  local suite=$1 exp=$2 want fix dump got taint label
  while read -r want fix; do
    case "$want" in ''|'#'*) continue;; esac
    [ -n "$fix" ] || continue
    if [ -n "$only" ] && ! printf '%s' "$suite/$fix" | grep -qE "$only"; then continue; fi
    total=$((total + 1))
    label=$(printf '%s' "$fix" | tr '/' '_')
    dump="$OUT/$suite/$label.decls"
    want=$(want_for "$suite" "$fix" "$want")
    if [ ! -f "$dump" ]; then
      skipped=$((skipped + 1))
      [ "$verbose" -eq 1 ] && echo "SKIP $suite/$fix (no declaration list: the frontend declined or rejected it)"
      echo "SKIP $suite/$fix" >>"$log"
      continue
    fi
    # The taint-skip driver rule: the count is frontend state, not in the dump.
    taint=$(taint_of "$fix")
    {
      echo "=== $suite/$fix (expect $want)"
      timeout "$TO" "$BIN" "$MODE" --taint-skipped "$taint" \
        $( [ "$stats" -eq 1 ] && echo --stats ) "$dump"
      echo "  exit $?"
    } >>"$log" 2>&1
    got=$(tail -n 20 "$log" | sed -n 's/^  exit \([0-9]*\)$/\1/p' | tail -1)
    if [ "$got" = 124 ]; then
      timedout=$((timedout + 1))
      echo "TIMEOUT $suite/$fix (after ${TO}s, expected $want)"
    elif [ "$got" = "$want" ]; then
      agree=$((agree + 1))
      [ "$verbose" -eq 1 ] && echo "ok   $suite/$fix ($got)"
    else
      differ=$((differ + 1))
      echo "DIFFER $suite/$fix: con-leche expects $want, con-ron got $got"
      grep -A 3 "^=== $suite/$fix (expect" "$log" | sed -n '2,3p' | sed 's/^/         /'
    fi
  done <"$exp"
}

t0=$(date +%s)
run_suite arena vendor/con-leche/tests/arena-expected.txt
run_suite e2e vendor/con-leche/tests/e2e-expected.txt
run_suite annot vendor/con-leche/tests/annot-expected.txt
t1=$(date +%s)

echo "diff-fixtures ($MODE): $total fixtures, $agree agree, $differ differ, $skipped skipped (no declaration list), $timedout timed out, $((t1 - t0))s"
echo "  log: $log"
[ "$differ" -eq 0 ] && [ "$timedout" -eq 0 ]
