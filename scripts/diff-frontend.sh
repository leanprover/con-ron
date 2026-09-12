#!/usr/bin/env bash
# THE FRONTEND ORACLE (DESIGN.md task #37).  For every fixture con-leche's own
# frontend produced a `con-ron-decls/1` dump for, `con-ron --dump-decls` must
# produce the SAME BYTES.
#
#   usage: scripts/diff-frontend.sh [--verbose] [--timeout=SECS] [--only=REGEX]
#                                   [--corpus]
#
# Inputs
#   * the Lean dumps `scripts/dump-fixtures.sh` wrote (task #10), under `$OUT`
#     (default `_tmp/dump-fixtures/{arena,e2e,annot}/<label with / as _>.decls`)
#     -- each is `dumpDecls` of the `List DeclC` con-leche's frontend parsed,
#     with the built-in prelude prepended, the Nat-op ground hoisted, the
#     projection functions rewritten and the in-process models spliced in;
#   * the fixtures themselves, enumerated exactly as `dump-fixtures.sh`
#     enumerates them: from `vendor/con-leche/tests/{arena,e2e,annot}
#     -expected.txt`, with the gzipped e2e streams gunzipped and the arena
#     tarball extracted to `$ARENA_DIR`;
#   * `--corpus` adds `_tmp/corpus/init.ndjson` against `_tmp/corpus/init.decls`
#     (task #29's scale corpus), which is not in the fixture enumeration.
#
# Byte identity is the whole test.  It is a strong one: the dump's nine id
# spaces are dense and assigned in the writer's own walk order, so a single
# divergence anywhere -- one interning decision, one binder's `pw`, one
# `IndCaps` default, one hoist tie-break, one prelude dedupe -- moves every
# later id and the files differ from that point on.
#
# A fixture whose Lean dump does not exist is SKIPPED: those are the 33
# streams con-leche's own frontend declines or rejects before the fold (task
# #10), so there is no declaration list to compare.
#
# A fixture con-ron declines because it needs the IN-PROCESS MODELLER is
# reported as `INMODEL` and counted separately: the modeller is task #38, and
# `frontend::export_c` declines at exactly the point con-leche calls it.
#
# ONE fixture is expected to TIME OUT, and it is a finding rather than a flake:
# `e2e/tower_beqpair.ndjson` is exponential in `con-ron-core`'s `expr::beq`,
# whose pair memo is keyed on the two nodes' hash words (task #11's deviation)
# where con-leche keys it on their addresses.  DESIGN.md's task-#37 entry has
# the measurement and the options; until it is fixed, pass `--timeout=40` to
# keep the sweep short.
#
# A run is otherwise green when `differ` and `other` are both zero.
set -u
cd "$(dirname "$0")/.."
root="$PWD"

CL="$root/vendor/con-leche"
OUT="${OUT:-$root/_tmp/dump-fixtures}"
ARENA_DIR="${ARENA_DIR:-$root/_tmp/arena-tests}"
CORPUS="${CORPUS:-$root/_tmp/corpus}"
TO=600
verbose=0
only=""
corpus=0

for a in "$@"; do
  case "$a" in
    --verbose) verbose=1 ;;
    --corpus) corpus=1 ;;
    --timeout=*) TO=${a#--timeout=} ;;
    --only=*) only=${a#--only=} ;;
    *) echo "usage: $0 [--verbose] [--corpus] [--timeout=SECS] [--only=REGEX]" >&2; exit 2 ;;
  esac
done

cargo build --release -p con-ron >"$root/_tmp/diff-frontend-build.log" 2>&1 || {
  echo "diff-frontend: cargo build failed, see _tmp/diff-frontend-build.log" >&2; exit 3; }
BIN="$root/target/release/con-ron"
[ -x "$BIN" ] || { echo "diff-frontend: $BIN is not executable" >&2; exit 3; }

if [ ! -d "$OUT" ] || [ -z "$(find "$OUT" -name '*.decls' -print -quit 2>/dev/null)" ]; then
  echo "diff-frontend: no Lean dumps under $OUT; run scripts/dump-fixtures.sh --no-check" >&2
  exit 3
fi
if [ ! -d "$ARENA_DIR/good" ]; then
  echo "extracting the vendored arena snapshot to $ARENA_DIR" >&2
  mkdir -p "$ARENA_DIR"
  tar -xzf "$CL/tests/arena/lean-arena-tests.tar.gz" -C "$ARENA_DIR" || exit 3
fi

WORK="$root/_tmp/diff-frontend"
rm -rf "$WORK"; mkdir -p "$WORK"
log="${LOG:-$root/_tmp/diff-frontend.log}"
: >"$log"

total=0; same=0; differ=0; skipped=0; inmodel=0; other=0; timedout=0
bytes=0

one() { # one <suite> <label> <stream-path>
  local suite=$1 label=$2 path=$3
  if [ -n "$only" ] && ! printf '%s' "$suite/$label" | grep -qE "$only"; then return; fi
  local flat want got rc out
  flat=$(printf '%s' "$label" | tr '/' '_')
  want="$OUT/$suite/$flat.decls"
  total=$((total + 1))
  if [ ! -f "$want" ]; then
    skipped=$((skipped + 1))
    [ "$verbose" -eq 1 ] && echo "SKIP   $suite/$label (no Lean dump: the frontend declined or rejected it)"
    echo "SKIP $suite/$label" >>"$log"
    return
  fi
  got="$WORK/$suite-$flat.decls"
  mkdir -p "$(dirname "$got")"
  out=$(timeout "$TO" "$BIN" --dump-decls "$got" "$path" 2>&1); rc=$?
  printf '=== %s/%s\n%s\n  exit %s\n' "$suite" "$label" "$out" "$rc" >>"$log"
  case $rc in
    0)
      if cmp -s "$got" "$want"; then
        same=$((same + 1))
        bytes=$((bytes + $(stat -c %s "$got")))
        [ "$verbose" -eq 1 ] && echo "ok     $suite/$label ($(stat -c %s "$got") bytes)"
      else
        differ=$((differ + 1))
        echo "DIFFER $suite/$label: $(stat -c %s "$got") bytes vs $(stat -c %s "$want") expected"
        cmp "$got" "$want" 2>&1 | sed 's/^/         /' | head -2
      fi
      ;;
    2)
      if printf '%s' "$out" | grep -q "task #38"; then
        inmodel=$((inmodel + 1))
        echo "INMODEL $suite/$label: $(printf '%s' "$out" | head -1)"
      else
        other=$((other + 1))
        echo "DECLINE $suite/$label: $(printf '%s' "$out" | head -1)"
      fi
      ;;
    124) timedout=$((timedout + 1)); echo "TIMEOUT $suite/$label" ;;
    *) other=$((other + 1)); echo "ERROR($rc) $suite/$label: $(printf '%s' "$out" | head -1)" ;;
  esac
}

t0=$(date +%s)

while read -r exp rel; do
  case "$exp" in ''|'#'*) continue;; esac
  [ -n "$rel" ] || continue
  one arena "$rel" "$ARENA_DIR/$rel"
done <"$CL/tests/arena-expected.txt"

while read -r exp rel; do
  case "$exp" in ''|'#'*) continue;; esac
  [ -n "$rel" ] || continue
  src="$CL/tests/e2e/$rel"
  if [ ! -f "$src" ] && [ -f "$src.gz" ]; then
    src="$WORK/gunzipped-$(basename "$rel")"
    gunzip -c "$CL/tests/e2e/$rel.gz" >"$src" || { echo "GUNZIP FAIL $rel"; other=$((other+1)); continue; }
  fi
  one e2e "$rel" "$src"
done <"$CL/tests/e2e-expected.txt"

while read -r exp rel; do
  case "$exp" in ''|'#'*) continue;; esac
  [ -n "$rel" ] || continue
  one annot "$rel" "$CL/tests/annot/$rel"
done <"$CL/tests/annot-expected.txt"

# `_tmp/corpus/init.ndjson` (task #29), which is not a fixture.  `Init`
# declares `Lean.Syntax`, a NESTED block, so con-leche's own dump has that
# block's generated `_model` family in it and con-ron declines the stream:
# the row is reported INMODEL until task #38.
if [ "$corpus" -eq 1 ]; then
  if [ -f "$CORPUS/init.ndjson" ] && [ -f "$CORPUS/init.decls" ]; then
    mkdir -p "$OUT/corpus"
    cp -n "$CORPUS/init.decls" "$OUT/corpus/init.ndjson.decls" 2>/dev/null || true
    one corpus "init.ndjson" "$CORPUS/init.ndjson"
  else
    echo "diff-frontend: no $CORPUS/init.{ndjson,decls}; run scripts/corpus.sh" >&2
  fi
fi

t1=$(date +%s)
echo
echo "diff-frontend: $total fixtures"
echo "  byte-identical      $same"
echo "  DIFFER              $differ"
echo "  needs the modeller  $inmodel   (task #38; declined at the parse)"
echo "  no Lean dump        $skipped   (con-leche's frontend declined or rejected them)"
echo "  timed out           $timedout"
echo "  other errors        $other"
echo "  total bytes compared $bytes, $((t1 - t0))s"
echo "  log: $log"
[ "$differ" -eq 0 ] && [ "$other" -eq 0 ] && [ "$timedout" -eq 0 ]
