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
#   * `--corpus` adds `_tmp/corpus/{init,core}.ndjson` against their
#     `.decls` (task #29's scale corpus), which are not in the fixture
#     enumeration.  Give them room: `ulimit -v 2600000` for `init` and
#     `5000000` for `core`.
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
# Since task #39 the IN-PROCESS MODELLER is ported, so the dump of a mutual or
# nested block's stream contains its generated `_model` family and is compared
# like any other: the `INMODEL` row exists only to catch a regression that
# reintroduces the "not ported" decline, and is expected to read 0.  A
# generator DECLINE (`in-process model of <T>: <why>`) counts as `other` and
# reddens the run, which is what makes the 26 modeller fixtures a gate.
#
# A run is green when `differ`, `other` and `timed out` are all zero.
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
      if printf '%s' "$out" | grep -q "the in-process modeller is not ported"; then
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

# `_tmp/corpus/{init,core}.ndjson` (task #29), which are not fixtures.  `Init`
# declares `Lean.Syntax` and `Init+Std+Lean` 45 mutual/nested blocks, so
# con-leche's own dumps have those blocks' generated `_model` families in them:
# these two rows are the modeller's scale gate (task #39).
if [ "$corpus" -eq 1 ]; then
  for c in init core; do
    if [ -f "$CORPUS/$c.ndjson" ] && [ -f "$CORPUS/$c.decls" ]; then
      mkdir -p "$OUT/corpus"
      cp -n "$CORPUS/$c.decls" "$OUT/corpus/$c.ndjson.decls" 2>/dev/null || true
      one corpus "$c.ndjson" "$CORPUS/$c.ndjson"
    else
      echo "diff-frontend: no $CORPUS/$c.{ndjson,decls}; run scripts/corpus.sh" >&2
    fi
  done
fi

t1=$(date +%s)
echo
echo "diff-frontend: $total fixtures"
echo "  byte-identical      $same"
echo "  DIFFER              $differ"
echo "  needs the modeller  $inmodel   (task #39 ported it; expected 0)"
echo "  no Lean dump        $skipped   (con-leche's frontend declined or rejected them)"
echo "  timed out           $timedout"
echo "  other errors        $other"
echo "  total bytes compared $bytes, $((t1 - t0))s"
echo "  log: $log"
[ "$differ" -eq 0 ] && [ "$other" -eq 0 ] && [ "$timedout" -eq 0 ]
