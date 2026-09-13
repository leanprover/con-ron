#!/usr/bin/env bash
# Task #63, route A(2): a chunked-byte-constant crate through
# charon -> aeneas -> lean.  Usage: runchunked.sh <bytes> <chunk> [timeout]
set -u
R="$(cd "$(dirname "$0")/../.." && pwd)"   # the checkout this spike lives in
HERE="$(cd "$(dirname "$0")" && pwd)"
TOT="$1"; CK="$2"; TMO="${3:-1800}"
D=$R/_tmp/a63/ck-${TOT}-${CK}
rm -rf "$D"; mkdir -p "$D"
python3 "$HERE/genchunked.py" "$TOT" "$CK" "$D" || exit 1

t() { local s e; s=$(date +%s.%N); "$@" > "$D/$1.log" 2>&1; local rc=$?;
      e=$(date +%s.%N); echo "$rc $s $e"; }

echo "== charon"
S=$(date +%s.%N)
( cd "$D" && ulimit -v 30000000 && timeout "$TMO" charon cargo --preset=aeneas \
    --dest-file "$D/a63.llbc" ) > "$D/charon.log" 2>&1
RC1=$?; E=$(date +%s.%N)
python3 -c "import sys;print(f'charon rc=$RC1 wall={float('$E')-float('$S'):.1f}s')"
tail -3 "$D/charon.log"
ls -l "$D/a63.llbc" 2>/dev/null

echo "== aeneas"
mkdir -p "$D/lean"
S=$(date +%s.%N)
( ulimit -v 30000000 && timeout "$TMO" aeneas -backend lean -split-files \
    -loops-to-rec -dest "$D/lean" -subdir A63 -namespace A63 -no-progress-bar \
    "$D/a63.llbc" ) > "$D/aeneas.log" 2>&1
RC2=$?; E=$(date +%s.%N)
python3 -c "import sys;print(f'aeneas rc=$RC2 wall={float('$E')-float('$S'):.1f}s')"
tail -5 "$D/aeneas.log"
wc -l "$D"/lean/A63/*.lean 2>/dev/null
