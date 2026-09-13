#!/usr/bin/env bash
# Task #63 route A: charon + aeneas only, at a fixed chunk size, over a range
# of chunk counts.  Run with nothing else on the machine: aeneas is
# multithreaded and memory-hungry, and a concurrent job distorts both.
# Usage: sweepAe.sh <chunk> <count> [<count> ...]
set -u
R="$(cd "$(dirname "$0")/../.." && pwd)"   # the checkout this spike lives in
H="$(cd "$(dirname "$0")" && pwd)"
CK="$1"; shift
for N in "$@"; do
  TOT=$((CK * N))
  D=$R/_tmp/a63/ae-$N-$CK
  rm -rf "$D"; mkdir -p "$D/lean"
  python3 "$H/genchunked.py" "$TOT" "$CK" "$D"
  ( cd "$D" && charon cargo --preset=aeneas --dest-file "$D/a63.llbc" ) \
    > "$D/charon.log" 2>&1 || { echo "  charon FAILED"; continue; }
  "$H/meas.sh" "ae-$N-$CK" 3600 aeneas -backend lean -split-files \
    -loops-to-rec -max-recdepth 1000000 -dest "$D/lean" -subdir A63 \
    -namespace A63 -no-progress-bar "$D/a63.llbc"
  tail -1 "$R/_tmp/a63/ae-$N-$CK.log" | sed 's/^/  /'
done
