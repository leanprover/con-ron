#!/usr/bin/env bash
# Task #63: time one Lean kernel-cost microbenchmark (spikes/pins-encoding).
# Usage: runbench.sh <encoding> <nbytes> [timeout-seconds]
# Prints: wall, the `elaboration` line (cost of the data literal), the
# `eqRefl` tactic line (elaborator-side defeq) and the final `type checking`
# line (the kernel).
set -u
R="$(cd "$(dirname "$0")/../.." && pwd)"   # the checkout this spike lives in
LEAN=/home/joachim/.elan/toolchains/leanprover--lean4---v4.33.0/bin/lean
HERE="$(cd "$(dirname "$0")" && pwd)"
ENC="$1"; N="$2"; TMO="${3:-300}"
D=$R/_tmp/a63/lean
mkdir -p "$D"
F="$D/${ENC}_${N}.lean"
python3 "$HERE/genbench.py" "$ENC" "$N" "$F" || exit 1
SZ=$(wc -c < "$F")
S=$(date +%s.%N)
( ulimit -v 30000000
  timeout "$TMO" "$LEAN" "$F" > "$D/${ENC}_${N}.out" 2> "$D/${ENC}_${N}.err" )
RC=$?
E=$(date +%s.%N)
python3 "$HERE/report.py" "$ENC" "$N" "$SZ" "$RC" "$S" "$E" \
  "$D/${ENC}_${N}.out" "$D/${ENC}_${N}.err"
