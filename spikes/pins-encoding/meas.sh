#!/usr/bin/env bash
# Task #63: run a command under `perf stat -e instructions:u` (DESIGN.md's
# measure of record on this shared machine) and print instructions, user CPU
# and wall.  aeneas is multithreaded, so wall alone understates it.
# Usage: meas.sh <label> <timeout> <cmd...>
set -u
R="$(cd "$(dirname "$0")/../.." && pwd)"   # the checkout this spike lives in
L="$1"; TMO="$2"; shift 2
P="$R/_tmp/a63/perf-$L.txt"
( ulimit -v 45000000
  perf stat -e instructions:u -o "$P" timeout "$TMO" "$@" ) \
  > "$R/_tmp/a63/$L.log" 2>&1
RC=$?
python3 - "$L" "$RC" "$P" <<'PY'
import re, sys
label, rc, p = sys.argv[1:]
t = open(p).read()
def g(pat, d=0.0):
    m = re.search(pat, t)
    return float(m.group(1).replace(",", "")) if m else d
print("%-30s rc=%s instr=%8.1fG user=%7.1fs wall=%7.1fs"
      % (label, rc, g(r"([\d,]+)\s+instructions:u") / 1e9,
         g(r"([\d.]+) seconds user"), g(r"([\d.]+) seconds time elapsed")))
PY
