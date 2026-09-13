#!/usr/bin/env bash
# Task #63, route A(1): kernel cost of N table lookups, list vs trie.
# Usage: runtable.sh <list|trie> <N> [timeout]
set -u
R="$(cd "$(dirname "$0")/../.." && pwd)"   # the checkout this spike lives in
H="$(cd "$(dirname "$0")" && pwd)"
LEAN=/home/joachim/.elan/toolchains/leanprover--lean4---v4.33.0/bin/lean
D=$R/_tmp/a63/lean
mkdir -p "$D"
K="$1"; N="$2"; TMO="${3:-900}"
python3 "$H/gentable.py" "$K" "$N" "$D/tb_${K}_${N}.lean" || exit 1
"$H/meas.sh" "tb-$K-$N" "$TMO" "$LEAN" "$D/tb_${K}_${N}.lean"
grep -E "eqRefl|type checking" "$R/_tmp/a63/tb-$K-$N.log" | tail -2
grep -E "^.*error" "$R/_tmp/a63/tb-$K-$N.log" | head -2
