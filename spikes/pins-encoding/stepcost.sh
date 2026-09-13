#!/usr/bin/env bash
# Task #63 route B: the per-node cost of the `step` proof style, measured on
# the one file that already has it -- `proof/ConRon/Refine/BasisTables.lean`
# (task #22: six block lemmas over 18/19/25/48/54/98 interned nodes).
#
# Read-only: the file is re-elaborated against an ALREADY BUILT checkout's
# oleans and nothing is written into it.  `$CON_RON_BUILT` names that checkout
# (default: the repository this spike is in); an agent worktree with no
# `proof/.lake/build` should point it at the main tree.
#
# `lake env lean` ignores `[leanOptions]`, so task #22's two `backward.*`
# options are passed with -D.
set -u
R="$(cd "$(dirname "$0")/../.." && pwd)"   # the checkout this spike lives in
M="${CON_RON_BUILT:-$R}"                   # a checkout with proof/ built
LEAN=/home/joachim/.elan/toolchains/leanprover--lean4---v4.33.0/bin/lean
export LEAN_PATH="$M/proof/.lake/build/lib/lean:$(cd "$R/proof" && lake env printenv LEAN_PATH)"
export LEAN_NUM_THREADS=4
O=$R/_tmp/a63/steps.out
mkdir -p "$(dirname "$O")"
( cd "$M/proof" && ulimit -v 40000000
  timeout 1800 "$LEAN" -R "$M/proof" -D profiler=true -D profiler.threshold=200 \
    -D backward.isDefEq.respectTransparency=false -D backward.do.legacy=true \
    "$M/proof/ConRon/Refine/BasisTables.lean" ) > "$O" 2>&1
echo "rc=$?"
grep -E "error" "$O" | head -3
grep -nE "took" "$O" | head -40
