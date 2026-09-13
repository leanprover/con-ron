#!/usr/bin/env bash
# Task #63 route A: `#print axioms` of the chunked byte constants.  Task #43's
# obstacle (a) was that a `&str` constant carries `toStr`'s `decide +native`
# axiom; a `[u8; N]` constant must carry none.
# Usage: axioms.sh <dir-holding-A63>
set -u
R="$(cd "$(dirname "$0")/../.." && pwd)"   # the checkout this spike lives in
LEAN=/home/joachim/.elan/toolchains/leanprover--lean4---v4.33.0/bin/lean
P=$R/proof
ROOT="$1"
export LEAN_PATH="$(cd "$P" && lake env printenv LEAN_PATH):$ROOT"
export LEAN_NUM_THREADS=4
( cd "$ROOT" && ulimit -v 40000000
  timeout 1800 "$LEAN" -R "$ROOT" -o "$ROOT/A63/Funs.olean" "$ROOT/A63/Funs.lean" )
( cd "$ROOT" && ulimit -v 40000000; timeout 600 "$LEAN" -R "$ROOT" "$ROOT/Ax.lean" )
