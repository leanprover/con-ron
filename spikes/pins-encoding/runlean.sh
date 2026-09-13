#!/usr/bin/env bash
# Task #63: elaborate an Aeneas-generated A63/{Types,Funs}.lean outside the
# project build (so no other worktree's `lake build` is disturbed).
# Usage: runlean.sh <dir-holding-A63> [extra.lean] [timeout]
set -u
R="$(cd "$(dirname "$0")/../.." && pwd)"   # the checkout this spike lives in
LEAN=/home/joachim/.elan/toolchains/leanprover--lean4---v4.33.0/bin/lean
ROOT="$1"; EXTRA="${2:-}"; TMO="${3:-3600}"
P=$R/proof
LP="$(cd "$P" && lake env printenv LEAN_PATH)"
export LEAN_PATH="$LP:$ROOT"

run() {
  local f="$1" s e rc
  s=$(date +%s.%N)
  ( cd "$ROOT" && ulimit -v 30000000
    timeout "$TMO" "$LEAN" -R "$ROOT" -o "${f%.lean}.olean" "$f" ) > "$f.out" 2>&1
  rc=$?
  e=$(date +%s.%N)
  python3 -c "print(f'  $(basename $f): rc=$rc wall={float('$e')-float('$s'):.1f}s')"
  grep -E "error|elaboration took|type checking took" "$f.out" | head -6
}

run "$ROOT/A63/Types.lean"
run "$ROOT/A63/Funs.lean"
[ -n "$EXTRA" ] && run "$EXTRA"
exit 0
