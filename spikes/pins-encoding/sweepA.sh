#!/usr/bin/env bash
# Task #63 route A: charon / aeneas / lean cost of the chunked byte table,
# at a fixed chunk size, over a range of total sizes.
# Usage: sweepA.sh <chunk> <total> [<total> ...]
set -u
R="$(cd "$(dirname "$0")/../.." && pwd)"   # the checkout this spike lives in
H="$(cd "$(dirname "$0")" && pwd)"
LEAN=/home/joachim/.elan/toolchains/leanprover--lean4---v4.33.0/bin/lean
P=$R/proof
export LEAN_PATH="$(cd "$P" && lake env printenv LEAN_PATH)"
CK="$1"; shift
for TOT in "$@"; do
  D=$R/_tmp/a63/ck-$TOT-$CK
  rm -rf "$D"; mkdir -p "$D/lean"
  python3 "$H/genchunked.py" "$TOT" "$CK" "$D"
  ( cd "$D" && "$H/meas.sh" "charon-$TOT-$CK" 3600 charon cargo \
      --preset=aeneas --dest-file "$D/a63.llbc" )
  "$H/meas.sh" "aeneas-$TOT-$CK" 3600 aeneas -backend lean -split-files \
    -loops-to-rec -dest "$D/lean" -subdir A63 -namespace A63 \
    -no-progress-bar "$D/a63.llbc"
  ( cd "$D/lean" && LEAN_PATH="$LEAN_PATH:$D/lean" "$H/meas.sh" \
      "leanT-$TOT-$CK" 3600 "$LEAN" -R "$D/lean" -o "$D/lean/A63/Types.olean" \
      "$D/lean/A63/Types.lean" )
  ( cd "$D/lean" && LEAN_PATH="$LEAN_PATH:$D/lean" "$H/meas.sh" \
      "leanF-$TOT-$CK" 3600 "$LEAN" -R "$D/lean" "$D/lean/A63/Funs.lean" )
  wc -l "$D/lean/A63/Funs.lean"
done
