#!/usr/bin/env bash
# Task #63 route A: the chunk-size tradeoff at a fixed total.  Aeneas cost
# grows with the *number* of constants; Lean's cost grows with the *size* of
# each, because `Aeneas.Std.Array.make`'s `hl : init.length = n` default
# argument is discharged by `simp`.
# Usage: sweepCk.sh <total> <recdepth> <chunk> [<chunk> ...]
set -u
R="$(cd "$(dirname "$0")/../.." && pwd)"   # the checkout this spike lives in
H="$(cd "$(dirname "$0")" && pwd)"
LEAN=/home/joachim/.elan/toolchains/leanprover--lean4---v4.33.0/bin/lean
P=$R/proof
export LEAN_PATH="$(cd "$P" && lake env printenv LEAN_PATH)"
export LEAN_NUM_THREADS=8
TOT="$1"; RD="$2"; shift 2
for CK in "$@"; do
  D=$R/_tmp/a63/ck-$TOT-$CK-$RD
  rm -rf "$D"; mkdir -p "$D/lean"
  python3 "$H/genchunked.py" "$TOT" "$CK" "$D"
  ( cd "$D" && charon cargo --preset=aeneas --dest-file "$D/a63.llbc" ) \
    > "$D/charon.log" 2>&1
  "$H/meas.sh" "aeneas-$TOT-$CK-$RD" 3600 aeneas -backend lean -split-files \
    -loops-to-rec -max-recdepth "$RD" -dest "$D/lean" -subdir A63 \
    -namespace A63 -no-progress-bar "$D/a63.llbc"
  ( cd "$D/lean" && LEAN_PATH="$LEAN_PATH:$D/lean" "$H/meas.sh" \
      "leanT-$TOT-$CK-$RD" 3600 "$LEAN" -R "$D/lean" \
      -o "$D/lean/A63/Types.olean" "$D/lean/A63/Types.lean" ) > /dev/null
  ( cd "$D/lean" && LEAN_PATH="$LEAN_PATH:$D/lean" "$H/meas.sh" \
      "leanF-$TOT-$CK-$RD" 3600 "$LEAN" -R "$D/lean" "$D/lean/A63/Funs.lean" )
  grep -cE "^.*error:" "$R/_tmp/a63/leanF-$TOT-$CK-$RD.log" \
    | sed 's/^/  lean errors: /'
done
