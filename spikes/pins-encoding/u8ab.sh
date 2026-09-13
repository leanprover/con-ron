#!/usr/bin/env bash
# Task #63 route A: where the chunk's Lean cost actually is.  Same 1700 bytes
# as a `List Std.U8` written in Aeneas's `99#u8` notation (what the generated
# constant holds) and as a plain core `List UInt8`.
set -u
R="$(cd "$(dirname "$0")/../.." && pwd)"   # the checkout this spike lives in
H="$(cd "$(dirname "$0")" && pwd)"
P=$R/proof
export LEAN_PATH="$(cd "$P" && lake env printenv LEAN_PATH)"
export LEAN_NUM_THREADS=8
D=$R/_tmp/a63/u8ab
LEAN=/home/joachim/.elan/toolchains/leanprover--lean4---v4.33.0/bin/lean
for f in AeneasU8 CoreU8; do
  ( cd "$D" && "$H/meas.sh" "u8ab-$f" 1800 "$LEAN" "$D/$f.lean" )
done
