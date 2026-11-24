#!/usr/bin/env bash
# The unused-declaration gate (task #105): build what the census imports that
# the default targets do not (the four executables and the two index roots
# `ConRon.Bridge`/`ConRon.Refine2`, which `globs` libraries leave out, task
# #101), then `scripts/dead-census.py --check`: no declaration of
# `proof/ConRon/**` may be unreachable from the capstone's headline theorems,
# the Test modules and the tooling, beyond `scripts/dead-census-allow.txt`.
# Runs after `lake-build`, which builds these targets too (task #177: one
# Lake invocation, so their C compile overlaps the elaboration): under
# `scripts/gates.sh` the build below is a no-op, and it stays so that the
# script also runs on its own.  Keep the two target lists in step.  The census
# itself: ~3 minutes and ~10 GB for its import of the whole environment.
set -euo pipefail
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
key=$(printf '%s' "$root" | sha256sum | cut -c1-12)
( cd "$root/proof" && lake build ConRon.Bridge ConRon.Refine2 con-ron-lean con-ron-lean-olean-compare \
    con-ron-arena-bench con-ron-dump-pins )
python3 "$root/scripts/dead-census.py" --out "_tmp/deadcode-$key" --check
