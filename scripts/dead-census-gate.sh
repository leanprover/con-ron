#!/usr/bin/env bash
# The unused-declaration gate (task #105): build what the census imports that
# the default targets do not (the four executables and the two index roots
# `ConRon.Bridge`/`ConRon.Refine2`, which `globs` libraries leave out, task
# #101), then `scripts/dead-census.py --check`: no declaration of
# `proof/ConRon/**` may be unreachable from the capstone's headline theorems,
# the Test modules and the tooling, beyond `scripts/dead-census-allow.txt`.
# Runs after `lake-build`, so everything else is already built; ~3 minutes and
# ~10 GB for the census's import of the whole environment.
set -euo pipefail
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
key=$(printf '%s' "$root" | sha256sum | cut -c1-12)
( cd "$root/proof" && lake build ConRon.Bridge ConRon.Refine2 con-ron-lean \
    con-ron-arena-bench con-ron-gen-tables con-ron-dump-pins )
python3 "$root/scripts/dead-census.py" --out "_tmp/deadcode-$key" --check
