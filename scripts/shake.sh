#!/usr/bin/env bash
# scripts/shake.sh — `lake shake` over con-ron's module files (task #137).
#
# The 178 `module` files (`ConRon/Arena/**`, `ConRon/Bridge/**`, the two roots,
# `Gen/`, `Dump/`) are the only ones `lake shake` accepts; the classic tiers
# (`Generated`, `Refine*`, `Capstone`) are outside every closure it is given,
# so it never proposes an edit there.  It is run with `--keep-implied` (an
# import another import implies is kept, which is what stops shake from
# rewriting the whole graph), and only proposals whose target is `ConRon.*` or
# `ConLeche.*` are reported: shake's `Std`/`Lean` additions are its noise floor
# (constants a `grind`/`omega` proof term mentions), and those edges never
# change, so they cannot move an early cutoff.
#
# The four modules that define `main` cannot share one environment, so each is
# shaken on its own with `--only`.
#
# Blind spots, each answered by a `-- shake: keep (reason)` on the import line
# or `module -- shake: keep-all (reason)` on the header: `#print axioms` and
# `#guard` store no constant; a `vcgen [-foo]` erasure names a lemma no proof
# term holds; a `grind_pattern`/`attribute` in module B on a lemma of module A
# is recorded as a need of A only; a bare `open N` needs `N` to exist.  A
# classic file that reached a name through a re-export shake demoted needs a
# plain `import` of its own; shake cannot see that either, the build does.
#
# Usage: scripts/shake.sh         report; exit 1 if shake proposes an edit
#        scripts/shake.sh --fix   apply shake's own `--fix` (all proposals,
#                                 noise included: review the diff, keep the
#                                 in-tree lines, drop the Std/Lean ones)
set -uo pipefail
set +a   # an allexport shell would put the shake log into the environment
cd "$(dirname "$0")/../proof" || exit 3

mods=$(python3 - <<'PY'
import re, subprocess
for f in subprocess.run(['git', 'ls-files', 'ConRon'], capture_output=True, text=True).stdout.split():
    if not f.endswith('.lean'): continue
    t = re.sub(r'/-.*?-/', '', open(f).read(), flags=re.S)
    for l in t.split('\n'):
        l = l.split('--')[0].strip()
        if l:
            if l == 'module': print(f[:-5].replace('/', '.'))
            break
PY
)
mains="ConRon.Arena.Exe ConRon.Arena.Bench ConRon.Arena.Main ConRon.Gen.Main ConRon.Dump.Pins"
libs=$(printf '%s\n' $mods | grep -vxF -f <(printf '%s\n' $mains))

# shake reads the oleans; `lake build` does not build the roots or the exes.
if ! lake build $mods > /dev/null 2>&1; then
  echo 'shake: ERROR — the module files do not build'; exit 3
fi

fix=
[ "${1:-}" = --fix ] && fix=--fix
out=$(mktemp); trap 'rm -f "$out"' EXIT
{ lake shake --keep-implied $fix $libs
  for m in $mains; do lake shake --keep-implied $fix --only "$m" "$m"; done; } > "$out" 2>&1
if grep -q '^error:' "$out"; then
  grep '^error:' "$out" | head -5; exit 3
fi
[ -n "$fix" ] && { tail -1 "$out"; exit 0; }

found=$(python3 -c '
import sys, re
cur = None
for line in sys.stdin:
    line = line.rstrip("\n")
    if line.endswith(".lean:") and not line.startswith(" "):
        cur = re.sub(r"^.*?/proof/", "", line[:-1]); continue
    m = re.match(r"\s+(remove|add) #\[(.*)\]$", line)
    if cur and m:
        items = [x for x in m.group(2).split(", ") if x.split()[-1].startswith(("ConRon", "ConLeche"))]
        if items: print(f"{cur}: {m.group(1)} {items}")
' < "$out")
if [ -n "$found" ]; then
  printf '%s\n' "$found"
  echo "shake: FAIL — $(printf '%s\n' "$found" | wc -l) in-tree proposal(s); apply each, or mark it '-- shake: keep (reason)'"
  exit 1
fi
echo "shake: OK — no in-tree proposal over $(echo $mods | wc -w) module files"
