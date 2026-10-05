#!/usr/bin/env bash
# scripts/sync-shared-con-leche.sh — MOVE THE SHARED CON-LECHE CHECKOUT to the
# pin master records (task #108; DESIGN.md §7, the last step of a sync).
#
#   scripts/sync-shared-con-leche.sh [--force] [--no-build] [--tree DIR]
#
# con-leche's lake package directory is shared: every worktree's
# `proof/.lake/packages` is a symlink to `_tmp/aeneas-lean-<tag>/.lake/packages`
# (CLAUDE.md), so its `con-leche` checkout is ONE checkout for all of them.
# A sync runs on a private copy (`scripts/bump-con-leche.sh start`) and, once
# landed, the shared checkout has to follow master's
# `proof/lake-manifest.json`, or every tree reading it builds and cites the
# old con-leche.  Tasks #100, #103, #105 and #106 each left that move to a
# hand-typed command, and #106's agent wrongly suggested `lake update`: that
# RE-RESOLVES the dependency and rewrites the manifest, which is the bump
# itself, not following it.  This script only follows.
#
#   1. reads the target rev from the main tree's `proof/lake-manifest.json`
#      (the `«con-leche»` entry — Lake writes the name with guillemets);
#   2. refuses if any OTHER worktree whose `proof/.lake/packages` is the same
#      shared directory has a manifest naming a different con-leche rev —
#      moving the checkout under it would change what it builds against —
#      unless `--force` (say why in the report);
#   3. `git checkout --detach <rev>` in the shared package directory
#      (fetching from its origin first if the commit is not there), refusing
#      a checkout with local modifications;
#   4. `lake build` in the main tree's `proof/`, which restores the modules of
#      the new pin from the shared Lake cache (`land` seeded it) — skipped
#      with `--no-build`.
#
# `--tree DIR` names the tree whose manifest and packages are meant (default:
# the main worktree); it exists for testing the script on a private copy.
# Exit codes: 0 moved or already there, 1 refused, 2 usage/IO error.
set -euo pipefail
force=0; build=1; tree=""
while [ $# -gt 0 ]; do
  case "$1" in
    --force) force=1; shift ;;
    --no-build) build=0; shift ;;
    --tree) tree=${2-}; shift 2 ;;
    --tree=*) tree=${1#--tree=}; shift ;;
    *) echo "usage: $0 [--force] [--no-build] [--tree DIR]" >&2; exit 2 ;;
  esac
done
here=$(cd "$(dirname "$0")/.." && pwd -P)
if [ -z "$tree" ]; then
  tree=$(dirname "$(git -C "$here" rev-parse --path-format=absolute --git-common-dir)")
fi
tree=$(cd "$tree" && pwd -P)

manifest_rev() { # <tree> -> the «con-leche» rev of its working manifest, or ""
  python3 - "$1/proof/lake-manifest.json" <<'PY' 2>/dev/null || true
import json, sys
try:
    data = json.load(open(sys.argv[1], encoding="utf-8"))
except (OSError, ValueError):
    sys.exit(0)
for p in data.get("packages", []):
    if p.get("name", "").strip("«»") == "con-leche":
        print(p.get("rev", ""))
PY
}

rev=$(manifest_rev "$tree")
[ -n "$rev" ] || { echo "error: no «con-leche» entry in $tree/proof/lake-manifest.json" >&2; exit 2; }
pkgs=$(cd "$tree/proof/.lake/packages" 2>/dev/null && pwd -P) || {
  echo "error: $tree/proof/.lake/packages does not exist" >&2; exit 2; }
dir="$pkgs/con-leche"
[ -d "$dir/.git" ] || [ -f "$dir/.git" ] || { echo "error: $dir is not a git checkout" >&2; exit 2; }

# 2. the other worktrees reading the same directory
others=()
while read -r wt; do
  wt=$(cd "$wt" 2>/dev/null && pwd -P) || continue
  [ "$wt" = "$tree" ] && continue
  theirs=$(cd "$wt/proof/.lake/packages" 2>/dev/null && pwd -P) || continue
  [ "$theirs" = "$pkgs" ] || continue   # a private copy: not ours to worry about
  r=$(manifest_rev "$wt")
  if [ -n "$r" ] && [ "$r" != "$rev" ]; then others+=("$wt (${r:0:8})"); fi
done < <(git -C "$tree" worktree list --porcelain | sed -n 's/^worktree //p')
if [ ${#others[@]} -gt 0 ]; then
  echo "sync-shared-con-leche: other worktrees read $pkgs at another con-leche pin:"
  printf '  %s\n' "${others[@]}"
  if [ "$force" -eq 0 ]; then
    echo "refusing to move it to ${rev:0:8} under them; merge master there first, or pass --force" >&2
    exit 1
  fi
  echo "--force: moving it anyway"
fi

# 3. the move
cur=$(git -C "$dir" rev-parse HEAD)
if [ "$cur" = "$rev" ]; then
  echo "sync-shared-con-leche: $dir is already at ${rev:0:8}"
else
  if [ -n "$(git -C "$dir" status --porcelain --untracked-files=no)" ]; then
    echo "error: $dir has local modifications; refusing to check out over them" >&2
    exit 1
  fi
  if ! git -C "$dir" cat-file -e "$rev^{commit}" 2>/dev/null; then
    echo "sync-shared-con-leche: fetching ${rev:0:8} into $dir"
    git -C "$dir" fetch --quiet origin "$rev" 2>/dev/null || git -C "$dir" fetch --quiet origin
  fi
  git -C "$dir" -c advice.detachedHead=false checkout --quiet --detach "$rev"
  echo "sync-shared-con-leche: $dir moved ${cur:0:8} -> ${rev:0:8}"
fi

# 4. restore the new pin's modules from the shared cache.  `env -C`, never
#    `lake -d proof` from the root (CLAUDE.md: a different toolchain).
if [ "$build" -eq 1 ]; then
  echo "sync-shared-con-leche: lake build in $tree/proof (restores from the shared cache)"
  env -C "$tree/proof" lake build
fi
