#!/usr/bin/env bash
# scripts/drop-worktree.sh <worktree-path> — the landing step after an agent
# branch is merged and the gates are green on master: remove exactly that
# worktree, delete its branch, and delete its per-checkout scratch
# (`_tmp/gates-<key>`, `_tmp/extract-<key>`, `_tmp/extract-check-<key>`).
#
# Refuses a worktree whose branch is not merged into master.  No sweeping,
# no discovery: one path, given explicitly, or nothing happens.
set -euo pipefail
[ $# -eq 1 ] || { echo "usage: $0 <worktree-path>" >&2; exit 2; }
root=$(cd "$(dirname "$0")/.." && pwd -P)
cd "$root"
path=$(cd "$1" && pwd -P) || { echo "error: $1 is not a directory" >&2; exit 2; }
[ "$path" != "$root" ] || { echo "error: that is the main tree" >&2; exit 2; }
line=$(git worktree list | awk -v p="$path" '$1 == p') 
[ -n "$line" ] || { echo "error: $path is not a worktree of this repository" >&2; exit 2; }
branch=$(sed -n 's/.*\[\([^]]*\)\].*/\1/p' <<<"$line")
[ -n "$branch" ] || { echo "error: $path has no branch (detached HEAD); remove it by hand" >&2; exit 2; }
if ! git merge-base --is-ancestor "$branch" master; then
  echo "error: branch $branch is not merged into master; merge it first (or remove by hand)" >&2
  exit 1
fi
git worktree unlock "$path" 2>/dev/null || true
git worktree remove --force "$path"
git branch -d "$branch" >/dev/null
key=$(printf '%s' "$path" | sha256sum | cut -c1-12)
rm -rf "_tmp/gates-$key" "_tmp/extract-$key" "_tmp/extract-check-$key"
echo "dropped $path ($branch), $(git worktree list | wc -l) worktree(s) remain"
