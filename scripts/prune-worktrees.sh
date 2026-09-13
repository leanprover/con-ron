#!/usr/bin/env bash
# scripts/prune-worktrees.sh [--dry-run] — remove the agent worktrees whose
# branch is merged into master, delete those branches, and delete the
# per-checkout scratch (`_tmp/gates-<key>`, `_tmp/extract-<key>`,
# `_tmp/extract-check-<key>`) of every checkout that no longer exists.
#
# A worktree whose branch is NOT merged is listed and kept (its branch too);
# pass its path as an argument to remove the worktree anyway (the branch ref
# stays, so nothing is lost).  Run from the main tree after a landing.
set -euo pipefail
root=$(cd "$(dirname "$0")/.." && pwd -P)
cd "$root"
dry=0; force=()
for a in "$@"; do case "$a" in --dry-run) dry=1;; *) force+=("$a");; esac; done
run() { if [ "$dry" = 1 ]; then echo "  would: $*"; else "$@"; fi; }
key() { printf '%s' "$1" | sha256sum | cut -c1-12; }

kept=0; removed=0
while read -r line; do
  path=${line%% *}
  branch=$(sed -n 's/.*\[\([^]]*\)\].*/\1/p' <<<"$line")
  [ -n "$branch" ] || continue
  forced=0
  for f in "${force[@]:-}"; do [ "$f" = "$path" ] && forced=1; done
  [ "$path" = "$root" ] && continue
  if [ "$(git rev-parse "$branch")" = "$(git rev-parse master)" ] && [ "$forced" != 1 ]; then
    echo "fresh    $branch  ($path) — no commits yet, an agent may be working in it; kept"
    kept=$((kept+1))
    continue
  fi
  if git merge-base --is-ancestor "$branch" master 2>/dev/null; then
    echo "merged   $branch  ($path)"
    run git worktree unlock "$path" 2>/dev/null || true
    run git worktree remove --force "$path"
    run git branch -d "$branch" >/dev/null
    removed=$((removed+1))
  else
    if [ "$forced" = 1 ]; then
      echo "unmerged $branch — removing the worktree as asked, keeping the branch"
      run git worktree unlock "$path" 2>/dev/null || true
      run git worktree remove --force "$path"
      removed=$((removed+1))
    else
      echo "unmerged $branch  ($path) — kept; pass the path to remove it"
      kept=$((kept+1))
    fi
  fi
done < <(git worktree list | grep -v ' (bare)$' | grep -v '\[master\]$')

# Scratch of checkouts that no longer exist.
live=$(git worktree list | awk '{print $1}' | while read -r p; do key "$p"; done)
for d in _tmp/gates-* _tmp/extract-* _tmp/extract-check-*; do
  [ -d "$d" ] || continue
  k=${d##*-}
  if ! grep -qx "$k" <<<"$live"; then
    echo "stale scratch $d"
    run rm -rf "$d"
  fi
done
echo "worktrees removed: $removed, kept: $kept; $(git worktree list | wc -l) remain"
