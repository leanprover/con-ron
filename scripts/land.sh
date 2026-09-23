#!/usr/bin/env bash
# scripts/land.sh <worktree-path> — an agent lands its own branch on the
# integration branch (the main worktree's current branch, `arena` during a
# campaign).  Run it from the agent's worktree AFTER merging the integration
# branch into the agent branch and running scripts/gates.sh there.
#
#   1. fast-forward the main tree to the agent branch (refuses anything that is
#      not a fast-forward: then merge the integration branch again, re-run the
#      gates the delta can touch, and retry);
#   2. drop the worktree, its branch and its per-checkout scratch
#      (scripts/drop-worktree.sh).
#
# This is the one sanctioned write to the main tree from an agent.  Concurrent
# landings serialise on git's index lock; the loser retries a few times.
set -euo pipefail
[ $# -eq 1 ] || { echo "usage: $0 <worktree-path>" >&2; exit 2; }
root=$(cd "$(dirname "$0")/.." && git rev-parse --path-format=absolute --git-common-dir)
root=$(dirname "$root")
wt=$(cd "$1" && pwd -P)
branch=$(git -C "$wt" symbolic-ref --quiet --short HEAD) || { echo "error: $wt is on a detached HEAD" >&2; exit 2; }
into=$(git -C "$root" symbolic-ref --quiet --short HEAD)
[ -z "$(git -C "$wt" status --porcelain)" ] || { echo "error: $wt has uncommitted changes" >&2; exit 1; }
for i in 1 2 3 4 5; do
  if out=$(git -C "$root" merge --ff-only "$branch" 2>&1); then
    echo "landed $branch on $into at $(git -C "$root" rev-parse --short HEAD)"
    cd "$root"   # the worktree is about to disappear; do not sit in it
    exec "$root/scripts/drop-worktree.sh" "$wt"
  fi
  case "$out" in
    *index.lock*) sleep $((i * 5)) ;;
    *) echo "error: not a fast-forward of $into — merge $into into $branch, re-gate what the delta can touch, retry" >&2
       echo "$out" >&2; exit 1 ;;
  esac
done
echo "error: main tree stayed locked; retry later" >&2; exit 1
