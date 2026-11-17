#!/usr/bin/env bash
# scripts/land.sh <worktree-path> <report-file> — land an agent branch on the
# integration branch (the main worktree's current branch: `master`, or `arena`
# during a campaign).  Run it AFTER merging the integration branch into the
# agent branch and running scripts/gates.sh there.
#
#   1. refuse unless the integration branch is already merged into the agent
#      branch (then merge it, re-run the gates the delta can touch, retry) —
#      so the landing merge is conflict-free and adds nothing ungated;
#   2. merge the branch with `git merge --no-ff`, the commit message being
#      <report-file>: a subject line `Task #N: merge <branch> — <summary>`, a
#      blank line, then the task's final report (what changed, gates,
#      measurements, what was left) and the Co-Authored-By trailer (task #160:
#      every task lands as one merge commit that carries its report);
#   3. drop the worktree, its branch and its per-checkout scratch
#      (scripts/drop-worktree.sh).
#
# This is the one sanctioned write to the main tree from an agent.  Concurrent
# landings serialise on git's index lock; the loser retries a few times.
set -euo pipefail
[ $# -eq 2 ] || { echo "usage: $0 <worktree-path> <report-file>" >&2; exit 2; }
msg=$(cd "$(dirname "$2")" && pwd -P)/$(basename "$2")
[ -s "$msg" ] || { echo "error: the report file $2 is missing or empty" >&2; exit 2; }
root=$(cd "$(dirname "$0")/.." && git rev-parse --path-format=absolute --git-common-dir)
root=$(dirname "$root")
wt=$(cd "$1" && pwd -P)
branch=$(git -C "$wt" symbolic-ref --quiet --short HEAD) || { echo "error: $wt is on a detached HEAD" >&2; exit 2; }
into=$(git -C "$root" symbolic-ref --quiet --short HEAD)
[ -z "$(git -C "$wt" status --porcelain)" ] || { echo "error: $wt has uncommitted changes" >&2; exit 1; }
[ -z "$(git -C "$root" status --porcelain --untracked-files=no)" ] || { echo "error: the main tree has uncommitted changes" >&2; exit 1; }
for i in 1 2 3 4 5; do
  if ! git -C "$root" merge-base --is-ancestor "$into" "$branch"; then
    echo "error: $into is not merged into $branch — merge $into into $branch, re-gate what the delta can touch, retry" >&2
    exit 1
  fi
  if out=$(git -C "$root" merge --no-ff -F "$msg" "$branch" 2>&1); then
    echo "landed $branch on $into at $(git -C "$root" rev-parse --short HEAD) (merge commit)"
    cd "$root"   # the worktree is about to disappear; do not sit in it
    exec "$root/scripts/drop-worktree.sh" "$wt"
  fi
  case "$out" in
    *index.lock*) sleep $((i * 5)) ;;
    *) echo "error: the merge of $branch into $into failed" >&2
       echo "$out" >&2; exit 1 ;;
  esac
done
echo "error: main tree stayed locked; retry later" >&2; exit 1
