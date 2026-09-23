#!/usr/bin/env bash
# scripts/submit.sh <worktree-path> [note] — a lane agent hands its gated
# branch to the MERGE QUEUE instead of landing it itself (task #97-MQ).
#
# Appends one tab-separated line to `_tmp/merge-queue`:
#   <time> <branch> <commit> <worktree> <base> <touched top dirs> <note>
# where <base> is the integration-branch commit the branch last merged and
# <touched> the paths the branch changes relative to it (collapsed to their
# first two components).  The queue agent merges <commit> — exactly the gated
# commit — into the integration branch, gates what the delta can touch,
# fast-forwards the main tree and drops the worktree.
#
# After submitting, do NOT commit to that branch again: the queue merges the
# submitted commit and then deletes the branch.  If the queue bounces the
# branch back (a conflict or a red gate it cannot fix mechanically), fix it,
# commit, and submit again; the newer line supersedes the older one.
set -euo pipefail
[ $# -ge 1 ] || { echo "usage: $0 <worktree-path> [note]" >&2; exit 2; }
root=$(cd "$(dirname "$0")/.." && git rev-parse --path-format=absolute --git-common-dir)
root=$(dirname "$root")
wt=$(cd "$1" && pwd -P)
note=${2-}
branch=$(git -C "$wt" symbolic-ref --quiet --short HEAD) || { echo "error: $wt is on a detached HEAD" >&2; exit 2; }
into=$(git -C "$root" symbolic-ref --quiet --short HEAD)
[ -z "$(git -C "$wt" status --porcelain --untracked-files=no)" ] || { echo "error: $wt has uncommitted changes" >&2; exit 1; }
commit=$(git -C "$wt" rev-parse HEAD)
base=$(git -C "$wt" merge-base HEAD "$into")
touched=$(git -C "$wt" diff --name-only "$base" HEAD | awk -F/ '{print (NF>2 ? $1"/"$2"/"$3 : $0)}' | sort -u | paste -sd, -)
q="$root/_tmp/merge-queue"
line=$(printf '%s\t%s\t%s\t%s\t%s\t%s\t%s' "$(date -u +%FT%TZ)" "$branch" "${commit:0:12}" "$wt" "${base:0:12}" "${touched:-none}" "$note")
flock "$root/_tmp/.merge-queue.lock" sh -c 'printf "%s\n" "$1" >> "$2"' _ "$line" "$q"
echo "submitted $branch at ${commit:0:12} (base ${base:0:12}) to the merge queue:"
echo "  touched: ${touched:-none}"
echo "Now report to the coordinator; do not commit to $branch again unless the queue bounces it."
