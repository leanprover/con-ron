#!/usr/bin/env bash
# scripts/drop-worktree.sh [--into <ref>] <worktree-path> — the landing step
# after an agent branch is merged and the gates are green: remove exactly that
# worktree, delete its branch, and delete its per-checkout scratch
# (`_tmp/*-<key>`, see below).
#
# The integration ref defaults to the MAIN WORKTREE'S CURRENT BRANCH, not to
# `master`: during a campaign the branches land on the campaign branch (task
# #97 lands on `arena`), and a hard-coded `master` made this script refuse
# every landing, so they were removed by hand — and the per-checkout scratch
# drifted, 13 GB of it by the time anyone looked.  Pass `--into <ref>` to
# override.
#
# Refuses a worktree whose branch is not merged into that ref.  No sweeping,
# no discovery: one path, given explicitly, or nothing happens.
set -euo pipefail
into=""
while [ $# -gt 0 ]; do
  case "$1" in
    --into) into=${2-}; [ -n "$into" ] || { echo "usage: $0 [--into <ref>] <worktree-path>" >&2; exit 2; }; shift 2;;
    --into=*) into=${1#--into=}; shift;;
    *) break;;
  esac
done
[ $# -eq 1 ] || { echo "usage: $0 [--into <ref>] <worktree-path>" >&2; exit 2; }
root=$(cd "$(dirname "$0")/.." && pwd -P)
cd "$root"
# default: whatever the main worktree is currently on (`arena` during a
# campaign, `master` the rest of the time)
[ -n "$into" ] || into=$(git symbolic-ref --quiet --short HEAD) || {
  echo "error: main worktree is on a detached HEAD; pass --into <ref>" >&2; exit 2; }
path=$(cd "$1" && pwd -P) || { echo "error: $1 is not a directory" >&2; exit 2; }
[ "$path" != "$root" ] || { echo "error: that is the main tree" >&2; exit 2; }
line=$(git worktree list | awk -v p="$path" '$1 == p') 
[ -n "$line" ] || { echo "error: $path is not a worktree of this repository" >&2; exit 2; }
branch=$(sed -n 's/.*\[\([^]]*\)\].*/\1/p' <<<"$line")
[ -n "$branch" ] || { echo "error: $path has no branch (detached HEAD); remove it by hand" >&2; exit 2; }
if ! git merge-base --is-ancestor "$branch" "$into"; then
  echo "error: branch $branch is not merged into $into; merge it first (or pass --into <ref>)" >&2
  exit 1
fi
git worktree unlock "$path" 2>/dev/null || true
git worktree remove --force "$path"
# `-D`, not `-d`: the ancestry check above is against $into, while `-d`
# checks the MAIN worktree's HEAD, which refuses a branch merged into a
# campaign branch (task #105).
git branch -D "$branch" >/dev/null
# The per-checkout scratch.  Every script that keeps scratch under the shared
# `_tmp/` keys it by the checkout and names it `_tmp/<name>-<key>`, where
# <key> is the first 12 hex digits of sha256(checkout root) — today
# `gates.sh` (gates-), `extract.sh` (extract-, extract-check-),
# `diff-e2e.sh` (diff-e2e-), `frontier.sh` (frontier-), `gen-pins.sh`
# (gen-pins-), `gen-prelude.sh` (gen-prelude-), `gen-prelude-lean.sh`
# (gen-prelude-lean-), `dead-census.py` via `dead-census-gate.sh`
# (deadcode-) and `provenance-selftest.py` (provenance-selftest-).  So the
# list is not enumerated here, it is that naming rule: everything directly
# under `_tmp/` whose name ends in `-<key>` (task #108 — the enumerated list
# this replaced had missed `diff-e2e-` and `deadcode-`, which #106 and #107
# then deleted by hand).  A new script that keys its scratch the same way is
# covered without an edit here; `grep -n sha256 scripts/*` lists them.
key=$(printf '%s' "$path" | sha256sum | cut -c1-12)
for d in _tmp/*-"$key"; do
  [ -e "$d" ] && rm -rf "$d"
done
echo "dropped $path ($branch, merged into $into), $(git worktree list | wc -l) worktree(s) remain"
# The worktree is only half of a landing.  An agent that has reported is still
# a live subagent holding its context until it is stopped explicitly, and
# nothing sweeps them: they accumulate silently, because a finished agent looks
# exactly like a working one in every view except an explicit listing.  The
# directory is named after the agent, so say which one out loud here — this is
# the moment the step is otherwise forgotten.
case "$(basename "$path")" in
  agent-*) echo "NEXT: stop the agent as well — ${path##*/agent-} (TaskStop, or your runner's equivalent); landing = merge + drop worktree + STOP AGENT" ;;
esac
