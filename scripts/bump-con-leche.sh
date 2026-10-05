#!/usr/bin/env bash
# scripts/bump-con-leche.sh — THE CON-LECHE SYNC, one command per step
# (task #108; DESIGN.md §7 is the procedure this script is).
#
#   scripts/bump-con-leche.sh start <rev> --task <id> [--from <commit>]
#                                   [--overlay-scripts]
#   scripts/bump-con-leche.sh status  [<short>]
#   scripts/bump-con-leche.sh measure [<short>]
#   scripts/bump-con-leche.sh pin     [<short>]
#   scripts/bump-con-leche.sh land    [<short>] [--no-measure]
#   scripts/bump-con-leche.sh abort   [<short>] --yes
#
# <short> is the first eight hex digits of the new con-leche commit; inside
# the bump's worktree (`_tmp/wt-bump-<short>`) it can be left out.
# Everything the sync keeps lives in `_tmp/bump-<short>/` (the private
# packages, the logs, the findings, master's binary), next to the worktree.
#
# start <rev>   (run anywhere in the repository)
#   1. resolves <rev> (a commit of con-leche, or `master`) in a reflink copy
#      of the shared packages directory, `_tmp/bump-<short>/packages`, so
#      that nothing the other worktrees read moves (CLAUDE.md's bump-campaign
#      rule; the Aeneas library itself is a path dependency that a sync does
#      not change, so the packages are all that is copied).  When con-leche's
#      `lean-toolchain` at <rev> differs from `proof/`'s, the sync MOVES THE
#      TOOLCHAIN (task #110): no copy; the worktree gets the new
#      `proof/lean-toolchain`, the Aeneas path of the new toolchain's
#      `_tmp/aeneas-lean-<tag>` (built beside the old one by
#      `setup-aeneas-lean.sh`, Mathlib fetched) and that directory's package
#      set, which no other tree reads yet; `lake update` re-resolves all of
#      it.  Porting `patches/aeneas.patch` to the new toolchain is then hand
#      work, like the rest of the port;
#   2. creates the worktree `_tmp/wt-bump-<short>` on branch `bump-<short>`
#      off master (or --from), with `_tmp` linked to the shared one,
#      `proof/.lake/packages` linked to the private copy and NO
#      `proof/.lake/build` (CLAUDE.md: the shared Lake cache restores it);
#   3. checks the private con-leche out at the old pin, builds master's
#      binary (`_tmp/bump-<short>/con-ron-master`) and records `coverage`;
#   4. edits `rev` in `proof/lakefile.toml` and runs `lake update con-leche`
#      in `proof/` — the pin is now changed in the working tree and is NOT
#      committed (it is the last commit, `pin` below);
#   5. `provenance.py update --auto` (the classifier: mechanical buckets
#      applied, `findings.tsv`), `coverage` again, `overview-links.sh
#      --follow` (the anchors whose text did not change), the prelude
#      generators' `--check`, and `diff-e2e.sh` with master's binary at the
#      new pin;
#   6. commits what it changed (the pin files excepted) and prints the work
#      order, also saved as `_tmp/bump-<short>/work-order.txt`.
#
# (`--overlay-scripts` is for testing the script itself on an old --from:
# it copies this tree's scripts/ into the worktree first, as its own commit.)
#
# order         prints the work order `start` saved, recomputed.
# status        the work order's live numbers: markers left, `check`,
#               `coverage`'s new uncovered declarations.
# measure       §7.x's one regression check, made once, on the binary that
#               lands: `Init`, con-ron only, one worker, `instructions:u`, with
#               `scripts/bench-baselines.sh` — master's binary and the branch's,
#               one run each — and the delta.  Not wall time, not Mathlib (the
#               landing rule's Mathlib run is the porter's call when the sync
#               touches memory), never OVERVIEW §9.
# pin           `overview-links.sh --follow` once more (its own commit if it
#               moved anything), then commits `proof/lakefile.toml` and
#               `proof/lake-manifest.json` — nothing else — as the branch's
#               LAST commit; `scripts/pin-last.py --tip-is-pin` confirms.
# land          preconditions: the worktree is clean, the tip is the pin commit
#               and no earlier commit moves the pin (`pin-last.py`), master is
#               merged, `scripts/gates.sh` was green at exactly this commit
#               (its stamp), and `measure` saw the crates as they are.  Then:
#               the fast-forward of master, seeding the shared Lake cache from
#               the worktree, `drop-worktree.sh`, deleting `_tmp/bump-<short>`
#               (the private packages with it), after a toolchain move
#               `setup-aeneas-lean.sh` in the main tree (repoints its
#               packages link), and `sync-shared-con-leche.sh` (which may
#               refuse while other worktrees sit at the old pin; it says what
#               to run later).
# abort --yes   throws a bump away: the worktree, its branch, `_tmp/bump-<short>`.
set -euo pipefail

here=$(cd "$(dirname "$0")/.." && pwd -P)
main=$(dirname "$(git -C "$here" rev-parse --path-format=absolute --git-common-dir)")
TMP="$main/_tmp"

die() { echo "bump-con-leche: $*" >&2; exit 1; }
say() { echo "== $*"; }

manifest_rev() { # <manifest file> -> the «con-leche» rev
  python3 -c '
import json, sys
for p in json.load(open(sys.argv[1], encoding="utf-8")).get("packages", []):
    if p.get("name", "").strip("«»") == "con-leche":
        print(p.get("rev", ""))' "$1"
}

# The bump a subcommand means: its argument, or the worktree it runs in.
resolve_short() {
  local s=${1-}
  if [ -z "$s" ]; then
    local top
    top=$(git rev-parse --show-toplevel 2>/dev/null || true)
    case "$(basename "$top")" in
      wt-bump-*) s=${top##*/wt-bump-} ;;
      *) die "which bump? pass <short>, or run inside _tmp/wt-bump-<short>" ;;
    esac
  fi
  short=$s
  state="$TMP/bump-$short"
  wt="$TMP/wt-bump-$short"
  [ -f "$state/state" ] || die "no bump $short ($state/state missing)"
  # shellcheck disable=SC1091
  . "$state/state"
}

# The baseline binary, built from `git archive` of <ref> in the bump's
# scratch (no second worktree), and rebuilt only when <ref> has moved since:
# `start` builds the commit the bump branches from (master, or --from),
# `measure` master as it is then (what the branch lands on).
master_binary() {
  local m
  m=$(git -C "$main" rev-parse "$1^{commit}")
  if [ -x "$state/con-ron-master" ] && [ "$(cat "$state/con-ron-master.commit" 2>/dev/null)" = "$m" ]; then
    return 0
  fi
  say "building the baseline con-ron at ${m:0:8} (release)"
  rm -rf "$state/master-src"
  mkdir -p "$state/master-src"
  git -C "$main" archive "$m" Cargo.toml Cargo.lock crates | tar -x -C "$state/master-src"
  CARGO_TARGET_DIR="$state/master-target" cargo build --quiet --release -p con-ron \
    --manifest-path "$state/master-src/Cargo.toml" > "$state/master-build.log" 2>&1 \
    || { tail -20 "$state/master-build.log"; die "the baseline build failed"; }
  cp "$state/master-target/release/con-ron" "$state/con-ron-master"
  echo "$m" > "$state/con-ron-master.commit"
}

# ---------------------------------------------------------------- start
cmd_start() {
  local rev="" from=master task="" overlay=0
  while [ $# -gt 0 ]; do
    case "$1" in
      --from) from=$2; shift 2 ;;
      --overlay-scripts) overlay=1; shift ;;
      --task) task=$2; shift 2 ;;
      -*) die "unknown option $1" ;;
      *) [ -z "$rev" ] || die "one <rev>"; rev=$1; shift ;;
    esac
  done
  [ -n "$rev" ] || die "usage: start <rev> --task <id> [--from <commit>]"
  [ -n "$task" ] || die "start needs --task <id> (e.g. '#109'): the commits name it"
  from=$(git -C "$main" rev-parse --verify "$from^{commit}")
  local old
  old=$(git -C "$main" show "$from:proof/lake-manifest.json" | python3 -c '
import json, sys
for p in json.load(sys.stdin).get("packages", []):
    if p.get("name", "").strip("«»") == "con-leche":
        print(p["rev"])')
  [ -n "$old" ] || die "no con-leche pin at $from"

  # 1. the new commit, resolved in a private copy of the con-leche checkout
  #    (a fresh clone when no tree has one yet)
  local shared="" stage
  if [ -d "$main/proof/.lake/packages" ]; then
    shared=$(cd "$main/proof/.lake/packages" && pwd -P)
  fi
  stage="$TMP/bump-staging-$$"
  rm -rf "$stage"; mkdir -p "$stage"
  if [ -n "$shared" ] && [ -d "$shared/con-leche" ]; then
    cp -a --reflink=auto "$shared/con-leche" "$stage/con-leche"
    [ -z "$(git -C "$stage/con-leche" status --porcelain --untracked-files=no)" ] \
      || { rm -rf "$stage"; die "the shared con-leche checkout has local modifications"; }
  else
    local url
    url=$(git -C "$main" show "$from:proof/lake-manifest.json" | python3 -c '
import json, sys
for p in json.load(sys.stdin).get("packages", []):
    if p.get("name", "").strip("«»") == "con-leche":
        print(p["url"])')
    say "no shared con-leche checkout: cloning $url"
    git clone --quiet "$url" "$stage/con-leche"
  fi
  git -C "$stage/con-leche" fetch --quiet origin
  local new
  if [ "$rev" = master ]; then rev=origin/master; fi
  new=$(git -C "$stage/con-leche" rev-parse --verify --quiet "$rev^{commit}") \
    || { rm -rf "$stage"; die "con-leche has no commit $rev"; }
  [ "$new" != "$old" ] || { rm -rf "$stage"; die "con-leche is already pinned at ${new:0:8} on $from"; }
  short=${new:0:8}
  state="$TMP/bump-$short"
  wt="$TMP/wt-bump-$short"
  [ ! -e "$state" ] && [ ! -e "$wt" ] || { rm -rf "$stage"; die "bump $short exists already ($state, $wt)"; }

  # A sync that also MOVES THE TOOLCHAIN (task #110): con-leche's
  # `lean-toolchain` at the new commit is not `proof/`'s.  Then the old
  # package set (its Mathlib, its Aeneas build) is of no use, and the bump
  # gets the new toolchain's own `_tmp/aeneas-lean-<tag>` instead of a copy:
  # `setup-aeneas-lean.sh` builds it beside the old one, which the other
  # worktrees keep reading.  Nobody else reads the new directory until the
  # bump lands, so its con-leche checkout is the bump's to move.
  local oldtc newtc move=0
  oldtc=$(git -C "$main" show "$from:proof/lean-toolchain" | tr -d '[:space:]')
  newtc=$(git -C "$stage/con-leche" show "$new:lean-toolchain" | tr -d '[:space:]')
  [ "$oldtc" = "$newtc" ] || move=1
  if [ "$move" -eq 0 ]; then
    [ -n "$shared" ] || { rm -rf "$stage"; die "no shared packages ($main/proof/.lake/packages): run scripts/setup-aeneas-lean.sh and lake build in the main tree's proof/ first"; }
    say "private packages: reflink copy of $shared"
    rm -rf "$stage/con-leche"
    cp -a --reflink=auto "$shared" "$stage/packages"
  else
    say "toolchain move: $oldtc -> $newtc"
  fi
  mv "$stage" "$state"
  cat > "$state/state" <<EOF
new=$new
old=$old
from=$from
branch=bump-$short
task='$task'
move=$move
oldtc=$oldtc
newtc=$newtc
EOF
  local branch="bump-$short"

  # 2. the worktree
  say "worktree $wt on $branch off ${from:0:8}"
  git -C "$main" worktree add --quiet "$wt" -b "$branch" "$from"
  ln -s "$TMP" "$wt/_tmp"
  mkdir -p "$wt/proof/.lake"
  if [ "$overlay" -eq 1 ]; then
    # Testing only (task #108's dry runs): a --from commit older than these
    # scripts gets this tree's scripts/, committed on the throwaway branch.
    # The programs only: the data files beside them (`*.txt` — the link
    # expectation, the skip and allow lists) describe the old tree.
    (cd "$here/scripts" && find . -name '*.txt' -prune -o -type f -print0 \
       | xargs -0 cp --parents -t "$wt/scripts/")
    git -C "$wt" add -A scripts
    git -C "$wt" commit --quiet -m "Dry run: scripts/ from $(git -C "$here" rev-parse --short HEAD) (bump-con-leche.sh --overlay-scripts)"
  fi
  if [ "$move" -eq 0 ]; then
    ln -s "$state/packages" "$wt/proof/.lake/packages"
  else
    # the toolchain and the Aeneas path in the working tree (the toolchain is
    # committed with step 6; the lakefile and manifest go with the pin), then
    # the new package set, with the staged con-leche checkout in it
    local tag=${newtc##*:}
    echo "$newtc" > "$wt/proof/lean-toolchain"
    sed -i -E 's#^path = "\.\./_tmp/aeneas-lean[^"]*"#path = "../_tmp/aeneas-lean-'"$tag"'"#' "$wt/proof/lakefile.toml"
    say "scripts/setup-aeneas-lean.sh for $newtc (fetches Mathlib $tag)"
    (cd "$wt" && git submodule update --init --quiet vendor/aeneas && scripts/setup-aeneas-lean.sh) \
      > "$state/setup-aeneas-lean.log" 2>&1 \
      || { tail -20 "$state/setup-aeneas-lean.log"; die "setup-aeneas-lean.sh failed ($state/setup-aeneas-lean.log)"; }
    (cd "$TMP/aeneas-lean-$tag" && lake exe cache get) >> "$state/setup-aeneas-lean.log" 2>&1 || true
    local pk="$TMP/aeneas-lean-$tag/.lake/packages"
    if [ -d "$pk/con-leche" ]; then
      rm -rf "$state/con-leche"
      git -C "$pk/con-leche" fetch --quiet origin
    else
      mv "$state/con-leche" "$pk/con-leche"
    fi
    ln -s "$pk" "$state/packages"
  fi

  # 3. the old pin: master's binary, coverage
  local cl="$state/packages/con-leche"
  git -C "$cl" -c advice.detachedHead=false checkout --quiet --detach "$old"
  master_binary "$from"
  (cd "$wt" && python3 scripts/provenance.py coverage > "$state/coverage-old.txt" || true)

  # 4. the pin, in the working tree only
  say "proof/lakefile.toml rev -> $new; lake update con-leche"
  python3 - "$wt/proof/lakefile.toml" "$new" <<'PY'
import re, sys
p, new = sys.argv[1], sys.argv[2]
s = open(p, encoding="utf-8").read()
blocks = list(re.finditer(r"\[\[require\]\]\s*\n((?:(?!\[).*\n?)*)", s))
for m in blocks:
    if re.search(r'^name\s*=\s*"con-leche"', m.group(1), re.M):
        body = re.sub(r'^(rev\s*=\s*")[^"]*(")', r"\g<1>%s\g<2>" % new, m.group(1),
                      count=1, flags=re.M)
        s = s[:m.start(1)] + body + s[m.end(1):]
        break
else:
    sys.exit("no con-leche [[require]] in " + p)
open(p, "w", encoding="utf-8").write(s)
PY
  # (a toolchain move re-resolves everything: the manifest's Mathlib and
  # friends follow the new Aeneas lakefile, not only con-leche)
  local -a upd=(lake update con-leche)
  [ "$move" -eq 0 ] || upd=(lake update)
  (cd "$wt/proof" && "${upd[@]}") > "$state/lake-update.log" 2>&1 \
    || { tail -20 "$state/lake-update.log"; die "lake update con-leche failed ($state/lake-update.log)"; }
  [ "$(manifest_rev "$wt/proof/lake-manifest.json")" = "$new" ] \
    || die "lake update left the manifest at $(manifest_rev "$wt/proof/lake-manifest.json")"
  [ "$(git -C "$cl" rev-parse HEAD)" = "$new" ] || die "the private con-leche is not at $new"

  # 5. the classification and the rest of the work order
  say "provenance.py update --auto"
  local rc=0
  (cd "$wt" && python3 scripts/provenance.py update --auto --tsv "$state/findings.tsv") \
    > "$state/update.log" 2>&1 || rc=$?
  [ "$rc" -le 1 ] || { tail -20 "$state/update.log"; die "provenance.py update failed"; }
  (cd "$wt" && python3 scripts/provenance.py coverage > "$state/coverage-new.txt" || true)
  say "overview-links.sh --follow"
  (cd "$wt" && scripts/overview-links.sh --follow) > "$state/links.log" 2>&1 || true
  local g1 g2
  g1=$(cd "$wt" && scripts/gen-prelude.sh --check > "$state/gen-prelude.log" 2>&1 && echo same || echo CHANGED)
  g2=$(cd "$wt" && scripts/gen-prelude-lean.sh --check > "$state/gen-prelude-lean.log" 2>&1 && echo same || echo CHANGED)
  echo "gen-prelude $g1, gen-prelude-lean $g2" > "$state/generators.txt"
  say "diff-e2e.sh with master's binary at the new pin"
  (cd "$wt" && LOG="$state/e2e-master.log" scripts/diff-e2e.sh --timeout=60 \
      --bin="$state/con-ron-master") > "$state/e2e-master.out" 2>&1 || true

  # 6. commit (never the pin files), then the work order
  git -C "$wt" add -A
  git -C "$wt" reset --quiet -- proof/lakefile.toml proof/lake-manifest.json vendor/aeneas
  if ! git -C "$wt" diff --cached --quiet; then
    git -C "$wt" commit --quiet -m "Task $task: provenance update --auto at con-leche ${short} (pin uncommitted); anchors follow their text

The mechanical buckets of scripts/provenance.py update --auto applied; the
markers left are the work order (scripts/bump-con-leche.sh status).

Co-Authored-By: Claude Opus 5.5 (1M context) <noreply@anthropic.com>"
  fi
  work_order | tee "$state/work-order.txt"
}

uncovered() { sed -n 's/^    uncovered \([^ ]*\) \([^:]*\):.*/\1 \2/p' "$1" | sort -u; }

work_order() {
  local cl="$state/packages/con-leche"
  echo
  echo "# con-leche sync ${old:0:8} -> ${new:0:8} (task $task), worktree $wt"
  echo
  echo "## Upstream: $(git -C "$cl" rev-list --count "$old..$new") commit(s)"
  git -C "$cl" log --oneline --first-parent -40 "$old..$new"
  echo
  git -C "$cl" diff --shortstat "$old" "$new" -- ConLeche Main.lean | sed 's/^ */executed tiers and the rest of ConLeche\/, Main.lean: /'
  echo "(read upstream DESIGN.md's task sections between the two commits first: §7 step 1)"
  echo
  echo "## Findings ($state/findings.tsv)"
  sed -n '/^update --auto:/,$p' "$state/update.log"
  echo
  echo "## Markers left, by part"
  awk -F'\t' 'NR > 1 && $1 !~ /^(doc-only|moved|moved-doc)$/ {print "  " $1 "\t" $2 "\t" $3 "\t" $4 "\t" $5}' \
    "$state/findings.tsv" | sort -t$'\t' -k2,2 -k3,3
  echo
  echo "## Coverage"
  grep '^TOTAL' "$state/coverage-old.txt" | sed 's/^/  at the old pin: /'
  grep '^TOTAL' "$state/coverage-new.txt" | sed 's/^/  at the new pin: /'
  echo "  uncovered at the new pin and not at the old (port, or skip with a reason):"
  comm -13 <(uncovered "$state/coverage-old.txt") <(uncovered "$state/coverage-new.txt") | sed 's/^/    /'
  grep -E '^(STALE|REDUNDANT)' "$state/coverage-new.txt" | sed 's/^/  /' || true
  echo
  echo "## diff-e2e.sh, master's binary ($(cut -c1-8 "$state/con-ron-master.commit")) at the new pin"
  sed -n '/^diff-e2e (/,$p' "$state/e2e-master.out" | sed 's/^/  /'
  grep -oE '(DIFFER|TIMEOUT) +[^ ]+' "$state/e2e-master.out" | sed -n '1,40s/^/    /p' || true
  echo
  echo "## Generated files and links"
  echo "  $(cat "$state/generators.txt") (CHANGED: run the generator, extract, re-gate; gen-pins needs a build: run it with the gates)"
  head -1 "$state/links.log" | sed 's/^/  /'
  sed -n '2,$p' "$state/links.log" | grep -E '^  (changed|new) ' | sed 's/^/  /' || true
  echo
  echo "## Next (DESIGN.md §7)"
  echo "  port in order — Rust, measure, twin, Theorem 1, Theorem 2 — deleting each marker as it is reconciled;"
  echo "  scripts/bump-con-leche.sh status                     # what is left"
  echo "  scripts/bump-con-leche.sh measure                    # once, when the Rust is final"
  echo "  git merge master; LAKE_JOBS=4 scripts/gates.sh       # green, on a clean tree"
  echo "  scripts/bump-con-leche.sh pin                        # the LAST commit"
  echo "  LAKE_JOBS=4 scripts/gates.sh; scripts/bump-con-leche.sh land"
}

# ---------------------------------------------------------------- status
cmd_status() {
  resolve_short "${1-}"
  echo "bump ${old:0:8} -> ${new:0:8} (task $task), $wt on $branch"
  (cd "$wt" && python3 scripts/provenance.py check | tail -1) || true
  local n
  n=$(cd "$wt" && python3 scripts/provenance.py check | grep -c '^UNRECONCILED' || true)
  echo "markers left: $n"
  (cd "$wt" && python3 scripts/provenance.py coverage > "$state/coverage-now.txt" || true)
  grep '^TOTAL' "$state/coverage-now.txt" || true
  echo "new uncovered declarations still uncovered:"
  comm -12 <(comm -13 <(uncovered "$state/coverage-old.txt") <(uncovered "$state/coverage-new.txt")) \
           <(uncovered "$state/coverage-now.txt") | sed 's/^/  /'
  (cd "$wt" && python3 scripts/pin-last.py) || true
}

# ---------------------------------------------------------------- measure
perf_field() { # <perf file> <event>
  grep -oP "^\s*[\d,]+(?=\s+$2)" "$1" 2>/dev/null | tr -d ' ,' || true
}
cmd_measure() {
  resolve_short "${1-}"
  [ -z "$(git -C "$wt" status --porcelain --untracked-files=no -- crates Cargo.toml Cargo.lock)" ] \
    || die "commit the crates first: the measurement names a commit"
  master_binary master
  say "building the branch's con-ron (release)"
  (cd "$wt" && cargo build --quiet --release -p con-ron) > "$state/branch-build.log" 2>&1 \
    || { tail -20 "$state/branch-build.log"; die "the branch's build failed"; }
  local head
  head=$(git -C "$wt" rev-parse HEAD)
  rm -rf "$state/perf-master" "$state/perf-branch"
  say "Init, con-ron, one worker: master's binary"
  CONRON="$state/con-ron-master" CONRON_SRC="$state/master-src" \
    "$wt/scripts/bench-baselines.sh" --bin con-ron --export init --runs 1 --out "$state/perf-master"
  say "Init, con-ron, one worker: the branch's binary"
  CONRON="$wt/target/release/con-ron" CONRON_SRC="$wt" \
    "$wt/scripts/bench-baselines.sh" --bin con-ron --export init --runs 1 --out "$state/perf-branch"
  local mi bi mc bc ma ba
  mi=$(perf_field "$state/perf-master/con-ron-init-r1.perf" instructions:u)
  bi=$(perf_field "$state/perf-branch/con-ron-init-r1.perf" instructions:u)
  mc=$(perf_field "$state/perf-master/con-ron-init-r1.perf" cycles:u)
  bc=$(perf_field "$state/perf-branch/con-ron-init-r1.perf" cycles:u)
  ma=$(grep -oP 'accepted \K\d+' "$state/perf-master/con-ron-init-r1.out" | tail -1 || true)
  ba=$(grep -oP 'accepted \K\d+' "$state/perf-branch/con-ron-init-r1.out" | tail -1 || true)
  [ -n "$mi" ] && [ -n "$bi" ] || die "a run produced no instruction count (see $state/perf-*)"
  python3 - "$mi" "$bi" "$mc" "$bc" "$ma" "$ba" "$(cut -c1-8 "$state/con-ron-master.commit")" "${head:0:8}" \
    > "$state/measure.md" <<'PY'
import sys
mi, bi, mc, bc, ma, ba, m, b = sys.argv[1:]
g = lambda n: f"{int(n):,}".replace(",", " ") if n else "?"
d = (int(bi) - int(mi)) / int(mi) * 100
print(f"`Init`, `--verified --jobs=1`, `perf stat -e instructions:u,cycles:u`, one run each "
      f"(§7.x; `scripts/bump-con-leche.sh measure`), accepting {g(ma)} / {g(ba)}:")
print()
print("| binary | instructions:u | cycles:u |")
print("|---|---:|---:|")
print(f"| master `{m}` | {g(mi)} | {g(mc)} |")
print(f"| this branch `{b}` | **{g(bi)}** ({'+' if d >= 0 else '−'}{abs(d):.3f} %) | {g(bc)} |")
PY
  cat "$state/measure.md"
  { echo "measured_head=$head"; echo "measured_crates=$(git -C "$wt" rev-parse "HEAD:crates")"; } > "$state/measured"
  [ "$ma" = "$ba" ] || echo "WARNING: the two binaries accept different counts ($ma, $ba)"
}

# ---------------------------------------------------------------- pin
cmd_pin() {
  resolve_short "${1-}"
  [ "$(manifest_rev "$wt/proof/lake-manifest.json")" = "$new" ] || die "the working manifest is not at $new"
  grep -q "rev = \"$new\"" "$wt/proof/lakefile.toml" || die "proof/lakefile.toml's rev is not $new"
  [ "$(git -C "$wt" show HEAD:proof/lake-manifest.json | python3 -c '
import json, sys
for p in json.load(sys.stdin).get("packages", []):
    if p.get("name", "").strip("«»") == "con-leche":
        print(p["rev"])')" != "$new" ] || die "the pin is committed already"
  local dirty
  dirty=$(git -C "$wt" status --porcelain --untracked-files=no | grep -v -E ' proof/(lakefile\.toml|lake-manifest\.json)$' || true)
  [ -z "$dirty" ] || die "commit the rest first; uncommitted besides the pin files:
$dirty"
  (cd "$wt" && scripts/overview-links.sh --follow) || true
  git -C "$wt" add -- README.md OVERVIEW.md scripts/overview-links-expected.txt
  if ! git -C "$wt" diff --cached --quiet; then
    git -C "$wt" commit --quiet -m "Task $task: anchors follow their unchanged text at con-leche ${short} (numbers and pins only)

Co-Authored-By: Claude Opus 5.5 (1M context) <noreply@anthropic.com>"
  fi
  git -C "$wt" add -- proof/lakefile.toml proof/lake-manifest.json
  git -C "$wt" commit --quiet -m "Task $task: pin con-leche at ${short}

The last commit of the sync (DESIGN.md §7): proof/lakefile.toml and
proof/lake-manifest.json, nothing else.

Co-Authored-By: Claude Opus 5.5 (1M context) <noreply@anthropic.com>"
  (cd "$wt" && python3 scripts/pin-last.py --tip-is-pin)
  echo "next: LAKE_JOBS=4 scripts/gates.sh, then scripts/bump-con-leche.sh land"
}

# ---------------------------------------------------------------- land
cmd_land() {
  local arg="" nomeasure=0
  for a in "$@"; do
    case "$a" in --no-measure) nomeasure=1 ;; *) arg=$a ;; esac
  done
  resolve_short "$arg"
  [ -z "$(git -C "$wt" status --porcelain --untracked-files=no)" ] || die "$wt has uncommitted changes"
  (cd "$wt" && python3 scripts/pin-last.py --tip-is-pin) || die "the pin commit must be the tip, and the only commit moving the pin"
  git -C "$wt" merge-base --is-ancestor master HEAD || die "master is not merged into $branch; merge it, re-gate, pin"
  local head key
  head=$(git -C "$wt" rev-parse HEAD)
  key=$(printf '%s' "$(cd "$wt" && pwd)" | sha256sum | cut -c1-12)
  [ "$(cat "$TMP/gates-$key/green" 2>/dev/null)" = "$head" ] \
    || die "no green scripts/gates.sh run at ${head:0:8} (_tmp/gates-$key/green); run LAKE_JOBS=4 scripts/gates.sh in $wt"
  if [ "$nomeasure" -eq 0 ]; then
    [ -f "$state/measured" ] || die "not measured: scripts/bump-con-leche.sh measure (or --no-measure, and say why)"
    local measured_head="" measured_crates=""
    # shellcheck disable=SC1091
    . "$state/measured"
    [ "$measured_crates" = "$(git -C "$wt" rev-parse HEAD:crates)" ] \
      || die "crates/ changed since the measurement at ${measured_head:0:8}; measure again"
  fi
  [ "$(git -C "$main" symbolic-ref --quiet --short HEAD)" = master ] || die "the main tree is not on master"
  [ -z "$(git -C "$main" status --porcelain --untracked-files=no)" ] || die "the main tree has uncommitted changes"

  say "fast-forward master to $branch"
  git -C "$main" merge --quiet --ff-only "$branch" || die "not a fast-forward; merge master into $branch, re-gate, retry"
  say "seeding the shared Lake cache from $wt (the private packages are the bump's own)"
  (cd "$wt/proof" && LAKE_ARTIFACT_CACHE=true LAKE_RESTORE_ARTIFACTS=true lake build) \
    > "$state/seed.log" 2>&1 || echo "WARNING: seeding failed ($state/seed.log); the main tree will build what it misses"
  say "dropping the worktree"
  (cd "$main" && scripts/drop-worktree.sh "$wt")
  say "deleting $state (the private packages, the logs)"
  rm -rf "$state"
  if [ "${move:-0}" -eq 1 ]; then
    # the main tree follows the toolchain move: its packages link goes to the
    # new toolchain's Aeneas directory (the one the bump built and used)
    say "the main tree follows the toolchain move ($oldtc -> $newtc)"
    (cd "$main" && git submodule update --init --quiet vendor/aeneas && scripts/setup-aeneas-lean.sh --no-update) \
      || echo "WARNING: scripts/setup-aeneas-lean.sh failed in $main; run it by hand"
    echo "The old toolchain's _tmp/aeneas-lean-${oldtc##*:} stays for the worktrees still on it;"
    echo "delete it (and sweep _tmp/lake-cache) once none is."
  fi
  say "moving the shared con-leche checkout"
  if ! (cd "$main" && scripts/sync-shared-con-leche.sh); then
    echo "NOT MOVED: the shared con-leche checkout stays at ${old:0:8} for now."
    echo "Run \`scripts/sync-shared-con-leche.sh\` in $main once the worktrees it names have merged master."
  fi
  echo "landed: master at $(git -C "$main" rev-parse --short HEAD), con-leche ${new:0:8}"
}

# ---------------------------------------------------------------- abort
cmd_abort() {
  local arg="" yes=0
  for a in "$@"; do case "$a" in --yes) yes=1 ;; *) arg=$a ;; esac; done
  resolve_short "$arg"
  [ "$yes" -eq 1 ] || die "abort deletes $wt, branch $branch and $state; pass --yes"
  git -C "$main" worktree remove --force "$wt" 2>/dev/null || true
  git -C "$main" branch -D "$branch" >/dev/null 2>&1 || true
  local key
  key=$(printf '%s' "$wt" | sha256sum | cut -c1-12)
  for d in "$TMP"/*-"$key"; do [ -e "$d" ] && rm -rf "$d"; done
  rm -rf "$state"
  echo "aborted bump $short: worktree, branch and scratch deleted"
}

cmd=${1-}; shift || true
case "$cmd" in
  start) cmd_start "$@" ;;
  status) cmd_status "$@" ;;
  order) resolve_short "${1-}"; work_order | tee "$state/work-order.txt" ;;
  measure) cmd_measure "$@" ;;
  pin) cmd_pin "$@" ;;
  land) cmd_land "$@" ;;
  abort) cmd_abort "$@" ;;
  *) sed -n '2,60p' "$0" | sed 's/^# \{0,1\}//'; exit 2 ;;
esac
