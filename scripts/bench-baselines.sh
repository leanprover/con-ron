#!/usr/bin/env bash
# scripts/bench-baselines.sh -- THE PERFORMANCE MATRIX: the one runner behind
# OVERVIEW section 9 (task #107; first written as the arena campaign's
# baseline harness, DESIGN.md "Task #97-P6-3 -- the baselines").
#
# Refreshing OVERVIEW section 9 is one command:
#
#     scripts/bench-baselines.sh --build --render --task '#NNN'
#
# which builds the binaries and ensures the inputs (the exports through
# `scripts/corpus.sh`, at the project toolchain; nanoda through
# `scripts/build-nanoda.sh`), runs the matrix into --out, and then runs
# `scripts/perf-table.py` on the raw files, rewriting the marked region of
# OVERVIEW.md and printing the raw-numbers block for DESIGN.md's task
# section.  Nothing in that section is typed by hand.
#
# One run is `time -v` around `perf stat -e instructions:u,cycles:u` around
# `timeout`, in a subshell that has set `ulimit -v`.  CLAUDE.md's measuring
# rules apply: `instructions:u` is the measure of record, wall time is
# secondary and is only reported with a spread when the benchmark is small
# enough to repeat (that is `init`; `core` and `mathlib` get one run each and
# their wall is indicative only), and every checker runs under `timeout` AND
# `ulimit -v` so a runaway dies instead of taking the machine down.  One
# checker runs at a time; `init`'s runs are interleaved (round r runs every
# binary once) so that a change in machine load spreads over all rows.
#
# The rows (`--bin`):
#   con-ron     con-ron --verified --jobs=1 --progress=1000000.  A bare
#               `--jobs=1` bypasses the driver, and the campaign is measured
#               through the driver, so the heartbeat flag stays on (at a
#               stride large enough that the printing is noise).
#   con-ron-j8  con-ron --verified --jobs=8 --progress=1000000.
#   con-leche   con-leche --verified --jobs=1, built at con-ron's pin
#               (`scripts/provenance.py dir`'s checkout) by `lake build
#               con-leche` in a private clone under --out (never inside the
#               shared package directory), as task #97-REMEASURE did.
#   nanoda      nanoda_bin with `num_threads: 0` (nanoda's serial default),
#               the build of DESIGN.md "Task #97-P6-3" ($NANODA).
#
# Usage:
#   scripts/bench-baselines.sh [--bin NAME]... [--export NAME]... [--runs N]
#                              [--out DIR] [--build] [--render --task ID]
#                              [--list] [--dry-run]
#
#   --bin      con-ron | con-ron-j8 | con-leche | nanoda   (default: all four)
#   --export   init | core | mathlib       (default: init mathlib, the table's)
#   --runs N   runs per (bin, export) pair; default is the per-export default
#              (init 3, core 1, mathlib 1)
#   --out DIR  where the raw files land (default: _tmp/perf)
#   --build    first build con-ron (`cargo build --release -p con-ron`) and
#              con-leche (the private clone at the pin), make the matrix's
#              exports (`scripts/corpus.sh --steps=1 --exports=...`, which
#              re-exports one whose `<name>.toolchain` stamp is not the
#              project toolchain) and nanoda (`scripts/build-nanoda.sh`);
#              each skips what is already there.  Without it the binaries
#              and exports must already be there
#   --render   afterwards run `scripts/perf-table.py --overview OVERVIEW.md
#              --task ID --raw DIR` (needs --task)
#   --task ID  the DESIGN.md task that records this refresh, e.g. '#107'
#   --list     print the matrix and the limits, run nothing
#   --dry-run  print each command instead of running it
#   --limit-kb KB
#              DIAGNOSTIC ONLY: override the per-run `ulimit -v` cap.  A
#              number produced this way is not a baseline number -- the caps
#              are the budget, and a checker that does not fit one is a bug
#              to fix (CLAUDE.md), not a cap to raise.  Every run it makes is
#              tagged `-limit<KB>` in its file names, which the renderer
#              ignores.
#
# Every run writes <out>/<bin>-<export>-r<N>.{perf,time,out,err,exit,load}
# (`.load` is /proc/loadavg at the start of the run).  The matrix also
# writes <out>/identity.json (the date, and the commit and md5 of every
# binary) and <out>/matrix.{start,end} (epoch seconds).
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
CORPUS="${CORPUS:-$ROOT/_tmp/corpus}"
NANODA="${NANODA:-$ROOT/_tmp/t97/nanoda-build/target/release/nanoda_bin}"
# `CONRON`/`CONRON_SRC` name another con-ron binary and the tree it was built
# from (task #108: `scripts/bump-con-leche.sh measure` runs master's binary and
# the branch's one after the other).  `--build` always builds `$ROOT`'s.
CONRON="${CONRON:-$ROOT/target/release/con-ron}"
CONRON_SRC="${CONRON_SRC:-$ROOT}"
OUT="$ROOT/_tmp/perf"

# GNU time, not the shell builtin: `time -v` is what reports peak RSS.
GNUTIME="${GNUTIME:-}"
if [[ -z $GNUTIME ]]; then
  # `command -v time` answers with the shell keyword; look for a real file.
  for c in /usr/bin/time $(type -ap time 2>/dev/null || true); do
    [[ -x $c ]] && "$c" -v true >/dev/null 2>&1 && { GNUTIME=$c; break; }
  done
fi

BINS=(); EXPORTS=(); RUNS=""; LIST=0; DRY=0; LIMIT_KB=""; BUILD=0
RENDER=0; TASK=""
while [[ $# -gt 0 ]]; do
  case "$1" in
    --bin)     BINS+=("$2"); shift 2 ;;
    --bin=*)   BINS+=("${1#*=}"); shift ;;
    --export)  EXPORTS+=("$2"); shift 2 ;;
    --export=*) EXPORTS+=("${1#*=}"); shift ;;
    --runs)    RUNS="$2"; shift 2 ;;
    --runs=*)  RUNS="${1#*=}"; shift ;;
    --out)     OUT="$2"; shift 2 ;;
    --out=*)   OUT="${1#*=}"; shift ;;
    --limit-kb)   LIMIT_KB="$2"; shift 2 ;;
    --limit-kb=*) LIMIT_KB="${1#*=}"; shift ;;
    --build)   BUILD=1; shift ;;
    --render)  RENDER=1; shift ;;
    --task)    TASK="$2"; shift 2 ;;
    --task=*)  TASK="${1#*=}"; shift ;;
    --list)    LIST=1; shift ;;
    --dry-run) DRY=1; shift ;;
    -h|--help) sed -n '2,73p' "${BASH_SOURCE[0]}"; exit 0 ;;
    *) echo "bench-baselines.sh: unknown argument $1" >&2; exit 2 ;;
  esac
done
[[ ${#BINS[@]}    -eq 0 ]] && BINS=(con-ron con-ron-j8 con-leche nanoda)
[[ ${#EXPORTS[@]} -eq 0 ]] && EXPORTS=(init mathlib)
[[ $RENDER -eq 1 && -z $TASK ]] && { echo "bench-baselines.sh: --render needs --task" >&2; exit 2; }
OUT="$(mkdir -p "$OUT" && cd "$OUT" && pwd)"
CONLECHE_SRC="${CONLECHE_SRC:-$OUT/con-leche}"
CONLECHE="$CONLECHE_SRC/.lake/build/bin/con-leche"

# Per-run address-space cap (KB) and timeout (s).  Address space is not
# memory: Lean reserves address space per thread and con-ron's pool reserves
# a 1 GiB stack per worker even at --jobs=1, so the 2.6 GB `init` cap this
# script once had (3x con-leche's 0.48 GB peak RSS) killed both con-leche
# ("failed to create thread") and con-ron ("cannot spawn a check worker");
# task #97-REMEASURE found it.  The caps are therefore the ones every run
# since then used: 8 GiB for one worker on `init`/`core`, 27 000 000 KB for
# eight workers (8 GiB of stack reservation alone), 27 GiB on `mathlib`.
# CLAUDE.md's 3x-con-leche budget is checked on peak RSS by
# `scripts/perf-table.py`, which names any row that exceeds it.  A checker
# that does not fit its cap is a bug to investigate, never a reason to raise
# the cap.
limit_kb() {
  local bin="$1" exp="$2"
  case "$exp" in
    init|core) if [[ $bin == con-ron-j8 ]]; then echo 27000000; else echo 8388608; fi ;;
    mathlib)   echo 28311552 ;;
    *) echo "bench-baselines.sh: unknown export $exp" >&2; exit 2 ;;
  esac; }
timeout_s() { case "$1" in
    init) echo 1800 ;; core) echo 3600 ;; mathlib) echo 9000 ;;
  esac; }
# Wall is only meaningful from several runs of a benchmark small enough to
# repeat (CLAUDE.md): `init` is, the other two are not.
default_runs() { case "$1" in init) echo 3 ;; *) echo 1 ;; esac; }

if [[ $LIST -eq 1 ]]; then
  printf '%-12s %-8s %-6s %12s %8s\n' bin export runs 'ulimit -v' timeout
  for e in "${EXPORTS[@]}"; do for b in "${BINS[@]}"; do
    printf '%-12s %-8s %-6s %12s %8s\n' \
      "$b" "$e" "${RUNS:-$(default_runs "$e")}" "${LIMIT_KB:-$(limit_kb "$b" "$e")} KB" "$(timeout_s "$e")s"
  done; done
  exit 0
fi

[[ -n $GNUTIME ]] || { echo "bench-baselines.sh: GNU time not found; set GNUTIME=" >&2; exit 2; }

has_bin() { local b; for b in "${BINS[@]}"; do [[ $b == "$1" ]] && return 0; done; return 1; }

# ---- building -------------------------------------------------------------
if [[ $BUILD -eq 1 && $DRY -eq 0 ]]; then
  if has_bin con-ron || has_bin con-ron-j8; then
    echo "== cargo build --release -p con-ron" >&2
    (cd "$ROOT" && cargo build --release -p con-ron)
  fi
  if has_bin con-leche; then
    pkg="$(cd "$ROOT" && python3 scripts/provenance.py dir)"
    # The pin is the manifest's rev, not whatever the shared checkout has.
    rev="$(cd "$ROOT" && python3 scripts/provenance.py pin)"
    if [[ ! -d $CONLECHE_SRC/.git ]]; then
      echo "== cloning con-leche $rev into $CONLECHE_SRC" >&2
      git clone --quiet --no-checkout "$pkg" "$CONLECHE_SRC"
    fi
    git -C "$CONLECHE_SRC" fetch --quiet "$pkg" "$rev" 2>/dev/null || true
    git -C "$CONLECHE_SRC" checkout --quiet --detach "$rev"
    echo "== lake build con-leche (in $CONLECHE_SRC)" >&2
    (cd "$CONLECHE_SRC" && lake build con-leche)
  fi
  # The inputs (task #114): after a wiped `_tmp/` or a toolchain move this
  # is what keeps the refresh one command.
  echo "== scripts/corpus.sh --steps=1 --exports=$(IFS=,; echo "${EXPORTS[*]}") $CORPUS" >&2
  "$ROOT/scripts/corpus.sh" --steps=1 --exports="$(IFS=,; echo "${EXPORTS[*]}")" "$CORPUS"
  if has_bin nanoda; then
    NANODA="$NANODA" "$ROOT/scripts/build-nanoda.sh"
  fi
fi

# ---- identities -----------------------------------------------------------
commit_of() { git -C "$1" rev-parse HEAD 2>/dev/null || echo unknown; }
dirty_of()  { if [[ -n $(git -C "$1" status --porcelain --untracked-files=no 2>/dev/null) ]]; then echo true; else echo false; fi; }
md5_of()    { if [[ -f $1 ]]; then md5sum "$1" | cut -d' ' -f1; else echo missing; fi; }
NANODA_SRC="$(cd "$(dirname "$NANODA")/../.." 2>/dev/null && pwd || echo "$NANODA")"

if [[ $DRY -eq 0 ]]; then
  for f in "${EXPORTS[@]}"; do
    [[ -f $CORPUS/$f.ndjson ]] || { echo "bench-baselines.sh: missing export $CORPUS/$f.ndjson (scripts/corpus.sh)" >&2; exit 2; }
  done
  has_bin con-leche && { [[ -x $CONLECHE ]] || { echo "bench-baselines.sh: $CONLECHE not built (--build)" >&2; exit 2; }; }
  { has_bin con-ron || has_bin con-ron-j8; } && { [[ -x $CONRON ]] || { echo "bench-baselines.sh: $CONRON not built (--build)" >&2; exit 2; }; }
  has_bin nanoda && { [[ -x $NANODA ]] || { echo "bench-baselines.sh: $NANODA not built; see DESIGN.md \"Task #97-P6-3\"" >&2; exit 2; }; }
  cat > "$OUT/identity.json" <<EOF
{"date": "$(date -u +%Y-%m-%d)",
 "con-ron":   {"commit": "$(commit_of "$CONRON_SRC")", "dirty": $(dirty_of "$CONRON_SRC"), "md5": "$(md5_of "$CONRON")"},
 "con-leche": {"commit": "$(commit_of "$CONLECHE_SRC")", "dirty": $(dirty_of "$CONLECHE_SRC"), "md5": "$(md5_of "$CONLECHE")"},
 "nanoda":    {"commit": "$(commit_of "$NANODA_SRC")", "dirty": $(dirty_of "$NANODA_SRC"), "md5": "$(md5_of "$NANODA")"},
 "exports":   {$(for e in "${EXPORTS[@]}"; do printf '"%s": %s, ' "$e" "$(head -1 "$CORPUS/$e.ndjson")"; done | sed 's/, $//')},
 "nproc": $(nproc)}
EOF
  date +%s > "$OUT/matrix.start"
fi

# ---- the command for one (bin, export) pair, written into the array CMD ----
build_cmd() {
  local bin="$1" exp="$2" file="$CORPUS/$exp.ndjson"
  case "$bin" in
    con-ron)    CMD=("$CONRON" --verified --jobs=1 --progress=1000000 "$file") ;;
    con-ron-j8) CMD=("$CONRON" --verified --jobs=8 --progress=1000000 "$file") ;;
    con-leche)  CMD=("$CONLECHE" --verified --jobs=1 "$file") ;;
    nanoda)
      # nanoda has no CLI: one JSON config per run.  `unsafe_permit_all_axioms`
      # (with `unpermitted_axiom_hard_error: false`, which it requires) matches
      # nomeata's own Mathlib measurement, and so do the two kernel extensions;
      # `num_threads: 0` is nanoda's serial default.
      local cfg="$OUT/nanoda-$exp.json"
      cat > "$cfg" <<EOF
{"export_file_path": "$file",
 "use_stdin": false,
 "unpermitted_axiom_hard_error": false,
 "unsafe_permit_all_axioms": true,
 "nat_extension": true,
 "string_extension": true,
 "num_threads": 0,
 "print_axioms": false,
 "print_success_message": true}
EOF
      CMD=("$NANODA" "$cfg") ;;
    *) echo "bench-baselines.sh: unknown bin $bin" >&2; exit 2 ;;
  esac
}

# ---- the matrix: per export, per round, per binary -------------------------
for exp in "${EXPORTS[@]}"; do
  n="${RUNS:-$(default_runs "$exp")}"
  to="$(timeout_s "$exp")"
  for ((r = 1; r <= n; r++)); do
    for bin in "${BINS[@]}"; do
      kb="${LIMIT_KB:-$(limit_kb "$bin" "$exp")}"
      sfx=""; [[ -n $LIMIT_KB ]] && sfx="-limit$LIMIT_KB"
      build_cmd "$bin" "$exp"
      tag="$OUT/$bin-$exp$sfx-r$r"
      if [[ $DRY -eq 1 ]]; then
        echo "( ulimit -v $kb; $GNUTIME -v -o $tag.time -- perf stat -e instructions:u,cycles:u -o $tag.perf -- timeout $to ${CMD[*]} > $tag.out 2> $tag.err )"
        continue
      fi
      echo "== $bin $exp run $r/$n (ulimit -v $kb KB, timeout ${to}s)" >&2
      cat /proc/loadavg > "$tag.load"
      rc=0
      ( ulimit -v "$kb"
        "$GNUTIME" -v -o "$tag.time" -- \
          perf stat -e instructions:u,cycles:u -o "$tag.perf" -- \
            timeout "$to" "${CMD[@]}" > "$tag.out" 2> "$tag.err"
      ) || rc=$?
      echo "$rc" > "$tag.exit"
      ins=$(grep -oP '^\s*[\d,]+(?=\s+instructions:u)' "$tag.perf" 2>/dev/null | tr -d ' ,' || true)
      cyc=$(grep -oP '^\s*[\d,]+(?=\s+cycles:u)'       "$tag.perf" 2>/dev/null | tr -d ' ,' || true)
      wall=$(grep -oP '^\s+\K[\d.]+(?= seconds time elapsed)' "$tag.perf" 2>/dev/null || true)
      rss=$(awk -F': ' '/Maximum resident set size/ {print $2}' "$tag.time" 2>/dev/null || true)
      echo "   exit=$rc instructions=$ins cycles=$cyc wall=${wall}s peakRSS=${rss}KB" >&2
      tail -1 "$tag.out" >&2 || true
    done
  done
done
[[ $DRY -eq 1 ]] && exit 0
date +%s > "$OUT/matrix.end"

if [[ $RENDER -eq 1 ]]; then
  python3 "$ROOT/scripts/perf-table.py" --overview "$ROOT/OVERVIEW.md" --task "$TASK" --raw "$OUT"
fi
