#!/usr/bin/env bash
# scripts/bench-baselines.sh -- the arena campaign's baseline harness
# (DESIGN.md section 8.6 P6 item 3, "Task #97-P6-3 -- the baselines").
#
# One run is `time -v` around `perf stat -e instructions:u,cycles:u` around
# `timeout`, in a subshell that has set `ulimit -v` -- the shape
# `_tmp/corpus/baseline.md` already used, plus cycles.  CLAUDE.md's measuring
# rules apply: `instructions:u` is the measure of record, wall time is
# secondary and is only reported with a spread when the benchmark is small
# enough to repeat (that is `init`; `core` and `mathlib` get one run each and
# their wall is indicative only), and every checker runs under `timeout` AND
# `ulimit -v` so a runaway dies instead of taking the machine down.
#
# The lane is single-threaded for both binaries.  For `con-ron` that is
# `--jobs=1 --progress=1000000`: a bare `--jobs=1`
# bypasses the driver, and the campaign is measured through the driver, so the
# heartbeat flag stays on (at a stride large enough that the printing is
# noise).  For nanoda it is `num_threads: 0` in the config file, which is
# nanoda's own serial default.  (Task #97-SWAP retired `con-ron-arena`: the
# arena IS `con-ron` now, so there are two binaries here and not three.)
#
# Usage:
#   scripts/bench-baselines.sh [--bin NAME]... [--export NAME]... [--runs N]
#                              [--out DIR] [--list] [--dry-run]
#
#   --bin      con-ron | nanoda                   (default: both)
#   --export   init | core | mathlib              (default: all three)
#   --runs N   runs per (bin, export) pair; default is the per-export default
#              (init 3, core 1, mathlib 1)
#   --out DIR  where the .perf/.time/.out/.err/.exit files land
#              (default: _tmp/t97/p6-3)
#   --list     print the matrix and the limits, run nothing
#   --dry-run  print each command instead of running it
#   --limit-kb KB
#              DIAGNOSTIC ONLY: override the per-export `ulimit -v` cap.  A
#              number produced this way is not a baseline number -- the caps
#              above are the budget, and a checker that does not fit one is a
#              bug to fix (CLAUDE.md), not a cap to raise.  The flag exists so
#              that "how much does it actually want?" can be answered, and
#              every run it makes is tagged `-limit<KB>` in its file names.
#
# Every run writes <out>/<bin>-<export>-r<N>.{perf,time,out,err,exit}.
# `--list` after a campaign prints nothing; read the files, or the table in
# DESIGN.md section "Task #97-P6-3".
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
CORPUS="${CORPUS:-$ROOT/_tmp/corpus}"
NANODA="${NANODA:-$ROOT/_tmp/t97/nanoda-build/target/release/nanoda_bin}"
OUT="$ROOT/_tmp/t97/p6-3"

# GNU time, not the shell builtin: `time -v` is what reports peak RSS.
GNUTIME="${GNUTIME:-}"
if [[ -z $GNUTIME ]]; then
  # `command -v time` answers with the shell keyword; look for a real file.
  for c in /usr/bin/time $(type -ap time 2>/dev/null || true); do
    [[ -x $c ]] && "$c" -v true >/dev/null 2>&1 && { GNUTIME=$c; break; }
  done
fi

BINS=(); EXPORTS=(); RUNS=""; LIST=0; DRY=0; LIMIT_KB=""
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
    --list)    LIST=1; shift ;;
    --dry-run) DRY=1; shift ;;
    -h|--help) sed -n '2,48p' "${BASH_SOURCE[0]}"; exit 0 ;;
    *) echo "bench-baselines.sh: unknown argument $1" >&2; exit 2 ;;
  esac
done
[[ ${#BINS[@]}    -eq 0 ]] && BINS=(con-ron nanoda)
[[ ${#EXPORTS[@]} -eq 0 ]] && EXPORTS=(init core mathlib)

# Per-export address-space cap (KB) and timeout (s).  The caps are CLAUDE.md's
# budget rule applied to what con-leche needs on the same input (0.48 / 1.22 /
# 8.75 GB peak RSS, OVERVIEW section 7.2): 2.6 GB, 5 GB, 27 GB.  A checker that
# does not fit is a bug to investigate, never a reason to raise the cap.
limit_kb() { case "$1" in
    init)    echo 2726400 ;;     # 2.6 GB
    core)    echo 5242880 ;;     # 5 GB
    mathlib) echo 28311552 ;;    # 27 GB
    *) echo "bench-baselines.sh: unknown export $1" >&2; exit 2 ;;
  esac; }
timeout_s() { case "$1" in
    init) echo 1800 ;; core) echo 3600 ;; mathlib) echo 9000 ;;
  esac; }
# Wall is only meaningful from several runs of a benchmark small enough to
# repeat (CLAUDE.md): `init` is, the other two are not.
default_runs() { case "$1" in init) echo 3 ;; *) echo 1 ;; esac; }

if [[ $LIST -eq 1 ]]; then
  printf '%-16s %-8s %-6s %12s %8s\n' bin export runs 'ulimit -v' timeout
  for b in "${BINS[@]}"; do for e in "${EXPORTS[@]}"; do
    printf '%-16s %-8s %-6s %12s %8s\n' \
      "$b" "$e" "${RUNS:-$(default_runs "$e")}" "${LIMIT_KB:-$(limit_kb "$e")} KB" "$(timeout_s "$e")s"
  done; done
  exit 0
fi

[[ -n $GNUTIME ]] || { echo "bench-baselines.sh: GNU time not found; set GNUTIME=" >&2; exit 2; }
mkdir -p "$OUT"

# The command for one (bin, export) pair, written into the array CMD.
build_cmd() {
  local bin="$1" exp="$2" file="$CORPUS/$exp.ndjson"
  [[ -f $file ]] || { echo "bench-baselines.sh: missing export $file" >&2; exit 2; }
  case "$bin" in
    con-ron)
      local b="$ROOT/target/release/$bin"
      [[ -x $b ]] || { echo "bench-baselines.sh: $b not built (cargo build --release)" >&2; exit 2; }
      CMD=("$b" --verified --jobs=1 --progress=1000000 "$file") ;;
    nanoda)
      [[ -x $NANODA ]] || { echo "bench-baselines.sh: $NANODA not built; see DESIGN.md \"Task #97-P6-3\"" >&2; exit 2; }
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

for bin in "${BINS[@]}"; do
  for exp in "${EXPORTS[@]}"; do
    n="${RUNS:-$(default_runs "$exp")}"
    kb="${LIMIT_KB:-$(limit_kb "$exp")}"; to="$(timeout_s "$exp")"
    sfx=""; [[ -n $LIMIT_KB ]] && sfx="-limit$LIMIT_KB"
    build_cmd "$bin" "$exp"
    for ((r = 1; r <= n; r++)); do
      tag="$OUT/$bin-$exp$sfx-r$r"
      if [[ $DRY -eq 1 ]]; then
        echo "( ulimit -v $kb; $GNUTIME -v -o $tag.time -- perf stat -e instructions:u,cycles:u -o $tag.perf -- timeout $to ${CMD[*]} > $tag.out 2> $tag.err )"
        continue
      fi
      echo "== $bin $exp run $r/$n (ulimit -v $kb KB, timeout ${to}s)" >&2
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
