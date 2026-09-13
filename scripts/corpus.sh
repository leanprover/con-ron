#!/usr/bin/env bash
# scripts/corpus.sh — THE SCALE CORPUS (DESIGN.md task #29, P1.8 preparation).
#
# Builds, from a clean `_tmp/`, everything the performance comparison of
# P1.8 needs *except* the Rust checker itself:
#
#   1. `lean4export` at the project toolchain (con-leche's `lean-toolchain`,
#      v4.33.0 — the export format tracks the Lean version, so the exporter
#      MUST be built at the toolchain whose oleans it reads), and three
#      exports: `Init` (the core prelude), `Init Std Lean` (all of core) and
#      `Mathlib` (the scale workload, read from the mathlib package tree
#      that `_tmp/aeneas-lean` already has built).
#   2. con-leche's own verdict on each export, at `--jobs=1` and at a
#      parallel setting, with `perf stat -e instructions:u` (the measurement
#      of record), wall time and peak RSS.
#   3. the `con-ron-decls/1` dump of each export (`lake exe con-ron-dump`),
#      with the Lean round trip on the small ones and `--write-only` on
#      Mathlib, and `con-ron-dump-check` (the Rust reader, task #19) on
#      every dump.
#   4. three reports rebuilt from the artifacts on disk.
#
# Every step is skipped when its output is already there, so a re-run is
# cheap and a partial run resumes.  Results land in
#   $OUT/README.md    the exports: commands, sizes, times
#   $OUT/baseline.md  con-leche's verdicts and costs
#   $OUT/dumps.md     the dumps and the Rust reader's verdicts
# and the raw logs next to them (`<tag>.{out,err,perf,time,exit}`).  Nothing
# here is committed: `_tmp/` is gitignored and the Mathlib export alone is
# gigabytes.
#
# NOT parallel with itself: `proof/` and `vendor/con-leche` share the
# con-leche package build directory, so the two `lake build`s below must not
# run at the same time as each other (or as another agent's).
#
# USAGE
#     scripts/corpus.sh [--steps=1,2,3,4] [--no-mathlib] [OUTDIR]
#
# Every exporter/checker/dump run is wrapped in `timeout` and `ulimit -v`
# (22 GB), so that a runaway run dies rather than the machine.
set -u
cd "$(dirname "$0")/.."
root=$PWD

CL="$root/vendor/con-leche"
OUT="${OUT:-$root/_tmp/corpus}"
L4E="${L4E:-$root/_tmp/lean4export}"
# A Lake package tree with Mathlib built at the project toolchain.
MATHLIB_ROOT="${MATHLIB_ROOT:-$root/_tmp/aeneas-lean}"
VMAX="${VMAX:-22000000}"          # ulimit -v, in KiB: 22 GB
TO_EXPORT="${TO_EXPORT:-14400}"   # 4 h
TO_CHECK="${TO_CHECK:-14400}"
# con-leche's worker threads reserve ~1 GiB of address space each, so the
# `--jobs` default (one per hardware thread) does not fit under `ulimit -v`
# on a big machine; con-leche's own scripts/selfcheck.sh uses 8 for the same
# reason, and that is what the "default jobs" column measures here.
JOBS_PAR="${JOBS_PAR:-8}"
# The Rust reader's round trip holds the parsed DAG and the re-dumped text at
# once: measured at 17.5 GB RSS for the 3.06 GB Mathlib dump (~5.7x the file),
# i.e. inside the 22 GB cap but not by much.  Dumps above this get parse + DAG
# census only; raise it deliberately, with the cap in mind.
RT_MAX="${RT_MAX:-4000000000}"

STEPS=1,2,3,4
WANT_MATHLIB=1
for a in "$@"; do
  case "$a" in
    --steps=*)    STEPS="${a#--steps=}" ;;
    --no-mathlib) WANT_MATHLIB=0 ;;
    -*) echo "usage: $0 [--steps=1,2,3,4] [--no-mathlib] [OUTDIR]" >&2; exit 2 ;;
    *)  OUT="$a" ;;
  esac
done
step_wanted() { case ",$STEPS," in *",$1,"*) return 0;; *) return 1;; esac; }

mkdir -p "$OUT" || exit 2
OUT=$(cd "$OUT" && pwd)
TOOLCHAIN=$(cat "$CL/lean-toolchain")

say() { printf '[corpus] %s\n' "$*" >&2; }

# measure <tag> -- cmd...   →  $OUT/<tag>.{out,err,perf,time}, exit code in
# $OUT/<tag>.exit.  perf counts the whole process tree; GNU time gives the
# peak RSS of its largest member.
measure() {
  local tag=$1; shift; [ "$1" = "--" ] && shift
  local rc
  ( ulimit -v "$VMAX"
    command time -v -o "$OUT/$tag.time" \
      perf stat -e instructions:u -o "$OUT/$tag.perf" -- "$@" ) \
    > "$OUT/$tag.out" 2> "$OUT/$tag.err"
  rc=$?
  echo "$rc" > "$OUT/$tag.exit"
  return $rc
}
m_instr() { sed -n 's/^ *\([0-9,]*\) *instructions:u.*/\1/p' "$OUT/$1.perf" | tr -d ,; }
m_wall()  { sed -n 's/^ *\([0-9.]*\) seconds time elapsed/\1/p' "$OUT/$1.perf"; }
m_rss()   { sed -n 's/.*Maximum resident set size (kbytes): //p' "$OUT/$1.time"; }
hsize()   { [ -f "$1" ] && stat -c %s "$1" || echo 0; }

# The record census: one awk pass printing, per record, its first JSON key.
# lean4export emits a record's keys in ALPHABETICAL order, so that key is the
# record's kind only when the record is a single-key object -- which is
# exactly the declaration records (`axiom`/`def`/`thm`/`opaque`/`inductive`/
# `quot`), and those are the only rows the reports read.  An expression record
# `{"app":{...},"ie":7}` lands under `app`, not `ie`, so the other rows of the
# census are "records whose alphabetically-first key is this", not node kinds.
# Deliberately outside the `measure`d runs: bookkeeping, not a workload.
counts_one() { # <name>
  local src="$OUT/$1.ndjson" dest="$OUT/$1.counts"
  [ -s "$src" ] || return 0
  [ -s "$dest" ] && return 0
  say "counting $1.ndjson records"
  LC_ALL=C awk -F'"' '{c[$2]++} END {for (k in c) printf "%d %s\n", c[k], k}' \
    "$src" | sort -rn > "$dest"
}

###################################################################### 1
# The exporter and the three exports.
export_one() { # <name> <cwd> <root-module>...
  local name=$1 cwd=$2; shift 2
  local dest="$OUT/$name.ndjson"
  if [ -s "$dest" ]; then say "export $name: already there ($(hsize "$dest") bytes)"; return 0; fi
  say "exporting $name ($*) from $cwd"
  ( cd "$cwd" && measure "export-$name" -- \
      timeout "$TO_EXPORT" lake env "$L4E/.lake/build/bin/lean4export" "$@" )
  local rc=$?
  if [ $rc -ne 0 ]; then
    say "export $name FAILED (exit $rc); see $OUT/export-$name.err"
    mv "$OUT/export-$name.out" "$dest.partial" 2>/dev/null
    return 1
  fi
  mv "$OUT/export-$name.out" "$dest"
  say "export $name: $(hsize "$dest") bytes, $(m_wall "export-$name")s"
  counts_one "$name"
}

if step_wanted 1; then
  if [ ! -x "$L4E/.lake/build/bin/lean4export" ]; then
    say "building lean4export for $TOOLCHAIN"
    if [ ! -d "$L4E/.git" ]; then
      rm -rf "$L4E"
      git clone -q https://github.com/leanprover/lean4export "$L4E" || exit 2
    fi
    ( cd "$L4E"
      # The newest commit whose `lean-toolchain` is ours (upstream carries one
      # `chore: bump toolchain` commit per release; the v4.33.0 *tag* of the
      # exporter is not what matters — the toolchain file is).
      if [ "$(cat lean-toolchain)" != "$TOOLCHAIN" ]; then
        for c in $(git log --format=%H -- lean-toolchain); do
          if [ "$(git show "$c:lean-toolchain")" = "$TOOLCHAIN" ]; then
            git checkout -q "$c"; break
          fi
        done
      fi
      [ "$(cat lean-toolchain)" = "$TOOLCHAIN" ] || {
        echo "[corpus] no lean4export commit for $TOOLCHAIN" >&2; exit 3; }
      lake build ) || exit 2
  fi
  say "lean4export at $(cd "$L4E" && git log --format='%h %s' -1 | head -c 60)"

  export_one init    "$L4E" Init
  export_one core    "$L4E" Init Std Lean
  if [ "$WANT_MATHLIB" = 1 ]; then
    export_one mathlib "$MATHLIB_ROOT" Mathlib
  fi
  for n in init core mathlib; do counts_one "$n"; done
fi

###################################################################### 2
# con-leche's baseline on each export.
if step_wanted 2; then
  if [ ! -x "$CL/.lake/build/bin/con-leche" ]; then
    say "building con-leche"
    ( cd "$CL" && lake build con-leche ) || exit 2
  fi
  for name in init core mathlib; do
    src="$OUT/$name.ndjson"; [ -s "$src" ] || continue
    for j in 1 "$JOBS_PAR"; do
      tag="cl-$name-j$j"
      [ -s "$OUT/$tag.exit" ] && { say "con-leche $name jobs=$j: already there"; continue; }
      say "con-leche --verified --jobs=$j $name"
      measure "$tag" -- timeout "$TO_CHECK" \
        "$CL/.lake/build/bin/con-leche" --verified "--jobs=$j" "$src"
      say "  exit $(cat "$OUT/$tag.exit"), $(m_instr "$tag") instructions:u, \
$(m_wall "$tag")s, $(m_rss "$tag") KB"
    done
  done
  # One probe of the DEFAULT --jobs (one worker per hardware thread: $(nproc)
  # here), on the smallest export, so what the address-space cap does to it is
  # recorded rather than asserted.
  tag=cl-init-jdefault
  if [ -s "$OUT/init.ndjson" ] && [ ! -s "$OUT/$tag.exit" ]; then
    say "con-leche --verified (default jobs = $(nproc)) init"
    measure "$tag" -- timeout "$TO_CHECK" \
      "$CL/.lake/build/bin/con-leche" --verified "$OUT/init.ndjson"
    say "  exit $(cat "$OUT/$tag.exit"), $(m_instr "$tag") instructions:u, \
$(m_wall "$tag")s, $(m_rss "$tag") KB"
  fi
fi

###################################################################### 3
# The `con-ron-decls/1` dumps, and the Rust reader on each.
if step_wanted 3; then
  DUMP="$root/proof/.lake/build/bin/con-ron-dump"
  if [ ! -x "$DUMP" ]; then
    say "building con-ron-dump"
    ( cd "$root/proof" && lake build con-ron-dump ) || exit 2
  fi
  DCHECK="$root/target/release/con-ron-dump-check"
  if [ ! -x "$DCHECK" ]; then
    say "building con-ron-dump-check"
    ( cd "$root" && cargo build --release -p con-ron-dump ) || exit 2
  fi
  for name in init core mathlib; do
    src="$OUT/$name.ndjson"; [ -s "$src" ] || continue
    dest="$OUT/$name.decls"
    # The round trip (read back, re-dump, compare) roughly doubles the peak
    # memory, and that is what `--write-only` drops; at Mathlib scale it is
    # the difference between a run and an OOM.  `--no-check` drops the two
    # `checkDecls` runs, which are con-leche's cost, not the dump's.
    case "$name" in
      mathlib) flag=--write-only ;;
      *)       flag=--no-check ;;
    esac
    tag="dump-$name"
    if [ -s "$dest" ] && [ -s "$OUT/$tag.exit" ]; then
      say "dump $name: already there ($(hsize "$dest") bytes)"
    else
      say "con-ron-dump $flag $name"
      measure "$tag" -- timeout "$TO_CHECK" "$DUMP" "$flag" "$src" "$dest"
      say "  exit $(cat "$OUT/$tag.exit"), $(hsize "$dest") bytes, \
$(m_wall "$tag")s, $(m_rss "$tag") KB"
    fi
    [ -s "$dest" ] || continue
    tag="dcheck-$name"
    if [ -s "$OUT/$tag.exit" ]; then
      say "con-ron-dump-check $name: already there"
    else
      say "con-ron-dump-check $name"
      # `--roundtrip` re-dumps and compares bytes, which is what keeps the
      # format pinned where `--write-only` dropped the Lean round trip -- and
      # pins it by the *other* reader, which is the stronger check.
      rflag=--roundtrip
      [ "$(hsize "$dest")" -gt "$RT_MAX" ] && rflag=
      measure "$tag" -- timeout "$TO_CHECK" "$DCHECK" $rflag "$dest"
      say "  exit $(cat "$OUT/$tag.exit"), $(m_wall "$tag")s, $(m_rss "$tag") KB"
    fi
  done
fi

###################################################################### 4
# The three reports, rebuilt from the artifacts every run (cheap, and the
# numbers then always describe what is actually on disk).
decls_of() { # <name>: declaration records, total and by kind, from the census
  local f="$OUT/$1.counts"; [ -s "$f" ] || { echo "- |"; return; }
  local tot=0 part="" k n
  for k in axiom def thm opaque inductive quot; do
    n=$(awk -v k="$k" '$2 == k {print $1}' "$f"); n=${n:-0}
    tot=$((tot + n)); [ "$n" != 0 ] && part="$part $k $n"
  done
  echo "$tot |$part"
}
field() { # <name> <key>: a count from the dump tool's own stdout
  sed -n "s/.*$2 \([0-9]*\).*/\1/p" "$OUT/dump-$1.out" 2>/dev/null | head -1
}
verdict_of() { # <tag>: con-leche's own verdict line (printed on stdout), or
              # the exception that stopped it
  grep -m1 -hE "accepted|rejected|declined|internal|exception" \
    "$OUT/$1.out" "$OUT/$1.err" 2>/dev/null | sed 's/^con-leche: //' \
    | tr '|\n' '/ ' | head -c 110
}
dcheck_line() { # <name>: what the Rust reader concluded
  grep -m1 -hE "^(OK|FAIL)" "$OUT/dcheck-$1.out" 2>/dev/null \
    | sed 's/.* B  //' | head -c 90
}

if step_wanted 4; then
  say "writing $OUT/README.md, baseline.md, dumps.md"
  {
    echo "# The scale corpus (con-ron task #29)"
    echo
    echo "Generated by \`scripts/corpus.sh\` on $(date -u +%FT%TZ)."
    echo "Nothing here is committed (\`_tmp/\` is gitignored); regenerate with"
    echo "\`scripts/corpus.sh\`, which skips whatever is already present."
    echo
    echo "## The exporter"
    echo
    echo '```'
    echo "git clone https://github.com/leanprover/lean4export $L4E"
    echo "# the newest commit whose lean-toolchain is $TOOLCHAIN:"
    echo "cd $L4E && git checkout $(cd "$L4E" && git rev-parse --short HEAD) && lake build"
    echo "#   $(cd "$L4E" && git log --format=%s -1)"
    echo '```'
    echo
    echo "Stream header: \`$(head -1 "$OUT/init.ndjson" 2>/dev/null | head -c 200)\`"
    echo
    echo "## The exports"
    echo
    echo '```'
    echo "cd $L4E          && lake env .lake/build/bin/lean4export Init          > init.ndjson"
    echo "cd $L4E          && lake env .lake/build/bin/lean4export Init Std Lean > core.ndjson"
    echo "cd $MATHLIB_ROOT && lake env $L4E/.lake/build/bin/lean4export Mathlib  > mathlib.ndjson"
    echo '```'
    echo
    echo "\`lake env\` is what puts the package tree on \`LEAN_PATH\`: for the two"
    echo "core exports the exporter's own package is enough (its toolchain carries"
    echo "\`Init\`, \`Std\` and \`Lean\`), and Mathlib is exported from the tree that"
    echo "already has it built, \`_tmp/aeneas-lean\`, with the exporter named by"
    echo "absolute path."
    echo
    echo "| export | roots | bytes | lines | declarations | instructions:u | wall | peak RSS |"
    echo "|---|---|---|---|---|---|---|---|"
    for n in init core mathlib; do
      f="$OUT/$n.ndjson"; [ -s "$f" ] || continue
      case "$n" in init) r='`Init`';; core) r='`Init Std Lean`';; mathlib) r='`Mathlib`';; esac
      d=$(decls_of "$n")
      printf '| `%s` | %s | %s | %s | %s | %s | %ss | %s KB |\n' \
        "$n.ndjson" "$r" "$(hsize "$f")" "$(wc -l < "$f")" "${d%% |*}" \
        "$(m_instr "export-$n")" "$(m_wall "export-$n")" "$(m_rss "export-$n")"
    done
    echo
    echo "Declaration records by kind (from \`<name>.counts\`, the awk census;"
    echo "its non-declaration rows are alphabetically-first keys, not node"
    echo "kinds -- see \`counts_one\`):"
    echo
    for n in init core mathlib; do
      [ -s "$OUT/$n.counts" ] || continue
      d=$(decls_of "$n"); echo "* \`$n\`:${d#* |}"
    done
  } > "$OUT/README.md"

  {
    echo "# con-leche's baseline on the scale corpus (task #29)"
    echo
    echo "\`con-leche --verified --jobs=<j> <export>\`, con-leche at"
    echo "$(cd "$CL" && git rev-parse --short HEAD), under \`ulimit -v $VMAX\` and"
    echo "\`timeout $TO_CHECK\`.  \`instructions:u\` (perf) is the measurement of"
    echo "record; wall time and peak RSS are secondary and machine-dependent."
    echo "The parallel row is \`--jobs=$JOBS_PAR\`, not the default: a worker"
    echo "reserves ~1 GiB of address space and the default is one per hardware"
    echo "thread, which does not fit the 22 GB cap on this 96-thread machine."
    echo
    echo "| export | jobs | exit | verdict | instructions:u | wall | peak RSS |"
    echo "|---|---|---|---|---|---|---|"
    for n in init core mathlib; do
      for j in 1 "$JOBS_PAR"; do
        t="cl-$n-j$j"; [ -s "$OUT/$t.exit" ] || continue
        printf '| `%s` | %s | %s | %s | %s | %ss | %s KB |\n' "$n" "$j" \
          "$(cat "$OUT/$t.exit")" "$(verdict_of "$t")" \
          "$(m_instr "$t")" "$(m_wall "$t")" "$(m_rss "$t")"
      done
    done
    t=cl-init-jdefault
    if [ -s "$OUT/$t.exit" ]; then
      printf '| `init` | default (%s) | %s | %s | %s | %ss | %s KB |\n' \
        "$(nproc)" "$(cat "$OUT/$t.exit")" \
        "$(verdict_of "$t")" \
        "$(m_instr "$t")" "$(m_wall "$t")" "$(m_rss "$t")"
    fi
  } > "$OUT/baseline.md"

  {
    echo "# The \`con-ron-decls/1\` dumps of the scale corpus (task #29)"
    echo
    echo "\`lake exe con-ron-dump <flag> <export> <dump>\` (task #10) and then"
    echo "\`con-ron-dump-check <dump>\` (the Rust reader, task #19).  \`--no-check\`"
    echo "keeps the Lean round trip and drops the two \`checkDecls\` runs;"
    echo "\`--write-only\` drops the round trip too and streams the lines out one"
    echo "declaration at a time instead of accumulating them, which is what a"
    echo "Mathlib-scale dump needs to stay inside the 22 GB cap (the buffered"
    echo "writer dies at 18.9 GB RSS on \`mathlib.ndjson\`).  The bytes are"
    echo "identical either way -- checked on a fixture and on \`init.ndjson\`."
    echo
    echo "| dump | flag | exit | bytes | declarations | names | levels | exprs | wall | peak RSS |"
    echo "|---|---|---|---|---|---|---|---|---|---|"
    for n in init core mathlib; do
      t="dump-$n"; [ -s "$OUT/$t.exit" ] || continue
      case "$n" in mathlib) fl='`--write-only`';; *) fl='`--no-check`';; esac
      printf '| `%s` | %s | %s | %s | %s | %s | %s | %s | %ss | %s KB |\n' \
        "$n.decls" "$fl" "$(cat "$OUT/$t.exit")" "$(hsize "$OUT/$n.decls")" \
        "$(field "$n" declarations)" "$(field "$n" names)" "$(field "$n" levels)" \
        "$(field "$n" exprs)" "$(m_wall "$t")" "$(m_rss "$t")"
    done
    echo
    echo "| dump | con-ron-dump-check | exit | wall | peak RSS |"
    echo "|---|---|---|---|---|"
    for n in init core mathlib; do
      t="dcheck-$n"; [ -s "$OUT/$t.exit" ] || continue
      printf '| `%s` | %s | %s | %ss | %s KB |\n' "$n.decls" \
        "$(dcheck_line "$n")" \
        "$(cat "$OUT/$t.exit")" "$(m_wall "$t")" "$(m_rss "$t")"
    done
  } > "$OUT/dumps.md"
fi

say "done; logs in $OUT"
