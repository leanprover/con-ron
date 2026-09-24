#!/usr/bin/env bash
# scripts/frontier.sh [--summary] [--scope P,...] [--top N] [--tag T] <root>...
#
# The `sorry` frontier of the given theorems (task #97-FRONTIER): every
# declaration of their dependency closure whose OWN term mentions `sorryAx`,
# sorted by fan-in (how many closure declarations reach `sorryAx` only
# through it), the non-standard axioms of the closure (there should be none),
# and the dead weight — direct `sorry`s in the scope modules that are NOT on
# the frontier.  The analysis is `ConRon.Tools.Frontier` (`proof/ConRon/
# Tools/Frontier.lean`); this wrapper writes a scratch Lean file that imports
# the roots' modules plus every module of the scope, runs it, and prints the
# report.
#
#   <root>      a full declaration name (`ConRon.Refine2.check_decls_pure_refines`)
#               or `Module:Name` when the module cannot be found by grep.
#   --scope     module prefixes for the dead-weight count (default: the
#               `ConRon.Bridge`/`ConRon.Refine2` tier(s) the roots live in;
#               both when a root is in neither).  `--scope ''` skips it.
#   --summary   print only the one-line summary.
#   --top N     how many frontier items the report lists (default 20).
#   --tag T     output file stem (default: the roots' last components).
#   --history   print the history file (one row per run, every worktree) and exit.
#
# Output: `_tmp/frontier-<checkout key>/<tag>.{frontier.tsv,dead.tsv,summary.txt,line.txt}`,
# and one row appended to `_tmp/frontier-history.tsv` (shared, see below).
# Several roots are analysed TOGETHER (one closure); they must be importable
# into one environment.  `ConRonBridge` and `ConRonRefine2` are not: run one
# root per call there.
set -euo pipefail
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
proof="$root/proof"
summary=0; scope=unset; top=20; tag=""
roots=()
while [ $# -gt 0 ]; do
  case "$1" in
    --summary) summary=1; shift;;
    --scope) scope=$2; shift 2;;
    --scope=*) scope=${1#--scope=}; shift;;
    --top) top=$2; shift 2;;
    --tag) tag=$2; shift 2;;
    --history) hist="$root/_tmp/frontier-history.tsv"
               if [ -s "$hist" ]; then column -t -s $'\t' "$hist"; else echo "no history yet ($hist)"; fi
               exit 0;;
    -h|--help) sed -n '2,32p' "$0"; exit 0;;
    -*) echo "unknown option $1" >&2; exit 2;;
    *) roots+=("$1"); shift;;
  esac
done
[ ${#roots[@]} -gt 0 ] || { echo "usage: $0 [--summary] [--scope P,...] <root>..." >&2; exit 2; }

# The module that declares NAME: the longest suffix of NAME declared by a
# `theorem`/`def`/… line of `proof/ConRon/**` in a
# file that opens the rest of NAME as a namespace.
locate() {
  local name=$1 n i
  local parts
  IFS=. read -r -a parts <<<"$name"
  n=${#parts[@]}
  for ((i = 0; i < n; i++)); do
    local pre suf
    pre=$(IFS=.; echo "${parts[*]:0:i}")
    suf=$(IFS=.; echo "${parts[*]:i}")
    local re="^[[:space:]]*(@\[[^]]*\][[:space:]]*)?((private|protected|noncomputable|partial|nonrec)[[:space:]]+)*(theorem|lemma|def|abbrev|instance|opaque|axiom)[[:space:]]+${suf//./\\.}([[:space:]]|$)"
    local files
    files=$(grep -rlE --include='*.lean' "$re" "$proof/ConRon" || true)
    [ -n "$files" ] || continue
    local hits=()
    local f
    while IFS= read -r f; do
      if [ -z "$pre" ] || grep -qE "^namespace[[:space:]]+(${pre//./\\.}|.*\\.${pre##*.})\$" "$f"; then
        hits+=("$f")
      fi
    done <<<"$files"
    if [ ${#hits[@]} -eq 1 ]; then
      local rel=${hits[0]#"$proof/"}
      rel=${rel%.lean}
      echo "${rel//\//.}"
      return 0
    elif [ ${#hits[@]} -gt 1 ]; then
      echo "error: $name is ambiguous (${hits[*]}); pass Module:Name" >&2
      return 1
    fi
  done
  echo "error: cannot find the module declaring $name; pass Module:Name" >&2
  return 1
}

mods=(); names=()
for r in "${roots[@]}"; do
  if [[ $r == *:* ]]; then mods+=("${r%%:*}"); names+=("${r#*:}")
  else mods+=("$(locate "$r")"); names+=("$r"); fi
done

if [ "$scope" = unset ]; then
  scope=""
  for m in "${mods[@]}"; do
    case $m in
      ConRon.Bridge.*) t=ConRon.Bridge;;
      ConRon.Refine2.*) t=ConRon.Refine2;;
      *) t=ConRon.Bridge,ConRon.Refine2;;
    esac
    case ",$scope," in *",$t,"*) ;; *) scope=${scope:+$scope,}$t;; esac
  done
fi

# Every module of the scope, so that a `sorry` nothing imports is counted.
extra=()
IFS=, read -r -a scopes <<<"$scope"
for p in "${scopes[@]}"; do
  [ -n "$p" ] || continue
  d="$proof/${p//.//}"
  [ -d "$d" ] || { echo "error: scope $p: no directory $d" >&2; exit 2; }
  while IFS= read -r f; do
    rel=${f#"$proof/"}; rel=${rel%.lean}; extra+=("${rel//\//.}")
  done < <(find "$d" -name '*.lean' | sort)
done

if [ -z "$tag" ]; then
  tag=$(for n in "${names[@]}"; do echo "${n##*.}"; done | paste -sd+ -)
fi
# Per-checkout, like `gates.sh`'s logs: `_tmp` is shared between worktrees.
key=$(printf '%s' "$root" | sha256sum | cut -c1-12)
scratch="$root/_tmp/frontier-$key"
out=$scratch
mkdir -p "$scratch"
file="$scratch/Run.lean"
{
  echo "import ConRon.Tools.Frontier"
  printf 'import %s\n' "${mods[@]}" "${extra[@]}" | awk '!seen[$0]++'
  printf 'run_cmd do\n  let s ← Lean.Elab.Command.liftCoreM <| ConRon.Tools.Frontier.report #['
  first=1
  for n in "${names[@]}"; do
    [ $first = 1 ] || printf ', '; first=0
    printf '`%s' "$n"
  done
  printf '] { outDir := some "%s", tag := "%s", top := %s, deadScope := #[' "$out" "$tag" "$top"
  first=1
  for p in "${scopes[@]}"; do
    [ -n "$p" ] || continue
    [ $first = 1 ] || printf ', '; first=0
    printf '`%s' "$p"
  done
  printf '] }\n  pure ()\n'
} > "$file"

cd "$proof"
# Build what the scratch file imports (a no-op when the tree is built).
targets=(ConRon.Tools.Frontier "${mods[@]}")
for p in "${scopes[@]}"; do
  case $p in
    ConRon.Bridge) targets+=(ConRonBridge);;
    ConRon.Refine2) targets+=(ConRonRefine2);;
  esac
done
if ! lake build "${targets[@]}" > "$scratch/build.log" 2>&1; then
  echo "error: lake build ${targets[*]} failed; see $scratch/build.log" >&2
  tail -20 "$scratch/build.log" >&2
  exit 1
fi
rm -f "$out/$tag.summary.txt" "$out/$tag.line.txt" "$out/$tag.stats.tsv"
start=$(date +%s%N)
if ! lake env lean "$file" > "$scratch/run.log" 2>&1; then
  echo "error: the frontier run failed; see $scratch/run.log" >&2
  tail -20 "$scratch/run.log" >&2
  exit 1
fi
end=$(date +%s%N)
wall="$(( (end - start) / 1000000 )) ms"
# The frontier's size OVER TIME: one row per run, in a history file shared by
# every worktree (`_tmp` is one directory), so gate runs on every branch add
# to the same series.  `--history` prints it.
hist="$root/_tmp/frontier-history.tsv"
[ -s "$hist" ] || printf 'date\tcommit\tbranch\tdirty\ttag\titems\ttainted\tdead\tnonstd_axioms\ttop\ttop_fan_in\n' > "$hist"
rev=$(git -C "$root" rev-parse --short HEAD 2>/dev/null || echo -)
br=$(git -C "$root" symbolic-ref --quiet --short HEAD 2>/dev/null || echo -)
dirty=$(git -C "$root" status --porcelain --untracked-files=no -- proof 2>/dev/null | grep -q . && echo dirty || echo clean)
printf '%s\t%s\t%s\t%s\t%s\t%s\n' "$(date -u +%Y-%m-%dT%H:%M:%SZ)" "$rev" "$br" "$dirty" "$tag" \
  "$(cat "$out/$tag.stats.tsv")" >> "$hist"
if [ $summary = 1 ]; then
  echo "$(cat "$out/$tag.line.txt") [${wall}]"
else
  cat "$out/$tag.summary.txt"
  echo "  wall time (import + analysis): $wall"
  echo "  files: $out/$tag.{frontier.tsv,dead.tsv,summary.txt}"
fi
