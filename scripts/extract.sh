#!/usr/bin/env bash
# Extract `crates/con-ron-core` to Lean, through Charon and Aeneas, into
# `proof/ConRon/Generated/` (DESIGN.md §3.5, P2 / task #12).
#
#   scripts/extract.sh            regenerate the committed files in place
#   scripts/extract.sh --check    regenerate into `_tmp/` and diff; non-zero
#                                 on any difference.  This is the CI rule
#                                 "the committed generated code matches the
#                                 crate".
#
# Generated (overwritten, committed):
#   proof/ConRon/Generated/Types.lean
#   proof/ConRon/Generated/Funs.lean
#   proof/ConRon/Generated/TypesExternal_Template.lean
#   proof/ConRon/Generated/FunsExternal_Template.lean
#
# Hand-written (NEVER overwritten, committed): the models of DESIGN.md §3.2
#   proof/ConRon/Generated/TypesExternal.lean
#   proof/ConRon/Generated/FunsExternal.lean
# The script fails if a template declares an external (`@[rust_type "..."]` /
# `@[rust_fun "..."]`) that the corresponding hand-written file does not
# model -- that is the signal that the crate grew a new hole.
#
# Deterministic: two runs produce byte-identical output.  (The intermediate
# `.llbc` is *not* deterministic -- it records the absolute output path -- but
# the Lean it produces is, which is what is committed.)
set -euo pipefail

root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
crate_dir="$root/crates/con-ron-core"
crate="con_ron_core"
subdir="ConRon/Generated"
namespace="ConRon.Generated"
committed="$root/proof/$subdir"

gen_files=(Types.lean Funs.lean TypesExternal_Template.lean FunsExternal_Template.lean)
# hand-written file <- the template whose holes it must fill
hand_files=(TypesExternal.lean FunsExternal.lean)
template_of() {
  case "$1" in
    TypesExternal.lean) echo TypesExternal_Template.lean ;;
    FunsExternal.lean)  echo FunsExternal_Template.lean ;;
  esac
}

check=0
case "${1-}" in
  "") ;;
  --check) check=1 ;;
  *) echo "usage: $0 [--check]" >&2; exit 2 ;;
esac
[ "$#" -le 1 ] || { echo "usage: $0 [--check]" >&2; exit 2; }

if [ "$check" -eq 1 ]; then work="$root/_tmp/extract-check"; else work="$root/_tmp/extract"; fi
rm -rf "$work"
mkdir -p "$work/llbc" "$work/lean"

# 1. Rust -> LLBC.  `charon cargo` always recompiles (it drives rustc itself),
#    so no `cargo clean` is needed; the destination must be absolute -- a
#    relative one is resolved against the workspace root, not the crate.
echo "extract: charon cargo --preset=aeneas ($crate_dir)"
( cd "$crate_dir" && charon cargo --preset=aeneas --dest-file "$work/llbc/$crate.llbc" )
[ -f "$work/llbc/$crate.llbc" ] || {
  echo "error: charon produced no $crate.llbc in $work/llbc" >&2; exit 1; }

# 2. LLBC -> Lean.  `-subdir` is what makes the files import each other as
#    `ConRon.Generated.*` (it sets both the output path and the import
#    prefix); `-namespace` puts the definitions in `ConRon.Generated`, so a
#    generated function is `ConRon.Generated.<module>.<fn>`.  No `sed`
#    post-processing of the import lines is needed.
echo "extract: aeneas -backend lean -split-files -loops-to-rec"
aeneas -backend lean -split-files -loops-to-rec \
  -dest "$work/lean" -subdir "$subdir" -namespace "$namespace" \
  -no-progress-bar "$work/llbc/$crate.llbc"

out="$work/lean/$subdir"
for f in "${gen_files[@]}"; do
  [ -f "$out/$f" ] || { echo "error: aeneas produced no $f" >&2; exit 1; }
done

# 3. Every hole a template declares must be modeled by hand.  The names are
#    the `@[rust_type "..."]` / `@[rust_fun "..."]` attribute arguments; an
#    attribute may be wrapped over two lines (hence the `tr`) and may sit
#    beside others (`@[reducible, rust_type "..."]`), hence no `@[` anchor.
externals() {
  tr '\n' ' ' < "$1" \
    | { grep -oP 'rust_(?:type|fun)\s+"[^"]*"' || true; } \
    | sed 's/.*"\(.*\)"$/\1/' | LC_ALL=C sort -u
}
missing=0
for hand in "${hand_files[@]}"; do
  tmpl="$out/$(template_of "$hand")"
  if [ ! -f "$committed/$hand" ]; then
    echo "error: proof/$subdir/$hand is missing (hand-written, DESIGN.md §3.2)" >&2
    missing=1; continue
  fi
  modeled="$(externals "$committed/$hand")"
  while IFS= read -r name; do
    [ -n "$name" ] || continue
    if ! printf '%s\n' "$modeled" | grep -qxF -- "$name"; then
      echo "error: $hand does not model the external \"$name\"" >&2
      echo "       (declared by $(template_of "$hand"); fill the hole by hand)" >&2
      missing=1
    fi
  done < <(externals "$tmpl")
done
[ "$missing" -eq 0 ] || { echo "extract: FAIL (unmodeled externals)" >&2; exit 1; }
echo "extract: externals OK ($(externals "$out/TypesExternal_Template.lean" | wc -l) type(s), $(externals "$out/FunsExternal_Template.lean" | wc -l) fn(s) modeled by hand)"

# 4. Install, or diff.
if [ "$check" -eq 1 ]; then
  rc=0
  for f in "${gen_files[@]}"; do
    if ! diff -u "$committed/$f" "$out/$f" > "$work/$f.diff" 2>&1; then
      echo "extract --check: $subdir/$f differs from the crate:" >&2
      sed -n '1,40p' "$work/$f.diff" >&2
      rc=1
    fi
  done
  if [ "$rc" -ne 0 ]; then
    echo "extract --check: FAIL -- run scripts/extract.sh and commit the result" >&2
    exit 1
  fi
  echo "extract --check: OK (committed $subdir matches $crate_dir)"
else
  mkdir -p "$committed"
  for f in "${gen_files[@]}"; do
    cp "$out/$f" "$committed/$f"
  done
  echo "extract: wrote ${#gen_files[@]} files to proof/$subdir"
fi
