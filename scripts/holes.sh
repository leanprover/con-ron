#!/usr/bin/env bash
# scripts/holes.sh — THE HOLE LIST (task #95).
#
#   scripts/holes.sh            print every external hole, one per line
#   scripts/holes.sh --check    …and check OVERVIEW.md §7.1's table against it
#
# WHAT A HOLE IS.  The theorem covers the verified crate *as Aeneas translates
# it*.  Everything the translator does not see is trusted, and the sharpest,
# most mechanical part of that trust surface is the set of items Aeneas could
# not translate and asked us to model by hand: another crate's type or function
# (`alloc::sync::Arc`, `core::str::as_bytes`), or an item of this crate marked
# opaque on purpose.  Those are the *holes*.  Each one is a definition someone
# wrote by hand, in `proof/ConRon/Generated/TypesExternal.lean` and
# `FunsExternal.lean`, and the theorem is only about the binary to the extent
# that each of those definitions is a faithful account of the Rust.
#
# So the list has to be visible, and it has to be in the user-facing document
# with its models and its justifications — which is OVERVIEW.md §7.1's table,
# and which `--check` keeps honest.
#
# WHICH SOURCE IS AUTHORITATIVE, AND WHY IT IS THE TEMPLATES.  There are three
# candidates and only one of them is both authoritative and cheap:
#
#   * The **templates** Aeneas emits — `Generated/TypesExternal_Template.lean`
#     and `Generated/FunsExternal_Template.lean`.  This is the translator's own
#     statement of what it could not translate: every declaration in a template
#     is a hole *by construction* (a template holds nothing else — no helper,
#     no lemma), and it is what Aeneas asks us for, not what we chose to
#     answer.  Both files are **committed**, and `scripts/extract.sh --check`
#     (gate 8) fails if they are not what today's crate extracts to.  So the
#     templates are authoritative AND readable in milliseconds with no build.
#     *This is the source this script reads.*
#
#   * The **hand-written models** — `TypesExternal.lean`, `FunsExternal.lean`.
#     These are what we *answered*, not what was asked, and they cannot
#     identify the holes reliably: the `@[rust_type]`/`@[rust_fun]` attribute
#     is present only on the holes Aeneas maps by name pattern, and a hole that
#     is an opaque item of *this* crate comes out of the template as a bare
#     `axiom` with no attribute at all (commit `8e7cb88c`, found by task #94's
#     spike).  A hand file's unattributed `def` is therefore indistinguishable
#     from a helper the modeller added for convenience.
#
#   * Re-running the extraction.  Authoritative, and minutes of Charon and
#     Aeneas for a list that is already sitting in the tree.
#
# The two agree: `extract.sh` steps 3a/3b fail unless every hole a template
# declares — by attribute *and* by declaration — is modelled in the
# corresponding hand file.  That gate is what lets this one read the templates
# and still be a statement about the models.
#
# NO BUILD REQUIRED.  Pure text over two committed files (and, for `--check`,
# over `OVERVIEW.md`); it costs milliseconds, like `scripts/overview-links.sh`.
set -u
cd "$(dirname "$0")/.."

GEN=proof/ConRon/Generated
TYPES_TMPL=$GEN/TypesExternal_Template.lean
FUNS_TMPL=$GEN/FunsExternal_Template.lean
DOC=OVERVIEW.md
# The table is delimited by HTML comments so that the gate never has to guess
# where a markdown section ends (and so that a row can be added to some *other*
# table of §7 without this gate having an opinion about it).
BEGIN_MARK='<!-- holes: begin'
END_MARK='<!-- holes: end'

check=0
case "${1:-}" in
  --check) check=1 ;;
  "") ;;
  *) echo "usage: scripts/holes.sh [--check]" >&2; exit 2 ;;
esac
[ "$#" -le 1 ] || { echo "usage: scripts/holes.sh [--check]" >&2; exit 2; }

for f in "$TYPES_TMPL" "$FUNS_TMPL"; do
  [ -f "$f" ] || {
    echo "holes: FAIL — $f is missing; run scripts/extract.sh" >&2; exit 1; }
done

# Every declaration of a template is an `axiom`; the name is what a hand model
# must define and what OVERVIEW's table must carry in backticks.  (An axiom's
# signature may run over several lines, so anchor on the keyword only.)
axioms() {
  { grep -oP '^axiom\s+\K[A-Za-z_][A-Za-z0-9_.\x27]*' "$1" || true; } \
    | LC_ALL=C sort -u
}

types=$(axioms "$TYPES_TMPL")
funs=$(axioms "$FUNS_TMPL")

listing=$(
  [ -n "$types" ] && printf '%s\n' "$types" | sed 's/^/type /'
  [ -n "$funs" ]  && printf '%s\n' "$funs"  | sed 's/^/fn /'
)
names=$(printf '%s\n' "$listing" | sed 's/^[a-z]* //' | LC_ALL=C sort -u)
ntypes=$(printf '%s\n' "$types" | grep -c . || true)
nfuns=$(printf '%s\n' "$funs" | grep -c . || true)

if [ "$check" = 0 ]; then
  printf '%s\n' "$listing"
  exit 0
fi

# --- the gate -------------------------------------------------------------
#
# The table's first column carries the Lean name of the hole in backticks, and
# nothing else does; so the row set is exactly the set of backticked names in
# the first cell of every row between the two markers.
[ -f "$DOC" ] || { echo "holes: FAIL — $DOC is missing" >&2; exit 1; }

block=$(awk -v b="$BEGIN_MARK" -v e="$END_MARK" '
  index($0, b) { inside = 1; next }
  index($0, e) { inside = 0 }
  inside' "$DOC")
if [ -z "$block" ]; then
  echo "holes: FAIL — $DOC has no '$BEGIN_MARK … $END_MARK' block (§7.1's table)" >&2
  exit 1
fi
rows=$(printf '%s\n' "$block" | grep '^|' \
  | awk -F'|' '{ print $2 }' \
  | { grep -oP '`\K[A-Za-z_][A-Za-z0-9_.\x27]*(?=`)' || true; } \
  | LC_ALL=C sort -u)

rc=0
while IFS= read -r name; do
  [ -n "$name" ] || continue
  if ! printf '%s\n' "$rows" | grep -qxF -- "$name"; then
    echo "holes: FAIL — the hole \"$name\" has no row in $DOC §7.1" >&2
    echo "       (it is declared by $GEN/*External_Template.lean; add a row" >&2
    echo "        giving its Lean model and why that model is faithful)" >&2
    rc=1
  fi
done <<< "$names"
while IFS= read -r name; do
  [ -n "$name" ] || continue
  if ! printf '%s\n' "$names" | grep -qxF -- "$name"; then
    echo "holes: FAIL — $DOC §7.1 has a row for \"$name\", which is not a hole" >&2
    echo "       (nothing in $GEN/*External_Template.lean declares it; the row" >&2
    echo "        is stale — drop it, or fix the name)" >&2
    rc=1
  fi
done <<< "$rows"

if [ "$rc" -ne 0 ]; then
  echo "holes: the list is scripts/holes.sh; the table is $DOC §7.1" >&2
  exit 1
fi
echo "holes: $ntypes type(s), $nfuns fn(s), all in $DOC §7.1, OK"
