#!/usr/bin/env bash
# Produce `_tmp/aeneas-lean-<tag>/`: a copy of `vendor/aeneas/backends/lean`
# with `patches/aeneas.patch` applied, set to the project's toolchain, so that
# the Aeneas Lean library builds on con-leche's Lean and its Mathlib.  See
# DESIGN.md, tasks #2 and #110.
#
# <tag> is the version part of `proof/lean-toolchain` (`v4.35.0-rc3` for
# `leanprover/lean4:v4.35.0-rc3`).  The directory is keyed by it so that a
# sync that moves the toolchain (task #110) builds the new library beside the
# old one, which every other worktree keeps reading until it merges the move;
# `proof/lakefile.toml`'s `aeneas` path names the same directory (checked).
# The toolchain and the Mathlib tag are not in the patch: the script writes
# `lean-toolchain` and the `require mathlib … @ "<tag>"` line itself, so the
# patch holds only genuine source changes.
#
# Idempotent: a stamp records the patch's, the toolchain's and the source
# tree's hashes; a second run with nothing changed is a no-op and, crucially,
# keeps the existing `.lake/` (rebuilding Mathlib's dependents costs minutes).
#
# Exits non-zero if the patch does not apply cleanly to the pinned Aeneas
# submodule -- that is the signal that the submodule moved and the patch needs
# rebasing.
#
# Usage: scripts/setup-aeneas-lean.sh [--force] [--no-update] [--print-dest]
set -euo pipefail

root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
src="$root/vendor/aeneas/backends/lean"
patch_file="$root/patches/aeneas.patch"
toolchain="$(tr -d '[:space:]' < "$root/proof/lean-toolchain")"
tag="${toolchain##*:}"
dest="${AENEAS_LEAN_DEST:-$root/_tmp/aeneas-lean-$tag}"  # override for testing the script itself
stamp="$dest/.con-ron-setup-stamp"

force=0
do_update=1
for arg in "$@"; do
  case "$arg" in
    --force) force=1 ;;
    --no-update) do_update=0 ;;
    --print-dest) echo "$dest"; exit 0 ;;
    *) echo "usage: $0 [--force] [--no-update] [--print-dest]" >&2; exit 2 ;;
  esac
done

[ -d "$src" ] || { echo "error: $src missing (git submodule update --init?)" >&2; exit 1; }
[ -f "$patch_file" ] || { echo "error: $patch_file missing" >&2; exit 1; }
if [ -z "${AENEAS_LEAN_DEST:-}" ] && ! grep -q "^path = \"../_tmp/aeneas-lean-$tag\"" "$root/proof/lakefile.toml"; then
  echo "error: proof/lakefile.toml's aeneas path is not ../_tmp/aeneas-lean-$tag (proof/lean-toolchain is $toolchain)" >&2
  exit 1
fi

# The identity of the inputs: every tracked source byte, the patch, the toolchain.
fingerprint() {
  {
    echo "$toolchain"
    ( cd "$src" && find . -path ./.lake -prune -o -type f -print0 | sort -z \
        | xargs -0 sha256sum )
    sha256sum "$patch_file" | awk '{print $1}'
  } | sha256sum | awk '{print $1}'
}
want="$(fingerprint)"

# Let `proof/` share this package set instead of cloning Mathlib twice.
# Lake keeps git dependencies under the ROOT package's `.lake/packages`, so
# without this the proof project would fetch its own Mathlib checkout (and
# build it).  Both roots resolve Mathlib to the same rev (the <tag> tag the
# lakefile asks for), so one checkout serves both.  A link to ANOTHER
# toolchain's `_tmp/aeneas-lean*` directory (this tree just merged a
# toolchain move) is repointed; any other link (a bump's private copy) and a
# real directory are left alone.
link_proof() {
  proof_pkgs="$root/proof/.lake/packages"
  want_link="../../_tmp/$(basename "$dest")/.lake/packages"
  if [ -d "$root/proof" ] && [ -z "${AENEAS_LEAN_DEST:-}" ]; then
    if [ -L "$proof_pkgs" ] && [ "$(readlink "$proof_pkgs")" != "$want_link" ] \
       && [[ "$(readlink "$proof_pkgs")" == *_tmp/aeneas-lean*/.lake/packages ]]; then
      echo "aeneas-lean: proof/.lake/packages was -> $(readlink "$proof_pkgs"); repointing"
      rm "$proof_pkgs"
    fi
    if [ ! -e "$proof_pkgs" ] && [ ! -L "$proof_pkgs" ]; then
      mkdir -p "$root/proof/.lake"
      ln -s "$want_link" "$proof_pkgs"
      echo "aeneas-lean: linked proof/.lake/packages -> $dest/.lake/packages"
    fi
  fi
}

if [ "$force" -eq 0 ] && [ -f "$stamp" ] && [ "$(cat "$stamp")" = "$want" ]; then
  echo "aeneas-lean: up to date ($dest)"
  link_proof
  exit 0
fi

work="$root/_tmp/.aeneas-lean.new.$$"
rm -rf "$work"
mkdir -p "$work"
trap 'rm -rf "$work"' EXIT

# 1. copy the pinned library (never the build tree, and never upstream's
#    manifest: it pins the Mathlib of upstream's toolchain, and carrying it
#    is what made a fresh machine's `lake exe cache get` fetch the wrong
#    Mathlib — task #82)
tar -C "$src" --exclude=./.lake --exclude=./lake-manifest.json -cf - . | tar -C "$work" -xf -

# 2. apply the patch -- must be clean -- and set the toolchain and Mathlib tag
if ! ( cd "$work" && patch -p1 --forward --dry-run < "$patch_file" ); then
  echo "error: $patch_file does not apply cleanly to $src" >&2
  echo "       (the aeneas submodule probably moved; rebase the patch)" >&2
  exit 1
fi
( cd "$work" && patch -p1 --forward -s < "$patch_file" )
echo "$toolchain" > "$work/lean-toolchain"
sed -i -E "s#(mathlib4\.git\" @ \")[^\"]*(\")#\1$tag\2#" "$work/lakefile.lean"
grep -q "mathlib4.git\" @ \"$tag\"" "$work/lakefile.lean" \
  || { echo "error: could not set the Mathlib tag in $work/lakefile.lean" >&2; exit 1; }

# 3. carry the previous build tree and manifest over, then swap in place
if [ -d "$dest/.lake" ]; then
  mv "$dest/.lake" "$work/.lake"
fi
if [ -f "$dest/lake-manifest.json" ]; then
  cp "$dest/lake-manifest.json" "$work/lake-manifest.json"
fi

rm -rf "$dest.old"
if [ -e "$dest" ]; then mv "$dest" "$dest.old"; fi
mkdir -p "$(dirname "$dest")"
mv "$work" "$dest"
trap - EXIT
rm -rf "$dest.old"

# 4. resolve dependencies.  `lake-manifest.json` is deliberately not in the
#    patch: upstream pins its own Mathlib and the lakefile asks for <tag>, so
#    the manifest has to be regenerated rather than carried.
#    The update runs when there is no manifest, or when the manifest's
#    Mathlib is not the one the patched lakefile asks for.
mathlib_rev="$(sed -n 's/.*mathlib4.git" @ "\([^"]*\)".*/\1/p' "$dest/lakefile.lean" | head -1)"
if [ "$do_update" -eq 1 ]; then
  if [ ! -f "$dest/lake-manifest.json" ] \
     || ! grep -q "\"inputRev\": \"$mathlib_rev\"" "$dest/lake-manifest.json"; then
    echo "aeneas-lean: lake update (this fetches Mathlib $mathlib_rev)"
    ( cd "$dest" && lake update )
  fi
fi

# 5. the proof project shares the package set
link_proof
echo "$want" > "$stamp"
echo "aeneas-lean: ready at $dest"
