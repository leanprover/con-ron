#!/usr/bin/env bash
# Produce `_tmp/aeneas-lean/`: a copy of `vendor/aeneas/backends/lean` with
# `spikes/toolchain/aeneas-433.patch` applied, so that the Aeneas Lean library
# builds on con-leche's toolchain (leanprover/lean4:v4.33.0 + Mathlib v4.33.0).
# See DESIGN.md, task #2.
#
# Idempotent: a stamp records the patch's and the source tree's hashes; a
# second run with nothing changed is a no-op and, crucially, keeps the
# existing `.lake/` (rebuilding Mathlib's dependents costs minutes).
#
# Exits non-zero if the patch does not apply cleanly to the pinned Aeneas
# submodule -- that is the signal that the submodule moved and the patch needs
# rebasing.
#
# Usage: scripts/setup-aeneas-lean.sh [--force] [--no-update]
set -euo pipefail

root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
src="$root/vendor/aeneas/backends/lean"
patch_file="$root/spikes/toolchain/aeneas-433.patch"
dest="$root/_tmp/aeneas-lean"
stamp="$dest/.con-ron-setup-stamp"

force=0
do_update=1
for arg in "$@"; do
  case "$arg" in
    --force) force=1 ;;
    --no-update) do_update=0 ;;
    *) echo "usage: $0 [--force] [--no-update]" >&2; exit 2 ;;
  esac
done

[ -d "$src" ] || { echo "error: $src missing (git submodule update --init?)" >&2; exit 1; }
[ -f "$patch_file" ] || { echo "error: $patch_file missing" >&2; exit 1; }

# The identity of the inputs: every tracked source byte plus the patch.
fingerprint() {
  {
    ( cd "$src" && find . -path ./.lake -prune -o -type f -print0 | sort -z \
        | xargs -0 sha256sum )
    sha256sum "$patch_file" | awk '{print $1}'
  } | sha256sum | awk '{print $1}'
}
want="$(fingerprint)"

if [ "$force" -eq 0 ] && [ -f "$stamp" ] && [ "$(cat "$stamp")" = "$want" ]; then
  echo "aeneas-lean: up to date ($dest)"
  exit 0
fi

work="$root/_tmp/.aeneas-lean.new.$$"
rm -rf "$work"
mkdir -p "$work"
trap 'rm -rf "$work"' EXIT

# 1. copy the pinned library (never the build tree)
tar -C "$src" --exclude=./.lake -cf - . | tar -C "$work" -xf -

# 2. apply the 4.33 patch -- must be clean
if ! ( cd "$work" && patch -p1 --forward --dry-run < "$patch_file" ); then
  echo "error: $patch_file does not apply cleanly to $src" >&2
  echo "       (the aeneas submodule probably moved; rebase the patch)" >&2
  exit 1
fi
( cd "$work" && patch -p1 --forward -s < "$patch_file" )

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
#    patch: upstream pins Mathlib v4.31.0 and the patched lakefile asks for
#    v4.33.0, so the manifest has to be regenerated rather than carried.
if [ "$do_update" -eq 1 ] && [ ! -f "$dest/lake-manifest.json" ]; then
  echo "aeneas-lean: lake update (this fetches Mathlib v4.33.0)"
  ( cd "$dest" && lake update )
fi

# 5. let `proof/` share this package set instead of cloning Mathlib twice.
#    Lake keeps git dependencies under the ROOT package's `.lake/packages`, so
#    without this the proof project would fetch its own Mathlib checkout (and
#    build it).  Both roots resolve Mathlib to the same rev (the `v4.33.0` tag
#    the patched lakefile asks for), so one checkout serves both.
proof_pkgs="$root/proof/.lake/packages"
if [ -d "$root/proof" ] && [ ! -e "$proof_pkgs" ]; then
  mkdir -p "$root/proof/.lake"
  ln -s "../../_tmp/aeneas-lean/.lake/packages" "$proof_pkgs"
  echo "aeneas-lean: linked proof/.lake/packages -> $dest/.lake/packages"
fi

echo "$want" > "$stamp"
echo "aeneas-lean: ready at $dest"
