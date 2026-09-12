#!/usr/bin/env bash
# Style gate for the Aeneas-facing Rust (DESIGN.md §3.4).
# Usage: scripts/lint-rust-style.sh [dir ...]   (default: crates/con-ron-core/src)
set -u
dirs=("$@"); [ ${#dirs[@]} -eq 0 ] && dirs=(crates/con-ron-core/src)
fail=0
check() { # check <label> <regex>
  local label=$1 re=$2 hits
  hits=$(grep -rnE --include='*.rs' "$re" "${dirs[@]}" 2>/dev/null | grep -v '^\S*:\S*:\s*//' | grep -v 'lint: allow')
  if [ -n "$hits" ]; then echo "== $label"; echo "$hits"; fail=1; fi
}
check "derive(Debug) (mixed recursion groups in Charon)" 'derive\([^)]*Debug'
check "closures" '\|[a-z_,& ]*\|\s*(\{|[a-z])'
check "? operator" '\)\?[;.) ]|\)\?$'
check "loops (use recursion; -loops-to-rec only in leaf helpers)" '^\s*(while|for|loop)\b'
check "unsafe" '\bunsafe\b'
check "std::collections" 'std::collections'
check "Rc API beyond new/clone/deref/ptr_eq" 'Rc::(get_mut|make_mut|downgrade|try_unwrap|into_raw|from_raw|strong_count|weak_count)|RefCell|Cell<'
check "panics as control flow" '\b(panic!|unwrap\(\)|expect\(|unreachable!|todo!|unimplemented!)'
exit $fail
