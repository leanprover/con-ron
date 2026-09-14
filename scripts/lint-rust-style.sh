#!/usr/bin/env bash
# Style gate for the Aeneas-facing Rust (DESIGN.md §3.4).
# Usage: scripts/lint-rust-style.sh [dir ...]   (default: crates/con-ron-core/src)
#
# `#[cfg(test)]` modules are exempt: Charon never sees them (they are not in
# the non-test build), so they may use closures, iterators and loops.
set -u
dirs=("$@"); [ ${#dirs[@]} -eq 0 ] && dirs=(crates/con-ron-core/src)
# Every source line before the first `#[cfg(test)]`, as `file:line:text`.
gather() {
  local f
  find "${dirs[@]}" -name '*.rs' -type f 2>/dev/null | sort | while read -r f; do
    awk -v F="$f" '/#\[cfg\(test\)\]/ { exit } { printf "%s:%d:%s\n", F, NR, $0 }' "$f"
  done
}
fail=0
check() { # check <label> <regex>
  local label=$1 re=$2 hits
  hits=$(gather | grep -E "$re" | grep -v '^\S*:\S*:\s*//' | grep -v 'lint: allow')
  if [ -n "$hits" ]; then echo "== $label"; echo "$hits"; fail=1; fi
}
check "derive(Debug) (mixed recursion groups in Charon)" 'derive\([^)]*Debug'
# A closure bar has at least one character between the bars, which is what
# keeps `a || b` and `x | y` out (`||` and `|_|`-less bars are not closures).
check "closures" '\|\s*(_|mut |&|[a-z])[a-z_0-9,&: ]*\|\s*(\{|[a-z])'
check "? operator" '\)\?[;.) ]|\)\?$'
# Loops.  The rule is recursion (DESIGN.md §3.4); the ONE exemption is
# `crates/con-ron-core/src/frontend/`, the ported parser (task #84): the Lean
# it cites is a per-byte tail recursion that *Lean* compiles to a loop, and a
# per-byte recursion in Rust overflows the stack on a long export line.
# `-loops-to-rec` gives each loop a `foo_loop` function that mirrors the Lean
# recursion one for one.  (The `:[0-9]+:` is the `file:line:` prefix `gather`
# adds: a `^\s*` anchor here matched nothing at all until task #84 noticed.)
check_loops() {
  local hits
  hits=$(gather | grep -E ':[0-9]+:[[:space:]]*(while|for|loop)\b' \
    | grep -v '^\S*:\S*:\s*//' | grep -v 'lint: allow' \
    | grep -v '^crates/con-ron-core/src/frontend/')
  if [ -n "$hits" ]; then
    echo "== loops (use recursion; only crates/con-ron-core/src/frontend/ may loop, DESIGN.md §3.4)"
    echo "$hits"; fail=1
  fi
}
check_loops
check "unsafe" '\bunsafe\b'
check "std::collections" 'std::collections'
check "P/Rc/Arc API beyond new/clone/deref/ptr_eq" '\b(P|Rc|Arc)::(get_mut|make_mut|downgrade|try_unwrap|into_raw|from_raw|as_ptr|strong_count|weak_count|increment_strong_count|decrement_strong_count)|RefCell|Cell<'
check "panics as control flow" '\b(panic!|unwrap\(\)|expect\(|unreachable!|todo!|unimplemented!)'
exit $fail
