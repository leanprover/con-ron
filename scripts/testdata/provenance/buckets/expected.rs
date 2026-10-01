//! The citing side of the bucket fixture: one item per bucket of
//! `provenance.py update --auto` (task #108), cited at the OLD tree.

/// con-leche: ConLeche/A.lean:6-7 one
/// Unchanged; moves down three lines (MOVED, not a finding).
pub fn one() {}

/// con-leche: ConLeche/A.lean:9-10 two
/// A docstring edit (doc-only).
pub fn two() {}

/// con-leche: ConLeche/A.lean:12 three
/// An end-of-line `--` comment edit (doc-only).
pub fn three() {}

/// con-leche: ConLeche/A.lean:14-15 four
/// con-leche: CHANGED since @@OLD@@ — re-port, re-test, re-prove citer::four_refines, then delete this line
/// The code changed (changed).
pub fn four() {}

/// con-leche: ConLeche/B.lean:3-4 five
/// Moved to B.lean, byte-identical (moved).
pub fn five() {}

/// con-leche: ConLeche/B.lean:6-7 six
/// Moved to B.lean, its docstring edited (moved-doc).
pub fn six() {}

/// con-leche: ConLeche/B.lean:9-10 seven
/// con-leche: CHANGED since @@OLD@@ — re-port, re-test, re-prove citer::seven_refines, then delete this line
/// Moved to B.lean and changed (moved-changed).
pub fn seven() {}

/// con-leche: ConLeche/A.lean:25-26 Foo.helper
/// con-leche: CHANGED since @@OLD@@ — re-port, re-test, re-prove citer::helper_refines, then delete this line
/// Gone; only `Bar.helper` has the short name (moved-by-name).
pub fn helper() {}

/// con-leche: ConLeche/A.lean:30-31 nine
/// con-leche: CHANGED since @@OLD@@ — re-port, re-test, re-prove citer::nine_refines, then delete this line
/// Gone (deleted).
pub fn nine() {}

/// con-leche: ConLeche/A.lean:36-38 Expr.beqGo
/// con-leche: CHANGED since @@OLD@@ — re-port, re-test, re-prove citer::beq_go_refines, then delete this line
/// Renamed upstream; `Expr` matches by prefix and must not be taken for it
/// (deleted, task #98's trap).
pub fn beq_go() {}

/// con-leche: ConLeche/A.lean:24-27 subst.go
/// A `where` clause cited on its parent, docstring edited (doc-only).
pub fn subst_go() {}

/// con-leche: ConLeche/B.lean:19-20 twelve
/// Its whole file is gone; byte-identical in B.lean (moved).
pub fn twelve() {}
