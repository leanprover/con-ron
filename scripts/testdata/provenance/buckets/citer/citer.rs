//! The citing side of the bucket fixture: one item per bucket of
//! `provenance.py update --auto` (task #108), cited at the OLD tree.

/// con-leche: ConLeche/A.lean:3-4 one
/// Unchanged; moves down three lines (MOVED, not a finding).
pub fn one() {}

/// con-leche: ConLeche/A.lean:6-7 two
/// A docstring edit (doc-only).
pub fn two() {}

/// con-leche: ConLeche/A.lean:9 three
/// An end-of-line `--` comment edit (doc-only).
pub fn three() {}

/// con-leche: ConLeche/A.lean:11-12 four
/// The code changed (changed).
pub fn four() {}

/// con-leche: ConLeche/A.lean:14-15 five
/// Moved to B.lean, byte-identical (moved).
pub fn five() {}

/// con-leche: ConLeche/A.lean:17-18 six
/// Moved to B.lean, its docstring edited (moved-doc).
pub fn six() {}

/// con-leche: ConLeche/A.lean:20-21 seven
/// Moved to B.lean and changed (moved-changed).
pub fn seven() {}

/// con-leche: ConLeche/A.lean:25-26 Foo.helper
/// Gone; only `Bar.helper` has the short name (moved-by-name).
pub fn helper() {}

/// con-leche: ConLeche/A.lean:30-31 nine
/// Gone (deleted).
pub fn nine() {}

/// con-leche: ConLeche/A.lean:36-38 Expr.beqGo
/// Renamed upstream; `Expr` matches by prefix and must not be taken for it
/// (deleted, task #98's trap).
pub fn beq_go() {}

/// con-leche: ConLeche/A.lean:40-43 subst.go
/// A `where` clause cited on its parent, docstring edited (doc-only).
pub fn subst_go() {}

/// con-leche: ConLeche/C.lean:3-4 twelve
/// Its whole file is gone; byte-identical in B.lean (moved).
pub fn twelve() {}

/// con-leche: ConLeche/C.lean:8-9 Baz.thirteen
/// Under another namespace now, byte-identical: found by its short name
/// and trusted because the text is the same (moved).
pub fn thirteen() {}
