//! **The core's values cross threads** (task #45, DESIGN.md §3.2).
//!
//! `ron::ptr::P` is `std::sync::Arc`, and the whole point of paying its ~15 %
//! single-threaded penalty (task #44's table) is that the installed
//! environment can then be shared read-only by a pool of check workers.  That
//! needs `Send + Sync` on the values the workers touch, and this file asserts
//! it *at compile time*: `assert_send_sync::<T>()` does not typecheck unless
//! `T: Send + Sync`, so the assertions below are the test.
//!
//! It is a test rather than a `#[cfg(test)]` module because it is a fact about
//! the crate's public types, and it lives in `tests/` next to the other
//! cross-module one.  Nothing here runs anything: the body is empty and the
//! function is called only so that `cargo test` reports it.
//!
//! This is also the regression guard on the alias.  Swap `ron::ptr::P` back to
//! `std::rc::Rc` and this file stops compiling with errors each naming one of
//! `Rc<NameNode>`, `Rc<LevelNode>`, `Rc<ConstantInfo>` (`Expr`'s own handle is
//! `ron::node`'s since task #94's spike, and carries its own `Send`/`Sync`)
//! — i.e. only the alias, never a `Cell`, a `RefCell` or a raw pointer (§3.4's
//! lint forbids those; this is the independent confirmation).  A future change
//! that puts a non-`Sync` field anywhere in the state will be caught here,
//! before the pool is written rather than after.

use con_ron_core::kernel::env::{ConstantInfo, Env};
use con_ron_core::kernel::expr::Expr;
use con_ron_core::kernel::fenv::FEnv;
use con_ron_core::kernel::level::Level;
use con_ron_core::kernel::name::Name;

/// Typechecks only for `T: Send + Sync`; the whole assertion is the bound.
fn assert_send_sync<T: Send + Sync>() {}

/// The three the pinned data is written in (`Expr`, `FEnv`, `Env`), plus the
/// two handle types underneath them and the value the pinned blocks compare.
/// (`CState` went with the `Expr`-tree checker at task #97-SWAP; the arena's
/// own state is `AState`, and the pool shares a frozen `PersTier` by
/// reference rather than a counted pointer — `crates/con-ron/src/pool.rs`.)
#[test]
fn core_values_are_send_and_sync() {
    assert_send_sync::<Expr>();
    assert_send_sync::<FEnv>();
    assert_send_sync::<Env>();
    assert_send_sync::<Name>();
    assert_send_sync::<Level>();
    assert_send_sync::<ConstantInfo>();
}
