//! con-leche: none — the shared-pointer type of DESIGN.md §3.2; Lean's value semantics have no counterpart.
//!
//! `ron::ptr` — **the one place the core names its shared pointer**
//! (DESIGN.md §3.2, task #44).
//!
//! con-leche's terms are persistent trees with sharing, which the port gives
//! reference counting: `P<T>` is the handle, and the model erases it
//! (`Rc T := T`, plus four definitions).  Which *concrete* counted pointer
//! stands behind `P` is a performance question and nothing else — the four
//! operations below are the entire API the §3.2 model allows, and every one of
//! them is the identity in Lean — so this module exists so that the choice is
//! **one line**:
//!
//! ```ignore
//! pub type P<T> = std::rc::Rc<T>;    // non-atomic; one thread
//! pub type P<T> = std::sync::Arc<T>; // atomic; `Send + Sync`, for the pool
//! ```
//!
//! # The four operations, and why there are only four
//!
//! | here | `Rc`/`Arc` | model |
//! |---|---|---|
//! | [`new`] | `Rc::new` | `ok x` |
//! | [`clone`] | `Rc::clone` | `ok x` |
//! | *(deref)* | `Deref::deref`, i.e. `*p` and every auto-deref | `ok x` |
//! | [`ptr_eq`] | `Rc::ptr_eq` | `ok false` |
//!
//! `deref` is deliberately **not** a function here: the port reads through a
//! handle by `&*p`, `p.field` and pattern matching on `&*p`, which is the
//! `Deref` impl of whatever `P` is, and wrapping it would put a crate
//! function in front of 400-odd generated call sites for no gain.  Everything
//! else — `get_mut`, `make_mut`, `Weak`, `as_ptr`, `into_raw`, the counts —
//! stays out: the model is only faithful because an allocated `P<T>` is an
//! immutable owner, and `scripts/lint-rust-style.sh` gates the excluded names
//! for `P`, `Rc` and `Arc` alike.
//!
//! `ptr_eq` is modeled as `false`, so the model always takes the slow path;
//! each fast path is transparent by a reflexivity lemma (§3.2).
//!
//! The three wrappers are what the generated Lean calls (`ron.ptr.new`,
//! `ron.ptr.clone`, `ron.ptr.ptr_eq`), each one call to the external it
//! renames; `Refine/Abs.lean`'s `ptr_*_eq` simp lemmas make them as invisible
//! to the proofs as the externals were, and the external templates still hold
//! exactly one type and four functions.
//!
//! # Why the alias exists, and what it measured (task #44)
//!
//! The parallel check phase needs the installed environment shared across
//! threads.  §3's first sketch was the core's own counted pointer with an
//! immortal sentinel and an `unsafe impl Send + Sync`; the maintainer's
//! ruling of 2026-09-12 is that `std` (or a common crate) does it instead if
//! it can, and `std::sync::Arc` can.  Task #44 priced that swap on a quiet
//! machine, single-threaded, and the price is **+14.7 % wall on `core`**
//! (+17.2 % on `init`) at *unchanged instruction count* — the atomics are
//! stalls, not work.  Over the brief's 10 % budget, so the alias in force is
//! still `Rc` and the decision is the maintainer's; DESIGN.md's task-#44
//! entry has the table, `triomphe::Arc`'s column and the two ways out.
//!
//! Two facts the pool task inherits.  With `P = std::sync::Arc`, `Name`,
//! `Level`, `Expr`, `Env`, `FEnv` and `CState` are all `Send + Sync` with no
//! `unsafe` and no other change — measured with
//!
//! ```ignore
//! fn assert_send_sync<T: Send + Sync>() {}
//! assert_send_sync::<Expr>();  // and FEnv, Env, CState, Name, Level
//! ```
//!
//! which compiles under `Arc` and, under `Rc`, fails with eight errors that
//! name **only** `Rc<ExprNode>`, `Rc<NameNode>`, `Rc<LevelNode>` and
//! `Rc<ConstantInfo>`: nothing else in the core — no `Cell`, no `RefCell`, no
//! raw pointer, no handle outside this alias — stands between the checker and
//! a thread pool.

/// con-leche: none — the shared pointer itself (DESIGN.md §3.2)
/// The core's shared pointer: a counted handle to an immutable `T`.
///
/// Modeled as `T` (`alloc.rc.Rc T := T`), so nothing in the proof tier sees
/// it; see the module note for the four operations that are allowed on it and
/// DESIGN.md's task #44 for the measurement behind the alias in force.
pub type P<T> = std::rc::Rc<T>;

/// con-leche: none — `Rc::new`, modeled as the identity (DESIGN.md §3.2)
/// Allocate a node and take the first handle to it.
pub fn new<T>(x: T) -> P<T> {
    P::new(x)
}

/// con-leche: none — `Rc::clone`, modeled as the identity (DESIGN.md §3.2)
/// Share a node: a count bump, no copy of `T`.
pub fn clone<T>(p: &P<T>) -> P<T> {
    P::clone(p)
}

/// con-leche: none — `Rc::ptr_eq`, modeled as `false` (DESIGN.md §3.2)
/// Do the two handles point at the *same* node?  The fast path of every
/// structural walk that has one; modeled as `false`, so the model always
/// descends and each use needs a reflexivity lemma (§3.2).
pub fn ptr_eq<T>(a: &P<T>, b: &P<T>) -> bool {
    P::ptr_eq(a, b)
}
