//! con-leche: none — the shared-pointer type of DESIGN.md §3.2; Lean's value semantics have no counterpart.
//!
//! `ron::ptr` — **the one place the core names its shared pointer**
//! (DESIGN.md §3.2, task #44).
//!
//! con-leche's terms are persistent trees with sharing, which the port gives
//! reference counting: `P<T>` is the handle, and the model erases it
//! (`Arc T := T`, plus four definitions).  Which *concrete* counted pointer
//! stands behind `P` is a performance question and nothing else — the four
//! operations below are the entire API the §3.2 model allows, and every one of
//! them is the identity in Lean — so this module exists so that the choice is
//! **one line**.  The alias in force, since task #45, is atomic:
//!
//! ```ignore
//! pub type P<T> = std::sync::Arc<T>; // in force: atomic; `Send + Sync`
//! pub type P<T> = std::rc::Rc<T>;    // the other configuration: non-atomic
//! ```
//!
//! Going back to `Rc` is that one line **plus** the matching rename in the two
//! hand-written model files: `proof/ConRon/Generated/TypesExternal.lean` and
//! `FunsExternal.lean` model the hole *by name*, so `alloc.sync.Arc` becomes
//! `alloc.rc.Rc` there (and in the `Refine/*` lemma names that mention it,
//! whose current spelling is `arc_*`).  That is why the choice is a documented
//! edit and **not** a cargo feature: a feature would have to select between two
//! hand-written Lean files, which the extraction gate checks against the
//! template Charon emits for whichever alias is compiled.
//!
//! # The four operations, and why there are only four
//!
//! | here | `Arc`/`Rc` | model |
//! |---|---|---|
//! | [`new`] | `Arc::new` | `ok x` |
//! | [`clone`] | `Arc::clone` | `ok x` |
//! | *(deref)* | `Deref::deref`, i.e. `*p` and every auto-deref | `ok x` |
//! | [`ptr_eq`] | `Arc::ptr_eq` | `ok false` |
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
//! # Why the alias is atomic (tasks #44, #45)
//!
//! The parallel check phase needs the installed environment shared across
//! threads, which needs the handle to be `Send + Sync`, which `Rc` is not.
//! §3's first sketch bought that with the core's own counted pointer, an
//! immortal sentinel and an `unsafe impl Send + Sync`; the maintainer's
//! ruling of 2026-09-12 is that `std` (or a common crate) does it instead if
//! it can, and `std::sync::Arc` can — at zero `unsafe`, zero model change and
//! zero proof obligations.  Task #44 priced it on a quiet machine,
//! single-threaded: **+14.7 % wall on `core`** (+17.2 % on `init`) at an
//! *unchanged instruction count* — the atomics are stalls, not work.  The
//! maintainer's decision of the same day is to **pay it** for a safe,
//! `unsafe`-free pool (con-leche measures `--jobs=8` at ~3.5×), and task #45
//! landed the swap.  DESIGN.md §3.2 and the task-#44 entry have the table,
//! `triomphe::Arc`'s column (atomic, 8 bytes leaner, and the slowest of the
//! three) and the ways back.
//!
//! What the swap buys, asserted by a compile-only test in `tests/`: `Name`,
//! `Level`, `Expr`, `Env`, `FEnv` and `CState` are all `Send + Sync` with no
//! `unsafe` and no other change.  Under `Rc` that test fails with eight errors
//! that name **only** `Rc<ExprNode>`, `Rc<NameNode>`, `Rc<LevelNode>` and
//! `Rc<ConstantInfo>`: nothing else in the core — no `Cell`, no `RefCell`, no
//! raw pointer, no handle outside this alias — stands between the checker and
//! a thread pool.

/// con-leche: none — the shared pointer itself (DESIGN.md §3.2)
/// The core's shared pointer: a counted handle to an immutable `T`.
///
/// Modeled as `T` (`alloc.sync.Arc T := T`), so nothing in the proof tier
/// sees it; see the module note for the four operations that are allowed on
/// it and DESIGN.md §3.2 for the measurement behind the alias in force.
///
/// **This is the one line.**  `std::rc::Rc<T>` is the other configuration
/// (non-atomic, ~15 % faster at one worker, not `Send`); swapping it back also
/// means renaming `alloc.sync.Arc` to `alloc.rc.Rc` in the two hand-written
/// model files, as the module note says.
pub type P<T> = std::sync::Arc<T>;

/// con-leche: none — `Arc::new`, modeled as the identity (DESIGN.md §3.2)
/// Allocate a node and take the first handle to it.
pub fn new<T>(x: T) -> P<T> {
    P::new(x)
}

/// con-leche: none — `Arc::clone`, modeled as the identity (DESIGN.md §3.2)
/// Share a node: a count bump, no copy of `T`.
pub fn clone<T>(p: &P<T>) -> P<T> {
    P::clone(p)
}

/// con-leche: none — `Arc::ptr_eq`, modeled as `false` (DESIGN.md §3.2)
/// Do the two handles point at the *same* node?  The fast path of every
/// structural walk that has one; modeled as `false`, so the model always
/// descends and each use needs a reflexivity lemma (§3.2).
pub fn ptr_eq<T>(a: &P<T>, b: &P<T>) -> bool {
    P::ptr_eq(a, b)
}
