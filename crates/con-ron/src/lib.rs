//! con-ron's **unverified crate**: the binary's `main`, its instance of the
//! verified driver's trait, the worker pool and the scheduler.
//!
//! ```text
//! con-ron [OPTIONS] [--] FILE.ndjson
//! con-ron --help
//! ```
//!
//! **The driver is verified** (DESIGN.md §3.9, task #171): the argument parse,
//! the usage errors, every mode and the verdict are
//! `con_ron_core::driver::cli::run_args`, written once over the trait
//! `con_ron_core::frontend::checker_io::CheckerIo` (con-leche's class
//! `CheckerIO`), and the main theorems (`proof/ConRon/MainTheorem.lean`) are
//! about it.  This crate is what they assume of a run (OVERVIEW §3.1): the
//! binary's instance of the trait, `std_io::StdIo` — the file operations over
//! `std` (`olean_fs`), the worker map (`pool`), the code map, the escapes, and
//! the rendering of every line in the binary's words (`driver`, `render`) —
//! and `main` (`src/bin/con-ron.rs`).  `--schedule` is the one mode that runs
//! here (`modular`, `schedule`), as con-leche's scheduler is `liftIO`.
//!
//! Charon never sees this crate, no refinement lemma mentions it, and §3.4's
//! Aeneas subset does not apply (it uses `for`, `while`, `?`,
//! `std::collections`, closures and `derive(Debug)` freely).  There is no
//! `unsafe`.  It keeps §3.1's mirroring and §3.7's citations: every item
//! carries its `/// con-leche:` line, the only sync signal an unverified module
//! has.
//!
//! | Rust | con-leche |
//! |---|---|
//! | `std_io` | `Frontend/CheckerIO.lean`'s `instCheckerIOIO`: the binary's instance of `CheckerIo` |
//! | `driver` | `Driver/{Cli,CheckMain,Run}.lean`: the flag messages, the heartbeat, the verdict lines |
//! | `pool` | `Driver/CheckPool.lean`: the worker map on a pool of threads |
//! | `olean_fs` | `Frontend/CheckerIO.lean`'s file operations over `std` |
//! | `modular`, `schedule` | `Driver/Schedule.lean`: the scheduler |
//! | `keys` | none — `std::hash::Hash`/`Eq` wrappers for `Expr` and `Name` |
//! | `render` | none — `Name.toString`, which the core's skip list keeps out |
//! | `src/bin/con-ron.rs` | `Main.lean` (the binary's `main`) |
//!
//! **The worker pool** (`pool`) is DESIGN.md §8.3's "the persistent tier is
//! immutable in phase B, each worker owns a scratch tier — no atomics
//! anywhere", with the tier frozen at the phase boundary and shared by
//! reference.  Threads live here and never in `con-ron-core` (§8.5).

pub mod driver;
pub mod keys;
pub mod modular;
pub mod olean_fs;
pub mod pool;
pub mod render;
pub mod schedule;
pub mod std_io;
