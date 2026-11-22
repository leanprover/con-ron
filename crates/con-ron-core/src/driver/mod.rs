//! The driver over `CheckerIo` (DESIGN.md §3.9, task #171): con-leche's
//! `ConLeche/Driver/*.lean`, one module per file the port has, written once
//! over the traits of `frontend::checker_io` and run by `crates/con-ron`'s
//! `StdIo`.
//!
//! | Rust | con-leche |
//! |---|---|
//! | `cli` | `Driver/Cli.lean` (the argument parser, `runArgs`) |
//! | `check_main` | `Driver/CheckMain.lean` (the check of a lean4export file, of an `.olean` closure) |
//! | `compare_json` | `Driver/CompareJson.lean` (a lean4export file with a solution) |
//! | `compare` | `Driver/Compare.lean` (`--olean --compare`) |
//! | `compare_module` | `Driver/CompareModule.lean` (the compare worker, `--check-graph --compare`) |
//! | `graph` | `Driver/Graph.lean` (`--check-graph`) |
//! | `worker` | `Driver/Worker.lean` (a module's worker: `--olean --module`) |
//! | `modular` | `Driver/Modular.lean` (`--olean --modular`) |
//!
//! `--schedule` (con-leche's scheduler is `liftIO`) and `--modular --pins` are
//! the instance's `run_legacy`, the unverified driver of `crates/con-ron`.

pub mod check_main;
pub mod cli;
pub mod compare;
pub mod compare_json;
pub mod compare_module;
pub mod graph;
pub mod modular;
pub mod worker;
