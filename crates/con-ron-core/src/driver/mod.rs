//! The driver over `CheckerIo` (DESIGN.md §3.9, task #171): con-leche's
//! `ConLeche/Driver/*.lean`, one module per file the port has, written once
//! over the traits of `frontend::checker_io` and run by `crates/con-ron`'s
//! `StdIo`.
//!
//! | Rust | con-leche |
//! |---|---|
//! | `cli` | `Driver/Cli.lean` (the argument parser, `runArgs`) |
//! | `check_main` | `Driver/CheckMain.lean` (the check of a lean4export file) |
//! | `compare_json` | `Driver/CompareJson.lean` (a lean4export file with a solution) |
//!
//! `-- <file>` and `--compare -- <c> <s>` (and `--help`, the usage errors) run
//! here; every other request is the instance's `run_legacy`, the unverified
//! driver of `crates/con-ron`.

pub mod check_main;
pub mod cli;
pub mod compare_json;
