//! Modular checking (task #166): con-leche's `ConLeche/Driver/{Graph,Reach,Worker}.lean`,
//! the verified core of `--check-graph`, `--module` and `--modular`, one Rust
//! module per Lean file.
//!
//! | Rust | Lean twin | con-leche |
//! |---|---|---|
//! | `graph` | `Arena/Modular/Graph.lean` | `Driver/Graph.lean` (the closure, its order, its verdict) |
//! | `reach` | `Arena/Modular/Reach.lean` | `Driver/Reach.lean` (a worker's context) |
//! | `worker` | `Arena/Modular/Worker.lean` | `Driver/Worker.lean` (a worker's reads and records) |
//!
//! The reads a worker makes before its own records (the header fixpoint, the
//! name index, the clash rule, freshness) are `frontend::olean::{levels, index}`;
//! the imported constants' reads `frontend::olean::{present, group}`.

pub mod graph;
pub mod reach;
pub mod worker;
