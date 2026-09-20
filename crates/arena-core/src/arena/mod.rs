//! The arena: handles and the four interned stores (DESIGN.md §8.3/§8.5).
//!
//! | Rust | Lean twin |
//! |---|---|
//! | `handle` | `proof/ConRon/Arena/Handle.lean` |
//! | `store` | `proof/ConRon/Arena/Store.lean` |
//!
//! `Denote.lean`, `WF.lean` and `WFProofs.lean` have no Rust counterpart and
//! never will: they are the arena's own verification (DESIGN.md §8.6's P2a,
//! con-leche's lesson 27), stated about the Lean twin.

pub mod handle;
pub mod expr_ops;
pub mod monad;
pub mod env;
pub mod store;
