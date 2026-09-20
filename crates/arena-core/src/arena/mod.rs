//! The arena: handles and the four interned stores (DESIGN.md §8.3/§8.5).
//!
//! | Rust | Lean twin |
//! |---|---|
//! | `handle` | `proof/ConRon/Arena/Handle.lean` |
//! | `store` | `proof/ConRon/Arena/Store.lean` |
//! | `monad` | `proof/ConRon/Arena/Monad.lean` |
//! | `expr_ops` | `proof/ConRon/Arena/ExprOps.lean` |
//! | `env` | `proof/ConRon/Arena/Env.lean` |
//! | `core_state` | `proof/ConRon/Arena/CoreState.lean` |
//! | `prop_read` | `proof/ConRon/Arena/PropRead.lean` |
//! | `core` | `proof/ConRon/Arena/Core.lean` |
//! | `fenv` | `proof/ConRon/Arena/FEnv.lean` |
//! | `core_io` | `proof/ConRon/Arena/CoreIO.lean` |
//! | `core_gated` | `proof/ConRon/Arena/CoreGated.lean` |
//!
//! `Denote.lean`, `WF.lean` and `WFProofs.lean` have no Rust counterpart and
//! never will: they are the arena's own verification (DESIGN.md §8.6's P2a,
//! con-leche's lesson 27), stated about the Lean twin.

pub mod handle;
pub mod store;
pub mod core_state;
pub mod monad;
pub mod expr_ops;
pub mod env;
pub mod prop_read;
pub mod core;
pub mod fenv;
pub mod core_io;
pub mod core_gated;
