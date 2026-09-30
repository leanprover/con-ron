//! `arena::fenv` — the indexed environment's guard twins.
//!
//! The Rust twin of `proof/ConRon/Arena/FEnv.lean`, which is itself the
//! seven `F`-suffixed NAMES of `ConLeche/Kernel/FEnv.lean` and nothing else.
//!
//! con-leche's `FEnv.lean` is fourteen declarations: the indexed environment
//! `FEnv` and its five operations, and the seven `F`-suffixed guard twins that
//! read the environment *through the index* rather than through the
//! association list.  **The arena splits them the other way round**, and this
//! module records why:
//!
//! * the environment half — `IFEnv`, `mk_ifenv_go`, `mk_ifenv`, `ifenv_find`,
//!   `ifenv_restrict_to`, `ifenv_push`, `ifenv_find_proj` — is `arena::env`'s
//!   (task #97e), because the arena has ONE environment type and the
//!   declaration layer is where it belongs;
//! * the guard half is `arena::core`'s, as the ONE twin of each con-leche PAIR
//!   (`natLitSupported` / `natLitSupportedF`, and its six siblings).
//!   con-leche needs two spellings because its kernel tier reads `Env` and its
//!   `Cached` tier reads `FEnv`; the arena's checker reads `IFEnv` and nothing
//!   else (DESIGN.md §8.3, lesson 13), so the two collapse.
//!
//! The import order forces the split: con-leche's `FEnv.lean` imports
//! `Core.lean`, while the arena's `Core.lean` has to CALL the guards from
//! inside `whnfCoreBody` and `inferBody`.  So the bodies are where the guards
//! must be defined, and what is left for this module is the seven `F`-suffixed
//! NAMES — which P4d, the census and anyone reading con-leche's `Cached` tier
//! beside the arena will look for.  The twin makes them `abbrev`s, so that
//! they are the same function and no second definition exists to drift; the
//! Rust makes them one-line delegations, which is the same thing after
//! inlining.








