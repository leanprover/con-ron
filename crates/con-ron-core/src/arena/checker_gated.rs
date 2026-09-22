//! `arena::checker_gated` — the gated `CheckerOps` instantiations.
//!
//! The Rust twin of `proof/ConRon/Arena/CheckerGated.lean`, itself
//! `ConLeche/Kernel/CheckerGated.lean`'s: `fueledOps`/`pureOps` over the GATED
//! knot (`arena::core_gated`), which is `ConLeche/Kernel/CoreGated.lean`'s
//! verification-tier variant of the six bodies.
//!
//! **Class (S) in the census, and one step thinner here than in the twin.**
//! con-leche's Rust port skips the record entirely, and so does this crate:
//! §3.4 rules out a record of function values, so `CheckerOpsA` has no Rust
//! counterpart at all (`arena::checker_base`'s module note 2) and neither do
//! its three instantiations — `fueledOpsA`, `pureOpsA` and the two here.  What
//! replaces them is exactly what replaces `pureFnsA`: the LANE, a `u32` the
//! six `knot_*` functions of `arena::core` dispatch on
//! (`arena::core`'s `PURE_FNS_A`, `arena::core_io`'s `CORE_KNOT_IO`,
//! `arena::core_gated`'s `CORE_KNOT_GATED`).
//!
//! So this module is the gated declaration-checker lane's **name** and nothing
//! else: the five entry points the twin's record projects are
//! `arena::core_gated`'s `whnf_gated`, `annotate_core_gated`,
//! `infer_type_core_gated`, `is_def_eq_core_gated` and `ensure_sort_core_gated`
//! already, and `orElse` is `arena::checker_base::or_else_attempt`, which does
//! not read the knot at all (it decides on an attempt's outcome).  It is
//! twinned for the reason task #97c gives for twinning `CoreIO.lean` and
//! `CoreGated.lean`: P3 needs the statement subject by name, and it costs
//! a constant.

use crate::arena::core::LANE_GATED;

/// con-leche: ConLeche/Kernel/CheckerGated.lean:27-37 fueledOpsGated
/// Lean twin: `proof/ConRon/Arena/CheckerGated.lean:23-36 fueledOpsGated` — the
/// pure instantiation over the **gated** knot, at an arbitrary fuel.  The
/// twin's record has no Rust counterpart (the module note); this constant is
/// what replaces it, and the fuel is the entry points' own argument.
pub const FUELED_OPS_GATED: u32 = LANE_GATED;

/// con-leche: ConLeche/Kernel/CheckerGated.lean:39-40 pureOpsGated
/// Lean twin: `proof/ConRon/Arena/CheckerGated.lean:38-40 pureOpsGated` — the pure
/// gated instantiation at the standard fuel (`arena::core::CHECK_FUEL`, which
/// every caller passes).
pub const PURE_OPS_GATED: u32 = FUELED_OPS_GATED;
