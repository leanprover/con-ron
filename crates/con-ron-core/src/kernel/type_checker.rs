//! `ConLeche/Kernel/TypeChecker.lean` — **the checker's front door**: the six
//! core entry points and `ensureSort`, under the names the declaration
//! checker calls them by.
//!
//! In con-leche this file ties `Kernel/Core.lean`'s bodies with the *pure*
//! knot (`coreKnot`, no memoization) and is the **specification** the
//! semantic verification reasons about; the binary executes the cached knot
//! (`Cached/CoreC.lean`).  DESIGN.md §3.1 gives the port **one** knot — the
//! cached one, `crate::cached::core_c`, because that is what the executed
//! program is — so these seven entry points are the cached wrappers under
//! con-leche's pure-lane names, and they are simultaneously the five slots of
//! `CheckerOps`' two instantiations (`fueledOps`, `sharedOpsC`).
//!
//! ## The three deviations, recorded once
//!
//! 1. **The knot is the cached one.**  `pureFns mode env fuel` has no Rust
//!    spelling: §3.1's "bodies over wrappers" says the bodies
//!    (`kernel::core_k`) are tied by the memoizing wrappers
//!    (`cached::core_c`) and by nothing else.  A refinement lemma about one
//!    of these entry points is therefore stated against `coreKnotI`, not
//!    `coreKnot`, exactly as §3.5 writes it.
//! 2. **The fuel is `checkFuel`, not a parameter.**  Every cited entry point
//!    takes `fuel : Nat`, and `CheckerOps`' two instantiations instantiate
//!    it: `pureOps = fueledOps checkFuel`, and `sharedOpsC` — the one the
//!    executable uses — builds `coreKnotI mode fe checkFuel` at every call.
//!    The port follows the executed path and spells `core_k::check_fuel()`
//!    here, in the one place, rather than at two hundred call sites.
//!    `fueledOps` at an arbitrary `F` is then the same functions with a
//!    different constant, and is cited here.
//! 3. **The environment is the index** (task #18's deviation 3): the cited
//!    `env : Env` parameter is `fe: &FEnv`, and `sharedOpsC` ignores its own
//!    `Env` argument for exactly that reason (`annotate _ d e := …`).
//!
//! **`sharedOpsC`'s three entry points are these functions** (task #33).
//! `Cached/CheckerC.lean`'s `opE` (`:68-71`), `opB` (`:73-75`) and `opS`
//! (`:77-79`) are the bodies the executable's `CheckerOps` instance is built
//! from — `opE mode fe pick d e = pick (coreKnotI mode fe checkFuel) d e`,
//! and `opB`/`opS` the same at `.defeq` and at `ensureSortI`.  `opE` is
//! higher-order in `pick` (§3.4 forbids the closure), so the port has it
//! four times over, once per pick: `whnf_core`, `whnf`, `infer_type_core` and
//! `annotate_core` each cite it, `is_def_eq_core` cites `opB` and
//! `ensure_sort_core` cites `opS`.  That is the whole of `opE`/`opB`/`opS`;
//! nothing of them is left over.
//!
//! **`CheckerOps` itself is cited, not ported.**  It is a higher-order record
//! of the knot's operations; §3.1's knot rule forbids a trait in the
//! recursion and §3.4 forbids closures, so a function that the Lean writes
//! against `ops : CheckerOps m` drops the parameter and calls these names.
//! The record's one non-core field, `orElse`, is the only place the checker
//! recovers from an error and is ported separately in
//! `crate::cached::checker_c`.

use crate::cached::core_c;
use crate::cached::state_c::CState;
use crate::kernel::core_k;
use crate::kernel::core_types::CheckM;
use crate::kernel::env::CheckMode;
use crate::kernel::expr::Expr;
use crate::kernel::fenv::FEnv;
use crate::kernel::level::Level;

/// con-leche: ConLeche/Kernel/TypeChecker.lean:27-29 whnfCore
/// con-leche: ConLeche/Kernel/CheckerBase.lean:57-66 fueledOps
/// con-leche: ConLeche/Kernel/CheckerBase.lean:68-69 pureOps
/// con-leche: ConLeche/Cached/CheckerC.lean:68-71 opE
/// con-leche: ConLeche/Cached/CheckerC.lean:81-96 sharedOpsC
/// Head normalization without delta, at `checkFuel` (`CheckerOps.whnf`'s
/// sibling; the record's `whnf` slot is `whnf` below).
pub fn whnf_core(
    mode: &CheckMode,
    st: &mut CState,
    fe: &FEnv,
    depth: u64,
    e: &Expr,
) -> CheckM<Expr> {
    core_c::whnf_core(mode, core_k::check_fuel(), st, fe, depth, e)
}

/// con-leche: ConLeche/Kernel/TypeChecker.lean:31-33 whnf
/// con-leche: ConLeche/Kernel/CheckerBase.lean:25-53 CheckerOps
/// con-leche: ConLeche/Cached/CheckerC.lean:68-71 opE
/// The full reduction loop, at `checkFuel` — `CheckerOps.whnf`.
pub fn whnf(mode: &CheckMode, st: &mut CState, fe: &FEnv, depth: u64, e: &Expr) -> CheckM<Expr> {
    core_c::whnf(mode, core_k::check_fuel(), st, fe, depth, e)
}

/// con-leche: ConLeche/Kernel/TypeChecker.lean:35-38 inferTypeCore
/// con-leche: ConLeche/Kernel/CheckerBase.lean:25-53 CheckerOps
/// con-leche: ConLeche/Cached/CheckerC.lean:68-71 opE
/// Full-grade type inference at `checkFuel`: the declaration front door's
/// entry — official's `infer_type_core(e, infer_only = false)`, and
/// `CheckerOps.inferType`.
pub fn infer_type_core(
    mode: &CheckMode,
    st: &mut CState,
    fe: &FEnv,
    depth: u64,
    e: &Expr,
) -> CheckM<Expr> {
    core_c::infer(mode, core_k::check_fuel(), st, fe, depth, e)
}

/// con-leche: ConLeche/Kernel/TypeChecker.lean:40-46 inferTypeIO
/// Type inference at the io grade — the knot's `inferIO` slot, what every
/// *internal* inference call site runs.  No declaration-level function calls
/// it (`CheckerOps` has no io slot); ported so the family stays whole.
pub fn infer_type_io(
    mode: &CheckMode,
    st: &mut CState,
    fe: &FEnv,
    depth: u64,
    e: &Expr,
) -> CheckM<Expr> {
    core_c::infer_io(mode, core_k::check_fuel(), st, fe, depth, e)
}

/// con-leche: ConLeche/Kernel/TypeChecker.lean:48-50 isDefEqCore
/// con-leche: ConLeche/Kernel/CheckerBase.lean:25-53 CheckerOps
/// con-leche: ConLeche/Cached/CheckerC.lean:73-75 opB
/// Definitional equality at `checkFuel` — `CheckerOps.isDefEq`.
pub fn is_def_eq_core(
    mode: &CheckMode,
    st: &mut CState,
    fe: &FEnv,
    depth: u64,
    a: &Expr,
    b: &Expr,
) -> CheckM<bool> {
    core_c::defeq(mode, core_k::check_fuel(), st, fe, depth, a, b)
}

/// con-leche: ConLeche/Kernel/TypeChecker.lean:52-54 annotateCore
/// con-leche: ConLeche/Kernel/CheckerBase.lean:25-53 CheckerOps
/// con-leche: ConLeche/Cached/CheckerC.lean:68-71 opE
/// The annotation pass at `checkFuel` — `CheckerOps.annotate`.
pub fn annotate_core(
    mode: &CheckMode,
    st: &mut CState,
    fe: &FEnv,
    depth: u64,
    e: &Expr,
) -> CheckM<Expr> {
    core_c::annotate(mode, core_k::check_fuel(), st, fe, depth, e)
}

/// con-leche: ConLeche/Kernel/TypeChecker.lean:56-58 ensureSortCore
/// con-leche: ConLeche/Kernel/CheckerBase.lean:25-53 CheckerOps
/// con-leche: ConLeche/Cached/CheckerC.lean:77-79 opS
/// `ensureSort` over the knot at `checkFuel` — `CheckerOps.ensureSort`, and
/// `ensureSortI`'s executed spelling (`core_c::ensure_sort_i`, task #23).
pub fn ensure_sort_core(
    mode: &CheckMode,
    st: &mut CState,
    fe: &FEnv,
    depth: u64,
    e: &Expr,
) -> CheckM<Level> {
    core_c::ensure_sort_i(mode, core_k::check_fuel(), st, fe, depth, e)
}
