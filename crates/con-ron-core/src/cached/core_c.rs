//! **The memoized knot** — the six wrappers of `ConLeche/Cached/CoreC.lean`
//! (`memoEI` `:1877-1891`, `memoBI` `:1893-1905`, `coreKnotI` `:1916-1973`).
//!
//! This is the other half of DESIGN.md §3.1's "bodies over wrappers": the
//! *bodies* are `crate::kernel::core_k` (a transliteration of
//! `Kernel/Core.lean`), and these six functions are the knot that ties them —
//! fuel check, memo probe, call the body one fuel level down, memo insert.
//! Together they are one block of plain mutually recursive functions: no
//! record, no trait, no closure (§3.1's ruling, and §3.4).
//!
//! ## What a wrapper is
//!
//! ```text
//! coreKnotI fe 0       →  every slot throws `.internal "fuel exhausted: …"`
//! coreKnotI fe (n + 1) →  memoEI <map> (fun d e => <body>I mode (prev ()) fe d e)
//! ```
//!
//! and `memoEI get' set' f = fun d e => do match (get' (← get))[e]? with |
//! some r => pure r | none => let r ← f d e; modify (… insert e r); pure r`.
//! So `whnf_core(mode, fuel, st, fe, d, e)` is `(coreKnotI fe fuel).whnfCore
//! d e` run at state `st`: `fuel = 0` is the zero arm, and otherwise the
//! probe, the body at `fuel - 1`, and the insert.  The `fuel - 1` is what
//! makes the Rust's `fuel` the same number as the Lean's knot level.
//!
//! Three things to note.
//!
//! 1. **No generic `memoEI`.**  The Lean's getter/setter pair is two
//!    closures, which §3.4 forbids; each wrapper therefore spells its own
//!    `CState` field out, and the probe is a function over a *shared* state
//!    borrow (task #14's rule: never hold a container's borrow across a
//!    branch that touches the container).  `@[inline]` on `memoEI` says the
//!    Lean does the same thing after inlining.
//! 2. **con-leche's linear-update dance is dropped**, as task #14 recorded:
//!    `let mp := get' st; let st := set' st ∅; set' st (mp.insert e r)`
//!    detaches the map so Lean's runtime sees a unique reference;
//!    `st.<map>.insert(…)` on a `&mut CState` *is* that in-place update.
//! 3. **The io slot's dispatch is `CoreC.lean`'s, not `coreKnot`'s.**  The
//!    cached knot selects on `mode.ioGate` (`true` at both modes), the pure
//!    knot on `mode.betaGate`; the port follows the cached one, because these
//!    are the cached wrappers.  At `ioGate` the io body runs under its own
//!    memo (`CState.inferIOC`) — con-leche's task-#170 memo ruling: a hit in
//!    the io memo never serves a full-infer query.
//!
//! **What is not here yet.**  `CoreC.lean` is 2 091 lines; the rest of it —
//! the interned bodies `whnfCoreBodyI`/`whnfBodyI`/`inferBodyI`/
//! `inferBodyIOI`/`defeqBodyI`/`annotateBodyI`, the `whnfCoreLoopI`
//! telescope loops and the `CoreFnsI` record — is task #19's.  Until then the
//! wrappers tie `core_k`'s bodies, which is what makes the crate's knot
//! runnable; swapping in the interned bodies is a change of six call sites.

use crate::cached::state_c::CState;
use crate::kernel::core_k;
use crate::kernel::core_types;
use crate::kernel::core_types::CheckM;
use crate::kernel::env;
use crate::kernel::env::CheckMode;
use crate::kernel::expr;
use crate::kernel::expr::Expr;
use crate::kernel::fenv::FEnv;

/// con-leche: ConLeche/Cached/CoreC.lean:1871-1889 memoEI
/// The `(get' (← get))[e]?` probe of `memoEI` at `CState.whnfCoreC`, over a
/// *shared* state borrow so the map's borrow ends before the miss branch
/// writes.
pub fn whnf_core_probe(st: &CState, e: &Expr) -> Option<Expr> {
    match st.whnf_core_c.get(e) {
        Some(r) => Some(expr::dup(r)),
        None => None,
    }
}

/// con-leche: ConLeche/Cached/CoreC.lean:1871-1889 memoEI
/// The `whnfC` probe (see `whnf_core_probe`).
pub fn whnf_probe(st: &CState, e: &Expr) -> Option<Expr> {
    match st.whnf_c.get(e) {
        Some(r) => Some(expr::dup(r)),
        None => None,
    }
}

/// con-leche: ConLeche/Cached/CoreC.lean:1871-1889 memoEI
/// The `inferC` probe (see `whnf_core_probe`).
pub fn infer_probe(st: &CState, e: &Expr) -> Option<Expr> {
    match st.infer_c.get(e) {
        Some(r) => Some(expr::dup(r)),
        None => None,
    }
}

/// con-leche: ConLeche/Cached/CoreC.lean:1871-1889 memoEI
/// The `inferIOC` probe (see `whnf_core_probe`).
pub fn infer_io_probe(st: &CState, e: &Expr) -> Option<Expr> {
    match st.infer_io_c.get(e) {
        Some(r) => Some(expr::dup(r)),
        None => None,
    }
}

/// con-leche: ConLeche/Cached/CoreC.lean:1871-1889 memoEI
/// The `annotC` probe (see `whnf_core_probe`).
pub fn annot_probe(st: &CState, e: &Expr) -> Option<Expr> {
    match st.annot_c.get(e) {
        Some(r) => Some(expr::dup(r)),
        None => None,
    }
}

/// con-leche: ConLeche/Cached/CoreC.lean:1891-1904 memoBI
/// The `(← get).defeqC[(a, b)]?` probe of `memoBI` (see `whnf_core_probe`).
pub fn defeq_probe(st: &CState, key: &(Expr, Expr)) -> Option<bool> {
    match st.defeq_c.get(key) {
        Some(r) => Some(*r),
        None => None,
    }
}

/// con-leche: ConLeche/Cached/CoreC.lean:1906-1976 coreKnotI
/// con-leche: ConLeche/Kernel/Core.lean:2860-2899 coreKnot
/// con-leche: ConLeche/Cached/CoreC.lean:1871-1889 memoEI
/// `(coreKnotI fe fuel).whnfCore d e`: the fuel-zero throw, the `whnfCoreC`
/// probe, `core_k::whnf_core_body` at `fuel - 1`, and the memo insert.
pub fn whnf_core(
    mode: &CheckMode,
    fuel: u64,
    st: &mut CState,
    fe: &FEnv,
    d: u64,
    e: &Expr,
) -> CheckM<Expr> {
    const M: [u32; 24] = [
        102, 117, 101, 108, 32, 101, 120, 104, 97, 117, 115, 116, 101, 100, 58, 32, 119, 104,
        110, 102, 67, 111, 114, 101,
    ];
    if fuel == 0 {
        Err(core_types::internal(core_types::code_points(&M)))
    } else {
        match whnf_core_probe(st, e) {
            Some(r) => Ok(r),
            None => match core_k::whnf_core_body(mode, fuel - 1, st, fe, d, e) {
                Err(err) => Err(err),
                Ok(r) => {
                    st.whnf_core_c.insert(expr::dup(e), expr::dup(&r));
                    Ok(r)
                }
            },
        }
    }
}

/// con-leche: ConLeche/Cached/CoreC.lean:1906-1976 coreKnotI
/// con-leche: ConLeche/Kernel/Core.lean:2860-2899 coreKnot
/// `(coreKnotI fe fuel).whnf d e`, memoized in `whnfC`.
pub fn whnf(
    mode: &CheckMode,
    fuel: u64,
    st: &mut CState,
    fe: &FEnv,
    d: u64,
    e: &Expr,
) -> CheckM<Expr> {
    const M: [u32; 20] = [
        102, 117, 101, 108, 32, 101, 120, 104, 97, 117, 115, 116, 101, 100, 58, 32, 119, 104,
        110, 102,
    ];
    if fuel == 0 {
        Err(core_types::internal(core_types::code_points(&M)))
    } else {
        match whnf_probe(st, e) {
            Some(r) => Ok(r),
            None => match core_k::whnf_body(mode, fuel - 1, st, fe, d, e) {
                Err(err) => Err(err),
                Ok(r) => {
                    st.whnf_c.insert(expr::dup(e), expr::dup(&r));
                    Ok(r)
                }
            },
        }
    }
}

/// con-leche: ConLeche/Cached/CoreC.lean:1906-1976 coreKnotI
/// con-leche: ConLeche/Kernel/Core.lean:2860-2899 coreKnot
/// `(coreKnotI fe fuel).infer d e`, memoized in `inferC`.
pub fn infer(
    mode: &CheckMode,
    fuel: u64,
    st: &mut CState,
    fe: &FEnv,
    d: u64,
    e: &Expr,
) -> CheckM<Expr> {
    const M: [u32; 21] = [
        102, 117, 101, 108, 32, 101, 120, 104, 97, 117, 115, 116, 101, 100, 58, 32, 105, 110,
        102, 101, 114,
    ];
    if fuel == 0 {
        Err(core_types::internal(core_types::code_points(&M)))
    } else {
        match infer_probe(st, e) {
            Some(r) => Ok(r),
            None => match core_k::infer_body(mode, fuel - 1, st, fe, d, e) {
                Err(err) => Err(err),
                Ok(r) => {
                    st.infer_c.insert(expr::dup(e), expr::dup(&r));
                    Ok(r)
                }
            },
        }
    }
}

/// con-leche: ConLeche/Cached/CoreC.lean:1906-1976 coreKnotI
/// con-leche: ConLeche/Kernel/Core.lean:2860-2899 coreKnot
/// **The io slot**, selected once per knot level: at `mode.ioGate` the io
/// body under its OWN memo (`inferIOC`), tied to the io-grade view of the
/// previous level; at `ioGate = false` the full inference body, verbatim,
/// under `inferC`, because the two grades are the same function there.
/// `CheckMode.ioGate` is `true` at both modes (task #14's port of it), so the
/// second arm is currently dead — and ported anyway, as in the Lean.
pub fn infer_io(
    mode: &CheckMode,
    fuel: u64,
    st: &mut CState,
    fe: &FEnv,
    d: u64,
    e: &Expr,
) -> CheckM<Expr> {
    const M: [u32; 21] = [
        102, 117, 101, 108, 32, 101, 120, 104, 97, 117, 115, 116, 101, 100, 58, 32, 105, 110,
        102, 101, 114,
    ];
    if fuel == 0 {
        Err(core_types::internal(core_types::code_points(&M)))
    } else if env::io_gate(mode) {
        match infer_io_probe(st, e) {
            Some(r) => Ok(r),
            None => match core_k::infer_body_io(mode, fuel - 1, st, fe, d, e) {
                Err(err) => Err(err),
                Ok(r) => {
                    st.infer_io_c.insert(expr::dup(e), expr::dup(&r));
                    Ok(r)
                }
            },
        }
    } else {
        match infer_probe(st, e) {
            Some(r) => Ok(r),
            None => match core_k::infer_body(mode, fuel - 1, st, fe, d, e) {
                Err(err) => Err(err),
                Ok(r) => {
                    st.infer_c.insert(expr::dup(e), expr::dup(&r));
                    Ok(r)
                }
            },
        }
    }
}

/// con-leche: ConLeche/Cached/CoreC.lean:1906-1976 coreKnotI
/// con-leche: ConLeche/Kernel/Core.lean:2860-2899 coreKnot
/// con-leche: ConLeche/Cached/CoreC.lean:1891-1904 memoBI
/// `(coreKnotI fe fuel).defeq d a b`, memoized in `defeqC` under the **pair**
/// key `(a, b)` (`memoBI`).  The key is built before the probe, as the Lean's
/// tuple is, and moved into the map on a miss.
pub fn defeq(
    mode: &CheckMode,
    fuel: u64,
    st: &mut CState,
    fe: &FEnv,
    d: u64,
    a: &Expr,
    b: &Expr,
) -> CheckM<bool> {
    const M: [u32; 21] = [
        102, 117, 101, 108, 32, 101, 120, 104, 97, 117, 115, 116, 101, 100, 58, 32, 100, 101,
        102, 101, 113,
    ];
    if fuel == 0 {
        Err(core_types::internal(core_types::code_points(&M)))
    } else {
        let key = (expr::dup(a), expr::dup(b));
        match defeq_probe(st, &key) {
            Some(r) => Ok(r),
            None => match core_k::defeq_body(mode, fuel - 1, st, fe, d, a, b) {
                Err(err) => Err(err),
                Ok(r) => {
                    st.defeq_c.insert(key, r);
                    Ok(r)
                }
            },
        }
    }
}

/// con-leche: ConLeche/Cached/CoreC.lean:1906-1976 coreKnotI
/// con-leche: ConLeche/Kernel/Core.lean:2860-2899 coreKnot
/// `(coreKnotI fe fuel).annotate d e`, memoized in `annotC`.
pub fn annotate(
    mode: &CheckMode,
    fuel: u64,
    st: &mut CState,
    fe: &FEnv,
    d: u64,
    e: &Expr,
) -> CheckM<Expr> {
    const M: [u32; 24] = [
        102, 117, 101, 108, 32, 101, 120, 104, 97, 117, 115, 116, 101, 100, 58, 32, 97, 110,
        110, 111, 116, 97, 116, 101,
    ];
    if fuel == 0 {
        Err(core_types::internal(core_types::code_points(&M)))
    } else {
        match annot_probe(st, e) {
            Some(r) => Ok(r),
            None => match core_k::annotate_body(mode, fuel - 1, st, fe, d, e) {
                Err(err) => Err(err),
                Ok(r) => {
                    st.annot_c.insert(expr::dup(e), expr::dup(&r));
                    Ok(r)
                }
            },
        }
    }
}
