//! `arena::prop_read` — the head-symbol prop-ness readers over handles.
//!
//! The Rust twin of `proof/ConRon/Arena/PropRead.lean`, which is
//! `ConLeche/Kernel/PropRead.lean` (con-leche's task #168) clause for clause
//! over handles: two pure readers that answer "is this type a proposition?" /
//! "is this term a proof?" off the head symbol, the arity and the residual
//! sorts of stored types — no inference, no reduction.  `core::prop_irrel`'s
//! two fast arms are their only callers.
//!
//! **Task #119 (con-leche's task #342 S0/L18).**  With the binder datum gone
//! from `Expr`, the readers no longer read a ∀'s or a λ's annotation: a ∀
//! telescope is peeled down to its residual head (`typeSortPWGo`, which also
//! reads a telescope-bvar head's binder domain, `binderDom`), a λ, a `let` and
//! an application answer from their body or function (`proofPW`), a
//! projection answers "not a proof" from its field's stored type, and the
//! peels look through identity-like wrapper definitions (`outParam`, …:
//! `lamProj?`, `unwrapIdDefs`, `peelPisW`).
//!
//! **The three deviations are the twin's, and they are systematic.**
//!
//! 1. **The lookup is not abstracted.**  con-leche writes `(find? : Name →
//!    Option ConstantInfo)`; the arena has ONE environment type — `IFEnv`, the
//!    index (DESIGN.md §8.3, lesson 13) — so the twin takes `fe : IFEnv` and
//!    calls `fe.find?`.  Passing `fe.find?` would be a closure (§3.4).
//! 2. **The readers are monadic**: every structural match on a term is a
//!    `view`, so a pure `Expr → Option PropWhen` is an `EIdx → AM (Option
//!    PropWhen)` and a walk down a term takes an explicit `fuel`.
//! 3. **Levels are read back, not twinned** (DESIGN.md §8.3, lesson 4).
//!    `level::subst_pw` and `level::zeroness_of` are con-ron-core's own, run
//!    on transient `Level` trees and `Name`s.  `PropWhen` itself is
//!    con-ron-core's, so `PropWhen.isProp` is `kernel::prop_read::is_prop`.

use crate::arena::env;
use crate::arena::env::{IConstantInfo, IFEnv};
use crate::arena::expr_ops::{get_app_args, get_app_fn};
use crate::arena::handle::{EIdx, ETAG_APP, ETAG_BVAR, ETAG_CONST, ETAG_FORALL_E, ETAG_LAM, ETAG_LET_E, ETAG_SORT};
use crate::arena::monad::read_level;
use crate::arena::monad::{view_const_name, view_let};
use crate::arena::monad::{
    fail, fail_dangling_e, fail_dangling_ls, read_levels_m, read_names_m, view, view_app,
    view_bind, view_bvar, view_ls_len, view_sort, AState,
};
use crate::arena::store::ENodeView;
use crate::arena::store::PersTier;
use crate::kernel::core_types::{code_points, CheckError};
use crate::kernel::level;
use crate::kernel::prop_read;
use crate::kernel::prop_when;
use crate::kernel::prop_when::PropWhen;
use crate::ron::hashmap::Dup;
use crate::arena::handle::NIdx;
use crate::arena::handle::LsIdx;

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `"fuel exhausted: numArgs"`, as code points.
const M_FUEL_NUM_ARGS: [u32; 23] = [
    102, 117, 101, 108, 32, 101, 120, 104, 97, 117, 115, 116, 101, 100, 58, 32, 110, 117, 109,
    65, 114, 103, 115,
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `"fuel exhausted: propRead"`, as code points: the fuel of the readers'
/// walks down a term (`lamProj?`, `typeSortPWGo`, `proofPW`), which con-leche
/// writes as structural recursions.
const M_FUEL_PROP_READ: [u32; 24] = [
    102, 117, 101, 108, 32, 101, 120, 104, 97, 117, 115, 116, 101, 100, 58, 32, 112, 114, 111,
    112, 82, 101, 97, 100,
];

/// con-leche: none — the depth bound `4` of `peelPisW`'s two `unwrapIdDefs` calls
const UNWRAP_FUEL: u64 = 4;

/// con-leche: ConLeche/Kernel/PropRead.lean:40-46 Expr.peelPis
/// Lean twin: `proof/ConRon/Arena/PropRead.lean:45-57 peelPis` — the residual
/// after peeling `k` *syntactic* ∀ binders, whatever their domains (no
/// substitution).  Structural on `k`, so no fuel.
pub fn peel_pis(pers: &PersTier, st: &AState, k: u64, h: &EIdx) -> Result<Option<EIdx>, CheckError> {
    if k == 0 {
        Ok(Some(h.dup2()))
    } else if h.tag() == ETAG_FORALL_E {
        match view_bind(pers, st, h) {
            None => fail_dangling_e(),
            Some((_, b)) => peel_pis(pers, st, k - 1, &b),
        }
    } else {
        Ok(None)
    }
}

/// con-leche: ConLeche/Kernel/PropRead.lean:48-53 Expr.binderDom
/// Lean twin: `proof/ConRon/Arena/PropRead.lean:59-74 binderDom` — the domain
/// of the `k`-th syntactic ∀ binder (`0` = outermost) of a telescope,
/// unsubstituted.  Structural on `k`.
pub fn binder_dom(pers: &PersTier, st: &AState, k: u64, h: &EIdx) -> Result<Option<EIdx>, CheckError> {
    if h.tag() == ETAG_FORALL_E {
        match view_bind(pers, st, h) {
            None => fail_dangling_e(),
            Some((a, b)) => {
                if k == 0 {
                    Ok(Some(a))
                } else {
                    binder_dom(pers, st, k - 1, &b)
                }
            }
        }
    } else {
        Ok(None)
    }
}

/// con-leche: ConLeche/Kernel/PropRead.lean:55-58 Expr.numArgs
/// Lean twin: `proof/ConRon/Arena/PropRead.lean:76-89 numArgs` — the number of
/// arguments of an application spine.  A spine walk, hence fuel.
pub fn num_args(pers: &PersTier, st: &AState, fuel: u64, h: &EIdx) -> Result<u64, CheckError> {
    if fuel == 0 {
        fail(CheckError::Internal(code_points(&M_FUEL_NUM_ARGS)))
    } else if h.tag() == ETAG_APP {
        match view_app(pers, st, h) {
            None => fail_dangling_e(),
            Some((f, _)) => match num_args(pers, st, fuel - 1, &f) {
                Err(e) => Err(e),
                Ok(n) => Ok(n + 1),
            },
        }
    } else {
        Ok(0)
    }
}

/// con-leche: ConLeche/Kernel/PropRead.lean:62-68 residualPW
/// Lean twin: `proof/ConRon/Arena/PropRead.lean:91-105 residualPW` — the
/// zero-ness datum of the sort of a *residual type*.  The level is read back
/// and `level::zeroness_of` is con-leche's own (deviation 3).
pub fn residual_pw(pers: &PersTier, st: &AState, h: Option<EIdx>) -> Result<Option<PropWhen>, CheckError> {
    match h {
        Some(r) => {
            if r.tag() == ETAG_SORT {
                match view_sort(pers, st, &r) {
                    None => fail_dangling_e(),
                    Some(u) => match read_level(pers, st, &u) {
                        Err(e) => Err(e),
                        Ok(l) => Ok(Some(level::zeroness_of(&l))),
                    },
                }
            } else {
                Ok(None)
            }
        }
        None => Ok(None),
    }
}

/// con-leche: ConLeche/Kernel/PropRead.lean:70-76 lamProj?
/// Lean twin: `proof/ConRon/Arena/PropRead.lean:109-123 lamProj?` — the body
/// of a λ-telescope that is a single bound variable: `some (k, j)` for
/// `fun x₁ … x_k => x_{k-j}` (the shape of `outParam`, `semiOutParam`,
/// `optParam`, `autoParam`).  A walk down the λ chain, hence fuel.
pub fn lam_proj(pers: &PersTier, st: &AState, fuel: u64, k: u64, h: &EIdx) -> Result<Option<(u64, u64)>, CheckError> {
    if fuel == 0 {
        fail(CheckError::Internal(code_points(&M_FUEL_PROP_READ)))
    } else if h.tag() == ETAG_LAM {
        match view_bind(pers, st, h) {
            None => fail_dangling_e(),
            Some((_, b)) => lam_proj(pers, st, fuel - 1, k + 1, &b),
        }
    } else if h.tag() == ETAG_BVAR {
        match view_bvar(pers, st, h) {
            None => fail_dangling_e(),
            Some(j) => {
                if j < k {
                    Ok(Some((k, j)))
                } else {
                    Ok(None)
                }
            }
        }
    } else {
        Ok(None)
    }
}

/// con-leche: ConLeche/Kernel/PropRead.lean:78-96 unwrapIdDefs
/// Lean twin: `proof/ConRon/Arena/PropRead.lean:125-148 unwrapIdDefs` — unfold
/// an identity-like wrapper (a definition whose value is `fun x₁ … x_k =>
/// x_i`, e.g. `outParam`) at the head of a residual type, `n` times at most;
/// definitional (δ then β).
pub fn unwrap_id_defs(
    pers: &PersTier,
    vis: u64,
    st: &mut AState,
    fe: &IFEnv,
    fuel: u64,
    n: u64,
    e: &EIdx,
) -> Result<EIdx, CheckError> {
    if n == 0 {
        Ok(e.dup2())
    } else {
        match get_app_fn(pers, st, fuel, e) {
            Err(er) => Err(er),
            Ok(hd) => if hd.tag() == ETAG_CONST {
                match view_const_name(pers, st, &hd) {
                None => fail_dangling_e(),
                Some(c) => match env::ifenv_find(vis, fe, &c) {
                    Some(IConstantInfo::DefnInfo(_, v0, _)) => {
                        let v: EIdx = v0.dup2();
                        match lam_proj(pers, st, fuel, 0, &v) {
                            Err(er) => Err(er),
                            Ok(Some((k, j))) => match get_app_args(pers, st, fuel, e) {
                                Err(er) => Err(er),
                                Ok(args) => {
                                    if k <= args.len() as u64 && args.len() as u64 == k {
                                        // `args.getD (k - 1 - j) e`: `j < k`
                                        // by `lamProj?`, so the index is in
                                        // range and the default unread.
                                        let a: EIdx = args[(k - 1 - j) as usize].dup2();
                                        unwrap_id_defs(pers, vis, st, fe, fuel, n - 1, &a)
                                    } else {
                                        Ok(e.dup2())
                                    }
                                }
                            },
                            Ok(None) => Ok(e.dup2()),
                        }
                    }
                    Some(_) => Ok(e.dup2()),
                    None => Ok(e.dup2()),
                },
                }
            } else {
                Ok(e.dup2())
            },
        }
    }
}

/// con-leche: ConLeche/Kernel/PropRead.lean:98-105 peelPisW
/// Lean twin: `proof/ConRon/Arena/PropRead.lean:150-168 peelPisW` —
/// `peel_pis` through identity-like wrappers (`outParam (α → Sort u)`).
/// Structural on `k`.
pub fn peel_pis_w(
    pers: &PersTier,
    vis: u64,
    st: &mut AState,
    fe: &IFEnv,
    fuel: u64,
    k: u64,
    h: &EIdx,
) -> Result<Option<EIdx>, CheckError> {
    if k == 0 {
        match unwrap_id_defs(pers, vis, st, fe, fuel, UNWRAP_FUEL, h) {
            Err(e) => Err(e),
            Ok(r) => Ok(Some(r)),
        }
    } else if h.tag() == ETAG_FORALL_E {
        match view_bind(pers, st, h) {
            None => fail_dangling_e(),
            Some((_, b)) => peel_pis_w(pers, vis, st, fe, fuel, k - 1, &b),
        }
    } else {
        match unwrap_id_defs(pers, vis, st, fe, fuel, UNWRAP_FUEL, h) {
            Err(e) => Err(e),
            Ok(u) => {
                if u.tag() == ETAG_FORALL_E {
                    match view_bind(pers, st, &u) {
                        None => fail_dangling_e(),
                        Some((_, b)) => peel_pis_w(pers, vis, st, fe, fuel, k - 1, &b),
                    }
                } else {
                    Ok(None)
                }
            }
        }
    }
}

/// con-leche: none — `Level.substPW ks vs pw` at a stored constant's level parameters
/// Lean twin: `proof/ConRon/Arena/PropRead.lean:172-184 substPWAt` — the
/// datum level-instantiated at a use's universe arguments, with **the cutoff
/// hoisted over the readback** (task #97-P6-10): a datum that names no
/// parameter (`never`, or `ifAllZero []`) is its own substitution (`bindZ`
/// is the identity there), so both readbacks would be computed and dropped.
/// The constant arm both head readers share.
pub fn subst_pw_at(
    pers: &PersTier,
    st: &mut AState,
    lps: &Vec<NIdx>,
    us: &LsIdx,
    pw: PropWhen,
) -> Result<Option<PropWhen>, CheckError> {
    match pw {
        PropWhen::IfAllZero(ps) => {
            if ps.len() == 0 {
                Ok(Some(PropWhen::IfAllZero(ps)))
            } else {
                match read_names_m(pers, st, lps) {
                    Err(e) => Err(e),
                    Ok(ks) => match read_levels_m(pers, st, us) {
                        Err(e) => Err(e),
                        Ok(vs) => Ok(Some(level::subst_pw(&ks, &vs, &PropWhen::IfAllZero(ps)))),
                    },
                }
            }
        }
        PropWhen::Never => Ok(Some(PropWhen::Never)),
    }
}

/// con-leche: ConLeche/Kernel/PropRead.lean:107-130 headTypePW
/// con-leche: CHANGED since ae1f3198 — re-port, re-test, re-prove prop_read::head_type_pw_refines, then delete this line
/// Lean twin: `proof/ConRon/Arena/PropRead.lean:186-220 headTypePW` — the datum
/// of a type-former application's *head* at `n` arguments: a constant head
/// reads its stored type (level-instantiated), an fvar head its declared type,
/// a `bvar` head (inside the ∀ telescope `root`, `d` binders deep) its
/// binder's domain; the residual after `n` syntactic binders (through
/// identity wrappers) is read by `residual_pw`.
pub fn head_type_pw(
    pers: &PersTier,
    vis: u64,
    st: &mut AState,
    fe: &IFEnv,
    fuel: u64,
    root: &EIdx,
    d: u64,
    h: &EIdx,
    n: u64,
) -> Result<Option<PropWhen>, CheckError> {
    match view(pers, st, h) {
        Err(e) => Err(e),
        Ok(ENodeView::Const(i, us)) => match env::ifenv_find(vis, fe, &i) {
            Some(ci) => {
                if env::i_constant_info_is_tower_entry(ci) {
                    Ok(None)
                } else {
                    match env::i_constant_info_to_constant_val(pers, &mut st.store, ci) {
                        Err(e) => Err(e),
                        Ok(cv) => match view_ls_len(pers, st, &us) {
                            None => fail_dangling_ls(),
                            Some(usl) => {
                                if usl == cv.level_params.len() {
                                    match peel_pis_w(pers, vis, st, fe, fuel, n, &cv.ty) {
                                        Err(e) => Err(e),
                                        Ok(res) => match residual_pw(pers, st, res) {
                                            Err(e) => Err(e),
                                            Ok(Some(pw)) => subst_pw_at(pers, st, &cv.level_params, &us, pw),
                                            Ok(None) => Ok(None),
                                        },
                                    }
                                } else {
                                    Ok(None)
                                }
                            }
                        },
                    }
                }
            }
            None => Ok(None),
        },
        Ok(ENodeView::FVar(_, ty)) => match peel_pis_w(pers, vis, st, fe, fuel, n, &ty) {
            Err(e) => Err(e),
            Ok(res) => residual_pw(pers, st, res),
        },
        Ok(ENodeView::BVar(i)) => {
            if i < d {
                match binder_dom(pers, st, d - 1 - i, root) {
                    Err(e) => Err(e),
                    Ok(Some(dom)) => match peel_pis_w(pers, vis, st, fe, fuel, n, &dom) {
                        Err(e) => Err(e),
                        Ok(res) => residual_pw(pers, st, res),
                    },
                    Ok(None) => Ok(None),
                }
            } else {
                Ok(None)
            }
        }
        Ok(_) => Ok(None),
    }
}

/// con-leche: ConLeche/Kernel/PropRead.lean:132-139 typeSortPWGo
/// Lean twin: `proof/ConRon/Arena/PropRead.lean:222-238 typeSortPWGo` — the
/// walk of `typeSortPW`: peel the ∀ telescope (a ∀'s prop-ness is its
/// codomain's: `zeronessOf (imax u v) = zeronessOf v`), counting the binders,
/// then read the residual's head.
pub fn type_sort_pw_go(
    pers: &PersTier,
    vis: u64,
    st: &mut AState,
    fe: &IFEnv,
    fuel: u64,
    root: &EIdx,
    t: &EIdx,
    d: u64,
) -> Result<Option<PropWhen>, CheckError> {
    if fuel == 0 {
        fail(CheckError::Internal(code_points(&M_FUEL_PROP_READ)))
    } else {
        // tag first, then the binder projection, as the twin (task #97-P5-Core
        // round 6, D1); the inner walks run at the decremented fuel
        if t.tag() == ETAG_FORALL_E {
            match view_bind(pers, st, t) {
                None => fail_dangling_e(),
                Some((_, b)) => type_sort_pw_go(pers, vis, st, fe, fuel - 1, root, &b, d + 1),
            }
        } else if t.tag() == ETAG_SORT {
            Ok(Some(prop_when::never()))
        } else {
            match get_app_fn(pers, st, fuel - 1, t) {
                Err(e) => Err(e),
                Ok(fnh) => match num_args(pers, st, fuel - 1, t) {
                    Err(e) => Err(e),
                    Ok(n) => head_type_pw(pers, vis, st, fe, fuel - 1, root, d, &fnh, n),
                },
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/PropRead.lean:141-149 typeSortPW
/// Lean twin: `proof/ConRon/Arena/PropRead.lean:240-243 typeSortPW` — the
/// zero-ness datum of the sort of the *type* `t` ("is `t` a proposition?"),
/// read off `t`'s shape.  `none` = unknown.
pub fn type_sort_pw(
    pers: &PersTier,
    vis: u64,
    st: &mut AState,
    fe: &IFEnv,
    fuel: u64,
    t: &EIdx,
) -> Result<Option<PropWhen>, CheckError> {
    type_sort_pw_go(pers, vis, st, fe, fuel, t, t, 0)
}

/// con-leche: ConLeche/Kernel/PropRead.lean:151-181 headProofPW
/// con-leche: CHANGED since ae1f3198 — re-port, re-test, re-prove prop_read::head_proof_pw_refines, then delete this line
/// Lean twin: `proof/ConRon/Arena/PropRead.lean:245-277 headProofPW` — the
/// datum of a term's *head* (any arity): a constant head answers from its
/// stored type (prop-ness is invariant under application), an fvar head from
/// its declared type; sorts, ∀s and literals are never proofs; a projection
/// answers from its field's stored type, "not a proof" only.
pub fn head_proof_pw(
    pers: &PersTier,
    vis: u64,
    st: &mut AState,
    fe: &IFEnv,
    fuel: u64,
    h: &EIdx,
) -> Result<Option<PropWhen>, CheckError> {
    match view(pers, st, h) {
        Err(e) => Err(e),
        Ok(ENodeView::Const(c, us)) => match env::ifenv_find(vis, fe, &c) {
            Some(ci) => {
                if env::i_constant_info_is_tower_entry(ci) {
                    Ok(None)
                } else {
                    match env::i_constant_info_to_constant_val(pers, &mut st.store, ci) {
                        Err(e) => Err(e),
                        Ok(cv) => match view_ls_len(pers, st, &us) {
                            None => fail_dangling_ls(),
                            Some(usl) => {
                                if usl == cv.level_params.len() {
                                    match type_sort_pw(pers, vis, st, fe, fuel, &cv.ty) {
                                        Err(e) => Err(e),
                                        Ok(Some(pw)) => subst_pw_at(pers, st, &cv.level_params, &us, pw),
                                        Ok(None) => Ok(None),
                                    }
                                } else {
                                    Ok(None)
                                }
                            }
                        },
                    }
                }
            }
            None => Ok(None),
        },
        Ok(ENodeView::FVar(_, ty)) => type_sort_pw(pers, vis, st, fe, fuel, &ty),
        Ok(ENodeView::Sort(_)) => Ok(Some(prop_when::never())),
        Ok(ENodeView::ForallE(_, _)) => Ok(Some(prop_when::never())),
        Ok(ENodeView::Lit(_)) => Ok(Some(prop_when::never())),
        Ok(ENodeView::Proj(s, i, _)) => match env::ifenv_find_proj(pers, vis, &mut st.store, fe, &s, i) {
            Err(e) => Err(e),
            Ok(Some(entry)) => match type_sort_pw(pers, vis, st, fe, fuel, &entry.body) {
                Err(e) => Err(e),
                Ok(Some(pw)) => {
                    if prop_when::is_never(&pw) {
                        Ok(Some(pw))
                    } else {
                        Ok(None)
                    }
                }
                Ok(None) => Ok(None),
            },
            Ok(None) => Ok(None),
        },
        Ok(_) => Ok(None),
    }
}

/// con-leche: ConLeche/Kernel/PropRead.lean:183-195 proofPW
/// con-leche: CHANGED since ae1f3198 — re-port, re-test, re-prove prop_read::proof_pw_refines, then delete this line
/// Lean twin: `proof/ConRon/Arena/PropRead.lean:279-300 proofPW` — the
/// zero-ness datum of the sort of the *type* of `a` ("is `a` a proof?"), read
/// off `a`'s head symbol at any arity: a λ and a `let` answer from their body,
/// an application from its function, anything else from its head.
pub fn proof_pw(
    pers: &PersTier,
    vis: u64,
    st: &mut AState,
    fe: &IFEnv,
    fuel: u64,
    a: &EIdx,
) -> Result<Option<PropWhen>, CheckError> {
    if fuel == 0 {
        fail(CheckError::Internal(code_points(&M_FUEL_PROP_READ)))
    } else {
        // tag first, then the projection, as the twin (task #97-P5-Core
        // round 6, D1)
        if a.tag() == ETAG_LAM {
            match view_bind(pers, st, a) {
                None => fail_dangling_e(),
                Some((_, b)) => proof_pw(pers, vis, st, fe, fuel - 1, &b),
            }
        } else if a.tag() == ETAG_LET_E {
            match view_let(pers, st, a) {
                None => fail_dangling_e(),
                Some((_, _, b)) => proof_pw(pers, vis, st, fe, fuel - 1, &b),
            }
        } else if a.tag() == ETAG_APP {
            match view_app(pers, st, a) {
                None => fail_dangling_e(),
                Some((f, _)) => proof_pw(pers, vis, st, fe, fuel - 1, &f),
            }
        } else {
            head_proof_pw(pers, vis, st, fe, fuel - 1, a)
        }
    }
}

/// con-leche: ConLeche/Kernel/PropRead.lean:203-209 notProofFast
/// con-leche: CHANGED since ae1f3198 — re-port, re-test, re-prove prop_read::not_proof_fast_refines, then delete this line
/// Lean twin: `proof/ConRon/Arena/PropRead.lean:304-310 notProofFast` —
/// **definitely not a proof**: the datum is known and is not always-zero.
/// Refusing the proof-irrelevance shortcut is always sound.
pub fn not_proof_fast(
    pers: &PersTier,
    vis: u64,
    st: &mut AState,
    fe: &IFEnv,
    fuel: u64,
    a: &EIdx,
) -> Result<bool, CheckError> {
    match proof_pw(pers, vis, st, fe, fuel, a) {
        Err(e) => Err(e),
        Ok(Some(pw)) => {
            if prop_read::is_prop(&pw) {
                Ok(false)
            } else {
                Ok(true)
            }
        }
        Ok(None) => Ok(false),
    }
}

/// con-leche: ConLeche/Kernel/PropRead.lean:211-217 isProofFast
/// con-leche: CHANGED since ae1f3198 — re-port, re-test, re-prove prop_read::is_proof_fast_refines, then delete this line
/// Lean twin: `proof/ConRon/Arena/PropRead.lean:312-318 isProofFast` —
/// **definitely a proof**: the datum is known and always-zero (justified by
/// the squash regime, con-leche's `prf_of_isProofFast`).
pub fn is_proof_fast(
    pers: &PersTier,
    vis: u64,
    st: &mut AState,
    fe: &IFEnv,
    fuel: u64,
    a: &EIdx,
) -> Result<bool, CheckError> {
    match proof_pw(pers, vis, st, fe, fuel, a) {
        Err(e) => Err(e),
        Ok(Some(pw)) => Ok(prop_read::is_prop(&pw)),
        Ok(None) => Ok(false),
    }
}
