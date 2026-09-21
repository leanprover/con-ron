//! `arena::prop_read` — the head-symbol prop-ness readers over handles.
//!
//! The Rust twin of `proof/ConRon/Arena/PropRead.lean`, which is
//! `ConLeche/Kernel/PropRead.lean` (con-leche's task #168) clause for clause
//! over handles: two pure readers that answer "is this type a proposition?" /
//! "is this term a proof?" off the head symbol, the arity and the validated
//! `pw` annotations — no inference, no reduction.  `core::prop_irrel`'s two
//! fast arms and the annotation pass's two datum computations are their only
//! callers, and all four are on the hot path, so the readers exist to keep
//! inference out of them.
//!
//! **The three deviations are the twin's, and they are systematic.**
//!
//! 1. **The lookup is not abstracted.**  con-leche writes `(find? : Name →
//!    Option ConstantInfo)` so that the plain environment and the indexed one
//!    share the body; the arena has ONE environment type — `IFEnv`, the index
//!    (DESIGN.md §8.3, lesson 13) — so the twin takes `fe : IFEnv` and calls
//!    `fe.find?`.  Passing `fe.find?` would be a closure, which DESIGN.md
//!    §3.4 forbids.
//! 2. **The readers are monadic**: every structural match on a term is a
//!    `view`, so a pure `Expr → Option PropWhen` is an `EIdx → AM (Option
//!    PropWhen)` and a spine walk takes an explicit `fuel`.
//! 3. **Levels are read back, not twinned** (DESIGN.md §8.3, lesson 4).
//!    `level::subst_pw` and `level::zeroness_of` are con-ron-core's own, run
//!    on transient `Level` trees and `Name`s that `read_levels` / `read_names`
//!    hand over.  `PropWhen` itself is con-ron-core's, so `PropWhen.isProp`
//!    needs no twin at all — it is `con_ron_core::kernel::prop_read::is_prop`.
//!
//! The Rust of the twin's `AM` is `arena::monad`'s: `&mut AState` first plus
//! `Result`.  `peel_never_pis` and `residual_pw` can fail only through
//! `view`, so they are `Result` like everything else.

use crate::arena::env;
use crate::arena::env::IFEnv;
use crate::arena::handle::{EIdx, ETAG_APP, ETAG_FORALL_E, ETAG_LAM, ETAG_SORT};
use crate::arena::expr_ops::get_app_fn;
use crate::arena::monad::{
    fail, fail_dangling_ls, read_levels, read_names, view, view_ls_len, AState, fail_dangling_e, view_app, view_bind, view_sort};
use crate::arena::monad::read_level;
use crate::arena::store::ENodeView;
use con_ron_core::kernel::core_types::{code_points, CheckError};
use con_ron_core::kernel::level;
use con_ron_core::kernel::prop_read;
use con_ron_core::kernel::prop_when;
use con_ron_core::kernel::prop_when::PropWhen;
use con_ron_core::ron::hashmap::Dup;
use crate::arena::store::PersTier;

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `"fuel exhausted: numArgs"`, as code points.
const M_FUEL_NUM_ARGS: [u32; 23] = [
    102, 117, 101, 108, 32, 101, 120, 104, 97, 117, 115, 116, 101, 100, 58, 32, 110, 117, 109,
    65, 114, 103, 115,
];

/// con-leche: ConLeche/Kernel/PropRead.lean:44-56 Expr.peelNeverPis
/// Lean twin: `proof/ConRon/Arena/PropRead.lean:45-50 peelNeverPis` — the
/// residual after peeling `k` *syntactic* ∀ binders whose data are all
/// `.never`.  Structural on `k`, so no fuel: con-leche's own recursion
/// measure survives the change of representation unchanged.
pub fn peel_never_pis(
    pers: &PersTier,
    st: &AState,
    k: u64,
    h: &EIdx,
) -> Result<Option<EIdx>, CheckError> {
    if k == 0 {
        Ok(Some(h.dup2()))
    } else {
        if h.tag() == ETAG_FORALL_E {
            match view_bind(pers, st, h) {
                None => fail_dangling_e(),
                Some((_, b, m)) => {
                    if prop_when::is_never(&m.pw) {
                        peel_never_pis(pers, st, k - 1, &b)
                    } else {
                        Ok(None)
                    }
                },
            }
        } else {
            Ok(None)
        }
    }
}

/// con-leche: ConLeche/Kernel/PropRead.lean:58-61 Expr.numArgs
/// Lean twin: `proof/ConRon/Arena/PropRead.lean:54-61 numArgs` — the number of
/// arguments of an application spine.  A spine walk, hence fuel.
pub fn num_args(pers: &PersTier, st: &AState, fuel: u64, h: &EIdx) -> Result<u64, CheckError> {
    if fuel == 0 {
        fail(CheckError::Internal(code_points(&M_FUEL_NUM_ARGS)))
    } else {
        if h.tag() == ETAG_APP {
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
}

/// con-leche: ConLeche/Kernel/PropRead.lean:65-71 residualPW
/// Lean twin: `proof/ConRon/Arena/PropRead.lean:66-73 residualPW` — the
/// zero-ness datum of the sort of a *residual type*.  The level is read back
/// and `level::zeroness_of` is con-leche's own (deviation 3).
pub fn residual_pw(
    pers: &PersTier,
    st: &AState,
    h: Option<EIdx>,
) -> Result<Option<PropWhen>, CheckError> {
    match h {
        Some(r) => if r.tag() == ETAG_SORT {
            match view_sort(pers, st, &r) {
                None => fail_dangling_e(),
                Some(u) => match read_level(pers, st, &u) {
                    Err(e) => Err(e),
                    Ok(l) => Ok(Some(level::zeroness_of(&l))),
                },
            }
        } else {
            Ok(None)
        },
        None => Ok(None),
    }
}

/// con-leche: ConLeche/Kernel/PropRead.lean:73-90 headTypePW
/// Lean twin: `proof/ConRon/Arena/PropRead.lean:81-103 headTypePW` — the datum
/// of a type-former application's *head* at `n` arguments.  A constant head
/// reads its stored type, an fvar head its declared type; the residual after
/// `n` syntactic binders is read by `residual_pw`.
pub fn head_type_pw(
    pers: &PersTier,
    vis: u64,
    st: &mut AState,
    fe: &IFEnv,
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
                                    match peel_never_pis(pers, st, n, &cv.ty) {
                                        Err(e) => Err(e),
                                        Ok(res) => match residual_pw(pers, st, res) {
                                            Err(e) => Err(e),
                                            // The cutoff hoisted over the
                                            // readback, as in `head_proof_pw`.
                                            Ok(Some(pw)) => {
                                                if !prop_when::has_params(&pw) {
                                                    Ok(Some(pw))
                                                } else {
                                                    match read_names(
                                                        pers,
                                                        st,
                                                        &cv.level_params,
                                                    ) {
                                                        Err(e) => Err(e),
                                                        Ok(ks) => {
                                                            match read_levels(pers, st, &us) {
                                                                Err(e) => Err(e),
                                                                Ok(vs) => Ok(Some(
                                                                    level::subst_pw(
                                                                        &ks, &vs, &pw,
                                                                    ),
                                                                )),
                                                            }
                                                        }
                                                    }
                                                }
                                            }
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
        Ok(ENodeView::FVar(_, ty)) => match peel_never_pis(pers, st, n, &ty) {
            Err(e) => Err(e),
            Ok(res) => residual_pw(pers, st, res),
        },
        Ok(_) => Ok(None),
    }
}

/// con-leche: ConLeche/Kernel/PropRead.lean:92-103 typeSortPW
/// Lean twin: `proof/ConRon/Arena/PropRead.lean:108-115 typeSortPW` — the
/// zero-ness datum of the sort of the *type* `t` ("is `t` a proposition?").
/// con-leche's last arm rebinds the scrutinee; the twin keeps the handle.
pub fn type_sort_pw(
    pers: &PersTier,
    vis: u64,
    st: &mut AState,
    fe: &IFEnv,
    fuel: u64,
    t: &EIdx,
) -> Result<Option<PropWhen>, CheckError> {
    match view(pers, st, t) {
        Err(e) => Err(e),
        Ok(ENodeView::ForallE(_, _, m)) => Ok(Some(m.pw)),
        Ok(ENodeView::Sort(_)) => Ok(Some(prop_when::never())),
        Ok(_) => match get_app_fn(pers, st, fuel, t) {
            Err(e) => Err(e),
            Ok(fnh) => match num_args(pers, st, fuel, t) {
                Err(e) => Err(e),
                Ok(n) => head_type_pw(pers, vis, st, fe, &fnh, n),
            },
        },
    }
}

/// con-leche: ConLeche/Kernel/PropRead.lean:105-122 headProofPW
/// Lean twin: `proof/ConRon/Arena/PropRead.lean:121-141 headProofPW` — the
/// datum of a term's *head* (any arity): a constant head answers from its
/// stored type, an fvar head from its declared type; sorts, ∀s and literals
/// are never proofs.
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
                                        // **The cutoff hoisted over the
                                        // readback** (task #97-P6-10), the
                                        // shape task #97-P6-9's item 5 has.
                                        // `Level.substPW ks vs pw = pw` when
                                        // `pw` names no parameter (its `never`
                                        // and `always` arms are what
                                        // `PropWhen.hasParams` is false on,
                                        // and `bindZ` is the identity there),
                                        // so on a parameter-free datum — which
                                        // is what a `Prop`-or-never head
                                        // carries — both readbacks are
                                        // computed and dropped.
                                        Ok(Some(pw)) => {
                                            if !prop_when::has_params(&pw) {
                                                Ok(Some(pw))
                                            } else {
                                                match read_names(pers, st, &cv.level_params) {
                                                    Err(e) => Err(e),
                                                    Ok(ks) => match read_levels(pers, st, &us) {
                                                        Err(e) => Err(e),
                                                        Ok(vs) => Ok(Some(level::subst_pw(
                                                            &ks, &vs, &pw,
                                                        ))),
                                                    },
                                                }
                                            }
                                        }
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
        Ok(ENodeView::ForallE(_, _, _)) => Ok(Some(prop_when::never())),
        Ok(ENodeView::Lit(_)) => Ok(Some(prop_when::never())),
        Ok(_) => Ok(None),
    }
}

/// con-leche: ConLeche/Kernel/PropRead.lean:124-134 proofPW
/// Lean twin: `proof/ConRon/Arena/PropRead.lean:146-151 proofPW` — the
/// zero-ness datum of the sort of the *type* of `a` ("is `a` a proof?"), read
/// off `a`'s head symbol at any arity.
pub fn proof_pw(
    pers: &PersTier,
    vis: u64,
    st: &mut AState,
    fe: &IFEnv,
    fuel: u64,
    a: &EIdx,
) -> Result<Option<PropWhen>, CheckError> {
    if a.tag() == ETAG_LAM {
        match view_bind(pers, st, a) {
            None => fail_dangling_e(),
            Some((_, _, m)) => Ok(Some(m.pw)),
        }
    } else {
        match get_app_fn(pers, st, fuel, a) {
            Err(e) => Err(e),
            Ok(fnh) => head_proof_pw(pers, vis, st, fe, fuel, &fnh),
        }
    }
}

/// con-leche: ConLeche/Kernel/PropRead.lean:141-146 notProofFast
/// Lean twin: `proof/ConRon/Arena/PropRead.lean:158-161 notProofFast` —
/// **definitely not a proof**: the datum is known and is not always-zero.
/// Refusing the proof-irrelevance shortcut is always sound.  The cited
/// `!pw.isProp` is an `if` nest, as `con_ron_core::kernel::prop_read`'s is.
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

/// con-leche: ConLeche/Kernel/PropRead.lean:148-153 isProofFast
/// Lean twin: `proof/ConRon/Arena/PropRead.lean:166-169 isProofFast` —
/// **definitely a proof**: the datum is known and always-zero (the
/// squash-regime licence, con-leche's `prf_of_isProofFast`).
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
