//! Fast prop-ness off the head symbol — `ConLeche/Kernel/PropRead.lean`
//! (con-leche's task #168).
//!
//! Two pure readers that answer "is this type a proposition?" /
//! "is this term a proof?" from the head symbol, the arity and the validated
//! `pw` annotations — no inference, no reduction, no memo.  Ported with
//! `Kernel/Core.lean` (task #18) because `core_k::prop_irrel`,
//! `core_k::annot_pw_pi` and `core_k::annot_pw_lam` are their only consumers.
//!
//! **The `find?` function argument becomes the environment itself.**  The
//! Lean abstracts every reader over `find? : Name → Option ConstantInfo` so
//! that the pure core (`Env.find?`) and the interned core (`FEnv.find?`)
//! share one body.  The port has one environment type on the checker's path
//! — the index (`FEnv`, task #14) — so the parameter is `fe: &FEnv` and the
//! lookup is `fenv::find`, whose agreement with `Env.find?` is con-leche's
//! own F-mirror lemma (`ConLeche/Verify/EnvBound.lean`).  This is cheaper
//! than task #9's one-method-trait pattern and loses nothing: there is no
//! second instantiation to share with.
//!
//! Both readers are three-valued: `Some(pw)` is the datum, `None` is
//! "unknown, fall back to inference".

use crate::kernel::env;
use crate::kernel::env::ConstantVal;
use crate::kernel::expr;
use crate::kernel::expr::{Expr, ExprKind};
use crate::kernel::expr_ops;
use crate::kernel::fenv;
use crate::kernel::fenv::FEnv;
use crate::kernel::level;
use crate::kernel::levels;
use crate::kernel::name::Name;
use crate::kernel::prop_when;
use crate::kernel::prop_when::PropWhen;
use std::vec::Vec;

/// con-leche: ConLeche/Kernel/PropRead.lean:44-56 Expr.peelNeverPis
/// The residual after peeling `k` *syntactic* ∀ binders whose data are all
/// `.never` (no substitution — the residual may mention the peeled binders;
/// the readers only look at its head shape).
pub fn peel_never_pis(k: u64, e: &Expr) -> Option<Expr> {
    if k == 0 {
        Some(expr::dup(e))
    } else {
        match &e.0.kind {
            ExprKind::ForallE(_, b, m) => {
                if prop_when::is_never(&m.pw) {
                    peel_never_pis(k - 1, b)
                } else {
                    None
                }
            }
            _ => None,
        }
    }
}

/// con-leche: ConLeche/Kernel/PropRead.lean:58-61 Expr.numArgs
/// The number of arguments of an application spine.
pub fn num_args(e: &Expr) -> u64 {
    match &e.0.kind {
        ExprKind::App(f, _) => num_args(f) + 1,
        _ => 0,
    }
}

/// con-leche: ConLeche/Kernel/PropRead.lean:65-71 residualPW
/// The zero-ness datum of the sort of a *residual type*: a `Sort u` residual
/// says the type inhabits `Sort u`.  The argument is taken by value — it is
/// always a fresh `peel_never_pis` result.
pub fn residual_pw(e: Option<Expr>) -> Option<PropWhen> {
    match e {
        Some(r) => match &r.0.kind {
            ExprKind::Sort(u) => Some(level::zeroness_of(u)),
            _ => None,
        },
        None => None,
    }
}

/// con-leche: ConLeche/Kernel/PropRead.lean:73-90 headTypePW
/// con-leche: ConLeche/Kernel/PropRead.lean:105-122 headProofPW
/// The stored `ConstantVal` under `n` at a matching level-parameter count —
/// the `some ci => if ci.isTowerEntry then none else let cv :=
/// ci.toConstantVal; if us.length = cv.levelParams.length …` prefix both
/// cited readers open with, as its own function.
///
/// Deviations: a *probe*, per task #14's rule (never hold a container's
/// borrow across a branch that touches the container), so the copy of the
/// record happens at the call boundary and the reader below sees an owned
/// value; and `ci.toConstantVal` is the cited copy (task #14's note that a
/// Lean record share costs a `Vec<Name>` copy here).
pub fn stored_cv_at(fe: &FEnv, n: &Name, n_us: usize) -> Option<ConstantVal> {
    match fenv::find(fe, n) {
        Some(ci) => {
            if env::is_tower_entry(ci) {
                None
            } else {
                let cv = env::to_constant_val(ci);
                if n_us == cv.level_params.len() {
                    Some(cv)
                } else {
                    None
                }
            }
        }
        None => None,
    }
}

/// con-leche: ConLeche/Kernel/PropRead.lean:73-90 headTypePW
/// The datum of a type-former application's *head* at `n` arguments: a
/// constant head reads its stored type (level-instantiated), an fvar head its
/// declared type; the residual after `n` syntactic binders is read by
/// `residual_pw`.  The cited `Option.map` is an explicit `match` (§3.4 forbids
/// closures).
pub fn head_type_pw(fe: &FEnv, e: &Expr, n: u64) -> Option<PropWhen> {
    match &e.0.kind {
        ExprKind::Const(i, us) => match stored_cv_at(fe, i, levels::len(us)) {
            Some(cv) => match residual_pw(peel_never_pis(n, &cv.ty)) {
                Some(pw) => {
                    Some(level::subst_pw(&cv.level_params, &levels::to_vec(us), &pw))
                }
                None => None,
            },
            None => None,
        },
        ExprKind::Fvar(_, ty) => residual_pw(peel_never_pis(n, ty)),
        _ => None,
    }
}

/// con-leche: ConLeche/Kernel/PropRead.lean:92-103 typeSortPW
/// The zero-ness datum of the sort of the *type* `t` ("is `t` a
/// proposition?"), read off `t`'s head symbol and the annotations.
pub fn type_sort_pw(fe: &FEnv, t: &Expr) -> Option<PropWhen> {
    match &t.0.kind {
        ExprKind::ForallE(_, _, m) => Some(prop_when::dup(&m.pw)),
        ExprKind::Sort(_) => Some(prop_when::never()),
        _ => head_type_pw(fe, &expr_ops::get_app_fn(t), num_args(t)),
    }
}

/// con-leche: ConLeche/Kernel/PropRead.lean:105-122 headProofPW
/// The datum of a term's *head* (any arity): a constant head answers from its
/// stored type (prop-ness is invariant under application), an fvar head from
/// its declared type; sorts, ∀s and literals are never proofs.
pub fn head_proof_pw(fe: &FEnv, e: &Expr) -> Option<PropWhen> {
    match &e.0.kind {
        ExprKind::Const(c, us) => match stored_cv_at(fe, c, levels::len(us)) {
            Some(cv) => match type_sort_pw(fe, &cv.ty) {
                Some(pw) => {
                    Some(level::subst_pw(&cv.level_params, &levels::to_vec(us), &pw))
                }
                None => None,
            },
            None => None,
        },
        ExprKind::Fvar(_, ty) => type_sort_pw(fe, ty),
        ExprKind::Sort(_) => Some(prop_when::never()),
        ExprKind::ForallE(_, _, _) => Some(prop_when::never()),
        ExprKind::Lit(_) => Some(prop_when::never()),
        _ => None,
    }
}

/// con-leche: ConLeche/Kernel/PropRead.lean:124-134 proofPW
/// The zero-ness datum of the sort of the *type* of `a` ("is `a` a proof?"),
/// read off `a`'s head symbol at any arity.
pub fn proof_pw(fe: &FEnv, a: &Expr) -> Option<PropWhen> {
    match &a.0.kind {
        ExprKind::Lam(_, _, m) => Some(prop_when::dup(&m.pw)),
        _ => head_proof_pw(fe, &expr_ops::get_app_fn(a)),
    }
}

/// con-leche: ConLeche/Kernel/PropRead.lean:136-139 PropWhen.isProp
/// Is the datum "always zero" — the sort is `Prop` at every valuation?  The
/// cited `pw == (.ifAllZero [])` goes through the port's `prop_when::beq`.
pub fn is_prop(pw: &PropWhen) -> bool {
    prop_when::beq(pw, &prop_when::if_all_zero(Vec::new()))
}

/// con-leche: ConLeche/Kernel/PropRead.lean:141-146 notProofFast
/// **Definitely not a proof** (the no arm): the datum is known and is not
/// always-zero.  The cited `!pw.isProp` is an `if` nest: a `!` in a *value*
/// position comes out of Aeneas as Lean's propositional `¬`
/// (`core_k::defeq_lits`' note).
pub fn not_proof_fast(fe: &FEnv, a: &Expr) -> bool {
    match proof_pw(fe, a) {
        Some(pw) => {
            if is_prop(&pw) {
                false
            } else {
                true
            }
        }
        None => false,
    }
}

/// con-leche: ConLeche/Kernel/PropRead.lean:148-153 isProofFast
/// **Definitely a proof** (the yes arm): the datum is known and always-zero.
pub fn is_proof_fast(fe: &FEnv, a: &Expr) -> bool {
    match proof_pw(fe, a) {
        Some(pw) => is_prop(&pw),
        None => false,
    }
}

#[cfg(test)]
mod tests {
    use crate::kernel::env;
    use crate::kernel::env::{ConstantInfo, ConstantVal};
    use crate::kernel::expr;
    use crate::kernel::expr::BinderMeta;
    use crate::kernel::fenv;
    use crate::kernel::level;
    use crate::kernel::name;
    use crate::kernel::prop_read;
    use crate::kernel::prop_when;

    /// `x` as a one-character name.
    fn nm(c: u32) -> name::Name {
        name::mk_str(name::anonymous(), vec![c])
    }

    fn prop_meta() -> BinderMeta {
        expr::binder_meta(prop_when::if_all_zero(Vec::new()))
    }

    fn never_meta() -> BinderMeta {
        expr::binder_meta(prop_when::never())
    }

    /// `P : Sort 0` (a proposition) and `A : Sort 1` (data), as axioms, plus
    /// `hp : P` and `a : A`.
    fn env3() -> fenv::FEnv {
        let mut consts: Vec<ConstantInfo> = Vec::new();
        // newest first, as `Env.consts` is
        consts.push(ConstantInfo::AxiomInfo(ConstantVal {
            name: nm(97),
            ty: expr::mk_const(nm(65), Vec::new()),
            level_params: Vec::new(),
        })); // a : A
        consts.push(ConstantInfo::AxiomInfo(ConstantVal {
            name: nm(104),
            ty: expr::mk_const(nm(80), Vec::new()),
            level_params: Vec::new(),
        })); // h : P
        consts.push(ConstantInfo::AxiomInfo(ConstantVal {
            name: nm(80),
            ty: expr::sort(level::zero()),
            level_params: Vec::new(),
        })); // P : Sort 0
        consts.push(ConstantInfo::AxiomInfo(ConstantVal {
            name: nm(65),
            ty: expr::sort(level::succ(level::zero())),
            level_params: Vec::new(),
        })); // A : Sort 1
        fenv::mk_fenv(env::env_of(&consts))
    }

    #[test]
    fn peel_and_num_args() {
        let a = expr::mk_const(nm(65), Vec::new());
        let sp = expr::sort(level::zero());
        // ∀ (_ : A), Sort 0, with a `.never` binder datum
        let pi = expr::forall_e(expr::dup(&a), expr::dup(&sp), never_meta());
        assert!(prop_read::peel_never_pis(0, &pi).is_some());
        match prop_read::peel_never_pis(1, &pi) {
            Some(r) => assert!(expr::beq(&r, &sp)),
            None => panic!("peel should have passed the `.never` binder"),
        }
        assert!(prop_read::peel_never_pis(2, &pi).is_none());
        // a non-`.never` binder blocks the peel
        let pi2 = expr::forall_e(expr::dup(&a), expr::dup(&sp), prop_meta());
        assert!(prop_read::peel_never_pis(1, &pi2).is_none());
        // spine length
        let sp3 = expr::app(
            expr::app(expr::dup(&a), expr::dup(&a)),
            expr::dup(&a),
        );
        assert_eq!(prop_read::num_args(&sp3), 2);
        assert_eq!(prop_read::num_args(&a), 0);
    }

    #[test]
    fn readers_separate_proofs_from_data() {
        let fe = env3();
        let hp = expr::mk_const(nm(104), Vec::new());
        let a = expr::mk_const(nm(97), Vec::new());
        // `h : P` with `P : Sort 0` — definitely a proof
        assert!(prop_read::is_proof_fast(&fe, &hp));
        assert!(!prop_read::not_proof_fast(&fe, &hp));
        // `a : A` with `A : Sort 1` — definitely not a proof
        assert!(!prop_read::is_proof_fast(&fe, &a));
        assert!(prop_read::not_proof_fast(&fe, &a));
        // a sort is never a proof, and an unknown constant is unknown
        assert!(prop_read::not_proof_fast(&fe, &expr::sort(level::zero())));
        let unknown = expr::mk_const(nm(122), Vec::new());
        assert!(!prop_read::is_proof_fast(&fe, &unknown));
        assert!(!prop_read::not_proof_fast(&fe, &unknown));
        // `typeSortPW` of a ∀ is its binder datum; of a sort, `.never`
        match prop_read::type_sort_pw(
            &fe,
            &expr::forall_e(expr::dup(&a), expr::dup(&a), prop_meta()),
        ) {
            Some(pw) => assert!(prop_read::is_prop(&pw)),
            None => panic!("a ∀ always answers"),
        }
        match prop_read::type_sort_pw(&fe, &expr::sort(level::zero())) {
            Some(pw) => assert!(prop_when::is_never(&pw)),
            None => panic!("a sort always answers"),
        }
        // an unapplied λ answers from its own datum
        let lam = expr::lam(expr::mk_const(nm(65), Vec::new()), expr::bvar(0), prop_meta());
        assert!(prop_read::is_proof_fast(&fe, &lam));
        // `isProp` at the two extremes
        assert!(prop_read::is_prop(&prop_when::if_all_zero(Vec::new())));
        assert!(!prop_read::is_prop(&prop_when::never()));
        // an fvar head reads its annotation
        let fv = expr::fvar(0, expr::mk_const(nm(80), Vec::new()));
        assert!(prop_read::is_proof_fast(&fe, &fv));
        // the probe: a level-count mismatch is `none`
        assert!(prop_read::stored_cv_at(&fe, &nm(80), 1).is_none());
        assert!(prop_read::stored_cv_at(&fe, &nm(80), 0).is_some());
        let _ = env::empty();
    }
}
