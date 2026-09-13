//! `ConLeche/Kernel/DeclCheck.lean` — **the declaration checker through the
//! environment index** (con-leche task #63): the `FEnv`-indexed guard twins
//! and the `F`-mirrors of every `Kernel/Checker.lean` declaration-level
//! function.
//!
//! ## Most of this file is already ported, under its generic twin's name
//!
//! Each mirror is its generic counterpart with every environment lookup
//! (`Env.find?`, `Env.findCV?`, `Expr.constsResolve` and the compound guards
//! built from them) routed through the index, and under `mkFEnv` the two are
//! equal (`ConLeche/Verify/CheckerF.lean`).  **The port has one environment
//! spelling — the index** (task #18's deviation 3), so a mirror and its twin
//! are *one* Rust function carrying both citations, and they live with the
//! generic one:
//!
//! | mirror | Rust |
//! |---|---|
//! | `Expr.constsResolveF` | `core_k::consts_resolve` |
//! | `natOpCodF`, `natOpTyPinnedF`, `natOpStoredOkF` | `core_k::nat_op_cod`, `nat_op_ty_pinned`, `nat_op_stored_ok` |
//! | `stdAxiomOkF` | `std_axioms::std_axiom_ok` |
//! | `trustCompilerOkF`, `reduceStoredOkF`, `reduceElemOkF`, `ofReduceAxOkF`, `reducePinGuardF` | `trust_axioms::*` |
//! | `FEnv.findCV?` | `checker_base::find_cv` |
//! | `checkConstantValF`, `checkProjRuleF` | `checker_base::*` |
//! | `divMod*F`, `checkDivMod*F`, `checkReducePinF`, `checkDefnValF`, `installBasisDeclF` | `checker::*` |
//!
//! What is left, and what this module holds, is the **memoized
//! `constsResolveF` walk** and nothing else.
//!
//! ## The artifact/member family lives in `inductives::modeled`
//!
//! This module used to carry a second copy of `checkEtaThmF`,
//! `checkUnitThmF`, `indBlockCapsF`, `checkMemberValF`, `checkProjLookupsF`
//! and their helpers.  Task #25 re-ported all of them into
//! `kernel::inductives::modeled` — where the iota family they belong with is
//! — and *those* copies are what the install routes call; this file's were
//! dead from the day they were written, and two Rust functions under one
//! con-leche citation is a §3.1 one-to-one violation.  Task #58 deleted them.
//! Every remaining `F`-mirror of `DeclCheck.lean:344-830` is therefore
//! `inductives::modeled`'s and carries that citation there:
//! `checkEtaThmF`/`checkUnitThmF`/`indBlockCapsF`/`checkMemberValF`/
//! `checkProjLookupsF` (`:344-746`), `ctorResidualOkF` (`:416`),
//! `checkIotaThmF` (`:507`), `nestedRuleShapeF` (`:575`), `checkIotaThmNF`
//! (`:601`), `checkIotaRuleF` (`:687`), `checkIotaRulesF` (`:718`),
//! `checkProjTyF` (`:748`) and `checkProjIotaF` (`:797`) — the last two
//! ported by task #25, which this module's note used to call unported.
//!
//! `CRFMemoInv` (`:70`) and the three theorems about it are `Prop`s — the
//! invariant the Rust-side refinement proof will restate about
//! `crate::ron::hashmap` memos, not code (task #13's ruling).

use crate::kernel::core_k;
use crate::kernel::expr;
use crate::kernel::expr::{Expr, ExprKind};
use crate::kernel::expr_ops;
use crate::kernel::fenv;
use crate::kernel::fenv::FEnv;
use crate::ron::hashmap::HashMap;

// ---------------------------------------------------------------------------
// `constsResolveF`, memoized (`DeclCheck.lean:60-204`)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/DeclCheck.lean:89-124 Expr.constsResolveFGo
/// con-leche: ConLeche/Kernel/DeclCheck.lean:37-58 Expr.constsResolveF
/// The memoized constant-resolution walk.  Every direct-install stage asks it
/// of the block's types, and a tree walk does not finish on a DAG-shared
/// field type (con-leche task #215's `tower_struct`); swapped in by
/// `@[csimp]`, so the pure walk (`core_k::consts_resolve`) stays the spec.
/// Keyed by the node and dropped after each call, because the answer depends
/// on `fe`.
///
/// The four leaf arms answer through the spec walk, as the cited clauses do
/// (`(Expr.bvar i).constsResolveF fe` and friends): on a leaf it is `O(1)`.
pub fn consts_resolve_f_go(fe: &FEnv, memo: &mut HashMap<Expr, bool>, e: &Expr) -> bool {
    match &e.0.kind {
        ExprKind::Bvar(_) => core_k::consts_resolve(fe, e),
        ExprKind::Sort(_) => core_k::consts_resolve(fe, e),
        ExprKind::Lit(_) => core_k::consts_resolve(fe, e),
        ExprKind::Const(_, _) => core_k::consts_resolve(fe, e),
        _ => match expr_ops::memo_b_get(memo, e) {
            Some(r) => r,
            None => {
                let r: bool = match &e.0.kind {
                    ExprKind::Fvar(_, ty) => consts_resolve_f_go(fe, memo, ty),
                    ExprKind::App(f, a) => {
                        let b1: bool = consts_resolve_f_go(fe, memo, f);
                        let b2: bool = consts_resolve_f_go(fe, memo, a);
                        expr_ops::bool_and(b1, b2)
                    }
                    ExprKind::Lam(ty, body, _) => {
                        let b1: bool = consts_resolve_f_go(fe, memo, ty);
                        let b2: bool = consts_resolve_f_go(fe, memo, body);
                        expr_ops::bool_and(b1, b2)
                    }
                    ExprKind::ForallE(ty, body, _) => {
                        let b1: bool = consts_resolve_f_go(fe, memo, ty);
                        let b2: bool = consts_resolve_f_go(fe, memo, body);
                        expr_ops::bool_and(b1, b2)
                    }
                    ExprKind::LetE(ty, val, body) => {
                        let b1: bool = consts_resolve_f_go(fe, memo, ty);
                        let b2: bool = consts_resolve_f_go(fe, memo, val);
                        let b3: bool = consts_resolve_f_go(fe, memo, body);
                        expr_ops::bool_and3(b1, b2, b3)
                    }
                    ExprKind::Proj(s, _, sub) => {
                        let b: bool = consts_resolve_f_go(fe, memo, sub);
                        let ok: bool = fenv::find(fe, s).is_some();
                        expr_ops::bool_and(ok, b)
                    }
                    _ => core_k::consts_resolve(fe, e),
                };
                memo.insert(expr::dup(e), r);
                r
            }
        },
    }
}

/// con-leche: ConLeche/Kernel/DeclCheck.lean:197-199 Expr.constsResolveFFast
/// con-leche: ConLeche/Kernel/DeclCheck.lean:200-204 Expr.constsResolveF_eq_constsResolveFFast
/// The executed `constsResolveF` (one memoized DAG walk).  The cited
/// `@[csimp]` lemma is the kernel-checked equation with the spec walk.
pub fn consts_resolve_f_fast(fe: &FEnv, e: &Expr) -> bool {
    let mut memo: HashMap<Expr, bool> = HashMap::new();
    consts_resolve_f_go(fe, &mut memo, e)
}
