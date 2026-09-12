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
//! What is left, and what this module holds, is the part of the file that has
//! **no** generic twin: the memoized `constsResolveF` walk, the
//! model-companion member check, the two structure-artifact shape predicates
//! and the capability record they feed, and the projection lookups.
//!
//! ## What is not ported yet
//!
//! `checkIotaThmF` (`:507`), `nestedRuleShapeF` (`:575`), `checkIotaThmNF`
//! (`:601`), `checkIotaRuleF` (`:687`), `checkIotaRulesF` (`:718`),
//! `checkProjTyF` (`:748`), `checkProjIotaF` (`:797`) and `ctorResidualOkF`
//! (`:416`) stand on `ConLeche/Kernel/Inductives/*` — `checkIotaSidesTy`,
//! `projFwd`/`projBack`, `structFam` — a family this task does not port.
//! Two of them would additionally need the **two** index views the Lean
//! passes (`fe'` and `feSelf`), which in the port are one index at two
//! visibility bounds (`kernel::checker`'s module note 1); the function that
//! threads those bounds is their caller's, so they wait for it.
//!
//! `CRFMemoInv` (`:70`) and the three theorems about it are `Prop`s — the
//! invariant the Rust-side refinement proof will restate about
//! `crate::ron::hashmap` memos, not code (task #13's ruling).

use crate::cached::state_c::CState;
use crate::kernel::basis_names;
use crate::kernel::checker_base;
use crate::kernel::core_k;
use crate::kernel::core_types;
use crate::kernel::core_types::CheckM;
use crate::kernel::env;
use crate::kernel::env::{CheckMode, ConstantVal, IndCaps};
use crate::kernel::expr;
use crate::kernel::expr::{Expr, ExprKind};
use crate::kernel::expr_ops;
use crate::kernel::expr_ops::NameToName;
use crate::kernel::fenv;
use crate::kernel::fenv::FEnv;
use crate::kernel::level;
use crate::kernel::level::Level;
use crate::kernel::name;
use crate::kernel::name::Name;
use crate::kernel::prop_when;
use crate::kernel::std_axioms;
use crate::ron::hashmap::HashMap;
use std::vec::Vec;

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

// ---------------------------------------------------------------------------
// Model-companion names (the `_model` family the artifacts are looked up by)
// ---------------------------------------------------------------------------

/// con-leche: none — the `"_model"` string literal of `DeclCheck.lean`'s artifact lookups
/// The suffix as code points (DESIGN.md §3.3); Lean writes `n.str "_model"`.
pub fn model_suffix() -> Vec<u32> {
    core_types::code_points(&[95, 109, 111, 100, 101, 108])
}

/// con-leche: none — `n.str "_model"`, spelled a dozen times in `DeclCheck.lean`
/// The model companion's name.
pub fn model_name(n: &Name) -> Name {
    name::mk_str(name::dup(n), model_suffix())
}

/// con-leche: none — `(T.str "_model").str "eta"` of `checkEtaThmF`
/// The η-theorem artifact's name.
pub fn eta_thm_name(t: &Name) -> Name {
    name::mk_str(model_name(t), core_types::code_points(&[101, 116, 97]))
}

/// con-leche: none — `(T.str "_model").str "unitlike"` of `checkUnitThmF`
/// The unit-likeness-theorem artifact's name.
pub fn unit_thm_name(t: &Name) -> Name {
    name::mk_str(
        model_name(t),
        core_types::code_points(&[117, 110, 105, 116, 108, 105, 107, 101]),
    )
}

/// con-leche: none — replaces `checkMemberValF`'s local `f : Name → Name`
/// The one-method dictionary standing for the block-renaming function (task
/// #9's pattern 1; DESIGN.md §3.4 forbids closures): a block member's name
/// becomes its model companion's, every other name is itself.
pub struct ModelRename<'a> {
    pub block_names: &'a Vec<Name>,
}

/// con-leche: ConLeche/Kernel/DeclCheck.lean:487-505 checkMemberValF
/// The dictionary's one method (see `ModelRename`).
impl<'a> NameToName for ModelRename<'a> {
    /// con-leche: ConLeche/Kernel/DeclCheck.lean:487-505 checkMemberValF
    /// The cited `fun n => if blockNames.contains n then n.str "_model" else n`.
    fn rename(&self, n: &Name) -> Name {
        if name::contains(self.block_names, n) {
            model_name(n)
        } else {
            name::dup(n)
        }
    }
}

// ---------------------------------------------------------------------------
// Little `List`-over-`Vec` builders the shape predicates need
// ---------------------------------------------------------------------------

/// con-leche: none — `lps.map .param` of `checkEtaThmF`/`checkUnitThmF`
/// The level parameters as levels; DESIGN.md §3.4 forbids the closure.
pub fn lp_params(lps: &Vec<Name>) -> Vec<Level> {
    lp_params_from(lps, 0, Vec::new())
}

/// con-leche: none — the index recursion behind `lp_params`
/// The accumulator is passed by value and returned.
pub fn lp_params_from(lps: &Vec<Name>, i: usize, out: Vec<Level>) -> Vec<Level> {
    if i >= lps.len() {
        out
    } else {
        let mut out = out;
        out.push(level::param(name::dup(&lps[i])));
        lp_params_from(lps, i + 1, out)
    }
}

/// con-leche: none — `(List.range nP).map fun k => Expr.bvar (off - k)` of the artifact shapes
/// The parameter spine as descending de Bruijn indices, `off` down to
/// `off - (n - 1)`.  `checkEtaThmF` uses it at `off = nP - 1` (under one
/// binder) and at `off = nP` (under two); DESIGN.md §3.4 forbids the closure.
pub fn desc_bvars(n: u64, off: u64) -> Vec<Expr> {
    desc_bvars_from(n, off, 0, Vec::new())
}

/// con-leche: none — the index recursion behind `desc_bvars`
/// The accumulator is passed by value and returned.
pub fn desc_bvars_from(n: u64, off: u64, k: u64, out: Vec<Expr>) -> Vec<Expr> {
    if k >= n {
        out
    } else {
        let mut out = out;
        out.push(expr::bvar(off - k));
        desc_bvars_from(n, off, k + 1, out)
    }
}

/// con-leche: none — the `.const (T.str "_model") (lps.map .param)` spine of the artifact shapes
/// `mkAppN (.const (model T) lpsParams) (descBvars nP off)`, written four
/// times in the cited predicates.
pub fn model_app(t: &Name, lps: &Vec<Name>, n_p: u64, off: u64) -> Expr {
    expr_ops::mk_app_n(
        expr::mk_const(model_name(t), lp_params(lps)),
        &desc_bvars(n_p, off),
    )
}

// ---------------------------------------------------------------------------
// The structure artifacts' shape predicates (`DeclCheck.lean:344-441`)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/DeclCheck.lean:344-382 checkEtaThmF
/// The per-field model-companion level check of `checkEtaThmF`:
/// `(List.range nF).all (fun j => match fe.find? (projModelName T j) with
/// | some (.defnInfo cvmj _ _) => cvmj.levelParams == lps | _ => false)`.
pub fn proj_models_leveled(fe: &FEnv, t: &Name, lps: &Vec<Name>, n_f: u64, j: u64) -> bool {
    if j >= n_f {
        true
    } else {
        match core_k::defn_probe(fe, &core_k::proj_model_name(t, j)) {
            Some((cvmj, _, _)) => {
                if prop_when::names_beq(&cvmj.level_params, lps) {
                    proj_models_leveled(fe, t, lps, n_f, j + 1)
                } else {
                    false
                }
            }
            None => false,
        }
    }
}

/// con-leche: ConLeche/Kernel/DeclCheck.lean:344-382 checkEtaThmF
/// The η-statement's right-hand side: the constructor's model companion
/// applied to the parameters and to every field's projection companion at the
/// same parameters and the bound structure.
pub fn eta_rhs(t: &Name, ctor_name: &Name, lps: &Vec<Name>, n_p: u64, n_f: u64) -> Expr {
    let args: Vec<Expr> = core_k::append_exprs(
        desc_bvars(n_p, n_p),
        &eta_proj_apps(t, lps, n_p, n_f, 0, Vec::new()),
    );
    expr_ops::mk_app_n(
        expr::mk_const(model_name(ctor_name), lp_params(lps)),
        &args,
    )
}

/// con-leche: ConLeche/Kernel/DeclCheck.lean:344-382 checkEtaThmF
/// The cited `(List.range nF).map fun j => mkAppN (.const (projModelName T j)
/// …) (params ++ [bvar 0])`, as an index recursion.
pub fn eta_proj_apps(
    t: &Name,
    lps: &Vec<Name>,
    n_p: u64,
    n_f: u64,
    j: u64,
    out: Vec<Expr>,
) -> Vec<Expr> {
    if j >= n_f {
        out
    } else {
        let mut args: Vec<Expr> = desc_bvars(n_p, n_p);
        args.push(expr::bvar(0));
        let mut out = out;
        out.push(expr_ops::mk_app_n(
            expr::mk_const(core_k::proj_model_name(t, j), lp_params(lps)),
            &args,
        ));
        eta_proj_apps(t, lps, n_p, n_f, j + 1, out)
    }
}

/// con-leche: ConLeche/Kernel/DeclCheck.lean:344-382 checkEtaThmF
/// The η-statement's body shape: `Eq.{ℓA} (T._model ps) (bvar 0)
/// (ctor._model ps (proj₀ ps (bvar 0)) …)`, plus the TT-lane check that the
/// model's own codomain is `Sort ℓA` (skipped unless `mode.ttChecks`).
pub fn eta_body_ok(
    mode: &CheckMode,
    t: &Name,
    ctor_name: &Name,
    lps: &Vec<Name>,
    n_p: u64,
    n_f: u64,
    sbody: &Expr,
    tbody_m: &Expr,
) -> bool {
    match eq_spine3(sbody) {
        None => false,
        Some((l_a, ty_slot, lhs_c, rhs_c)) => {
            if !expr::beq(&lhs_c, &expr::bvar(0)) {
                false
            } else if !expr::beq(&ty_slot, &model_app(t, lps, n_p, n_p)) {
                false
            } else if !expr::beq(&rhs_c, &eta_rhs(t, ctor_name, lps, n_p, n_f)) {
                false
            } else if !env::tt_checks(mode) {
                true
            } else {
                expr::beq(tbody_m, &expr::sort(l_a))
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/DeclCheck.lean:344-382 checkEtaThmF
/// con-leche: ConLeche/Kernel/DeclCheck.lean:384-414 checkUnitThmF
/// The cited `.app (.app (.app (.const c [ℓA]) tySlot) lhsC) rhsC` pattern
/// with `c == eqName`: the equation's level and its three arguments, or
/// `none` off shape.  Both artifact predicates open with it.
pub fn eq_spine3(e: &Expr) -> Option<(Level, Expr, Expr, Expr)> {
    match &e.0.kind {
        ExprKind::App(f1, rhs_c) => match &f1.0.kind {
            ExprKind::App(f2, lhs_c) => match &f2.0.kind {
                ExprKind::App(f3, ty_slot) => match &f3.0.kind {
                    ExprKind::Const(c, us) => {
                        if us.len() == 1 && name::beq(c, &basis_names::eq_name()) {
                            Some((
                                level::dup(&us[0]),
                                expr::dup(ty_slot),
                                expr::dup(lhs_c),
                                expr::dup(rhs_c),
                            ))
                        } else {
                            None
                        }
                    }
                    _ => None,
                },
                _ => None,
            },
            _ => None,
        },
        _ => None,
    }
}

/// con-leche: ConLeche/Kernel/DeclCheck.lean:344-382 checkEtaThmF
/// Is the block's η artifact present and standardly shaped?  The stored
/// `T._model.eta` theorem, the type former's and the constructor's model
/// companions, every field's projection companion, the pinned `Eq` basis, and
/// the statement's telescope and body.  Deviation: the cited four-way `match`
/// on simultaneous lookups is a cascade of owning probes (task #14's rule),
/// and the `&&` chain is an `if` nest (task #3's pattern 9).
pub fn check_eta_thm(
    mode: &CheckMode,
    fe: &FEnv,
    t: &Name,
    ctor_name: &Name,
    lps: &Vec<Name>,
    n_p: u64,
    n_f: u64,
) -> bool {
    match thm_probe(fe, &eta_thm_name(t)) {
        None => false,
        Some(tcv) => match core_k::defn_probe(fe, &model_name(t)) {
            None => false,
            Some((cvm_t, _, _)) => match core_k::defn_probe(fe, &model_name(ctor_name)) {
                None => false,
                Some((cvm_c, _, _)) => {
                    if !std_axioms::eq_basis_pinned(fe) {
                        false
                    } else if !prop_when::names_beq(&tcv.level_params, lps) {
                        false
                    } else if !prop_when::names_beq(&cvm_t.level_params, lps) {
                        false
                    } else if !prop_when::names_beq(&cvm_c.level_params, lps) {
                        false
                    } else if !proj_models_leveled(fe, t, lps, n_f, 0) {
                        false
                    } else {
                        eta_telescope_ok(mode, t, ctor_name, lps, n_p, n_f, &tcv, &cvm_t)
                    }
                }
            },
        },
    }
}

/// con-leche: ConLeche/Kernel/DeclCheck.lean:344-382 checkEtaThmF
/// The cited `match tcv.type.stripPis (nP + 1), cvmT.type.stripPis nP with`
/// stage: the statement's parameter domains against the model's, its
/// structure binder, and its body.
pub fn eta_telescope_ok(
    mode: &CheckMode,
    t: &Name,
    ctor_name: &Name,
    lps: &Vec<Name>,
    n_p: u64,
    n_f: u64,
    tcv: &ConstantVal,
    cvm_t: &ConstantVal,
) -> bool {
    match expr_ops::strip_pis(n_p + 1, &tcv.ty) {
        None => false,
        Some((sbinders, sbody)) => match expr_ops::strip_pis(n_p, &cvm_t.ty) {
            None => false,
            Some((tbinders_m, tbody_m)) => {
                if !checker_base::doms_match_aux(&sbinders, &tbinders_m, 0, 0, n_p) {
                    false
                } else if n_p >= sbinders.len() as u64 {
                    false
                } else if !expr::beq(
                    &sbinders[n_p as usize].0,
                    &model_app(t, lps, n_p, n_p - 1),
                ) {
                    false
                } else {
                    eta_body_ok(mode, t, ctor_name, lps, n_p, n_f, &sbody, &tbody_m)
                }
            }
        },
    }
}

/// con-leche: ConLeche/Kernel/DeclCheck.lean:384-414 checkUnitThmF
/// Is the block's unit-likeness artifact present and standardly shaped?  The
/// stored `T._model.unitlike` theorem over the pinned `Eq` basis, whose
/// statement equates two inhabitants of the model at the same parameters.
pub fn check_unit_thm(
    mode: &CheckMode,
    fe: &FEnv,
    t: &Name,
    lps: &Vec<Name>,
    n_p: u64,
) -> bool {
    match thm_probe(fe, &unit_thm_name(t)) {
        None => false,
        Some(tcv) => match core_k::defn_probe(fe, &model_name(t)) {
            None => false,
            Some((cvm_t, _, _)) => {
                if !std_axioms::eq_basis_pinned(fe) {
                    false
                } else if !prop_when::names_beq(&tcv.level_params, lps) {
                    false
                } else if !prop_when::names_beq(&cvm_t.level_params, lps) {
                    false
                } else {
                    unit_telescope_ok(mode, t, lps, n_p, &tcv, &cvm_t)
                }
            }
        },
    }
}

/// con-leche: ConLeche/Kernel/DeclCheck.lean:384-414 checkUnitThmF
/// The cited `match tcv.type.stripPis (nP + 2), cvmT.type.stripPis nP with`
/// stage: the parameter domains, the two structure binders, and the body
/// `Eq.{ℓA} (T._model ps) (bvar 1) (bvar 0)`.
pub fn unit_telescope_ok(
    mode: &CheckMode,
    t: &Name,
    lps: &Vec<Name>,
    n_p: u64,
    tcv: &ConstantVal,
    cvm_t: &ConstantVal,
) -> bool {
    match expr_ops::strip_pis(n_p + 2, &tcv.ty) {
        None => false,
        Some((sbinders, sbody)) => match expr_ops::strip_pis(n_p, &cvm_t.ty) {
            None => false,
            Some((tbinders_m, tbody_m)) => {
                if !checker_base::doms_match_aux(&sbinders, &tbinders_m, 0, 0, n_p) {
                    false
                } else if n_p + 1 >= sbinders.len() as u64 {
                    false
                } else if !expr::beq(
                    &sbinders[n_p as usize].0,
                    &model_app(t, lps, n_p, n_p - 1),
                ) {
                    false
                } else if !expr::beq(
                    &sbinders[(n_p + 1) as usize].0,
                    &model_app(t, lps, n_p, n_p),
                ) {
                    false
                } else {
                    unit_body_ok(mode, t, lps, n_p, &sbody, &tbody_m)
                }
            }
        },
    }
}

/// con-leche: ConLeche/Kernel/DeclCheck.lean:384-414 checkUnitThmF
/// The unit-likeness statement's body shape, plus the TT-lane check.
pub fn unit_body_ok(
    mode: &CheckMode,
    t: &Name,
    lps: &Vec<Name>,
    n_p: u64,
    sbody: &Expr,
    tbody_m: &Expr,
) -> bool {
    match eq_spine3(sbody) {
        None => false,
        Some((l_a, ty_slot, lhs_c, rhs_c)) => {
            if !expr::beq(&lhs_c, &expr::bvar(1)) {
                false
            } else if !expr::beq(&rhs_c, &expr::bvar(0)) {
                false
            } else if !expr::beq(&ty_slot, &model_app(t, lps, n_p, n_p + 1)) {
                false
            } else if !env::tt_checks(mode) {
                true
            } else {
                expr::beq(tbody_m, &expr::sort(l_a))
            }
        }
    }
}

/// con-leche: none — the `some (.thmInfo tcv _)` destructuring of `DeclCheck.lean`'s artifact lookups
/// An owning probe, as `core_k`'s five environment probes (task #14's rule):
/// the index's borrow dies at the call boundary and the caller works on the
/// copy Lean's value semantics hands its pattern variables.
pub fn thm_probe(fe: &FEnv, n: &Name) -> Option<ConstantVal> {
    match fenv::find(fe, n) {
        Some(env::ConstantInfo::ThmInfo(cv, _)) => Some(env::constant_val_dup(cv)),
        _ => None,
    }
}

/// con-leche: ConLeche/Kernel/DeclCheck.lean:430-441 indBlockCapsF
/// The capability record recorded at a modeled structure-like block's
/// install: η (from the η artifact), unit-likeness, the K rule, and the
/// sort's zeroness.  `indBlockCapsF_sortZ` (`:443-446`) is the field equation
/// this record satisfies by construction.
pub fn ind_block_caps(
    mode: &CheckMode,
    fe: &FEnv,
    cv_t: &ConstantVal,
    cv_c: &ConstantVal,
    n_p: u64,
    n_f: u64,
) -> IndCaps {
    let eta: bool = if prop_when::names_beq(&cv_c.level_params, &cv_t.level_params) {
        check_eta_thm(
            mode,
            fe,
            &cv_t.name,
            &cv_c.name,
            &cv_t.level_params,
            n_p,
            n_f,
        )
    } else {
        false
    };
    IndCaps {
        eta,
        eta_ctor: name::dup(&cv_c.name),
        eta_params: n_p,
        eta_fields: n_f,
        unitlike: check_unit_thm(mode, fe, &cv_t.name, &cv_t.level_params, n_p),
        unit_params: n_p,
        rule_k: n_f == 0 && core_k::pi_result_is_prop(&cv_t.ty),
        sort_z: core_k::pi_result_z(&cv_t.ty),
    }
}

// ---------------------------------------------------------------------------
// The member and projection mirrors (`DeclCheck.lean:487-746`)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/DeclCheck.lean:487-505 checkMemberValF
/// One inductive-block member's constant check: the common
/// `checkConstantVal`, no model-shaped name of its own, and the *model
/// companion* that the in-process modeller generated for it — same level
/// parameters, and a type that is this member's with the block's names
/// renamed to their companions'.
pub fn check_member_val(
    mode: &CheckMode,
    st: &mut CState,
    block_names: &Vec<Name>,
    fe: &FEnv,
    cv: &ConstantVal,
) -> CheckM<ConstantVal> {
    match checker_base::check_constant_val(mode, st, fe, cv) {
        Err(err) => Err(err),
        Ok(cv_a) => {
            if level::name_is_model_suffix(&cv_a.name) {
                Err(core_types::invalid({ const M: [u32; 24] = [109, 111, 100, 101, 108, 45, 115, 104, 97, 112, 101, 100, 32, 109, 101, 109, 98, 101, 114, 32, 110, 97, 109, 101]; core_types::code_points(&M) }))
            } else {
                match core_k::defn_probe(fe, &model_name(&cv_a.name)) {
                    None => Err(core_types::not_implemented({ const M: [u32; 94] = [110, 111, 32, 105, 110, 115, 116, 97, 108, 108, 32, 114, 111, 117, 116, 101, 32, 102, 111, 114, 32, 105, 110, 100, 117, 99, 116, 105, 118, 101, 32, 98, 108, 111, 99, 107, 58, 32, 110, 111, 32, 100, 105, 114, 101, 99, 116, 32, 114, 111, 117, 116, 101, 32, 114, 101, 99, 111, 103, 110, 105, 115, 101, 115, 32, 105, 116, 32, 97, 110, 100, 32, 110, 111, 32, 109, 111, 100, 101, 108, 32, 119, 97, 115, 32, 103, 101, 110, 101, 114, 97, 116, 101, 100]; core_types::code_points(&M) })),
                    Some((cvm, _, _)) => {
                        if !prop_when::names_beq(&cvm.level_params, &cv_a.level_params) {
                            Err(core_types::not_implemented({ const M: [u32; 31] = [109, 111, 100, 101, 108, 32, 108, 101, 118, 101, 108, 32, 112, 97, 114, 97, 109, 101, 116, 101, 114, 115, 32, 109, 105, 115, 109, 97, 116, 99, 104]; core_types::code_points(&M) }))
                        } else {
                            let f: ModelRename = ModelRename { block_names };
                            let renamed: Expr = expr_ops::rename_consts(&f, &cv_a.ty);
                            if expr::beq(&renamed, &cvm.ty) {
                                Ok(cv_a)
                            } else {
                                Err(core_types::not_implemented({ const M: [u32; 19] = [109, 111, 100, 101, 108, 32, 116, 121, 112, 101, 32, 109, 105, 115, 109, 97, 116, 99, 104]; core_types::code_points(&M) }))
                            }
                        }
                    }
                }
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/DeclCheck.lean:729-746 checkProjLookupsF
/// The projection-function install's environment lookups: the stored
/// constructor at the expected arity, the field's projection model companion
/// at the block's level parameters, a free projection-function name, the
/// stored parent, and the pinned `Eq` basis (the projection iota is an
/// equation in it).
pub fn check_proj_lookups(
    fe: &FEnv,
    t: &Name,
    ctor_name: &Name,
    lps: &Vec<Name>,
    n_p: u64,
    n_f: u64,
    i: u64,
) -> CheckM<(ConstantVal, ConstantVal)> {
    match core_k::ctor_probe(fe, ctor_name) {
        None => Err(core_types::not_implemented({ const M: [u32; 33] = [112, 114, 111, 106, 101, 99, 116, 105, 111, 110, 32, 99, 111, 110, 115, 116, 114, 117, 99, 116, 111, 114, 32, 110, 111, 116, 32, 115, 116, 111, 114, 101, 100]; core_types::code_points(&M) })),
        Some((cvj, cn_p, cn_f)) => {
            if cn_p != n_p || cn_f != n_f {
                Err(core_types::not_implemented({ const M: [u32; 37] = [112, 114, 111, 106, 101, 99, 116, 105, 111, 110, 32, 99, 111, 110, 115, 116, 114, 117, 99, 116, 111, 114, 32, 97, 114, 105, 116, 121, 32, 109, 105, 115, 109, 97, 116, 99, 104]; core_types::code_points(&M) }))
            } else {
                match core_k::defn_probe(fe, &core_k::proj_model_name(t, i)) {
                    None => Err(core_types::not_implemented({ const M: [u32; 24] = [109, 105, 115, 115, 105, 110, 103, 32, 112, 114, 111, 106, 101, 99, 116, 105, 111, 110, 32, 109, 111, 100, 101, 108]; core_types::code_points(&M) })),
                    Some((mcv, _, _)) => {
                        if !prop_when::names_beq(&mcv.level_params, lps) {
                            Err(core_types::not_implemented({ const M: [u32; 31] = [112, 114, 111, 106, 101, 99, 116, 105, 111, 110, 32, 109, 111, 100, 101, 108, 32, 108, 101, 118, 101, 108, 32, 109, 105, 115, 109, 97, 116, 99, 104]; core_types::code_points(&M) }))
                        } else if fenv::find(fe, &env::proj_fn_name(t, i)).is_some() {
                            Err(core_types::invalid({ const M: [u32; 21] = [112, 114, 111, 106, 101, 99, 116, 105, 111, 110, 32, 110, 97, 109, 101, 32, 116, 97, 107, 101, 110]; core_types::code_points(&M) }))
                        } else if fenv::find(fe, t).is_none() {
                            Err(core_types::not_implemented({ const M: [u32; 28] = [112, 114, 111, 106, 101, 99, 116, 105, 111, 110, 32, 112, 97, 114, 101, 110, 116, 32, 110, 111, 116, 32, 115, 116, 111, 114, 101, 100]; core_types::code_points(&M) }))
                        } else if !std_axioms::eq_basis_pinned(fe) {
                            Err(core_types::not_implemented({ const M: [u32; 44] = [112, 114, 111, 106, 101, 99, 116, 105, 111, 110, 32, 105, 111, 116, 97, 32, 114, 101, 113, 117, 105, 114, 101, 115, 32, 116, 104, 101, 32, 112, 105, 110, 110, 101, 100, 32, 69, 113, 32, 98, 97, 115, 105, 115]; core_types::code_points(&M) }))
                        } else {
                            Ok((cvj, mcv))
                        }
                    }
                }
            }
        }
    }
}
