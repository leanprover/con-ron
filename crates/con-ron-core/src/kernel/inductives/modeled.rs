//! `ConLeche/Kernel/Inductives/Modeled.lean` — **the modeled install route**:
//! every member of the block is checked against its `_model` counterpart (its
//! type up to the public↔model renaming, its iota rules against the model's
//! `iota_j` theorems), then stored as a real inductive-kind constant; a
//! single-constructor block determines its capability record first and, when
//! structure-like, installs the projection functions the model documents.
//!
//! Every stage here carries **two** citations: the `Env`-shaped definition of
//! `Inductives/Modeled.lean` and the index-threaded twin of
//! `Kernel/DeclCheck.lean` that the executable runs (`super`'s module note 1).
//! The three `Cached/CheckerC.lean` stages that add a `flushC` at an
//! environment transition — `checkIndMemberS`, `provisionRecsS`,
//! `checkIndRecsS`, `installProjFnStepS`, `checkIndDeclSF` — are
//! `super::inductives_c`'s.
//!
//! ## `fenv::dup` at the recursor group
//!
//! `checkIndRecs` holds **three** views of the index at once: the block-member
//! environment `env₂` (the one every iota check runs its `env'` lookups in),
//! the fully provisioned `envSelf` that `provisionRecs` built on top of it,
//! and the fold's accumulator, which starts as `env₂` and grows.  con-leche's
//! index is persistent, so all three are free; the port threads linearly
//! (task #14) and takes two `fenv::dup`s here — once for `provisionRecs`'
//! accumulator and once for the `env'` view the fold keeps.  Per inductive
//! block, as in `native_install`'s module note.

use crate::cached::core_c;
use crate::cached::state_c::CState;
use crate::kernel::basis_pins;
use crate::kernel::checker_base;
use crate::kernel::core_k;
use crate::kernel::decl_check;
use crate::kernel::core_types;
use crate::kernel::core_types::CheckM;
use crate::kernel::env;
use crate::kernel::env::{
    CheckMode, ConstantInfo, ConstantVal, IndCaps, RecRule, RecRuleFire,
};
use crate::kernel::expr;
use crate::kernel::expr::{Expr, ExprKind};
use crate::kernel::expr_ops;
use crate::kernel::expr_ops::NameToName;
use crate::kernel::fenv;
use crate::kernel::fenv::FEnv;
use crate::kernel::checker_base::{DomIdent, DomView};
use crate::kernel::inductives::struct_parts;
use crate::kernel::level;
use crate::kernel::level::Level;
use crate::kernel::name;
use crate::kernel::name::Name;
use crate::kernel::prop_when;
use std::vec::Vec;

// ---------------------------------------------------------------------------
// The name maps (`Modeled.lean:379-477`, `DeclCheck.lean:487-489`)
// ---------------------------------------------------------------------------

/// con-leche: none — `"_model"`, the model companion's name component
/// Every `n.str "_model"` below goes through this (§3.3's code-point
/// spelling of a Lean string literal).
pub fn model_str() -> Vec<u32> {
    const MODEL: [u32; 6] = [95, 109, 111, 100, 101, 108];
    core_types::code_points(&MODEL)
}

/// con-leche: none — `n.str "_model"`
/// The model companion of a name.
pub fn model_of(n: &Name) -> Name {
    name::mk_str(name::dup(n), model_str())
}

/// con-leche: ConLeche/Kernel/Inductives/Modeled.lean:373-401 checkMemberVal
/// con-leche: ConLeche/Kernel/DeclCheck.lean:487-505 checkMemberValF
/// con-leche: ConLeche/Kernel/Inductives/Modeled.lean:435-455 checkIndRecs
/// The block renaming `fun n => if blockNames.contains n then n.str "_model"
/// else n`, as a `NameToName` dictionary (task #9's pattern 1; §3.4 forbids
/// closures).  It captures the block's names by shared reference, which is
/// what Lean's closure captures by value.
pub struct BlockRename<'a> {
    pub block_names: &'a Vec<Name>,
}

/// con-leche: ConLeche/Kernel/Inductives/Modeled.lean:373-401 checkMemberVal
impl<'a> NameToName for BlockRename<'a> {
    /// con-leche: ConLeche/Kernel/Inductives/Modeled.lean:373-401 checkMemberVal
    fn rename(&self, n: &Name) -> Name {
        if name::contains(self.block_names, n) {
            model_of(n)
        } else {
            name::dup(n)
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/Modeled.lean:457-464 projBack
/// Rename a model-side projection type back to public names, as a
/// `NameToName` dictionary.
pub struct ProjBack<'a> {
    pub t: &'a Name,
    pub ctor: &'a Name,
    pub n_f: u64,
}

/// con-leche: ConLeche/Kernel/Inductives/Modeled.lean:457-464 projBack
impl<'a> NameToName for ProjBack<'a> {
    /// con-leche: ConLeche/Kernel/Inductives/Modeled.lean:457-464 projBack
    fn rename(&self, n: &Name) -> Name {
        if name::beq(n, &model_of(self.t)) {
            name::dup(self.t)
        } else if name::beq(n, &model_of(self.ctor)) {
            name::dup(self.ctor)
        } else {
            match find_proj_model_slot(self.t, self.n_f, n, 0) {
                Some(j) => env::proj_fn_name(self.t, j),
                None => name::dup(n),
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/Modeled.lean:457-464 projBack
/// `(List.range nF).find? (fun j => n == projModelName T j)`, as an index
/// recursion (task #3's pattern).
pub fn find_proj_model_slot(t: &Name, n_f: u64, n: &Name, j: u64) -> Option<u64> {
    if j >= n_f {
        None
    } else if name::beq(n, &core_k::proj_model_name(t, j)) {
        Some(j)
    } else {
        find_proj_model_slot(t, n_f, n, j + 1)
    }
}

/// con-leche: ConLeche/Kernel/Inductives/Modeled.lean:466-473 projFwd
/// The forward (public → model) map on the projection family.
pub struct ProjFwd<'a> {
    pub t: &'a Name,
    pub ctor: &'a Name,
    pub n_f: u64,
}

/// con-leche: ConLeche/Kernel/Inductives/Modeled.lean:466-473 projFwd
impl<'a> NameToName for ProjFwd<'a> {
    /// con-leche: ConLeche/Kernel/Inductives/Modeled.lean:466-473 projFwd
    fn rename(&self, n: &Name) -> Name {
        if name::beq(n, self.t) {
            model_of(self.t)
        } else if name::beq(n, self.ctor) {
            model_of(self.ctor)
        } else {
            match find_proj_fn_slot(self.t, self.n_f, n, 0) {
                Some(j) => core_k::proj_model_name(self.t, j),
                None => name::dup(n),
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/Modeled.lean:466-473 projFwd
/// `(List.range nF).find? (fun j => n == projFnName T j)`.
pub fn find_proj_fn_slot(t: &Name, n_f: u64, n: &Name, j: u64) -> Option<u64> {
    if j >= n_f {
        None
    } else if name::beq(n, &env::proj_fn_name(t, j)) {
        Some(j)
    } else {
        find_proj_fn_slot(t, n_f, n, j + 1)
    }
}

/// con-leche: ConLeche/Kernel/Inductives/Modeled.lean:513-563 checkProjIota
/// con-leche: ConLeche/Kernel/DeclCheck.lean:797-836 checkProjIotaF
/// `domsMatchAux (fun _ e => e.renameConsts (projFwd T ctorName nF))`, the one
/// non-identity binder view in the port (`checker_base::DomView`).
pub struct DomProjFwd<'a> {
    pub t: &'a Name,
    pub ctor: &'a Name,
    pub n_f: u64,
}

/// con-leche: ConLeche/Kernel/Inductives/Modeled.lean:513-563 checkProjIota
impl<'a> DomView for DomProjFwd<'a> {
    /// con-leche: ConLeche/Kernel/Inductives/Modeled.lean:513-563 checkProjIota
    fn view(&self, _i: u64, e: &Expr) -> Expr {
        let f = ProjFwd {
            t: self.t,
            ctor: self.ctor,
            n_f: self.n_f,
        };
        expr_ops::rename_consts(&f, e)
    }
}

// ---------------------------------------------------------------------------
// Small readers
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/Inductives/Modeled.lean:55-149 checkIotaThm
/// con-leche: ConLeche/Kernel/DeclCheck.lean:507-573 checkIotaThmF
/// `(cvName.str "_model").str s!"iota_{j}"` — the model's `j`-th iota
/// theorem's name.  The decimal rendering is `core_k::nat_to_dec`
/// (task #18's deviation 7).
pub fn iota_thm_name(cv_name: &Name, j: u64) -> Name {
    const IOTA_: [u32; 5] = [105, 111, 116, 97, 95];
    let head: Name = model_of(cv_name);
    let mut s: Vec<u32> = core_types::code_points(&IOTA_);
    let digits: Vec<u32> = core_k::nat_to_dec(j);
    s = core_types::code_points_from(&digits, 0, s);
    name::mk_str(head, s)
}

/// con-leche: ConLeche/Kernel/Inductives/Modeled.lean:513-563 checkProjIota
/// con-leche: ConLeche/Kernel/DeclCheck.lean:797-836 checkProjIotaF
/// `(projModelName T i).str "iota"` — the model's projection-iota theorem.
pub fn proj_iota_name(t: &Name, i: u64) -> Name {
    const IOTA: [u32; 4] = [105, 111, 116, 97];
    name::mk_str(core_k::proj_model_name(t, i), core_types::code_points(&IOTA))
}

/// con-leche: ConLeche/Kernel/Inductives/Modeled.lean:586-642 checkEtaThm
/// con-leche: ConLeche/Kernel/DeclCheck.lean:344-382 checkEtaThmF
/// `(T.str "_model").str "eta"`.
pub fn eta_thm_name(t: &Name) -> Name {
    const ETA: [u32; 3] = [101, 116, 97];
    name::mk_str(model_of(t), core_types::code_points(&ETA))
}

/// con-leche: ConLeche/Kernel/Inductives/Modeled.lean:644-680 checkUnitThm
/// con-leche: ConLeche/Kernel/DeclCheck.lean:384-414 checkUnitThmF
/// `(T.str "_model").str "unitlike"`.
pub fn unit_thm_name(t: &Name) -> Name {
    const UL: [u32; 8] = [117, 110, 105, 116, 108, 105, 107, 101];
    name::mk_str(model_of(t), core_types::code_points(&UL))
}

/// con-leche: ConLeche/Kernel/Inductives/Modeled.lean:513-563 checkProjIota
/// con-leche: ConLeche/Kernel/Inductives/Modeled.lean:586-642 checkEtaThm
/// The `some (.thmInfo tcv _)` destructuring, as an owning probe (task #18's
/// deviation 8: the index's borrow dies at the call boundary).
pub fn thm_probe(fe: &FEnv, n: &Name) -> Option<ConstantVal> {
    match fenv::find(fe, n) {
        Some(ConstantInfo::ThmInfo(cv, _)) => Some(env::constant_val_dup(cv)),
        Some(_) => None,
        None => None,
    }
}

/// con-leche: none — `targs.getD k (.bvar 0)` over a `Vec<Expr>`
/// The out-of-range fallback the equation readers spell at every argument
/// read (`Expr.bvar 0` is Lean's `default : Expr`, `env::default_expr`).
pub fn arg_get_d(args: &Vec<Expr>, k: usize) -> Expr {
    if k < args.len() {
        expr::dup(&args[k])
    } else {
        expr::bvar(0)
    }
}

/// con-leche: none — `largs.getLastD (.bvar 0)` over a `Vec<Expr>`
/// The major premise is the spine's last argument.
pub fn arg_get_last_d(args: &Vec<Expr>) -> Expr {
    if args.len() == 0 {
        expr::bvar(0)
    } else {
        expr::dup(&args[args.len() - 1])
    }
}

// ---------------------------------------------------------------------------
// `checkIotaSidesTy` (`Modeled.lean:30-53`)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/Inductives/Modeled.lean:31-53 checkIotaSidesTy
/// Certify that both sides of a modeled iota equation inhabit the equation's
/// type, and that the equation's type slot itself inhabits the sort the
/// statement's own `Eq.{ℓA}` names.  The slot-sort certification is a TT-lane
/// check — skipped unless `mode.ttChecks`.
pub fn check_iota_sides_ty(
    mode: &CheckMode,
    st: &mut CState,
    fe_self: &FEnv,
    depth: u64,
    alpha_s: &Expr,
    lhs_s: &Expr,
    rhs_s: &Expr,
    l_a: &Level,
) -> CheckM<()> {
    const M_LHS: [u32; 22] = [
        105, 111, 116, 97, 32, 115, 116, 97, 116, 101, 109, 101, 110, 116, 32, 108, 104, 115,
        32, 116, 121, 112,
    ];
    const M_RHS: [u32; 22] = [
        105, 111, 116, 97, 32, 115, 116, 97, 116, 101, 109, 101, 110, 116, 32, 114, 104, 115,
        32, 116, 121, 112,
    ];
    const M_SLOT: [u32; 27] = [
        105, 111, 116, 97, 32, 116, 121, 112, 101, 32, 115, 108, 111, 116, 32, 115, 111, 114,
        116, 32, 109, 105, 115, 109, 97, 116, 99,
    ];
    match core_c::infer(mode, core_k::check_fuel(), st, fe_self, depth, lhs_s) {
        Err(err) => Err(err),
        Ok(tl) => match core_c::defeq(
            mode,
            core_k::check_fuel(),
            st,
            fe_self,
            depth,
            &tl,
            alpha_s,
        ) {
            Err(err) => Err(err),
            Ok(false) => Err(core_types::not_implemented(core_types::code_points(&M_LHS))),
            Ok(true) => {
                match core_c::infer(mode, core_k::check_fuel(), st, fe_self, depth, rhs_s) {
                    Err(err) => Err(err),
                    Ok(tr) => match core_c::defeq(
                        mode,
                        core_k::check_fuel(),
                        st,
                        fe_self,
                        depth,
                        &tr,
                        alpha_s,
                    ) {
                        Err(err) => Err(err),
                        Ok(false) => {
                            Err(core_types::not_implemented(core_types::code_points(&M_RHS)))
                        }
                        Ok(true) => {
                            if !env::tt_checks(mode) {
                                Ok(())
                            } else {
                                match core_c::infer(
                                    mode,
                                    core_k::check_fuel(),
                                    st,
                                    fe_self,
                                    depth,
                                    alpha_s,
                                ) {
                                    Err(err) => Err(err),
                                    Ok(t_alpha) => {
                                        let s: Expr = expr::sort(level::dup(l_a));
                                        match core_c::defeq(
                                            mode,
                                            core_k::check_fuel(),
                                            st,
                                            fe_self,
                                            depth,
                                            &t_alpha,
                                            &s,
                                        ) {
                                            Err(err) => Err(err),
                                            Ok(true) => Ok(()),
                                            Ok(false) => {
                                                Err(core_types::not_implemented(
                                                    core_types::code_points(&M_SLOT),
                                                ))
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    },
                }
            }
        },
    }
}

// ---------------------------------------------------------------------------
// `checkIotaThm` (`Modeled.lean:55-165` / `DeclCheck.lean:507-575`)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/Inductives/Modeled.lean:55-149 checkIotaThm
/// con-leche: ConLeche/Kernel/DeclCheck.lean:507-573 checkIotaThmF
/// The **statement's opened head data**: the model's iota theorem looked up,
/// its level parameters pinned, its telescope opened at `rP + cnF` variables,
/// and its body read as an equation at one level.  Shared by `checkIotaThm`
/// and `checkIotaThmN`, which spell it identically.
pub fn iota_stmt_open(
    fe2: &FEnv,
    cv_name: &Name,
    lps: &Vec<Name>,
    r_p: u64,
    cn_f: u64,
    j: u64,
) -> CheckM<(Vec<Expr>, Vec<Expr>, Level)> {
    const M_MISS: [u32; 25] = [
        109, 105, 115, 115, 105, 110, 103, 32, 105, 111, 116, 97, 32, 116, 104, 101, 111, 114,
        101, 109, 32, 102, 111, 114, 32,
    ];
    const M_LPS: [u32; 27] = [
        105, 111, 116, 97, 32, 116, 104, 101, 111, 114, 101, 109, 32, 108, 101, 118, 101, 108,
        32, 109, 105, 115, 109, 97, 116, 99, 104,
    ];
    const M_SHAPE: [u32; 30] = [
        105, 111, 116, 97, 32, 115, 116, 97, 116, 101, 109, 101, 110, 116, 32, 115, 104, 97,
        112, 101, 32, 109, 105, 115, 109, 97, 116, 99, 104, 32,
    ];
    const M_EQ: [u32; 28] = [
        105, 111, 116, 97, 32, 115, 116, 97, 116, 101, 109, 101, 110, 116, 32, 110, 111, 116,
        32, 97, 110, 32, 101, 113, 110, 32, 32, 32,
    ];
    match checker_base::find_cv(fe2, &iota_thm_name(cv_name, j)) {
        None => Err(core_types::not_implemented(core_types::code_points(&M_MISS))),
        Some(cvt) => {
            if !prop_when::names_beq(&cvt.level_params, lps) {
                Err(core_types::not_implemented(core_types::code_points(&M_LPS)))
            } else {
                match checker_base::open_pis_at_fvars_f(r_p + cn_f, &cvt.ty, 0) {
                    None => Err(core_types::not_implemented(core_types::code_points(
                        &M_SHAPE,
                    ))),
                    Some(q) => {
                        let head: Expr = expr_ops::get_app_fn(&q.1);
                        let targs: Vec<Expr> = expr_ops::get_app_args(&q.1);
                        if !checker_base::is_eq_head(&head) {
                            Err(core_types::not_implemented(core_types::code_points(&M_EQ)))
                        } else if targs.len() != 3 {
                            Err(core_types::not_implemented(core_types::code_points(&M_EQ)))
                        } else {
                            Ok((q.0, targs, checker_base::eq_head_level(&head)))
                        }
                    }
                }
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/Modeled.lean:55-149 checkIotaThm
/// con-leche: ConLeche/Kernel/DeclCheck.lean:507-573 checkIotaThmF
/// The left side's **head, arity and prefix** pins, shared by the plain and
/// the nested statement checks: the renamed recursor applied to the opened
/// prefix variables, `mI + 1` arguments in all.
pub fn iota_lhs_prefix_ok(
    f: &BlockRename,
    cv_name: &Name,
    lps: &Vec<Name>,
    m_i: u64,
    r_p: u64,
    fvs: &Vec<Expr>,
    lhs_s: &Expr,
    largs: &Vec<Expr>,
) -> bool {
    let head: Expr = expr_ops::get_app_fn(lhs_s);
    let expected: Expr =
        expr::mk_const(f.rename(cv_name), struct_parts::params_of(lps));
    if !expr::beq(&head, &expected) {
        false
    } else if largs.len() as u64 != m_i + 1 {
        false
    } else {
        expr::exprs_beq(
            &expr_ops::take_exprs(largs, r_p as usize),
            &expr_ops::take_exprs(fvs, r_p as usize),
        )
    }
}

/// con-leche: ConLeche/Kernel/Inductives/Modeled.lean:55-149 checkIotaThm
/// con-leche: ConLeche/Kernel/DeclCheck.lean:507-573 checkIotaThmF
/// Check a *canonical* recursor rule's `iota_j` theorem, **semantically**: the
/// stored theorem's telescope is opened at free variables, its body must be an
/// `Eq`, the equation's left side is structurally the renamed recursor applied
/// to the opened variables and a canonical major, and the right side is
/// definitionally the rule's applied right-hand side.
pub fn check_iota_thm(
    mode: &CheckMode,
    st: &mut CState,
    fe2: &FEnv,
    fe_self: &FEnv,
    f: &BlockRename,
    cv_name: &Name,
    lps: &Vec<Name>,
    ty_a: &Expr,
    m_i: u64,
    r_p: u64,
    j: u64,
    r: &RecRule,
    cvj: &ConstantVal,
    cn_p: u64,
    cn_f: u64,
    rhs_a: &Expr,
) -> CheckM<()> {
    const M_HEAD: [u32; 28] = [
        105, 111, 116, 97, 32, 115, 116, 97, 116, 101, 109, 101, 110, 116, 32, 104, 101, 97,
        100, 32, 109, 105, 115, 109, 97, 116, 99, 104,
    ];
    const M_MAJ: [u32; 29] = [
        105, 111, 116, 97, 32, 115, 116, 97, 116, 101, 109, 101, 110, 116, 32, 109, 97, 106,
        111, 114, 32, 109, 105, 115, 109, 97, 116, 99, 104,
    ];
    match iota_stmt_open(fe2, cv_name, lps, r_p, cn_f, j) {
        Err(err) => Err(err),
        Ok(oq) => {
            let fvs: Vec<Expr> = oq.0;
            let targs: Vec<Expr> = oq.1;
            let l_a: Level = oq.2;
            let lhs_s: Expr = arg_get_d(&targs, 1);
            let rhs_s: Expr = arg_get_d(&targs, 2);
            let x_fvs: Vec<Expr> = core_k::drop_exprs(&fvs, r_p as usize);
            let largs: Vec<Expr> = expr_ops::get_app_args(&lhs_s);
            if !iota_lhs_prefix_ok(f, cv_name, lps, m_i, r_p, &fvs, &lhs_s, &largs) {
                Err(core_types::not_implemented(core_types::code_points(&M_HEAD)))
            } else {
                let major: Expr = arg_get_last_d(&largs);
                let spine: Vec<Expr> = core_k::append_exprs(
                    expr_ops::take_exprs(&fvs, cn_p as usize),
                    &x_fvs,
                );
                let expected_major: Expr = expr_ops::mk_app_n(
                    expr::mk_const(
                        f.rename(&r.ctor),
                        struct_parts::params_of(&cvj.level_params),
                    ),
                    &spine,
                );
                if !expr::beq(&major, &expected_major) {
                    Err(core_types::not_implemented(core_types::code_points(&M_MAJ)))
                } else {
                    check_iota_thm_ctor(
                        mode, st, fe_self, f, ty_a, m_i, r_p, cvj, cn_p, cn_f, rhs_a,
                        &fvs, &x_fvs, &largs, &targs, &lhs_s, &rhs_s, &l_a,
                    )
                }
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/Modeled.lean:55-149 checkIotaThm
/// con-leche: ConLeche/Kernel/DeclCheck.lean:507-573 checkIotaThmF
/// The constructor-telescope half of `checkIotaThm`: the constructor's
/// telescope (renamed), instantiated at the major's arguments, gives the field
/// domains and the canonical index tuple, both compared definitionally; then
/// the statement's prefix domains against the recursor's (renamed).
pub fn check_iota_thm_ctor(
    mode: &CheckMode,
    st: &mut CState,
    fe_self: &FEnv,
    f: &BlockRename,
    ty_a: &Expr,
    m_i: u64,
    r_p: u64,
    cvj: &ConstantVal,
    cn_p: u64,
    cn_f: u64,
    rhs_a: &Expr,
    fvs: &Vec<Expr>,
    x_fvs: &Vec<Expr>,
    largs: &Vec<Expr>,
    targs: &Vec<Expr>,
    lhs_s: &Expr,
    rhs_s: &Expr,
    l_a: &Level,
) -> CheckM<()> {
    const M_CTELE: [u32; 26] = [
        105, 111, 116, 97, 32, 99, 111, 110, 115, 116, 114, 117, 99, 116, 111, 114, 32, 116,
        101, 108, 101, 115, 99, 111, 112, 101,
    ];
    const M_CIDX: [u32; 23] = [
        105, 111, 116, 97, 32, 99, 111, 110, 115, 116, 114, 117, 99, 116, 111, 114, 32, 105,
        110, 100, 105, 99, 101,
    ];
    const M_RTELE: [u32; 23] = [
        105, 111, 116, 97, 32, 114, 101, 99, 117, 114, 115, 111, 114, 32, 116, 101, 108, 101,
        115, 99, 111, 112, 101,
    ];
    if expr_ops::strip_pis(cn_p + cn_f, &cvj.ty).is_none() {
        Err(core_types::not_implemented(core_types::code_points(&M_CTELE)))
    } else {
        let spine: Vec<Expr> =
            core_k::append_exprs(expr_ops::take_exprs(fvs, cn_p as usize), x_fvs);
        let renamed: Expr = expr_ops::rename_consts(f, &cvj.ty);
        match expr_ops::inst_pis_at(&spine, &renamed) {
            None => Err(core_types::not_implemented(core_types::code_points(&M_CTELE))),
            Some(cq) => {
                let cres_args: Vec<Expr> = expr_ops::get_app_args(&cq.1);
                if cres_args.len() as u64 != cn_p + expr_ops::sub_nat(m_i, r_p) {
                    Err(core_types::not_implemented(core_types::code_points(&M_CIDX)))
                } else {
                    let stmt_idx: Vec<Expr> = expr_ops::take_exprs(
                        &core_k::drop_exprs(largs, r_p as usize),
                        expr_ops::sub_nat(m_i, r_p) as usize,
                    );
                    let ctor_idx: Vec<Expr> =
                        core_k::drop_exprs(&cres_args, cn_p as usize);
                    match checker_base::check_def_eq_list(
                        mode,
                        st,
                        fe_self,
                        r_p + cn_f,
                        &stmt_idx,
                        &ctor_idx,
                    ) {
                        Err(err) => Err(err),
                        Ok(()) => {
                            let x_doms: Vec<Expr> = checker_base::fvar_types(x_fvs);
                            let c_doms: Vec<Expr> =
                                core_k::drop_exprs(&cq.0, cn_p as usize);
                            match checker_base::check_def_eq_list(
                                mode,
                                st,
                                fe_self,
                                r_p + cn_f,
                                &x_doms,
                                &c_doms,
                            ) {
                                Err(err) => Err(err),
                                Ok(()) => {
                                    let ty_renamed: Expr =
                                        expr_ops::rename_consts(f, ty_a);
                                    let prefix: Vec<Expr> =
                                        expr_ops::take_exprs(fvs, r_p as usize);
                                    match expr_ops::inst_pis_at(&prefix, &ty_renamed) {
                                        None => Err(core_types::not_implemented(
                                            core_types::code_points(&M_RTELE),
                                        )),
                                        Some(rq) => {
                                            let p_doms: Vec<Expr> =
                                                checker_base::fvar_types(&prefix);
                                            match checker_base::check_def_eq_list(
                                                mode,
                                                st,
                                                fe_self,
                                                r_p + cn_f,
                                                &p_doms,
                                                &rq.0,
                                            ) {
                                                Err(err) => Err(err),
                                                Ok(()) => check_iota_thm_frames(
                                                    mode, st, fe_self, f, ty_a, r_p, cvj,
                                                    cn_p, cn_f, rhs_a, fvs, targs, lhs_s,
                                                    rhs_s, l_a,
                                                ),
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/Modeled.lean:55-149 checkIotaThm
/// con-leche: ConLeche/Kernel/DeclCheck.lean:507-573 checkIotaThmF
/// The public-frame half of `checkIotaThm`: the rule's λ-domains are the
/// public recursor prefix and constructor field domains (the fold fact's
/// value spines fit the public telescopes; these equalities let them fit the
/// λs), then the right side is definitionally the rule's applied rhs and both
/// sides inhabit the equation's type slot.
pub fn check_iota_thm_frames(
    mode: &CheckMode,
    st: &mut CState,
    fe_self: &FEnv,
    f: &BlockRename,
    ty_a: &Expr,
    r_p: u64,
    cvj: &ConstantVal,
    cn_p: u64,
    cn_f: u64,
    rhs_a: &Expr,
    fvs: &Vec<Expr>,
    targs: &Vec<Expr>,
    lhs_s: &Expr,
    rhs_s: &Expr,
    l_a: &Level,
) -> CheckM<()> {
    const M_RTELE: [u32; 23] = [
        105, 111, 116, 97, 32, 114, 101, 99, 117, 114, 115, 111, 114, 32, 116, 101, 108, 101,
        115, 99, 111, 112, 101,
    ];
    const M_CTELE: [u32; 26] = [
        105, 111, 116, 97, 32, 99, 111, 110, 115, 116, 114, 117, 99, 116, 111, 114, 32, 116,
        101, 108, 101, 115, 99, 111, 112, 101,
    ];
    const M_RULE: [u32; 19] = [
        114, 117, 108, 101, 32, 115, 104, 97, 112, 101, 32, 109, 105, 115, 109, 97, 116, 99,
        104,
    ];
    const M_MIS: [u32; 24] = [
        105, 111, 116, 97, 32, 115, 116, 97, 116, 101, 109, 101, 110, 116, 32, 109, 105, 115,
        109, 97, 116, 99, 104, 32,
    ];
    match checker_base::open_pis_at_fvars_f(r_p, ty_a, 0) {
        None => Err(core_types::not_implemented(core_types::code_points(&M_RTELE))),
        Some(pq) => {
            let p_head: Vec<Expr> = expr_ops::take_exprs(&pq.0, cn_p as usize);
            match expr_ops::inst_pis_at(&p_head, &cvj.ty) {
                None => Err(core_types::not_implemented(core_types::code_points(&M_CTELE))),
                Some(cq) => {
                    let p_doms: Vec<Expr> = checker_base::fvar_types(&p_head);
                    match checker_base::check_def_eq_list(
                        mode,
                        st,
                        fe_self,
                        r_p + cn_f,
                        &p_doms,
                        &cq.0,
                    ) {
                        Err(err) => Err(err),
                        Ok(()) => match checker_base::open_pis_at_fvars_f(cn_f, &cq.1, r_p) {
                            None => Err(core_types::not_implemented(
                                core_types::code_points(&M_CTELE),
                            )),
                            Some(xq) => {
                                let frame: Vec<Expr> =
                                    core_k::append_exprs(env::exprs_copy(&pq.0), &xq.0);
                                match expr_ops::inst_lams_at(&frame, rhs_a) {
                                    None => Err(core_types::not_implemented(
                                        core_types::code_points(&M_RULE),
                                    )),
                                    Some(lq) => {
                                        let f_doms: Vec<Expr> =
                                            checker_base::fvar_types(&frame);
                                        match checker_base::check_def_eq_list(
                                            mode,
                                            st,
                                            fe_self,
                                            r_p + cn_f,
                                            &f_doms,
                                            &lq.0,
                                        ) {
                                            Err(err) => Err(err),
                                            Ok(()) => {
                                                let applied: Expr = expr_ops::mk_app_n(
                                                    expr_ops::rename_consts(f, rhs_a),
                                                    fvs,
                                                );
                                                match core_c::defeq(
                                                    mode,
                                                    core_k::check_fuel(),
                                                    st,
                                                    fe_self,
                                                    r_p + cn_f,
                                                    rhs_s,
                                                    &applied,
                                                ) {
                                                    Err(err) => Err(err),
                                                    Ok(false) => {
                                                        Err(core_types::not_implemented(
                                                            core_types::code_points(&M_MIS),
                                                        ))
                                                    }
                                                    Ok(true) => {
                                                        let alpha: Expr =
                                                            arg_get_d(targs, 0);
                                                        check_iota_sides_ty(
                                                            mode,
                                                            st,
                                                            fe_self,
                                                            r_p + cn_f,
                                                            &alpha,
                                                            lhs_s,
                                                            rhs_s,
                                                            l_a,
                                                        )
                                                    }
                                                }
                                            }
                                        }
                                    }
                                }
                            }
                        },
                    }
                }
            }
        }
    }
}

// ---------------------------------------------------------------------------
// The nested-auxiliary rule shape (`Modeled.lean:167-206` /
// `DeclCheck.lean:576-601`)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/Inductives/Modeled.lean:151-190 nestedRuleShape
/// con-leche: ConLeche/Kernel/DeclCheck.lean:575-599 nestedRuleShapeF
/// `(args.take cnP).map (Expr.lowerBVars k 0)`: the parameter instantiations
/// lowered into the rule-prefix context.
pub fn lower_all(k: u64, args: &Vec<Expr>, cn_p: usize, i: usize, out: Vec<Expr>) -> Vec<Expr> {
    if i >= cn_p {
        out
    } else if i >= args.len() {
        out
    } else {
        let mut out = out;
        out.push(expr_ops::lower_bvars(k, 0, &args[i]));
        lower_all(k, args, cn_p, i + 1, out)
    }
}

/// con-leche: ConLeche/Kernel/Inductives/Modeled.lean:151-190 nestedRuleShape
/// `pins.map (Expr.liftLooseBVars k 0)`: the lift-back roundtrip that
/// certifies that no index variable occurs in a pin.
pub fn lift_all_0(k: u64, pins: &Vec<Expr>, i: usize, out: Vec<Expr>) -> Vec<Expr> {
    if i >= pins.len() {
        out
    } else {
        let mut out = out;
        out.push(expr_ops::lift_loose_bvars(k, 0, &pins[i]));
        lift_all_0(k, pins, i + 1, out)
    }
}

/// con-leche: ConLeche/Kernel/Inductives/Modeled.lean:151-190 nestedRuleShape
/// `pins.all (fun p => !p.hasFvar && p.looseBVarsBounded rP && p.constsResolve
/// envSelf && p.allLevelParamsDefined lps)` — the syntactic well-formedness
/// `EnvWF` records for the stored rule.
pub fn pins_wf_from(
    fe_self: &FEnv,
    lps: &Vec<Name>,
    r_p: u64,
    pins: &Vec<Expr>,
    i: usize,
) -> bool {
    if i >= pins.len() {
        true
    } else if expr_ops::has_fvar(&pins[i]) {
        false
    } else if !expr_ops::loose_bvars_bounded(r_p, &pins[i]) {
        false
    } else if !decl_check::consts_resolve_f_fast(fe_self, &pins[i]) {
        false
    } else if !expr_ops::all_level_params_defined_fast(lps, &pins[i]) {
        false
    } else {
        pins_wf_from(fe_self, lps, r_p, pins, i + 1)
    }
}

/// con-leche: ConLeche/Kernel/Inductives/Modeled.lean:151-190 nestedRuleShape
/// con-leche: ConLeche/Kernel/DeclCheck.lean:575-599 nestedRuleShapeF
/// The nested-shape data of a non-canonical rule: the constructor's level and
/// parameter instantiations, read off the recursor type's major-premise
/// domain.  `none` — the rule stays inert, and a matched major declines at
/// fire time — when the model stores no `iota_j`, the prefix exceeds the
/// major's position, the major domain is not a constant-headed application of
/// exactly `cnP + k` arguments of this split shape, or an instantiation fails
/// the syntactic guards.
pub fn nested_rule_shape(
    fe2: &FEnv,
    fe_self: &FEnv,
    cv_name: &Name,
    lps: &Vec<Name>,
    ty_a: &Expr,
    m_i: u64,
    r_p: u64,
    cn_p: u64,
    j: u64,
) -> Option<(Vec<Level>, Vec<Expr>)> {
    let gate = if fenv::find(fe2, &iota_thm_name(cv_name, j)).is_some() {
        r_p <= m_i
    } else {
        false
    };
    if !gate {
        None
    } else {
        match expr_ops::strip_pis(m_i, ty_a) {
            None => None,
            Some(tq) => match &tq.1 .0.kind {
                ExprKind::ForallE(dom, _, _) => {
                    let head: Expr = expr_ops::get_app_fn(dom);
                    match &head.0.kind {
                        ExprKind::Const(_, lvls) => {
                            let args: Vec<Expr> = expr_ops::get_app_args(dom);
                            let k: u64 = m_i - r_p;
                            let pins: Vec<Expr> =
                                lower_all(k, &args, cn_p as usize, 0, Vec::new());
                            if args.len() as u64 != cn_p + k {
                                None
                            } else if !expr::exprs_beq(
                                &expr_ops::take_exprs(&args, cn_p as usize),
                                &lift_all_0(k, &pins, 0, Vec::new()),
                            ) {
                                None
                            } else if !expr::exprs_beq(
                                &core_k::drop_exprs(&args, cn_p as usize),
                                &struct_parts::field_spine(k),
                            ) {
                                None
                            } else if !pins_wf_from(fe_self, lps, r_p, &pins, 0) {
                                None
                            } else if !expr_ops::levels_all_params_defined(lps, lvls, 0) {
                                None
                            } else {
                                Some((env::levels_copy(lvls), pins))
                            }
                        }
                        _ => None,
                    }
                }
                _ => None,
            },
        }
    }
}

// ---------------------------------------------------------------------------
// `checkIotaThmN` (`Modeled.lean:208-323` / `DeclCheck.lean:602-687`)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/Inductives/Modeled.lean:192-317 checkIotaThmN
/// con-leche: ConLeche/Kernel/DeclCheck.lean:601-685 checkIotaThmNF
/// `pins.map fun p => Expr.instSpine (fvs.take rP) (rP - 1) (p.renameConsts f)`
/// — the stored pins opened at the statement's prefix variables (renamed, or
/// not, per `ren`).
pub fn inst_pins_renamed(
    pins: &Vec<Expr>,
    prefix: &Vec<Expr>,
    r_p: u64,
    f: &BlockRename,
    i: usize,
    out: Vec<Expr>,
) -> Vec<Expr> {
    if i >= pins.len() {
        out
    } else {
        let p: Expr = expr_ops::rename_consts(f, &pins[i]);
        let mut out = out;
        out.push(expr_ops::inst_spine(
            prefix,
            expr_ops::sub_nat(r_p, 1),
            &p,
        ));
        inst_pins_renamed(pins, prefix, r_p, f, i + 1, out)
    }
}

/// con-leche: ConLeche/Kernel/Inductives/Modeled.lean:192-317 checkIotaThmN
/// con-leche: ConLeche/Kernel/DeclCheck.lean:601-685 checkIotaThmNF
/// `pins.map fun p => Expr.instSpine (fvsP.take rP) (rP - 1) p` — the *public*
/// spelling, without the block renaming.
///
/// Deviation: con-leche writes one `map` whose function either renames or does
/// not; the port has two functions, because a single one would take the
/// renaming as `Option<&BlockRename>` and Aeneas rejects a nested borrow
/// (*"Nested borrows are not supported yet"*).
pub fn inst_pins_plain(
    pins: &Vec<Expr>,
    prefix: &Vec<Expr>,
    r_p: u64,
    i: usize,
    out: Vec<Expr>,
) -> Vec<Expr> {
    if i >= pins.len() {
        out
    } else {
        let mut out = out;
        out.push(expr_ops::inst_spine(
            prefix,
            expr_ops::sub_nat(r_p, 1),
            &pins[i],
        ));
        inst_pins_plain(pins, prefix, r_p, i + 1, out)
    }
}

/// con-leche: ConLeche/Kernel/Inductives/Modeled.lean:192-317 checkIotaThmN
/// con-leche: ConLeche/Kernel/DeclCheck.lean:601-685 checkIotaThmNF
/// Check a *nested-auxiliary* recursor rule's `iota_j` theorem — the
/// generalization of `checkIotaThm` to rules whose constructor parameters and
/// levels are fixed instantiations (`nestedRuleShape`).  When the rule has no
/// certifiable shape it is stored inert (`.inert`; a matched major positively
/// declines at fire time); a shape whose theorem then fails the pin is a
/// positive decline here.
pub fn check_iota_thm_n(
    mode: &CheckMode,
    st: &mut CState,
    fe2: &FEnv,
    fe_self: &FEnv,
    f: &BlockRename,
    cv_name: &Name,
    lps: &Vec<Name>,
    ty_a: &Expr,
    m_i: u64,
    r_p: u64,
    j: u64,
    r: &RecRule,
    cvj: &ConstantVal,
    cn_p: u64,
    cn_f: u64,
    rhs_a: &Expr,
) -> CheckM<RecRuleFire> {
    const M_HEAD: [u32; 28] = [
        105, 111, 116, 97, 32, 115, 116, 97, 116, 101, 109, 101, 110, 116, 32, 104, 101, 97,
        100, 32, 109, 105, 115, 109, 97, 116, 99, 104,
    ];
    const M_MAJ: [u32; 29] = [
        105, 111, 116, 97, 32, 115, 116, 97, 116, 101, 109, 101, 110, 116, 32, 109, 97, 106,
        111, 114, 32, 109, 105, 115, 109, 97, 116, 99, 104,
    ];
    const M_CTELE: [u32; 26] = [
        105, 111, 116, 97, 32, 99, 111, 110, 115, 116, 114, 117, 99, 116, 111, 114, 32, 116,
        101, 108, 101, 115, 99, 111, 112, 101,
    ];
    const M_RHEAD: [u32; 31] = [
        105, 111, 116, 97, 32, 99, 111, 110, 115, 116, 114, 117, 99, 116, 111, 114, 32, 114,
        101, 115, 105, 100, 117, 97, 108, 32, 104, 101, 97, 100, 32,
    ];
    match nested_rule_shape(fe2, fe_self, cv_name, lps, ty_a, m_i, r_p, cn_p, j) {
        None => Ok(RecRuleFire::Inert),
        Some(sq) => {
            let lvls: Vec<Level> = sq.0;
            let pins: Vec<Expr> = sq.1;
            match iota_stmt_open(fe2, cv_name, lps, r_p, cn_f, j) {
                Err(err) => Err(err),
                Ok(oq) => {
                    let fvs: Vec<Expr> = oq.0;
                    let targs: Vec<Expr> = oq.1;
                    let l_a: Level = oq.2;
                    let lhs_s: Expr = arg_get_d(&targs, 1);
                    let rhs_s: Expr = arg_get_d(&targs, 2);
                    let x_fvs: Vec<Expr> = core_k::drop_exprs(&fvs, r_p as usize);
                    let prefix: Vec<Expr> = expr_ops::take_exprs(&fvs, r_p as usize);
                    let pins_f: Vec<Expr> =
                        inst_pins_renamed(&pins, &prefix, r_p, f, 0, Vec::new());
                    let largs: Vec<Expr> = expr_ops::get_app_args(&lhs_s);
                    if !iota_lhs_prefix_ok(f, cv_name, lps, m_i, r_p, &fvs, &lhs_s, &largs)
                    {
                        Err(core_types::not_implemented(core_types::code_points(&M_HEAD)))
                    } else {
                        let major: Expr = arg_get_last_d(&largs);
                        let spine: Vec<Expr> =
                            core_k::append_exprs(env::exprs_copy(&pins_f), &x_fvs);
                        let expected_major: Expr = expr_ops::mk_app_n(
                            expr::mk_const(f.rename(&r.ctor), env::levels_copy(&lvls)),
                            &spine,
                        );
                        if !expr::beq(&major, &expected_major) {
                            Err(core_types::not_implemented(core_types::code_points(
                                &M_MAJ,
                            )))
                        } else {
                            match expr_ops::strip_pis(cn_p + cn_f, &cvj.ty) {
                                None => Err(core_types::not_implemented(
                                    core_types::code_points(&M_CTELE),
                                )),
                                Some(bq) => {
                                    let rhead: Expr = expr_ops::get_app_fn(&bq.1);
                                    match &rhead.0.kind {
                                        ExprKind::Const(_, _) => {
                                            match check_iota_thm_n_ctor(
                                                mode, st, fe_self, f, ty_a, m_i, r_p, cvj,
                                                cn_p, cn_f, rhs_a, &fvs, &x_fvs, &largs,
                                                &targs, &lhs_s, &rhs_s, &l_a, &lvls,
                                                &pins, &pins_f,
                                            ) {
                                                Err(err) => Err(err),
                                                Ok(()) => {
                                                    Ok(RecRuleFire::Nested(lvls, pins))
                                                }
                                            }
                                        }
                                        _ => Err(core_types::not_implemented(
                                            core_types::code_points(&M_RHEAD),
                                        )),
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/Modeled.lean:192-317 checkIotaThmN
/// con-leche: ConLeche/Kernel/DeclCheck.lean:601-685 checkIotaThmNF
/// The constructor-telescope half of `checkIotaThmN`: the constructor's
/// telescope at the stored level instantiations (renamed), instantiated at
/// the major's arguments, then the statement's prefix domains against the
/// recursor's.
pub fn check_iota_thm_n_ctor(
    mode: &CheckMode,
    st: &mut CState,
    fe_self: &FEnv,
    f: &BlockRename,
    ty_a: &Expr,
    m_i: u64,
    r_p: u64,
    cvj: &ConstantVal,
    cn_p: u64,
    cn_f: u64,
    rhs_a: &Expr,
    fvs: &Vec<Expr>,
    x_fvs: &Vec<Expr>,
    largs: &Vec<Expr>,
    targs: &Vec<Expr>,
    lhs_s: &Expr,
    rhs_s: &Expr,
    l_a: &Level,
    lvls: &Vec<Level>,
    pins: &Vec<Expr>,
    pins_f: &Vec<Expr>,
) -> CheckM<()> {
    const M_CTELE: [u32; 26] = [
        105, 111, 116, 97, 32, 99, 111, 110, 115, 116, 114, 117, 99, 116, 111, 114, 32, 116,
        101, 108, 101, 115, 99, 111, 112, 101,
    ];
    const M_CIDX: [u32; 23] = [
        105, 111, 116, 97, 32, 99, 111, 110, 115, 116, 114, 117, 99, 116, 111, 114, 32, 105,
        110, 100, 105, 99, 101,
    ];
    const M_RTELE: [u32; 23] = [
        105, 111, 116, 97, 32, 114, 101, 99, 117, 114, 115, 111, 114, 32, 116, 101, 108, 101,
        115, 99, 111, 112, 101,
    ];
    let inst_ty: Expr =
        expr_ops::instantiate_level_params(&cvj.level_params, lvls, &cvj.ty);
    let renamed: Expr = expr_ops::rename_consts(f, &inst_ty);
    let spine: Vec<Expr> = core_k::append_exprs(env::exprs_copy(pins_f), x_fvs);
    match expr_ops::inst_pis_at(&spine, &renamed) {
        None => Err(core_types::not_implemented(core_types::code_points(&M_CTELE))),
        Some(cq) => {
            let cres_args: Vec<Expr> = expr_ops::get_app_args(&cq.1);
            if cres_args.len() as u64 != cn_p + expr_ops::sub_nat(m_i, r_p) {
                Err(core_types::not_implemented(core_types::code_points(&M_CIDX)))
            } else {
                let stmt_idx: Vec<Expr> = expr_ops::take_exprs(
                    &core_k::drop_exprs(largs, r_p as usize),
                    expr_ops::sub_nat(m_i, r_p) as usize,
                );
                let ctor_idx: Vec<Expr> = core_k::drop_exprs(&cres_args, cn_p as usize);
                match checker_base::check_def_eq_list(
                    mode,
                    st,
                    fe_self,
                    r_p + cn_f,
                    &stmt_idx,
                    &ctor_idx,
                ) {
                    Err(err) => Err(err),
                    Ok(()) => {
                        let x_doms: Vec<Expr> = checker_base::fvar_types(x_fvs);
                        let c_doms: Vec<Expr> = core_k::drop_exprs(&cq.0, cn_p as usize);
                        match checker_base::check_def_eq_list(
                            mode,
                            st,
                            fe_self,
                            r_p + cn_f,
                            &x_doms,
                            &c_doms,
                        ) {
                            Err(err) => Err(err),
                            Ok(()) => {
                                let ty_renamed: Expr = expr_ops::rename_consts(f, ty_a);
                                let prefix: Vec<Expr> =
                                    expr_ops::take_exprs(fvs, r_p as usize);
                                match expr_ops::inst_pis_at(&prefix, &ty_renamed) {
                                    None => Err(core_types::not_implemented(
                                        core_types::code_points(&M_RTELE),
                                    )),
                                    Some(rq) => {
                                        let p_doms: Vec<Expr> =
                                            checker_base::fvar_types(&prefix);
                                        match checker_base::check_def_eq_list(
                                            mode,
                                            st,
                                            fe_self,
                                            r_p + cn_f,
                                            &p_doms,
                                            &rq.0,
                                        ) {
                                            Err(err) => Err(err),
                                            Ok(()) => check_iota_thm_n_frames(
                                                mode, st, fe_self, f, ty_a, r_p, cvj, cn_p,
                                                cn_f, rhs_a, fvs, targs, lhs_s, rhs_s, l_a,
                                                lvls, pins, m_i,
                                            ),
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/Modeled.lean:192-317 checkIotaThmN
/// con-leche: ConLeche/Kernel/DeclCheck.lean:601-685 checkIotaThmNF
/// The public-frame half of `checkIotaThmN`: the instantiated pins are fixed
/// points of the annotation pass and inhabit the constructor's parameter
/// domains, the auxiliary constructor's residual applies the family to its
/// parameters and the canonical index tuple, and the rule's λ-domains fit.
pub fn check_iota_thm_n_frames(
    mode: &CheckMode,
    st: &mut CState,
    fe_self: &FEnv,
    f: &BlockRename,
    ty_a: &Expr,
    r_p: u64,
    cvj: &ConstantVal,
    cn_p: u64,
    cn_f: u64,
    rhs_a: &Expr,
    fvs: &Vec<Expr>,
    targs: &Vec<Expr>,
    lhs_s: &Expr,
    rhs_s: &Expr,
    l_a: &Level,
    lvls: &Vec<Level>,
    pins: &Vec<Expr>,
    m_i: u64,
) -> CheckM<()> {
    const M_RTELE: [u32; 23] = [
        105, 111, 116, 97, 32, 114, 101, 99, 117, 114, 115, 111, 114, 32, 116, 101, 108, 101,
        115, 99, 111, 112, 101,
    ];
    const M_CTELE: [u32; 26] = [
        105, 111, 116, 97, 32, 99, 111, 110, 115, 116, 114, 117, 99, 116, 111, 114, 32, 116,
        101, 108, 101, 115, 99, 111, 112, 101,
    ];
    const M_ARITY: [u32; 23] = [
        105, 111, 116, 97, 32, 99, 111, 110, 115, 116, 114, 117, 99, 116, 111, 114, 32, 97,
        114, 105, 116, 121, 32,
    ];
    const M_RULE: [u32; 19] = [
        114, 117, 108, 101, 32, 115, 104, 97, 112, 101, 32, 109, 105, 115, 109, 97, 116, 99,
        104,
    ];
    const M_MIS: [u32; 24] = [
        105, 111, 116, 97, 32, 115, 116, 97, 116, 101, 109, 101, 110, 116, 32, 109, 105, 115,
        109, 97, 116, 99, 104, 32,
    ];
    match checker_base::open_pis_at_fvars_f(r_p, ty_a, 0) {
        None => Err(core_types::not_implemented(core_types::code_points(&M_RTELE))),
        Some(pq) => {
            let prefix_p: Vec<Expr> = expr_ops::take_exprs(&pq.0, r_p as usize);
            let pins_p: Vec<Expr> = inst_pins_plain(pins, &prefix_p, r_p, 0, Vec::new());
            match checker_base::check_annot_list(mode, st, fe_self, r_p + cn_f, &pins_p) {
                Err(err) => Err(err),
                Ok(()) => {
                    let inst_ty: Expr = expr_ops::instantiate_level_params(
                        &cvj.level_params,
                        lvls,
                        &cvj.ty,
                    );
                    match expr_ops::inst_pis_at(&pins_p, &inst_ty) {
                        None => Err(core_types::not_implemented(core_types::code_points(
                            &M_CTELE,
                        ))),
                        Some(cq) => {
                            match checker_base::check_typed_list(
                                mode,
                                st,
                                fe_self,
                                r_p + cn_f,
                                &pins_p,
                                &cq.0,
                            ) {
                                Err(err) => Err(err),
                                Ok(()) => {
                                    match checker_base::open_pis_at_fvars_f(
                                        cn_f, &cq.1, r_p,
                                    ) {
                                        None => Err(core_types::not_implemented(
                                            core_types::code_points(&M_CTELE),
                                        )),
                                        Some(xq) => {
                                            let resid: Vec<Expr> =
                                                expr_ops::get_app_args(&xq.1);
                                            if resid.len() as u64
                                                != cn_p + expr_ops::sub_nat(m_i, r_p)
                                            {
                                                Err(core_types::not_implemented(
                                                    core_types::code_points(&M_ARITY),
                                                ))
                                            } else {
                                                let frame: Vec<Expr> =
                                                    core_k::append_exprs(
                                                        env::exprs_copy(&pq.0),
                                                        &xq.0,
                                                    );
                                                match expr_ops::inst_lams_at(
                                                    &frame, rhs_a,
                                                ) {
                                                    None => {
                                                        Err(core_types::not_implemented(
                                                            core_types::code_points(
                                                                &M_RULE,
                                                            ),
                                                        ))
                                                    }
                                                    Some(lq) => {
                                                        let f_doms: Vec<Expr> =
                                                            checker_base::fvar_types(
                                                                &frame,
                                                            );
                                                        match checker_base::check_def_eq_list(
                                                            mode,
                                                            st,
                                                            fe_self,
                                                            r_p + cn_f,
                                                            &f_doms,
                                                            &lq.0,
                                                        ) {
                                                            Err(err) => Err(err),
                                                            Ok(()) => {
                                                                let applied: Expr =
                                                                    expr_ops::mk_app_n(
                                                                        expr_ops::rename_consts(
                                                                            f, rhs_a,
                                                                        ),
                                                                        fvs,
                                                                    );
                                                                match core_c::defeq(
                                                                    mode,
                                                                    core_k::check_fuel(),
                                                                    st,
                                                                    fe_self,
                                                                    r_p + cn_f,
                                                                    rhs_s,
                                                                    &applied,
                                                                ) {
                                                                    Err(err) => Err(err),
                                                                    Ok(false) => Err(
                                                                        core_types::not_implemented(
                                                                            core_types::code_points(
                                                                                &M_MIS,
                                                                            ),
                                                                        ),
                                                                    ),
                                                                    Ok(true) => {
                                                                        let alpha: Expr =
                                                                            arg_get_d(
                                                                                targs, 0,
                                                                            );
                                                                        check_iota_sides_ty(
                                                                            mode,
                                                                            st,
                                                                            fe_self,
                                                                            r_p + cn_f,
                                                                            &alpha,
                                                                            lhs_s,
                                                                            rhs_s,
                                                                            l_a,
                                                                        )
                                                                    }
                                                                }
                                                            }
                                                        }
                                                    }
                                                }
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
    }
}

// ---------------------------------------------------------------------------
// The per-rule check (`Modeled.lean:325-379` / `DeclCheck.lean:688-729`)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/Inductives/Modeled.lean:319-360 checkIotaRule
/// con-leche: ConLeche/Kernel/DeclCheck.lean:687-716 checkIotaRuleF
/// Check one modeled recursor rule: generic well-formedness of the right-hand
/// side, then the model's `iota_j` theorem — for canonical rules the plain
/// statement pin (`checkIotaThm`), for nested-auxiliary rules the generalized
/// pin over the stored instantiations (`checkIotaThmN`).  The firing mode is
/// computed once, here, and stored on the rule.
pub fn check_iota_rule(
    mode: &CheckMode,
    st: &mut CState,
    fe2: &FEnv,
    fe_self: &FEnv,
    f: &BlockRename,
    cv_name: &Name,
    lps: &Vec<Name>,
    ty_a: &Expr,
    m_i: u64,
    r_p: u64,
    j: u64,
    r: &RecRule,
) -> CheckM<RecRule> {
    const M_CTOR: [u32; 26] = [
        105, 111, 116, 97, 32, 114, 117, 108, 101, 32, 99, 111, 110, 115, 116, 114, 117, 99,
        116, 111, 114, 32, 32, 32, 32, 32,
    ];
    const M_NF: [u32; 26] = [
        114, 117, 108, 101, 32, 102, 105, 101, 108, 100, 32, 99, 111, 117, 110, 116, 32, 109,
        105, 115, 109, 97, 116, 99, 104, 32,
    ];
    const M_BVAR: [u32; 29] = [
        108, 111, 111, 115, 101, 32, 98, 111, 117, 110, 100, 32, 118, 97, 114, 105, 97, 98,
        108, 101, 32, 105, 110, 32, 114, 117, 108, 101, 32,
    ];
    const M_FVAR: [u32; 26] = [
        102, 114, 101, 101, 32, 118, 97, 114, 105, 97, 98, 108, 101, 32, 105, 110, 32, 114,
        117, 108, 101, 32, 32, 32, 32, 32,
    ];
    const M_LPS: [u32; 33] = [
        117, 110, 100, 101, 99, 108, 97, 114, 101, 100, 32, 117, 110, 105, 118, 101, 114,
        115, 101, 32, 112, 97, 114, 97, 109, 101, 116, 101, 114, 32, 32, 32, 32,
    ];
    const M_RESOLVE: [u32; 29] = [
        117, 110, 107, 110, 111, 119, 110, 32, 99, 111, 110, 115, 116, 97, 110, 116, 32, 105,
        110, 32, 114, 117, 108, 101, 32, 32, 32, 32, 32,
    ];
    const M_SHAPE: [u32; 19] = [
        114, 117, 108, 101, 32, 115, 104, 97, 112, 101, 32, 109, 105, 115, 109, 97, 116, 99,
        104,
    ];
    match core_k::ctor_probe(fe2, &r.ctor) {
        None => Err(core_types::invalid(core_types::code_points(&M_CTOR))),
        Some(cq) => {
            let cvj: ConstantVal = cq.0;
            let cn_p: u64 = cq.1;
            let cn_f: u64 = cq.2;
            if r.nfields != cn_f {
                Err(core_types::invalid(core_types::code_points(&M_NF)))
            } else if !expr_ops::loose_bvars_bounded(0, &r.rhs) {
                Err(core_types::invalid(core_types::code_points(&M_BVAR)))
            } else if expr_ops::has_fvar(&r.rhs) {
                Err(core_types::invalid(core_types::code_points(&M_FVAR)))
            } else {
                match core_c::annotate(mode, core_k::check_fuel(), st, fe_self, 0, &r.rhs) {
                    Err(err) => Err(err),
                    Ok(rhs_a) => {
                        if !expr_ops::all_level_params_defined_fast(lps, &rhs_a) {
                            Err(core_types::invalid(core_types::code_points(&M_LPS)))
                        } else if !decl_check::consts_resolve_f_fast(fe_self, &rhs_a) {
                            Err(core_types::invalid(core_types::code_points(&M_RESOLVE)))
                        } else if expr_ops::strip_lams(r_p + cn_f, &rhs_a).is_none() {
                            Err(core_types::not_implemented(core_types::code_points(
                                &M_SHAPE,
                            )))
                        } else {
                            match core_c::infer(
                                mode,
                                core_k::check_fuel(),
                                st,
                                fe_self,
                                0,
                                &rhs_a,
                            ) {
                                Err(err) => Err(err),
                                Ok(_rhs_ty) => check_iota_rule_fire(
                                    mode, st, fe2, fe_self, f, cv_name, lps, ty_a, m_i,
                                    r_p, j, r, &cvj, cn_p, cn_f, rhs_a,
                                ),
                            }
                        }
                    }
                }
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/Modeled.lean:319-360 checkIotaRule
/// con-leche: ConLeche/Kernel/DeclCheck.lean:687-716 checkIotaRuleF
/// The firing-mode decision and the stored rule, split off so the guard nest
/// above stays readable.  `iotaRec` reads the stored flag instead of
/// re-walking the recursor type on every fire.
pub fn check_iota_rule_fire(
    mode: &CheckMode,
    st: &mut CState,
    fe2: &FEnv,
    fe_self: &FEnv,
    f: &BlockRename,
    cv_name: &Name,
    lps: &Vec<Name>,
    ty_a: &Expr,
    m_i: u64,
    r_p: u64,
    j: u64,
    r: &RecRule,
    cvj: &ConstantVal,
    cn_p: u64,
    cn_f: u64,
    rhs_a: Expr,
) -> CheckM<RecRule> {
    if expr_ops::rec_rule_plain(ty_a, m_i, r_p, cn_p) {
        match check_iota_thm(
            mode, st, fe2, fe_self, f, cv_name, lps, ty_a, m_i, r_p, j, r, cvj, cn_p,
            cn_f, &rhs_a,
        ) {
            Err(err) => Err(err),
            Ok(()) => Ok(iota_rule_stored(
                fe2,
                cv_name,
                r,
                cn_p,
                RecRuleFire::Plain,
                rhs_a,
            )),
        }
    } else {
        match check_iota_thm_n(
            mode, st, fe2, fe_self, f, cv_name, lps, ty_a, m_i, r_p, j, r, cvj, cn_p,
            cn_f, &rhs_a,
        ) {
            Err(err) => Err(err),
            Ok(fr) => Ok(iota_rule_stored(fe2, cv_name, r, cn_p, fr, rhs_a)),
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/Modeled.lean:319-360 checkIotaRule
/// con-leche: ConLeche/Kernel/DeclCheck.lean:687-716 checkIotaRuleF
/// `recRuleBits env'.find? cvName { r with rhs := rhsA, ctorParams := cnP,
/// fire := fire, paramsBlind := false }` — the stored rule.  Its own function
/// because the two firing branches above must each *tail-call* it rather than
/// join on a `CheckM RecRuleFire` (task #18's rule: a gated certificate whose
/// arms rejoin on a shared result is split into two tail calls; Aeneas
/// answered with an internal error at the join).
pub fn iota_rule_stored(
    fe2: &FEnv,
    cv_name: &Name,
    r: &RecRule,
    cn_p: u64,
    fire: RecRuleFire,
    rhs_a: Expr,
) -> RecRule {
    let rl = RecRule {
        ctor: name::dup(&r.ctor),
        nfields: r.nfields,
        ctor_params: cn_p,
        fire,
        rhs: rhs_a,
        k: r.k,
        eta: r.eta,
        params_blind: false,
    };
    core_k::rec_rule_bits(fe2, cv_name, rl)
}

/// con-leche: ConLeche/Kernel/Inductives/Modeled.lean:362-371 checkIotaRules
/// con-leche: ConLeche/Kernel/DeclCheck.lean:718-727 checkIotaRulesF
/// The per-rule check, folded over a modeled recursor's rules.  Accumulated
/// on the way in (task #13's pattern 3).
pub fn check_iota_rules(
    mode: &CheckMode,
    st: &mut CState,
    fe2: &FEnv,
    fe_self: &FEnv,
    f: &BlockRename,
    cv_name: &Name,
    lps: &Vec<Name>,
    ty_a: &Expr,
    m_i: u64,
    r_p: u64,
    j: u64,
    rules: &Vec<RecRule>,
    i: usize,
    out: Vec<RecRule>,
) -> CheckM<Vec<RecRule>> {
    if i >= rules.len() {
        Ok(out)
    } else {
        match check_iota_rule(
            mode, st, fe2, fe_self, f, cv_name, lps, ty_a, m_i, r_p, j, &rules[i],
        ) {
            Err(err) => Err(err),
            Ok(r2) => {
                let mut out = out;
                out.push(r2);
                check_iota_rules(
                    mode,
                    st,
                    fe2,
                    fe_self,
                    f,
                    cv_name,
                    lps,
                    ty_a,
                    m_i,
                    r_p,
                    j + 1,
                    rules,
                    i + 1,
                    out,
                )
            }
        }
    }
}

// ---------------------------------------------------------------------------
// The members (`Modeled.lean:381-456` / `DeclCheck.lean:487-506`)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/Inductives/Modeled.lean:373-401 checkMemberVal
/// con-leche: ConLeche/Kernel/DeclCheck.lean:487-505 checkMemberValF
/// Check a block member's constant against its `_model` counterpart:
/// `checkConstantVal`, the member may not itself be model-shaped, and its type
/// is the model's under the block renaming — structurally.
///
/// Deviation: the cited message dumps both sides with `reprStr`; §3.1 drops
/// the interpolation.
pub fn check_member_val(
    mode: &CheckMode,
    st: &mut CState,
    block_names: &Vec<Name>,
    fe2: &FEnv,
    cv: &ConstantVal,
) -> CheckM<ConstantVal> {
    const M_MODEL_NAME: [u32; 27] = [
        109, 111, 100, 101, 108, 45, 115, 104, 97, 112, 101, 100, 32, 109, 101, 109, 98,
        101, 114, 32, 110, 97, 109, 101, 32, 32, 32,
    ];
    const M_NO_ROUTE: [u32; 47] = [
        110, 111, 32, 105, 110, 115, 116, 97, 108, 108, 32, 114, 111, 117, 116, 101, 32, 102,
        111, 114, 32, 105, 110, 100, 117, 99, 116, 105, 118, 101, 32, 98, 108, 111, 99, 107,
        32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32,
    ];
    const M_MLPS: [u32; 38] = [
        109, 111, 100, 101, 108, 32, 108, 101, 118, 101, 108, 32, 112, 97, 114, 97, 109, 101,
        116, 101, 114, 115, 32, 109, 105, 115, 109, 97, 116, 99, 104, 32, 32, 32, 32, 32, 32,
        32,
    ];
    const M_MTY: [u32; 26] = [
        109, 111, 100, 101, 108, 32, 116, 121, 112, 101, 32, 109, 105, 115, 109, 97, 116, 99,
        104, 32, 32, 32, 32, 32, 32, 32,
    ];
    let f = BlockRename { block_names };
    match checker_base::check_constant_val(mode, st, fe2, cv) {
        Err(err) => Err(err),
        Ok(cv_a) => {
            if level::name_is_model_suffix(&cv_a.name) {
                Err(core_types::invalid(core_types::code_points(&M_MODEL_NAME)))
            } else {
                match core_k::defn_probe(fe2, &model_of(&cv_a.name)) {
                    None => Err(core_types::not_implemented(core_types::code_points(
                        &M_NO_ROUTE,
                    ))),
                    Some(dq) => {
                        if !prop_when::names_beq(&dq.0.level_params, &cv_a.level_params) {
                            Err(core_types::not_implemented(core_types::code_points(
                                &M_MLPS,
                            )))
                        } else {
                            let renamed: Expr = expr_ops::rename_consts(&f, &cv_a.ty);
                            if !expr::beq(&renamed, &dq.0.ty) {
                                Err(core_types::not_implemented(core_types::code_points(
                                    &M_MTY,
                                )))
                            } else {
                                Ok(cv_a)
                            }
                        }
                    }
                }
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/Modeled.lean:403-414 checkIndMember
/// Check and install one non-recursor member of a modeled inductive block
/// against its `_model` counterpart.  `caps` is the capability record the
/// block earned (recorded on the inductive type former); recursors are
/// handled by `checkIndRecs`.
pub fn check_ind_member(
    mode: &CheckMode,
    st: &mut CState,
    block_names: &Vec<Name>,
    caps: &IndCaps,
    fe2: FEnv,
    ci: &ConstantInfo,
) -> CheckM<FEnv> {
    const M_NONIND: [u32; 30] = [
        110, 111, 110, 45, 105, 110, 100, 117, 99, 116, 105, 118, 101, 32, 109, 101, 109, 98,
        101, 114, 32, 105, 110, 32, 98, 108, 111, 99, 107, 32,
    ];
    let cv: ConstantVal = env::to_constant_val(ci);
    match check_member_val(mode, st, block_names, &fe2, &cv) {
        Err(err) => Err(err),
        Ok(cv_a) => match ci {
            ConstantInfo::IndInfo(_, _) => Ok(fenv::push(
                fe2,
                ConstantInfo::IndInfo(cv_a, env::ind_caps_dup(caps)),
            )),
            ConstantInfo::CtorInfo(_, n_p, n_f) => {
                Ok(fenv::push(fe2, ConstantInfo::CtorInfo(cv_a, *n_p, *n_f)))
            }
            _ => Err(core_types::invalid(core_types::code_points(&M_NONIND))),
        },
    }
}

/// con-leche: ConLeche/Kernel/Inductives/Modeled.lean:416-433 provisionRecs
/// Phase 0 of the recursor group: check each recursor's constant and provision
/// it *rule-less* on top of the previous ones.  Returns the fully provisioned
/// environment together with the checked constants (in order).  Rule
/// right-hand sides may mention any recursor of the block, so they are
/// annotated only against the fully provisioned environment.
pub fn provision_recs_step(
    mode: &CheckMode,
    st: &mut CState,
    block_names: &Vec<Name>,
    fe_acc: FEnv,
    ci: &ConstantInfo,
) -> CheckM<(FEnv, ConstantVal, u64, u64, Vec<RecRule>)> {
    const M_ORDER: [u32; 40] = [
        114, 101, 99, 117, 114, 115, 111, 114, 32, 98, 101, 102, 111, 114, 101, 32, 111, 116,
        104, 101, 114, 32, 98, 108, 111, 99, 107, 32, 109, 101, 109, 98, 101, 114, 115, 32,
        32, 32, 32, 32,
    ];
    match ci {
        ConstantInfo::RecInfo(_, m_i, r_p, rules) => {
            let cv: ConstantVal = env::to_constant_val(ci);
            let m_i2: u64 = *m_i;
            let r_p2: u64 = *r_p;
            let rules2: Vec<RecRule> = env::rec_rules_copy(rules);
            match check_member_val(mode, st, block_names, &fe_acc, &cv) {
                Err(err) => Err(err),
                Ok(cv_a) => {
                    let fe2: FEnv = fenv::push(
                        fe_acc,
                        ConstantInfo::RecInfo(
                            env::constant_val_dup(&cv_a),
                            m_i2,
                            r_p2,
                            Vec::new(),
                        ),
                    );
                    Ok((fe2, cv_a, m_i2, r_p2, rules2))
                }
            }
        }
        _ => Err(core_types::not_implemented(core_types::code_points(&M_ORDER))),
    }
}

/// con-leche: ConLeche/Kernel/Inductives/Modeled.lean:416-433 provisionRecs
/// The fold of `provisionRecs` over the block's recursors.  Split from
/// `provision_recs_step` above so that the cached driver's **per-recursor
/// flush** (`provisionRecsS`, `inductives_c::provision_recs_s`) sits exactly
/// where the cited `flushC` does, with one body for both.
pub fn provision_recs(
    mode: &CheckMode,
    st: &mut CState,
    block_names: &Vec<Name>,
    fe_acc: FEnv,
    recs: &Vec<ConstantInfo>,
    i: usize,
    out: Vec<(ConstantVal, u64, u64, Vec<RecRule>)>,
) -> CheckM<(FEnv, Vec<(ConstantVal, u64, u64, Vec<RecRule>)>)> {
    if i >= recs.len() {
        Ok((fe_acc, out))
    } else {
        match provision_recs_step(mode, st, block_names, fe_acc, &recs[i]) {
            Err(err) => Err(err),
            Ok(q) => {
                let mut out = out;
                out.push((q.1, q.2, q.3, q.4));
                provision_recs(mode, st, block_names, q.0, recs, i + 1, out)
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/Modeled.lean:435-455 checkIndRecs
/// The `checked.foldlM` of `checkIndRecs`: every recursor's rules checked at
/// `envSelf`, with the `env'` lookups in `env₂`, and the ruled recursor pushed
/// onto the accumulator.
pub fn check_ind_recs_fold(
    mode: &CheckMode,
    st: &mut CState,
    fe2: &FEnv,
    fe_self: &FEnv,
    f: &BlockRename,
    checked: &Vec<(ConstantVal, u64, u64, Vec<RecRule>)>,
    i: usize,
    acc: FEnv,
) -> CheckM<FEnv> {
    if i >= checked.len() {
        Ok(acc)
    } else {
        let c: &(ConstantVal, u64, u64, Vec<RecRule>) = &checked[i];
        match check_iota_rules(
            mode,
            st,
            fe2,
            fe_self,
            f,
            &c.0.name,
            &c.0.level_params,
            &c.0.ty,
            c.1,
            c.2,
            0,
            &c.3,
            0,
            Vec::new(),
        ) {
            Err(err) => Err(err),
            Ok(rules2) => {
                let acc2: FEnv = fenv::push(
                    acc,
                    ConstantInfo::RecInfo(
                        env::constant_val_dup(&c.0),
                        c.1,
                        c.2,
                        rules2,
                    ),
                );
                check_ind_recs_fold(mode, st, fe2, fe_self, f, checked, i + 1, acc2)
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/Modeled.lean:435-455 checkIndRecs
/// Check and install a block's recursors *as a group*: every rule right-hand
/// side may mention any of them, so all are provisioned rule-less together
/// (`envSelf`) and installed together — no intermediate environment stores a
/// recursor whose rules mention a missing sibling.
///
/// Deviation: the two `fenv::dup`s of the module note.
pub fn check_ind_recs(
    mode: &CheckMode,
    st: &mut CState,
    block_names: &Vec<Name>,
    fe2: FEnv,
    recs: &Vec<ConstantInfo>,
) -> CheckM<FEnv> {
    const M_EQ: [u32; 48] = [
        109, 111, 100, 101, 108, 101, 100, 32, 114, 101, 99, 117, 114, 115, 111, 114, 32,
        114, 101, 113, 117, 105, 114, 101, 115, 32, 116, 104, 101, 32, 112, 105, 110, 110,
        101, 100, 32, 69, 113, 32, 98, 97, 115, 105, 115, 32, 32, 32,
    ];
    if recs.len() == 0 {
        Ok(fe2)
    } else if !basis_pins::eq_basis_pinned(&fe2) {
        Err(core_types::not_implemented(core_types::code_points(&M_EQ)))
    } else {
        let f = BlockRename { block_names };
        let fe_env: FEnv = fenv::dup(&fe2);
        match provision_recs(
            mode,
            st,
            block_names,
            fenv::dup(&fe2),
            recs,
            0,
            Vec::new(),
        ) {
            Err(err) => Err(err),
            Ok(pq) => check_ind_recs_fold(
                mode, st, &fe_env, &pq.0, &f, &pq.1, 0, fe2,
            ),
        }
    }
}

// ---------------------------------------------------------------------------
// The projection functions (`Modeled.lean:479-594` / `DeclCheck.lean:730-837`)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/Inductives/Modeled.lean:475-495 checkProjLookups
/// con-leche: ConLeche/Kernel/DeclCheck.lean:729-746 checkProjLookupsF
/// Stage 1 of `checkProjFn`: the stored constants the projection depends on —
/// the single constructor (arity-matched), the model's `proj_i` definition
/// (level-matched), the parent type, and the pinned equality former; the
/// projection's own name must be free.
pub fn check_proj_lookups(
    fe2: &FEnv,
    t: &Name,
    ctor_name: &Name,
    lps: &Vec<Name>,
    n_p: u64,
    n_f: u64,
    i: u64,
) -> CheckM<(ConstantVal, ConstantVal)> {
    const M_CTOR: [u32; 34] = [
        112, 114, 111, 106, 101, 99, 116, 105, 111, 110, 32, 99, 111, 110, 115, 116, 114,
        117, 99, 116, 111, 114, 32, 110, 111, 116, 32, 115, 116, 111, 114, 101, 100, 32,
    ];
    const M_ARITY: [u32; 39] = [
        112, 114, 111, 106, 101, 99, 116, 105, 111, 110, 32, 99, 111, 110, 115, 116, 114,
        117, 99, 116, 111, 114, 32, 97, 114, 105, 116, 121, 32, 109, 105, 115, 109, 97, 116,
        99, 104, 32, 32,
    ];
    const M_MODEL: [u32; 26] = [
        109, 105, 115, 115, 105, 110, 103, 32, 112, 114, 111, 106, 101, 99, 116, 105, 111,
        110, 32, 109, 111, 100, 101, 108, 32, 32,
    ];
    const M_MLPS: [u32; 33] = [
        112, 114, 111, 106, 101, 99, 116, 105, 111, 110, 32, 109, 111, 100, 101, 108, 32,
        108, 101, 118, 101, 108, 32, 109, 105, 115, 109, 97, 116, 99, 104, 32, 32,
    ];
    const M_TAKEN: [u32; 22] = [
        112, 114, 111, 106, 101, 99, 116, 105, 111, 110, 32, 110, 97, 109, 101, 32, 116, 97,
        107, 101, 110, 32,
    ];
    const M_PARENT: [u32; 29] = [
        112, 114, 111, 106, 101, 99, 116, 105, 111, 110, 32, 112, 97, 114, 101, 110, 116, 32,
        110, 111, 116, 32, 115, 116, 111, 114, 101, 100, 32,
    ];
    const M_EQ: [u32; 43] = [
        112, 114, 111, 106, 101, 99, 116, 105, 111, 110, 32, 105, 111, 116, 97, 32, 114, 101,
        113, 117, 105, 114, 101, 115, 32, 116, 104, 101, 32, 112, 105, 110, 110, 101, 100, 32,
        69, 113, 32, 32, 32, 32, 32,
    ];
    match core_k::ctor_probe(fe2, ctor_name) {
        None => Err(core_types::not_implemented(core_types::code_points(&M_CTOR))),
        Some(cq) => {
            if cq.1 != n_p {
                Err(core_types::not_implemented(core_types::code_points(&M_ARITY)))
            } else if cq.2 != n_f {
                Err(core_types::not_implemented(core_types::code_points(&M_ARITY)))
            } else {
                match core_k::defn_probe(fe2, &core_k::proj_model_name(t, i)) {
                    None => Err(core_types::not_implemented(core_types::code_points(
                        &M_MODEL,
                    ))),
                    Some(dq) => {
                        if !prop_when::names_beq(&dq.0.level_params, lps) {
                            Err(core_types::not_implemented(core_types::code_points(
                                &M_MLPS,
                            )))
                        } else if fenv::find(fe2, &env::proj_fn_name(t, i)).is_some() {
                            Err(core_types::invalid(core_types::code_points(&M_TAKEN)))
                        } else if fenv::find(fe2, t).is_none() {
                            Err(core_types::not_implemented(core_types::code_points(
                                &M_PARENT,
                            )))
                        } else if !basis_pins::eq_basis_pinned(fe2) {
                            Err(core_types::not_implemented(core_types::code_points(&M_EQ)))
                        } else {
                            Ok((cq.0, dq.0))
                        }
                    }
                }
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/Modeled.lean:497-511 checkProjTy
/// con-leche: ConLeche/Kernel/DeclCheck.lean:748-761 checkProjTyF
/// Stage 2: the public projection type — the model's, renamed back (pinned by
/// the renaming roundtrip), well-formed and parameter-led.
pub fn check_proj_ty(
    fe2: &FEnv,
    t: &Name,
    ctor_name: &Name,
    lps: &Vec<Name>,
    mty: &Expr,
    n_p: u64,
    n_f: u64,
) -> CheckM<Expr> {
    const M_ROUND: [u32; 29] = [
        112, 114, 111, 106, 101, 99, 116, 105, 111, 110, 32, 116, 121, 112, 101, 32, 114,
        111, 117, 110, 100, 116, 114, 105, 112, 32, 32, 32, 32,
    ];
    const M_RES: [u32; 30] = [
        112, 114, 111, 106, 101, 99, 116, 105, 111, 110, 32, 116, 121, 112, 101, 32, 114,
        101, 115, 111, 108, 117, 116, 105, 111, 110, 32, 32, 32, 32,
    ];
    const M_WF: [u32; 35] = [
        112, 114, 111, 106, 101, 99, 116, 105, 111, 110, 32, 116, 121, 112, 101, 32, 119,
        101, 108, 108, 102, 111, 114, 109, 101, 100, 110, 101, 115, 115, 32, 32, 32, 32, 32,
    ];
    const M_TELE: [u32; 29] = [
        112, 114, 111, 106, 101, 99, 116, 105, 111, 110, 32, 116, 121, 112, 101, 32, 116,
        101, 108, 101, 115, 99, 111, 112, 101, 32, 32, 32, 32,
    ];
    let back = ProjBack {
        t,
        ctor: ctor_name,
        n_f,
    };
    let fwd = ProjFwd {
        t,
        ctor: ctor_name,
        n_f,
    };
    let pty: Expr = expr_ops::rename_consts(&back, mty);
    let round: Expr = expr_ops::rename_consts(&fwd, &pty);
    if !expr::beq(&round, mty) {
        Err(core_types::not_implemented(core_types::code_points(&M_ROUND)))
    } else if !decl_check::consts_resolve_f_fast(fe2, &pty) {
        Err(core_types::not_implemented(core_types::code_points(&M_RES)))
    } else {
        let wf = if expr_ops::loose_bvars_bounded(0, &pty) {
            if !expr_ops::has_fvar(&pty) {
                expr_ops::all_level_params_defined_fast(lps, &pty)
            } else {
                false
            }
        } else {
            false
        };
        if !wf {
            Err(core_types::not_implemented(core_types::code_points(&M_WF)))
        } else if expr_ops::strip_pis(n_p + 1, &pty).is_none() {
            Err(core_types::not_implemented(core_types::code_points(&M_TELE)))
        } else {
            Ok(pty)
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/Modeled.lean:513-563 checkProjIota
/// con-leche: ConLeche/Kernel/DeclCheck.lean:797-836 checkProjIotaF
/// Stage 4: the model's `proj_i.iota` theorem pins the rule — the statement's
/// telescope domains are the constructor's (renamed to the model side) and its
/// body equates the projected constructor spine with field `i`.  Both equation
/// sides are then certified against the equality's type slot definitionally at
/// the opened telescope.
pub fn check_proj_iota(
    mode: &CheckMode,
    st: &mut CState,
    fe2: &FEnv,
    fe_self: &FEnv,
    t: &Name,
    ctor_name: &Name,
    lps: &Vec<Name>,
    cvj: &ConstantVal,
    n_p: u64,
    n_f: u64,
    i: u64,
) -> CheckM<()> {
    const M_MISS: [u32; 32] = [
        109, 105, 115, 115, 105, 110, 103, 32, 112, 114, 111, 106, 101, 99, 116, 105, 111,
        110, 32, 105, 111, 116, 97, 32, 116, 104, 101, 111, 114, 101, 109, 32,
    ];
    const M_LPS: [u32; 32] = [
        112, 114, 111, 106, 101, 99, 116, 105, 111, 110, 32, 105, 111, 116, 97, 32, 108, 101,
        118, 101, 108, 32, 109, 105, 115, 109, 97, 116, 99, 104, 32, 32,
    ];
    const M_TELE: [u32; 29] = [
        112, 114, 111, 106, 101, 99, 116, 105, 111, 110, 32, 105, 111, 116, 97, 32, 116, 101,
        108, 101, 115, 99, 111, 112, 101, 32, 32, 32, 32,
    ];
    const M_CTELE: [u32; 36] = [
        112, 114, 111, 106, 101, 99, 116, 105, 111, 110, 32, 99, 111, 110, 115, 116, 114,
        117, 99, 116, 111, 114, 32, 116, 101, 108, 101, 115, 99, 111, 112, 101, 32, 32, 32,
        32,
    ];
    const M_DOM: [u32; 33] = [
        112, 114, 111, 106, 101, 99, 116, 105, 111, 110, 32, 105, 111, 116, 97, 32, 100, 111,
        109, 97, 105, 110, 32, 109, 105, 115, 109, 97, 116, 99, 104, 32, 32,
    ];
    match thm_probe(fe2, &proj_iota_name(t, i)) {
        None => Err(core_types::not_implemented(core_types::code_points(&M_MISS))),
        Some(tcv) => {
            if !prop_when::names_beq(&tcv.level_params, lps) {
                Err(core_types::not_implemented(core_types::code_points(&M_LPS)))
            } else {
                match expr_ops::strip_pis(n_p + n_f, &tcv.ty) {
                    None => Err(core_types::not_implemented(core_types::code_points(
                        &M_TELE,
                    ))),
                    Some(sq) => match expr_ops::strip_pis(n_p + n_f, &cvj.ty) {
                        None => Err(core_types::not_implemented(core_types::code_points(
                            &M_CTELE,
                        ))),
                        Some(cq) => {
                            let view = DomProjFwd {
                                t,
                                ctor: ctor_name,
                                n_f,
                            };
                            if !checker_base::doms_match_aux(
                                &view, &sq.0, &cq.0, 0, 0, n_p + n_f,
                            ) {
                                Err(core_types::not_implemented(core_types::code_points(
                                    &M_DOM,
                                )))
                            } else {
                                check_proj_iota_body(
                                    mode, st, fe_self, t, cvj, lps, n_p, n_f, i, &tcv,
                                    &sq.1,
                                )
                            }
                        }
                    },
                }
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/Modeled.lean:513-563 checkProjIota
/// con-leche: ConLeche/Kernel/DeclCheck.lean:797-836 checkProjIotaF
/// The body pin of `checkProjIota` and the two side certificates: the
/// statement's body is `Eq _ (T._model.proj_i p⃗ (C._model p⃗ f⃗)) f_i`.
pub fn check_proj_iota_body(
    mode: &CheckMode,
    st: &mut CState,
    fe_self: &FEnv,
    t: &Name,
    cvj: &ConstantVal,
    lps: &Vec<Name>,
    n_p: u64,
    n_f: u64,
    i: u64,
    tcv: &ConstantVal,
    sbody: &Expr,
) -> CheckM<()> {
    const M_HEAD: [u32; 21] = [
        112, 114, 111, 106, 101, 99, 116, 105, 111, 110, 32, 105, 111, 116, 97, 32, 104, 101,
        97, 100, 32,
    ];
    const M_REDEX: [u32; 31] = [
        112, 114, 111, 106, 101, 99, 116, 105, 111, 110, 32, 105, 111, 116, 97, 32, 114, 101,
        100, 101, 120, 32, 109, 105, 115, 109, 97, 116, 99, 104, 32,
    ];
    const M_FIELD: [u32; 31] = [
        112, 114, 111, 106, 101, 99, 116, 105, 111, 110, 32, 105, 111, 116, 97, 32, 102, 105,
        101, 108, 100, 32, 109, 105, 115, 109, 97, 116, 99, 104, 32,
    ];
    const M_SHAPE: [u32; 28] = [
        112, 114, 111, 106, 101, 99, 116, 105, 111, 110, 32, 105, 111, 116, 97, 32, 98, 111,
        100, 121, 32, 115, 104, 97, 112, 101, 32, 32,
    ];
    const M_TELE: [u32; 29] = [
        112, 114, 111, 106, 101, 99, 116, 105, 111, 110, 32, 105, 111, 116, 97, 32, 116, 101,
        108, 101, 115, 99, 111, 112, 101, 32, 32, 32, 32,
    ];
    let depth: u64 = n_p + n_f;
    let p_args: Vec<Expr> = struct_parts::struct_ps_at(n_f, n_p);
    let x_args: Vec<Expr> = struct_parts::field_spine(n_f);
    let mut spine: Vec<Expr> = env::exprs_copy(&p_args);
    spine = core_k::append_exprs(spine, &x_args);
    let mk_spine: Expr = expr_ops::mk_app_n(
        expr::mk_const(
            model_of(&cvj.name),
            struct_parts::params_of(&cvj.level_params),
        ),
        &spine,
    );
    let mut largs: Vec<Expr> = env::exprs_copy(&p_args);
    largs.push(mk_spine);
    let lhs_s: Expr = expr_ops::mk_app_n(
        expr::mk_const(core_k::proj_model_name(t, i), struct_parts::params_of(lps)),
        &largs,
    );
    let head: Expr = expr_ops::get_app_fn(sbody);
    let args: Vec<Expr> = expr_ops::get_app_args(sbody);
    // the cited `.app (.app (.app (.const c [_ℓ]) _tySlot) lhsC) rhsC` pattern
    let shaped = if args.len() == 3 {
        match &head.0.kind {
            ExprKind::Const(_, us) => us.len() == 1,
            _ => false,
        }
    } else {
        false
    };
    if !shaped {
        Err(core_types::not_implemented(core_types::code_points(&M_SHAPE)))
    } else if !checker_base::is_eq_head(&head) {
        Err(core_types::not_implemented(core_types::code_points(&M_HEAD)))
    } else if !expr::beq(&args[1], &lhs_s) {
        Err(core_types::not_implemented(core_types::code_points(&M_REDEX)))
    } else if !expr::beq(&args[2], &expr::bvar(expr_ops::sub_nat(n_f, 1 + i))) {
        Err(core_types::not_implemented(core_types::code_points(&M_FIELD)))
    } else {
        match checker_base::open_pis_at_fvars_f(depth, &tcv.ty, 0) {
            None => Err(core_types::not_implemented(core_types::code_points(&M_TELE))),
            Some(oq) => {
                let targs_o: Vec<Expr> = expr_ops::get_app_args(&oq.1);
                let alpha: Expr = arg_get_d(&targs_o, 0);
                let l: Expr = arg_get_d(&targs_o, 1);
                let r: Expr = arg_get_d(&targs_o, 2);
                let l_a: Level = checker_base::eq_head_level(&head);
                check_iota_sides_ty(mode, st, fe_self, depth, &alpha, &l, &r, &l_a)
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/Modeled.lean:565-584 checkProjFn
/// con-leche: ConLeche/Cached/CheckerC.lean:153-166 checkProjFnS
/// Check and install the public projection function for field `i` of a modeled
/// single-constructor structure, against the model's `T._model.proj_i`
/// definition and its `iota` theorem.  The function is stored as a degenerate
/// recursor (no motive, no minors) carrying one rule, so the generic iota
/// machinery reduces it.
pub fn check_proj_fn(
    mode: &CheckMode,
    st: &mut CState,
    fe2: FEnv,
    t: &Name,
    ctor_name: &Name,
    lps: &Vec<Name>,
    n_p: u64,
    n_f: u64,
    i: u64,
) -> CheckM<FEnv> {
    const M_RANGE: [u32; 33] = [
        112, 114, 111, 106, 101, 99, 116, 105, 111, 110, 32, 105, 110, 100, 101, 120, 32,
        111, 117, 116, 32, 111, 102, 32, 114, 97, 110, 103, 101, 32, 32, 32, 32,
    ];
    match check_proj_lookups(&fe2, t, ctor_name, lps, n_p, n_f, i) {
        Err(err) => Err(err),
        Ok(lq) => {
            let cvj: ConstantVal = lq.0;
            let mcv: ConstantVal = lq.1;
            match check_proj_ty(&fe2, t, ctor_name, lps, &mcv.ty, n_p, n_f) {
                Err(err) => Err(err),
                Ok(pty) => match checker_base::check_proj_shape(&pty, &cvj.ty, n_p, n_f) {
                    Err(err) => Err(err),
                    Ok(()) => {
                        if i >= n_f {
                            Err(core_types::invalid(core_types::code_points(&M_RANGE)))
                        } else {
                            match checker_base::check_proj_rule(
                                mode, st, &fe2, &pty, &cvj, lps, n_p, n_f, i,
                            ) {
                                Err(err) => Err(err),
                                Ok(rhs_a) => {
                                    match check_proj_iota(
                                        mode, st, &fe2, &fe2, t, ctor_name, lps, &cvj,
                                        n_p, n_f, i,
                                    ) {
                                        Err(err) => Err(err),
                                        Ok(()) => {
                                            let mut rules: Vec<RecRule> = Vec::new();
                                            rules.push(core_k::proj_fn_rule(
                                                &fe2, t, ctor_name, &pty, n_p, n_f, i,
                                                rhs_a,
                                            ));
                                            Ok(fenv::push(
                                                fe2,
                                                ConstantInfo::RecInfo(
                                                    ConstantVal {
                                                        name: env::proj_fn_name(t, i),
                                                        level_params:
                                                            prop_when::names_copy(lps),
                                                        ty: pty,
                                                    },
                                                    n_p,
                                                    n_p,
                                                    rules,
                                                ),
                                            ))
                                        }
                                    }
                                }
                            }
                        }
                    }
                },
            }
        }
    }
}

// ---------------------------------------------------------------------------
// The capability artifacts (`Modeled.lean:596-738` / `DeclCheck.lean:344-443`)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/Inductives/Modeled.lean:586-642 checkEtaThm
/// con-leche: ConLeche/Kernel/DeclCheck.lean:344-382 checkEtaThmF
/// `(List.range nF).all (fun j => match env'.find? (projModelName T j) with
/// | some (.defnInfo cvmj _ _) => cvmj.levelParams == lps | _ => false)` — the
/// projection models exist at the family's level parameters.
pub fn proj_models_at_lps_from(fe2: &FEnv, t: &Name, lps: &Vec<Name>, n_f: u64, j: u64) -> bool {
    if j >= n_f {
        true
    } else {
        match core_k::defn_probe(fe2, &core_k::proj_model_name(t, j)) {
            Some(dq) => {
                if prop_when::names_beq(&dq.0.level_params, lps) {
                    proj_models_at_lps_from(fe2, t, lps, n_f, j + 1)
                } else {
                    false
                }
            }
            None => false,
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/Modeled.lean:586-642 checkEtaThm
/// con-leche: ConLeche/Kernel/DeclCheck.lean:344-382 checkEtaThmF
/// The right-hand side of the eta statement:
/// `C._model p⃗ (T._model.proj_0 p⃗ x) … (T._model.proj_{nF-1} p⃗ x)`, with the
/// parameters at `bvar (nP - k)` and the subject at `bvar 0`.
pub fn eta_rhs(t: &Name, ctor_name: &Name, lps: &Vec<Name>, n_p: u64, n_f: u64) -> Expr {
    let ps: Vec<Expr> = struct_parts::struct_proj_ps(n_p);
    let mut args: Vec<Expr> = env::exprs_copy(&ps);
    args = eta_projs_from(t, lps, &ps, n_f, 0, args);
    expr_ops::mk_app_n(
        expr::mk_const(model_of(ctor_name), struct_parts::params_of(lps)),
        &args,
    )
}

/// con-leche: ConLeche/Kernel/Inductives/Modeled.lean:586-642 checkEtaThm
/// The `(List.range nF).map` of `eta_rhs`: each field's projection model
/// applied to the parameters and the subject.
pub fn eta_projs_from(
    t: &Name,
    lps: &Vec<Name>,
    ps: &Vec<Expr>,
    n_f: u64,
    j: u64,
    out: Vec<Expr>,
) -> Vec<Expr> {
    if j >= n_f {
        out
    } else {
        let mut pargs: Vec<Expr> = env::exprs_copy(ps);
        pargs.push(expr::bvar(0));
        let mut out = out;
        out.push(expr_ops::mk_app_n(
            expr::mk_const(core_k::proj_model_name(t, j), struct_parts::params_of(lps)),
            &pargs,
        ));
        eta_projs_from(t, lps, ps, n_f, j + 1, out)
    }
}

/// con-leche: ConLeche/Kernel/Inductives/Modeled.lean:586-642 checkEtaThm
/// con-leche: ConLeche/Kernel/DeclCheck.lean:344-382 checkEtaThmF
/// Does the model document structural eta for this single-constructor block —
/// a `T._model.eta` theorem with the pinned statement
/// `∀ p⃗ (x : T._model p⃗), x = C._model p⃗ (T._model.proj_0 p⃗ x) …`?
/// `Bool`-valued: an absent or differently shaped artifact just means no
/// capability.
pub fn check_eta_thm(
    mode: &CheckMode,
    fe2: &FEnv,
    t: &Name,
    ctor_name: &Name,
    lps: &Vec<Name>,
    n_p: u64,
    n_f: u64,
) -> bool {
    match thm_probe(fe2, &eta_thm_name(t)) {
        None => false,
        Some(tcv) => match core_k::defn_probe(fe2, &model_of(t)) {
            None => false,
            Some(dt) => match core_k::defn_probe(fe2, &model_of(ctor_name)) {
                None => false,
                Some(dc) => {
                    if !basis_pins::eq_basis_pinned(fe2) {
                        false
                    } else if !prop_when::names_beq(&tcv.level_params, lps) {
                        false
                    } else if !prop_when::names_beq(&dt.0.level_params, lps) {
                        false
                    } else if !prop_when::names_beq(&dc.0.level_params, lps) {
                        false
                    } else if !proj_models_at_lps_from(fe2, t, lps, n_f, 0) {
                        false
                    } else {
                        check_eta_thm_shape(
                            mode, t, ctor_name, lps, n_p, n_f, &tcv.ty, &dt.0.ty,
                        )
                    }
                }
            },
        },
    }
}

/// con-leche: ConLeche/Kernel/Inductives/Modeled.lean:586-642 checkEtaThm
/// con-leche: ConLeche/Kernel/DeclCheck.lean:344-382 checkEtaThmF
/// The statement-shape half of `checkEtaThm`: the parameter telescope against
/// the constructor model's, the subject binder's domain, and the equation —
/// the type slot pinned to the family application and its sort to the
/// statement's own `Eq` level (a TT-lane check).
pub fn check_eta_thm_shape(
    mode: &CheckMode,
    t: &Name,
    ctor_name: &Name,
    lps: &Vec<Name>,
    n_p: u64,
    n_f: u64,
    tty: &Expr,
    tty_m: &Expr,
) -> bool {
    match expr_ops::strip_pis(n_p + 1, tty) {
        None => false,
        Some(sq) => match expr_ops::strip_pis(n_p, tty_m) {
            None => false,
            Some(mq) => {
                if !checker_base::doms_match_aux(&DomIdent, &sq.0, &mq.0, 0, 0, n_p) {
                    false
                } else if (n_p as usize) >= sq.0.len() {
                    false
                } else {
                    let fam_at_1: Expr = expr_ops::mk_app_n(
                        expr::mk_const(model_of(t), struct_parts::params_of(lps)),
                        &struct_parts::struct_ps_at(0, n_p),
                    );
                    if !expr::beq(&sq.0[n_p as usize].0, &fam_at_1) {
                        false
                    } else {
                        let head: Expr = expr_ops::get_app_fn(&sq.1);
                        let args: Vec<Expr> = expr_ops::get_app_args(&sq.1);
                        if args.len() != 3 {
                            false
                        } else if !checker_base::is_eq_head(&head) {
                            false
                        } else if !expr::beq(&args[1], &expr::bvar(0)) {
                            false
                        } else {
                            let slot: Expr = expr_ops::mk_app_n(
                                expr::mk_const(model_of(t), struct_parts::params_of(lps)),
                                &struct_parts::struct_proj_ps(n_p),
                            );
                            if !expr::beq(&args[0], &slot) {
                                false
                            } else if !expr::beq(
                                &args[2],
                                &eta_rhs(t, ctor_name, lps, n_p, n_f),
                            ) {
                                false
                            } else if !env::tt_checks(mode) {
                                true
                            } else {
                                let l_a: Level = checker_base::eq_head_level(&head);
                                expr::beq(&mq.1, &expr::sort(l_a))
                            }
                        }
                    }
                }
            }
        },
    }
}

/// con-leche: ConLeche/Kernel/Inductives/Modeled.lean:644-680 checkUnitThm
/// con-leche: ConLeche/Kernel/DeclCheck.lean:384-414 checkUnitThmF
/// Does the model document unit-likeness for this block — a
/// `T._model.unitlike` theorem with the pinned statement
/// `∀ p⃗ (x y : T._model p⃗), x = y`?
pub fn check_unit_thm(
    mode: &CheckMode,
    fe2: &FEnv,
    t: &Name,
    lps: &Vec<Name>,
    n_p: u64,
) -> bool {
    match thm_probe(fe2, &unit_thm_name(t)) {
        None => false,
        Some(tcv) => match core_k::defn_probe(fe2, &model_of(t)) {
            None => false,
            Some(dt) => {
                if !basis_pins::eq_basis_pinned(fe2) {
                    false
                } else if !prop_when::names_beq(&tcv.level_params, lps) {
                    false
                } else if !prop_when::names_beq(&dt.0.level_params, lps) {
                    false
                } else {
                    check_unit_thm_shape(mode, t, lps, n_p, &tcv.ty, &dt.0.ty)
                }
            }
        },
    }
}

/// con-leche: ConLeche/Kernel/Inductives/Modeled.lean:644-680 checkUnitThm
/// con-leche: ConLeche/Kernel/DeclCheck.lean:384-414 checkUnitThmF
/// The statement-shape half of `checkUnitThm`.
pub fn check_unit_thm_shape(
    mode: &CheckMode,
    t: &Name,
    lps: &Vec<Name>,
    n_p: u64,
    tty: &Expr,
    tty_m: &Expr,
) -> bool {
    match expr_ops::strip_pis(n_p + 2, tty) {
        None => false,
        Some(sq) => match expr_ops::strip_pis(n_p, tty_m) {
            None => false,
            Some(mq) => {
                if !checker_base::doms_match_aux(&DomIdent, &sq.0, &mq.0, 0, 0, n_p) {
                    false
                } else if (n_p as usize + 1) >= sq.0.len() {
                    false
                } else {
                    let fam: Expr = expr::mk_const(model_of(t), struct_parts::params_of(lps));
                    let x_dom: Expr = expr_ops::mk_app_n(
                        expr::dup(&fam),
                        &struct_parts::struct_ps_at(0, n_p),
                    );
                    let y_dom: Expr = expr_ops::mk_app_n(
                        expr::dup(&fam),
                        &struct_parts::struct_proj_ps(n_p),
                    );
                    if !expr::beq(&sq.0[n_p as usize].0, &x_dom) {
                        false
                    } else if !expr::beq(&sq.0[n_p as usize + 1].0, &y_dom) {
                        false
                    } else {
                        let head: Expr = expr_ops::get_app_fn(&sq.1);
                        let args: Vec<Expr> = expr_ops::get_app_args(&sq.1);
                        if args.len() != 3 {
                            false
                        } else if !checker_base::is_eq_head(&head) {
                            false
                        } else if !expr::beq(&args[1], &expr::bvar(1)) {
                            false
                        } else if !expr::beq(&args[2], &expr::bvar(0)) {
                            false
                        } else {
                            let slot: Expr = expr_ops::mk_app_n(
                                expr::dup(&fam),
                                &struct_parts::struct_ps_at(2, n_p),
                            );
                            if !expr::beq(&args[0], &slot) {
                                false
                            } else if !env::tt_checks(mode) {
                                true
                            } else {
                                let l_a: Level = checker_base::eq_head_level(&head);
                                expr::beq(&mq.1, &expr::sort(l_a))
                            }
                        }
                    }
                }
            }
        },
    }
}

/// con-leche: ConLeche/Kernel/Inductives/Modeled.lean:682-710 ctorTargetsFam
/// **Official's structure-likeness, read off the block's own constructor**
/// (`is_non_rec_structure`: one constructor and *no indices*).  An index-free
/// single-constructor family's constructor targets the family at exactly its
/// parameters, `T p⃗`, while an indexed family's targets `T p⃗ i⃗`.  The subject
/// is the block's *incoming* constructor type, not the stored one, so the
/// decision is a function of the block.  A gate, not a pin.
pub fn ctor_targets_fam(ctor_ty: &Expr, t: &Name, lps: &Vec<Name>, n_p: u64, n_f: u64) -> bool {
    match expr_ops::strip_pis(n_p + n_f, ctor_ty) {
        Some(q) => expr::beq(&q.1, &struct_parts::struct_fam(t, lps, n_p, n_f)),
        None => false,
    }
}

/// con-leche: ConLeche/Kernel/Inductives/Modeled.lean:712-722 installProjFnStep
/// One projection-function install step (skipped where the model's projection
/// artifact is absent — a family with such fields simply gets no table, and a
/// `.proj` on it declines at its own site).  The whole fold is skipped for a
/// block that is not structure-like (`ctorTargetsFam`).
pub fn install_proj_fn_step(
    mode: &CheckMode,
    st: &mut CState,
    t: &Name,
    ctor_name: &Name,
    lps: &Vec<Name>,
    n_p: u64,
    n_f: u64,
    fe2: FEnv,
    i: u64,
) -> CheckM<FEnv> {
    if fenv::find(&fe2, &core_k::proj_model_name(t, i)).is_some() {
        check_proj_fn(mode, st, fe2, t, ctor_name, lps, n_p, n_f, i)
    } else {
        Ok(fe2)
    }
}

/// con-leche: ConLeche/Kernel/Inductives/Modeled.lean:724-735 indBlockCaps
/// con-leche: ConLeche/Kernel/DeclCheck.lean:430-441 indBlockCapsF
/// The capabilities recorded for a single-constructor modeled block.  The K
/// flag is computed from shape exactly as the official kernel does — an
/// inductive proposition with a single constructor taking only the parameters
/// — and the reduction site carries the semantic load (proof irrelevance), so
/// no model theorem backs it.
pub fn ind_block_caps(
    mode: &CheckMode,
    fe2: &FEnv,
    cv_t: &ConstantVal,
    cv_c: &ConstantVal,
    n_p: u64,
    n_f: u64,
) -> IndCaps {
    let eta = if prop_when::names_beq(&cv_c.level_params, &cv_t.level_params) {
        check_eta_thm(
            mode,
            fe2,
            &cv_t.name,
            &cv_c.name,
            &cv_t.level_params,
            n_p,
            n_f,
        )
    } else {
        false
    };
    let rule_k = if n_f == 0 {
        core_k::pi_result_is_prop(&cv_t.ty)
    } else {
        false
    };
    IndCaps {
        eta,
        eta_ctor: name::dup(&cv_c.name),
        eta_params: n_p,
        eta_fields: n_f,
        unitlike: check_unit_thm(mode, fe2, &cv_t.name, &cv_t.level_params, n_p),
        unit_params: n_p,
        rule_k,
        sort_z: core_k::pi_result_z(&cv_t.ty),
    }
}

/// con-leche: ConLeche/Kernel/Inductives/Modeled.lean:744-779 ctorResidualOk
/// con-leche: ConLeche/Kernel/DeclCheck.lean:416-428 ctorResidualOkF
/// **An eta-capable family's constructor returns the family applied to its
/// parameters.**  The subject is the **stored** constant — what
/// `checkMemberVal` stored, i.e. `checkConstantVal`'s annotated output, which
/// is what every consumer reads back — and the capability guard is not
/// cosmetic: unguarded the conjunct is refuted by the corpus at the *indexed*
/// families.  A TT-lane check: trivially true unless `mode.ttChecks`.
pub fn ctor_residual_ok(
    mode: &CheckMode,
    fe3: &FEnv,
    t: &Name,
    ctor_name: &Name,
    lps: &Vec<Name>,
    n_p: u64,
    n_f: u64,
    eta: bool,
) -> bool {
    if !env::tt_checks(mode) {
        true
    } else if !eta {
        true
    } else {
        match core_k::ctor_probe(fe3, ctor_name) {
            Some(cq) => match expr_ops::strip_pis(n_p + n_f, &cq.0.ty) {
                Some(q) => {
                    expr::beq(&q.1, &struct_parts::struct_fam(t, lps, n_p, n_f))
                }
                None => false,
            },
            None => false,
        }
    }
}

// ---------------------------------------------------------------------------
// The block (`Modeled.lean:784-836`)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/Inductives/Modeled.lean:781-834 checkModeled
/// con-leche: ConLeche/Cached/CheckerC.lean:233-268 checkIndDeclSF
/// `block.filter (fun ci => match ci with | .recInfo … => keep | _ => !keep)`,
/// as an index recursion.  Lean's list is shared; a `Vec` copies
/// (`constant_info_dup`).
pub fn filter_recs(block: &Vec<ConstantInfo>, keep: bool) -> Vec<ConstantInfo> {
    filter_recs_from(block, keep, 0, Vec::new())
}

/// con-leche: ConLeche/Kernel/Inductives/Modeled.lean:781-834 checkModeled
/// The index recursion behind `filter_recs`.
pub fn filter_recs_from(
    block: &Vec<ConstantInfo>,
    keep: bool,
    i: usize,
    out: Vec<ConstantInfo>,
) -> Vec<ConstantInfo> {
    if i >= block.len() {
        out
    } else {
        let is_rec: bool = env::is_rec_info(&block[i]);
        let mut out = out;
        if is_rec == keep {
            out.push(env::constant_info_dup(&block[i]));
        }
        filter_recs_from(block, keep, i + 1, out)
    }
}

/// con-leche: ConLeche/Kernel/Inductives/Modeled.lean:781-834 checkModeled
/// `block.map (·.name)`, the block's names the renaming reads.
pub fn block_names_of(block: &Vec<ConstantInfo>) -> Vec<Name> {
    block_names_of_from(block, 0, Vec::new())
}

/// con-leche: ConLeche/Kernel/Inductives/Modeled.lean:781-834 checkModeled
/// The index recursion behind `block_names_of`.
pub fn block_names_of_from(
    block: &Vec<ConstantInfo>,
    i: usize,
    out: Vec<Name>,
) -> Vec<Name> {
    if i >= block.len() {
        out
    } else {
        let mut out = out;
        out.push(env::constant_info_name(&block[i]));
        block_names_of_from(block, i + 1, out)
    }
}

/// con-leche: ConLeche/Kernel/Inductives/Modeled.lean:781-834 checkModeled
/// con-leche: ConLeche/Cached/CheckerC.lean:233-268 checkIndDeclSF
/// The block's **single type former and single constructor**, if it has
/// exactly one of each: the cited
/// `match block.filter indInfo, block.filter ctorInfo with
/// | [.indInfo cvT _], [.ctorInfo cvC nP nF] => …`.
pub fn single_ind_ctor(
    block: &Vec<ConstantInfo>,
) -> Option<(ConstantVal, ConstantVal, u64, u64)> {
    let r = single_ind_ctor_from(block, 0, None, None, 0, 0);
    if r.2 == 1 {
        if r.3 == 1 {
            match r.0 {
                Some(cv_t) => match r.1 {
                    Some(cq) => Some((cv_t, cq.0, cq.1, cq.2)),
                    None => None,
                },
                None => None,
            }
        } else {
            None
        }
    } else {
        None
    }
}

/// con-leche: ConLeche/Kernel/Inductives/Modeled.lean:781-834 checkModeled
/// The index recursion behind `single_ind_ctor`: the two filters counted and
/// their first element remembered, which is what the two one-element list
/// patterns decide.
pub fn single_ind_ctor_from(
    block: &Vec<ConstantInfo>,
    i: usize,
    t: Option<ConstantVal>,
    c: Option<(ConstantVal, u64, u64)>,
    n_ind: u64,
    n_ctor: u64,
) -> (Option<ConstantVal>, Option<(ConstantVal, u64, u64)>, u64, u64) {
    if i >= block.len() {
        (t, c, n_ind, n_ctor)
    } else {
        match &block[i] {
            ConstantInfo::IndInfo(cv, _) => {
                let t2 = match t {
                    None => Some(env::constant_val_dup(cv)),
                    Some(old) => Some(old),
                };
                single_ind_ctor_from(block, i + 1, t2, c, n_ind + 1, n_ctor)
            }
            ConstantInfo::CtorInfo(cv, n_p, n_f) => {
                let c2 = match c {
                    None => Some((env::constant_val_dup(cv), *n_p, *n_f)),
                    Some(old) => Some(old),
                };
                single_ind_ctor_from(block, i + 1, t, c2, n_ind, n_ctor + 1)
            }
            _ => single_ind_ctor_from(block, i + 1, t, c, n_ind, n_ctor),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::kernel::expr::BinderMeta;

    fn nm(s: &str) -> Name {
        let cps: Vec<u32> = s.chars().map(|c| c as u32).collect();
        name::mk_str(name::anonymous(), cps)
    }

    fn raw() -> BinderMeta {
        expr::binder_meta(prop_when::never())
    }

    /// **The public↔model renaming is a bijection on the block's names**, which
    /// is what `checkProjTy`'s roundtrip pin turns into a check: the family,
    /// the constructor and the whole projection family map across and back,
    /// and anything else is fixed.
    #[test]
    fn the_projection_renaming_roundtrips() {
        let t = nm("T");
        let c = nm("Cmk");
        let fwd = ProjFwd {
            t: &t,
            ctor: &c,
            n_f: 2,
        };
        let back = ProjBack {
            t: &t,
            ctor: &c,
            n_f: 2,
        };
        assert!(name::beq(&fwd.rename(&t), &model_of(&t)));
        assert!(name::beq(&back.rename(&model_of(&t)), &t));
        assert!(name::beq(&fwd.rename(&c), &model_of(&c)));
        assert!(name::beq(&back.rename(&model_of(&c)), &c));
        let mut j: u64 = 0;
        while j < 2 {
            let pub_n = env::proj_fn_name(&t, j);
            let mod_n = core_k::proj_model_name(&t, j);
            assert!(name::beq(&fwd.rename(&pub_n), &mod_n));
            assert!(name::beq(&back.rename(&mod_n), &pub_n));
            j += 1;
        }
        // field 2 is out of range, so it is not in the family
        let out = env::proj_fn_name(&t, 2);
        assert!(name::beq(&fwd.rename(&out), &out));
        // and an unrelated constant is fixed both ways
        let other = nm("Nat");
        assert!(name::beq(&fwd.rename(&other), &other));
        assert!(name::beq(&back.rename(&other), &other));
        // the block renaming maps a member to its `_model` twin and nothing else
        let mut names: Vec<Name> = Vec::new();
        names.push(name::dup(&t));
        let f = BlockRename {
            block_names: &names,
        };
        assert!(name::beq(&f.rename(&t), &model_of(&t)));
        assert!(name::beq(&f.rename(&c), &c));
    }

    /// **Official's structure-likeness gate.**  A constructor that targets the
    /// family at exactly its parameters is structure-like; one that targets it
    /// at an index is not (the `SigmaHom` ruling: an indexed family's model
    /// projections are ignored at install).
    #[test]
    fn ctor_targets_fam_reads_the_residual() {
        let t = nm("T");
        let a = expr::mk_const(nm("A"), Vec::new());
        // `∀ (p : A) (f : A), T p`
        let mut ps: Vec<Expr> = Vec::new();
        ps.push(expr::bvar(1));
        let plain = expr::forall_e(
            expr::dup(&a),
            expr::forall_e(
                expr::dup(&a),
                expr_ops::mk_app_n(expr::mk_const(name::dup(&t), Vec::new()), &ps),
                raw(),
            ),
            raw(),
        );
        assert!(ctor_targets_fam(&plain, &t, &Vec::new(), 1, 1));
        // `∀ (p : A) (f : A), T p f` — an index, so not structure-like
        let mut psi: Vec<Expr> = Vec::new();
        psi.push(expr::bvar(1));
        psi.push(expr::bvar(0));
        let indexed = expr::forall_e(
            expr::dup(&a),
            expr::forall_e(
                expr::dup(&a),
                expr_ops::mk_app_n(expr::mk_const(name::dup(&t), Vec::new()), &psi),
                raw(),
            ),
            raw(),
        );
        assert!(!ctor_targets_fam(&indexed, &t, &Vec::new(), 1, 1));
        // and a telescope that is too short is not read at all
        assert!(!ctor_targets_fam(&plain, &t, &Vec::new(), 1, 2));
    }

    /// The two `iota`-artifact names and the block filters the driver reads.
    #[test]
    fn the_model_artifact_names_and_the_block_filters() {
        let t = nm("R");
        // `R._model.iota_12`
        let n = iota_thm_name(&t, 12);
        let expected = name::mk_str(
            model_of(&t),
            vec![105, 111, 116, 97, 95, 49, 50],
        );
        assert!(name::beq(&n, &expected));
        // `R._model.proj_0.iota`
        let pj = proj_iota_name(&t, 0);
        assert!(name::beq(
            &pj,
            &name::mk_str(core_k::proj_model_name(&t, 0), vec![105, 111, 116, 97])
        ));
        // `R._model.eta` / `R._model.unitlike`
        assert!(name::beq(
            &eta_thm_name(&t),
            &name::mk_str(model_of(&t), vec![101, 116, 97])
        ));
        assert!(name::beq(
            &unit_thm_name(&t),
            &name::mk_str(
                model_of(&t),
                vec![117, 110, 105, 116, 108, 105, 107, 101]
            )
        ));
        // the block split: the recursors and everything else, in order
        let s1 = expr::sort(level::succ(level::zero()));
        let cv_t = ConstantVal {
            name: name::dup(&t),
            level_params: Vec::new(),
            ty: expr::dup(&s1),
        };
        let cv_c = ConstantVal {
            name: nm("Rmk"),
            level_params: Vec::new(),
            ty: expr::mk_const(name::dup(&t), Vec::new()),
        };
        let cv_r = ConstantVal {
            name: nm("Rrec"),
            level_params: Vec::new(),
            ty: expr::dup(&s1),
        };
        let mut block: Vec<ConstantInfo> = Vec::new();
        block.push(ConstantInfo::IndInfo(cv_t, env::ind_caps_default()));
        block.push(ConstantInfo::CtorInfo(cv_c, 0, 0));
        block.push(ConstantInfo::RecInfo(cv_r, 1, 1, Vec::new()));
        assert_eq!(filter_recs(&block, true).len(), 1);
        assert_eq!(filter_recs(&block, false).len(), 2);
        assert_eq!(block_names_of(&block).len(), 3);
        // one type former and one constructor: the capability-bearing arm
        match single_ind_ctor(&block) {
            Some(q) => {
                assert!(name::beq(&q.0.name, &t));
                assert!(name::beq(&q.1.name, &nm("Rmk")));
                assert_eq!(q.2, 0);
                assert_eq!(q.3, 0);
            }
            None => panic!("the block has one former and one constructor"),
        }
        // a second constructor takes it to the general arm
        let mut block2: Vec<ConstantInfo> = Vec::new();
        block2.push(env::constant_info_dup(&block[0]));
        block2.push(env::constant_info_dup(&block[1]));
        block2.push(ConstantInfo::CtorInfo(
            ConstantVal {
                name: nm("Rmk2"),
                level_params: Vec::new(),
                ty: expr::mk_const(name::dup(&t), Vec::new()),
            },
            0,
            0,
        ));
        block2.push(env::constant_info_dup(&block[2]));
        assert!(single_ind_ctor(&block2).is_none());
    }
}
