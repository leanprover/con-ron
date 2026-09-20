//! `arena::inductives` — the inductive block's dispatch.
//!
//! The Rust twin of `proof/ConRon/Arena/Inductives.lean`: the `.indDecl` arm of
//! con-leche's `checkDecl` (`ConLeche/Kernel/Checker.lean:566-609`), from the
//! declared parameter count down to the two routes.  This is the single entry
//! point `arena::checker`'s declaration checker calls, and everything in
//! `arena::inductives::*` is what it calls.
//!
//! What is NOT here is the **pinned basis block** (`basisPinHit`): a stream's
//! `Nat` block arrives as an ordinary `indDecl` and is recognised before this,
//! in the declaration checker, because its install is `checkBasisDecl`'s and
//! not an inductive route's.  con-leche's `checkDecl` makes that test first and
//! only then reaches the two clauses below; the arena's does the same.
//!
//! | Rust | Lean twin |
//! |---|---|
//! | `struct_parts` | `Arena/Inductives/StructParts.lean` |
//! | `sum_parts` | `Arena/Inductives/SumParts.lean` |
//! | `modeled` | `Arena/Inductives/Modeled.lean` |
//! | `struct_install` | `Arena/Inductives/StructInstall.lean` |
//! | `struct_install_f` | `Arena/Inductives/StructInstallF.lean` |
//! | `sum_install` | `Arena/Inductives/SumInstall.lean` |
//! | `sum_install_f` | `Arena/Inductives/SumInstallF.lean` |
//! | `native_parts` | `Arena/Inductives/NativeParts.lean` |
//! | `native_install` | `Arena/Inductives/NativeInstall.lean` |
//! | `native_install_f` | `Arena/Inductives/NativeInstallF.lean` |
//!
//! The declaration checker's own helpers — `unwrapOr`, `checkConstantVal`,
//! `allLevelParamsDefined`, `constsResolveFFast`, `openPisAtFvarsF`,
//! `domsMatchAux`, the three list checks, `isEqHead`, `IFEnv.findCV?`,
//! `checkProjShape`, `checkProjRule`, `isRecInfo`, `recsFormSuffix`,
//! `indParamsOk` — are `arena::checker_base`'s, the whole-constant
//! comparisons `arena::canon`'s, the interning converters `arena::intern`'s
//! and the pinned `Eq` basis `arena::std_axioms`'s.  While the two halves of
//! P4d ran concurrently this module carried a borrowed copy of them
//! (`arena::inductives::ind_base`, as the Lean carried
//! `Arena/Inductives/Base.lean`); the merge deleted both.

pub mod modeled;
pub mod native_install;
pub mod native_install_f;
pub mod native_parts;
pub mod struct_install;
pub mod struct_install_f;
pub mod struct_parts;
pub mod sum_install;
pub mod sum_install_f;
pub mod sum_parts;

use crate::arena::checker_base;
use crate::arena::env::{IConstantInfo, IFEnv};
use crate::arena::monad::{fail, AState};
use con_ron_core::kernel::core_types;
use con_ron_core::kernel::core_types::{code_points, CheckError};
use con_ron_core::kernel::env::CheckMode;

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `'number of parameters mismatch'`, as code points —
/// `con_ron_core::cached::parsed_c::check_ind_decl_route_c`'s own, so the
/// differential test can compare error text.
pub const M_NUM_PARAMS: [u32; 29] = [
    110, 117, 109, 98, 101, 114, 32, 111, 102, 32, 112, 97, 114, 97, 109, 101, 116, 101, 114, 115,
    32, 109, 105, 115, 109, 97, 116, 99, 104,
];

/// con-leche: ConLeche/Kernel/Checker.lean:440-609 checkDecl
/// Lean twin: `proof/ConRon/Arena/Inductives.lean:38-44 checkIndDecl` — the
/// `.indDecl` arm: **the declared parameter count first, and for both routes**
/// (con-leche's task #228; `indParamsOk` is official's own check, one-sided,
/// so a `false` is official's reject), then ONE ROUTE (task #210) — the
/// fixpoint route takes every block its recogniser recognises, and everything
/// else is the modeled path's, which DECLINES, naming the block, when there is
/// no model.  The dispatch is the RECOGNISER alone (task #219): a mutual or
/// nested block carries several type formers, resp. several recursors, so
/// `sumSplit` refuses it outright and no model lookup is needed to route it.
///
/// The signature is the one the coordinator froze for the two halves of P4d,
/// with the state first as `arena::monad`'s convention has it.
pub fn check_ind_decl(
    mode: CheckMode,
    fe: IFEnv,
    block: Vec<IConstantInfo>,
    num_params: u64,
    st: &mut AState,
) -> Result<IFEnv, CheckError> {
    match checker_base::ind_params_ok(st, num_params, &block, 0) {
        Err(e) => Err(e),
        Ok(false) => fail(core_types::invalid(code_points(&M_NUM_PARAMS))),
        Ok(true) => match native_parts::native_parts(st, num_params, &block) {
            Err(e) => Err(e),
            Ok(Some(p)) => native_install::check_native(st, &mode, &fe, &p),
            Ok(None) => modeled::check_modeled(st, &mode, fe, &block),
        },
    }
}

// ---------------------------------------------------------------------------
// The differential test (`proof/ConRon/Arena/InductivesTest.lean`)
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::arena::env::{
        i_constant_info_name, mk_ifenv, IConstantVal, IEnv, IIndCaps, IProjTable, IRecRule,
        IRecRuleFire,
    };
    use crate::arena::handle::{EIdx, NIdx};
    use crate::arena::monad::{intern_level, intern_name};
    use crate::arena::store::EStore;
    use con_ron_core::cached::parsed_c;
    use con_ron_core::cached::state_c;
    use con_ron_core::cached::state_c::CState;
    use con_ron_core::kernel::core_types::CheckM;
    use con_ron_core::kernel::env as cenv;
    use con_ron_core::kernel::env::{
        ConstantInfo, ConstantVal, IndCaps, ProjTable, RecRule, RecRuleFire, ReducibilityHint,
    };
    use con_ron_core::kernel::expr;
    use con_ron_core::kernel::expr::{BinderMeta, Expr};
    use con_ron_core::kernel::fenv;
    use con_ron_core::kernel::fenv::FEnv;
    use con_ron_core::kernel::inductives::native_parts as cnp;
    use con_ron_core::kernel::level as clevel;
    use con_ron_core::kernel::level::Level;
    use con_ron_core::kernel::name as cname;
    use con_ron_core::kernel::name::Name;
    use con_ron_core::kernel::prop_when;
    use con_ron_core::ron::hashmap::Eq2;

    // --- the con-leche → handle converters (the twin's `iE`/`iCV`/`iCI`) ----

    fn ok<T>(r: Result<T, CheckError>) -> T {
        match r {
            Ok(x) => x,
            Err(_) => panic!("the fixture must build without a decline"),
        }
    }

    fn intern_expr(st: &mut AState, e: &Expr) -> EIdx {
        ok(crate::arena::intern::intern_expr(st, e))
    }

    fn intern_names(st: &mut AState, ns: &Vec<Name>) -> Vec<NIdx> {
        ns.iter().map(|n| ok(intern_name(st, n))).collect()
    }

    fn intern_cv(st: &mut AState, cv: &ConstantVal) -> IConstantVal {
        ok(crate::arena::intern::intern_cv(st, cv))
    }

    fn intern_caps(st: &mut AState, c: &IndCaps) -> IIndCaps {
        ok(crate::arena::intern::intern_caps(st, c))
    }

    fn intern_fire(st: &mut AState, f: &RecRuleFire) -> IRecRuleFire {
        match f {
            RecRuleFire::Inert => IRecRuleFire::Inert,
            RecRuleFire::Plain => IRecRuleFire::Plain,
            RecRuleFire::Nested(lvls, pins) => IRecRuleFire::Nested(
                lvls.iter().map(|l| ok(intern_level(st, l))).collect(),
                pins.iter().map(|p| intern_expr(st, p)).collect(),
            ),
        }
    }

    fn intern_rule(st: &mut AState, r: &RecRule) -> IRecRule {
        IRecRule {
            ctor: ok(intern_name(st, &r.ctor)),
            nfields: r.nfields,
            ctor_params: r.ctor_params,
            fire: intern_fire(st, &r.fire),
            rhs: intern_expr(st, &r.rhs),
            k: r.k,
            eta: r.eta,
            params_blind: r.params_blind,
        }
    }

    /// The twin's `iTbl`.  `IProjTable.table_name` is the field `arena::env`
    /// adds: the reserved name the install interned, which is by construction
    /// `proj_table_name struct_name`.
    fn intern_tbl(st: &mut AState, t: &ProjTable) -> IProjTable {
        let sn = ok(intern_name(st, &t.struct_name));
        let tn = ok(crate::arena::env::proj_table_name(&mut st.store, &sn));
        IProjTable {
            struct_name: sn,
            table_name: tn,
            level_params: intern_names(st, &t.level_params),
            num_params: t.num_params,
            ctor: ok(intern_name(st, &t.ctor)),
            num_fields: t.num_fields,
            struct_sort: ok(intern_level(st, &t.struct_sort)),
            bodies: t.bodies.iter().map(|b| intern_expr(st, b)).collect(),
            guards: t.guards.iter().map(|g| ok(intern_level(st, g))).collect(),
            off: t.off,
        }
    }

    fn intern_ci(st: &mut AState, c: &ConstantInfo) -> IConstantInfo {
        match c {
            ConstantInfo::AxiomInfo(cv) => IConstantInfo::AxiomInfo(intern_cv(st, cv)),
            ConstantInfo::DefnInfo(cv, v, h) => {
                let icv = intern_cv(st, cv);
                let iv = intern_expr(st, v);
                IConstantInfo::DefnInfo(icv, iv, cenv::reducibility_hint_dup(h))
            }
            ConstantInfo::ThmInfo(cv, v) => {
                let icv = intern_cv(st, cv);
                let iv = intern_expr(st, v);
                IConstantInfo::ThmInfo(icv, iv)
            }
            ConstantInfo::IndInfo(cv, caps) => {
                let icv = intern_cv(st, cv);
                let ic = intern_caps(st, caps);
                IConstantInfo::IndInfo(icv, ic)
            }
            ConstantInfo::CtorInfo(cv, n_p, n_f) => {
                IConstantInfo::CtorInfo(intern_cv(st, cv), *n_p, *n_f)
            }
            ConstantInfo::RecInfo(cv, m_i, r_p, rules) => {
                let icv = intern_cv(st, cv);
                let irs = rules.iter().map(|r| intern_rule(st, r)).collect();
                IConstantInfo::RecInfo(icv, *m_i, *r_p, irs)
            }
            ConstantInfo::ProjInfo(t) => IConstantInfo::ProjInfo(intern_tbl(st, t)),
        }
    }

    // --- running the two checkers (the twin's `chk`) ------------------------

    /// The twin's `MU`: the bridge is stated at `.verified` (DESIGN.md §8.2).
    fn mode() -> CheckMode {
        CheckMode::Verified
    }

    /// con-ron-core's executed `.indDecl` arm — the cached driver, which is
    /// what the binary runs (`kernel::checker::check_ind_decl_route` is the
    /// stub that declines `Native`).  It tests `basisPinHit` first, exactly as
    /// the twin's `ConLeche.checkDecl` does.
    fn expect(base: &Vec<ConstantInfo>, block: &Vec<ConstantInfo>, n_p: u64) -> CheckM<FEnv> {
        let mut cst: CState = state_c::cstate_new();
        let cfe: FEnv = fenv::mk_fenv(cenv::env_of(base));
        parsed_c::check_ind_decl_c(&mode(), &mut cst, cfe, block, n_p)
    }

    /// The twin's `errEq`: kind AND message.  The arena's `CheckError` has a
    /// fourth constructor (`.native`, the store's capacity limit), which no
    /// con-ron-core error of this arm can meet.
    fn err_eq(a: &CheckError, b: &CheckError) -> bool {
        match (a, b) {
            (CheckError::NotImplemented(x), CheckError::NotImplemented(y)) => x == y,
            (CheckError::Invalid(x), CheckError::Invalid(y)) => x == y,
            (CheckError::Internal(x), CheckError::Internal(y)) => x == y,
            _ => false,
        }
    }

    /// **The differential**: con-ron-core's `.indDecl` arm at `base`, against
    /// the arena's `check_ind_decl` on the interned block at the interned
    /// `base`, over the WHOLE outcome.  An `ok` must meet an `ok` at the same
    /// environment — the expected one is interned INTO THE ARENA'S OWN STORE,
    /// after the run, so the comparison is handle equality, which is sound
    /// because `intern` is hash-consing and `denoteE` is injective (task #97a).
    fn chk(base: &Vec<ConstantInfo>, block: &Vec<ConstantInfo>, n_p: u64) -> bool {
        let want = expect(base, block, n_p);
        let mut st = AState::init(EStore::empty());
        // `IEnv.consts` is oldest-first here and the cited list is
        // newest-first, so the base is interned back to front (`env_of` does
        // the same on con-ron-core's side)
        let mut ics: Vec<IConstantInfo> = Vec::new();
        for c in base.iter().rev() {
            let ic = intern_ci(&mut st, c);
            ics.push(ic);
        }
        let fe = mk_ifenv(IEnv { consts: ics });
        let iblock: Vec<IConstantInfo> = block.iter().map(|c| intern_ci(&mut st, c)).collect();
        let got = check_ind_decl(mode(), fe, iblock, n_p, &mut st);
        match (got, want) {
            (Ok(fe2), Ok(wfe)) => {
                let wics: Vec<IConstantInfo> = wfe
                    .env
                    .consts
                    .iter()
                    .map(|c| intern_ci(&mut st, c))
                    .collect();
                fe2.env.consts.len() == wics.len()
                    && fe2
                        .env
                        .consts
                        .iter()
                        .zip(wics.iter())
                        .all(|(a, b)| crate::arena::canon::i_constant_info_beq(a, b))
            }
            (Err(a), Err(b)) => err_eq(&a, &b),
            _ => false,
        }
    }

    /// The twin's `accepts`: does con-ron-core ACCEPT this block?  Used to pin
    /// the positive fixtures, so that `chk` cannot pass vacuously on two
    /// agreeing errors.
    fn accepts(base: &Vec<ConstantInfo>, block: &Vec<ConstantInfo>, n_p: u64) -> bool {
        expect(base, block, n_p).is_ok()
    }

    /// The twin's `hasTable`: does the run install a projection TABLE?
    fn has_table(base: &Vec<ConstantInfo>, block: &Vec<ConstantInfo>, n_p: u64) -> bool {
        match expect(base, block, n_p) {
            Ok(fe) => fe
                .env
                .consts
                .iter()
                .any(|c| matches!(&**c, ConstantInfo::ProjInfo(_))),
            Err(_) => false,
        }
    }

    /// The twin's `installed`: how many constants the run installs.
    fn installed(base: &Vec<ConstantInfo>, block: &Vec<ConstantInfo>, n_p: u64) -> usize {
        match expect(base, block, n_p) {
            Ok(fe) => fe.env.consts.len() - base.len(),
            Err(_) => 0,
        }
    }

    // --- the fixture builder (the twin's `mkNativeBlock`) -------------------

    fn nm(s: &str) -> Name {
        cname::mk_str(cname::anonymous(), s.chars().map(|c| c as u32).collect())
    }

    fn str_of(n: &Name, s: &str) -> Name {
        cname::mk_str(cname::dup(n), s.chars().map(|c| c as u32).collect())
    }

    fn never() -> BinderMeta {
        expr::binder_meta(prop_when::never())
    }

    /// The twin's `pi`: a `∀` binder at the parse placeholder datum.
    fn pi(ty: Expr, b: Expr) -> Expr {
        expr::forall_e(ty, b, never())
    }

    /// The twin's `c0`: a constant at no universe arguments.
    fn c0(n: &Name) -> Expr {
        expr::mk_const(cname::dup(n), Vec::new())
    }

    /// The twin's `mkNativeBlock`: a block the fixpoint route recognises, with
    /// the recursor's type and rules generated by **con-ron-core's own**
    /// `structRecTyR` / `structRecRhsR` — the very terms the install
    /// fabricates and compares against, so a fixture is the block a real
    /// elaborator exports.
    fn mk_native_block(
        t: &Name,
        lps: &Vec<Name>,
        elim: &Name,
        large: bool,
        n_p: u64,
        n_idx: u64,
        tty: &Expr,
        ctors: &Vec<(Name, u64, Expr)>,
    ) -> Option<Vec<ConstantInfo>> {
        let n = ctors.len() as u64;
        let mut ctors4: Vec<(Name, u64, Expr, Vec<u64>)> = Vec::new();
        for c in ctors.iter() {
            let cv = ConstantVal {
                name: cname::dup(&c.0),
                level_params: prop_when::names_copy(lps),
                ty: expr::dup(&c.2),
            };
            let ks = cnp::rec_ctor_kinds(t, lps, n_p, n_idx, &(cv, c.1))?;
            ctors4.push((cname::dup(&c.0), c.1, expr::dup(&c.2), cnp::rec_idx_of(&ks)));
        }
        let rec_name = str_of(t, "rec");
        let mut rlps: Vec<Name> = Vec::new();
        if large {
            rlps.push(cname::dup(elim));
        }
        for l in lps.iter() {
            rlps.push(cname::dup(l));
        }
        let rlvls: Vec<Level> = rlps.iter().map(|l| clevel::param(cname::dup(l))).collect();
        let rec_ty = cnp::struct_rec_ty_r(t, lps, elim, large, n_p, n_idx, tty, &ctors4)?;
        let mut rules: Vec<RecRule> = Vec::new();
        for j in 0..n {
            let rhs = cnp::struct_rec_rhs_r(
                t, lps, elim, large, n_p, n_idx, tty, &ctors4, &rec_name, &rlvls, j,
            )?;
            rules.push(cenv::rec_rule_parsed(
                cname::dup(&ctors[j as usize].0),
                ctors[j as usize].1,
                rhs,
            ));
        }
        let r_p = n_p + 1 + n;
        let mut out: Vec<ConstantInfo> = Vec::new();
        out.push(ConstantInfo::IndInfo(
            ConstantVal {
                name: cname::dup(t),
                level_params: prop_when::names_copy(lps),
                ty: expr::dup(tty),
            },
            cenv::ind_caps_default(),
        ));
        for c in ctors.iter() {
            out.push(ConstantInfo::CtorInfo(
                ConstantVal {
                    name: cname::dup(&c.0),
                    level_params: prop_when::names_copy(lps),
                    ty: expr::dup(&c.2),
                },
                n_p,
                c.1,
            ));
        }
        out.push(ConstantInfo::RecInfo(
            ConstantVal {
                name: rec_name,
                level_params: rlps,
                ty: rec_ty,
            },
            r_p + n_idx,
            r_p,
            rules,
        ));
        Some(out)
    }

    /// The twin's `orEmpty`: an empty block stands in when a generator
    /// declines; the `chk` on it is still a differential.
    fn or_empty(o: Option<Vec<ConstantInfo>>) -> Vec<ConstantInfo> {
        o.unwrap_or_default()
    }

    // --- the twelve fixtures -----------------------------------------------

    /// Fixture 1: `N`, the `Nat` shape — two constructors, one recursive.
    fn nat_block() -> Vec<ConstantInfo> {
        let n = nm("N");
        let t = c0(&n);
        or_empty(mk_native_block(
            &n,
            &Vec::new(),
            &nm("u"),
            true,
            0,
            0,
            &expr::sort(clevel::succ(clevel::zero())),
            &vec![
                (str_of(&n, "zero"), 0, expr::dup(&t)),
                (str_of(&n, "succ"), 1, pi(expr::dup(&t), expr::dup(&t))),
            ],
        ))
    }

    /// Fixture 2: `Lst.{u} (α : Type u) : Type u`, parametric and recursive.
    fn lst_block() -> Vec<ConstantInfo> {
        let n = nm("Lst");
        let uu = nm("u");
        let t_u = expr::sort(clevel::succ(clevel::param(cname::dup(&uu))));
        let lst_at = |k: u64| {
            expr::app(
                expr::mk_const(cname::dup(&n), vec![clevel::param(cname::dup(&uu))]),
                expr::bvar(k),
            )
        };
        or_empty(mk_native_block(
            &n,
            &vec![cname::dup(&uu)],
            &nm("v"),
            true,
            1,
            0,
            &pi(expr::dup(&t_u), expr::dup(&t_u)),
            &vec![
                (str_of(&n, "nil"), 0, pi(expr::dup(&t_u), lst_at(0))),
                (
                    str_of(&n, "cons"),
                    2,
                    pi(expr::dup(&t_u), pi(expr::bvar(0), pi(lst_at(1), lst_at(2)))),
                ),
            ],
        ))
    }

    /// Fixture 3: `Pair.{u} (α β : Sort u)`, a two-field structure.
    fn pair_block() -> Vec<ConstantInfo> {
        let n = nm("Pair");
        let uu = nm("u");
        let s_u = expr::sort(clevel::param(cname::dup(&uu)));
        let pr_at = |a: u64, b: u64| {
            expr::app(
                expr::app(
                    expr::mk_const(cname::dup(&n), vec![clevel::param(cname::dup(&uu))]),
                    expr::bvar(a),
                ),
                expr::bvar(b),
            )
        };
        or_empty(mk_native_block(
            &n,
            &vec![cname::dup(&uu)],
            &nm("v"),
            true,
            2,
            0,
            &pi(expr::dup(&s_u), pi(expr::dup(&s_u), expr::dup(&s_u))),
            &vec![(
                str_of(&n, "mk"),
                2,
                pi(
                    expr::dup(&s_u),
                    pi(
                        expr::dup(&s_u),
                        pi(expr::bvar(1), pi(expr::bvar(1), pr_at(3, 2))),
                    ),
                ),
            )],
        ))
    }

    /// Fixture 4: `Eq'.{u} (α : Sort u) (a : α) : α → Prop`, indexed and
    /// propositional with a large eliminator.
    fn eq_block() -> Vec<ConstantInfo> {
        let n = nm("Eq'");
        let uu = nm("u");
        let s_u = expr::sort(clevel::param(cname::dup(&uu)));
        let eq_at = |a: u64, b: u64, c: u64| {
            expr::app(
                expr::app(
                    expr::app(
                        expr::mk_const(cname::dup(&n), vec![clevel::param(cname::dup(&uu))]),
                        expr::bvar(a),
                    ),
                    expr::bvar(b),
                ),
                expr::bvar(c),
            )
        };
        or_empty(mk_native_block(
            &n,
            &vec![cname::dup(&uu)],
            &nm("v"),
            true,
            2,
            1,
            &pi(
                expr::dup(&s_u),
                pi(expr::bvar(0), pi(expr::bvar(1), expr::sort(clevel::zero()))),
            ),
            &vec![(
                str_of(&n, "refl"),
                0,
                pi(expr::dup(&s_u), pi(expr::bvar(0), eq_at(1, 0, 0))),
            )],
        ))
    }

    /// Fixture 5: `Tru : Prop` with one fieldless constructor.
    fn tru_block() -> Vec<ConstantInfo> {
        let n = nm("Tru");
        or_empty(mk_native_block(
            &n,
            &Vec::new(),
            &nm("u"),
            true,
            0,
            0,
            &expr::sort(clevel::zero()),
            &vec![(str_of(&n, "intro"), 0, c0(&n))],
        ))
    }

    /// Fixture 6: the base environment of the MUTUAL fixture — the two
    /// `_model` companions, as ordinary definitions.
    fn mut_base() -> Vec<ConstantInfo> {
        let a = nm("MutA");
        let b = nm("MutB");
        let ty1 = expr::sort(clevel::succ(clevel::zero()));
        vec![
            ConstantInfo::DefnInfo(
                ConstantVal {
                    name: str_of(&b, "_model"),
                    level_params: Vec::new(),
                    ty: expr::dup(&ty1),
                },
                expr::sort(clevel::zero()),
                ReducibilityHint::Regular(1),
            ),
            ConstantInfo::DefnInfo(
                ConstantVal {
                    name: str_of(&a, "_model"),
                    level_params: Vec::new(),
                    ty: ty1,
                },
                expr::sort(clevel::zero()),
                ReducibilityHint::Regular(1),
            ),
        ]
    }

    /// Fixture 6: the mutual block — two type formers, no recursor.
    fn mut_block() -> Vec<ConstantInfo> {
        let ty1 = expr::sort(clevel::succ(clevel::zero()));
        vec![
            ConstantInfo::IndInfo(
                ConstantVal {
                    name: nm("MutA"),
                    level_params: Vec::new(),
                    ty: expr::dup(&ty1),
                },
                cenv::ind_caps_default(),
            ),
            ConstantInfo::IndInfo(
                ConstantVal {
                    name: nm("MutB"),
                    level_params: Vec::new(),
                    ty: ty1,
                },
                cenv::ind_caps_default(),
            ),
        ]
    }

    /// Fixture 7: a NESTED-shaped block — one former, one constructor, TWO
    /// recursor records.
    fn nest_block() -> Vec<ConstantInfo> {
        let n = nm("Nest");
        let rec_ty = pi(c0(&n), expr::sort(clevel::zero()));
        vec![
            ConstantInfo::IndInfo(
                ConstantVal {
                    name: cname::dup(&n),
                    level_params: Vec::new(),
                    ty: expr::sort(clevel::succ(clevel::zero())),
                },
                cenv::ind_caps_default(),
            ),
            ConstantInfo::CtorInfo(
                ConstantVal {
                    name: str_of(&n, "mk"),
                    level_params: Vec::new(),
                    ty: c0(&n),
                },
                0,
                0,
            ),
            ConstantInfo::RecInfo(
                ConstantVal {
                    name: str_of(&n, "rec"),
                    level_params: Vec::new(),
                    ty: expr::dup(&rec_ty),
                },
                1,
                1,
                Vec::new(),
            ),
            ConstantInfo::RecInfo(
                ConstantVal {
                    name: str_of(&n, "rec_1"),
                    level_params: Vec::new(),
                    ty: rec_ty,
                },
                1,
                1,
                Vec::new(),
            ),
        ]
    }

    /// Fixture 9: `Bad : Type` with `Bad.mk : (Bad → Bad) → Bad`.
    fn bad_block() -> Vec<ConstantInfo> {
        let n = nm("Bad");
        or_empty(mk_native_block(
            &n,
            &Vec::new(),
            &nm("u"),
            true,
            0,
            0,
            &expr::sort(clevel::succ(clevel::zero())),
            &vec![(str_of(&n, "mk"), 1, pi(pi(c0(&n), c0(&n)), c0(&n)))],
        ))
    }

    /// Fixture 10: the `N` block with both constructors under one name.
    fn dup_block() -> Vec<ConstantInfo> {
        let n = nm("N");
        let t = c0(&n);
        or_empty(mk_native_block(
            &n,
            &Vec::new(),
            &nm("u"),
            true,
            0,
            0,
            &expr::sort(clevel::succ(clevel::zero())),
            &vec![
                (str_of(&n, "zero"), 0, expr::dup(&t)),
                (str_of(&n, "zero"), 1, pi(expr::dup(&t), expr::dup(&t))),
            ],
        ))
    }

    /// Fixture 11: `N` with its recursor's rules dropped.
    fn stub_rec_block() -> Vec<ConstantInfo> {
        nat_block()
            .iter()
            .map(|c| match c {
                ConstantInfo::RecInfo(cv, m_i, r_p, _) => {
                    ConstantInfo::RecInfo(cenv::constant_val_dup(cv), *m_i, *r_p, Vec::new())
                }
                other => cenv::constant_info_dup(other),
            })
            .collect()
    }

    fn no_base() -> Vec<ConstantInfo> {
        Vec::new()
    }

    // --- the 46 checks ------------------------------------------------------

    #[test]
    fn fixture_1_the_nat_shape() {
        let b = nat_block();
        assert_eq!(b.len(), 4);
        assert!(accepts(&no_base(), &b, 0));
        // the former, the two constructors and the recursor; a two-constructor
        // block is not structure-like, so no projection table
        assert_eq!(installed(&no_base(), &b, 0), 4);
        assert!(!has_table(&no_base(), &b, 0));
        assert!(chk(&no_base(), &b, 0));
    }

    #[test]
    fn fixture_2_a_parametric_recursive_family() {
        let b = lst_block();
        assert_eq!(b.len(), 4);
        assert!(accepts(&no_base(), &b, 1));
        assert_eq!(installed(&no_base(), &b, 1), 4);
        assert!(!has_table(&no_base(), &b, 1));
        assert!(chk(&no_base(), &b, 1));
    }

    #[test]
    fn fixture_3_a_two_field_structure_and_its_table() {
        let b = pair_block();
        assert_eq!(b.len(), 3);
        assert!(accepts(&no_base(), &b, 2));
        // four installs: the former, the constructor, the recursor and the
        // projection TABLE (`off = 1`, two guard levels, one body per field)
        assert_eq!(installed(&no_base(), &b, 2), 4);
        assert!(has_table(&no_base(), &b, 2));
        assert!(chk(&no_base(), &b, 2));
    }

    #[test]
    fn fixture_4_an_indexed_propositional_family() {
        let b = eq_block();
        assert_eq!(b.len(), 3);
        assert!(accepts(&no_base(), &b, 2));
        // an INDEXED family is not structure-like: no projection table
        assert_eq!(installed(&no_base(), &b, 2), 3);
        assert!(!has_table(&no_base(), &b, 2));
        assert!(chk(&no_base(), &b, 2));
    }

    #[test]
    fn fixture_5_a_prop_with_one_fieldless_constructor() {
        let b = tru_block();
        assert_eq!(b.len(), 3);
        assert!(accepts(&no_base(), &b, 0));
        assert_eq!(installed(&no_base(), &b, 0), 4);
        assert!(has_table(&no_base(), &b, 0));
        assert!(chk(&no_base(), &b, 0));
    }

    #[test]
    fn fixture_6_a_mutual_block_through_the_modelled_route() {
        let base = mut_base();
        let b = mut_block();
        assert!(accepts(&base, &b, 0));
        assert_eq!(installed(&base, &b, 0), 2);
        assert!(chk(&base, &b, 0));
        // the same block with NO models: the modelled route declines, naming
        // the block
        assert!(!accepts(&no_base(), &b, 0));
        assert!(chk(&no_base(), &b, 0));
    }

    #[test]
    fn fixture_7_a_nested_block_through_the_modelled_route() {
        let b = nest_block();
        assert!(!accepts(&no_base(), &b, 0));
        assert!(chk(&no_base(), &b, 0));
    }

    #[test]
    fn fixture_8_the_declared_parameter_count() {
        let n = nat_block();
        assert!(!accepts(&no_base(), &n, 3));
        assert!(chk(&no_base(), &n, 3));
        let l = lst_block();
        assert!(!accepts(&no_base(), &l, 2));
        assert!(chk(&no_base(), &l, 2));
    }

    #[test]
    fn fixture_9_a_non_positive_occurrence() {
        let b = bad_block();
        assert_eq!(b.len(), 3);
        assert!(!accepts(&no_base(), &b, 0));
        assert!(chk(&no_base(), &b, 0));
    }

    #[test]
    fn fixture_10_a_duplicate_constructor_name() {
        let b = dup_block();
        assert_eq!(b.len(), 4);
        assert!(!accepts(&no_base(), &b, 0));
        assert!(chk(&no_base(), &b, 0));
    }

    #[test]
    fn fixture_11_a_recursor_record_that_is_not_the_generated_one() {
        let b = stub_rec_block();
        assert!(!accepts(&no_base(), &b, 0));
        assert!(chk(&no_base(), &b, 0));
    }

    #[test]
    fn fixture_12_a_member_redeclaring_a_stored_name() {
        let b = nat_block();
        let base = nat_block();
        assert!(!accepts(&base, &b, 0));
        assert!(chk(&base, &b, 0));
    }

    /// Beyond the twin: the interned environment the arena installs is
    /// compared handle for handle, so a `chk` that passed must ALSO have
    /// interned every name the differential names.  This pins the one thing a
    /// vacuous comparison could hide — that `i_constant_info_name` of the two
    /// lists agrees position by position.
    #[test]
    fn the_installed_names_line_up() {
        let b = pair_block();
        let mut st = AState::init(EStore::empty());
        let fe = mk_ifenv(IEnv { consts: Vec::new() });
        let iblock: Vec<IConstantInfo> = b.iter().map(|c| intern_ci(&mut st, c)).collect();
        let got = match check_ind_decl(mode(), fe, iblock, 2, &mut st) {
            Ok(x) => x,
            Err(_) => panic!("Pair installs"),
        };
        let want = match expect(&no_base(), &b, 2) {
            Ok(x) => x,
            Err(_) => panic!("Pair installs"),
        };
        let wics: Vec<IConstantInfo> = want
            .env
            .consts
            .iter()
            .map(|c| intern_ci(&mut st, c))
            .collect();
        assert_eq!(got.env.consts.len(), wics.len());
        for (a, w) in got.env.consts.iter().zip(wics.iter()) {
            assert!(i_constant_info_name(a).eq2(&i_constant_info_name(w)));
        }
    }
}
