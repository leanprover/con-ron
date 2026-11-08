//! `arena::basis` — the pinned basis blocks, over handles.
//!
//! The Rust twin of `proof/ConRon/Arena/Basis.lean`, which is con-leche's
//! `Kernel/Basis.lean`: the constants of the five pinned blocks (`Eq`, `Nat`,
//! `Empty`, `False`, `Quot`), a pin at a stream's level-parameter names
//! (`constant_info_at_lps`), the block's comparison with its pin
//! (`pin_list_ok`), the name test that says a record is a pinned block's
//! (`basis_name_hit`), the reserved names' check run after a declaration's own
//! checks (`basis_names_ok`, `basis_names_error`), what a quotient record
//! stores (`quot_at`), and the fold's `And` pin (`and_pin_ok`):
//! a record that declares `And`, `And.intro` or `And.rec` and is not the
//! toolchain's block is rejected.
//!
//! **The pins are values, interned** (`arena::intern`'s module note): the Lean
//! twin interns con-leche's `BasisKind.decls`, the Rust interns
//! `con_ron_core::kernel::basis_raw::basis_kind_decls`, which is the same block
//! hand-ported from the same builder.
//!
//! **Two lists for a function.**  Each `List.map`, `List.zip … |>.all`,
//! `List.find?` and `listBeqBy` of the cited code is a cursor recursion here
//! (§3.4 forbids the closure), named after the function it belongs to.

use crate::arena::canon::{i_constant_info_beq, i_constant_val_beq, nidx_vec_beq};
use crate::arena::checker_base::name_nodup;
use crate::arena::core::{reserved_basis_names, subst_levels_at, CORE_WALK_FUEL};
use crate::arena::env::{
    i_constant_info_dummy, i_constant_info_dup, i_constant_info_name,
    i_constant_info_to_constant_val, i_ind_caps_dup, i_rec_rule_fire_dup, ifenv_find,
    nidx_vec_contains, nidx_vec_dup, IConstantInfo, IConstantVal, IDeclaration, IFEnv, IRecRule,
    IRecRuleFire,
};
use crate::arena::expr_ops::inst_lp_fast;
use crate::arena::inductives::struct_parts::param_levels;
use crate::arena::handle::{LsIdx, NIdx};
use crate::arena::intern::{intern_ci, intern_ci_list};
use crate::arena::monad::{read_names_m, AState};
use crate::arena::pins::{pin_eq, pin_quot, pin_quot_mk, pin_quot_sound};
use crate::arena::store::PersTier;
use crate::kernel::basis_raw;
use crate::kernel::core_types::{code_points, CheckError};
use crate::kernel::env as cenv;
use crate::kernel::env::{BasisKind, QuotKind};
use crate::kernel::level;
use crate::kernel::level::Level;
use crate::kernel::name::Name;
use crate::ron::hashmap::{Dup, Eq2};

/// con-leche: ConLeche/Kernel/Basis.lean:39-45 BasisKind.decls
/// Lean twin: `proof/ConRon/Arena/Basis.lean:37-40 BasisKind.decls` — the constants
/// of one basis block, in install order, interned.
pub fn basis_kind_decls(
    pers: &PersTier,
    st: &mut AState,
    k: &BasisKind,
) -> Result<Vec<IConstantInfo>, CheckError> {
    intern_ci_list(pers, st, &basis_raw::basis_kind_decls(k))
}

/// con-leche: ConLeche/Kernel/Basis/Nat.lean:24-26 natA
/// The pinned `Nat` type former, interned: its `ConstantVal` is the comparand
/// of `reduceElemOk`'s `ConstantVal.matchesPin`.
pub fn nat_a(pers: &PersTier, st: &mut AState) -> Result<IConstantInfo, CheckError> {
    intern_ci(pers, st, &basis_raw::nat_a())
}

// ---------------------------------------------------------------------------
// A pin at a stream's level-parameter names
// ---------------------------------------------------------------------------

/// con-leche: none — `ps.map Level.param` over read-back names
/// The transient levels `.param p`, for `Level.subst`'s substitution list.
pub fn param_level_values(ps: &Vec<Name>, i: usize, out: Vec<Level>) -> Vec<Level> {
    if i >= ps.len() {
        out
    } else {
        let mut out2 = out;
        out2.push(level::param(crate::kernel::name::dup(&ps[i])));
        param_level_values(ps, i + 1, out2)
    }
}

/// con-leche: ConLeche/Kernel/Basis.lean:54-56 ConstantVal.atLps
/// Lean twin: `proof/ConRon/Arena/Basis.lean:51-57 IConstantVal.atLps` — a constant's
/// common data at other level-parameter names: the type with the old names
/// replaced positionally.
pub fn constant_val_at_lps(
    pers: &PersTier,
    st: &mut AState,
    cv: &IConstantVal,
    ps: &Vec<NIdx>,
) -> Result<IConstantVal, CheckError> {
    match param_levels(pers, st, ps) {
        Err(e) => Err(e),
        Ok(us) => match inst_lp_fast(pers, st, CORE_WALK_FUEL, &cv.level_params, &us, &cv.ty) {
            Err(e) => Err(e),
            Ok(ty) => Ok(IConstantVal {
                name: cv.name.dup2(),
                level_params: nidx_vec_dup(ps),
                ty,
            }),
        },
    }
}

/// con-leche: ConLeche/Kernel/Basis.lean:58-61 RecRuleFire.atLps
/// Lean twin: `proof/ConRon/Arena/Basis.lean:59-65 IRecRuleFire.atLps` — a firing mode
/// at other level-parameter names: the `.levels` comparands substituted, every
/// other mode as it is.
pub fn rec_rule_fire_at_lps(
    pers: &PersTier,
    st: &mut AState,
    lps: &Vec<Name>,
    us: &Vec<Level>,
    f: &IRecRuleFire,
) -> Result<IRecRuleFire, CheckError> {
    match f {
        IRecRuleFire::Levels(lvls) => match subst_levels_at(pers, st, lps, us, lvls, 0, Vec::new()) {
            Err(e) => Err(e),
            Ok(lvls2) => Ok(IRecRuleFire::Levels(lvls2)),
        },
        _ => Ok(i_rec_rule_fire_dup(f)),
    }
}

/// con-leche: ConLeche/Kernel/Basis.lean:63-79 ConstantInfo.atLps
/// Lean twin: `proof/ConRon/Arena/Basis.lean:67-78 rulesAtLps` — the
/// `.recInfo` arm's `rules.map`: each rule's right-hand side and firing mode at
/// the new names.  `lps_h`/`us` are the cited `lps`/`us` as handles (for
/// `instantiateLevelParams`), `lps_t`/`us_t` as read-back values (for
/// `Level.subst`).
pub fn rules_at_lps(
    pers: &PersTier,
    st: &mut AState,
    lps_h: &Vec<NIdx>,
    us: &LsIdx,
    lps_t: &Vec<Name>,
    us_t: &Vec<Level>,
    rules: &Vec<IRecRule>,
    i: usize,
    out: Vec<IRecRule>,
) -> Result<Vec<IRecRule>, CheckError> {
    if i >= rules.len() {
        Ok(out)
    } else {
        match inst_lp_fast(pers, st, CORE_WALK_FUEL, lps_h, us, &rules[i].rhs) {
            Err(e) => Err(e),
            Ok(rhs) => match rec_rule_fire_at_lps(pers, st, lps_t, us_t, &rules[i].fire) {
                Err(e) => Err(e),
                Ok(fire) => {
                    let mut out2 = out;
                    out2.push(IRecRule {
                        ctor: rules[i].ctor.dup2(),
                        nfields: rules[i].nfields,
                        fire,
                        rhs,
                    });
                    rules_at_lps(pers, st, lps_h, us, lps_t, us_t, rules, i + 1, out2)
                }
            },
        }
    }
}

/// con-leche: ConLeche/Kernel/Basis.lean:63-79 ConstantInfo.atLps
/// Lean twin: `proof/ConRon/Arena/Basis.lean:80-100 IConstantInfo.atLps` — **a stored
/// constant at other level-parameter names**: its type, a definition's value,
/// its rules' right-hand sides and firing modes renamed; nothing else.
pub fn constant_info_at_lps(
    pers: &PersTier,
    st: &mut AState,
    ci: &IConstantInfo,
    ps: &Vec<NIdx>,
) -> Result<IConstantInfo, CheckError> {
    match ci {
        IConstantInfo::AxiomInfo(cv) => match constant_val_at_lps(pers, st, cv, ps) {
            Err(e) => Err(e),
            Ok(cv2) => Ok(IConstantInfo::AxiomInfo(cv2)),
        },
        IConstantInfo::DefnInfo(cv, v, h) => match constant_val_at_lps(pers, st, cv, ps) {
            Err(e) => Err(e),
            Ok(cv2) => match param_levels(pers, st, ps) {
                Err(e) => Err(e),
                Ok(us) => match inst_lp_fast(pers, st, CORE_WALK_FUEL, &cv.level_params, &us, v) {
                    Err(e) => Err(e),
                    Ok(v2) => Ok(IConstantInfo::DefnInfo(cv2, v2, cenv::reducibility_hint_dup(h))),
                },
            },
        },
        IConstantInfo::ThmInfo(cv) => match constant_val_at_lps(pers, st, cv, ps) {
            Err(e) => Err(e),
            Ok(cv2) => Ok(IConstantInfo::ThmInfo(cv2)),
        },
        IConstantInfo::IndInfo(cv, caps) => match constant_val_at_lps(pers, st, cv, ps) {
            Err(e) => Err(e),
            Ok(cv2) => Ok(IConstantInfo::IndInfo(cv2, i_ind_caps_dup(caps))),
        },
        IConstantInfo::CtorInfo(cv, n_p, n_f) => match constant_val_at_lps(pers, st, cv, ps) {
            Err(e) => Err(e),
            Ok(cv2) => Ok(IConstantInfo::CtorInfo(cv2, *n_p, *n_f)),
        },
        IConstantInfo::RecInfo(cv, m_i, r_p, is_k, rules) => {
            constant_info_at_lps_rec(pers, st, cv, *m_i, *r_p, *is_k, rules, ps)
        }
    }
}

/// con-leche: ConLeche/Kernel/Basis.lean:63-79 ConstantInfo.atLps
/// Lean twin: `proof/ConRon/Arena/Basis.lean:80-100 IConstantInfo.atLps` — the
/// `.recInfo` arm.
pub fn constant_info_at_lps_rec(
    pers: &PersTier,
    st: &mut AState,
    cv: &IConstantVal,
    m_i: u64,
    r_p: u64,
    is_k: bool,
    rules: &Vec<IRecRule>,
    ps: &Vec<NIdx>,
) -> Result<IConstantInfo, CheckError> {
    match constant_val_at_lps(pers, st, cv, ps) {
        Err(e) => Err(e),
        Ok(cv2) => match param_levels(pers, st, ps) {
            Err(e) => Err(e),
            Ok(us) => match read_names_m(pers, st, &cv.level_params) {
                Err(e) => Err(e),
                Ok(lps_t) => match read_names_m(pers, st, ps) {
                    Err(e) => Err(e),
                    Ok(ps_t) => {
                        let us_t: Vec<Level> = param_level_values(&ps_t, 0, Vec::new());
                        match rules_at_lps(
                            pers,
                            st,
                            &cv.level_params,
                            &us,
                            &lps_t,
                            &us_t,
                            rules,
                            0,
                            Vec::new(),
                        ) {
                            Err(e) => Err(e),
                            Ok(rules2) => Ok(IConstantInfo::RecInfo(cv2, m_i, r_p, is_k, rules2)),
                        }
                    }
                },
            },
        },
    }
}

/// con-leche: ConLeche/Kernel/Basis.lean:81-85 pinAgrees
/// Lean twin: `proof/ConRon/Arena/Basis.lean:102-107 pinAgrees` — a record against the
/// pin at the record's own names: what the record writes.  An inductive record
/// has no capabilities to compare.
pub fn pin_agrees(c: &IConstantInfo, c2: &IConstantInfo) -> bool {
    match (c, c2) {
        (IConstantInfo::IndInfo(v, _), IConstantInfo::IndInfo(v2, _)) => i_constant_val_beq(v, v2),
        _ => i_constant_info_beq(c, c2),
    }
}

/// con-leche: ConLeche/Kernel/Basis.lean:87-92 pinCopyOk
/// Lean twin: `proof/ConRon/Arena/Basis.lean:109-116 pinCopyOk` — **is the record the
/// pin, up to its level-parameter names?**  Distinct names, as many as the
/// pin's; the renaming is computed only when both hold (`&&` short-circuits).
pub fn pin_copy_ok(
    pers: &PersTier,
    st: &mut AState,
    ci: &IConstantInfo,
    pin: &IConstantInfo,
) -> Result<bool, CheckError> {
    let ps: Vec<NIdx> = i_constant_info_to_constant_val(ci).level_params;
    if name_nodup(&ps)
        && ps.len() == i_constant_info_to_constant_val(pin).level_params.len()
    {
        match constant_info_at_lps(pers, st, pin, &ps) {
            Err(e) => Err(e),
            Ok(pin2) => Ok(pin_agrees(ci, &pin2)),
        }
    } else {
        Ok(false)
    }
}

/// con-leche: ConLeche/Kernel/Basis.lean:94-99 pinLinkOk
/// Lean twin: `proof/ConRon/Arena/Basis.lean:118-127 pinLinkOk` — **what a recursor's
/// rule reads off its constructor's parameters**, by name: the constructor's
/// parameters at the recursor's names.  `C.map Level.param == Cp.map fun p =>
/// Level.subst Rp (R.map Level.param) (.param p)`, compared on read-back
/// levels.
pub fn pin_link_ok(
    pers: &PersTier,
    st: &mut AState,
    r: &Vec<NIdx>,
    rp: &Vec<NIdx>,
    c: &Vec<NIdx>,
    cp: &Vec<NIdx>,
) -> Result<bool, CheckError> {
    match read_names_m(pers, st, r) {
        Err(e) => Err(e),
        Ok(r_t) => match read_names_m(pers, st, rp) {
            Err(e) => Err(e),
            Ok(rp_t) => match read_names_m(pers, st, c) {
                Err(e) => Err(e),
                Ok(c_t) => match read_names_m(pers, st, cp) {
                    Err(e) => Err(e),
                    Ok(cp_t) => {
                        let rs: Vec<Level> = param_level_values(&r_t, 0, Vec::new());
                        let lhs: Vec<Level> = param_level_values(&c_t, 0, Vec::new());
                        let rhs: Vec<Level> = pin_link_rhs(&rp_t, &rs, &cp_t, 0, Vec::new());
                        Ok(level_list_beq(&lhs, &rhs, 0))
                    }
                },
            },
        },
    }
}

/// con-leche: ConLeche/Kernel/Basis.lean:94-99 pinLinkOk
/// The cited `Cp.map fun p => Level.subst Rp (R.map Level.param) (.param p)`,
/// as a cursor recursion.
pub fn pin_link_rhs(
    rp: &Vec<Name>,
    rs: &Vec<Level>,
    cp: &Vec<Name>,
    i: usize,
    out: Vec<Level>,
) -> Vec<Level> {
    if i >= cp.len() {
        out
    } else {
        let mut out2 = out;
        out2.push(level::subst(rp, rs, &level::param(crate::kernel::name::dup(&cp[i]))));
        pin_link_rhs(rp, rs, cp, i + 1, out2)
    }
}

/// con-leche: none — the `==` of `List Level`
/// Two level lists compared elementwise by `Level`'s structural equality.
pub fn level_list_beq(a: &Vec<Level>, b: &Vec<Level>, i: usize) -> bool {
    if i >= a.len() && i >= b.len() {
        true
    } else if i >= a.len() || i >= b.len() {
        false
    } else if level::beq(&a[i], &b[i]) {
        level_list_beq(a, b, i + 1)
    } else {
        false
    }
}

/// con-leche: ConLeche/Kernel/Basis.lean:101-103 constNamed?
/// Lean twin: `proof/ConRon/Arena/Basis.lean:129-132 constNamed?` — the constant of a
/// list by name, the first from position `i` on.  Deviation: the constant is
/// returned copied, not borrowed (a borrow handed out of the recursion is what
/// Aeneas could not translate at the caller).
pub fn const_named(cs: &Vec<IConstantInfo>, n: &NIdx, i: usize) -> Option<IConstantInfo> {
    if i >= cs.len() {
        None
    } else if i_constant_info_name(&cs[i]).eq2(n) {
        Some(crate::arena::env::i_constant_info_dup(&cs[i]))
    } else {
        const_named(cs, n, i + 1)
    }
}

/// con-leche: ConLeche/Kernel/Basis.lean:105-119 blockLinksOk
/// Lean twin: `proof/ConRon/Arena/Basis.lean:166-171 blockLinksOk` — the stream's
/// recursor links its rules' constructors as the pin's does (`pin_link_ok`),
/// and a constructor carries its former's names.  The cited `(List.zip block
/// pins).all`, as a cursor bounded by the shorter list.
pub fn block_links_ok(
    pers: &PersTier,
    st: &mut AState,
    block: &Vec<IConstantInfo>,
    pins: &Vec<IConstantInfo>,
) -> Result<bool, CheckError> {
    let former: Vec<NIdx> = if block.len() == 0 {
        Vec::new()
    } else {
        i_constant_info_to_constant_val(&block[0]).level_params
    };
    block_links_ok_go(pers, st, block, pins, &former, 0)
}

/// con-leche: ConLeche/Kernel/Basis.lean:105-119 blockLinksOk
/// Lean twin: `proof/ConRon/Arena/Basis.lean:166-171 blockLinksOk` — the pairs from
/// position `i` on.
pub fn block_links_ok_go(
    pers: &PersTier,
    st: &mut AState,
    block: &Vec<IConstantInfo>,
    pins: &Vec<IConstantInfo>,
    former: &Vec<NIdx>,
    i: usize,
) -> Result<bool, CheckError> {
    if i >= block.len() || i >= pins.len() {
        Ok(true)
    } else {
        match block_link_ok_at(pers, st, block, pins, former, &block[i], &pins[i]) {
            Err(e) => Err(e),
            Ok(false) => Ok(false),
            Ok(true) => block_links_ok_go(pers, st, block, pins, former, i + 1),
        }
    }
}

/// con-leche: ConLeche/Kernel/Basis.lean:105-119 blockLinksOk
/// Lean twin: `proof/ConRon/Arena/Basis.lean:166-171 blockLinksOk` — the cited `match
/// c, p with`, one pair.
pub fn block_link_ok_at(
    pers: &PersTier,
    st: &mut AState,
    block: &Vec<IConstantInfo>,
    pins: &Vec<IConstantInfo>,
    former: &Vec<NIdx>,
    c: &IConstantInfo,
    p: &IConstantInfo,
) -> Result<bool, CheckError> {
    match c {
        IConstantInfo::CtorInfo(cv, _, _) => Ok(nidx_vec_beq(&cv.level_params, former, 0)),
        IConstantInfo::RecInfo(cv, _, _, _, _) => match p {
            IConstantInfo::RecInfo(cvp, _, _, _, rules) => {
                rules_link_ok(pers, st, block, pins, &cv.level_params, &cvp.level_params, rules, 0)
            }
            _ => Ok(true),
        },
        _ => Ok(true),
    }
}

/// con-leche: ConLeche/Kernel/Basis.lean:105-119 blockLinksOk
/// Lean twin: `proof/ConRon/Arena/Basis.lean:166-171 blockLinksOk` — the cited
/// `rules.all`: each of the pin's rules' constructors, found in both lists,
/// linked as the pin links it.
pub fn rules_link_ok(
    pers: &PersTier,
    st: &mut AState,
    block: &Vec<IConstantInfo>,
    pins: &Vec<IConstantInfo>,
    r: &Vec<NIdx>,
    rp: &Vec<NIdx>,
    rules: &Vec<IRecRule>,
    i: usize,
) -> Result<bool, CheckError> {
    if i >= rules.len() {
        Ok(true)
    } else {
        let lps: Option<(Vec<NIdx>, Vec<NIdx>)> = match const_named(block, &rules[i].ctor, 0) {
            None => None,
            Some(cc) => match const_named(pins, &rules[i].ctor, 0) {
                None => None,
                Some(ccp) => Some((
                    i_constant_info_to_constant_val(&cc).level_params,
                    i_constant_info_to_constant_val(&ccp).level_params,
                )),
            },
        };
        match lps {
            None => Ok(false),
            Some((c, cp)) => match pin_link_ok(pers, st, r, rp, &c, &cp) {
                Err(e) => Err(e),
                Ok(false) => Ok(false),
                Ok(true) => rules_link_ok(pers, st, block, pins, r, rp, rules, i + 1),
            },
        }
    }
}

/// con-leche: ConLeche/Kernel/Canon.lean:291-295 listBeqBy
/// con-leche: ConLeche/Kernel/Basis.lean:121-123 pinListOk
/// Lean twin: `proof/ConRon/Arena/Basis.lean:182-185 pinListOk` — the cited
/// `listBeqBy pinCopyOk block pins`, at the one function it is applied to
/// (§3.4 forbids the function argument).
pub fn pin_copies_ok(
    pers: &PersTier,
    st: &mut AState,
    block: &Vec<IConstantInfo>,
    pins: &Vec<IConstantInfo>,
    i: usize,
) -> Result<bool, CheckError> {
    if i >= block.len() && i >= pins.len() {
        Ok(true)
    } else if i >= block.len() || i >= pins.len() {
        Ok(false)
    } else {
        match pin_copy_ok(pers, st, &block[i], &pins[i]) {
            Err(e) => Err(e),
            Ok(false) => Ok(false),
            Ok(true) => pin_copies_ok(pers, st, block, pins, i + 1),
        }
    }
}

/// con-leche: ConLeche/Kernel/Basis.lean:121-123 pinListOk
/// Lean twin: `proof/ConRon/Arena/Basis.lean:182-185 pinListOk` — **the block's
/// comparison with its pin** (the check phase's).
pub fn pin_list_ok(
    pers: &PersTier,
    st: &mut AState,
    block: &Vec<IConstantInfo>,
    pins: &Vec<IConstantInfo>,
) -> Result<bool, CheckError> {
    match pin_copies_ok(pers, st, block, pins, 0) {
        Err(e) => Err(e),
        Ok(false) => Ok(false),
        Ok(true) => block_links_ok(pers, st, block, pins),
    }
}

// ---------------------------------------------------------------------------
// Recognising a pinned block in a stream record
// ---------------------------------------------------------------------------

/// con-leche: none — `block.map (·.name)` (`i_constant_info_name` is pure), as a cursor
/// The names of a block's members, for `basis_name_hit`.
pub fn block_names(block: &Vec<IConstantInfo>, i: usize, out: Vec<NIdx>) -> Vec<NIdx> {
    if i >= block.len() {
        out
    } else {
        let mut out2 = out;
        out2.push(i_constant_info_name(&block[i]));
        block_names(block, i + 1, out2)
    }
}

/// con-leche: ConLeche/Kernel/Basis.lean:133-136 basisNameHit
/// Lean twin: `proof/ConRon/Arena/Basis.lean:202-206 basisNameHit` — the cited
/// `List.find?` over the four kinds, from position `i` on.
pub fn basis_name_hit_go(
    pers: &PersTier,
    st: &mut AState,
    block: &Vec<IConstantInfo>,
    ks: &Vec<BasisKind>,
    i: usize,
) -> Result<Option<BasisKind>, CheckError> {
    if i >= ks.len() {
        Ok(None)
    } else {
        match basis_kind_decls(pers, st, &ks[i]) {
            Err(e) => Err(e),
            Ok(pinned) => {
                if nidx_vec_beq(
                    &block_names(&pinned, 0, Vec::new()),
                    &block_names(block, 0, Vec::new()),
                    0,
                ) {
                    Ok(Some(cenv::basis_kind_dup(&ks[i])))
                } else {
                    basis_name_hit_go(pers, st, block, ks, i + 1)
                }
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/Basis.lean:133-136 basisNameHit
/// Lean twin: `proof/ConRon/Arena/Basis.lean:202-206 basisNameHit` — **the pinned block
/// a record declares**, by its members' names.  `.quotK` is not among the
/// kinds tried (a quotient arrives as five one-constant records); the list is
/// `con_ron_core::kernel::basis_raw::block_pin_kinds`, the cited literal.
pub fn basis_name_hit(
    pers: &PersTier,
    st: &mut AState,
    block: &Vec<IConstantInfo>,
) -> Result<Option<BasisKind>, CheckError> {
    let ks: Vec<BasisKind> = basis_raw::block_pin_kinds();
    basis_name_hit_go(pers, st, block, &ks, 0)
}

/// con-leche: none — `block.all fun c => !reservedBasisNames.contains c.name`, as a cursor
/// Lean twin: the `.indDecl` arm of `proof/ConRon/Arena/Basis.lean:1-1 basisNamesOk` at a
/// block that hits no pinned block: no member takes a reserved name.
pub fn block_unreserved(rs: &Vec<NIdx>, block: &Vec<IConstantInfo>, i: usize) -> bool {
    if i >= block.len() {
        true
    } else if nidx_vec_contains(rs, &i_constant_info_name(&block[i])) {
        false
    } else {
        block_unreserved(rs, block, i + 1)
    }
}

/// con-leche: ConLeche/Kernel/Basis.lean:138-151 basisNamesOk
/// Lean twin: `proof/ConRon/Arena/Basis.lean:1-1 basisNamesOk` — **the reserved
/// names' check**, the one place the checker sets the basis names apart.  It
/// runs after a declaration's own checks, which treat a basis block as any
/// other block: a block under one of the pinned blocks' names must be that
/// block, up to its level-parameter names (`pin_list_ok`), and no other
/// declaration may take a reserved name.  `Quot.sound` and the quotient
/// records are compared with their own pins, so they pass here.
pub fn basis_names_ok(pers: &PersTier, st: &mut AState, d: &IDeclaration) -> Result<bool, CheckError> {
    match d {
        IDeclaration::IndDecl(block, _) => match basis_name_hit(pers, st, block) {
            Err(e) => Err(e),
            Ok(Some(kind)) => match basis_kind_decls(pers, st, &kind) {
                Err(e) => Err(e),
                Ok(pins) => pin_list_ok(pers, st, block, &pins),
            },
            Ok(None) => match reserved_basis_names(st) {
                Err(e) => Err(e),
                Ok(rs) => Ok(block_unreserved(&rs, block, 0)),
            },
        },
        IDeclaration::AxiomDecl(cv) => match pin_quot_sound(st) {
            Err(e) => Err(e),
            Ok(qs) => {
                if cv.name.eq2(&qs) {
                    Ok(true)
                } else {
                    basis_name_unreserved(st, &cv.name)
                }
            }
        },
        IDeclaration::QuotDecl(_, _) => Ok(true),
        IDeclaration::DefnDecl(cv, _, _) => basis_name_unreserved(st, &cv.name),
        IDeclaration::ThmDecl(cv, _) => basis_name_unreserved(st, &cv.name),
        IDeclaration::OpaqueDecl(cv, _) => basis_name_unreserved(st, &cv.name),
    }
}

/// con-leche: ConLeche/Kernel/Basis.lean:138-151 basisNamesOk
/// Lean twin: `proof/ConRon/Arena/Basis.lean:1-1 basisNamesOk` — the
/// one-constant arms' test, `!reservedBasisNames.contains cv.name`.
pub fn basis_name_unreserved(st: &AState, n: &NIdx) -> Result<bool, CheckError> {
    match reserved_basis_names(st) {
        Err(e) => Err(e),
        Ok(rs) => Ok(!nidx_vec_contains(&rs, n)),
    }
}

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `reserved basis name: the block is not the pinned one`, as code points.
pub const M_BASIS_NOT_PIN: [u32; 52] = [
    114, 101, 115, 101, 114, 118, 101, 100, 32, 98, 97, 115, 105, 115, 32, 110, 97, 109, 101, 58,
    32, 116, 104, 101, 32, 98, 108, 111, 99, 107, 32, 105, 115, 32, 110, 111, 116, 32, 116, 104,
    101, 32, 112, 105, 110, 110, 101, 100, 32, 111, 110, 101,
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `reserved basis name in the block of`, as code points.
pub const M_BASIS_IN_BLOCK: [u32; 35] = [
    114, 101, 115, 101, 114, 118, 101, 100, 32, 98, 97, 115, 105, 115, 32, 110, 97, 109, 101, 32,
    105, 110, 32, 116, 104, 101, 32, 98, 108, 111, 99, 107, 32, 111, 102,
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `reserved basis name`, as code points.
pub const M_BASIS_NAME: [u32; 19] = [
    114, 101, 115, 101, 114, 118, 101, 100, 32, 98, 97, 115, 105, 115, 32, 110, 97, 109, 101,
];

/// con-leche: ConLeche/Kernel/Basis.lean:153-161 basisNamesError
/// Lean twin: `proof/ConRon/Arena/Basis.lean:1-1 basisNamesError` — **what a
/// failed `basis_names_ok` reports**: a block under a pinned block's names that
/// is not the pin, a reserved name in another block, or a one-constant
/// declaration at a reserved name; all invalid input.  The messages drop
/// con-leche's interpolated names (§3.1).
pub fn basis_names_error(pers: &PersTier, st: &mut AState, d: &IDeclaration) -> Result<CheckError, CheckError> {
    match d {
        IDeclaration::IndDecl(block, _) => match basis_name_hit(pers, st, block) {
            Err(e) => Err(e),
            Ok(Some(_)) => Ok(CheckError::Invalid(code_points(&M_BASIS_NOT_PIN))),
            Ok(None) => Ok(CheckError::Invalid(code_points(&M_BASIS_IN_BLOCK))),
        },
        _ => Ok(CheckError::Invalid(code_points(&M_BASIS_NAME))),
    }
}

/// con-leche: ConLeche/Kernel/Basis.lean:163-165 quotPin
/// Lean twin: `proof/ConRon/Arena/Basis.lean:223-227 quotPin` — the pinned quotient
/// package's constant at a slot (`getD`'s default the inhabitant
/// `i_constant_info_dummy`, unreachable: the package has the five slots
/// `quot_kind_slot` indexes).
pub fn quot_pin(pers: &PersTier, st: &mut AState, k: &QuotKind) -> Result<IConstantInfo, CheckError> {
    match basis_kind_decls(pers, st, &BasisKind::QuotK) {
        Err(e) => Err(e),
        Ok(blk) => {
            let slot: u64 = cenv::quot_kind_slot(k);
            if slot >= blk.len() as u64 {
                Ok(i_constant_info_dummy())
            } else {
                Ok(i_constant_info_dup(&blk[slot as usize]))
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/Basis.lean:167-170 quotAt
/// Lean twin: `proof/ConRon/Arena/Basis.lean:229-232 quotAt` — **what a quotient record
/// stores**: its slot's pin at the names it declares.
pub fn quot_at(
    pers: &PersTier,
    st: &mut AState,
    k: &QuotKind,
    cv: &IConstantVal,
) -> Result<IConstantInfo, CheckError> {
    match quot_pin(pers, st, k) {
        Err(e) => Err(e),
        Ok(pin) => constant_info_at_lps(pers, st, &pin, &cv.level_params),
    }
}

/// con-leche: ConLeche/Kernel/Basis.lean:172-178 quotPinHit
/// Lean twin: `proof/ConRon/Arena/Basis.lean:234-242 quotPinHit` — **the quotient-pin
/// match**: the record is the pinned package's constant at the slot it
/// declares itself at, up to its level-parameter names: distinct, as many as
/// the pin's.
pub fn quot_pin_hit(
    pers: &PersTier,
    st: &mut AState,
    k: &QuotKind,
    cv: &IConstantVal,
) -> Result<bool, CheckError> {
    match quot_pin(pers, st, k) {
        Err(e) => Err(e),
        Ok(pin) => {
            let pcv: IConstantVal = i_constant_info_to_constant_val(&pin);
            if name_nodup(&cv.level_params) && cv.level_params.len() == pcv.level_params.len() {
                match constant_val_at_lps(pers, st, &pcv, &cv.level_params) {
                    Err(e) => Err(e),
                    Ok(pcv2) => Ok(i_constant_val_beq(cv, &pcv2)),
                }
            } else {
                Ok(false)
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/Basis.lean:180-192 quotPredsOk
/// Lean twin: `proof/ConRon/Arena/Basis.lean:244-256 quotPredsOk` — **what a quotient
/// record's slot needs stored before it**: the constants its type mentions.  A
/// reserved name is stored only as a copy of its pin, at whatever names, and
/// references are positional.  The cited `find?` argument is the index `fe`.
pub fn quot_preds_ok(
    pers: &PersTier,
    st: &AState,
    fe: &IFEnv,
    k: &QuotKind,
) -> Result<bool, CheckError> {
    match pin_eq(st) {
        Err(e) => Err(e),
        Ok(en) => match pin_quot(st) {
            Err(e) => Err(e),
            Ok(qn) => match pin_quot_mk(st) {
                Err(e) => Err(e),
                Ok(mn) => {
                    let has_eq: bool = ifenv_find(pers, fe, &en).is_some();
                    let has_q: bool = ifenv_find(pers, fe, &qn).is_some();
                    let has_m: bool = ifenv_find(pers, fe, &mn).is_some();
                    match k {
                        QuotKind::Type => Ok(has_eq),
                        QuotKind::Ctor => Ok(has_q),
                        QuotKind::Lift => Ok(has_eq && has_q && has_m),
                        QuotKind::Ind => Ok(has_q && has_m),
                        QuotKind::Sound => Ok(has_eq && has_q && has_m),
                    }
                }
            },
        },
    }
}

// ---------------------------------------------------------------------------
// The pinned `And`
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/Basis/And.lean:94-95 andPin
/// Lean twin: `proof/ConRon/Arena/Basis.lean:260-264 andPinDecls` — the pinned `And`
/// block, interned: `basis_kind_decls`'s shape for the one pinned block that is
/// recognised and never installed from literals.
pub fn and_pin_decls(pers: &PersTier, st: &mut AState) -> Result<Vec<IConstantInfo>, CheckError> {
    intern_ci_list(pers, st, &basis_raw::and_pin())
}

/// con-leche: ConLeche/Kernel/Basis/And.lean:97-99 andPinNames
/// Lean twin: `proof/ConRon/Arena/Basis.lean:266-273 andPinNameHs` — the names the
/// pinned `And` block declares, as handles: `And`, `And.intro`, `And.rec`, off
/// the reserved-name table (`arena::pins`), so the test below costs three slot
/// reads per record and interns nothing.
pub fn and_pin_name_hs(st: &AState) -> Result<Vec<NIdx>, CheckError> {
    match crate::arena::pins::pin_and(st) {
        Err(e) => Err(e),
        Ok(a) => match crate::arena::pins::pin_and_intro(st) {
            Err(e) => Err(e),
            Ok(i) => match crate::arena::pins::pin_and_rec(st) {
                Err(e) => Err(e),
                Ok(r) => {
                    let mut hs: Vec<NIdx> = Vec::new();
                    hs.push(a);
                    hs.push(i);
                    hs.push(r);
                    Ok(hs)
                }
            },
        },
    }
}

/// con-leche: ConLeche/Kernel/Basis.lean:206-214 andPinOk
/// Lean twin: `proof/ConRon/Arena/Basis.lean:275-280 blockAndNamed` — the `.indDecl`
/// arm's `block.any fun c => andPinNames.contains c.name`, as a cursor
/// recursion (§3.4 forbids the closure).
pub fn block_and_named(block: &Vec<IConstantInfo>, hs: &Vec<NIdx>, i: usize) -> bool {
    if i >= block.len() {
        false
    } else if crate::arena::env::nidx_vec_contains(hs, &i_constant_info_name(&block[i])) {
        true
    } else {
        block_and_named(block, hs, i + 1)
    }
}

/// con-leche: ConLeche/Kernel/Basis.lean:206-214 andPinOk
/// Lean twin: `proof/ConRon/Arena/Basis.lean:282-287 andPinNameFree` — the arm of every
/// one-constant record: it may not declare one of the pinned `And` block's
/// names.
pub fn and_pin_name_free(st: &AState, n: &NIdx) -> Result<bool, CheckError> {
    match and_pin_name_hs(st) {
        Err(e) => Err(e),
        Ok(hs) => Ok(!crate::arena::env::nidx_vec_contains(&hs, n)),
    }
}

/// con-leche: ConLeche/Kernel/Basis.lean:206-214 andPinOk
/// Lean twin: `proof/ConRon/Arena/Basis.lean:289-307 andPinOk` — **the `And` pin's
/// test**: the record declares none of the pinned `And` block's names, or it
/// IS that block — two parameters, and equal to `andPin` up to
/// `ConstantInfo.canon` (`canon_eq_list`).  Only a block that declares one of
/// the three names gets that far, so an ordinary record pays the three slot
/// reads and a handle scan.
pub fn and_pin_ok(pers: &PersTier, st: &mut AState, pd: &IDeclaration) -> Result<bool, CheckError> {
    match pd {
        IDeclaration::IndDecl(block, n_p) => match and_pin_name_hs(st) {
            Err(e) => Err(e),
            Ok(hs) => {
                if block_and_named(block, &hs, 0) {
                    if *n_p == 2 {
                        match and_pin_decls(pers, st) {
                            Err(e) => Err(e),
                            Ok(pinned) => crate::arena::canon::canon_eq_list(pers, st, block, &pinned, 0),
                        }
                    } else {
                        Ok(false)
                    }
                } else {
                    Ok(true)
                }
            }
        },
        IDeclaration::AxiomDecl(cv) => and_pin_name_free(st, &cv.name),
        IDeclaration::DefnDecl(cv, _, _) => and_pin_name_free(st, &cv.name),
        IDeclaration::ThmDecl(cv, _) => and_pin_name_free(st, &cv.name),
        IDeclaration::OpaqueDecl(cv, _) => and_pin_name_free(st, &cv.name),
        IDeclaration::QuotDecl(_, cv) => and_pin_name_free(st, &cv.name),
    }
}
