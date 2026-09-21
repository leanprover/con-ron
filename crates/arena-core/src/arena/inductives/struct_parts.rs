//! `arena::inductives::struct_parts` — the direct install's generators.
//!
//! The Rust twin of `proof/ConRon/Arena/Inductives/StructParts.lean`, which is
//! `ConLeche/Kernel/Inductives/StructParts.lean` whole over handles: the
//! syntactic generators every direct install reads and compares against the
//! stream — the type-former family, the constructor spines, the rule bodies,
//! the Π→Π/λ rewrites — and `StructParts`, the shape record.
//!
//! ## What the twin's deviations become here
//!
//! The twin's module note lists five; four of them are already the arena's
//! own shape and carry over unchanged (every structural match on a term is a
//! `view`; every term built is interned; `lps.map .param` is one interned
//! `LsIdx`; the fields' sorts are a `Vec<LIdx>` and not an `LsIdx`).  The
//! fifth — *the pure walk, the cutoff walk and the memoized walk are ONE
//! twin* — is why `has_loose_bvar_b_go` and `mentions_const_go` each cite
//! three or four con-leche declarations.
//!
//! ## The memos are ARGUMENTS, threaded by value
//!
//! con-leche threads a `Std.HashMap Expr Bool` through `hasLooseBVarBGo` and
//! `mentionsConstGo` rather than putting it in a state, because the answer
//! depends on data that is fixed for one call (`T`, and for `hasLooseBVarB`
//! the index, which is in the key).  The twin does the same at handle keys —
//! **nothing is added to `AState`** — and this port threads the table *by
//! value*, moved in and returned, which is the twin's `AM (Bool × Std.HashMap
//! …)` term for term.  `con_ron_core::kernel::inductives::struct_parts` hands
//! the same table down as a `&mut` instead; here the state parameter is
//! already the one `&mut` (DESIGN.md §3.4), and a moved `Vec`-backed table
//! costs nothing to move.
//!
//! ## Two shapes the port adds, both of them the campaign's standing rules
//!
//! * every `List`/`Array` recursion over a `Vec` is a cursor recursion with
//!   an `_from` companion (DESIGN.md §3.4, task #97-P4b's row);
//! * a `HashMap::get` match that produces a value is its own function and is
//!   never inlined — task #97-P4c's **extraction rule 5**.  That is what
//!   `hlb_probe` and `mc_probe` are.

use crate::arena::core;
use crate::arena::core::CORE_WALK_FUEL;
use crate::arena::env::IConstantVal;
use crate::arena::expr_ops;
use crate::arena::handle::{EIdx, LIdx, LsIdx, NIdx, ETAG_FORALL_E, ETAG_SORT};
use crate::arena::monad::{
    AState, EIdxNat, eidx_nat_key, fail, fail_dangling_e, intern_e_app, intern_e_bvar, intern_e_const, intern_e_forall_e, intern_e_lam, intern_e_proj, intern_e_sort, intern_l_node, intern_ls_node, view, view_bind, view_sort,
};
use crate::arena::store::{ENodeView, LNodeView};
use con_ron_core::kernel::core_types::{code_points, CheckError};
use con_ron_core::kernel::expr;
use con_ron_core::kernel::expr::BinderMeta;
use con_ron_core::kernel::prop_when;
use con_ron_core::kernel::prop_when::PropWhen;
use con_ron_core::ron::hashmap::{Dup, Eq2};
// The arena's tables are the epoch-stamped open-addressed map
// (DESIGN.md's `Task #97-P6-4b`), aliased so that every use site below
// reads as it did.  `ron::hashmap::HashMap` is still what `crates/con-ron`
// uses, and is still the one with proofs.
use con_ron_core::ron::hashmap2::HashMap2 as HashMap;
use crate::arena::store::PersTier;

// ---------------------------------------------------------------------------
// The messages of this module's declines
// ---------------------------------------------------------------------------

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `"fuel exhausted: hasLooseBVarB"`, as code points.
pub const M_FUEL_HLB: [u32; 29] = [
    102, 117, 101, 108, 32, 101, 120, 104, 97, 117, 115, 116, 101, 100, 58, 32, 104, 97, 115, 76,
    111, 111, 115, 101, 66, 86, 97, 114, 66,
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `"fuel exhausted: mentionsConst"`, as code points.
pub const M_FUEL_MENTIONS: [u32; 29] = [
    102, 117, 101, 108, 32, 101, 120, 104, 97, 117, 115, 116, 101, 100, 58, 32, 109, 101, 110, 116,
    105, 111, 110, 115, 67, 111, 110, 115, 116,
];

// ---------------------------------------------------------------------------
// One list helper the twin gets from `List` (DESIGN.md §3.4's standing rule)
// ---------------------------------------------------------------------------

/// con-leche: none — `ns.tail` over a `Vec<NIdx>`; Lean's `elim :: relps` pattern binds it
/// Lean twin: `proof/ConRon/Arena/Inductives/StructParts.lean:292 structPartsCore?`
/// — the recogniser's `match cvR.levelParams with | elim :: relps` splits the
/// list; a `Vec` has no tail-sharing, so the tail is copied.  The list is a
/// declaration's level parameters, never a term.
pub fn nidx_vec_tail(ns: &Vec<NIdx>) -> Vec<NIdx> {
    nidx_vec_tail_from(ns, 1, Vec::new())
}

/// con-leche: none — `ns.tail` over a `Vec<NIdx>`
/// Lean twin: `proof/ConRon/Arena/Inductives/StructParts.lean:292 structPartsCore?`
/// — the cursor recursion behind `nidx_vec_tail`.
pub fn nidx_vec_tail_from(ns: &Vec<NIdx>, i: usize, out: Vec<NIdx>) -> Vec<NIdx> {
    if i >= ns.len() {
        out
    } else {
        let mut o: Vec<NIdx> = out;
        o.push(ns[i].dup2());
        nidx_vec_tail_from(ns, i + 1, o)
    }
}

// ---------------------------------------------------------------------------
// Level lists over handles (`StructParts.lean:51-62` of the twin)
// ---------------------------------------------------------------------------

/// con-leche: none — `lps.map .param`, interned: the universe arguments a block's own constants carry
/// Lean twin: `proof/ConRon/Arena/Inductives/StructParts.lean:55-62 paramLevels`
/// — con-leche writes the list inline at every use; over handles a level list
/// is a node, so it is built once by a function of its own.
pub fn param_levels(
    pers: &PersTier,
    st: &mut AState,
    lps: &Vec<NIdx>,
) -> Result<LsIdx, CheckError>  {
    match param_levels_go(pers, st, lps, 0, Vec::new()) {
        Err(e) => Err(e),
        Ok(us) => intern_ls_node(pers, st, us),
    }
}

/// con-leche: none — `lps.map .param`, interned
/// Lean twin: `proof/ConRon/Arena/Inductives/StructParts.lean:56-61 paramLevels.go`
/// — the cursor recursion behind `param_levels`.
pub fn param_levels_go(
    pers: &PersTier,
    st: &mut AState,
    lps: &Vec<NIdx>,
    i: usize,
    out: Vec<LIdx>,
) -> Result<Vec<LIdx>, CheckError> {
    if i >= lps.len() {
        Ok(out)
    } else {
        match intern_l_node(pers, st, LNodeView::Param(lps[i].dup2())) {
            Err(e) => Err(e),
            Ok(u) => {
                let mut o: Vec<LIdx> = out;
                o.push(u);
                param_levels_go(pers, st, lps, i + 1, o)
            }
        }
    }
}

// ---------------------------------------------------------------------------
// The families and the spines (`StructParts.lean:66-125` of the twin)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/Inductives/StructParts.lean:134-137 structPsAt
/// Lean twin: `proof/ConRon/Arena/Inductives/StructParts.lean:70-77 structPsAt`
/// — the parameter variables as seen from under `o` extra binders:
/// `p_k = bvar (o + nP - 1 - k)`, `structFam`'s argument spine.
pub fn struct_ps_at(
    pers: &PersTier,
    st: &mut AState,
    o: u64,
    n_p: u64,
) -> Result<Vec<EIdx>, CheckError>  {
    struct_ps_at_from(pers, st, o, n_p, 0, Vec::new())
}

/// con-leche: ConLeche/Kernel/Inductives/StructParts.lean:134-137 structPsAt
/// Lean twin: `proof/ConRon/Arena/Inductives/StructParts.lean:71-76 structPsAt.go`
/// — the cursor recursion behind `struct_ps_at`.
pub fn struct_ps_at_from(
    pers: &PersTier,
    st: &mut AState,
    o: u64,
    n_p: u64,
    k: u64,
    out: Vec<EIdx>,
) -> Result<Vec<EIdx>, CheckError> {
    if k >= n_p {
        Ok(out)
    } else {
        match intern_e_bvar(pers, st, o + n_p - 1 - k) {
            Err(e) => Err(e),
            Ok(b) => {
                let mut o2: Vec<EIdx> = out;
                o2.push(b);
                struct_ps_at_from(pers, st, o, n_p, k + 1, o2)
            }
        }
    }
}

/// con-leche: none — `(List.range n).map fun j => Expr.bvar (n - 1 - j)`, interned
/// Lean twin: `proof/ConRon/Arena/Inductives/StructParts.lean:82 bvarsDesc` —
/// the FIELD variables' spine.  `structPsAt 0 n` is the same list; it is named
/// apart because con-leche writes the two inline at different frames.
pub fn bvars_desc(pers: &PersTier, st: &mut AState, n: u64) -> Result<Vec<EIdx>, CheckError> {
    struct_ps_at(pers, st, 0, n)
}

/// con-leche: ConLeche/Kernel/Inductives/StructParts.lean:82-86 structFam
/// Lean twin: `proof/ConRon/Arena/Inductives/StructParts.lean:87-90 structFam`
/// — the type former applied to its parameter variables, `bvar` indices offset
/// by `o` (the number of binders crossed since the parameters).
pub fn struct_fam(
    pers: &PersTier,
    st: &mut AState,
    t: &NIdx,
    lps: &Vec<NIdx>,
    n_p: u64,
    o: u64,
) -> Result<EIdx, CheckError> {
    match param_levels(pers, st, lps) {
        Err(e) => Err(e),
        Ok(us) => match intern_e_const(pers, st, t.dup2(), us) {
            Err(e) => Err(e),
            Ok(hd) => match struct_ps_at(pers, st, o, n_p) {
                Err(e) => Err(e),
                Ok(ps) => expr_ops::mk_app_n(pers, st, &hd, &ps),
            },
        },
    }
}

/// con-leche: ConLeche/Kernel/Inductives/StructParts.lean:88-94 structCtorSpine
/// Lean twin: `proof/ConRon/Arena/Inductives/StructParts.lean:96-101 structCtorSpine`
/// — the constructor applied to the parameter and field variables, as spelled
/// inside the recursor's minor premise (parameters sit above the motive
/// binder).
pub fn struct_ctor_spine(
    pers: &PersTier,
    st: &mut AState,
    c: &NIdx,
    lps: &Vec<NIdx>,
    n_p: u64,
    n_f: u64,
) -> Result<EIdx, CheckError> {
    match param_levels(pers, st, lps) {
        Err(e) => Err(e),
        Ok(us) => match intern_e_const(pers, st, c.dup2(), us) {
            Err(e) => Err(e),
            Ok(hd) => match struct_ps_at(pers, st, n_f + 1, n_p) {
                Err(e) => Err(e),
                Ok(ps) => match bvars_desc(pers, st, n_f) {
                    Err(e) => Err(e),
                    Ok(fs) => {
                        let args: Vec<EIdx> = core::append_eidx(ps, &fs);
                        expr_ops::mk_app_n(pers, st, &hd, &args)
                    }
                },
            },
        },
    }
}

/// con-leche: ConLeche/Kernel/Inductives/StructParts.lean:96-99 structRuleBody
/// Lean twin: `proof/ConRon/Arena/Inductives/StructParts.lean:106-108 structRuleBody`
/// — the recursor rule's right-hand side body: the minor premise applied to
/// the field variables.
pub fn struct_rule_body(pers: &PersTier, st: &mut AState, n_f: u64) -> Result<EIdx, CheckError> {
    match intern_e_bvar(pers, st, n_f) {
        Err(e) => Err(e),
        Ok(hd) => match bvars_desc(pers, st, n_f) {
            Err(e) => Err(e),
            Ok(fs) => expr_ops::mk_app_n(pers, st, &hd, &fs),
        },
    }
}

/// con-leche: ConLeche/Kernel/Inductives/StructParts.lean:139-142 structElimLevel
/// Lean twin: `proof/ConRon/Arena/Inductives/StructParts.lean:113-114 structElimLevel`
/// — the recursor's elimination level: the fresh parameter at the large
/// eliminator, `zero` at the small one.
pub fn struct_elim_level(
    pers: &PersTier,
    st: &mut AState,
    elim: &NIdx,
    large: bool,
) -> Result<LIdx, CheckError>  {
    if large {
        intern_l_node(pers, st, LNodeView::Param(elim.dup2()))
    } else {
        intern_l_node(pers, st, LNodeView::Zero)
    }
}

/// con-leche: ConLeche/Kernel/Inductives/StructParts.lean:144-150 structCtorSpineAt
/// Lean twin: `proof/ConRon/Arena/Inductives/StructParts.lean:120-125 structCtorSpineAt`
/// — the constructor applied to the parameter and field variables, as spelled
/// under `o` binders between the parameters and the fields (the motive and the
/// earlier minor premises); `struct_ctor_spine` is the `o = 1` case.
pub fn struct_ctor_spine_at(
    pers: &PersTier,
    st: &mut AState,
    c: &NIdx,
    lps: &Vec<NIdx>,
    o: u64,
    n_p: u64,
    n_f: u64,
) -> Result<EIdx, CheckError> {
    match param_levels(pers, st, lps) {
        Err(e) => Err(e),
        Ok(us) => match intern_e_const(pers, st, c.dup2(), us) {
            Err(e) => Err(e),
            Ok(hd) => match struct_ps_at(pers, st, o + n_f, n_p) {
                Err(e) => Err(e),
                Ok(ps) => match bvars_desc(pers, st, n_f) {
                    Err(e) => Err(e),
                    Ok(fs) => {
                        let args: Vec<EIdx> = core::append_eidx(ps, &fs);
                        expr_ops::mk_app_n(pers, st, &hd, &args)
                    }
                },
            },
        },
    }
}

/// con-leche: ConLeche/Kernel/Inductives/StructParts.lean:152-158 Expr.replacePisPw
/// Lean twin: `proof/ConRon/Arena/Inductives/StructParts.lean:130-140 replacePisPw`
/// — replace the body under the first `k` `∀`-binders, resetting their codomain
/// data to `pw` (the domains are kept).
pub fn replace_pis_pw(
    pers: &PersTier,
    st: &mut AState,
    pw: &PropWhen,
    k: u64,
    h: &EIdx,
    b: &EIdx,
) -> Result<Option<EIdx>, CheckError> {
    if k == 0 {
        Ok(Some(b.dup2()))
    } else {
        if h.tag() == ETAG_FORALL_E {
            match view_bind(pers, st, h) {
                None => fail_dangling_e(),
                Some((ty, rest, _)) => match replace_pis_pw(pers, st, pw, k - 1, &rest, b) {
                    Err(e) => Err(e),
                    Ok(None) => Ok(None),
                    Ok(Some(r)) => {
                        let m: BinderMeta = expr::binder_meta(prop_when::dup(pw));
                        match intern_e_forall_e(pers, st, ty, r, m) {
                            Err(e) => Err(e),
                            Ok(n) => Ok(Some(n)),
                        }
                    }
                },
            }
        } else {
            Ok(None)
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/StructParts.lean:160-167 Expr.pisToLamsPw
/// Lean twin: `proof/ConRon/Arena/Inductives/StructParts.lean:145-155 pisToLamsPw`
/// — convert the first `k` `∀`-binders into `λ`-binders with datum `pw` over a
/// body.
pub fn pis_to_lams_pw(
    pers: &PersTier,
    st: &mut AState,
    pw: &PropWhen,
    k: u64,
    h: &EIdx,
    b: &EIdx,
) -> Result<Option<EIdx>, CheckError> {
    if k == 0 {
        Ok(Some(b.dup2()))
    } else {
        if h.tag() == ETAG_FORALL_E {
            match view_bind(pers, st, h) {
                None => fail_dangling_e(),
                Some((ty, rest, _)) => match pis_to_lams_pw(pers, st, pw, k - 1, &rest, b) {
                    Err(e) => Err(e),
                    Ok(None) => Ok(None),
                    Ok(Some(r)) => {
                        let m: BinderMeta = expr::binder_meta(prop_when::dup(pw));
                        match intern_e_lam(pers, st, ty, r, m) {
                            Err(e) => Err(e),
                            Ok(n) => Ok(Some(n)),
                        }
                    }
                },
            }
        } else {
            Ok(None)
        }
    }
}

// ---------------------------------------------------------------------------
// The generated recursor at an indexed family (`StructParts.lean:159-188`)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/Inductives/StructParts.lean:189-194 structFamI
/// Lean twin: `proof/ConRon/Arena/Inductives/StructParts.lean:161-166 structFamI`
/// — the family applied to its parameter variables and its index variables.
pub fn struct_fam_i(
    pers: &PersTier,
    st: &mut AState,
    t: &NIdx,
    lps: &Vec<NIdx>,
    n_p: u64,
    n_idx: u64,
    e: u64,
    o: u64,
) -> Result<EIdx, CheckError> {
    match param_levels(pers, st, lps) {
        Err(er) => Err(er),
        Ok(us) => match intern_e_const(pers, st, t.dup2(), us) {
            Err(er) => Err(er),
            Ok(hd) => match struct_ps_at(pers, st, o + e + n_idx, n_p) {
                Err(er) => Err(er),
                Ok(ps) => match struct_ps_at(pers, st, o, n_idx) {
                    Err(er) => Err(er),
                    Ok(is) => {
                        let args: Vec<EIdx> = core::append_eidx(ps, &is);
                        expr_ops::mk_app_n(pers, st, &hd, &args)
                    }
                },
            },
        },
    }
}

/// con-leche: ConLeche/Kernel/Inductives/StructParts.lean:196-202 structCtorResidOk
/// Lean twin: `proof/ConRon/Arena/Inductives/StructParts.lean:172-179 structCtorResidOk`
/// — a constructor residual's shape at an indexed family: the family at exactly
/// the parameter variables (`o` binders below the parameter frame) followed by
/// `nIdx` index expressions.
pub fn struct_ctor_resid_ok(
    pers: &PersTier,
    st: &mut AState,
    t: &NIdx,
    lps: &Vec<NIdx>,
    n_p: u64,
    o: u64,
    n_idx: u64,
    cbody: &EIdx,
) -> Result<bool, CheckError> {
    match param_levels(pers, st, lps) {
        Err(e) => Err(e),
        Ok(us) => match intern_e_const(pers, st, t.dup2(), us) {
            Err(e) => Err(e),
            Ok(hd) => match expr_ops::get_app_fn(pers, st, CORE_WALK_FUEL, cbody) {
                Err(e) => Err(e),
                Ok(fna) => match expr_ops::get_app_args(pers, st, CORE_WALK_FUEL, cbody) {
                    Err(e) => Err(e),
                    Ok(args) => match struct_ps_at(pers, st, o, n_p) {
                        Err(e) => Err(e),
                        Ok(ps) => Ok(fna.eq2(&hd)
                            && args.len() as u64 == n_p + n_idx
                            && expr_ops::eidx_take_beq(&args, &ps)),
                    },
                },
            },
        },
    }
}

/// con-leche: ConLeche/Kernel/Inductives/StructParts.lean:204-211 structMotiveTyI
/// Lean twin: `proof/ConRon/Arena/Inductives/StructParts.lean:183-188 structMotiveTyI`
/// — the motive's type `∀ ı⃗ (t : T p⃗ ı⃗), Sort ℓ` at the parameters' frame.
pub fn struct_motive_ty_i(
    pers: &PersTier,
    st: &mut AState,
    t: &NIdx,
    lps: &Vec<NIdx>,
    n_p: u64,
    n_idx: u64,
    l: &LIdx,
    itele: &EIdx,
) -> Result<Option<EIdx>, CheckError> {
    match struct_fam_i(pers, st, t, lps, n_p, n_idx, 0, 0) {
        Err(e) => Err(e),
        Ok(fam) => match intern_e_sort(pers, st, l.dup2()) {
            Err(e) => Err(e),
            Ok(s) => {
                let m: BinderMeta = expr::binder_meta(prop_when::never());
                match intern_e_forall_e(pers, st, fam, s, m) {
                    Err(e) => Err(e),
                    Ok(body) => {
                        let pw: PropWhen = prop_when::never();
                        replace_pis_pw(pers, st, &pw, n_idx, itele, &body)
                    }
                }
            }
        },
    }
}

// ---------------------------------------------------------------------------
// The shape record and its recogniser (`StructParts.lean:190-311` of the twin)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/Inductives/StructParts.lean:213-244 StructParts
/// Lean twin: `proof/ConRon/Arena/Inductives/StructParts.lean:192-214 StructParts`
/// — the pieces of a recognised simple-structure block, over handles.
pub struct StructParts {
    /// the type former
    pub cv_t: IConstantVal,
    /// the single constructor
    pub cv_c: IConstantVal,
    /// parameter count
    pub n_p: u64,
    /// field count
    pub n_f: u64,
    /// the recursor
    pub cv_r: IConstantVal,
    /// the recursor's fresh elimination level parameter (`large` only)
    pub elim: NIdx,
    /// the structure's result sort
    pub res_sort: LIdx,
    /// the single rule's right-hand side (as exported)
    pub rhs: EIdx,
    /// **large eliminator**: the recursor carries a fresh elimination level
    /// parameter in front and its motive lands in `Sort elim`.
    pub large: bool,
    /// **propositional result**: the result sort is provably `Prop`.
    pub is_prop: bool,
}

/// con-leche: ConLeche/Kernel/Inductives/StructParts.lean:246-281 structShape
/// Lean twin: `proof/ConRon/Arena/Inductives/StructParts.lean:218-261 structShape`
/// — the *shape* facts the model reads off the stored (annotated) types.  The
/// twin's one `do` block is four functions here, split at its own
/// `if … then pure false else do` boundaries (task #97-P4c's arrangement).
pub fn struct_shape(
    pers: &PersTier,
    st: &mut AState,
    t: &NIdx,
    c: &NIdx,
    lps: &Vec<NIdx>,
    elim: &NIdx,
    large: bool,
    n_p: u64,
    n_f: u64,
    tty: &EIdx,
    cty: &EIdx,
    rty: &EIdx,
) -> Result<bool, CheckError> {
    match expr_ops::strip_pis(pers, st, n_p, tty) {
        Err(e) => Err(e),
        Ok(None) => Ok(false),
        Ok(Some(tq)) => match expr_ops::strip_pis(pers, st, n_p + n_f, cty) {
            Err(e) => Err(e),
            Ok(None) => Ok(false),
            Ok(Some(cq)) => match expr_ops::strip_pis(pers, st, n_p + 3, rty) {
                Err(e) => Err(e),
                Ok(None) => Ok(false),
                Ok(Some(rq)) => if tq.1.tag() == ETAG_SORT {
                    match view_sort(pers, st, &tq.1) {
                        None => fail_dangling_e(),
                        Some(_) => {
                            struct_shape_at(pers, st, t, c, lps, elim, large, n_p, n_f, &cq.1, &rq.0, &rq.1)
                        },
                    }
                } else {
                    Ok(false)
                },
            },
        },
    }
}

/// con-leche: ConLeche/Kernel/Inductives/StructParts.lean:246-281 structShape
/// Lean twin: `proof/ConRon/Arena/Inductives/StructParts.lean:222-259 structShape`
/// — `structShape`'s body once the three telescopes are peeled and the type
/// former's residual is a sort: the constructor residual and the recursor
/// body, then the motive, minor and major domains.
pub fn struct_shape_at(
    pers: &PersTier,
    st: &mut AState,
    t: &NIdx,
    c: &NIdx,
    lps: &Vec<NIdx>,
    elim: &NIdx,
    large: bool,
    n_p: u64,
    n_f: u64,
    cbody: &EIdx,
    rbs: &Vec<(EIdx, BinderMeta)>,
    rbody: &EIdx,
) -> Result<bool, CheckError> {
    match struct_fam(pers, st, t, lps, n_p, n_f) {
        Err(e) => Err(e),
        Ok(fam) => match intern_e_bvar(pers, st, 2) {
            Err(e) => Err(e),
            Ok(b2) => match intern_e_bvar(pers, st, 0) {
                Err(e) => Err(e),
                Ok(b0) => match intern_e_app(pers, st, b2, b0) {
                    Err(e) => Err(e),
                    Ok(want) => {
                        if !(cbody.eq2(&fam) && rbody.eq2(&want)) {
                            Ok(false)
                        } else {
                            match struct_shape_motive(pers, st, t, lps, elim, large, n_p, rbs) {
                                Err(e) => Err(e),
                                Ok(false) => Ok(false),
                                Ok(true) => match struct_shape_minor(pers, st, c, lps, n_p, n_f, rbs) {
                                    Err(e) => Err(e),
                                    Ok(false) => Ok(false),
                                    Ok(true) => struct_shape_major(pers, st, t, lps, n_p, rbs),
                                },
                            }
                        }
                    }
                },
            },
        },
    }
}

/// con-leche: ConLeche/Kernel/Inductives/StructParts.lean:246-281 structShape
/// Lean twin: `proof/ConRon/Arena/Inductives/StructParts.lean:231-243 structShape`
/// — the motive binder's codomain: `Sort elim` for the large eliminator,
/// `Prop` for the small one (con-leche's task #175 W4c/O4).
pub fn struct_shape_motive(
    pers: &PersTier,
    st: &mut AState,
    t: &NIdx,
    lps: &Vec<NIdx>,
    elim: &NIdx,
    large: bool,
    n_p: u64,
    rbs: &Vec<(EIdx, BinderMeta)>,
) -> Result<bool, CheckError> {
    if (n_p as usize) >= rbs.len() {
        Ok(false)
    } else {
        let mdom: EIdx = rbs[n_p as usize].0.dup2();
        if mdom.tag() == ETAG_FORALL_E {
            match view_bind(pers, st, &mdom) {
                None => fail_dangling_e(),
                Some((mmaj, mcod, _)) => if mcod.tag() == ETAG_SORT {
                    match view_sort(pers, st, &mcod) {
                        None => fail_dangling_e(),
                        Some(s2) => match struct_elim_level(pers, st, elim, large) {
                            Err(e) => Err(e),
                            Ok(want) => match struct_fam(pers, st, t, lps, n_p, 0) {
                                Err(e) => Err(e),
                                Ok(fam0) => Ok(s2.eq2(&want) && mmaj.eq2(&fam0)),
                            },
                        },
                    }
                } else {
                    Ok(false)
                },
            }
        } else {
            Ok(false)
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/StructParts.lean:246-281 structShape
/// Lean twin: `proof/ConRon/Arena/Inductives/StructParts.lean:244-253 structShape`
/// — the minor premise's body is the minor variable at the constructor spine.
pub fn struct_shape_minor(
    pers: &PersTier,
    st: &mut AState,
    c: &NIdx,
    lps: &Vec<NIdx>,
    n_p: u64,
    n_f: u64,
    rbs: &Vec<(EIdx, BinderMeta)>,
) -> Result<bool, CheckError> {
    if ((n_p + 1) as usize) >= rbs.len() {
        Ok(false)
    } else {
        let mindom: EIdx = rbs[(n_p + 1) as usize].0.dup2();
        match expr_ops::strip_pis(pers, st, n_f, &mindom) {
            Err(e) => Err(e),
            Ok(None) => Ok(false),
            Ok(Some(q)) => match intern_e_bvar(pers, st, n_f) {
                Err(e) => Err(e),
                Ok(hd) => match struct_ctor_spine(pers, st, c, lps, n_p, n_f) {
                    Err(e) => Err(e),
                    Ok(sp) => match intern_e_app(pers, st, hd, sp) {
                        Err(e) => Err(e),
                        Ok(want) => Ok(q.1.eq2(&want)),
                    },
                },
            },
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/StructParts.lean:246-281 structShape
/// Lean twin: `proof/ConRon/Arena/Inductives/StructParts.lean:255-259 structShape`
/// — the major premise's domain is the family at two extra binders.
pub fn struct_shape_major(
    pers: &PersTier,
    st: &mut AState,
    t: &NIdx,
    lps: &Vec<NIdx>,
    n_p: u64,
    rbs: &Vec<(EIdx, BinderMeta)>,
) -> Result<bool, CheckError> {
    if ((n_p + 2) as usize) >= rbs.len() {
        Ok(false)
    } else {
        let majdom: EIdx = rbs[(n_p + 2) as usize].0.dup2();
        match struct_fam(pers, st, t, lps, n_p, 2) {
            Err(e) => Err(e),
            Ok(fam2) => Ok(majdom.eq2(&fam2)),
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/StructParts.lean:283-329 structPartsCore?
/// Lean twin: `proof/ConRon/Arena/Inductives/StructParts.lean:265-311 structPartsCore?`
/// — recognise a direct simple-structure block.  `None` means "not this
/// class".  The twin's one `match` on the block is this function's guard; its
/// two eliminator branches are `struct_parts_core_elim`.
pub fn struct_parts_core(
    pers: &PersTier,
    st: &mut AState,
    block: &Vec<crate::arena::env::IConstantInfo>,
) -> Result<Option<StructParts>, CheckError> {
    if block.len() != 3 {
        Ok(None)
    } else {
        match (&block[0], &block[1], &block[2]) {
            (
                crate::arena::env::IConstantInfo::IndInfo(cv_t, _),
                crate::arena::env::IConstantInfo::CtorInfo(cv_c, n_p, n_f),
                crate::arena::env::IConstantInfo::RecInfo(cv_r, m_i, r_p, rules),
            ) => {
                if rules.len() != 1 {
                    Ok(None)
                } else {
                    struct_parts_core_at(pers, st, cv_t, cv_c, *n_p, *n_f, cv_r, *m_i, *r_p, &rules[0])
                }
            }
            _ => Ok(None),
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/StructParts.lean:283-329 structPartsCore?
/// Lean twin: `proof/ConRon/Arena/Inductives/StructParts.lean:267-310 structPartsCore?`
/// — the recogniser's body once the block's three members are in hand: the
/// name and arity pins, then the result sort and the two eliminator shapes.
pub fn struct_parts_core_at(
    pers: &PersTier,
    st: &mut AState,
    cv_t: &IConstantVal,
    cv_c: &IConstantVal,
    n_p: u64,
    n_f: u64,
    cv_r: &IConstantVal,
    m_i: u64,
    r_p: u64,
    rule: &crate::arena::env::IRecRule,
) -> Result<Option<StructParts>, CheckError> {
    const REC: [u32; 3] = [114, 101, 99];
    let t: NIdx = cv_t.name.dup2();
    let c: NIdx = cv_c.name.dup2();
    match crate::arena::monad::intern_n_node(
        pers,
        st,
        crate::arena::store::NNodeView::Str(t.dup2(), code_points(&REC)),
    ) {
        Err(e) => Err(e),
        Ok(rec_name) => match core::reserved_basis_names(st) {
            Err(e) => Err(e),
            Ok(reserved) => match struct_parts_rhs_ok(pers, st, n_p, n_f, &rule.rhs) {
                Err(e) => Err(e),
                Ok(rhs_ok) => {
                    if cv_r.name.eq2(&rec_name)
                        && core::nidx_vec_beq(&cv_c.level_params, &cv_t.level_params)
                        && !crate::arena::env::nidx_vec_contains(&reserved, &t)
                        && !crate::arena::env::nidx_vec_contains(&reserved, &c)
                        && !crate::arena::env::nidx_vec_contains(&reserved, &cv_r.name)
                        && m_i == n_p + 2
                        && r_p == n_p + 2
                        && rule.ctor.eq2(&c)
                        && rule.nfields == n_f
                        && rhs_ok
                    {
                        struct_parts_core_sort(pers, st, cv_t, cv_c, n_p, n_f, cv_r, rule)
                    } else {
                        Ok(None)
                    }
                }
            },
        },
    }
}

/// con-leche: ConLeche/Kernel/Inductives/StructParts.lean:283-329 structPartsCore?
/// Lean twin: `proof/ConRon/Arena/Inductives/StructParts.lean:273-277 structPartsCore?`
/// — the exported rule's right-hand side is the generated one.
pub fn struct_parts_rhs_ok(
    pers: &PersTier,
    st: &mut AState,
    n_p: u64,
    n_f: u64,
    rhs: &EIdx,
) -> Result<bool, CheckError> {
    match expr_ops::strip_lams(pers, st, n_p + 2 + n_f, rhs) {
        Err(e) => Err(e),
        Ok(None) => Ok(false),
        Ok(Some(q)) => match struct_rule_body(pers, st, n_f) {
            Err(e) => Err(e),
            Ok(want) => Ok(q.1.eq2(&want)),
        },
    }
}

/// con-leche: ConLeche/Kernel/Inductives/StructParts.lean:283-329 structPartsCore?
/// Lean twin: `proof/ConRon/Arena/Inductives/StructParts.lean:284-309 structPartsCore?`
/// — the result sort, then the large eliminator (a fresh elimination level
/// parameter in front of the block's own) and, failing that, the small one.
pub fn struct_parts_core_sort(
    pers: &PersTier,
    st: &mut AState,
    cv_t: &IConstantVal,
    cv_c: &IConstantVal,
    n_p: u64,
    n_f: u64,
    cv_r: &IConstantVal,
    rule: &crate::arena::env::IRecRule,
) -> Result<Option<StructParts>, CheckError> {
    match expr_ops::strip_pis(pers, st, n_p, &cv_t.ty) {
        Err(e) => Err(e),
        Ok(None) => Ok(None),
        Ok(Some(q)) => if q.1.tag() == ETAG_SORT {
            match view_sort(pers, st, &q.1) {
                None => fail_dangling_e(),
                Some(s) => match core::zero_level(st) {
                    Err(e) => Err(e),
                    Ok(z) => match core::lvl_eq(pers, st, &s, &z) {
                        Err(e) => Err(e),
                        Ok(eq) => {
                            let is_prop: bool = match eq {
                                Some(true) => true,
                                Some(false) => false,
                                None => false,
                            };
                            struct_parts_core_elim(pers, st, cv_t, cv_c, n_p, n_f, cv_r, rule, &s, is_prop)
                        }
                    },
                },
            }
        } else {
            Ok(None)
        },
    }
}

/// con-leche: ConLeche/Kernel/Inductives/StructParts.lean:283-329 structPartsCore?
/// Lean twin: `proof/ConRon/Arena/Inductives/StructParts.lean:291-307 structPartsCore?`
/// — WHICH eliminator the block's recursor is: the large one carries a fresh
/// level parameter in front of the block's own and passes `structShape` at
/// `large := true`; else the small one at `.anonymous`.
pub fn struct_parts_core_elim(
    pers: &PersTier,
    st: &mut AState,
    cv_t: &IConstantVal,
    cv_c: &IConstantVal,
    n_p: u64,
    n_f: u64,
    cv_r: &IConstantVal,
    rule: &crate::arena::env::IRecRule,
    s: &LIdx,
    is_prop: bool,
) -> Result<Option<StructParts>, CheckError> {
    let lps: &Vec<NIdx> = &cv_t.level_params;
    let large: Option<NIdx> = if cv_r.level_params.len() == 0 {
        None
    } else {
        Some(cv_r.level_params[0].dup2())
    };
    match large {
        Some(elim) => {
            let relps: Vec<NIdx> = nidx_vec_tail(&cv_r.level_params);
            if core::nidx_vec_beq(&relps, lps) && !crate::arena::env::nidx_vec_contains(lps, &elim)
            {
                match struct_shape(
                    pers,
                    st, &cv_t.name, &cv_c.name, lps, &elim, true, n_p, n_f, &cv_t.ty, &cv_c.ty,
                    &cv_r.ty,
                ) {
                    Err(e) => Err(e),
                    Ok(true) => Ok(Some(StructParts {
                        cv_t: crate::arena::env::i_constant_val_dup(cv_t),
                        cv_c: crate::arena::env::i_constant_val_dup(cv_c),
                        n_p,
                        n_f,
                        cv_r: crate::arena::env::i_constant_val_dup(cv_r),
                        elim,
                        res_sort: s.dup2(),
                        rhs: rule.rhs.dup2(),
                        large: true,
                        is_prop,
                    })),
                    Ok(false) => {
                        struct_parts_core_small(pers, st, cv_t, cv_c, n_p, n_f, cv_r, rule, s, is_prop)
                    }
                }
            } else {
                struct_parts_core_small(pers, st, cv_t, cv_c, n_p, n_f, cv_r, rule, s, is_prop)
            }
        }
        None => struct_parts_core_small(pers, st, cv_t, cv_c, n_p, n_f, cv_r, rule, s, is_prop),
    }
}

/// con-leche: ConLeche/Kernel/Inductives/StructParts.lean:283-329 structPartsCore?
/// Lean twin: `proof/ConRon/Arena/Inductives/StructParts.lean:302-307 structPartsCore?`
/// — the small eliminator's branch: the recursor's level parameters are the
/// block's and `structShape` holds at `large := false`.
pub fn struct_parts_core_small(
    pers: &PersTier,
    st: &mut AState,
    cv_t: &IConstantVal,
    cv_c: &IConstantVal,
    n_p: u64,
    n_f: u64,
    cv_r: &IConstantVal,
    rule: &crate::arena::env::IRecRule,
    s: &LIdx,
    is_prop: bool,
) -> Result<Option<StructParts>, CheckError> {
    match crate::arena::monad::intern_n_node(pers, st, crate::arena::store::NNodeView::Anonymous) {
        Err(e) => Err(e),
        Ok(anon) => {
            if core::nidx_vec_beq(&cv_r.level_params, &cv_t.level_params) {
                match struct_shape(
                    pers,
                    st,
                    &cv_t.name,
                    &cv_c.name,
                    &cv_t.level_params,
                    &anon,
                    false,
                    n_p,
                    n_f,
                    &cv_t.ty,
                    &cv_c.ty,
                    &cv_r.ty,
                ) {
                    Err(e) => Err(e),
                    Ok(false) => Ok(None),
                    Ok(true) => Ok(Some(StructParts {
                        cv_t: crate::arena::env::i_constant_val_dup(cv_t),
                        cv_c: crate::arena::env::i_constant_val_dup(cv_c),
                        n_p,
                        n_f,
                        cv_r: crate::arena::env::i_constant_val_dup(cv_r),
                        elim: anon,
                        res_sort: s.dup2(),
                        rhs: rule.rhs.dup2(),
                        large: false,
                        is_prop,
                    })),
                }
            } else {
                Ok(None)
            }
        }
    }
}

// ---------------------------------------------------------------------------
// The projection bodies (`StructParts.lean:313-335` of the twin)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/Inductives/StructParts.lean:331-337 structProjPs
/// Lean twin: `proof/ConRon/Arena/Inductives/StructParts.lean:318 structProjPs`
/// — the parameter spine of the generated projection types, spelled at the
/// frame of the final `∀ p⃗ (t : T p⃗), _` telescope: `p_k = bvar (nP - k)`.
pub fn struct_proj_ps(pers: &PersTier, st: &mut AState, n_p: u64) -> Result<Vec<EIdx>, CheckError> {
    struct_ps_at(pers, st, 1, n_p)
}

/// con-leche: ConLeche/Kernel/Inductives/StructParts.lean:339-345 structProjArgP
/// Lean twin: `proof/ConRon/Arena/Inductives/StructParts.lean:323-325 structProjArgP`
/// — the `j`-th earlier-field substitute in a tower entry's generated type: the
/// first-class node `t.j` (`.proj T j` of the subject).
pub fn struct_proj_arg_p(
    pers: &PersTier,
    st: &mut AState,
    t: &NIdx,
    j: u64,
) -> Result<EIdx, CheckError>  {
    match intern_e_bvar(pers, st, 0) {
        Err(e) => Err(e),
        Ok(b) => intern_e_proj(pers, st, t.dup2(), j, b),
    }
}

/// con-leche: ConLeche/Kernel/Inductives/StructParts.lean:347-354 structProjResidP
/// Lean twin: `proof/ConRon/Arena/Inductives/StructParts.lean:330-335 structProjResidP`
/// — `structProjResid` in the `.proj`-node spelling: the constructor telescope
/// peeled at the parameters and the first `i` subject projections.
pub fn struct_proj_resid_p(
    pers: &PersTier,
    st: &mut AState,
    t: &NIdx,
    n_p: u64,
    cty: &EIdx,
    i: u64,
) -> Result<Option<EIdx>, CheckError> {
    if i == 0 {
        match struct_proj_ps(pers, st, n_p) {
            Err(e) => Err(e),
            Ok(ps) => expr_ops::inst_pis_at_lift(pers, st, CORE_WALK_FUEL, &ps, cty),
        }
    } else {
        match struct_proj_resid_p(pers, st, t, n_p, cty, i - 1) {
            Err(e) => Err(e),
            Ok(None) => Ok(None),
            Ok(Some(r)) => match struct_proj_arg_p(pers, st, t, i - 1) {
                Err(e) => Err(e),
                Ok(a) => {
                    let mut args: Vec<EIdx> = Vec::new();
                    args.push(a);
                    expr_ops::inst_pis_at_lift(pers, st, CORE_WALK_FUEL, &args, &r)
                }
            },
        }
    }
}

// ---------------------------------------------------------------------------
// `hasLooseBVar` — one twin for the pure walk, the cutoff and the memo
// (`StructParts.lean:337-397` of the twin)
// ---------------------------------------------------------------------------

/// con-leche: none — extraction rule 5 (DESIGN.md's task #97-P4c): a `HashMap::get` match is its own function
/// Lean twin: `proof/ConRon/Arena/Inductives/StructParts.lean:367 hasLooseBVarBGo`
/// — the `memo[(h, i)]?` probe of the `hasLooseBVarB` walk.  Inline, Aeneas
/// reports *"Could not match the contexts"* on the joined arms.
pub fn hlb_probe(memo: &HashMap<EIdxNat, bool>, k: &EIdxNat) -> Option<bool> {
    match memo.get(k) {
        Some(r) => Some(*r),
        None => None,
    }
}

/// con-leche: ConLeche/Kernel/Inductives/StructParts.lean:435-440 Expr.hasLooseBVarBIns
/// Lean twin: `proof/ConRon/Arena/Inductives/StructParts.lean:341-344 hasLooseBVarBIns`
/// — record one answer for `(e, i)` in the memo the walk hands back.
pub fn has_loose_bvar_b_ins(
    e: &EIdx,
    i: u64,
    r: (bool, HashMap<EIdxNat, bool>),
) -> (bool, HashMap<EIdxNat, bool>) {
    let mut memo: HashMap<EIdxNat, bool> = r.1;
    memo.insert(eidx_nat_key(e, i), r.0);
    (r.0, memo)
}

/// con-leche: ConLeche/Kernel/Inductives/StructParts.lean:356-369 Expr.hasLooseBVar
/// con-leche: ConLeche/Kernel/Inductives/StructParts.lean:371-390 Expr.hasLooseBVarB
/// con-leche: ConLeche/Kernel/Inductives/StructParts.lean:442-478 Expr.hasLooseBVarBGo
/// Lean twin: `proof/ConRon/Arena/Inductives/StructParts.lean:354-392 hasLooseBVarBGo`
/// — does `bvar i` occur loose in `e`?  con-leche's packed-bound cutoff
/// (`bvarB ≤ i`) and its per-call memo, both kept: the cutoff stops the walk
/// where the variable CANNOT occur, the memo shares a shared node's answer
/// across the paths that reach it.  The memo is keyed by the node AND the
/// index, because the index shifts under binders.
pub fn has_loose_bvar_b_go(
    pers: &PersTier,
    st: &mut AState,
    memo: HashMap<EIdxNat, bool>,
    i: u64,
    fuel: u64,
    h: &EIdx,
) -> Result<(bool, HashMap<EIdxNat, bool>), CheckError> {
    if fuel == 0 {
        fail(CheckError::Internal(code_points(&M_FUEL_HLB)))
    } else {
        match expr_ops::bvar_b(pers, st, fuel - 1, h) {
            Err(e) => Err(e),
            Ok(bb) => {
                if bb <= i {
                    Ok((false, memo))
                } else {
                    match view(pers, st, h) {
                        Err(e) => Err(e),
                        Ok(ENodeView::BVar(j)) => Ok((i == j, memo)),
                        Ok(ENodeView::FVar(_, _)) => Ok((false, memo)),
                        Ok(ENodeView::Sort(_)) => Ok((false, memo)),
                        Ok(ENodeView::Const(_, _)) => Ok((false, memo)),
                        Ok(ENodeView::Lit(_)) => Ok((false, memo)),
                        Ok(v) => {
                            let k: EIdxNat = eidx_nat_key(h, i);
                            match hlb_probe(&memo, &k) {
                                Some(r) => Ok((r, memo)),
                                None => match has_loose_bvar_b_node(pers, st, memo, i, fuel - 1, v) {
                                    Err(e) => Err(e),
                                    Ok(r) => Ok(has_loose_bvar_b_ins(h, i, r)),
                                },
                            }
                        }
                    }
                }
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/StructParts.lean:442-478 Expr.hasLooseBVarBGo
/// Lean twin: `proof/ConRon/Arena/Inductives/StructParts.lean:370-391 hasLooseBVarBGo`
/// — the walk's compound arms, split off so that the `view`'s loans are dead
/// at the memo's join (task #97-P4c's extraction rule 5, and P4a's second).
pub fn has_loose_bvar_b_node(
    pers: &PersTier,
    st: &mut AState,
    memo: HashMap<EIdxNat, bool>,
    i: u64,
    fuel: u64,
    v: ENodeView,
) -> Result<(bool, HashMap<EIdxNat, bool>), CheckError> {
    match v {
        ENodeView::App(f, a) => match has_loose_bvar_b_go(pers, st, memo, i, fuel, &f) {
            Err(e) => Err(e),
            Ok((true, m)) => Ok((true, m)),
            Ok((false, m)) => has_loose_bvar_b_go(pers, st, m, i, fuel, &a),
        },
        ENodeView::Lam(ty, b, _) => match has_loose_bvar_b_go(pers, st, memo, i, fuel, &ty) {
            Err(e) => Err(e),
            Ok((true, m)) => Ok((true, m)),
            Ok((false, m)) => has_loose_bvar_b_go(pers, st, m, i + 1, fuel, &b),
        },
        ENodeView::ForallE(ty, b, _) => match has_loose_bvar_b_go(pers, st, memo, i, fuel, &ty) {
            Err(e) => Err(e),
            Ok((true, m)) => Ok((true, m)),
            Ok((false, m)) => has_loose_bvar_b_go(pers, st, m, i + 1, fuel, &b),
        },
        ENodeView::LetE(t, val, b) => match has_loose_bvar_b_go(pers, st, memo, i, fuel, &t) {
            Err(e) => Err(e),
            Ok((true, m)) => Ok((true, m)),
            Ok((false, m)) => match has_loose_bvar_b_go(pers, st, m, i, fuel, &val) {
                Err(e) => Err(e),
                Ok((true, m2)) => Ok((true, m2)),
                Ok((false, m2)) => has_loose_bvar_b_go(pers, st, m2, i + 1, fuel, &b),
            },
        },
        ENodeView::Proj(_, _, sub) => has_loose_bvar_b_go(pers, st, memo, i, fuel, &sub),
        _ => Ok((false, memo)),
    }
}

/// con-leche: ConLeche/Kernel/Inductives/StructParts.lean:624-626 Expr.hasLooseBVarBFast
/// Lean twin: `proof/ConRon/Arena/Inductives/StructParts.lean:396-397 hasLooseBVarBFast`
/// — the executed `hasLooseBVarB` (one memoized DAG walk).
pub fn has_loose_bvar_b_fast(
    pers: &PersTier,
    st: &mut AState,
    i: u64,
    e: &EIdx,
) -> Result<bool, CheckError>  {
    match has_loose_bvar_b_go(pers, st, HashMap::new(), i, CORE_WALK_FUEL, e) {
        Err(er) => Err(er),
        Ok(r) => Ok(r.0),
    }
}

// ---------------------------------------------------------------------------
// `structUsedLater` and the guard table (`StructParts.lean:399-451`)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/Inductives/StructParts.lean:633-641 structUsedLater
/// Lean twin: `proof/ConRon/Arena/Inductives/StructParts.lean:402-405 structUsedLater`
/// — **field `j` is used by a later field**, the official `infer_proj`'s
/// `has_loose_bvars(binding_body(r))` at step `j`.
pub fn struct_used_later(
    pers: &PersTier,
    st: &mut AState,
    cty: &EIdx,
    n_p: u64,
    j: u64,
) -> Result<bool, CheckError> {
    match expr_ops::strip_pis(pers, st, n_p + j + 1, cty) {
        Err(e) => Err(e),
        Ok(Some(q)) => has_loose_bvar_b_fast(pers, st, 0, &q.1),
        Ok(None) => Ok(false),
    }
}

/// con-leche: ConLeche/Kernel/Inductives/StructParts.lean:669-674 structUsedLaterGo
/// Lean twin: `proof/ConRon/Arena/Inductives/StructParts.lean:409-413 structUsedLaterGo`
/// — memoized `structUsedLater`, taking and returning the shared memo.
pub fn struct_used_later_go(
    pers: &PersTier,
    st: &mut AState,
    memo: HashMap<EIdxNat, bool>,
    cty: &EIdx,
    n_p: u64,
    j: u64,
) -> Result<(bool, HashMap<EIdxNat, bool>), CheckError> {
    match expr_ops::strip_pis(pers, st, n_p + j + 1, cty) {
        Err(e) => Err(e),
        Ok(Some(q)) => has_loose_bvar_b_go(pers, st, memo, 0, CORE_WALK_FUEL, &q.1),
        Ok(None) => Ok((false, memo)),
    }
}

/// con-leche: ConLeche/Kernel/Inductives/StructParts.lean:685-692 structUsedLaterList
/// Lean twin: `proof/ConRon/Arena/Inductives/StructParts.lean:418-424 structUsedLaterList`
/// — `structUsedLater cty nP j` for `j = base, …, base + n - 1`, in order,
/// through one shared memo.  Lean conses on the way out; the port pushes on the
/// way in, which is the same list at the same order of effects.
pub fn struct_used_later_list(
    pers: &PersTier,
    st: &mut AState,
    memo: HashMap<EIdxNat, bool>,
    cty: &EIdx,
    n_p: u64,
    n: u64,
    base: u64,
    out: Vec<bool>,
) -> Result<Vec<bool>, CheckError> {
    if n == 0 {
        Ok(out)
    } else {
        match struct_used_later_go(pers, st, memo, cty, n_p, base) {
            Err(e) => Err(e),
            Ok((r, m)) => {
                let mut o: Vec<bool> = out;
                o.push(r);
                struct_used_later_list(pers, st, m, cty, n_p, n - 1, base + 1, o)
            }
        }
    }
}

/// con-leche: none — `used.getD j false` over a `Vec<bool>`
/// Lean twin: `proof/ConRon/Arena/Inductives/StructParts.lean:441 structProjGuards`
/// — the out-of-range fallback the guard fold spells at every read.
pub fn used_get_d(used: &Vec<bool>, j: u64) -> bool {
    if (j as usize) < used.len() {
        used[j as usize]
    } else {
        false
    }
}

/// con-leche: none — `sorts.getD j z` over a `Vec<LIdx>`
/// Lean twin: `proof/ConRon/Arena/Inductives/StructParts.lean:442 structProjGuards`
/// — the out-of-range fallback (`zeroLevel`) the guard fold spells at every
/// read.
pub fn sort_get_d(sorts: &Vec<LIdx>, j: u64, z: &LIdx) -> LIdx {
    if (j as usize) < sorts.len() {
        sorts[j as usize].dup2()
    } else {
        z.dup2()
    }
}

/// con-leche: ConLeche/Kernel/Inductives/StructParts.lean:643-656 structProjGuards
/// con-leche: ConLeche/Kernel/Inductives/StructParts.lean:722-732 structProjGuardsFast
/// Lean twin: `proof/ConRon/Arena/Inductives/StructParts.lean:438-444 structProjGuards.col`
/// — the inner fold: field `i`'s own sort joined with the sorts of the earlier
/// fields that a later field uses.
pub fn struct_proj_guards_col(
    pers: &PersTier,
    st: &mut AState,
    used: &Vec<bool>,
    sorts: &Vec<LIdx>,
    z: &LIdx,
    j: u64,
    k: u64,
    acc: LIdx,
) -> Result<LIdx, CheckError> {
    if k == 0 {
        Ok(acc)
    } else if used_get_d(used, j) {
        let s: LIdx = sort_get_d(sorts, j, z);
        match intern_l_node(pers, st, LNodeView::Max(acc, s)) {
            Err(e) => Err(e),
            Ok(m) => struct_proj_guards_col(pers, st, used, sorts, z, j + 1, k - 1, m),
        }
    } else {
        struct_proj_guards_col(pers, st, used, sorts, z, j + 1, k - 1, acc)
    }
}

/// con-leche: ConLeche/Kernel/Inductives/StructParts.lean:643-656 structProjGuards
/// con-leche: ConLeche/Kernel/Inductives/StructParts.lean:722-732 structProjGuardsFast
/// Lean twin: `proof/ConRon/Arena/Inductives/StructParts.lean:445-450 structProjGuards.row`
/// — the outer fold, one guard level per field.  Lean conses on the way out;
/// the port pushes on the way in, at the same order of effects.
pub fn struct_proj_guards_row(
    pers: &PersTier,
    st: &mut AState,
    used: &Vec<bool>,
    sorts: &Vec<LIdx>,
    z: &LIdx,
    i: u64,
    k: u64,
    out: Vec<LIdx>,
) -> Result<Vec<LIdx>, CheckError> {
    if k == 0 {
        Ok(out)
    } else {
        let a: LIdx = sort_get_d(sorts, i, z);
        match struct_proj_guards_col(pers, st, used, sorts, z, 0, i, a) {
            Err(e) => Err(e),
            Ok(g) => {
                let mut o: Vec<LIdx> = out;
                o.push(g);
                struct_proj_guards_row(pers, st, used, sorts, z, i + 1, k - 1, o)
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/StructParts.lean:643-656 structProjGuards
/// con-leche: ConLeche/Kernel/Inductives/StructParts.lean:722-732 structProjGuardsFast
/// Lean twin: `proof/ConRon/Arena/Inductives/StructParts.lean:434-451 structProjGuards`
/// — **the projection guard levels**.  con-leche's two forms are one twin: the
/// `nF` `structUsedLater` answers are computed first through one shared memo
/// (its task #236 arrangement), then the fold runs over the recorded answers.
/// `sorts` and the result are a `Vec<LIdx>` — the twin's module note says why.
pub fn struct_proj_guards(
    pers: &PersTier,
    st: &mut AState,
    cty: &EIdx,
    n_p: u64,
    n_f: u64,
    sorts: &Vec<LIdx>,
) -> Result<Vec<LIdx>, CheckError> {
    match core::zero_level(st) {
        Err(e) => Err(e),
        Ok(z) => match struct_used_later_list(pers, st, HashMap::new(), cty, n_p, n_f, 0, Vec::new()) {
            Err(e) => Err(e),
            Ok(used) => struct_proj_guards_row(pers, st, &used, sorts, &z, 0, n_f, Vec::new()),
        },
    }
}

/// con-leche: ConLeche/Kernel/Inductives/StructParts.lean:748-766 structProjBodiesGo
/// Lean twin: `proof/ConRon/Arena/Inductives/StructParts.lean:457-467 structProjBodiesGo`
/// — **the projection bodies of a recognised block**, one walk of the
/// constructor telescope: field `i`'s domain is body `i`, and the field is
/// replaced by the subject's projection `.proj T i (bvar 0)` before the walk
/// continues.  Lean conses on the way out; the port pushes on the way in.
pub fn struct_proj_bodies_go(
    pers: &PersTier,
    st: &mut AState,
    t: &NIdx,
    k: u64,
    i: u64,
    h: &EIdx,
    out: Vec<EIdx>,
) -> Result<Option<Vec<EIdx>>, CheckError> {
    if k == 0 {
        Ok(Some(out))
    } else {
        if h.tag() == ETAG_FORALL_E {
            match view_bind(pers, st, h) {
                None => fail_dangling_e(),
                Some((fdom, body, _)) => match struct_proj_arg_p(pers, st, t, i) {
                    Err(e) => Err(e),
                    Ok(a) => match expr_ops::instantiate1_lift_fast(pers, st, CORE_WALK_FUEL, &body, &a, 0) {
                        Err(e) => Err(e),
                        Ok(b) => {
                            let mut o: Vec<EIdx> = out;
                            o.push(fdom);
                            struct_proj_bodies_go(pers, st, t, k - 1, i + 1, &b, o)
                        }
                    },
                },
            }
        } else {
            Ok(None)
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/StructParts.lean:768-771 structProjBodies
/// Lean twin: `proof/ConRon/Arena/Inductives/StructParts.lean:471-478 structProjBodies`
/// — the block's projection bodies, as the table stores them.
pub fn struct_proj_bodies(
    pers: &PersTier,
    st: &mut AState,
    t: &NIdx,
    n_p: u64,
    n_f: u64,
    cty: &EIdx,
) -> Result<Option<Vec<EIdx>>, CheckError> {
    match struct_proj_ps(pers, st, n_p) {
        Err(e) => Err(e),
        Ok(ps) => match expr_ops::inst_pis_at_lift(pers, st, CORE_WALK_FUEL, &ps, cty) {
            Err(e) => Err(e),
            Ok(None) => Ok(None),
            Ok(Some(r)) => struct_proj_bodies_go(pers, st, t, n_f, 0, &r, Vec::new()),
        },
    }
}

// ---------------------------------------------------------------------------
// `mentionsConst` — one twin for the pure walk and the memo
// (`StructParts.lean:480-528` of the twin)
// ---------------------------------------------------------------------------

/// con-leche: none — extraction rule 5 (DESIGN.md's task #97-P4c): a `HashMap::get` match is its own function
/// Lean twin: `proof/ConRon/Arena/Inductives/StructParts.lean:497 mentionsConstGo`
/// — the `memo[h]?` probe of the `mentionsConst` walk.
pub fn mc_probe(memo: &HashMap<EIdx, bool>, k: &EIdx) -> Option<bool> {
    match memo.get(k) {
        Some(r) => Some(*r),
        None => None,
    }
}

/// con-leche: ConLeche/Kernel/Inductives/StructParts.lean:773-782 Expr.mentionsConst
/// con-leche: ConLeche/Kernel/Inductives/StructParts.lean:814-849 Expr.mentionsConstGo
/// Lean twin: `proof/ConRon/Arena/Inductives/StructParts.lean:487-523 mentionsConstGo`
/// — does the constant `T` occur in `e`?  A syntactic walk (`fvar`
/// annotations included; a `.proj` node names its structure), with con-leche's
/// per-call memo keyed by the node — `T` is fixed for the whole walk.
pub fn mentions_const_go(
    pers: &PersTier,
    st: &mut AState,
    t: &NIdx,
    memo: HashMap<EIdx, bool>,
    fuel: u64,
    h: &EIdx,
) -> Result<(bool, HashMap<EIdx, bool>), CheckError> {
    if fuel == 0 {
        fail(CheckError::Internal(code_points(&M_FUEL_MENTIONS)))
    } else {
        match view(pers, st, h) {
            Err(e) => Err(e),
            Ok(ENodeView::BVar(_)) => Ok((false, memo)),
            Ok(ENodeView::Sort(_)) => Ok((false, memo)),
            Ok(ENodeView::Lit(_)) => Ok((false, memo)),
            Ok(ENodeView::Const(n, _)) => Ok((n.eq2(t), memo)),
            Ok(v) => match mc_probe(&memo, h) {
                Some(r) => Ok((r, memo)),
                None => match mentions_const_node(pers, st, t, memo, fuel - 1, v) {
                    Err(e) => Err(e),
                    Ok((r, m)) => {
                        let mut m2: HashMap<EIdx, bool> = m;
                        m2.insert(h.dup2(), r);
                        Ok((r, m2))
                    }
                },
            },
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/StructParts.lean:814-849 Expr.mentionsConstGo
/// Lean twin: `proof/ConRon/Arena/Inductives/StructParts.lean:500-522 mentionsConstGo`
/// — the walk's compound arms, split off so that the `view`'s loans are dead at
/// the memo's join (extraction rule 5).
pub fn mentions_const_node(
    pers: &PersTier,
    st: &mut AState,
    t: &NIdx,
    memo: HashMap<EIdx, bool>,
    fuel: u64,
    v: ENodeView,
) -> Result<(bool, HashMap<EIdx, bool>), CheckError> {
    match v {
        ENodeView::FVar(_, ty) => mentions_const_go(pers, st, t, memo, fuel, &ty),
        ENodeView::App(f, a) => match mentions_const_go(pers, st, t, memo, fuel, &f) {
            Err(e) => Err(e),
            Ok((b1, m)) => match mentions_const_go(pers, st, t, m, fuel, &a) {
                Err(e) => Err(e),
                Ok((b2, m2)) => Ok((b1 || b2, m2)),
            },
        },
        ENodeView::Lam(ty, body, _) => match mentions_const_go(pers, st, t, memo, fuel, &ty) {
            Err(e) => Err(e),
            Ok((b1, m)) => match mentions_const_go(pers, st, t, m, fuel, &body) {
                Err(e) => Err(e),
                Ok((b2, m2)) => Ok((b1 || b2, m2)),
            },
        },
        ENodeView::ForallE(ty, body, _) => match mentions_const_go(pers, st, t, memo, fuel, &ty) {
            Err(e) => Err(e),
            Ok((b1, m)) => match mentions_const_go(pers, st, t, m, fuel, &body) {
                Err(e) => Err(e),
                Ok((b2, m2)) => Ok((b1 || b2, m2)),
            },
        },
        ENodeView::LetE(ty, val, body) => match mentions_const_go(pers, st, t, memo, fuel, &ty) {
            Err(e) => Err(e),
            Ok((b1, m)) => match mentions_const_go(pers, st, t, m, fuel, &val) {
                Err(e) => Err(e),
                Ok((b2, m2)) => match mentions_const_go(pers, st, t, m2, fuel, &body) {
                    Err(e) => Err(e),
                    Ok((b3, m3)) => Ok((b1 || b2 || b3, m3)),
                },
            },
        },
        ENodeView::Proj(s, _, sub) => match mentions_const_go(pers, st, t, memo, fuel, &sub) {
            Err(e) => Err(e),
            Ok((b, m)) => Ok((s.eq2(t) || b, m)),
        },
        _ => Ok((false, memo)),
    }
}

/// con-leche: ConLeche/Kernel/Inductives/StructParts.lean:922-924 Expr.mentionsConstFast
/// Lean twin: `proof/ConRon/Arena/Inductives/StructParts.lean:527-528 mentionsConst`
/// — the executed `mentionsConst` (one memoized DAG walk).
pub fn mentions_const(
    pers: &PersTier,
    st: &mut AState,
    t: &NIdx,
    e: &EIdx,
) -> Result<bool, CheckError>  {
    match mentions_const_go(pers, st, t, HashMap::new(), CORE_WALK_FUEL, e) {
        Err(er) => Err(er),
        Ok(r) => Ok(r.0),
    }
}
