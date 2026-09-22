//! `arena::inductives::native_parts` — the direct recursive class.
//!
//! The Rust twin of `proof/ConRon/Arena/Inductives/NativeParts.lean`, which is
//! `ConLeche/Kernel/Inductives/NativeParts.lean` whole over handles: the field
//! kinds and official's positivity classification, the generated recursor with
//! its inductive-hypothesis binders, the comparison of the stream's rules
//! against the generated ones, and the recogniser.
//!
//! ## The twin's deviations
//!
//! * **`RecFieldKind` is TWINNED, not imported.**  It carries no term, so
//!   DESIGN.md §8.7's rule would have (B) import con-leche's; it cannot,
//!   because the cited file also declares `structFam`, `structPsAt`,
//!   `structShape`, `sumSplit`, `InductiveShape` and `NativeParts`, and every
//!   arena module does `open ConLeche`.  Five constructors and no field is a
//!   cheap copy.
//! * **`structIhPis` and `structRuleBodyR` take the constructor type, not two
//!   functions.**  con-leche passes `teleOf`/`idxOf` and every call site
//!   instantiates them at `structFieldTeleOf cty nP nF` and
//!   `structFieldIdxOf cty nP nF`; two closures per call is what DESIGN.md
//!   §3.4 forbids, so the twins take `cty` and the counts and call the two
//!   readers themselves.
//! * **`nativeRecPinOk`, `nativeRecLpsOk`, `recIdxOf`, `NativeParts.complete`
//!   and `NativeParts.withKinds` stay PURE** — they read counts, names and
//!   tags and touch no term.
//!
//! `NativeParts extends InductiveShape` is a `shape` field here, as
//! `con_ron_core::kernel::inductives::native_parts`' is.

use super::struct_parts;
use super::sum_parts;
use super::sum_parts::InductiveShape;
use crate::arena::core;
use crate::arena::core::CORE_WALK_FUEL;
use crate::arena::env;
use crate::arena::env::{IConstantInfo, IConstantVal, IRecRule};
use crate::arena::expr_ops;
use crate::arena::handle::{EIdx, LIdx, LsIdx, NIdx, ETAG_CONST, ETAG_FORALL_E, ETAG_SORT};
use crate::arena::monad::{
    AState, fail, fail_dangling_e, intern_e_bvar, intern_e_const, intern_e_forall_e, intern_e_lam, read_level_m, view_bind, view_const_name, view_sort,
};
use crate::kernel::core_types;
use crate::kernel::core_types::{code_points, CheckError};
use crate::kernel::expr;
use crate::kernel::expr::BinderMeta;
use crate::kernel::expr_ops::sub_nat;
use crate::kernel::level;
use crate::kernel::prop_when;
use crate::kernel::prop_when::PropWhen;
use crate::ron::hashmap::{Dup, Eq2};
use crate::arena::store::PersTier;

// ---------------------------------------------------------------------------
// The messages of this module's declines
// ---------------------------------------------------------------------------

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `'fuel exhausted: recPositivity'`, as code points.
pub const M_FUEL_POS: [u32; 29] = [
    102, 117, 101, 108, 32, 101, 120, 104, 97, 117, 115, 116, 101, 100, 58, 32, 114, 101, 99, 80,
    111, 115, 105, 116, 105, 118, 105, 116, 121,
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `'fuel exhausted: piBinders'`, as code points.
pub const M_FUEL_PI_BINDERS: [u32; 25] = [
    102, 117, 101, 108, 32, 101, 120, 104, 97, 117, 115, 116, 101, 100, 58, 32, 112, 105, 66, 105,
    110, 100, 101, 114, 115,
];

// ---------------------------------------------------------------------------
// The field kinds (`NativeParts.lean:40-127` of the twin)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/Inductives/NativeParts.lean:60-76 RecFieldKind
/// Lean twin: `proof/ConRon/Arena/Inductives/NativeParts.lean:45-56 RecFieldKind`
/// — the kind of a constructor field of a recursive block.  Twinned rather
/// than imported; see the module note.
pub enum RecFieldKind {
    /// the domain does not mention the block
    Ordinary,
    /// the domain is exactly `T p⃗ e⃗`: a finitary recursive field
    Recursive,
    /// the domain is `Π a⃗ : A⃗, T p⃗ e⃗(a⃗)` with `A⃗` free of the block
    Reflexive,
    /// a non-positive (or non-valid) occurrence: the official kernel rejects
    Negative,
    /// an occurrence the official kernel accepts that this route does not model
    Unsupported,
}

/// con-leche: ConLeche/Kernel/Inductives/NativeParts.lean:60-76 RecFieldKind
/// Lean twin: `proof/ConRon/Arena/Inductives/NativeParts.lean:45-56 RecFieldKind`
/// — the cited `deriving Inhabited`'s copy; a kind is a tag.
pub fn rec_field_kind_dup(k: &RecFieldKind) -> RecFieldKind {
    match k {
        RecFieldKind::Ordinary => RecFieldKind::Ordinary,
        RecFieldKind::Recursive => RecFieldKind::Recursive,
        RecFieldKind::Reflexive => RecFieldKind::Reflexive,
        RecFieldKind::Negative => RecFieldKind::Negative,
        RecFieldKind::Unsupported => RecFieldKind::Unsupported,
    }
}

/// con-leche: ConLeche/Kernel/Inductives/NativeParts.lean:60-76 RecFieldKind
/// Lean twin: `proof/ConRon/Arena/Inductives/NativeParts.lean:45-56 RecFieldKind`
/// — the cited `deriving DecidableEq`, spelled out (§3.4 forbids `#[derive]`).
pub fn rec_field_kind_beq(a: &RecFieldKind, b: &RecFieldKind) -> bool {
    match (a, b) {
        (RecFieldKind::Ordinary, RecFieldKind::Ordinary) => true,
        (RecFieldKind::Recursive, RecFieldKind::Recursive) => true,
        (RecFieldKind::Reflexive, RecFieldKind::Reflexive) => true,
        (RecFieldKind::Negative, RecFieldKind::Negative) => true,
        (RecFieldKind::Unsupported, RecFieldKind::Unsupported) => true,
        _ => false,
    }
}

/// con-leche: none — a `List RecFieldKind` copy; Lean shares the list
/// Lean twin: `proof/ConRon/Arena/Inductives/NativeParts.lean:171 NativeParts`.
pub fn kinds_copy(ks: &Vec<RecFieldKind>, i: usize, out: Vec<RecFieldKind>) -> Vec<RecFieldKind> {
    if i >= ks.len() {
        out
    } else {
        let mut o: Vec<RecFieldKind> = out;
        o.push(rec_field_kind_dup(&ks[i]));
        kinds_copy(ks, i + 1, o)
    }
}

/// con-leche: none — a `List (List RecFieldKind)` copy
/// Lean twin: `proof/ConRon/Arena/Inductives/NativeParts.lean:171 NativeParts`.
pub fn kindss_copy(
    kss: &Vec<Vec<RecFieldKind>>,
    i: usize,
    out: Vec<Vec<RecFieldKind>>,
) -> Vec<Vec<RecFieldKind>> {
    if i >= kss.len() {
        out
    } else {
        let mut o: Vec<Vec<RecFieldKind>> = out;
        o.push(kinds_copy(&kss[i], 0, Vec::new()));
        kindss_copy(kss, i + 1, o)
    }
}

/// con-leche: none — `ks.getD i .ordinary` over a `Vec<RecFieldKind>`
/// Lean twin: `proof/ConRon/Arena/Inductives/NativeParts.lean:165 recIdxOf` —
/// the out-of-range fallback the kind readers spell.
pub fn kind_get_d(ks: &Vec<RecFieldKind>, i: u64) -> RecFieldKind {
    if (i as usize) < ks.len() {
        rec_field_kind_dup(&ks[i as usize])
    } else {
        RecFieldKind::Ordinary
    }
}

/// con-leche: ConLeche/Kernel/Inductives/NativeParts.lean:78-87 recFamOk
/// Lean twin: `proof/ConRon/Arena/Inductives/NativeParts.lean:62-69 recFamOk` —
/// is `e` the family at the parameter variables (sitting `o` binders up)
/// followed by `nIdx` index expressions none of which mentions the block?
/// Official's `is_valid_ind_app` exactly.
#[allow(clippy::too_many_arguments)]
pub fn rec_fam_ok(
    pers: &PersTier,
    st: &mut AState,
    t: &NIdx,
    lps: &Vec<NIdx>,
    n_p: u64,
    n_idx: u64,
    o: u64,
    e: &EIdx,
) -> Result<bool, CheckError> {
    match struct_parts::param_levels(pers, st, lps) {
        Err(er) => Err(er),
        Ok(us) => match intern_e_const(pers, st, t.dup2(), us) {
            Err(er) => Err(er),
            Ok(hd) => match expr_ops::get_app_fn(pers, st, CORE_WALK_FUEL, e) {
                Err(er) => Err(er),
                Ok(fna) => match expr_ops::get_app_args(pers, st, CORE_WALK_FUEL, e) {
                    Err(er) => Err(er),
                    Ok(args) => match struct_parts::struct_ps_at(pers, st, o, n_p) {
                        Err(er) => Err(er),
                        Ok(ps) => {
                            if !(fna.eq2(&hd)
                                && args.len() as u64 == n_p + n_idx
                                && expr_ops::eidx_take_beq(&args, &ps))
                            {
                                Ok(false)
                            } else {
                                let idx: Vec<EIdx> = core::drop_eidx(&args, n_p as usize);
                                idx_free_of(pers, st, t, &idx, 0)
                            }
                        }
                    },
                },
            },
        },
    }
}

/// con-leche: ConLeche/Kernel/Inductives/NativeParts.lean:78-87 recFamOk
/// Lean twin: `proof/ConRon/Arena/Inductives/NativeParts.lean:69 recFamOk` —
/// the `(args.drop nP).allM` of the cited clause: no index expression mentions
/// the block.
pub fn idx_free_of(
    pers: &PersTier,
    st: &mut AState,
    t: &NIdx,
    idx: &Vec<EIdx>,
    i: usize,
) -> Result<bool, CheckError> {
    if i >= idx.len() {
        Ok(true)
    } else {
        let a: EIdx = idx[i].dup2();
        match struct_parts::mentions_const(pers, st, t, &a) {
            Err(e) => Err(e),
            Ok(true) => Ok(false),
            Ok(false) => idx_free_of(pers, st, t, idx, i + 1),
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/NativeParts.lean:89-111 recPositivity
/// Lean twin: `proof/ConRon/Arena/Inductives/NativeParts.lean:74-98 recPositivity`
/// — official `check_positivity`'s telescope walk on a field domain that
/// mentions the block, syntactically.
#[allow(clippy::too_many_arguments)]
pub fn rec_positivity(
    pers: &PersTier,
    st: &mut AState,
    t: &NIdx,
    lps: &Vec<NIdx>,
    n_p: u64,
    n_idx: u64,
    o: u64,
    fuel: u64,
    h: &EIdx,
    k: u64,
) -> Result<RecFieldKind, CheckError> {
    if fuel == 0 {
        fail(core_types::internal(code_points(&M_FUEL_POS)))
    } else {
        if h.tag() == ETAG_FORALL_E {
            match view_bind(pers, st, h) {
                None => fail_dangling_e(),
                Some((dom, body, _)) => {
                    match struct_parts::mentions_const(pers, st, t, &dom) {
                        Err(e) => Err(e),
                        Ok(true) => Ok(RecFieldKind::Negative),
                        Ok(false) => rec_positivity(pers, st, t, lps, n_p, n_idx, o, fuel - 1, &body, k + 1),
                    }
                },
            }
        } else {
            match struct_parts::mentions_const(pers, st, t, h) {
                Err(e) => Err(e),
                Ok(false) => Ok(RecFieldKind::Ordinary),
                Ok(true) => rec_positivity_at(pers, st, t, lps, n_p, n_idx, o, h, k),
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/NativeParts.lean:89-111 recPositivity
/// Lean twin: `proof/ConRon/Arena/Inductives/NativeParts.lean:83-98 recPositivity`
/// — the leaf of the walk: a head that is the family at exactly the parameter
/// variables is finitary (`k = 0`) or reflexive, any other occurrence of the
/// block is negative, and a head that is another constant is unsupported.
#[allow(clippy::too_many_arguments)]
pub fn rec_positivity_at(
    pers: &PersTier,
    st: &mut AState,
    t: &NIdx,
    lps: &Vec<NIdx>,
    n_p: u64,
    n_idx: u64,
    o: u64,
    h: &EIdx,
    k: u64,
) -> Result<RecFieldKind, CheckError> {
    match struct_parts::param_levels(pers, st, lps) {
        Err(e) => Err(e),
        Ok(us) => match intern_e_const(pers, st, t.dup2(), us) {
            Err(e) => Err(e),
            Ok(hd) => match expr_ops::get_app_fn(pers, st, CORE_WALK_FUEL, h) {
                Err(e) => Err(e),
                Ok(fna) => match expr_ops::get_app_args(pers, st, CORE_WALK_FUEL, h) {
                    Err(e) => Err(e),
                    Ok(args) => {
                        if fna.eq2(&hd) {
                            match struct_parts::struct_ps_at(pers, st, o + k, n_p) {
                                Err(e) => Err(e),
                                Ok(ps) => {
                                    if args.len() as u64 == n_p + n_idx
                                        && expr_ops::eidx_take_beq(&args, &ps)
                                    {
                                        match rec_fam_ok(pers, st, t, lps, n_p, n_idx, o + k, h) {
                                            Err(e) => Err(e),
                                            Ok(true) => {
                                                if k == 0 {
                                                    Ok(RecFieldKind::Recursive)
                                                } else {
                                                    Ok(RecFieldKind::Reflexive)
                                                }
                                            }
                                            Ok(false) => Ok(RecFieldKind::Negative),
                                        }
                                    } else {
                                        Ok(RecFieldKind::Negative)
                                    }
                                }
                            }
                        } else {
                            if fna.tag() == ETAG_CONST {
                                match view_const_name(pers, st, &fna) {
                                    None => fail_dangling_e(),
                                    Some(t2) => {
                                        if t2.eq2(t) {
                                            Ok(RecFieldKind::Negative)
                                        } else {
                                            Ok(RecFieldKind::Unsupported)
                                        }
                                    },
                                }
                            } else {
                                Ok(RecFieldKind::Unsupported)
                            }
                        }
                    }
                },
            },
        },
    }
}

/// con-leche: ConLeche/Kernel/Inductives/NativeParts.lean:113-116 recFieldKind
/// Lean twin: `proof/ConRon/Arena/Inductives/NativeParts.lean:103-106 recFieldKind`
/// — the kind of a field whose domain is `dom`, `o` fields into the
/// constructor's telescope.
#[allow(clippy::too_many_arguments)]
pub fn rec_field_kind(
    pers: &PersTier,
    st: &mut AState,
    t: &NIdx,
    lps: &Vec<NIdx>,
    n_p: u64,
    n_idx: u64,
    o: u64,
    dom: &EIdx,
) -> Result<RecFieldKind, CheckError> {
    match struct_parts::mentions_const(pers, st, t, dom) {
        Err(e) => Err(e),
        Ok(true) => rec_positivity(pers, st, t, lps, n_p, n_idx, o, CORE_WALK_FUEL, dom, 0),
        Ok(false) => Ok(RecFieldKind::Ordinary),
    }
}

/// con-leche: ConLeche/Kernel/Inductives/NativeParts.lean:118-145 recCtorKinds
/// Lean twin: `proof/ConRon/Arena/Inductives/NativeParts.lean:112-127 recCtorKinds`
/// — the kinds of one constructor's fields, off its (raw or annotated) type.
/// A recursive field that a LATER binder or the residual mentions is marked
/// unsupported; a residual that mentions the block anywhere past the
/// parameters makes every field negative.
pub fn rec_ctor_kinds(
    pers: &PersTier,
    st: &mut AState,
    t: &NIdx,
    lps: &Vec<NIdx>,
    n_p: u64,
    n_idx: u64,
    c: &(IConstantVal, u64),
) -> Result<Option<Vec<RecFieldKind>>, CheckError> {
    match expr_ops::strip_pis(pers, st, n_p + c.1, &c.0.ty) {
        Err(e) => Err(e),
        Ok(None) => Ok(None),
        Ok(Some(q)) => {
            match rec_ctor_kinds_from(pers, st, t, lps, n_p, n_idx, &c.0.ty, c.1, &q.0, 0, Vec::new()) {
                Err(e) => Err(e),
                Ok(ks) => match expr_ops::get_app_args(pers, st, CORE_WALK_FUEL, &q.1) {
                    Err(e) => Err(e),
                    Ok(cargs) => {
                        let idx: Vec<EIdx> = core::drop_eidx(&cargs, n_p as usize);
                        match idx_free_of(pers, st, t, &idx, 0) {
                            Err(e) => Err(e),
                            Ok(true) => Ok(Some(ks)),
                            Ok(false) => Ok(Some(all_negative(c.1, 0, Vec::new()))),
                        }
                    }
                },
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/NativeParts.lean:118-145 recCtorKinds
/// Lean twin: `proof/ConRon/Arena/Inductives/NativeParts.lean:116-122 recCtorKinds`
/// — the `(List.range c.2).mapM` of the cited clause, as a cursor recursion.
#[allow(clippy::too_many_arguments)]
pub fn rec_ctor_kinds_from(
    pers: &PersTier,
    st: &mut AState,
    t: &NIdx,
    lps: &Vec<NIdx>,
    n_p: u64,
    n_idx: u64,
    cty: &EIdx,
    n_f: u64,
    cbs: &Vec<(EIdx, BinderMeta)>,
    i: u64,
    out: Vec<RecFieldKind>,
) -> Result<Vec<RecFieldKind>, CheckError> {
    if i >= n_f {
        Ok(out)
    } else {
        let dom: EIdx = if ((n_p + i) as usize) < cbs.len() {
            cbs[(n_p + i) as usize].0.dup2()
        } else {
            EIdx::of_word(0)
        };
        match rec_field_kind(pers, st, t, lps, n_p, n_idx, i, &dom) {
            Err(e) => Err(e),
            Ok(k) => match rec_ctor_kind_at(pers, st, cty, n_p, i, k) {
                Err(e) => Err(e),
                Ok(k2) => {
                    let mut o: Vec<RecFieldKind> = out;
                    o.push(k2);
                    rec_ctor_kinds_from(pers, st, t, lps, n_p, n_idx, cty, n_f, cbs, i + 1, o)
                }
            },
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/NativeParts.lean:118-145 recCtorKinds
/// Lean twin: `proof/ConRon/Arena/Inductives/NativeParts.lean:118-122 recCtorKinds`
/// — a recursive or reflexive field a LATER field uses is unsupported; every
/// other kind passes through.
pub fn rec_ctor_kind_at(
    pers: &PersTier,
    st: &mut AState,
    cty: &EIdx,
    n_p: u64,
    i: u64,
    k: RecFieldKind,
) -> Result<RecFieldKind, CheckError> {
    match k {
        RecFieldKind::Recursive => match struct_parts::struct_used_later(pers, st, cty, n_p, i) {
            Err(e) => Err(e),
            Ok(true) => Ok(RecFieldKind::Unsupported),
            Ok(false) => Ok(RecFieldKind::Recursive),
        },
        RecFieldKind::Reflexive => match struct_parts::struct_used_later(pers, st, cty, n_p, i) {
            Err(e) => Err(e),
            Ok(true) => Ok(RecFieldKind::Unsupported),
            Ok(false) => Ok(RecFieldKind::Reflexive),
        },
        other => Ok(other),
    }
}

/// con-leche: ConLeche/Kernel/Inductives/NativeParts.lean:118-145 recCtorKinds
/// Lean twin: `proof/ConRon/Arena/Inductives/NativeParts.lean:126 recCtorKinds`
/// — `ks.map fun _ => .negative`, the verdict when the residual mentions the
/// block outside its parameters.
pub fn all_negative(n: u64, i: u64, out: Vec<RecFieldKind>) -> Vec<RecFieldKind> {
    if i >= n {
        out
    } else {
        let mut o: Vec<RecFieldKind> = out;
        o.push(RecFieldKind::Negative);
        all_negative(n, i + 1, o)
    }
}

/// con-leche: ConLeche/Kernel/Inductives/NativeParts.lean:147-154 Expr.piBinders
/// Lean twin: `proof/ConRon/Arena/Inductives/NativeParts.lean:131-138 piBinders`
/// — all leading `∀` binders of an expression (outermost first) and the body.
/// Lean conses on the way out; the port pushes on the way in.
pub fn pi_binders(
    pers: &PersTier,
    st: &AState,
    fuel: u64,
    h: &EIdx,
    out: Vec<(EIdx, BinderMeta)>,
) -> Result<(Vec<(EIdx, BinderMeta)>, EIdx), CheckError> {
    if fuel == 0 {
        fail(core_types::internal(code_points(&M_FUEL_PI_BINDERS)))
    } else {
        if h.tag() == ETAG_FORALL_E {
            match view_bind(pers, st, h) {
                None => fail_dangling_e(),
                Some((ty, b, m)) => {
                    let mut o: Vec<(EIdx, BinderMeta)> = out;
                    o.push((ty, m));
                    pi_binders(pers, st, fuel - 1, &b, o)
                },
            }
        } else {
            Ok((out, h.dup2()))
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/NativeParts.lean:156-161 structFieldTeleOf
/// Lean twin: `proof/ConRon/Arena/Inductives/NativeParts.lean:143-148 structFieldTeleOf`
/// — field `i`'s own telescope `a⃗ : A⃗` (at the field's frame), off the
/// constructor's type.
pub fn struct_field_tele_of(
    pers: &PersTier,
    st: &mut AState,
    cty: &EIdx,
    n_p: u64,
    n_f: u64,
    i: u64,
) -> Result<Vec<(EIdx, BinderMeta)>, CheckError> {
    match expr_ops::strip_pis(pers, st, n_p + n_f, cty) {
        Err(e) => Err(e),
        Ok(None) => Ok(Vec::new()),
        Ok(Some(q)) => {
            let dom: EIdx = if ((n_p + i) as usize) < q.0.len() {
                q.0[(n_p + i) as usize].0.dup2()
            } else {
                EIdx::of_word(0)
            };
            match pi_binders(pers, st, CORE_WALK_FUEL, &dom, Vec::new()) {
                Err(e) => Err(e),
                Ok(p) => Ok(p.0),
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/NativeParts.lean:163-169 structFieldIdxOf
/// Lean twin: `proof/ConRon/Arena/Inductives/NativeParts.lean:153-159 structFieldIdxOf`
/// — the index expressions of field `i`'s domain `Π a⃗, T p⃗ e⃗`, off the
/// constructor's type; `[]` when the field is not of that shape.
pub fn struct_field_idx_of(
    pers: &PersTier,
    st: &mut AState,
    cty: &EIdx,
    n_p: u64,
    n_f: u64,
    i: u64,
) -> Result<Vec<EIdx>, CheckError> {
    match expr_ops::strip_pis(pers, st, n_p + n_f, cty) {
        Err(e) => Err(e),
        Ok(None) => Ok(Vec::new()),
        Ok(Some(q)) => {
            let dom: EIdx = if ((n_p + i) as usize) < q.0.len() {
                q.0[(n_p + i) as usize].0.dup2()
            } else {
                EIdx::of_word(0)
            };
            match pi_binders(pers, st, CORE_WALK_FUEL, &dom, Vec::new()) {
                Err(e) => Err(e),
                Ok(p) => match expr_ops::get_app_args(pers, st, CORE_WALK_FUEL, &p.1) {
                    Err(e) => Err(e),
                    Ok(args) => Ok(core::drop_eidx(&args, n_p as usize)),
                },
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/NativeParts.lean:171-175 recIdxOf
/// Lean twin: `proof/ConRon/Arena/Inductives/NativeParts.lean:163-165 recIdxOf`
/// — the positions of the recursive fields (finitary or reflexive).
pub fn rec_idx_of(ks: &Vec<RecFieldKind>, i: usize, out: Vec<u64>) -> Vec<u64> {
    if i >= ks.len() {
        out
    } else {
        let hit: bool = rec_field_kind_beq(&ks[i], &RecFieldKind::Recursive)
            || rec_field_kind_beq(&ks[i], &RecFieldKind::Reflexive);
        if hit {
            let mut o: Vec<u64> = out;
            o.push(i as u64);
            rec_idx_of(ks, i + 1, o)
        } else {
            rec_idx_of(ks, i + 1, out)
        }
    }
}

// ---------------------------------------------------------------------------
// The shape record (`NativeParts.lean:167-181` of the twin)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/Inductives/NativeParts.lean:177-192 NativeParts
/// Lean twin: `proof/ConRon/Arena/Inductives/NativeParts.lean:170-175 NativeParts`
/// — the pieces of a recognised direct recursive block: the sum parts with the
/// family's index count, and the per-constructor field kinds.  Lean's
/// `extends` is a `shape` field here.
pub struct NativeParts {
    pub shape: InductiveShape,
    /// per constructor, per field: its kind
    pub kinds: Vec<Vec<RecFieldKind>>,
    /// **the stream's recursor record passed the structural pin**
    pub rec_pinned: bool,
}

/// con-leche: ConLeche/Kernel/Inductives/NativeParts.lean:177-192 NativeParts
/// Lean twin: `proof/ConRon/Arena/Inductives/NativeParts.lean:170-175 NativeParts`
/// — the record copy.
pub fn native_parts_dup(p: &NativeParts) -> NativeParts {
    NativeParts {
        shape: sum_parts::inductive_shape_dup(&p.shape),
        kinds: kindss_copy(&p.kinds, 0, Vec::new()),
        rec_pinned: p.rec_pinned,
    }
}

/// con-leche: ConLeche/Kernel/Inductives/NativeParts.lean:194-199 NativeParts.complete
/// Lean twin: `proof/ConRon/Arena/Inductives/NativeParts.lean:180-181 NativeParts.complete`
/// — **the record completed by the former's stage**: the sum parts the
/// former's run returned with the recogniser's field kinds.
pub fn complete(p0: &NativeParts, p1: InductiveShape) -> NativeParts {
    NativeParts {
        shape: p1,
        kinds: kindss_copy(&p0.kinds, 0, Vec::new()),
        rec_pinned: p0.rec_pinned,
    }
}

/// con-leche: ConLeche/Kernel/Inductives/NativeParts.lean:616-622 NativeParts.withKinds
/// Lean twin: `proof/ConRon/Arena/Inductives/NativeParts.lean:524-526 NativeParts.withKinds`
/// — the record completed with the fields' kinds (con-leche's task #210 Part
/// D).  Takes the record by value and returns it, which is `{ p with … }`.
pub fn with_kinds(p: NativeParts, ks: Vec<Vec<RecFieldKind>>) -> NativeParts {
    let mut p2: NativeParts = p;
    p2.kinds = ks;
    p2
}

// ---------------------------------------------------------------------------
// The generated recursor with inductive hypotheses
// (`NativeParts.lean:183-380` of the twin)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/Inductives/NativeParts.lean:230-235 structRecPrefixAt
/// Lean twin: `proof/ConRon/Arena/Inductives/NativeParts.lean:188-192 structRecPrefixAt`
/// — the parameter, motive and minor variables as seen from under the `nF`
/// fields (and `e` further binders): the recursor's leading spine
/// `p⃗ motive m⃗`.
pub fn struct_rec_prefix_at(
    pers: &PersTier,
    st: &mut AState,
    n_p: u64,
    n: u64,
    n_f: u64,
    e: u64,
) -> Result<Vec<EIdx>, CheckError> {
    match struct_parts::struct_ps_at(pers, st, e + n_f + n + 1, n_p) {
        Err(er) => Err(er),
        Ok(ps) => match intern_e_bvar(pers, st, e + n_f + n) {
            Err(er) => Err(er),
            Ok(motive) => match struct_parts::struct_ps_at(pers, st, e + n_f, n) {
                Err(er) => Err(er),
                Ok(minors) => {
                    let mid: Vec<EIdx> = core::snoc_eidx(ps, &motive);
                    Ok(core::append_eidx(mid, &minors))
                }
            },
        },
    }
}

/// con-leche: ConLeche/Kernel/Inductives/NativeParts.lean:237-244 structIdxAt
/// Lean twin: `proof/ConRon/Arena/Inductives/NativeParts.lean:197-199 structIdxAt`
/// — an expression of recursive field `i`'s domain sitting under `m` binders
/// of the field's own telescope, spelled at the recursor-rule frame.
#[allow(clippy::too_many_arguments)]
pub fn struct_idx_at(
    pers: &PersTier,
    st: &mut AState,
    n_f: u64,
    o: u64,
    i: u64,
    l: u64,
    m: u64,
    e: &EIdx,
) -> Result<EIdx, CheckError> {
    match expr_ops::lift_loose_bvars_fast(pers, st, CORE_WALK_FUEL, sub_nat(n_f, i) + l, m, e) {
        Err(er) => Err(er),
        Ok(a) => expr_ops::lift_loose_bvars_fast(pers, st, CORE_WALK_FUEL, o, n_f + l + m, &a),
    }
}

/// con-leche: ConLeche/Kernel/Inductives/NativeParts.lean:246-252 structTeleAt
/// Lean twin: `proof/ConRon/Arena/Inductives/NativeParts.lean:203-207 structTeleAt`
/// — field `i`'s own telescope moved as `structIdxAt` moves its expressions,
/// with every binder's datum reset to the elimination datum.
#[allow(clippy::too_many_arguments)]
pub fn struct_tele_at(
    pers: &PersTier,
    st: &mut AState,
    n_f: u64,
    o: u64,
    i: u64,
    l: u64,
    pw: &PropWhen,
    tele: &Vec<(EIdx, BinderMeta)>,
    k: usize,
    out: Vec<(EIdx, BinderMeta)>,
) -> Result<Vec<(EIdx, BinderMeta)>, CheckError> {
    if k >= tele.len() {
        Ok(out)
    } else {
        let b: EIdx = tele[k].0.dup2();
        match struct_idx_at(pers, st, n_f, o, i, l, k as u64, &b) {
            Err(e) => Err(e),
            Ok(a) => {
                let mut o2: Vec<(EIdx, BinderMeta)> = out;
                o2.push((a, expr::binder_meta(prop_when::dup(pw))));
                struct_tele_at(pers, st, n_f, o, i, l, pw, tele, k + 1, o2)
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/NativeParts.lean:254-255 structTeleVars
/// Lean twin: `proof/ConRon/Arena/Inductives/NativeParts.lean:211 structTeleVars`
/// — the variables of an `m`-binder telescope, innermost last.
pub fn struct_tele_vars(pers: &PersTier, st: &mut AState, m: u64) -> Result<Vec<EIdx>, CheckError> {
    struct_parts::bvars_desc(pers, st, m)
}

/// con-leche: ConLeche/Kernel/Inductives/NativeParts.lean:257-260 Expr.mkPisOf
/// Lean twin: `proof/ConRon/Arena/Inductives/NativeParts.lean:215-217 mkPisOf`
/// — `∀ tele, body` over a binder list (outermost first).
pub fn mk_pis_of(
    pers: &PersTier,
    st: &mut AState,
    tele: &Vec<(EIdx, BinderMeta)>,
    k: usize,
    body: &EIdx,
) -> Result<EIdx, CheckError> {
    if k >= tele.len() {
        Ok(body.dup2())
    } else {
        match mk_pis_of(pers, st, tele, k + 1, body) {
            Err(e) => Err(e),
            Ok(rest) => {
                let ty: EIdx = tele[k].0.dup2();
                let mt: BinderMeta = expr::binder_meta_dup(&tele[k].1);
                intern_e_forall_e(pers, st, ty, rest, mt)
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/NativeParts.lean:261-263 Expr.mkLamsOf
/// Lean twin: `proof/ConRon/Arena/Inductives/NativeParts.lean:221-223 mkLamsOf`
/// — `λ tele, body` over a binder list (outermost first).
pub fn mk_lams_of(
    pers: &PersTier,
    st: &mut AState,
    tele: &Vec<(EIdx, BinderMeta)>,
    k: usize,
    body: &EIdx,
) -> Result<EIdx, CheckError> {
    if k >= tele.len() {
        Ok(body.dup2())
    } else {
        match mk_lams_of(pers, st, tele, k + 1, body) {
            Err(e) => Err(e),
            Ok(rest) => {
                let ty: EIdx = tele[k].0.dup2();
                let mt: BinderMeta = expr::binder_meta_dup(&tele[k].1);
                intern_e_lam(pers, st, ty, rest, mt)
            }
        }
    }
}

/// con-leche: none — `idx.mapM fun e => structIdxAt …`
/// Lean twin: `proof/ConRon/Arena/Inductives/NativeParts.lean:233 structIhApp`
/// — the cursor recursion the `mapM` becomes.
#[allow(clippy::too_many_arguments)]
pub fn struct_idx_list(
    pers: &PersTier,
    st: &mut AState,
    n_f: u64,
    o: u64,
    i: u64,
    l: u64,
    m: u64,
    idx: &Vec<EIdx>,
    k: usize,
    out: Vec<EIdx>,
) -> Result<Vec<EIdx>, CheckError> {
    if k >= idx.len() {
        Ok(out)
    } else {
        let e: EIdx = idx[k].dup2();
        match struct_idx_at(pers, st, n_f, o, i, l, m, &e) {
            Err(er) => Err(er),
            Ok(a) => {
                let mut o2: Vec<EIdx> = out;
                o2.push(a);
                struct_idx_list(pers, st, n_f, o, i, l, m, idx, k + 1, o2)
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/NativeParts.lean:265-277 structIhApp
/// Lean twin: `proof/ConRon/Arena/Inductives/NativeParts.lean:228-237 structIhApp`
/// — the inductive hypothesis' value for recursive field `i` with telescope
/// `tele` and index expressions `idx`, spelled under the fields of a rule body.
#[allow(clippy::too_many_arguments)]
pub fn struct_ih_app(
    pers: &PersTier,
    st: &mut AState,
    rec_c: &NIdx,
    rlvls: &LsIdx,
    pw: &PropWhen,
    n_p: u64,
    n: u64,
    n_f: u64,
    i: u64,
    tele: &Vec<(EIdx, BinderMeta)>,
    idx: &Vec<EIdx>,
) -> Result<EIdx, CheckError> {
    let m: u64 = tele.len() as u64;
    match intern_e_const(pers, st, rec_c.dup2(), rlvls.dup2()) {
        Err(e) => Err(e),
        Ok(hd) => match struct_rec_prefix_at(pers, st, n_p, n, n_f, m) {
            Err(e) => Err(e),
            Ok(prefix_spine) => {
                match struct_idx_list(pers, st, n_f, n + 1, i, 0, m, idx, 0, Vec::new()) {
                    Err(e) => Err(e),
                    Ok(idx2) => {
                        match intern_e_bvar(pers, st, sub_nat(sub_nat(n_f, 1), i) + m) {
                            Err(e) => Err(e),
                            Ok(fvar) => match struct_tele_vars(pers, st, m) {
                                Err(e) => Err(e),
                                Ok(tvars) => match expr_ops::mk_app_n(pers, st, &fvar, &tvars) {
                                    Err(e) => Err(e),
                                    Ok(fapp) => {
                                        let args: Vec<EIdx> = core::snoc_eidx(
                                            core::append_eidx(prefix_spine, &idx2),
                                            &fapp,
                                        );
                                        match expr_ops::mk_app_n(pers, st, &hd, &args) {
                                            Err(e) => Err(e),
                                            Ok(body) => match struct_tele_at(
                                                pers,
                                                st,
                                                n_f,
                                                n + 1,
                                                i,
                                                0,
                                                pw,
                                                tele,
                                                0,
                                                Vec::new(),
                                            ) {
                                                Err(e) => Err(e),
                                                Ok(tl) => mk_lams_of(pers, st, &tl, 0, &body),
                                            },
                                        }
                                    }
                                },
                            },
                        }
                    }
                }
            }
        },
    }
}

/// con-leche: ConLeche/Kernel/Inductives/NativeParts.lean:279-288 structRuleBodyR
/// Lean twin: `proof/ConRon/Arena/Inductives/NativeParts.lean:243-250 structRuleBodyR`
/// — the right-hand side body of rule `j` at a recursive block: minor `j` at
/// the fields, then at the inductive hypotheses of the recursive fields.
/// `cty` and the counts replace con-leche's two function arguments.
#[allow(clippy::too_many_arguments)]
pub fn struct_rule_body_r(
    pers: &PersTier,
    st: &mut AState,
    rec_c: &NIdx,
    rlvls: &LsIdx,
    pw: &PropWhen,
    n_p: u64,
    n: u64,
    n_f: u64,
    j: u64,
    rec_idx: &Vec<u64>,
    cty: &EIdx,
) -> Result<EIdx, CheckError> {
    match intern_e_bvar(pers, st, sub_nat(sub_nat(n_f + n, 1), j)) {
        Err(e) => Err(e),
        Ok(hd) => match struct_parts::bvars_desc(pers, st, n_f) {
            Err(e) => Err(e),
            Ok(fs) => match struct_ih_list(
                pers,
                st,
                rec_c,
                rlvls,
                pw,
                n_p,
                n,
                n_f,
                rec_idx,
                cty,
                0,
                Vec::new(),
            ) {
                Err(e) => Err(e),
                Ok(ihs) => {
                    let args: Vec<EIdx> = core::append_eidx(fs, &ihs);
                    expr_ops::mk_app_n(pers, st, &hd, &args)
                }
            },
        },
    }
}

/// con-leche: none — `recIdx.mapM fun i => structIhApp …`
/// Lean twin: `proof/ConRon/Arena/Inductives/NativeParts.lean:247-249 structRuleBodyR`
/// — the cursor recursion the `mapM` becomes; the two readers con-leche passes
/// as `teleOf`/`idxOf` are called here.
#[allow(clippy::too_many_arguments)]
pub fn struct_ih_list(
    pers: &PersTier,
    st: &mut AState,
    rec_c: &NIdx,
    rlvls: &LsIdx,
    pw: &PropWhen,
    n_p: u64,
    n: u64,
    n_f: u64,
    rec_idx: &Vec<u64>,
    cty: &EIdx,
    k: usize,
    out: Vec<EIdx>,
) -> Result<Vec<EIdx>, CheckError> {
    if k >= rec_idx.len() {
        Ok(out)
    } else {
        let i: u64 = rec_idx[k];
        match struct_field_tele_of(pers, st, cty, n_p, n_f, i) {
            Err(e) => Err(e),
            Ok(tele) => match struct_field_idx_of(pers, st, cty, n_p, n_f, i) {
                Err(e) => Err(e),
                Ok(idx) => match struct_ih_app(pers, st, rec_c, rlvls, pw, n_p, n, n_f, i, &tele, &idx) {
                    Err(e) => Err(e),
                    Ok(a) => {
                        let mut o: Vec<EIdx> = out;
                        o.push(a);
                        struct_ih_list(pers, st, rec_c, rlvls, pw, n_p, n, n_f, rec_idx, cty, k + 1, o)
                    }
                },
            },
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/NativeParts.lean:290-305 structIhPis
/// Lean twin: `proof/ConRon/Arena/Inductives/NativeParts.lean:256-270 structIhPis`
/// — the `ih` binders of a minor premise: for each recursive field position,
/// `∀ a⃗, motive e⃗_i(a⃗) (f_i a⃗)` under the `l` earlier `ih` binders.  `cty`
/// and `nP` replace con-leche's two function arguments.
#[allow(clippy::too_many_arguments)]
pub fn struct_ih_pis(
    pers: &PersTier,
    st: &mut AState,
    n_f: u64,
    o: u64,
    n_p: u64,
    pw: &PropWhen,
    cty: &EIdx,
    is: &Vec<u64>,
    k: usize,
    l: u64,
    body: &EIdx,
) -> Result<EIdx, CheckError> {
    if k >= is.len() {
        Ok(body.dup2())
    } else {
        let i: u64 = is[k];
        match struct_field_tele_of(pers, st, cty, n_p, n_f, i) {
            Err(e) => Err(e),
            Ok(tele) => match struct_field_idx_of(pers, st, cty, n_p, n_f, i) {
                Err(e) => Err(e),
                Ok(idx) => {
                    let m: u64 = tele.len() as u64;
                    match intern_e_bvar(pers, st, sub_nat(n_f + o, 1) + l + m) {
                        Err(e) => Err(e),
                        Ok(motive) => {
                            match struct_idx_list(pers, st, n_f, o, i, l, m, &idx, 0, Vec::new()) {
                                Err(e) => Err(e),
                                Ok(idx2) => struct_ih_pis_at(
                                    pers,
                                    st, n_f, o, n_p, pw, cty, is, k, l, body, &tele, &idx2,
                                    &motive, i, m,
                                ),
                            }
                        }
                    }
                }
            },
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/NativeParts.lean:290-305 structIhPis
/// Lean twin: `proof/ConRon/Arena/Inductives/NativeParts.lean:265-270 structIhPis`
/// — one `ih` binder's conclusion and domain, and the recursion under it.
#[allow(clippy::too_many_arguments)]
pub fn struct_ih_pis_at(
    pers: &PersTier,
    st: &mut AState,
    n_f: u64,
    o: u64,
    n_p: u64,
    pw: &PropWhen,
    cty: &EIdx,
    is: &Vec<u64>,
    k: usize,
    l: u64,
    body: &EIdx,
    tele: &Vec<(EIdx, BinderMeta)>,
    idx2: &Vec<EIdx>,
    motive: &EIdx,
    i: u64,
    m: u64,
) -> Result<EIdx, CheckError> {
    match intern_e_bvar(pers, st, sub_nat(sub_nat(n_f, 1), i) + l + m) {
        Err(e) => Err(e),
        Ok(fvar) => match struct_tele_vars(pers, st, m) {
            Err(e) => Err(e),
            Ok(tvars) => match expr_ops::mk_app_n(pers, st, &fvar, &tvars) {
                Err(e) => Err(e),
                Ok(fapp) => {
                    let cargs: Vec<EIdx> = core::snoc_eidx(env::eidx_vec_dup(idx2), &fapp);
                    match expr_ops::mk_app_n(pers, st, motive, &cargs) {
                        Err(e) => Err(e),
                        Ok(concl) => {
                            match struct_tele_at(pers, st, n_f, o, i, l, pw, tele, 0, Vec::new()) {
                                Err(e) => Err(e),
                                Ok(tl) => match mk_pis_of(pers, st, &tl, 0, &concl) {
                                    Err(e) => Err(e),
                                    Ok(dom) => {
                                        match struct_ih_pis(
                                            pers,
                                            st,
                                            n_f,
                                            o,
                                            n_p,
                                            pw,
                                            cty,
                                            is,
                                            k + 1,
                                            l + 1,
                                            body,
                                        ) {
                                            Err(e) => Err(e),
                                            Ok(rest) => {
                                                let bm: BinderMeta =
                                                    expr::binder_meta(prop_when::dup(pw));
                                                intern_e_forall_e(pers, st, dom, rest, bm)
                                            }
                                        }
                                    }
                                },
                            }
                        }
                    }
                }
            },
        },
    }
}

/// con-leche: ConLeche/Kernel/Inductives/NativeParts.lean:307-320 structMinorTyR
/// Lean twin: `proof/ConRon/Arena/Inductives/NativeParts.lean:276-292 structMinorTyR`
/// — a constructor's minor premise at a recursive block: its field telescope
/// lifted under the `o` extras, every binder's datum reset to the elimination
/// datum, then the `ih` binders, ending in `motive e⃗ (C p⃗ f⃗)` lifted above
/// the `ih`s.
#[allow(clippy::too_many_arguments)]
pub fn struct_minor_ty_r(
    pers: &PersTier,
    st: &mut AState,
    c: &NIdx,
    lps: &Vec<NIdx>,
    n_p: u64,
    n_f: u64,
    o: u64,
    pw: &PropWhen,
    cty: &EIdx,
    rec_idx: &Vec<u64>,
) -> Result<Option<EIdx>, CheckError> {
    match expr_ops::strip_pis(pers, st, n_p, cty) {
        Err(e) => Err(e),
        Ok(None) => Ok(None),
        Ok(Some(q)) => match expr_ops::strip_pis(pers, st, n_f, &q.1) {
            Err(e) => Err(e),
            Ok(None) => Ok(None),
            Ok(Some(r)) => {
                struct_minor_ty_at(pers, st, c, lps, n_p, n_f, o, pw, cty, rec_idx, &q.1, &r.1)
            }
        },
    }
}

/// con-leche: ConLeche/Kernel/Inductives/NativeParts.lean:307-320 structMinorTyR
/// Lean twin: `proof/ConRon/Arena/Inductives/NativeParts.lean:284-292 structMinorTyR`
/// — the conclusion, the `ih` binders and the re-datumed field telescope.
#[allow(clippy::too_many_arguments)]
pub fn struct_minor_ty_at(
    pers: &PersTier,
    st: &mut AState,
    c: &NIdx,
    lps: &Vec<NIdx>,
    n_p: u64,
    n_f: u64,
    o: u64,
    pw: &PropWhen,
    cty: &EIdx,
    rec_idx: &Vec<u64>,
    q2: &EIdx,
    r2: &EIdx,
) -> Result<Option<EIdx>, CheckError> {
    match intern_e_bvar(pers, st, sub_nat(n_f + o, 1)) {
        Err(e) => Err(e),
        Ok(motive) => match expr_ops::get_app_args(pers, st, CORE_WALK_FUEL, r2) {
            Err(e) => Err(e),
            Ok(rargs) => {
                let tail: Vec<EIdx> = core::drop_eidx(&rargs, n_p as usize);
                match lift_list(pers, st, o, n_f, &tail, 0, Vec::new()) {
                    Err(e) => Err(e),
                    Ok(idx) => match struct_parts::struct_ctor_spine_at(pers, st, c, lps, o, n_p, n_f) {
                        Err(e) => Err(e),
                        Ok(spine) => {
                            let cargs: Vec<EIdx> = core::snoc_eidx(idx, &spine);
                            match expr_ops::mk_app_n(pers, st, &motive, &cargs) {
                                Err(e) => Err(e),
                                Ok(concl0) => struct_minor_ty_close(
                                    pers,
                                    st, n_f, o, n_p, pw, cty, rec_idx, q2, &concl0,
                                ),
                            }
                        }
                    },
                }
            }
        },
    }
}

/// con-leche: ConLeche/Kernel/Inductives/NativeParts.lean:307-320 structMinorTyR
/// Lean twin: `proof/ConRon/Arena/Inductives/NativeParts.lean:289-292 structMinorTyR`
/// — the conclusion lifted above the `ih`s, the `ih` binders, and the field
/// telescope re-datumed around them.
#[allow(clippy::too_many_arguments)]
pub fn struct_minor_ty_close(
    pers: &PersTier,
    st: &mut AState,
    n_f: u64,
    o: u64,
    n_p: u64,
    pw: &PropWhen,
    cty: &EIdx,
    rec_idx: &Vec<u64>,
    q2: &EIdx,
    concl0: &EIdx,
) -> Result<Option<EIdx>, CheckError> {
    match expr_ops::lift_loose_bvars_fast(pers, st, CORE_WALK_FUEL, rec_idx.len() as u64, 0, concl0) {
        Err(e) => Err(e),
        Ok(concl) => match struct_ih_pis(pers, st, n_f, o, n_p, pw, cty, rec_idx, 0, 0, &concl) {
            Err(e) => Err(e),
            Ok(inner) => match expr_ops::lift_loose_bvars_fast(pers, st, CORE_WALK_FUEL, o, 0, q2) {
                Err(e) => Err(e),
                Ok(lifted) => struct_parts::replace_pis_pw(pers, st, pw, n_f, &lifted, &inner),
            },
        },
    }
}

/// con-leche: none — `(rargs.drop nP).mapM (liftLooseBVarsFast … o nF)`
/// Lean twin: `proof/ConRon/Arena/Inductives/NativeParts.lean:286 structMinorTyR`
/// — the cursor recursion the `mapM` becomes.
pub fn lift_list(
    pers: &PersTier,
    st: &mut AState,
    amount: u64,
    c: u64,
    xs: &Vec<EIdx>,
    i: usize,
    out: Vec<EIdx>,
) -> Result<Vec<EIdx>, CheckError> {
    if i >= xs.len() {
        Ok(out)
    } else {
        let e: EIdx = xs[i].dup2();
        match expr_ops::lift_loose_bvars_fast(pers, st, CORE_WALK_FUEL, amount, c, &e) {
            Err(er) => Err(er),
            Ok(a) => {
                let mut o: Vec<EIdx> = out;
                o.push(a);
                lift_list(pers, st, amount, c, xs, i + 1, o)
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/NativeParts.lean:322-330 structMinorsPisR
/// con-leche: ConLeche/Kernel/Inductives/NativeParts.lean:332-339 structMinorsLamsR
/// Lean twin: `proof/ConRon/Arena/Inductives/NativeParts.lean:306 structMinorsPisR`
/// Lean twin: `proof/ConRon/Arena/Inductives/NativeParts.lean:319 structMinorsLamsR`
/// — the one clause the twin's two functions differ in, as a function of its
/// own: a `Π` binder or a `λ` one.  Inlined as `if is_lam { … } else { … }` it
/// is an `if` whose two arms MOVE the node's three fields, and Aeneas cannot
/// join the contexts (*"Could not match the contexts"*); with the whole node
/// built inside one function the move happens once per branch and the join is
/// on a plain `EIdx`.
pub fn intern_binder(
    pers: &PersTier,
    st: &mut AState,
    is_lam: bool,
    ty: EIdx,
    body: EIdx,
    pw: &PropWhen,
) -> Result<EIdx, CheckError> {
    let bm: BinderMeta = expr::binder_meta(prop_when::dup(pw));
    if is_lam {
        intern_e_lam(pers, st, ty, body, bm)
    } else {
        intern_e_forall_e(pers, st, ty, body, bm)
    }
}

/// con-leche: ConLeche/Kernel/Inductives/NativeParts.lean:322-330 structMinorsPisR
/// Lean twin: `proof/ConRon/Arena/Inductives/NativeParts.lean:297-306 structMinorsPisR`
/// — the minor premises' `∀`-telescope at a recursive block, one per
/// constructor.  `is_lam` selects the `λ` twin (`structMinorsLamsR`), which the
/// twin writes out a second time and which differs only in the node built.
#[allow(clippy::too_many_arguments)]
pub fn struct_minors_pis_r(
    pers: &PersTier,
    st: &mut AState,
    lps: &Vec<NIdx>,
    n_p: u64,
    pw: &PropWhen,
    ctors: &Vec<(NIdx, u64, EIdx, Vec<u64>)>,
    k: usize,
    o: u64,
    body: &EIdx,
    is_lam: bool,
) -> Result<Option<EIdx>, CheckError> {
    if k >= ctors.len() {
        Ok(Some(body.dup2()))
    } else {
        let c: &(NIdx, u64, EIdx, Vec<u64>) = &ctors[k];
        let cn: NIdx = c.0.dup2();
        let n_f: u64 = c.1;
        let cty: EIdx = c.2.dup2();
        let rec_idx: Vec<u64> = u64_vec_dup(&c.3, 0, Vec::new());
        match struct_minor_ty_r(pers, st, &cn, lps, n_p, n_f, o, pw, &cty, &rec_idx) {
            Err(e) => Err(e),
            Ok(None) => Ok(None),
            Ok(Some(mty)) => {
                match struct_minors_pis_r(pers, st, lps, n_p, pw, ctors, k + 1, o + 1, body, is_lam) {
                    Err(e) => Err(e),
                    Ok(None) => Ok(None),
                    Ok(Some(rest)) => match intern_binder(pers, st, is_lam, mty, rest, pw) {
                        Err(e) => Err(e),
                        Ok(r) => Ok(Some(r)),
                    },
                }
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/NativeParts.lean:332-339 structMinorsLamsR
/// Lean twin: `proof/ConRon/Arena/Inductives/NativeParts.lean:310-319 structMinorsLamsR`
/// — the `λ` twin of `structMinorsPisR`; the shared body above at
/// `is_lam = true`.
#[allow(clippy::too_many_arguments)]
pub fn struct_minors_lams_r(
    pers: &PersTier,
    st: &mut AState,
    lps: &Vec<NIdx>,
    n_p: u64,
    pw: &PropWhen,
    ctors: &Vec<(NIdx, u64, EIdx, Vec<u64>)>,
    k: usize,
    o: u64,
    body: &EIdx,
) -> Result<Option<EIdx>, CheckError> {
    struct_minors_pis_r(pers, st, lps, n_p, pw, ctors, k, o, body, true)
}

/// con-leche: none — a `List Nat` copy; Lean shares the list
/// Lean twin: `proof/ConRon/Arena/Inductives/NativeParts.lean:298 structMinorsPisR`.
pub fn u64_vec_dup(xs: &Vec<u64>, i: usize, out: Vec<u64>) -> Vec<u64> {
    if i >= xs.len() {
        out
    } else {
        let mut o: Vec<u64> = out;
        o.push(xs[i]);
        u64_vec_dup(xs, i + 1, o)
    }
}

/// con-leche: ConLeche/Kernel/Inductives/NativeParts.lean:341-362 structRecTyR
/// Lean twin: `proof/ConRon/Arena/Inductives/NativeParts.lean:323-349 structRecTyR`
/// — **the generated recursor type at a recursive block.**
#[allow(clippy::too_many_arguments)]
pub fn struct_rec_ty_r(
    pers: &PersTier,
    st: &mut AState,
    t: &NIdx,
    lps: &Vec<NIdx>,
    elim: &NIdx,
    large: bool,
    n_p: u64,
    n_idx: u64,
    tty: &EIdx,
    ctors: &Vec<(NIdx, u64, EIdx, Vec<u64>)>,
) -> Result<Option<EIdx>, CheckError> {
    match struct_parts::struct_elim_level(pers, st, elim, large) {
        Err(e) => Err(e),
        Ok(l) => match read_level_m(pers, st, &l) {
            Err(e) => Err(e),
            Ok(lv) => {
                let pw: PropWhen = level::zeroness_of(&lv);
                let n: u64 = ctors.len() as u64;
                match expr_ops::strip_pis(pers, st, n_p, tty) {
                    Err(e) => Err(e),
                    Ok(None) => Ok(None),
                    Ok(Some(q)) => {
                        match struct_parts::struct_motive_ty_i(pers, st, t, lps, n_p, n_idx, &l, &q.1) {
                            Err(e) => Err(e),
                            Ok(None) => Ok(None),
                            Ok(Some(motive_ty)) => struct_rec_ty_at(
                                pers,
                                st, t, lps, n_p, n_idx, tty, ctors, &pw, n, &q.1, &motive_ty,
                            ),
                        }
                    }
                }
            }
        },
    }
}

/// con-leche: ConLeche/Kernel/Inductives/NativeParts.lean:341-362 structRecTyR
/// Lean twin: `proof/ConRon/Arena/Inductives/NativeParts.lean:335-349 structRecTyR`
/// — the major premise, the minors and the parameter telescope re-datumed.
#[allow(clippy::too_many_arguments)]
pub fn struct_rec_ty_at(
    pers: &PersTier,
    st: &mut AState,
    t: &NIdx,
    lps: &Vec<NIdx>,
    n_p: u64,
    n_idx: u64,
    tty: &EIdx,
    ctors: &Vec<(NIdx, u64, EIdx, Vec<u64>)>,
    pw: &PropWhen,
    n: u64,
    q2: &EIdx,
    motive_ty: &EIdx,
) -> Result<Option<EIdx>, CheckError> {
    match struct_parts::struct_fam_i(pers, st, t, lps, n_p, n_idx, n + 1, 0) {
        Err(e) => Err(e),
        Ok(fam) => match intern_e_bvar(pers, st, n_idx + n + 1) {
            Err(e) => Err(e),
            Ok(motive_var) => match struct_parts::struct_ps_at(pers, st, 1, n_idx) {
                Err(e) => Err(e),
                Ok(idx_vars) => match intern_e_bvar(pers, st, 0) {
                    Err(e) => Err(e),
                    Ok(b0) => {
                        let cargs: Vec<EIdx> = core::snoc_eidx(idx_vars, &b0);
                        match expr_ops::mk_app_n(pers, st, &motive_var, &cargs) {
                            Err(e) => Err(e),
                            Ok(concl) => {
                                let bm: BinderMeta = expr::binder_meta(prop_when::dup(pw));
                                match intern_e_forall_e(pers, st, fam, concl, bm) {
                                    Err(e) => Err(e),
                                    Ok(major_body) => struct_rec_ty_close(
                                        pers,
                                        st,
                                        lps,
                                        n_p,
                                        n_idx,
                                        tty,
                                        ctors,
                                        pw,
                                        n,
                                        q2,
                                        motive_ty,
                                        &major_body,
                                    ),
                                }
                            }
                        }
                    }
                },
            },
        },
    }
}

/// con-leche: ConLeche/Kernel/Inductives/NativeParts.lean:341-362 structRecTyR
/// Lean twin: `proof/ConRon/Arena/Inductives/NativeParts.lean:341-349 structRecTyR`
/// — the index binders around the major, the minors' telescope, the motive
/// binder and the parameter telescope.
#[allow(clippy::too_many_arguments)]
pub fn struct_rec_ty_close(
    pers: &PersTier,
    st: &mut AState,
    lps: &Vec<NIdx>,
    n_p: u64,
    n_idx: u64,
    tty: &EIdx,
    ctors: &Vec<(NIdx, u64, EIdx, Vec<u64>)>,
    pw: &PropWhen,
    n: u64,
    q2: &EIdx,
    motive_ty: &EIdx,
    major_body: &EIdx,
) -> Result<Option<EIdx>, CheckError> {
    match expr_ops::lift_loose_bvars_fast(pers, st, CORE_WALK_FUEL, n + 1, 0, q2) {
        Err(e) => Err(e),
        Ok(lifted) => match struct_parts::replace_pis_pw(pers, st, pw, n_idx, &lifted, major_body) {
            Err(e) => Err(e),
            Ok(None) => Ok(None),
            Ok(Some(major)) => {
                match struct_minors_pis_r(pers, st, lps, n_p, pw, ctors, 0, 1, &major, false) {
                    Err(e) => Err(e),
                    Ok(None) => Ok(None),
                    Ok(Some(minors)) => {
                        let bm: BinderMeta = expr::binder_meta(prop_when::dup(pw));
                        match intern_e_forall_e(pers, st, motive_ty.dup2(), minors, bm) {
                            Err(e) => Err(e),
                            Ok(body) => struct_parts::replace_pis_pw(pers, st, pw, n_p, tty, &body),
                        }
                    }
                }
            }
        },
    }
}

/// con-leche: ConLeche/Kernel/Inductives/NativeParts.lean:364-386 structRecRhsR
/// Lean twin: `proof/ConRon/Arena/Inductives/NativeParts.lean:353-380 structRecRhsR`
/// — **the generated rule** for constructor `j` at a recursive block.
#[allow(clippy::too_many_arguments)]
pub fn struct_rec_rhs_r(
    pers: &PersTier,
    st: &mut AState,
    t: &NIdx,
    lps: &Vec<NIdx>,
    elim: &NIdx,
    large: bool,
    n_p: u64,
    n_idx: u64,
    tty: &EIdx,
    ctors: &Vec<(NIdx, u64, EIdx, Vec<u64>)>,
    rec_c: &NIdx,
    rlvls: &LsIdx,
    j: u64,
) -> Result<Option<EIdx>, CheckError> {
    match struct_parts::struct_elim_level(pers, st, elim, large) {
        Err(e) => Err(e),
        Ok(l) => match read_level_m(pers, st, &l) {
            Err(e) => Err(e),
            Ok(lv) => {
                let pw: PropWhen = level::zeroness_of(&lv);
                let n: u64 = ctors.len() as u64;
                if (j as usize) >= ctors.len() {
                    Ok(None)
                } else {
                    let n_f: u64 = ctors[j as usize].1;
                    let cty: EIdx = ctors[j as usize].2.dup2();
                    let rec_idx: Vec<u64> = u64_vec_dup(&ctors[j as usize].3, 0, Vec::new());
                    struct_rec_rhs_at(
                        pers,
                        st, t, lps, n_p, n_idx, tty, ctors, rec_c, rlvls, j, &pw, n, n_f, &cty,
                        &rec_idx, &l,
                    )
                }
            }
        },
    }
}

/// con-leche: ConLeche/Kernel/Inductives/NativeParts.lean:364-386 structRecRhsR
/// Lean twin: `proof/ConRon/Arena/Inductives/NativeParts.lean:362-380 structRecRhsR`
/// — the motive's type, the rule's body, the field λs, the minors' λs and the
/// parameter λs.
#[allow(clippy::too_many_arguments)]
pub fn struct_rec_rhs_at(
    pers: &PersTier,
    st: &mut AState,
    t: &NIdx,
    lps: &Vec<NIdx>,
    n_p: u64,
    n_idx: u64,
    tty: &EIdx,
    ctors: &Vec<(NIdx, u64, EIdx, Vec<u64>)>,
    rec_c: &NIdx,
    rlvls: &LsIdx,
    j: u64,
    pw: &PropWhen,
    n: u64,
    n_f: u64,
    cty: &EIdx,
    rec_idx: &Vec<u64>,
    l: &LIdx,
) -> Result<Option<EIdx>, CheckError> {
    match expr_ops::strip_pis(pers, st, n_p, tty) {
        Err(e) => Err(e),
        Ok(None) => Ok(None),
        Ok(Some(tq)) => match struct_parts::struct_motive_ty_i(pers, st, t, lps, n_p, n_idx, l, &tq.1) {
            Err(e) => Err(e),
            Ok(None) => Ok(None),
            Ok(Some(motive_ty)) => match expr_ops::strip_pis(pers, st, n_p, cty) {
                Err(e) => Err(e),
                Ok(None) => Ok(None),
                Ok(Some(cq)) => {
                    match struct_rule_body_r(pers, st, rec_c, rlvls, pw, n_p, n, n_f, j, rec_idx, cty) {
                        Err(e) => Err(e),
                        Ok(body) => struct_rec_rhs_close(
                            pers,
                            st, lps, n_p, tty, ctors, pw, n, n_f, &cq.1, &body, &motive_ty,
                        ),
                    }
                }
            },
        },
    }
}

/// con-leche: ConLeche/Kernel/Inductives/NativeParts.lean:364-386 structRecRhsR
/// Lean twin: `proof/ConRon/Arena/Inductives/NativeParts.lean:371-380 structRecRhsR`
/// — the field λs, the minors' λs, the motive λ and the parameter λs.
#[allow(clippy::too_many_arguments)]
pub fn struct_rec_rhs_close(
    pers: &PersTier,
    st: &mut AState,
    lps: &Vec<NIdx>,
    n_p: u64,
    tty: &EIdx,
    ctors: &Vec<(NIdx, u64, EIdx, Vec<u64>)>,
    pw: &PropWhen,
    n: u64,
    n_f: u64,
    q2: &EIdx,
    body: &EIdx,
    motive_ty: &EIdx,
) -> Result<Option<EIdx>, CheckError> {
    match expr_ops::lift_loose_bvars_fast(pers, st, CORE_WALK_FUEL, n + 1, 0, q2) {
        Err(e) => Err(e),
        Ok(lifted) => match struct_parts::pis_to_lams_pw(pers, st, pw, n_f, &lifted, body) {
            Err(e) => Err(e),
            Ok(None) => Ok(None),
            Ok(Some(inner)) => match struct_minors_lams_r(pers, st, lps, n_p, pw, ctors, 0, 1, &inner) {
                Err(e) => Err(e),
                Ok(None) => Ok(None),
                Ok(Some(minors)) => {
                    let bm: BinderMeta = expr::binder_meta(prop_when::dup(pw));
                    match intern_e_lam(pers, st, motive_ty.dup2(), minors, bm) {
                        Err(e) => Err(e),
                        Ok(lam) => struct_parts::pis_to_lams_pw(pers, st, pw, n_p, tty, &lam),
                    }
                }
            },
        },
    }
}

/// con-leche: ConLeche/Kernel/Inductives/NativeParts.lean:388-392 nativeCtors4
/// Lean twin: `proof/ConRon/Arena/Inductives/NativeParts.lean:385-387 nativeCtors4`
/// — the constructors zipped with their recursive positions, as the generators
/// take them.
pub fn native_ctors4(
    ctors_a: &Vec<(IConstantVal, u64)>,
    kinds: &Vec<Vec<RecFieldKind>>,
    i: usize,
    out: Vec<(NIdx, u64, EIdx, Vec<u64>)>,
) -> Vec<(NIdx, u64, EIdx, Vec<u64>)> {
    if i >= ctors_a.len() || i >= kinds.len() {
        out
    } else {
        let mut o: Vec<(NIdx, u64, EIdx, Vec<u64>)> = out;
        o.push((
            ctors_a[i].0.name.dup2(),
            ctors_a[i].1,
            ctors_a[i].0.ty.dup2(),
            rec_idx_of(&kinds[i], 0, Vec::new()),
        ));
        native_ctors4(ctors_a, kinds, i + 1, o)
    }
}

// ---------------------------------------------------------------------------
// The stream's rules against the generated ones
// (`NativeParts.lean:389-436` of the twin)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/Inductives/NativeParts.lean:394-445 nativeRulePrefixOk
/// Lean twin: `proof/ConRon/Arena/Inductives/NativeParts.lean:394-415 nativeRulePrefixOk`
/// — **the rule's `λ` prefix against the stream's own recursor type**
/// (con-leche's task #271): the rule binds the recursor's parameters, its
/// motive, its minor premises and constructor `j`'s fields, and every one of
/// those binder types appears again in the recursor RECORD's own type.
#[allow(clippy::too_many_arguments)]
pub fn native_rule_prefix_ok(
    pers: &PersTier,
    st: &mut AState,
    rec_ty: &EIdx,
    n_p: u64,
    n: u64,
    j: u64,
    n_f: u64,
    rhs: &EIdx,
) -> Result<bool, CheckError> {
    match expr_ops::strip_lams(pers, st, n_p + 1 + n + n_f, rhs) {
        Err(e) => Err(e),
        Ok(None) => Ok(false),
        Ok(Some(rq)) => match expr_ops::strip_pis(pers, st, n_p + 1 + n, rec_ty) {
            Err(e) => Err(e),
            Ok(None) => Ok(false),
            Ok(Some(tq)) => match binders_reset_beq(pers, st, &rq.0, &tq.0, 0, 0, n_p + 1 + n) {
                Err(e) => Err(e),
                Ok(false) => Ok(false),
                Ok(true) => {
                    if ((n_p + 1 + j) as usize) >= tq.0.len() {
                        Ok(false)
                    } else {
                        let mty: EIdx = tq.0[(n_p + 1 + j) as usize].0.dup2();
                        native_rule_fields_ok(pers, st, n_p, n, j, n_f, &rq.0, &mty)
                    }
                }
            },
        },
    }
}

/// con-leche: ConLeche/Kernel/Inductives/NativeParts.lean:394-445 nativeRulePrefixOk
/// Lean twin: `proof/ConRon/Arena/Inductives/NativeParts.lean:405-413 nativeRulePrefixOk`
/// — the rule's FIELD binders against minor `j`'s own Π-telescope, lifted over
/// the later minors.
#[allow(clippy::too_many_arguments)]
pub fn native_rule_fields_ok(
    pers: &PersTier,
    st: &mut AState,
    n_p: u64,
    n: u64,
    j: u64,
    n_f: u64,
    rbs: &Vec<(EIdx, BinderMeta)>,
    mty: &EIdx,
) -> Result<bool, CheckError> {
    match expr_ops::lift_loose_bvars_fast(pers, st, CORE_WALK_FUEL, sub_nat(n, j), 0, mty) {
        Err(e) => Err(e),
        Ok(lifted) => match expr_ops::strip_pis(pers, st, n_f, &lifted) {
            Err(e) => Err(e),
            Ok(None) => Ok(false),
            Ok(Some(fq)) => binders_reset_beq(pers, st, rbs, &fq.0, n_p + 1 + n, 0, n_f),
        },
    }
}

/// con-leche: ConLeche/Kernel/Inductives/NativeParts.lean:394-445 nativeRulePrefixOk
/// Lean twin: `proof/ConRon/Arena/Inductives/NativeParts.lean:397-401 nativeRulePrefixOk`
/// — the `(List.range n).allM` of the cited clause: two binder lists compared
/// at their `resetMeta` normal forms, which is what makes the comparison blind
/// to the prop-ness data the two sides datum differently.
#[allow(clippy::too_many_arguments)]
pub fn binders_reset_beq(
    pers: &PersTier,
    st: &mut AState,
    bs1: &Vec<(EIdx, BinderMeta)>,
    bs2: &Vec<(EIdx, BinderMeta)>,
    o1: u64,
    o2: u64,
    n: u64,
) -> Result<bool, CheckError> {
    binders_reset_beq_from(pers, st, bs1, bs2, o1, o2, n, 0)
}

/// con-leche: ConLeche/Kernel/Inductives/NativeParts.lean:394-445 nativeRulePrefixOk
/// Lean twin: `proof/ConRon/Arena/Inductives/NativeParts.lean:397-401 nativeRulePrefixOk`
/// — the cursor recursion behind `binders_reset_beq`.
#[allow(clippy::too_many_arguments)]
pub fn binders_reset_beq_from(
    pers: &PersTier,
    st: &mut AState,
    bs1: &Vec<(EIdx, BinderMeta)>,
    bs2: &Vec<(EIdx, BinderMeta)>,
    o1: u64,
    o2: u64,
    n: u64,
    i: u64,
) -> Result<bool, CheckError> {
    if i >= n {
        Ok(true)
    } else {
        let j1: u64 = o1 + i;
        let j2: u64 = o2 + i;
        if j1 >= bs1.len() as u64 || j2 >= bs2.len() as u64 {
            Ok(false)
        } else {
            let a: EIdx = bs1[j1 as usize].0.dup2();
            let b: EIdx = bs2[j2 as usize].0.dup2();
            match expr_ops::reset_meta_fast(pers, st, CORE_WALK_FUEL, &a) {
                Err(e) => Err(e),
                Ok(ra) => match expr_ops::reset_meta_fast(pers, st, CORE_WALK_FUEL, &b) {
                    Err(e) => Err(e),
                    Ok(rb) => {
                        if ra.eq2(&rb) {
                            binders_reset_beq_from(pers, st, bs1, bs2, o1, o2, n, i + 1)
                        } else {
                            Ok(false)
                        }
                    }
                },
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/NativeParts.lean:447-475 nativeRulesOk
/// Lean twin: `proof/ConRon/Arena/Inductives/NativeParts.lean:421-436 nativeRulesOk`
/// — **the stream's rules against the generated ones** (at install): rule `j`
/// fires constructor `j` with its field count, and its body is the canonical
/// right-hand side with the inductive hypotheses, at the parse placeholder's
/// binder data.
#[allow(clippy::too_many_arguments)]
pub fn native_rules_ok(
    pers: &PersTier,
    st: &mut AState,
    rec_c: &NIdx,
    rlvls: &LsIdx,
    pw: &PropWhen,
    n_p: u64,
    n: u64,
    cs: &Vec<(IConstantVal, u64)>,
    kinds: &Vec<Vec<RecFieldKind>>,
    rhss: &Vec<EIdx>,
    rec_ty: &EIdx,
) -> Result<bool, CheckError> {
    if !(rhss.len() as u64 == n && kinds.len() as u64 == n) {
        Ok(false)
    } else {
        native_rules_ok_from(pers, st, rec_c, rlvls, pw, n_p, n, cs, kinds, rhss, rec_ty, 0)
    }
}

/// con-leche: ConLeche/Kernel/Inductives/NativeParts.lean:447-475 nativeRulesOk
/// Lean twin: `proof/ConRon/Arena/Inductives/NativeParts.lean:425-436 nativeRulesOk`
/// — the `(List.range n).allM` of the cited clause, as a counted recursion.
#[allow(clippy::too_many_arguments)]
pub fn native_rules_ok_from(
    pers: &PersTier,
    st: &mut AState,
    rec_c: &NIdx,
    rlvls: &LsIdx,
    pw: &PropWhen,
    n_p: u64,
    n: u64,
    cs: &Vec<(IConstantVal, u64)>,
    kinds: &Vec<Vec<RecFieldKind>>,
    rhss: &Vec<EIdx>,
    rec_ty: &EIdx,
    j: u64,
) -> Result<bool, CheckError> {
    if j >= n {
        Ok(true)
    } else if (j as usize) >= rhss.len() || (j as usize) >= cs.len() || (j as usize) >= kinds.len()
    {
        Ok(false)
    } else {
        let n_f: u64 = cs[j as usize].1;
        if kinds[j as usize].len() as u64 != n_f {
            Ok(false)
        } else {
            let rhs: EIdx = rhss[j as usize].dup2();
            let cty: EIdx = cs[j as usize].0.ty.dup2();
            let rec_idx: Vec<u64> = rec_idx_of(&kinds[j as usize], 0, Vec::new());
            match native_rule_body_ok(pers, st, rec_c, rlvls, pw, n_p, n, n_f, j, &rec_idx, &cty, &rhs) {
                Err(e) => Err(e),
                Ok(false) => Ok(false),
                Ok(true) => match native_rule_prefix_ok(pers, st, rec_ty, n_p, n, j, n_f, &rhs) {
                    Err(e) => Err(e),
                    Ok(false) => Ok(false),
                    Ok(true) => native_rules_ok_from(
                        pers,
                        st,
                        rec_c,
                        rlvls,
                        pw,
                        n_p,
                        n,
                        cs,
                        kinds,
                        rhss,
                        rec_ty,
                        j + 1,
                    ),
                },
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/NativeParts.lean:447-475 nativeRulesOk
/// Lean twin: `proof/ConRon/Arena/Inductives/NativeParts.lean:429-433 nativeRulesOk`
/// — rule `j`'s body under its `λ` prefix is the generated right-hand side's
/// body at the parse placeholder's binder data.
#[allow(clippy::too_many_arguments)]
pub fn native_rule_body_ok(
    pers: &PersTier,
    st: &mut AState,
    rec_c: &NIdx,
    rlvls: &LsIdx,
    pw: &PropWhen,
    n_p: u64,
    n: u64,
    n_f: u64,
    j: u64,
    rec_idx: &Vec<u64>,
    cty: &EIdx,
    rhs: &EIdx,
) -> Result<bool, CheckError> {
    match expr_ops::strip_lams(pers, st, n_p + 1 + n + n_f, rhs) {
        Err(e) => Err(e),
        Ok(None) => Ok(false),
        Ok(Some(q)) => {
            match struct_rule_body_r(pers, st, rec_c, rlvls, pw, n_p, n, n_f, j, rec_idx, cty) {
                Err(e) => Err(e),
                Ok(want) => match expr_ops::reset_meta_fast(pers, st, CORE_WALK_FUEL, &want) {
                    Err(e) => Err(e),
                    Ok(rw) => Ok(q.1.eq2(&rw)),
                },
            }
        }
    }
}

// ---------------------------------------------------------------------------
// Recognition (`NativeParts.lean:438-536` of the twin)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/Inductives/NativeParts.lean:501-523 nativeCounts?
/// Lean twin: `proof/ConRon/Arena/Inductives/NativeParts.lean:443-450 nativeCounts?`
/// — **the block's parameter and index counts** (con-leche's task #228), read
/// as official reads them.
pub fn native_counts(
    pers: &PersTier,
    st: &mut AState,
    n_pd: u64,
    cv_t: &IConstantVal,
    n_ctors: u64,
    m_i: u64,
    r_p: u64,
) -> Result<Option<(u64, u64)>, CheckError> {
    match pi_binders(pers, st, CORE_WALK_FUEL, &cv_t.ty, Vec::new()) {
        Err(e) => Err(e),
        Ok(q) => if q.1.tag() == ETAG_SORT {
            match view_sort(pers, st, &q.1) {
                None => fail_dangling_e(),
                Some(_) => {
                    let n: u64 = q.0.len() as u64;
                    if n_pd <= n {
                        Ok(Some((n_pd, n - n_pd)))
                    } else {
                        Ok(None)
                    }
                },
            }
        } else {
            {
                if r_p < n_ctors + 1 || m_i < r_p {
                    Ok(None)
                } else if sub_nat(r_p, n_ctors + 1) == n_pd {
                    Ok(Some((n_pd, sub_nat(m_i, r_p))))
                } else {
                    Ok(None)
                }
            }
        },
    }
}

/// con-leche: ConLeche/Kernel/Inductives/NativeParts.lean:525-549 nativeRecPinOk
/// Lean twin: `proof/ConRon/Arena/Inductives/NativeParts.lean:456-468 nativeRecPinOk`
/// — **the recursor record's structural pin** (con-leche's task #220): the two
/// argument sums the record claims, one rule per constructor in constructor
/// order, each rule naming its constructor with its field count.  Pure: tags,
/// names and counts only.
pub fn native_rec_pin_ok(p: &InductiveShape, block: &Vec<IConstantInfo>) -> bool {
    if block.len() == 0 {
        false
    } else {
        match &block[0] {
            IConstantInfo::IndInfo(_, _) => {
                let rest: Vec<IConstantInfo> =
                    env::i_constant_infos_dup_from(block, 1, Vec::with_capacity(block.len()));
                match sum_parts::sum_split(&rest) {
                    None => false,
                    Some(q) => {
                        let n: u64 = p.ctors.len() as u64;
                        q.3 == p.n_p + 1 + n
                            && q.2 == p.n_p + 1 + n + p.n_idx
                            && q.4.len() as u64 == n
                            && rules_pin_ok(&q.4, &q.0, n, 0)
                    }
                }
            }
            _ => false,
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/NativeParts.lean:525-549 nativeRecPinOk
/// Lean twin: `proof/ConRon/Arena/Inductives/NativeParts.lean:463-466 nativeRecPinOk`
/// — the `(List.range …).all` of the cited clause: rule `j` names constructor
/// `j` with its field count.
pub fn rules_pin_ok(
    rules: &Vec<IRecRule>,
    cs: &Vec<(IConstantVal, u64, u64)>,
    n: u64,
    j: u64,
) -> bool {
    if j >= n {
        true
    } else if (j as usize) >= rules.len() || (j as usize) >= cs.len() {
        false
    } else if rules[j as usize].ctor.eq2(&cs[j as usize].0.name)
        && rules[j as usize].nfields == cs[j as usize].2
    {
        rules_pin_ok(rules, cs, n, j + 1)
    } else {
        false
    }
}

/// con-leche: ConLeche/Kernel/Inductives/NativeParts.lean:551-560 nativeRecLpsOk
/// Lean twin: `proof/ConRon/Arena/Inductives/NativeParts.lean:472-474 nativeRecLpsOk`
/// — **the recursor record's level-parameter pin** (con-leche's task #220).
pub fn native_rec_lps_ok(p: &InductiveShape) -> bool {
    if p.large {
        let want: Vec<NIdx> = nidx_cons(&p.elim, &p.cv_t.level_params);
        core::nidx_vec_beq(&p.cv_r.level_params, &want)
    } else {
        core::nidx_vec_beq(&p.cv_r.level_params, &p.cv_t.level_params)
    }
}

/// con-leche: none — `n :: ns` over a `Vec<NIdx>`
/// Lean twin: `proof/ConRon/Arena/Inductives/NativeParts.lean:473 nativeRecLpsOk`
/// — a `Vec` has no cons, so the tail is copied; the list is a declaration's
/// level parameters.
pub fn nidx_cons(n: &NIdx, ns: &Vec<NIdx>) -> Vec<NIdx> {
    let mut out: Vec<NIdx> = Vec::new();
    out.push(n.dup2());
    nidx_cons_from(ns, 0, out)
}

/// con-leche: none — `n :: ns` over a `Vec<NIdx>`
/// Lean twin: `proof/ConRon/Arena/Inductives/NativeParts.lean:473 nativeRecLpsOk`
/// — the cursor recursion behind `nidx_cons`.
pub fn nidx_cons_from(ns: &Vec<NIdx>, i: usize, out: Vec<NIdx>) -> Vec<NIdx> {
    if i >= ns.len() {
        out
    } else {
        let mut o: Vec<NIdx> = out;
        o.push(ns[i].dup2());
        nidx_cons_from(ns, i + 1, o)
    }
}

/// con-leche: ConLeche/Kernel/Inductives/NativeParts.lean:562-614 nativeShape?
/// Lean twin: `proof/ConRon/Arena/Inductives/NativeParts.lean:480-520 nativeShape?`
/// — the block's shape at a recursive block: the type former, the constructors
/// and the counts, with the rules' right-hand sides as exported and the
/// recursor's level-parameter shape.
pub fn native_shape(
    pers: &PersTier,
    st: &mut AState,
    n_pd: u64,
    block: &Vec<IConstantInfo>,
) -> Result<Option<InductiveShape>, CheckError> {
    if block.len() == 0 {
        Ok(None)
    } else {
        let head: Option<IConstantVal> = match &block[0] {
            IConstantInfo::IndInfo(cv_t, _) => Some(env::i_constant_val_dup(cv_t)),
            _ => None,
        };
        match head {
            None => Ok(None),
            Some(cv_t) => {
                let rest: Vec<IConstantInfo> =
                    env::i_constant_infos_dup_from(block, 1, Vec::with_capacity(block.len()));
                match sum_parts::sum_split(&rest) {
                    None => Ok(None),
                    Some(q) => native_shape_at(pers, st, n_pd, &cv_t, &q.0, &q.1, q.2, q.3, &q.4),
                }
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/NativeParts.lean:562-614 nativeShape?
/// Lean twin: `proof/ConRon/Arena/Inductives/NativeParts.lean:486-518 nativeShape?`
/// — the counts, the reserved-name pins on every member, the result sort and
/// the eliminator.
#[allow(clippy::too_many_arguments)]
pub fn native_shape_at(
    pers: &PersTier,
    st: &mut AState,
    n_pd: u64,
    cv_t: &IConstantVal,
    cs: &Vec<(IConstantVal, u64, u64)>,
    cv_r: &IConstantVal,
    m_i: u64,
    r_p: u64,
    rules: &Vec<IRecRule>,
) -> Result<Option<InductiveShape>, CheckError> {
    match native_counts(pers, st, n_pd, cv_t, cs.len() as u64, m_i, r_p) {
        Err(e) => Err(e),
        Ok(None) => Ok(None),
        Ok(Some(counts)) => match core::reserved_basis_names(st) {
            Err(e) => Err(e),
            Ok(reserved) => {
                if env::nidx_vec_contains(&reserved, &cv_t.name)
                    || env::nidx_vec_contains(&reserved, &cv_r.name)
                    || !ctors_pin_ok(&reserved, cs, counts.0, &cv_t.level_params, 0)
                {
                    Ok(None)
                } else {
                    native_shape_sort(pers, st, cv_t, cs, cv_r, rules, counts.0, counts.1)
                }
            }
        },
    }
}

/// con-leche: ConLeche/Kernel/Inductives/NativeParts.lean:562-614 nativeShape?
/// Lean twin: `proof/ConRon/Arena/Inductives/NativeParts.lean:494-495 nativeShape?`
/// — every constructor declares `nP` parameters at the block's own level
/// parameters and is not a reserved basis name.
pub fn ctors_pin_ok(
    reserved: &Vec<NIdx>,
    cs: &Vec<(IConstantVal, u64, u64)>,
    n_p: u64,
    lps: &Vec<NIdx>,
    i: usize,
) -> bool {
    if i >= cs.len() {
        true
    } else if cs[i].1 == n_p
        && core::nidx_vec_beq(&cs[i].0.level_params, lps)
        && !env::nidx_vec_contains(reserved, &cs[i].0.name)
    {
        ctors_pin_ok(reserved, cs, n_p, lps, i + 1)
    } else {
        false
    }
}

/// con-leche: ConLeche/Kernel/Inductives/NativeParts.lean:562-614 nativeShape?
/// Lean twin: `proof/ConRon/Arena/Inductives/NativeParts.lean:496-518 nativeShape?`
/// — the result sort read off the declared type when it is a syntactic
/// telescope ending in a sort, otherwise a PLACEHOLDER the install's whnf loop
/// replaces (con-leche's task #195), and then WHICH eliminator the block's
/// recursor is (task #220).
#[allow(clippy::too_many_arguments)]
pub fn native_shape_sort(
    pers: &PersTier,
    st: &mut AState,
    cv_t: &IConstantVal,
    cs: &Vec<(IConstantVal, u64, u64)>,
    cv_r: &IConstantVal,
    rules: &Vec<IRecRule>,
    n_p: u64,
    n_idx: u64,
) -> Result<Option<InductiveShape>, CheckError> {
    match expr_ops::strip_pis(pers, st, n_p + n_idx, &cv_t.ty) {
        Err(e) => Err(e),
        Ok(Some(q)) => if q.1.tag() == ETAG_SORT {
            match view_sort(pers, st, &q.1) {
                None => fail_dangling_e(),
                Some(s) => native_shape_elim(pers, st, cv_t, cs, cv_r, rules, n_p, n_idx, s),
            }
        } else {
            match core::zero_level(st) {
                Err(e) => Err(e),
                Ok(z) => native_shape_elim(pers, st, cv_t, cs, cv_r, rules, n_p, n_idx, z),
            }
        },
        Ok(None) => match core::zero_level(st) {
            Err(e) => Err(e),
            Ok(z) => native_shape_elim(pers, st, cv_t, cs, cv_r, rules, n_p, n_idx, z),
        },
    }
}

/// con-leche: ConLeche/Kernel/Inductives/NativeParts.lean:562-614 nativeShape?
/// Lean twin: `proof/ConRon/Arena/Inductives/NativeParts.lean:505-518 nativeShape?`
/// — `isProp`, the constructors and right-hand sides, and the eliminator's
/// level-parameter shape.
#[allow(clippy::too_many_arguments)]
pub fn native_shape_elim(
    pers: &PersTier,
    st: &mut AState,
    cv_t: &IConstantVal,
    cs: &Vec<(IConstantVal, u64, u64)>,
    cv_r: &IConstantVal,
    rules: &Vec<IRecRule>,
    n_p: u64,
    n_idx: u64,
    s: LIdx,
) -> Result<Option<InductiveShape>, CheckError> {
    match core::zero_level(st) {
        Err(e) => Err(e),
        Ok(z) => match core::lvl_eq(pers, st, &s, &z) {
            Err(e) => Err(e),
            Ok(eq) => {
                let is_prop: bool = match eq {
                    Some(true) => true,
                    Some(false) => false,
                    None => false,
                };
                let ctors: Vec<(IConstantVal, u64)> = ctors_of(cs, 0, Vec::new());
                let rhss: Vec<EIdx> = rhss_of(rules, 0, Vec::new());
                let large: Option<NIdx> = if cv_r.level_params.len() == 0 {
                    None
                } else {
                    Some(cv_r.level_params[0].dup2())
                };
                match large {
                    Some(elim) => {
                        let relps: Vec<NIdx> = struct_parts::nidx_vec_tail(&cv_r.level_params);
                        if core::nidx_vec_beq(&relps, &cv_t.level_params)
                            && !env::nidx_vec_contains(&cv_t.level_params, &elim)
                        {
                            Ok(Some(InductiveShape {
                                cv_t: env::i_constant_val_dup(cv_t),
                                ctors,
                                n_p,
                                n_idx,
                                cv_r: env::i_constant_val_dup(cv_r),
                                elim,
                                res_sort: s,
                                rhss,
                                large: true,
                                is_prop,
                            }))
                        } else {
                            native_shape_small(pers, st, cv_t, cv_r, n_p, n_idx, s, is_prop, ctors, rhss)
                        }
                    }
                    None => native_shape_small(pers, st, cv_t, cv_r, n_p, n_idx, s, is_prop, ctors, rhss),
                }
            }
        },
    }
}

/// con-leche: ConLeche/Kernel/Inductives/NativeParts.lean:562-614 nativeShape?
/// Lean twin: `proof/ConRon/Arena/Inductives/NativeParts.lean:515-517 nativeShape?`
/// — the small eliminator's branch, at `.anonymous`.
#[allow(clippy::too_many_arguments)]
pub fn native_shape_small(
    pers: &PersTier,
    st: &mut AState,
    cv_t: &IConstantVal,
    cv_r: &IConstantVal,
    n_p: u64,
    n_idx: u64,
    s: LIdx,
    is_prop: bool,
    ctors: Vec<(IConstantVal, u64)>,
    rhss: Vec<EIdx>,
) -> Result<Option<InductiveShape>, CheckError> {
    match crate::arena::monad::intern_n_node(pers, st, crate::arena::store::NNodeView::Anonymous) {
        Err(e) => Err(e),
        Ok(anon) => Ok(Some(InductiveShape {
            cv_t: env::i_constant_val_dup(cv_t),
            ctors,
            n_p,
            n_idx,
            cv_r: env::i_constant_val_dup(cv_r),
            elim: anon,
            res_sort: s,
            rhss,
            large: false,
            is_prop,
        })),
    }
}

/// con-leche: none — `cs.map fun c => (c.1, c.2.2)`
/// Lean twin: `proof/ConRon/Arena/Inductives/NativeParts.lean:507 nativeShape?`.
pub fn ctors_of(
    cs: &Vec<(IConstantVal, u64, u64)>,
    i: usize,
    out: Vec<(IConstantVal, u64)>,
) -> Vec<(IConstantVal, u64)> {
    if i >= cs.len() {
        out
    } else {
        let mut o: Vec<(IConstantVal, u64)> = out;
        o.push((env::i_constant_val_dup(&cs[i].0), cs[i].2));
        ctors_of(cs, i + 1, o)
    }
}

/// con-leche: none — `rules.map (·.rhs)`
/// Lean twin: `proof/ConRon/Arena/Inductives/NativeParts.lean:508 nativeShape?`.
pub fn rhss_of(rules: &Vec<IRecRule>, i: usize, out: Vec<EIdx>) -> Vec<EIdx> {
    if i >= rules.len() {
        out
    } else {
        let mut o: Vec<EIdx> = out;
        o.push(rules[i].rhs.dup2());
        rhss_of(rules, i + 1, o)
    }
}

/// con-leche: ConLeche/Kernel/Inductives/NativeParts.lean:631-652 nativeParts?
/// Lean twin: `proof/ConRon/Arena/Inductives/NativeParts.lean:532-535 nativeParts?`
/// — recognise a direct block — ONE ROUTE (con-leche's task #210): its SHAPE;
/// the fields' kinds are a PLACEHOLDER the install fills after normalising
/// every field domain by official's positivity walk.
pub fn native_parts(
    pers: &PersTier,
    st: &mut AState,
    n_pd: u64,
    block: &Vec<IConstantInfo>,
) -> Result<Option<NativeParts>, CheckError> {
    match native_shape(pers, st, n_pd, block) {
        Err(e) => Err(e),
        Ok(None) => Ok(None),
        Ok(Some(p)) => {
            let pinned: bool = native_rec_pin_ok(&p, block);
            Ok(Some(NativeParts {
                shape: p,
                kinds: Vec::new(),
                rec_pinned: pinned,
            }))
        }
    }
}
