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
//! twin* — is why `mentions_const_go` cites several con-leche declarations.
//! (The `hasLooseBVarB` walk and `structUsedLater` moved upstream to
//! `Kernel/CoreDefs.lean`; their port is in `arena::core`.)
//!
//! ## The memos are ARGUMENTS, threaded by value
//!
//! con-leche threads a `Std.HashMap Expr Bool` through `mentionsConstGo`
//! rather than putting it in a state, because the answer depends on data that
//! is fixed for one call (`T`).  The twin does the same at handle keys —
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
//!   `mc_probe` is.

use crate::arena::core::CORE_WALK_FUEL;
use crate::arena::expr_ops;
use crate::arena::handle::{EIdx, LIdx, LsIdx, NIdx, ETAG_FORALL_E};
use crate::arena::monad::{
    AState, fail, fail_dangling_e, intern_e_bvar, intern_e_const, intern_e_proj, intern_l_node, intern_ls_node, view, view_bind,
};
use crate::arena::store::{ENodeView, LNodeView};
use crate::kernel::core_types::{code_points, CheckError};
use crate::ron::hashmap::{Dup, Eq2};
// The arena's tables are the epoch-stamped open-addressed map
// (DESIGN.md's `Task #97-P6-4b`), aliased so that every use site below
// reads as it did.  `ron::hashmap::HashMap` is still what `crates/con-ron`
// uses, and is still the one with proofs.
use crate::ron::hashmap2::HashMap2 as HashMap;
use crate::arena::store::PersTier;

// ---------------------------------------------------------------------------
// The messages of this module's declines
// ---------------------------------------------------------------------------

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `"fuel exhausted: mentionsConst"`, as code points.
pub const M_FUEL_MENTIONS: [u32; 29] = [
    102, 117, 101, 108, 32, 101, 120, 104, 97, 117, 115, 116, 101, 100, 58, 32, 109, 101, 110, 116,
    105, 111, 110, 115, 67, 111, 110, 115, 116,
];

// ---------------------------------------------------------------------------
// Level lists over handles (`StructParts.lean:51-62` of the twin)
// ---------------------------------------------------------------------------

/// con-leche: none — `lps.map .param`, interned: the universe arguments a block's own constants carry
/// Lean twin: `proof/ConRon/Arena/Inductives/StructParts.lean:47-58 paramLevels`
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
/// Lean twin: `proof/ConRon/Arena/Inductives/StructParts.lean:47-58 paramLevels.go`
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

/// con-leche: ConLeche/Kernel/Inductives/StructParts.lean:38-41 structPsAt
/// Lean twin: `proof/ConRon/Arena/Inductives/StructParts.lean:62-72 structPsAt`
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

/// con-leche: ConLeche/Kernel/Inductives/StructParts.lean:38-41 structPsAt
/// Lean twin: `proof/ConRon/Arena/Inductives/StructParts.lean:72 structPsAt.go`
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

/// con-leche: ConLeche/Kernel/Inductives/StructParts.lean:43-46 structElimLevel
/// Lean twin: `proof/ConRon/Arena/Inductives/StructParts.lean:74-78 structElimLevel`
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

// ---------------------------------------------------------------------------
// The generated recursor at an indexed family (`StructParts.lean:159-188`)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/Inductives/StructParts.lean:67-73 structCtorResidOk
/// Lean twin: `proof/ConRon/Arena/Inductives/StructParts.lean:82-93 structCtorResidOk`
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

// ---------------------------------------------------------------------------
// The shape record and its recogniser (`StructParts.lean:190-311` of the twin)
// ---------------------------------------------------------------------------

// ---------------------------------------------------------------------------
// The projection bodies (`StructParts.lean:313-335` of the twin)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/Inductives/StructParts.lean:75-79 structProjPs
/// Lean twin: `proof/ConRon/Arena/Inductives/StructParts.lean:97-100 structProjPs`
/// — the parameter spine of the generated projection types, spelled at the
/// frame of the final `∀ p⃗ (t : T p⃗), _` telescope: `p_k = bvar (nP - k)`.
pub fn struct_proj_ps(pers: &PersTier, st: &mut AState, n_p: u64) -> Result<Vec<EIdx>, CheckError> {
    struct_ps_at(pers, st, 1, n_p)
}

/// con-leche: ConLeche/Kernel/Inductives/StructParts.lean:81-87 structProjArgP
/// Lean twin: `proof/ConRon/Arena/Inductives/StructParts.lean:102-107 structProjArgP`
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

/// con-leche: ConLeche/Kernel/Inductives/StructParts.lean:89-110 structProjBodiesGo
/// con-leche: ConLeche/Cached/CheckerC.lean:28-34 structProjBodiesGoC
/// Lean twin: `proof/ConRon/Arena/Inductives/StructParts.lean structProjBodiesGo`
/// — **the projection bodies of a recognised block**, one walk of the
/// constructor telescope: field `i`'s raw domain is substituted once
/// (`instantiate_lift`) at the values of the binders before it, and the
/// field's own value, the subject's projection `.proj T i (bvar 0)`, is pushed
/// onto the values before the walk continues; the rest of the telescope is
/// never rewritten.  `vs` is in PUSH order (con-leche conses onto the front of
/// its list, innermost first).  Lean conses the bodies on the way out; the
/// port pushes them on the way in.
#[allow(clippy::too_many_arguments)]
pub fn struct_proj_bodies_go(
    pers: &PersTier,
    st: &mut AState,
    t: &NIdx,
    vs: Vec<EIdx>,
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
                Some((fdom, body)) => {
                    match expr_ops::instantiate_lift_fast(pers, st, CORE_WALK_FUEL, &fdom, &vs, 0) {
                        Err(e) => Err(e),
                        Ok(b) => match struct_proj_arg_p(pers, st, t, i) {
                            Err(e) => Err(e),
                            Ok(a) => {
                                let mut vs2: Vec<EIdx> = vs;
                                vs2.push(a);
                                let mut o: Vec<EIdx> = out;
                                o.push(b);
                                struct_proj_bodies_go(pers, st, t, vs2, k - 1, i + 1, &body, o)
                            }
                        },
                    }
                }
            }
        } else {
            Ok(None)
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/StructParts.lean:112-115 structProjBodies
/// con-leche: ConLeche/Cached/CheckerC.lean:36-41 structProjBodiesC
/// Lean twin: `proof/ConRon/Arena/Inductives/StructParts.lean structProjBodies`
/// — the block's projection bodies, as the table stores them: the parameter
/// binders skipped, then the fields' walk at the parameters' values
/// (`structProjPs`, which in push order is con-leche's reversed list itself).
pub fn struct_proj_bodies(
    pers: &PersTier,
    st: &mut AState,
    t: &NIdx,
    n_p: u64,
    n_f: u64,
    cty: &EIdx,
) -> Result<Option<Vec<EIdx>>, CheckError> {
    match expr_ops::strip_pis(pers, st, n_p, cty) {
        Err(e) => Err(e),
        Ok(None) => Ok(None),
        Ok(Some(p)) => match struct_proj_ps(pers, st, n_p) {
            Err(e) => Err(e),
            Ok(ps) => struct_proj_bodies_go(pers, st, t, ps, n_f, 0, &p.1, Vec::new()),
        },
    }
}

// ---------------------------------------------------------------------------
// `mentionsConst` — one twin for the pure walk and the memo
// (`StructParts.lean:480-528` of the twin)
// ---------------------------------------------------------------------------

/// con-leche: none — extraction rule 5 (DESIGN.md's task #97-P4c): a `HashMap::get` match is its own function
/// Lean twin: `proof/ConRon/Arena/Inductives/StructParts.lean:140-181 mentionsConstGo`
/// — the `memo[h]?` probe of the `mentionsConst` walk.
pub fn mc_probe(memo: &HashMap<EIdx, bool>, k: &EIdx) -> Option<bool> {
    match memo.get(k) {
        Some(r) => Some(*r),
        None => None,
    }
}

/// con-leche: ConLeche/Kernel/Inductives/StructParts.lean:124-133 Expr.mentionsConst
/// con-leche: CHANGED since 501589f5 — re-port, re-test, re-prove struct_parts::mentions_const_go_refines, then delete this line
/// con-leche: ConLeche/Kernel/Inductives/StructParts.lean:165-200 Expr.mentionsConstGo
/// con-leche: CHANGED since 501589f5 — re-port, re-test, re-prove struct_parts::mentions_const_go_refines, then delete this line
/// Lean twin: `proof/ConRon/Arena/Inductives/StructParts.lean:140-181 mentionsConstGo`
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

/// con-leche: ConLeche/Kernel/Inductives/StructParts.lean:165-200 Expr.mentionsConstGo
/// con-leche: CHANGED since 501589f5 — re-port, re-test, re-prove struct_parts::mentions_const_node_refines, then delete this line
/// Lean twin: `proof/ConRon/Arena/Inductives/StructParts.lean:140-181 mentionsConstGo`
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
        ENodeView::Lam(ty, body) => match mentions_const_go(pers, st, t, memo, fuel, &ty) {
            Err(e) => Err(e),
            Ok((b1, m)) => match mentions_const_go(pers, st, t, m, fuel, &body) {
                Err(e) => Err(e),
                Ok((b2, m2)) => Ok((b1 || b2, m2)),
            },
        },
        ENodeView::ForallE(ty, body) => match mentions_const_go(pers, st, t, memo, fuel, &ty) {
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

/// con-leche: ConLeche/Kernel/Inductives/StructParts.lean:273-275 Expr.mentionsConstFast
/// con-leche: CHANGED since 501589f5 — re-port, re-test, re-prove struct_parts::mentions_const_refines, then delete this line
/// Lean twin: `proof/ConRon/Arena/Inductives/StructParts.lean:183-186 mentionsConst`
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
