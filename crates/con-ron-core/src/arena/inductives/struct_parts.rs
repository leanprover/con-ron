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
use crate::arena::expr_ops;
use crate::arena::handle::{EIdx, LIdx, LsIdx, NIdx, ETAG_FORALL_E};
use crate::arena::monad::{
    AState, EIdxNat, eidx_nat_key, fail, fail_dangling_e, intern_e_bvar, intern_e_const, intern_e_proj, intern_l_node, intern_ls_node, view, view_bind,
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
// Level lists over handles (`StructParts.lean:51-62` of the twin)
// ---------------------------------------------------------------------------

/// con-leche: none — `lps.map .param`, interned: the universe arguments a block's own constants carry
/// Lean twin: `proof/ConRon/Arena/Inductives/StructParts.lean:54-65 paramLevels`
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
/// Lean twin: `proof/ConRon/Arena/Inductives/StructParts.lean:54-65 paramLevels.go`
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

/// con-leche: ConLeche/Kernel/Inductives/StructParts.lean:50-53 structPsAt
/// Lean twin: `proof/ConRon/Arena/Inductives/StructParts.lean:69-79 structPsAt`
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

/// con-leche: ConLeche/Kernel/Inductives/StructParts.lean:50-53 structPsAt
/// Lean twin: `proof/ConRon/Arena/Inductives/StructParts.lean:79 structPsAt.go`
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

/// con-leche: ConLeche/Kernel/Inductives/StructParts.lean:55-58 structElimLevel
/// Lean twin: `proof/ConRon/Arena/Inductives/StructParts.lean:81-85 structElimLevel`
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

/// con-leche: ConLeche/Kernel/Inductives/StructParts.lean:79-85 structCtorResidOk
/// Lean twin: `proof/ConRon/Arena/Inductives/StructParts.lean:89-100 structCtorResidOk`
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

/// con-leche: ConLeche/Kernel/Inductives/StructParts.lean:87-93 structProjPs
/// Lean twin: `proof/ConRon/Arena/Inductives/StructParts.lean:104-107 structProjPs`
/// — the parameter spine of the generated projection types, spelled at the
/// frame of the final `∀ p⃗ (t : T p⃗), _` telescope: `p_k = bvar (nP - k)`.
pub fn struct_proj_ps(pers: &PersTier, st: &mut AState, n_p: u64) -> Result<Vec<EIdx>, CheckError> {
    struct_ps_at(pers, st, 1, n_p)
}

/// con-leche: ConLeche/Kernel/Inductives/StructParts.lean:95-101 structProjArgP
/// Lean twin: `proof/ConRon/Arena/Inductives/StructParts.lean:109-114 structProjArgP`
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

// ---------------------------------------------------------------------------
// `hasLooseBVar` — one twin for the pure walk, the cutoff and the memo
// (`StructParts.lean:337-397` of the twin)
// ---------------------------------------------------------------------------

/// con-leche: none — extraction rule 5 (DESIGN.md's task #97-P4c): a `HashMap::get` match is its own function
/// Lean twin: `proof/ConRon/Arena/Inductives/StructParts.lean:125-171 hasLooseBVarBGo`
/// — the `memo[(h, i)]?` probe of the `hasLooseBVarB` walk.  Inline, Aeneas
/// reports *"Could not match the contexts"* on the joined arms.
pub fn hlb_probe(memo: &HashMap<EIdxNat, bool>, k: &EIdxNat) -> Option<bool> {
    match memo.get(k) {
        Some(r) => Some(*r),
        None => None,
    }
}

/// con-leche: ConLeche/Kernel/Inductives/StructParts.lean:190-195 Expr.hasLooseBVarBIns
/// Lean twin: `proof/ConRon/Arena/Inductives/StructParts.lean:118-123 hasLooseBVarBIns`
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

/// con-leche: ConLeche/Kernel/Inductives/StructParts.lean:111-124 Expr.hasLooseBVar
/// con-leche: ConLeche/Kernel/Inductives/StructParts.lean:126-145 Expr.hasLooseBVarB
/// con-leche: ConLeche/Kernel/Inductives/StructParts.lean:197-233 Expr.hasLooseBVarBGo
/// Lean twin: `proof/ConRon/Arena/Inductives/StructParts.lean:125-171 hasLooseBVarBGo`
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

/// con-leche: ConLeche/Kernel/Inductives/StructParts.lean:197-233 Expr.hasLooseBVarBGo
/// Lean twin: `proof/ConRon/Arena/Inductives/StructParts.lean:125-171 hasLooseBVarBGo`
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

/// con-leche: ConLeche/Kernel/Inductives/StructParts.lean:379-381 Expr.hasLooseBVarBFast
/// Lean twin: `proof/ConRon/Arena/Inductives/StructParts.lean:173-176 hasLooseBVarBFast`
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

/// con-leche: ConLeche/Kernel/Inductives/StructParts.lean:388-396 structUsedLater
/// Lean twin: `proof/ConRon/Arena/Inductives/StructParts.lean:178-184 structUsedLater`
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

/// con-leche: ConLeche/Kernel/Inductives/StructParts.lean:424-429 structUsedLaterGo
/// Lean twin: `proof/ConRon/Arena/Inductives/StructParts.lean:186-192 structUsedLaterGo`
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

/// con-leche: ConLeche/Kernel/Inductives/StructParts.lean:440-447 structUsedLaterList
/// Lean twin: `proof/ConRon/Arena/Inductives/StructParts.lean:194-203 structUsedLaterList`
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
/// Lean twin: `proof/ConRon/Arena/Inductives/StructParts.lean:205-230 structProjGuards`
/// — the out-of-range fallback the guard fold spells at every read.
pub fn used_get_d(used: &Vec<bool>, j: u64) -> bool {
    if j < used.len() as u64 {
        used[j as usize]
    } else {
        false
    }
}

/// con-leche: none — `sorts.getD j z` over a `Vec<LIdx>`
/// Lean twin: `proof/ConRon/Arena/Inductives/StructParts.lean:205-230 structProjGuards`
/// — the out-of-range fallback (`zeroLevel`) the guard fold spells at every
/// read.
pub fn sort_get_d(sorts: &Vec<LIdx>, j: u64, z: &LIdx) -> LIdx {
    if j < sorts.len() as u64 {
        sorts[j as usize].dup2()
    } else {
        z.dup2()
    }
}

/// con-leche: ConLeche/Kernel/Inductives/StructParts.lean:398-411 structProjGuards
/// con-leche: ConLeche/Kernel/Inductives/StructParts.lean:477-487 structProjGuardsFast
/// Lean twin: `proof/ConRon/Arena/Inductives/StructParts.lean:222 structProjGuards.col`
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

/// con-leche: ConLeche/Kernel/Inductives/StructParts.lean:398-411 structProjGuards
/// con-leche: ConLeche/Kernel/Inductives/StructParts.lean:477-487 structProjGuardsFast
/// Lean twin: `proof/ConRon/Arena/Inductives/StructParts.lean:230 structProjGuards.row`
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

/// con-leche: ConLeche/Kernel/Inductives/StructParts.lean:398-411 structProjGuards
/// con-leche: ConLeche/Kernel/Inductives/StructParts.lean:477-487 structProjGuardsFast
/// Lean twin: `proof/ConRon/Arena/Inductives/StructParts.lean:205-230 structProjGuards`
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

/// con-leche: ConLeche/Kernel/Inductives/StructParts.lean:503-521 structProjBodiesGo
/// Lean twin: `proof/ConRon/Arena/Inductives/StructParts.lean:232-248 structProjBodiesGo`
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

/// con-leche: ConLeche/Kernel/Inductives/StructParts.lean:523-526 structProjBodies
/// Lean twin: `proof/ConRon/Arena/Inductives/StructParts.lean:250-259 structProjBodies`
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
/// Lean twin: `proof/ConRon/Arena/Inductives/StructParts.lean:263-304 mentionsConstGo`
/// — the `memo[h]?` probe of the `mentionsConst` walk.
pub fn mc_probe(memo: &HashMap<EIdx, bool>, k: &EIdx) -> Option<bool> {
    match memo.get(k) {
        Some(r) => Some(*r),
        None => None,
    }
}

/// con-leche: ConLeche/Kernel/Inductives/StructParts.lean:528-537 Expr.mentionsConst
/// con-leche: ConLeche/Kernel/Inductives/StructParts.lean:569-604 Expr.mentionsConstGo
/// Lean twin: `proof/ConRon/Arena/Inductives/StructParts.lean:263-304 mentionsConstGo`
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

/// con-leche: ConLeche/Kernel/Inductives/StructParts.lean:569-604 Expr.mentionsConstGo
/// Lean twin: `proof/ConRon/Arena/Inductives/StructParts.lean:263-304 mentionsConstGo`
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

/// con-leche: ConLeche/Kernel/Inductives/StructParts.lean:677-679 Expr.mentionsConstFast
/// Lean twin: `proof/ConRon/Arena/Inductives/StructParts.lean:306-309 mentionsConst`
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
