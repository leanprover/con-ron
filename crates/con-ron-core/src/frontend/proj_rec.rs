//! `proof/ConRon/Arena/Frontend/ProjRec.lean` — **projection functions as
//! recursor applications, over handles** (DESIGN.md §8, task #97 P4e part 2).
//!
//! con-leche's `ConLeche/Frontend/ProjRec.lean`, clause for clause, through
//! the Lean twin.  The rewrite is con-leche's own: the elaborator spells a
//! structure's projection function as `fun p⃗ self => .proj T i self`, this
//! checker serves `.proj` only on the class its direct install recognises, and
//! for the others the definition is replaced — before installation,
//! transparently to the checked code — by the equivalent recursor application
//!
//! ```text
//! fun p⃗ (self : T p⃗) =>
//!   T.rec.{ℓ, u⃗} p⃗ motive_1 … motive_m minor_1 … minor_k self
//! ```
//!
//! What changes over handles, and nothing else does:
//!
//! * every structural read of a term is a `view`, so every walk carries
//!   DESIGN.md §8.4's explicit `fuel` (the store's node count bounds every
//!   path through it);
//! * every term the rewrite BUILDS is interned, so [`mk_lams`],
//!   [`inst_pis_open`], [`build_binders`] and [`proj_rec_value`] take the
//!   state by `&mut` where `con_ron_core::frontend::proj_rec`'s are pure;
//! * a name comparison is a handle comparison — sound because `denoteN` is
//!   injective (task #97a's `denoteN_inj`, DESIGN.md §8.3's exactness
//!   obligation) — and a name the rewrite needs to SPEAK (`T.str "rec"`,
//!   `PUnit`, `PUnit.unit`, `Eq`, `T._model.proj_i.iota`) is interned;
//! * the level algorithm (`Level.isEquiv`) runs on a READ-BACK level tree
//!   (DESIGN.md §8.3 lesson 4, "intern the representation, not the
//!   algorithm").
//!
//! ## Three deviations from con-leche, each the twin's and each forced
//!
//! 1. **[`build_binders`] takes a KIND, not a function.**  con-leche passes
//!    `mkMotive` / `mkMinor` as `mk : Expr → Option Expr`.  DESIGN.md §3.4
//!    forbids a closure in code Aeneas must translate, and this one would have
//!    to take the state besides.  The twin passes [`ProjBinderKind`] and a
//!    [`ProjBuild`] record of what the two bodies read, and dispatches by the
//!    tag — *"which is the enum the Rust would need anyway"*, and here it is.
//!    con-leche's two lambdas are [`mk_proj_motive`] and [`mk_proj_minor`].
//!    (`con_ron_core::frontend::proj_rec` uses a one-method trait instead,
//!    which the tree port could afford because its two builders are pure;
//!    over handles they intern, so a trait method would have to take `&mut
//!    AState` and the trait would be a `&mut`-taking generic — §3.4's own
//!    "no generic instantiated with `&mut`".)
//! 2. **The `List.any` / `List.find?` / `filterMap` closures of
//!    `projRecOwners` are explicit recursions** ([`occurs_any_of`],
//!    [`doms_mention_any`], [`ctors_mention_block`], [`find_ctor_rec`],
//!    [`find_rec_rec`], [`proj_rec_candidates`]), which is §3.4's own rule.
//! 3. **[`proj_rec_owners`] evaluates its guards in the cheap order, and the
//!    result is the same value.**  con-leche computes `recursive` and runs
//!    `structPartsCore?` / `nativeParts?` FIRST and the `filterMap` last; both
//!    early branches return `[]`.  So when the candidate list is empty the
//!    whole function is `[]` whatever the guards say, and computing the
//!    candidates first and the guards only when it is non-empty is the same
//!    function.
//!
//! **`occursConstB`, con-leche's budgeted allocation-free descent, has no
//! twin** — the twin's section note is the argument, and it is about the
//! representation: over a DAG the memo is not an optimisation but the thing
//! that makes the walk linear at all (a subterm reached by two parents is
//! visited twice without it), and the budget cannot be the walk's termination
//! measure either, since the budget a sub-call RETURNS is only bounded by the
//! one it was given, not below it.  So the port walks once, memoised, on the
//! explicit DAG fuel, and [`occurs_const_go`] cites all three of con-leche's
//! walks.
//!
//! ## The two block recognisers are CALLED, not twinned again
//!
//! [`proj_rec_owners`] asks `arena::inductives::struct_parts::
//! struct_parts_core` and `arena::inductives::native_parts::native_parts`
//! whether the direct install or the fixpoint route already serves the block.
//! Those are P4d-2's own handle twins of `ConLeche/Kernel/Inductives/
//! {StructParts,NativeParts}.lean`; the Lean side made the same move at task
//! #97f's dedup, and after it **nothing in the frontend crosses to the `Expr`
//! denotation**.
//!
//! ## Shapes the port adds, all of them the campaign's standing rules
//!
//! * `occursConstGo`'s `Std.HashSet EIdx` is a `ron::HashMap<EIdx, bool>`
//!   threaded **by value, moved in and returned** — the twin's
//!   `AM (Bool × Std.HashSet EIdx)` term for term, and
//!   `arena::inductives::struct_parts`' own arrangement for the same shape;
//! * a `HashMap::get` match that produces a value is its own function and is
//!   never inlined (extraction rule 5, task #97-P4c);
//! * every `List` recursion is a cursor recursion with an `_from` companion;
//! * the twin's `findCtorRec` / `findRecRec` return the RECORD; these return
//!   its index, because returning it would copy a `Vec<NIdx>` and an `EIdx`
//!   the caller reads in place.  `con_ron_core::frontend::proj_rec`'s
//!   `find_ctor` / `find_rec` are the same deviation.

use crate::arena::env::nidx_vec_dup;
use crate::arena::expr_ops;
use crate::arena::handle::{EIdx, LIdx, LsIdx, NIdx, ETAG_BVAR, ETAG_CONST, ETAG_FORALL_E, ETAG_LAM, ETAG_PROJ, ETAG_SORT, NTAG_STR};
use crate::arena::inductives::native_parts;
use crate::arena::inductives::struct_parts;
use crate::arena::monad::{
    AState, fail, fail_dangling_e, intern_e_bvar, intern_e_const, intern_e_lam, intern_l_node, intern_ls_node, intern_n_node, intern_name, read_level_m, view, view_bind, view_bvar, view_const, view_const_name, view_ls, view_n, view_proj, view_sort,
};
use crate::arena::store::{ENodeView, LNodeView, NNodeView};
use crate::frontend::types::ProjRecOwner;
use crate::frontend::text;
use crate::kernel::basis_names as bnm;
use crate::kernel::core_types::{code_points, CheckError};
use crate::kernel::expr;
use crate::kernel::expr::BinderMeta;
use crate::kernel::level;
use crate::ron::hashmap::{Dup, Eq2};
// The arena's tables are the epoch-stamped open-addressed map
// (DESIGN.md's `Task #97-P6-4b`), aliased so that every use site below
// reads as it did.  `ron::hashmap::HashMap` is still what `crates/con-ron`
// uses, and is still the one with proofs.
use crate::ron::hashmap2::HashMap2 as HashMap;
use crate::arena::store::PersTier;

// ---------------------------------------------------------------------------
// The shape records `projRecOwners` takes (`ProjRec.lean:498-501` of the twin)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Frontend/ProjRec.lean:332-370 projRecOwners
/// Lean twin: `proof/ConRon/Arena/Frontend/ProjRec.lean:482-517 projRecOwners` —
/// one type former of the parsed block as the census reads it:
/// `(name, levelParams, type, numParams, numIndices, ctors, isRec)`, the
/// export record's own data over handles.  The twin's tuple, spelled as a
/// tuple (`con_ron_core::frontend::proj_rec` names the seven fields instead;
/// here the twin is the original and `t.6` is `·.2.2.2.2.2.2`).
pub type ProjTypeRec = (NIdx, Vec<NIdx>, EIdx, u64, u64, Vec<NIdx>, bool);

/// con-leche: ConLeche/Frontend/ProjRec.lean:332-370 projRecOwners
/// Lean twin: `proof/ConRon/Arena/Frontend/ProjRec.lean:482-517 projRecOwners` —
/// one constructor: `(name, numFields, type)`.
pub type ProjCtorRec = (NIdx, u64, EIdx);

/// con-leche: ConLeche/Frontend/ProjRec.lean:332-370 projRecOwners
/// Lean twin: `proof/ConRon/Arena/Frontend/ProjRec.lean:482-517 projRecOwners` —
/// one recursor: `(name, levelParams, type, numMotives, numMinors)`.
pub type ProjRecRec = (NIdx, Vec<NIdx>, EIdx, u64, u64);

/// con-leche: ConLeche/Frontend/ProjRec.lean:83-104 ProjRecOwner
/// Lean twin: `proof/ConRon/Arena/Frontend/Types.lean:67-83 ProjRecOwner` —
/// the record copy (DESIGN.md §3.4: no `#[derive]`, an explicit `foo_dup` per
/// type).  It lives here and not beside the type because this module is the
/// only producer and `export_c`'s owner table the only consumer.
pub fn proj_rec_owner_dup(o: &ProjRecOwner) -> ProjRecOwner {
    ProjRecOwner {
        t: o.t.dup2(),
        lps: nidx_vec_dup(&o.lps),
        n_p: o.n_p,
        ctor: o.ctor.dup2(),
        n_f: o.n_f,
        rec_name: o.rec_name.dup2(),
        rec_lps: nidx_vec_dup(&o.rec_lps),
        rec_type: o.rec_type.dup2(),
        num_motives: o.num_motives,
        num_minors: o.num_minors,
    }
}

// ---------------------------------------------------------------------------
// The artifact's name and level (`ProjRec.lean:71-110` of the twin)
// ---------------------------------------------------------------------------

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `"_model"`, as code points.
pub const M_MODEL: [u32; 6] = [95, 109, 111, 100, 101, 108];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `"proj_"`, as code points.
pub const M_PROJ: [u32; 5] = [112, 114, 111, 106, 95];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `"iota"`, as code points.
pub const M_IOTA: [u32; 4] = [105, 111, 116, 97];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `"rec"`, as code points.
pub const M_REC: [u32; 3] = [114, 101, 99];

/// con-leche: none — `String.startsWith` on the port's code-point representation
/// Whether the code-point string `s` begins with the literal `lit`.
/// `text::cps_beq` is the whole-string twin;
/// `con_ron_core::frontend::proj_rec::cps_starts_with` is the same function
/// on the tree side.
pub fn cps_starts_with(s: &Vec<u32>, lit: &[u32]) -> bool {
    if s.len() < lit.len() {
        return false;
    }
    let n = lit.len();
    let mut i: usize = 0;
    while i < n {
        if s[i] != lit[i] {
            return false;
        }
        i += 1;
    }
    true
}

/// con-leche: ConLeche/Frontend/ProjRec.lean:106-111 projIotaName
/// Lean twin: `proof/ConRon/Arena/Frontend/ProjRec.lean:73-80 projIotaName` —
/// the name of the model family's constructor-reduction theorem for field `i`
/// of `T`: `T._model.proj_i.iota`.  Building a name means interning it, so the
/// twin is monadic and this takes the state; the cited `s!"proj_{i}"` is
/// `text::cat` of `text::u64_str` (§3.4 has no `format!`).
pub fn proj_iota_name(
    pers: &PersTier,
    st: &mut AState,
    t: &NIdx,
    i: u64,
) -> Result<NIdx, CheckError>  {
    match intern_n_node(pers, st, NNodeView::Str(t.dup2(), code_points(&M_MODEL))) {
        Err(e) => Err(e),
        Ok(a) => {
            let s = text::cat(code_points(&M_PROJ), &text::u64_str(i));
            match intern_n_node(pers, st, NNodeView::Str(a, s)) {
                Err(e) => Err(e),
                Ok(b) => intern_n_node(pers, st, NNodeView::Str(b, code_points(&M_IOTA))),
            }
        }
    }
}

/// con-leche: ConLeche/Frontend/ProjRec.lean:113-118 isProjIotaName
/// Lean twin: `proof/ConRon/Arena/Frontend/ProjRec.lean:82-94 isProjIotaName`
/// — is `n` of the shape `X._model.proj_i.iota`?  The cheap pre-filter for the
/// theorem records; the last component decides before anything is compared.
pub fn is_proj_iota_name(pers: &PersTier, st: &AState, n: &NIdx) -> Result<bool, CheckError> {
    if n.tag() == NTAG_STR {
        match view_n(pers, st, n) {
            Err(e) => Err(e),
            Ok(NNodeView::Str(p1, last)) => {
                if !text::cps_beq(&last, &M_IOTA) {
                    Ok(false)
                } else {
                    is_proj_iota_pre(pers, st, &p1)
                }
            }
            Ok(_) => Ok(false),
        }
    } else {
        Ok(false)
    }
}

/// con-leche: ConLeche/Frontend/ProjRec.lean:113-118 isProjIotaName
/// Lean twin: `proof/ConRon/Arena/Frontend/ProjRec.lean:82-94 isProjIotaName`
/// — the two inner `match ← viewN`es, past the `"iota"` test.  Its own
/// function so that the outer `view_n`'s loan is dead where the next one is
/// taken (extraction rule 5).
pub fn is_proj_iota_pre(pers: &PersTier, st: &AState, p1: &NIdx) -> Result<bool, CheckError> {
    if p1.tag() == NTAG_STR {
        match view_n(pers, st, p1) {
            Err(e) => Err(e),
            Ok(NNodeView::Str(p2, s)) => {
                if p2.tag() == NTAG_STR {
                    match view_n(pers, st, &p2) {
                        Err(e) => Err(e),
                        Ok(NNodeView::Str(_, m)) => {
                            Ok(text::cps_beq(&m, &M_MODEL) && cps_starts_with(&s, &M_PROJ))
                        }
                        Ok(_) => Ok(false),
                    }
                } else {
                    Ok(false)
                }
            }
            Ok(_) => Ok(false),
        }
    } else {
        Ok(false)
    }
}

/// con-leche: ConLeche/Frontend/ProjRec.lean:120-125 projIotaLevel
/// Lean twin: `proof/ConRon/Arena/Frontend/ProjRec.lean:96-110 projIotaLevel`
/// — the `Eq` level of an artifact iota statement `∀ …, @Eq.{ℓ} α a b`: the
/// field's sort.  `None` on any other shape.  The universe argument list is
/// ONE handle (DESIGN.md §8.3's `LsIdx`), so the singleton test is a
/// `view_ls`; `Eq`'s own name is interned, which is why this takes `&mut`.
pub fn proj_iota_level(
    pers: &PersTier,
    st: &mut AState,
    fuel: u64,
    ty: &EIdx,
) -> Result<Option<LIdx>, CheckError> {
    match expr_ops::pi_result(pers, st, fuel, ty) {
        Err(e) => Err(e),
        Ok(r) => match expr_ops::get_app_fn(pers, st, fuel, &r) {
            Err(e) => Err(e),
            Ok(f) => if f.tag() == ETAG_CONST {
                match view_const(pers, st, &f) {
                    None => fail_dangling_e(),
                    Some((n, us)) => proj_iota_level_at(pers, st, &n, &us),
                }
            } else {
                Ok(None)
            },
        },
    }
}

/// con-leche: ConLeche/Frontend/ProjRec.lean:120-125 projIotaLevel
/// Lean twin: `proof/ConRon/Arena/Frontend/ProjRec.lean:96-110 projIotaLevel`
/// — the `.const` arm: a one-element universe list on the constant `Eq`.  Its
/// own function because the `view`'s loan is dead before `Eq` is interned
/// (extraction rule 5).
pub fn proj_iota_level_at(
    pers: &PersTier,
    st: &mut AState,
    n: &NIdx,
    us: &LsIdx,
) -> Result<Option<LIdx>, CheckError> {
    match view_ls(pers, st, us) {
        Err(e) => Err(e),
        Ok(ls) => {
            if ls.len() != 1 {
                Ok(None)
            } else {
                match intern_name(pers, st, &bnm::eq_name()) {
                    Err(e) => Err(e),
                    Ok(eq_h) => {
                        if n.eq2(&eq_h) {
                            Ok(Some(ls[0].dup2()))
                        } else {
                            Ok(None)
                        }
                    }
                }
            }
        }
    }
}

// ---------------------------------------------------------------------------
// `occursConst`, memoised (`ProjRec.lean:112-193` of the twin)
// ---------------------------------------------------------------------------

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `"fuel exhausted: occursConstGo"`, as code points.
pub const M_FUEL_OCCURS: [u32; 29] = [
    102, 117, 101, 108, 32, 101, 120, 104, 97, 117, 115, 116, 101, 100, 58, 32, 111, 99, 99,
    117, 114, 115, 67, 111, 110, 115, 116, 71, 111,
];

/// con-leche: none — probe the visited set (extraction rule 5, task #97-P4c)
/// A `HashMap::get` match that produces a value is its own function; never
/// inlined.  The set holds the subterms already shown NOT to mention the
/// constant, so a hit is `false` and nothing else.
pub fn occurs_seen(seen: &HashMap<EIdx, bool>, h: &EIdx) -> bool {
    match seen.get(h) {
        Some(_) => true,
        None => false,
    }
}

/// con-leche: ConLeche/Frontend/ProjRec.lean:127-136 occursConst
/// con-leche: ConLeche/Frontend/ProjRec.lean:151-178 occursConstB
/// con-leche: ConLeche/Frontend/ProjRec.lean:180-225 occursConstGo
/// Lean twin: `proof/ConRon/Arena/Frontend/ProjRec.lean:134-187 occursConstGo`
/// — the memoised descent: the set holds the subterms already shown NOT to
/// mention `n`.  Only `false` is recorded — a `true` aborts the walk, so no
/// `true` is ever re-queried.  The set is keyed on the handle, which is
/// nanoda's identity hash (DESIGN.md §8.3) and con-leche's `Std.HashSet Expr`
/// with its cached hash; it is threaded **by value**, which is the twin's
/// `AM (Bool × Std.HashSet EIdx)` term for term.
pub fn occurs_const_go(
    pers: &PersTier,
    st: &AState,
    n: &NIdx,
    seen: HashMap<EIdx, bool>,
    fuel: u64,
    h: &EIdx,
) -> Result<(bool, HashMap<EIdx, bool>), CheckError> {
    if fuel == 0 {
        fail(CheckError::Internal(code_points(&M_FUEL_OCCURS)))
    } else {
        match view(pers, st, h) {
            Err(e) => Err(e),
            Ok(ENodeView::Const(m, _)) => Ok((m.eq2(n), seen)),
            Ok(ENodeView::BVar(_)) => Ok((false, seen)),
            Ok(ENodeView::FVar(_, _)) => Ok((false, seen)),
            Ok(ENodeView::Sort(_)) => Ok((false, seen)),
            Ok(ENodeView::Lit(_)) => Ok((false, seen)),
            Ok(v) => {
                if occurs_seen(&seen, h) {
                    Ok((false, seen))
                } else {
                    occurs_const_node(pers, st, n, seen, fuel - 1, h, v)
                }
            }
        }
    }
}

/// con-leche: ConLeche/Frontend/ProjRec.lean:180-225 occursConstGo
/// Lean twin: `proof/ConRon/Arena/Frontend/ProjRec.lean:134-187 occursConstGo`
/// — the compound arms, past the probe: walk the children and record the node
/// when the answer is `false`.  Split off so the `view`'s loans are dead at
/// the memo's join (extraction rule 5).
pub fn occurs_const_node(
    pers: &PersTier,
    st: &AState,
    n: &NIdx,
    seen: HashMap<EIdx, bool>,
    fuel: u64,
    h: &EIdx,
    v: ENodeView,
) -> Result<(bool, HashMap<EIdx, bool>), CheckError> {
    match v {
        ENodeView::App(f, a) => occurs_const_two(pers, st, n, seen, fuel, h, &f, &a),
        ENodeView::Lam(ty, b, _) => occurs_const_two(pers, st, n, seen, fuel, h, &ty, &b),
        ENodeView::ForallE(ty, b, _) => occurs_const_two(pers, st, n, seen, fuel, h, &ty, &b),
        ENodeView::LetE(t, val, b) => match occurs_const_go(pers, st, n, seen, fuel, &t) {
            Err(e) => Err(e),
            Ok((true, m)) => Ok((true, m)),
            Ok((false, m)) => occurs_const_two(pers, st, n, m, fuel, h, &val, &b),
        },
        ENodeView::Proj(_, _, sub) => match occurs_const_go(pers, st, n, seen, fuel, &sub) {
            Err(e) => Err(e),
            Ok((true, m)) => Ok((true, m)),
            Ok((false, m)) => Ok((false, occurs_record(m, h))),
        },
        // unreachable: the five leaf kinds answered before the probe
        _ => Ok((false, seen)),
    }
}

/// con-leche: ConLeche/Frontend/ProjRec.lean:180-225 occursConstGo
/// Lean twin: `proof/ConRon/Arena/Frontend/ProjRec.lean:134-187 occursConstGo`
/// — the two-child arms (`app`, `lam`, `forallE`, and `letE`'s tail), which
/// are one `match` nest in the twin and one function here.
pub fn occurs_const_two(
    pers: &PersTier,
    st: &AState,
    n: &NIdx,
    seen: HashMap<EIdx, bool>,
    fuel: u64,
    h: &EIdx,
    x: &EIdx,
    y: &EIdx,
) -> Result<(bool, HashMap<EIdx, bool>), CheckError> {
    match occurs_const_go(pers, st, n, seen, fuel, x) {
        Err(e) => Err(e),
        Ok((true, m)) => Ok((true, m)),
        Ok((false, m)) => match occurs_const_go(pers, st, n, m, fuel, y) {
            Err(e) => Err(e),
            Ok((true, m2)) => Ok((true, m2)),
            Ok((false, m2)) => Ok((false, occurs_record(m2, h))),
        },
    }
}

/// con-leche: ConLeche/Frontend/ProjRec.lean:180-225 occursConstGo
/// Lean twin: `proof/ConRon/Arena/Frontend/ProjRec.lean:134-187 occursConstGo` —
/// the cited `seen.insert h`, on the owned table.
pub fn occurs_record(seen: HashMap<EIdx, bool>, h: &EIdx) -> HashMap<EIdx, bool> {
    let mut m: HashMap<EIdx, bool> = seen;
    m.insert(h.dup2(), false);
    m
}

/// con-leche: ConLeche/Frontend/ProjRec.lean:227-231 occursConstFast
/// Lean twin: `proof/ConRon/Arena/Frontend/ProjRec.lean:189-193
/// occursConstFast` — the executed `occursConst`: the memoised descent at a
/// fresh set.
pub fn occurs_const_fast(
    pers: &PersTier,
    st: &AState,
    fuel: u64,
    n: &NIdx,
    h: &EIdx,
) -> Result<bool, CheckError> {
    let seen: HashMap<EIdx, bool> = HashMap::new();
    match occurs_const_go(pers, st, n, seen, fuel, h) {
        Err(e) => Err(e),
        Ok(p) => Ok(p.0),
    }
}

// ---------------------------------------------------------------------------
// Telescopes the rewrite builds and takes apart
// (`ProjRec.lean:195-239` of the twin)
// ---------------------------------------------------------------------------

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `"fuel exhausted: lamBody"`, as code points.
pub const M_FUEL_LAM_BODY: [u32; 23] = [
    102, 117, 101, 108, 32, 101, 120, 104, 97, 117, 115, 116, 101, 100, 58, 32, 108, 97, 109,
    66, 111, 100, 121,
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `"fuel exhausted: stripPisAll"`, as code points.
pub const M_FUEL_STRIP_PIS_ALL: [u32; 27] = [
    102, 117, 101, 108, 32, 101, 120, 104, 97, 117, 115, 116, 101, 100, 58, 32, 115, 116, 114,
    105, 112, 80, 105, 115, 65, 108, 108,
];

/// con-leche: ConLeche/Frontend/ProjRec.lean:233-237 lamBody
/// Lean twin: `proof/ConRon/Arena/Frontend/ProjRec.lean:197-205 lamBody` — the
/// body under every leading `λ` (the projection shape's pre-filter: the node
/// under the value's binders).
pub fn lam_body(pers: &PersTier, st: &AState, fuel: u64, h: &EIdx) -> Result<EIdx, CheckError> {
    if fuel == 0 {
        fail(CheckError::Internal(code_points(&M_FUEL_LAM_BODY)))
    } else {
        if h.tag() == ETAG_LAM {
            match view_bind(pers, st, h) {
                None => fail_dangling_e(),
                Some((_, b, _)) => lam_body(pers, st, fuel - 1, &b),
            }
        } else {
            Ok(h.dup2())
        }
    }
}

/// con-leche: ConLeche/Frontend/ProjRec.lean:239-245 stripPisAll
/// Lean twin: `proof/ConRon/Arena/Frontend/ProjRec.lean:207-216 stripPisAll` —
/// strip every leading `∀`: the binder list (outermost first) and the body.
pub fn strip_pis_all(
    pers: &PersTier,
    st: &AState,
    fuel: u64,
    h: &EIdx,
) -> Result<(Vec<(EIdx, BinderMeta)>, EIdx), CheckError> {
    if fuel == 0 {
        fail(CheckError::Internal(code_points(&M_FUEL_STRIP_PIS_ALL)))
    } else {
        if h.tag() == ETAG_FORALL_E {
            match view_bind(pers, st, h) {
                None => fail_dangling_e(),
                Some((ty, b, m)) => match strip_pis_all(pers, st, fuel - 1, &b) {
                    Err(e) => Err(e),
                    Ok(p) => Ok((expr_ops::cons_binder(&ty, &m, &p.0), p.1)),
                },
            }
        } else {
            Ok((Vec::new(), h.dup2()))
        }
    }
}

/// con-leche: ConLeche/Frontend/ProjRec.lean:247-249 mkLams
/// Lean twin: `proof/ConRon/Arena/Frontend/ProjRec.lean:218-225 mkLams` —
/// rebuild a `λ`-telescope over a binder list (outermost first).  Structural
/// on the list, so no fuel; every binder is interned.  The `i = 0` wrapper of
/// the cursor recursion below.
pub fn mk_lams(
    pers: &PersTier,
    st: &mut AState,
    bs: &Vec<(EIdx, BinderMeta)>,
    body: &EIdx,
) -> Result<EIdx, CheckError> {
    mk_lams_from(pers, st, bs, 0, body)
}

/// con-leche: ConLeche/Frontend/ProjRec.lean:247-249 mkLams
/// Lean twin: `proof/ConRon/Arena/Frontend/ProjRec.lean:218-225 mkLams` — the
/// cursor recursion behind `mk_lams`: the twin conses on the way OUT, so the
/// cursor recurses to the end of the list and interns outward from there.
pub fn mk_lams_from(
    pers: &PersTier,
    st: &mut AState,
    bs: &Vec<(EIdx, BinderMeta)>,
    i: usize,
    body: &EIdx,
) -> Result<EIdx, CheckError> {
    if i >= bs.len() {
        Ok(body.dup2())
    } else {
        match mk_lams_from(pers, st, bs, i + 1, body) {
            Err(e) => Err(e),
            Ok(acc) => intern_e_lam(pers, st, bs[i].0.dup2(), acc, expr::binder_meta_dup(&bs[i].1)),
        }
    }
}

/// con-leche: ConLeche/Frontend/ProjRec.lean:251-257 instPisOpen
/// Lean twin: `proof/ConRon/Arena/Frontend/ProjRec.lean:227-239 instPisOpen` —
/// instantiate the leading `∀`-binders at *open* arguments (the body-frame
/// variables and the built motives/minors), one binder per argument, returning
/// the residual telescope.  Structural on the argument list; `fuel` is the one
/// `instantiate1_lift_fast` needs.  The `i = 0` wrapper of the cursor
/// recursion below.
pub fn inst_pis_open(
    pers: &PersTier,
    st: &mut AState,
    fuel: u64,
    e: &EIdx,
    args: &Vec<EIdx>,
) -> Result<Option<EIdx>, CheckError> {
    inst_pis_open_from(pers, st, fuel, e, args, 0)
}

/// con-leche: ConLeche/Frontend/ProjRec.lean:251-257 instPisOpen
/// Lean twin: `proof/ConRon/Arena/Frontend/ProjRec.lean:227-239 instPisOpen` —
/// the cursor recursion behind `inst_pis_open`.
pub fn inst_pis_open_from(
    pers: &PersTier,
    st: &mut AState,
    fuel: u64,
    e: &EIdx,
    args: &Vec<EIdx>,
    i: usize,
) -> Result<Option<EIdx>, CheckError> {
    if i >= args.len() {
        Ok(Some(e.dup2()))
    } else {
        if e.tag() == ETAG_FORALL_E {
            match view_bind(pers, st, e) {
                None => fail_dangling_e(),
                Some((_, body, _)) => {
                    match expr_ops::instantiate1_lift_fast(pers, st, fuel, &body, &args[i], 0) {
                        Err(er) => Err(er),
                        Ok(b) => inst_pis_open_from(pers, st, fuel, &b, args, i + 1),
                    }
                },
            }
        } else {
            Ok(None)
        }
    }
}

// ---------------------------------------------------------------------------
// The two binder bodies, and the peel that uses them
// (`ProjRec.lean:241-330` of the twin)
// ---------------------------------------------------------------------------

/// con-leche: none — which of `projRecValue`'s two `mk` lambdas `buildBinders` runs
/// Lean twin: `proof/ConRon/Arena/Frontend/ProjRec.lean:243-250
/// ProjBinderKind` — con-leche passes the lambda itself; DESIGN.md §3.4
/// forbids a closure in translated code (and this one takes the state
/// besides), so the twin passes the tag the Rust would need anyway, and here
/// it is.
pub enum ProjBinderKind {
    Motive,
    Minor,
}

/// con-leche: none — what `projRecValue`'s two `mk` lambdas capture
/// Lean twin: `proof/ConRon/Arena/Frontend/ProjRec.lean:252-262 ProjBuild` —
/// the owner's type former and constructor, the projection's own codomain `R`,
/// the field index, and the two `PUnit` constants at the elimination level,
/// interned once at the entry rather than rebuilt per binder.
pub struct ProjBuild {
    pub t: NIdx,
    pub ctor: NIdx,
    pub r: EIdx,
    pub i: u64,
    pub punit_c: EIdx,
    pub punit_unit_c: EIdx,
}

/// con-leche: ConLeche/Frontend/ProjRec.lean:271-277 headIs
/// Lean twin: `proof/ConRon/Arena/Frontend/ProjRec.lean:264-270 headIs` — is
/// `T` the head of the owner's own carrier: the motive domain
/// `∀ (t : T p⃗), Sort ℓ` (exactly one binder) or the major-premise domain.
pub fn head_is(
    pers: &PersTier,
    st: &AState,
    fuel: u64,
    t: &NIdx,
    e: &EIdx,
) -> Result<bool, CheckError>  {
    match expr_ops::get_app_fn(pers, st, fuel, e) {
        Err(er) => Err(er),
        Ok(f) => if f.tag() == ETAG_CONST {
            match view_const_name(pers, st, &f) {
                None => fail_dangling_e(),
                Some(n) => Ok(n.eq2(t)),
            }
        } else {
            Ok(false)
        },
    }
}

/// con-leche: ConLeche/Frontend/ProjRec.lean:279-330 projRecValue
/// Lean twin: `proof/ConRon/Arena/Frontend/ProjRec.lean:272-289 mkProjMotive`
/// — the motive body (`mkMotive` inside `projRecValue`): the owner's motive is
/// `fun (t : T p⃗) => R` — `R`'s parameter references skip the new binder, its
/// subject reference IS the new binder — and every other one is the constant
/// `PUnit.{ℓ}` over its telescope.
pub fn mk_proj_motive(
    pers: &PersTier,
    st: &mut AState,
    pb: &ProjBuild,
    fuel: u64,
    dom: &EIdx,
) -> Result<Option<EIdx>, CheckError> {
    match strip_pis_all(pers, st, fuel, dom) {
        Err(e) => Err(e),
        Ok(bse) => if bse.1.tag() == ETAG_SORT {
            match view_sort(pers, st, &bse.1) {
                None => fail_dangling_e(),
                Some(_) => mk_proj_motive_at(pers, st, pb, fuel, &bse.0),
            }
        } else {
            Ok(None)
        },
    }
}

/// con-leche: ConLeche/Frontend/ProjRec.lean:279-330 projRecValue
/// Lean twin: `proof/ConRon/Arena/Frontend/ProjRec.lean:272-289 mkProjMotive`
/// — the cited `match bs with | [(d, m)] => … | bs => …`, past the sort test.
pub fn mk_proj_motive_at(
    pers: &PersTier,
    st: &mut AState,
    pb: &ProjBuild,
    fuel: u64,
    bs: &Vec<(EIdx, BinderMeta)>,
) -> Result<Option<EIdx>, CheckError> {
    if bs.len() != 1 {
        match mk_lams(pers, st, bs, &pb.punit_c) {
            Err(e) => Err(e),
            Ok(r) => Ok(Some(r)),
        }
    } else {
        match head_is(pers, st, fuel, &pb.t, &bs[0].0) {
            Err(e) => Err(e),
            Ok(true) => match expr_ops::lift_loose_bvars_fast(pers, st, fuel, 1, 1, &pb.r) {
                Err(e) => Err(e),
                Ok(rl) => match intern_e_lam(pers, st, bs[0].0.dup2(), rl, expr::binder_meta_dup(&bs[0].1)) {
                    Err(e) => Err(e),
                    Ok(r) => Ok(Some(r)),
                },
            },
            Ok(false) => match intern_e_lam(pers, st, bs[0].0.dup2(), pb.punit_c.dup2(), expr::binder_meta_dup(&bs[0].1)) {
                Err(e) => Err(e),
                Ok(r) => Ok(Some(r)),
            },
        }
    }
}

/// con-leche: ConLeche/Frontend/ProjRec.lean:279-330 projRecValue
/// Lean twin: `proof/ConRon/Arena/Frontend/ProjRec.lean:291-307 mkProjMinor` —
/// the minor body (`mkMinor` inside `projRecValue`): the owner constructor's
/// minor returns field `i` of its telescope (the fields come first, then the
/// inductive hypotheses recursion adds); every other one returns
/// `PUnit.unit.{ℓ}`.  The owner's minor is the one whose codomain applies a
/// motive to the owner constructor.
pub fn mk_proj_minor(
    pers: &PersTier,
    st: &mut AState,
    pb: &ProjBuild,
    fuel: u64,
    dom: &EIdx,
) -> Result<Option<EIdx>, CheckError> {
    match strip_pis_all(pers, st, fuel, dom) {
        Err(e) => Err(e),
        Ok(bse) => match expr_ops::get_app_args(pers, st, fuel, &bse.1) {
            Err(e) => Err(e),
            Ok(args) => {
                if args.len() == 0 {
                    Ok(None)
                } else {
                    mk_proj_minor_at(pers, st, pb, fuel, &bse.0, &args[args.len() - 1])
                }
            }
        },
    }
}

/// con-leche: ConLeche/Frontend/ProjRec.lean:279-330 projRecValue
/// Lean twin: `proof/ConRon/Arena/Frontend/ProjRec.lean:291-307 mkProjMinor` —
/// the cited `if ← headIs fuel pb.ctor major then … else …`, at the spine's
/// last argument.
pub fn mk_proj_minor_at(
    pers: &PersTier,
    st: &mut AState,
    pb: &ProjBuild,
    fuel: u64,
    bs: &Vec<(EIdx, BinderMeta)>,
    major: &EIdx,
) -> Result<Option<EIdx>, CheckError> {
    match head_is(pers, st, fuel, &pb.ctor, major) {
        Err(e) => Err(e),
        Ok(false) => match mk_lams(pers, st, bs, &pb.punit_unit_c) {
            Err(e) => Err(e),
            Ok(r) => Ok(Some(r)),
        },
        Ok(true) => {
            if pb.i >= bs.len() as u64 {
                Ok(None)
            } else {
                match intern_e_bvar(pers, st, bs.len() as u64 - 1 - pb.i) {
                    Err(e) => Err(e),
                    Ok(b) => match mk_lams(pers, st, bs, &b) {
                        Err(e) => Err(e),
                        Ok(r) => Ok(Some(r)),
                    },
                }
            }
        }
    }
}

/// con-leche: ConLeche/Frontend/ProjRec.lean:259-269 buildBinders
/// Lean twin: `proof/ConRon/Arena/Frontend/ProjRec.lean:309-330 buildBinders`
/// — peel `k` binders of a telescope, building one term per binder from its
/// (progressively instantiated) domain, and instantiating the telescope with
/// that term before the next binder is read.  `kind` is con-leche's `mk`
/// argument, as the module note explains.
pub fn build_binders(
    pers: &PersTier,
    st: &mut AState,
    kind: &ProjBinderKind,
    pb: &ProjBuild,
    fuel: u64,
    k: u64,
    h: &EIdx,
) -> Result<Option<(Vec<EIdx>, EIdx)>, CheckError> {
    if k == 0 {
        Ok(Some((Vec::new(), h.dup2())))
    } else {
        if h.tag() == ETAG_FORALL_E {
            match view_bind(pers, st, h) {
                None => fail_dangling_e(),
                Some((dom, body, _)) => {
                    build_binders_at(pers, st, kind, pb, fuel, k, &dom, &body)
                },
            }
        } else {
            Ok(None)
        }
    }
}

/// con-leche: ConLeche/Frontend/ProjRec.lean:259-269 buildBinders
/// Lean twin: `proof/ConRon/Arena/Frontend/ProjRec.lean:309-330 buildBinders`
/// — the `.forallE` arm's `do` block, at the binder's domain and body.  Its
/// own function because the `view`'s loans may not still be alive where the
/// recursion interns (extraction rule 5 / AENEAS_FINDINGS §2.1 F3: an arm ends
/// in a call, never in a branch).
pub fn build_binders_at(
    pers: &PersTier,
    st: &mut AState,
    kind: &ProjBinderKind,
    pb: &ProjBuild,
    fuel: u64,
    k: u64,
    dom: &EIdx,
    body: &EIdx,
) -> Result<Option<(Vec<EIdx>, EIdx)>, CheckError> {
    let t = match kind {
        ProjBinderKind::Motive => mk_proj_motive(pers, st, pb, fuel, dom),
        ProjBinderKind::Minor => mk_proj_minor(pers, st, pb, fuel, dom),
    };
    match t {
        Err(e) => Err(e),
        Ok(None) => Ok(None),
        Ok(Some(t)) => match expr_ops::instantiate1_lift_fast(pers, st, fuel, body, &t, 0) {
            Err(e) => Err(e),
            Ok(body2) => match build_binders(pers, st, kind, pb, fuel, k - 1, &body2) {
                Err(e) => Err(e),
                Ok(None) => Ok(None),
                Ok(Some(tsr)) => Ok(Some((expr_ops::cons_eidx(&t, &tsr.0), tsr.1))),
            },
        },
    }
}

// ---------------------------------------------------------------------------
// The rewrite (`ProjRec.lean:332-400` of the twin)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Frontend/ProjRec.lean:279-330 projRecValue
/// Lean twin: `proof/ConRon/Arena/Frontend/ProjRec.lean:392-400
/// projRecValue.internParamLevels` — `o.lps.map Level.param`, interned: a `List.map` with a
/// closure is §3.4's explicit recursion here.  The `i = 0` wrapper.
pub fn intern_param_levels(
    pers: &PersTier,
    st: &mut AState,
    ns: &Vec<NIdx>,
) -> Result<Vec<LIdx>, CheckError> {
    intern_param_levels_from(pers, st, ns, 0)
}

/// con-leche: ConLeche/Frontend/ProjRec.lean:279-330 projRecValue
/// Lean twin: `proof/ConRon/Arena/Frontend/ProjRec.lean:392-400
/// projRecValue.internParamLevels` — the cursor recursion behind `intern_param_levels`.
pub fn intern_param_levels_from(
    pers: &PersTier,
    st: &mut AState,
    ns: &Vec<NIdx>,
    i: usize,
) -> Result<Vec<LIdx>, CheckError> {
    if i >= ns.len() {
        Ok(Vec::new())
    } else {
        match intern_l_node(pers, st, LNodeView::Param(ns[i].dup2())) {
            Err(e) => Err(e),
            Ok(h) => match intern_param_levels_from(pers, st, ns, i + 1) {
                Err(e) => Err(e),
                Ok(hs) => Ok(cons_lidx(&h, &hs)),
            },
        }
    }
}

/// con-leche: none — Lean's `ℓ :: ups`, a level list built by hand
/// The one-element level list and the cons in front of it (§3.4 has no
/// `vec![…]`: it pulls `MaybeUninit` into the model).
pub fn cons_lidx(l: &LIdx, us: &Vec<LIdx>) -> Vec<LIdx> {
    let mut out: Vec<LIdx> = Vec::with_capacity(us.len() + 1);
    out.push(l.dup2());
    let n = us.len();
    let mut i: usize = 0;
    while i < n {
        out.push(us[i].dup2());
        i += 1;
    }
    out
}

/// con-leche: none — Lean's `xs ++ ys` on the recursor's argument spine
/// Append `xs` to the accumulator (§3.4: accumulators travel by value), as
/// `con_ron_core::frontend::proj_rec::append_exprs` does on the tree side.
pub fn append_eidx(out: Vec<EIdx>, xs: &Vec<EIdx>) -> Vec<EIdx> {
    let mut out = out;
    let n = xs.len();
    let mut i: usize = 0;
    while i < n {
        out.push(xs[i].dup2());
        i += 1;
    }
    out
}

/// con-leche: ConLeche/Frontend/ProjRec.lean:279-330 projRecValue
/// Lean twin: `proof/ConRon/Arena/Frontend/ProjRec.lean:334-400 projRecValue`
/// — **THE REWRITE.**  `ty`/`val` are the definition's declared type and
/// value, `i` the projected field, `l` the field's sort (from the artifact).
/// `None` = the value is not of the projection shape (the caller keeps the
/// declaration unchanged).
///
/// con-leche's `guard (body == .proj o.T i (.bvar 0))` is a `view` of the body
/// here rather than an interned comparand: exactness makes the two the same
/// test (`denoteE_inj`), and destructuring does not put a node in the store
/// when the answer is `false`.
pub fn proj_rec_value(
    pers: &PersTier,
    st: &mut AState,
    fuel: u64,
    o: &ProjRecOwner,
    l: &LIdx,
    ty: &EIdx,
    val: &EIdx,
    i: u64,
) -> Result<Option<EIdx>, CheckError> {
    match expr_ops::strip_lams(pers, st, o.n_p + 1, val) {
        Err(e) => Err(e),
        Ok(None) => Ok(None),
        Ok(Some(lbsb)) => if lbsb.1.tag() == ETAG_PROJ {
            match view_proj(pers, st, &lbsb.1) {
                None => fail_dangling_e(),
                Some((tn, bi, sub)) => if sub.tag() == ETAG_BVAR {
                    match view_bvar(pers, st, &sub) {
                        None => fail_dangling_e(),
                        Some(0) => {
                            if !tn.eq2(&o.t) || bi != i || i >= o.n_f {
                                Ok(None)
                            } else {
                                proj_rec_value_ty(pers, st, fuel, o, l, ty, i, &lbsb.0)
                            }
                        }
                        Some(_) => Ok(None),
                    }
                } else {
                    Ok(None)
                },
            }
        } else {
            Ok(None)
        },
    }
}

/// con-leche: ConLeche/Frontend/ProjRec.lean:279-330 projRecValue
/// Lean twin: `proof/ConRon/Arena/Frontend/ProjRec.lean:334-400 projRecValue`
/// — the cited `match ← stripPis (o.nP + 1) ty with`, past the shape test.
pub fn proj_rec_value_ty(
    pers: &PersTier,
    st: &mut AState,
    fuel: u64,
    o: &ProjRecOwner,
    l: &LIdx,
    ty: &EIdx,
    i: u64,
    lbs: &Vec<(EIdx, BinderMeta)>,
) -> Result<Option<EIdx>, CheckError> {
    match expr_ops::strip_pis(pers, st, o.n_p + 1, ty) {
        Err(e) => Err(e),
        Ok(None) => Ok(None),
        Ok(Some(r)) => proj_rec_value_at(pers, st, fuel, o, l, &r.1, i, lbs),
    }
}

/// con-leche: ConLeche/Frontend/ProjRec.lean:279-330 projRecValue
/// Lean twin: `proof/ConRon/Arena/Frontend/ProjRec.lean:334-400 projRecValue`
/// — the recursor's type at the chosen elimination level, its parameters
/// instantiated at the body frame (`nP + 1` binders: parameter `k` is
/// `bvar (nP - k)`, the subject `bvar 0`), and the two `PUnit` constants the
/// binder bodies read, interned once.
pub fn proj_rec_value_at(
    pers: &PersTier,
    st: &mut AState,
    fuel: u64,
    o: &ProjRecOwner,
    l: &LIdx,
    r: &EIdx,
    i: u64,
    lbs: &Vec<(EIdx, BinderMeta)>,
) -> Result<Option<EIdx>, CheckError> {
    let ups = match intern_param_levels(pers, st, &o.lps) {
        Err(e) => return Err(e),
        Ok(v) => v,
    };
    let us = match intern_ls_node(pers, st, cons_lidx(l, &ups)) {
        Err(e) => return Err(e),
        Ok(v) => v,
    };
    let rty0 = match expr_ops::inst_lp_fast(pers, st, fuel, &o.rec_lps, &us, &o.rec_type) {
        Err(e) => return Err(e),
        Ok(v) => v,
    };
    let params = match expr_ops::bvar_range(pers, st, o.n_p + 1, o.n_p, 0) {
        Err(e) => return Err(e),
        Ok(v) => v,
    };
    match inst_pis_open(pers, st, fuel, &rty0, &params) {
        Err(e) => Err(e),
        Ok(None) => Ok(None),
        Ok(Some(rty1)) => proj_rec_value_binders(pers, st, fuel, o, l, r, i, lbs, &us, &params, &rty1),
    }
}

/// con-leche: ConLeche/Frontend/ProjRec.lean:279-330 projRecValue
/// Lean twin: `proof/ConRon/Arena/Frontend/ProjRec.lean:334-400 projRecValue`
/// — the `ProjBuild` record and the two `buildBinders` runs.
pub fn proj_rec_value_binders(
    pers: &PersTier,
    st: &mut AState,
    fuel: u64,
    o: &ProjRecOwner,
    l: &LIdx,
    r: &EIdx,
    i: u64,
    lbs: &Vec<(EIdx, BinderMeta)>,
    us: &LsIdx,
    params: &Vec<EIdx>,
    rty1: &EIdx,
) -> Result<Option<EIdx>, CheckError> {
    let punit_h = match intern_name(pers, st, &bnm::punit_name()) {
        Err(e) => return Err(e),
        Ok(v) => v,
    };
    let punit_u_h = match intern_name(pers, st, &bnm::punit_unit_name()) {
        Err(e) => return Err(e),
        Ok(v) => v,
    };
    let ls_one = match intern_ls_node(pers, st, one_lidx(l)) {
        Err(e) => return Err(e),
        Ok(v) => v,
    };
    let punit_c = match intern_e_const(pers, st, punit_h, ls_one.dup2()) {
        Err(e) => return Err(e),
        Ok(v) => v,
    };
    let punit_unit_c = match intern_e_const(pers, st, punit_u_h, ls_one) {
        Err(e) => return Err(e),
        Ok(v) => v,
    };
    let pb = ProjBuild {
        t: o.t.dup2(),
        ctor: o.ctor.dup2(),
        r: r.dup2(),
        i,
        punit_c,
        punit_unit_c,
    };
    match build_binders(pers, st, &ProjBinderKind::Motive, &pb, fuel, o.num_motives, rty1) {
        Err(e) => Err(e),
        Ok(None) => Ok(None),
        Ok(Some(mrt)) => {
            match build_binders(pers, st, &ProjBinderKind::Minor, &pb, fuel, o.num_minors, &mrt.1) {
                Err(e) => Err(e),
                Ok(None) => Ok(None),
                Ok(Some(nrt)) => proj_rec_value_major(
                    pers,
                    st, fuel, o, lbs, us, params, &mrt.0, &nrt.0, &nrt.1,
                ),
            }
        }
    }
}

/// con-leche: none — Lean's `[ℓ]`, a one-element level list
/// `vec![…]` is out of the subset (it pulls `MaybeUninit` into the model), so
/// the port builds the singleton by hand.
pub fn one_lidx(l: &LIdx) -> Vec<LIdx> {
    let mut out: Vec<LIdx> = Vec::with_capacity(1);
    out.push(l.dup2());
    out
}

/// con-leche: ConLeche/Frontend/ProjRec.lean:279-330 projRecValue
/// Lean twin: `proof/ConRon/Arena/Frontend/ProjRec.lean:334-400 projRecValue`
/// — the cited final `match ← view rty3 with | .forallE majDom _ _ => …`: the
/// owner has no indices, so the next binder is the subject itself, and the
/// value is `T.rec.{ℓ, u⃗} p⃗ motives minors (bvar 0)` under the definition's
/// own binders.
pub fn proj_rec_value_major(
    pers: &PersTier,
    st: &mut AState,
    fuel: u64,
    o: &ProjRecOwner,
    lbs: &Vec<(EIdx, BinderMeta)>,
    us: &LsIdx,
    params: &Vec<EIdx>,
    motives: &Vec<EIdx>,
    minors: &Vec<EIdx>,
    rty3: &EIdx,
) -> Result<Option<EIdx>, CheckError> {
    if rty3.tag() == ETAG_FORALL_E {
        match view_bind(pers, st, rty3) {
            None => fail_dangling_e(),
            Some((maj_dom, _, _)) => match head_is(pers, st, fuel, &o.t, &maj_dom) {
                Err(e) => Err(e),
                Ok(false) => Ok(None),
                Ok(true) => proj_rec_value_app(pers, st, o, lbs, us, params, motives, minors),
            },
        }
    } else {
        Ok(None)
    }
}

/// con-leche: ConLeche/Frontend/ProjRec.lean:279-330 projRecValue
/// Lean twin: `proof/ConRon/Arena/Frontend/ProjRec.lean:334-400 projRecValue`
/// — the spine itself, past the major-premise test: `mkAppN` of the recursor
/// constant over `params ++ motives ++ minors ++ [bvar 0]`, under `mkLams`.
pub fn proj_rec_value_app(
    pers: &PersTier,
    st: &mut AState,
    o: &ProjRecOwner,
    lbs: &Vec<(EIdx, BinderMeta)>,
    us: &LsIdx,
    params: &Vec<EIdx>,
    motives: &Vec<EIdx>,
    minors: &Vec<EIdx>,
) -> Result<Option<EIdx>, CheckError> {
    let rc = match intern_e_const(pers, st, o.rec_name.dup2(), us.dup2()) {
        Err(e) => return Err(e),
        Ok(v) => v,
    };
    let b0 = match intern_e_bvar(pers, st, 0) {
        Err(e) => return Err(e),
        Ok(v) => v,
    };
    let mut args: Vec<EIdx> = Vec::new();
    args = append_eidx(args, params);
    args = append_eidx(args, motives);
    args = append_eidx(args, minors);
    args.push(b0);
    match expr_ops::mk_app_n(pers, st, &rc, &args) {
        Err(e) => Err(e),
        Ok(app) => match mk_lams(pers, st, lbs, &app) {
            Err(e) => Err(e),
            Ok(r) => Ok(Some(r)),
        },
    }
}

// ---------------------------------------------------------------------------
// Which owners the rewrite serves (`ProjRec.lean:402-517` of the twin)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Frontend/ProjRec.lean:332-370 projRecOwners
/// Lean twin: `proof/ConRon/Arena/Frontend/ProjRec.lean:404-411 occursAnyOf` —
/// does any of `ns` occur in `d`?  con-leche's inner `blockNames.any`, as an
/// explicit recursion (§3.4).  The `i = 0` wrapper.
pub fn occurs_any_of(
    pers: &PersTier,
    st: &AState,
    fuel: u64,
    ns: &Vec<NIdx>,
    d: &EIdx,
) -> Result<bool, CheckError> {
    occurs_any_of_from(pers, st, fuel, ns, d, 0)
}

/// con-leche: ConLeche/Frontend/ProjRec.lean:332-370 projRecOwners
/// Lean twin: `proof/ConRon/Arena/Frontend/ProjRec.lean:404-411 occursAnyOf` —
/// the cursor recursion behind `occurs_any_of`.
pub fn occurs_any_of_from(
    pers: &PersTier,
    st: &AState,
    fuel: u64,
    ns: &Vec<NIdx>,
    d: &EIdx,
    i: usize,
) -> Result<bool, CheckError> {
    if i >= ns.len() {
        Ok(false)
    } else {
        match occurs_const_fast(pers, st, fuel, &ns[i], d) {
            Err(e) => Err(e),
            Ok(true) => Ok(true),
            Ok(false) => occurs_any_of_from(pers, st, fuel, ns, d, i + 1),
        }
    }
}

/// con-leche: ConLeche/Frontend/ProjRec.lean:332-370 projRecOwners
/// Lean twin: `proof/ConRon/Arena/Frontend/ProjRec.lean:413-420 domsMentionAny`
/// — does any of `ns` occur in any binder domain of the list?  con-leche's
/// middle `(stripPisAll cty).1.any`, as an explicit recursion.  The `i = 0`
/// wrapper.
pub fn doms_mention_any(
    pers: &PersTier,
    st: &AState,
    fuel: u64,
    ns: &Vec<NIdx>,
    bs: &Vec<(EIdx, BinderMeta)>,
) -> Result<bool, CheckError> {
    doms_mention_any_from(pers, st, fuel, ns, bs, 0)
}

/// con-leche: ConLeche/Frontend/ProjRec.lean:332-370 projRecOwners
/// Lean twin: `proof/ConRon/Arena/Frontend/ProjRec.lean:413-420 domsMentionAny`
/// — the cursor recursion behind `doms_mention_any`.
pub fn doms_mention_any_from(
    pers: &PersTier,
    st: &AState,
    fuel: u64,
    ns: &Vec<NIdx>,
    bs: &Vec<(EIdx, BinderMeta)>,
    i: usize,
) -> Result<bool, CheckError> {
    if i >= bs.len() {
        Ok(false)
    } else {
        match occurs_any_of(pers, st, fuel, ns, &bs[i].0) {
            Err(e) => Err(e),
            Ok(true) => Ok(true),
            Ok(false) => doms_mention_any_from(pers, st, fuel, ns, bs, i + 1),
        }
    }
}

/// con-leche: ConLeche/Frontend/ProjRec.lean:332-370 projRecOwners
/// Lean twin: `proof/ConRon/Arena/Frontend/ProjRec.lean:422-431
/// ctorsMentionBlock` — a block name in a constructor's binder *domains* (its
/// result names the owner by definition): con-leche's outer `ctors.any`, as an
/// explicit recursion.  The `i = 0` wrapper.
pub fn ctors_mention_block(
    pers: &PersTier,
    st: &AState,
    fuel: u64,
    ns: &Vec<NIdx>,
    ctors: &Vec<ProjCtorRec>,
) -> Result<bool, CheckError> {
    ctors_mention_block_from(pers, st, fuel, ns, ctors, 0)
}

/// con-leche: ConLeche/Frontend/ProjRec.lean:332-370 projRecOwners
/// Lean twin: `proof/ConRon/Arena/Frontend/ProjRec.lean:422-431
/// ctorsMentionBlock` — the cursor recursion behind `ctors_mention_block`.
pub fn ctors_mention_block_from(
    pers: &PersTier,
    st: &AState,
    fuel: u64,
    ns: &Vec<NIdx>,
    ctors: &Vec<ProjCtorRec>,
    i: usize,
) -> Result<bool, CheckError> {
    if i >= ctors.len() {
        Ok(false)
    } else {
        match strip_pis_all(pers, st, fuel, &ctors[i].2) {
            Err(e) => Err(e),
            Ok(p) => match doms_mention_any(pers, st, fuel, ns, &p.0) {
                Err(e) => Err(e),
                Ok(true) => Ok(true),
                Ok(false) => ctors_mention_block_from(pers, st, fuel, ns, ctors, i + 1),
            },
        }
    }
}

/// con-leche: ConLeche/Frontend/ProjRec.lean:332-370 projRecOwners
/// Lean twin: `proof/ConRon/Arena/Frontend/ProjRec.lean:433-437 findCtorRec` —
/// `ctors.find? (·.1 == C)`, as an explicit recursion.  Returns the INDEX (the
/// module note's fourth shape: the record stays in place).
pub fn find_ctor_rec(ctors: &Vec<ProjCtorRec>, c: &NIdx) -> Option<usize> {
    find_ctor_rec_from(ctors, c, 0)
}

/// con-leche: ConLeche/Frontend/ProjRec.lean:332-370 projRecOwners
/// Lean twin: `proof/ConRon/Arena/Frontend/ProjRec.lean:433-437 findCtorRec` —
/// the cursor recursion behind `find_ctor_rec`.
pub fn find_ctor_rec_from(ctors: &Vec<ProjCtorRec>, c: &NIdx, i: usize) -> Option<usize> {
    if i >= ctors.len() {
        None
    } else if ctors[i].0.eq2(c) {
        Some(i)
    } else {
        find_ctor_rec_from(ctors, c, i + 1)
    }
}

/// con-leche: ConLeche/Frontend/ProjRec.lean:332-370 projRecOwners
/// Lean twin: `proof/ConRon/Arena/Frontend/ProjRec.lean:439-445 findRecRec` —
/// `recs.find? (·.1 == T.str "rec")`, as an explicit recursion.  Returns the
/// INDEX.
pub fn find_rec_rec(recs: &Vec<ProjRecRec>, n: &NIdx) -> Option<usize> {
    find_rec_rec_from(recs, n, 0)
}

/// con-leche: ConLeche/Frontend/ProjRec.lean:332-370 projRecOwners
/// Lean twin: `proof/ConRon/Arena/Frontend/ProjRec.lean:439-445 findRecRec` —
/// the cursor recursion behind `find_rec_rec`.
pub fn find_rec_rec_from(recs: &Vec<ProjRecRec>, n: &NIdx, i: usize) -> Option<usize> {
    if i >= recs.len() {
        None
    } else if recs[i].0.eq2(n) {
        Some(i)
    } else {
        find_rec_rec_from(recs, n, i + 1)
    }
}

/// con-leche: ConLeche/Frontend/ProjRec.lean:332-370 projRecOwners
/// Lean twin: `proof/ConRon/Arena/Frontend/ProjRec.lean:447-480
/// projRecCandidates` — the `filterMap` of `projRecOwners`: the officially
/// structure-like members (one constructor, zero indices, non-propositional)
/// whose recursor carries an elimination level parameter.  An explicit
/// recursion, since `filterMap` takes a closure; `Level.isEquiv` runs on the
/// READ-BACK level (DESIGN.md §8.3 lesson 4).  The `i = 0` wrapper.
///
/// **One argument is dropped**: the twin takes a `fuel` its body never reads
/// — every walk inside it is structural (`stripPis` on the parameter count,
/// one `view`, one `readLevel`) — and an unused parameter is a warning here
/// and a dead dictionary argument in the model.  `proj_rec_owners` still takes
/// the fuel, because `ctors_mention_block` needs it.
pub fn proj_rec_candidates(
    pers: &PersTier,
    st: &mut AState,
    ctors: &Vec<ProjCtorRec>,
    recs: &Vec<ProjRecRec>,
    types: &Vec<ProjTypeRec>,
) -> Result<Vec<ProjRecOwner>, CheckError> {
    proj_rec_candidates_from(pers, st, ctors, recs, types, 0)
}

/// con-leche: ConLeche/Frontend/ProjRec.lean:332-370 projRecOwners
/// Lean twin: `proof/ConRon/Arena/Frontend/ProjRec.lean:447-480
/// projRecCandidates` — the cursor recursion behind `proj_rec_candidates`.
/// The twin computes the TAIL first and conses; so does this, so that the
/// order of the interning the candidate test does is the twin's order.
pub fn proj_rec_candidates_from(
    pers: &PersTier,
    st: &mut AState,
    ctors: &Vec<ProjCtorRec>,
    recs: &Vec<ProjRecRec>,
    types: &Vec<ProjTypeRec>,
    i: usize,
) -> Result<Vec<ProjRecOwner>, CheckError> {
    if i >= types.len() {
        Ok(Vec::new())
    } else {
        match proj_rec_candidates_from(pers, st, ctors, recs, types, i + 1) {
            Err(e) => Err(e),
            Ok(tail) => match proj_rec_candidate_at(pers, st, ctors, recs, &types[i]) {
                Err(e) => Err(e),
                Ok(None) => Ok(tail),
                Ok(Some(o)) => {
                    let mut out: Vec<ProjRecOwner> = Vec::with_capacity(tail.len() + 1);
                    out.push(o);
                    let n = tail.len();
                    let mut j: usize = 0;
                    while j < n {
                        out.push(proj_rec_owner_dup(&tail[j]));
                        j += 1;
                    }
                    Ok(out)
                }
            },
        }
    }
}

/// con-leche: ConLeche/Frontend/ProjRec.lean:332-370 projRecOwners
/// Lean twin: `proof/ConRon/Arena/Frontend/ProjRec.lean:447-480
/// projRecCandidates` — the `filterMap`'s body at ONE type record: one
/// constructor, no indices, a syntactic sort under the parameters, not `Prop`.
pub fn proj_rec_candidate_at(
    pers: &PersTier,
    st: &mut AState,
    ctors: &Vec<ProjCtorRec>,
    recs: &Vec<ProjRecRec>,
    t: &ProjTypeRec,
) -> Result<Option<ProjRecOwner>, CheckError> {
    if t.5.len() != 1 || t.4 != 0 {
        return Ok(None);
    }
    let body = match expr_ops::strip_pis(pers, st, t.3, &t.2) {
        Err(e) => return Err(e),
        Ok(None) => return Ok(None),
        Ok(Some(b)) => b.1,
    };
    if body.tag() != ETAG_SORT {
        return Ok(None);
    }
    let s = match view_sort(pers, st, &body) {
        None => return fail_dangling_e(),
        Some(s) => s,
    };
    let s_p = match read_level_m(pers, st, &s) {
        Err(e) => return Err(e),
        Ok(v) => v,
    };
    match level::is_equiv(&s_p, &level::zero()) {
        Some(true) => return Ok(None),
        _ => {}
    }
    proj_rec_candidate_rec(pers, st, ctors, recs, t)
}

/// con-leche: ConLeche/Frontend/ProjRec.lean:332-370 projRecOwners
/// Lean twin: `proof/ConRon/Arena/Frontend/ProjRec.lean:447-480
/// projRecCandidates` — past the sort test: the constructor's record, the
/// recursor `T.rec`, and the elimination level parameter its level list must
/// carry.
pub fn proj_rec_candidate_rec(
    pers: &PersTier,
    st: &mut AState,
    ctors: &Vec<ProjCtorRec>,
    recs: &Vec<ProjRecRec>,
    t: &ProjTypeRec,
) -> Result<Option<ProjRecOwner>, CheckError> {
    let ci = match find_ctor_rec(ctors, &t.5[0]) {
        None => return Ok(None),
        Some(j) => j,
    };
    let rn = match intern_n_node(pers, st, NNodeView::Str(t.0.dup2(), code_points(&M_REC))) {
        Err(e) => return Err(e),
        Ok(v) => v,
    };
    let ri = match find_rec_rec(recs, &rn) {
        None => return Ok(None),
        Some(j) => j,
    };
    if recs[ri].1.len() != t.1.len() + 1 {
        return Ok(None);
    }
    Ok(Some(ProjRecOwner {
        t: t.0.dup2(),
        lps: nidx_vec_dup(&t.1),
        n_p: t.3,
        ctor: t.5[0].dup2(),
        n_f: ctors[ci].1,
        rec_name: recs[ri].0.dup2(),
        rec_lps: nidx_vec_dup(&recs[ri].1),
        rec_type: recs[ri].2.dup2(),
        num_motives: recs[ri].3,
        num_minors: recs[ri].4,
    }))
}

/// con-leche: ConLeche/Frontend/ProjRec.lean:332-370 projRecOwners
/// Lean twin: `proof/ConRon/Arena/Frontend/ProjRec.lean:482-517
/// projRecOwners` — the cited `types.map (·.1)`: the block's type formers.
pub fn type_names(types: &Vec<ProjTypeRec>) -> Vec<NIdx> {
    let n = types.len();
    let mut out: Vec<NIdx> = Vec::with_capacity(n);
    let mut i: usize = 0;
    while i < n {
        out.push(types[i].0.dup2());
        i += 1;
    }
    out
}

/// con-leche: ConLeche/Frontend/ProjRec.lean:332-370 projRecOwners
/// Lean twin: `proof/ConRon/Arena/Frontend/ProjRec.lean:482-517 projRecOwners` —
/// the cited `types.any (·.2.2.2.2.2.2)`: the export's own `isRec` flag on any
/// member.
pub fn any_is_rec(types: &Vec<ProjTypeRec>) -> bool {
    let n = types.len();
    let mut i: usize = 0;
    while i < n {
        if types[i].6 {
            return true;
        }
        i += 1;
    }
    false
}

/// con-leche: ConLeche/Frontend/ProjRec.lean:332-370 projRecOwners
/// Lean twin: `proof/ConRon/Arena/Frontend/ProjRec.lean:482-517 projRecOwners` —
/// the cited `(types.head?.map (·.2.2.2.1)).getD 0`: the block's DECLARED
/// parameter count, which is the first type record's and is what the parse
/// carries into `indDecl`.
pub fn declared_num_params(types: &Vec<ProjTypeRec>) -> u64 {
    if types.len() == 0 {
        0
    } else {
        types[0].3
    }
}

/// con-leche: ConLeche/Frontend/ProjRec.lean:332-370 projRecOwners
/// Lean twin: `proof/ConRon/Arena/Frontend/ProjRec.lean:482-517
/// projRecOwners` — **which block members the rewrite serves**: the officially
/// structure-like ones of a block the direct install does not recognise —
/// `struct_parts_core` rejects it (mutual, multi-constructor, indexed, shape
/// mismatch) or it is recursive (the export's `isRec`, or a block name
/// occurring in a constructor's binder domains) — and which the fixpoint route
/// does not serve natively either.  Propositional owners and owners whose
/// recursor carries no elimination level parameter are left out.
///
/// The guard ORDER is the module note's deviation 3; the two recognisers are
/// `arena::inductives::`'s own twins (the Lean side made the same move at task
/// #97f's dedup, and after it nothing in the frontend crosses to the `Expr`
/// denotation).
pub fn proj_rec_owners(
    pers: &PersTier,
    st: &mut AState,
    fuel: u64,
    block: &Vec<crate::arena::env::IConstantInfo>,
    types: &Vec<ProjTypeRec>,
    ctors: &Vec<ProjCtorRec>,
    recs: &Vec<ProjRecRec>,
) -> Result<Vec<ProjRecOwner>, CheckError> {
    match proj_rec_candidates(pers, st, ctors, recs, types) {
        Err(e) => Err(e),
        Ok(owners) => {
            if owners.len() == 0 {
                Ok(Vec::new())
            } else {
                proj_rec_owners_guard(pers, st, fuel, block, types, ctors, owners)
            }
        }
    }
}

/// con-leche: ConLeche/Frontend/ProjRec.lean:332-370 projRecOwners
/// Lean twin: `proof/ConRon/Arena/Frontend/ProjRec.lean:482-517 projRecOwners`
/// — the two recogniser guards, run only when there is a candidate to serve.
pub fn proj_rec_owners_guard(
    pers: &PersTier,
    st: &mut AState,
    fuel: u64,
    block: &Vec<crate::arena::env::IConstantInfo>,
    types: &Vec<ProjTypeRec>,
    ctors: &Vec<ProjCtorRec>,
    owners: Vec<ProjRecOwner>,
) -> Result<Vec<ProjRecOwner>, CheckError> {
    let block_names = type_names(types);
    let mentions = match ctors_mention_block(pers, st, fuel, &block_names, ctors) {
        Err(e) => return Err(e),
        Ok(v) => v,
    };
    let recursive = any_is_rec(types) || mentions;
    let direct = match struct_parts::struct_parts_core(pers, st, block) {
        Err(e) => return Err(e),
        Ok(Some(_)) => true,
        Ok(None) => false,
    };
    if direct && !recursive {
        return Ok(Vec::new());
    }
    // a block the fixpoint route takes serves its structure-like member's
    // `.proj` nodes natively, so no rewrite (the block's DECLARED parameter
    // count: the first type record's, which is what the parse carries into
    // `indDecl`)
    match native_parts::native_parts(pers, st, declared_num_params(types), block) {
        Err(e) => Err(e),
        Ok(Some(_)) => Ok(Vec::new()),
        Ok(None) => Ok(owners),
    }
}
#[cfg(test)]
mod tests {
    // Task #97-SWAP: this module's tests were a DIFFERENTIAL harness — every
    // one ran the subject here and `con-ron-core`'s `Expr`-tree twin of it on
    // the same fixture and compared the two outcomes, which is how the arena
    // was brought up beside the shipping checker (DESIGN.md §8.6).  The swap
    // deleted the twin: this IS the checker now, and there is nothing left to
    // compare against in-process.  `scripts/diff-e2e.sh` is the differential
    // test from here — 383 fixtures through the whole binary, against
    // con-leche's own verdicts — and it is a gate, not a unit test.
}
