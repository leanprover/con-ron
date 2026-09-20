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
use crate::arena::handle::{EIdx, LIdx, LsIdx, NIdx};
use crate::arena::inductives::native_parts;
use crate::arena::inductives::struct_parts;
use crate::arena::monad::{
    fail, intern_e, intern_l_node, intern_ls_node, intern_n_node, intern_name, read_level,
    view, view_ls, view_n, AState,
};
use crate::arena::store::{ENodeView, LNodeView, NNodeView};
use crate::frontend::types::ProjRecOwner;
use con_ron_core::frontend::text;
use con_ron_core::kernel::basis_names as bnm;
use con_ron_core::kernel::core_types::{code_points, CheckError};
use con_ron_core::kernel::expr;
use con_ron_core::kernel::expr::BinderMeta;
use con_ron_core::kernel::level;
use con_ron_core::ron::hashmap::{Dup, Eq2, HashMap};

// ---------------------------------------------------------------------------
// The shape records `projRecOwners` takes (`ProjRec.lean:498-501` of the twin)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Frontend/ProjRec.lean:332-370 projRecOwners
/// Lean twin: `proof/ConRon/Arena/Frontend/ProjRec.lean:499 projRecOwners` —
/// one type former of the parsed block as the census reads it:
/// `(name, levelParams, type, numParams, numIndices, ctors, isRec)`, the
/// export record's own data over handles.  The twin's tuple, spelled as a
/// tuple (`con_ron_core::frontend::proj_rec` names the seven fields instead;
/// here the twin is the original and `t.6` is `·.2.2.2.2.2.2`).
pub type ProjTypeRec = (NIdx, Vec<NIdx>, EIdx, u64, u64, Vec<NIdx>, bool);

/// con-leche: ConLeche/Frontend/ProjRec.lean:332-370 projRecOwners
/// Lean twin: `proof/ConRon/Arena/Frontend/ProjRec.lean:500 projRecOwners` —
/// one constructor: `(name, numFields, type)`.
pub type ProjCtorRec = (NIdx, u64, EIdx);

/// con-leche: ConLeche/Frontend/ProjRec.lean:332-370 projRecOwners
/// Lean twin: `proof/ConRon/Arena/Frontend/ProjRec.lean:501 projRecOwners` —
/// one recursor: `(name, levelParams, type, numMotives, numMinors)`.
pub type ProjRecRec = (NIdx, Vec<NIdx>, EIdx, u64, u64);

/// con-leche: ConLeche/Frontend/ProjRec.lean:83-104 ProjRecOwner
/// Lean twin: `proof/ConRon/Arena/Frontend/Types.lean:68-79 ProjRecOwner` —
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
/// Lean twin: `proof/ConRon/Arena/Frontend/ProjRec.lean:77-80 projIotaName` —
/// the name of the model family's constructor-reduction theorem for field `i`
/// of `T`: `T._model.proj_i.iota`.  Building a name means interning it, so the
/// twin is monadic and this takes the state; the cited `s!"proj_{i}"` is
/// `text::cat` of `text::u64_str` (§3.4 has no `format!`).
pub fn proj_iota_name(st: &mut AState, t: &NIdx, i: u64) -> Result<NIdx, CheckError> {
    match intern_n_node(st, NNodeView::Str(t.dup2(), code_points(&M_MODEL))) {
        Err(e) => Err(e),
        Ok(a) => {
            let s = text::cat(code_points(&M_PROJ), &text::u64_str(i));
            match intern_n_node(st, NNodeView::Str(a, s)) {
                Err(e) => Err(e),
                Ok(b) => intern_n_node(st, NNodeView::Str(b, code_points(&M_IOTA))),
            }
        }
    }
}

/// con-leche: ConLeche/Frontend/ProjRec.lean:113-118 isProjIotaName
/// Lean twin: `proof/ConRon/Arena/Frontend/ProjRec.lean:85-94 isProjIotaName`
/// — is `n` of the shape `X._model.proj_i.iota`?  The cheap pre-filter for the
/// theorem records; the last component decides before anything is compared.
pub fn is_proj_iota_name(st: &AState, n: &NIdx) -> Result<bool, CheckError> {
    match view_n(st, n) {
        Err(e) => Err(e),
        Ok(NNodeView::Str(p1, last)) => {
            if !text::cps_beq(&last, &M_IOTA) {
                Ok(false)
            } else {
                is_proj_iota_pre(st, &p1)
            }
        }
        Ok(_) => Ok(false),
    }
}

/// con-leche: ConLeche/Frontend/ProjRec.lean:113-118 isProjIotaName
/// Lean twin: `proof/ConRon/Arena/Frontend/ProjRec.lean:85-94 isProjIotaName`
/// — the two inner `match ← viewN`es, past the `"iota"` test.  Its own
/// function so that the outer `view_n`'s loan is dead where the next one is
/// taken (extraction rule 5).
pub fn is_proj_iota_pre(st: &AState, p1: &NIdx) -> Result<bool, CheckError> {
    match view_n(st, p1) {
        Err(e) => Err(e),
        Ok(NNodeView::Str(p2, s)) => match view_n(st, &p2) {
            Err(e) => Err(e),
            Ok(NNodeView::Str(_, m)) => {
                Ok(text::cps_beq(&m, &M_MODEL) && cps_starts_with(&s, &M_PROJ))
            }
            Ok(_) => Ok(false),
        },
        Ok(_) => Ok(false),
    }
}

/// con-leche: ConLeche/Frontend/ProjRec.lean:120-125 projIotaLevel
/// Lean twin: `proof/ConRon/Arena/Frontend/ProjRec.lean:100-110 projIotaLevel`
/// — the `Eq` level of an artifact iota statement `∀ …, @Eq.{ℓ} α a b`: the
/// field's sort.  `None` on any other shape.  The universe argument list is
/// ONE handle (DESIGN.md §8.3's `LsIdx`), so the singleton test is a
/// `view_ls`; `Eq`'s own name is interned, which is why this takes `&mut`.
pub fn proj_iota_level(
    st: &mut AState,
    fuel: u64,
    ty: &EIdx,
) -> Result<Option<LIdx>, CheckError> {
    match expr_ops::pi_result(st, fuel, ty) {
        Err(e) => Err(e),
        Ok(r) => match expr_ops::get_app_fn(st, fuel, &r) {
            Err(e) => Err(e),
            Ok(f) => match view(st, &f) {
                Err(e) => Err(e),
                Ok(ENodeView::Const(n, us)) => proj_iota_level_at(st, &n, &us),
                Ok(_) => Ok(None),
            },
        },
    }
}

/// con-leche: ConLeche/Frontend/ProjRec.lean:120-125 projIotaLevel
/// Lean twin: `proof/ConRon/Arena/Frontend/ProjRec.lean:104-109 projIotaLevel`
/// — the `.const` arm: a one-element universe list on the constant `Eq`.  Its
/// own function because the `view`'s loan is dead before `Eq` is interned
/// (extraction rule 5).
pub fn proj_iota_level_at(
    st: &mut AState,
    n: &NIdx,
    us: &LsIdx,
) -> Result<Option<LIdx>, CheckError> {
    match view_ls(st, us) {
        Err(e) => Err(e),
        Ok(ls) => {
            if ls.len() != 1 {
                Ok(None)
            } else {
                match intern_name(st, &bnm::eq_name()) {
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
/// Lean twin: `proof/ConRon/Arena/Frontend/ProjRec.lean:141-187 occursConstGo`
/// — the memoised descent: the set holds the subterms already shown NOT to
/// mention `n`.  Only `false` is recorded — a `true` aborts the walk, so no
/// `true` is ever re-queried.  The set is keyed on the handle, which is
/// nanoda's identity hash (DESIGN.md §8.3) and con-leche's `Std.HashSet Expr`
/// with its cached hash; it is threaded **by value**, which is the twin's
/// `AM (Bool × Std.HashSet EIdx)` term for term.
pub fn occurs_const_go(
    st: &AState,
    n: &NIdx,
    seen: HashMap<EIdx, bool>,
    fuel: u64,
    h: &EIdx,
) -> Result<(bool, HashMap<EIdx, bool>), CheckError> {
    if fuel == 0 {
        fail(CheckError::Internal(code_points(&M_FUEL_OCCURS)))
    } else {
        match view(st, h) {
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
                    occurs_const_node(st, n, seen, fuel - 1, h, v)
                }
            }
        }
    }
}

/// con-leche: ConLeche/Frontend/ProjRec.lean:180-225 occursConstGo
/// Lean twin: `proof/ConRon/Arena/Frontend/ProjRec.lean:148-187 occursConstGo`
/// — the compound arms, past the probe: walk the children and record the node
/// when the answer is `false`.  Split off so the `view`'s loans are dead at
/// the memo's join (extraction rule 5).
pub fn occurs_const_node(
    st: &AState,
    n: &NIdx,
    seen: HashMap<EIdx, bool>,
    fuel: u64,
    h: &EIdx,
    v: ENodeView,
) -> Result<(bool, HashMap<EIdx, bool>), CheckError> {
    match v {
        ENodeView::App(f, a) => occurs_const_two(st, n, seen, fuel, h, &f, &a),
        ENodeView::Lam(ty, b, _) => occurs_const_two(st, n, seen, fuel, h, &ty, &b),
        ENodeView::ForallE(ty, b, _) => occurs_const_two(st, n, seen, fuel, h, &ty, &b),
        ENodeView::LetE(t, val, b) => match occurs_const_go(st, n, seen, fuel, &t) {
            Err(e) => Err(e),
            Ok((true, m)) => Ok((true, m)),
            Ok((false, m)) => occurs_const_two(st, n, m, fuel, h, &val, &b),
        },
        ENodeView::Proj(_, _, sub) => match occurs_const_go(st, n, seen, fuel, &sub) {
            Err(e) => Err(e),
            Ok((true, m)) => Ok((true, m)),
            Ok((false, m)) => Ok((false, occurs_record(m, h))),
        },
        // unreachable: the five leaf kinds answered before the probe
        _ => Ok((false, seen)),
    }
}

/// con-leche: ConLeche/Frontend/ProjRec.lean:180-225 occursConstGo
/// Lean twin: `proof/ConRon/Arena/Frontend/ProjRec.lean:148-171 occursConstGo`
/// — the two-child arms (`app`, `lam`, `forallE`, and `letE`'s tail), which
/// are one `match` nest in the twin and one function here.
pub fn occurs_const_two(
    st: &AState,
    n: &NIdx,
    seen: HashMap<EIdx, bool>,
    fuel: u64,
    h: &EIdx,
    x: &EIdx,
    y: &EIdx,
) -> Result<(bool, HashMap<EIdx, bool>), CheckError> {
    match occurs_const_go(st, n, seen, fuel, x) {
        Err(e) => Err(e),
        Ok((true, m)) => Ok((true, m)),
        Ok((false, m)) => match occurs_const_go(st, n, m, fuel, y) {
            Err(e) => Err(e),
            Ok((true, m2)) => Ok((true, m2)),
            Ok((false, m2)) => Ok((false, occurs_record(m2, h))),
        },
    }
}

/// con-leche: ConLeche/Frontend/ProjRec.lean:180-225 occursConstGo
/// Lean twin: `proof/ConRon/Arena/Frontend/ProjRec.lean:153 occursConstGo` —
/// the cited `seen.insert h`, on the owned table.
pub fn occurs_record(seen: HashMap<EIdx, bool>, h: &EIdx) -> HashMap<EIdx, bool> {
    let mut m: HashMap<EIdx, bool> = seen;
    m.insert(h.dup2(), false);
    m
}

/// con-leche: ConLeche/Frontend/ProjRec.lean:227-231 occursConstFast
/// Lean twin: `proof/ConRon/Arena/Frontend/ProjRec.lean:192-193
/// occursConstFast` — the executed `occursConst`: the memoised descent at a
/// fresh set.
pub fn occurs_const_fast(
    st: &AState,
    fuel: u64,
    n: &NIdx,
    h: &EIdx,
) -> Result<bool, CheckError> {
    let seen: HashMap<EIdx, bool> = HashMap::new();
    match occurs_const_go(st, n, seen, fuel, h) {
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
/// Lean twin: `proof/ConRon/Arena/Frontend/ProjRec.lean:200-205 lamBody` — the
/// body under every leading `λ` (the projection shape's pre-filter: the node
/// under the value's binders).
pub fn lam_body(st: &AState, fuel: u64, h: &EIdx) -> Result<EIdx, CheckError> {
    if fuel == 0 {
        fail(CheckError::Internal(code_points(&M_FUEL_LAM_BODY)))
    } else {
        match view(st, h) {
            Err(e) => Err(e),
            Ok(ENodeView::Lam(_, b, _)) => lam_body(st, fuel - 1, &b),
            Ok(_) => Ok(h.dup2()),
        }
    }
}

/// con-leche: ConLeche/Frontend/ProjRec.lean:239-245 stripPisAll
/// Lean twin: `proof/ConRon/Arena/Frontend/ProjRec.lean:209-216 stripPisAll` —
/// strip every leading `∀`: the binder list (outermost first) and the body.
pub fn strip_pis_all(
    st: &AState,
    fuel: u64,
    h: &EIdx,
) -> Result<(Vec<(EIdx, BinderMeta)>, EIdx), CheckError> {
    if fuel == 0 {
        fail(CheckError::Internal(code_points(&M_FUEL_STRIP_PIS_ALL)))
    } else {
        match view(st, h) {
            Err(e) => Err(e),
            Ok(ENodeView::ForallE(ty, b, m)) => match strip_pis_all(st, fuel - 1, &b) {
                Err(e) => Err(e),
                Ok(p) => Ok((expr_ops::cons_binder(&ty, &m, &p.0), p.1)),
            },
            Ok(_) => Ok((Vec::new(), h.dup2())),
        }
    }
}

/// con-leche: ConLeche/Frontend/ProjRec.lean:247-249 mkLams
/// Lean twin: `proof/ConRon/Arena/Frontend/ProjRec.lean:221-225 mkLams` —
/// rebuild a `λ`-telescope over a binder list (outermost first).  Structural
/// on the list, so no fuel; every binder is interned.  The `i = 0` wrapper of
/// the cursor recursion below.
pub fn mk_lams(
    st: &mut AState,
    bs: &Vec<(EIdx, BinderMeta)>,
    body: &EIdx,
) -> Result<EIdx, CheckError> {
    mk_lams_from(st, bs, 0, body)
}

/// con-leche: ConLeche/Frontend/ProjRec.lean:247-249 mkLams
/// Lean twin: `proof/ConRon/Arena/Frontend/ProjRec.lean:221-225 mkLams` — the
/// cursor recursion behind `mk_lams`: the twin conses on the way OUT, so the
/// cursor recurses to the end of the list and interns outward from there.
pub fn mk_lams_from(
    st: &mut AState,
    bs: &Vec<(EIdx, BinderMeta)>,
    i: usize,
    body: &EIdx,
) -> Result<EIdx, CheckError> {
    if i >= bs.len() {
        Ok(body.dup2())
    } else {
        match mk_lams_from(st, bs, i + 1, body) {
            Err(e) => Err(e),
            Ok(acc) => intern_e(
                st,
                ENodeView::Lam(bs[i].0.dup2(), acc, expr::binder_meta_dup(&bs[i].1)),
            ),
        }
    }
}

/// con-leche: ConLeche/Frontend/ProjRec.lean:251-257 instPisOpen
/// Lean twin: `proof/ConRon/Arena/Frontend/ProjRec.lean:232-239 instPisOpen` —
/// instantiate the leading `∀`-binders at *open* arguments (the body-frame
/// variables and the built motives/minors), one binder per argument, returning
/// the residual telescope.  Structural on the argument list; `fuel` is the one
/// `instantiate1_lift_fast` needs.  The `i = 0` wrapper of the cursor
/// recursion below.
pub fn inst_pis_open(
    st: &mut AState,
    fuel: u64,
    e: &EIdx,
    args: &Vec<EIdx>,
) -> Result<Option<EIdx>, CheckError> {
    inst_pis_open_from(st, fuel, e, args, 0)
}

/// con-leche: ConLeche/Frontend/ProjRec.lean:251-257 instPisOpen
/// Lean twin: `proof/ConRon/Arena/Frontend/ProjRec.lean:232-239 instPisOpen` —
/// the cursor recursion behind `inst_pis_open`.
pub fn inst_pis_open_from(
    st: &mut AState,
    fuel: u64,
    e: &EIdx,
    args: &Vec<EIdx>,
    i: usize,
) -> Result<Option<EIdx>, CheckError> {
    if i >= args.len() {
        Ok(Some(e.dup2()))
    } else {
        match view(st, e) {
            Err(er) => Err(er),
            Ok(ENodeView::ForallE(_, body, _)) => {
                match expr_ops::instantiate1_lift_fast(st, fuel, &body, &args[i], 0) {
                    Err(er) => Err(er),
                    Ok(b) => inst_pis_open_from(st, fuel, &b, args, i + 1),
                }
            }
            Ok(_) => Ok(None),
        }
    }
}

// ---------------------------------------------------------------------------
// The two binder bodies, and the peel that uses them
// (`ProjRec.lean:241-330` of the twin)
// ---------------------------------------------------------------------------

/// con-leche: none — which of `projRecValue`'s two `mk` lambdas `buildBinders` runs
/// Lean twin: `proof/ConRon/Arena/Frontend/ProjRec.lean:247-250
/// ProjBinderKind` — con-leche passes the lambda itself; DESIGN.md §3.4
/// forbids a closure in translated code (and this one takes the state
/// besides), so the twin passes the tag the Rust would need anyway, and here
/// it is.
pub enum ProjBinderKind {
    Motive,
    Minor,
}

/// con-leche: none — what `projRecValue`'s two `mk` lambdas capture
/// Lean twin: `proof/ConRon/Arena/Frontend/ProjRec.lean:256-262 ProjBuild` —
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
/// Lean twin: `proof/ConRon/Arena/Frontend/ProjRec.lean:267-270 headIs` — is
/// `T` the head of the owner's own carrier: the motive domain
/// `∀ (t : T p⃗), Sort ℓ` (exactly one binder) or the major-premise domain.
pub fn head_is(st: &AState, fuel: u64, t: &NIdx, e: &EIdx) -> Result<bool, CheckError> {
    match expr_ops::get_app_fn(st, fuel, e) {
        Err(er) => Err(er),
        Ok(f) => match view(st, &f) {
            Err(er) => Err(er),
            Ok(ENodeView::Const(n, _)) => Ok(n.eq2(t)),
            Ok(_) => Ok(false),
        },
    }
}

/// con-leche: ConLeche/Frontend/ProjRec.lean:279-330 projRecValue
/// Lean twin: `proof/ConRon/Arena/Frontend/ProjRec.lean:277-289 mkProjMotive`
/// — the motive body (`mkMotive` inside `projRecValue`): the owner's motive is
/// `fun (t : T p⃗) => R` — `R`'s parameter references skip the new binder, its
/// subject reference IS the new binder — and every other one is the constant
/// `PUnit.{ℓ}` over its telescope.
pub fn mk_proj_motive(
    st: &mut AState,
    pb: &ProjBuild,
    fuel: u64,
    dom: &EIdx,
) -> Result<Option<EIdx>, CheckError> {
    match strip_pis_all(st, fuel, dom) {
        Err(e) => Err(e),
        Ok(bse) => match view(st, &bse.1) {
            Err(e) => Err(e),
            Ok(ENodeView::Sort(_)) => mk_proj_motive_at(st, pb, fuel, &bse.0),
            Ok(_) => Ok(None),
        },
    }
}

/// con-leche: ConLeche/Frontend/ProjRec.lean:279-330 projRecValue
/// Lean twin: `proof/ConRon/Arena/Frontend/ProjRec.lean:280-288 mkProjMotive`
/// — the cited `match bs with | [(d, m)] => … | bs => …`, past the sort test.
pub fn mk_proj_motive_at(
    st: &mut AState,
    pb: &ProjBuild,
    fuel: u64,
    bs: &Vec<(EIdx, BinderMeta)>,
) -> Result<Option<EIdx>, CheckError> {
    if bs.len() != 1 {
        match mk_lams(st, bs, &pb.punit_c) {
            Err(e) => Err(e),
            Ok(r) => Ok(Some(r)),
        }
    } else {
        match head_is(st, fuel, &pb.t, &bs[0].0) {
            Err(e) => Err(e),
            Ok(true) => match expr_ops::lift_loose_bvars_fast(st, fuel, 1, 1, &pb.r) {
                Err(e) => Err(e),
                Ok(rl) => match intern_e(
                    st,
                    ENodeView::Lam(bs[0].0.dup2(), rl, expr::binder_meta_dup(&bs[0].1)),
                ) {
                    Err(e) => Err(e),
                    Ok(r) => Ok(Some(r)),
                },
            },
            Ok(false) => match intern_e(
                st,
                ENodeView::Lam(
                    bs[0].0.dup2(),
                    pb.punit_c.dup2(),
                    expr::binder_meta_dup(&bs[0].1),
                ),
            ) {
                Err(e) => Err(e),
                Ok(r) => Ok(Some(r)),
            },
        }
    }
}

/// con-leche: ConLeche/Frontend/ProjRec.lean:279-330 projRecValue
/// Lean twin: `proof/ConRon/Arena/Frontend/ProjRec.lean:297-307 mkProjMinor` —
/// the minor body (`mkMinor` inside `projRecValue`): the owner constructor's
/// minor returns field `i` of its telescope (the fields come first, then the
/// inductive hypotheses recursion adds); every other one returns
/// `PUnit.unit.{ℓ}`.  The owner's minor is the one whose codomain applies a
/// motive to the owner constructor.
pub fn mk_proj_minor(
    st: &mut AState,
    pb: &ProjBuild,
    fuel: u64,
    dom: &EIdx,
) -> Result<Option<EIdx>, CheckError> {
    match strip_pis_all(st, fuel, dom) {
        Err(e) => Err(e),
        Ok(bse) => match expr_ops::get_app_args(st, fuel, &bse.1) {
            Err(e) => Err(e),
            Ok(args) => {
                if args.len() == 0 {
                    Ok(None)
                } else {
                    mk_proj_minor_at(st, pb, fuel, &bse.0, &args[args.len() - 1])
                }
            }
        },
    }
}

/// con-leche: ConLeche/Frontend/ProjRec.lean:279-330 projRecValue
/// Lean twin: `proof/ConRon/Arena/Frontend/ProjRec.lean:300-306 mkProjMinor` —
/// the cited `if ← headIs fuel pb.ctor major then … else …`, at the spine's
/// last argument.
pub fn mk_proj_minor_at(
    st: &mut AState,
    pb: &ProjBuild,
    fuel: u64,
    bs: &Vec<(EIdx, BinderMeta)>,
    major: &EIdx,
) -> Result<Option<EIdx>, CheckError> {
    match head_is(st, fuel, &pb.ctor, major) {
        Err(e) => Err(e),
        Ok(false) => match mk_lams(st, bs, &pb.punit_unit_c) {
            Err(e) => Err(e),
            Ok(r) => Ok(Some(r)),
        },
        Ok(true) => {
            if pb.i >= bs.len() as u64 {
                Ok(None)
            } else {
                match intern_e(st, ENodeView::BVar(bs.len() as u64 - 1 - pb.i)) {
                    Err(e) => Err(e),
                    Ok(b) => match mk_lams(st, bs, &b) {
                        Err(e) => Err(e),
                        Ok(r) => Ok(Some(r)),
                    },
                }
            }
        }
    }
}

/// con-leche: ConLeche/Frontend/ProjRec.lean:259-269 buildBinders
/// Lean twin: `proof/ConRon/Arena/Frontend/ProjRec.lean:314-330 buildBinders`
/// — peel `k` binders of a telescope, building one term per binder from its
/// (progressively instantiated) domain, and instantiating the telescope with
/// that term before the next binder is read.  `kind` is con-leche's `mk`
/// argument, as the module note explains.
pub fn build_binders(
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
        match view(st, h) {
            Err(e) => Err(e),
            Ok(ENodeView::ForallE(dom, body, _)) => {
                build_binders_at(st, kind, pb, fuel, k, &dom, &body)
            }
            Ok(_) => Ok(None),
        }
    }
}

/// con-leche: ConLeche/Frontend/ProjRec.lean:259-269 buildBinders
/// Lean twin: `proof/ConRon/Arena/Frontend/ProjRec.lean:319-329 buildBinders`
/// — the `.forallE` arm's `do` block, at the binder's domain and body.  Its
/// own function because the `view`'s loans may not still be alive where the
/// recursion interns (extraction rule 5 / AENEAS_FINDINGS §2.1 F3: an arm ends
/// in a call, never in a branch).
pub fn build_binders_at(
    st: &mut AState,
    kind: &ProjBinderKind,
    pb: &ProjBuild,
    fuel: u64,
    k: u64,
    dom: &EIdx,
    body: &EIdx,
) -> Result<Option<(Vec<EIdx>, EIdx)>, CheckError> {
    let t = match kind {
        ProjBinderKind::Motive => mk_proj_motive(st, pb, fuel, dom),
        ProjBinderKind::Minor => mk_proj_minor(st, pb, fuel, dom),
    };
    match t {
        Err(e) => Err(e),
        Ok(None) => Ok(None),
        Ok(Some(t)) => match expr_ops::instantiate1_lift_fast(st, fuel, body, &t, 0) {
            Err(e) => Err(e),
            Ok(body2) => match build_binders(st, kind, pb, fuel, k - 1, &body2) {
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
/// Lean twin: `proof/ConRon/Arena/Frontend/ProjRec.lean:395-400
/// internParamLevels` — `o.lps.map Level.param`, interned: a `List.map` with a
/// closure is §3.4's explicit recursion here.  The `i = 0` wrapper.
pub fn intern_param_levels(
    st: &mut AState,
    ns: &Vec<NIdx>,
) -> Result<Vec<LIdx>, CheckError> {
    intern_param_levels_from(st, ns, 0)
}

/// con-leche: ConLeche/Frontend/ProjRec.lean:279-330 projRecValue
/// Lean twin: `proof/ConRon/Arena/Frontend/ProjRec.lean:395-400
/// internParamLevels` — the cursor recursion behind `intern_param_levels`.
pub fn intern_param_levels_from(
    st: &mut AState,
    ns: &Vec<NIdx>,
    i: usize,
) -> Result<Vec<LIdx>, CheckError> {
    if i >= ns.len() {
        Ok(Vec::new())
    } else {
        match intern_l_node(st, LNodeView::Param(ns[i].dup2())) {
            Err(e) => Err(e),
            Ok(h) => match intern_param_levels_from(st, ns, i + 1) {
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
/// Lean twin: `proof/ConRon/Arena/Frontend/ProjRec.lean:343-390 projRecValue`
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
    st: &mut AState,
    fuel: u64,
    o: &ProjRecOwner,
    l: &LIdx,
    ty: &EIdx,
    val: &EIdx,
    i: u64,
) -> Result<Option<EIdx>, CheckError> {
    match expr_ops::strip_lams(st, o.n_p + 1, val) {
        Err(e) => Err(e),
        Ok(None) => Ok(None),
        Ok(Some(lbsb)) => match view(st, &lbsb.1) {
            Err(e) => Err(e),
            Ok(ENodeView::Proj(tn, bi, sub)) => match view(st, &sub) {
                Err(e) => Err(e),
                Ok(ENodeView::BVar(0)) => {
                    if !tn.eq2(&o.t) || bi != i || i >= o.n_f {
                        Ok(None)
                    } else {
                        proj_rec_value_ty(st, fuel, o, l, ty, i, &lbsb.0)
                    }
                }
                Ok(_) => Ok(None),
            },
            Ok(_) => Ok(None),
        },
    }
}

/// con-leche: ConLeche/Frontend/ProjRec.lean:279-330 projRecValue
/// Lean twin: `proof/ConRon/Arena/Frontend/ProjRec.lean:353-355 projRecValue`
/// — the cited `match ← stripPis (o.nP + 1) ty with`, past the shape test.
pub fn proj_rec_value_ty(
    st: &mut AState,
    fuel: u64,
    o: &ProjRecOwner,
    l: &LIdx,
    ty: &EIdx,
    i: u64,
    lbs: &Vec<(EIdx, BinderMeta)>,
) -> Result<Option<EIdx>, CheckError> {
    match expr_ops::strip_pis(st, o.n_p + 1, ty) {
        Err(e) => Err(e),
        Ok(None) => Ok(None),
        Ok(Some(r)) => proj_rec_value_at(st, fuel, o, l, &r.1, i, lbs),
    }
}

/// con-leche: ConLeche/Frontend/ProjRec.lean:279-330 projRecValue
/// Lean twin: `proof/ConRon/Arena/Frontend/ProjRec.lean:356-372 projRecValue`
/// — the recursor's type at the chosen elimination level, its parameters
/// instantiated at the body frame (`nP + 1` binders: parameter `k` is
/// `bvar (nP - k)`, the subject `bvar 0`), and the two `PUnit` constants the
/// binder bodies read, interned once.
pub fn proj_rec_value_at(
    st: &mut AState,
    fuel: u64,
    o: &ProjRecOwner,
    l: &LIdx,
    r: &EIdx,
    i: u64,
    lbs: &Vec<(EIdx, BinderMeta)>,
) -> Result<Option<EIdx>, CheckError> {
    let ups = match intern_param_levels(st, &o.lps) {
        Err(e) => return Err(e),
        Ok(v) => v,
    };
    let us = match intern_ls_node(st, cons_lidx(l, &ups)) {
        Err(e) => return Err(e),
        Ok(v) => v,
    };
    let rty0 = match expr_ops::inst_lp_fast(st, fuel, &o.rec_lps, &us, &o.rec_type) {
        Err(e) => return Err(e),
        Ok(v) => v,
    };
    let params = match expr_ops::bvar_range(st, o.n_p + 1, o.n_p, 0) {
        Err(e) => return Err(e),
        Ok(v) => v,
    };
    match inst_pis_open(st, fuel, &rty0, &params) {
        Err(e) => Err(e),
        Ok(None) => Ok(None),
        Ok(Some(rty1)) => proj_rec_value_binders(st, fuel, o, l, r, i, lbs, &us, &params, &rty1),
    }
}

/// con-leche: ConLeche/Frontend/ProjRec.lean:279-330 projRecValue
/// Lean twin: `proof/ConRon/Arena/Frontend/ProjRec.lean:366-378 projRecValue`
/// — the `ProjBuild` record and the two `buildBinders` runs.
pub fn proj_rec_value_binders(
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
    let punit_h = match intern_name(st, &bnm::punit_name()) {
        Err(e) => return Err(e),
        Ok(v) => v,
    };
    let punit_u_h = match intern_name(st, &bnm::punit_unit_name()) {
        Err(e) => return Err(e),
        Ok(v) => v,
    };
    let ls_one = match intern_ls_node(st, one_lidx(l)) {
        Err(e) => return Err(e),
        Ok(v) => v,
    };
    let punit_c = match intern_e(st, ENodeView::Const(punit_h, ls_one.dup2())) {
        Err(e) => return Err(e),
        Ok(v) => v,
    };
    let punit_unit_c = match intern_e(st, ENodeView::Const(punit_u_h, ls_one)) {
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
    match build_binders(st, &ProjBinderKind::Motive, &pb, fuel, o.num_motives, rty1) {
        Err(e) => Err(e),
        Ok(None) => Ok(None),
        Ok(Some(mrt)) => {
            match build_binders(st, &ProjBinderKind::Minor, &pb, fuel, o.num_minors, &mrt.1) {
                Err(e) => Err(e),
                Ok(None) => Ok(None),
                Ok(Some(nrt)) => proj_rec_value_major(
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
/// Lean twin: `proof/ConRon/Arena/Frontend/ProjRec.lean:379-388 projRecValue`
/// — the cited final `match ← view rty3 with | .forallE majDom _ _ => …`: the
/// owner has no indices, so the next binder is the subject itself, and the
/// value is `T.rec.{ℓ, u⃗} p⃗ motives minors (bvar 0)` under the definition's
/// own binders.
pub fn proj_rec_value_major(
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
    match view(st, rty3) {
        Err(e) => Err(e),
        Ok(ENodeView::ForallE(maj_dom, _, _)) => match head_is(st, fuel, &o.t, &maj_dom) {
            Err(e) => Err(e),
            Ok(false) => Ok(None),
            Ok(true) => proj_rec_value_app(st, o, lbs, us, params, motives, minors),
        },
        Ok(_) => Ok(None),
    }
}

/// con-leche: ConLeche/Frontend/ProjRec.lean:279-330 projRecValue
/// Lean twin: `proof/ConRon/Arena/Frontend/ProjRec.lean:384-387 projRecValue`
/// — the spine itself, past the major-premise test: `mkAppN` of the recursor
/// constant over `params ++ motives ++ minors ++ [bvar 0]`, under `mkLams`.
pub fn proj_rec_value_app(
    st: &mut AState,
    o: &ProjRecOwner,
    lbs: &Vec<(EIdx, BinderMeta)>,
    us: &LsIdx,
    params: &Vec<EIdx>,
    motives: &Vec<EIdx>,
    minors: &Vec<EIdx>,
) -> Result<Option<EIdx>, CheckError> {
    let rc = match intern_e(st, ENodeView::Const(o.rec_name.dup2(), us.dup2())) {
        Err(e) => return Err(e),
        Ok(v) => v,
    };
    let b0 = match intern_e(st, ENodeView::BVar(0)) {
        Err(e) => return Err(e),
        Ok(v) => v,
    };
    let mut args: Vec<EIdx> = Vec::new();
    args = append_eidx(args, params);
    args = append_eidx(args, motives);
    args = append_eidx(args, minors);
    args.push(b0);
    match expr_ops::mk_app_n(st, &rc, &args) {
        Err(e) => Err(e),
        Ok(app) => match mk_lams(st, lbs, &app) {
            Err(e) => Err(e),
            Ok(r) => Ok(Some(r)),
        },
    }
}

// ---------------------------------------------------------------------------
// Which owners the rewrite serves (`ProjRec.lean:402-517` of the twin)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Frontend/ProjRec.lean:332-370 projRecOwners
/// Lean twin: `proof/ConRon/Arena/Frontend/ProjRec.lean:407-411 occursAnyOf` —
/// does any of `ns` occur in `d`?  con-leche's inner `blockNames.any`, as an
/// explicit recursion (§3.4).  The `i = 0` wrapper.
pub fn occurs_any_of(
    st: &AState,
    fuel: u64,
    ns: &Vec<NIdx>,
    d: &EIdx,
) -> Result<bool, CheckError> {
    occurs_any_of_from(st, fuel, ns, d, 0)
}

/// con-leche: ConLeche/Frontend/ProjRec.lean:332-370 projRecOwners
/// Lean twin: `proof/ConRon/Arena/Frontend/ProjRec.lean:407-411 occursAnyOf` —
/// the cursor recursion behind `occurs_any_of`.
pub fn occurs_any_of_from(
    st: &AState,
    fuel: u64,
    ns: &Vec<NIdx>,
    d: &EIdx,
    i: usize,
) -> Result<bool, CheckError> {
    if i >= ns.len() {
        Ok(false)
    } else {
        match occurs_const_fast(st, fuel, &ns[i], d) {
            Err(e) => Err(e),
            Ok(true) => Ok(true),
            Ok(false) => occurs_any_of_from(st, fuel, ns, d, i + 1),
        }
    }
}

/// con-leche: ConLeche/Frontend/ProjRec.lean:332-370 projRecOwners
/// Lean twin: `proof/ConRon/Arena/Frontend/ProjRec.lean:416-420 domsMentionAny`
/// — does any of `ns` occur in any binder domain of the list?  con-leche's
/// middle `(stripPisAll cty).1.any`, as an explicit recursion.  The `i = 0`
/// wrapper.
pub fn doms_mention_any(
    st: &AState,
    fuel: u64,
    ns: &Vec<NIdx>,
    bs: &Vec<(EIdx, BinderMeta)>,
) -> Result<bool, CheckError> {
    doms_mention_any_from(st, fuel, ns, bs, 0)
}

/// con-leche: ConLeche/Frontend/ProjRec.lean:332-370 projRecOwners
/// Lean twin: `proof/ConRon/Arena/Frontend/ProjRec.lean:416-420 domsMentionAny`
/// — the cursor recursion behind `doms_mention_any`.
pub fn doms_mention_any_from(
    st: &AState,
    fuel: u64,
    ns: &Vec<NIdx>,
    bs: &Vec<(EIdx, BinderMeta)>,
    i: usize,
) -> Result<bool, CheckError> {
    if i >= bs.len() {
        Ok(false)
    } else {
        match occurs_any_of(st, fuel, ns, &bs[i].0) {
            Err(e) => Err(e),
            Ok(true) => Ok(true),
            Ok(false) => doms_mention_any_from(st, fuel, ns, bs, i + 1),
        }
    }
}

/// con-leche: ConLeche/Frontend/ProjRec.lean:332-370 projRecOwners
/// Lean twin: `proof/ConRon/Arena/Frontend/ProjRec.lean:425-431
/// ctorsMentionBlock` — a block name in a constructor's binder *domains* (its
/// result names the owner by definition): con-leche's outer `ctors.any`, as an
/// explicit recursion.  The `i = 0` wrapper.
pub fn ctors_mention_block(
    st: &AState,
    fuel: u64,
    ns: &Vec<NIdx>,
    ctors: &Vec<ProjCtorRec>,
) -> Result<bool, CheckError> {
    ctors_mention_block_from(st, fuel, ns, ctors, 0)
}

/// con-leche: ConLeche/Frontend/ProjRec.lean:332-370 projRecOwners
/// Lean twin: `proof/ConRon/Arena/Frontend/ProjRec.lean:425-431
/// ctorsMentionBlock` — the cursor recursion behind `ctors_mention_block`.
pub fn ctors_mention_block_from(
    st: &AState,
    fuel: u64,
    ns: &Vec<NIdx>,
    ctors: &Vec<ProjCtorRec>,
    i: usize,
) -> Result<bool, CheckError> {
    if i >= ctors.len() {
        Ok(false)
    } else {
        match strip_pis_all(st, fuel, &ctors[i].2) {
            Err(e) => Err(e),
            Ok(p) => match doms_mention_any(st, fuel, ns, &p.0) {
                Err(e) => Err(e),
                Ok(true) => Ok(true),
                Ok(false) => ctors_mention_block_from(st, fuel, ns, ctors, i + 1),
            },
        }
    }
}

/// con-leche: ConLeche/Frontend/ProjRec.lean:332-370 projRecOwners
/// Lean twin: `proof/ConRon/Arena/Frontend/ProjRec.lean:435-437 findCtorRec` —
/// `ctors.find? (·.1 == C)`, as an explicit recursion.  Returns the INDEX (the
/// module note's fourth shape: the record stays in place).
pub fn find_ctor_rec(ctors: &Vec<ProjCtorRec>, c: &NIdx) -> Option<usize> {
    find_ctor_rec_from(ctors, c, 0)
}

/// con-leche: ConLeche/Frontend/ProjRec.lean:332-370 projRecOwners
/// Lean twin: `proof/ConRon/Arena/Frontend/ProjRec.lean:435-437 findCtorRec` —
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
/// Lean twin: `proof/ConRon/Arena/Frontend/ProjRec.lean:441-445 findRecRec` —
/// `recs.find? (·.1 == T.str "rec")`, as an explicit recursion.  Returns the
/// INDEX.
pub fn find_rec_rec(recs: &Vec<ProjRecRec>, n: &NIdx) -> Option<usize> {
    find_rec_rec_from(recs, n, 0)
}

/// con-leche: ConLeche/Frontend/ProjRec.lean:332-370 projRecOwners
/// Lean twin: `proof/ConRon/Arena/Frontend/ProjRec.lean:441-445 findRecRec` —
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
/// Lean twin: `proof/ConRon/Arena/Frontend/ProjRec.lean:452-480
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
    st: &mut AState,
    ctors: &Vec<ProjCtorRec>,
    recs: &Vec<ProjRecRec>,
    types: &Vec<ProjTypeRec>,
) -> Result<Vec<ProjRecOwner>, CheckError> {
    proj_rec_candidates_from(st, ctors, recs, types, 0)
}

/// con-leche: ConLeche/Frontend/ProjRec.lean:332-370 projRecOwners
/// Lean twin: `proof/ConRon/Arena/Frontend/ProjRec.lean:452-480
/// projRecCandidates` — the cursor recursion behind `proj_rec_candidates`.
/// The twin computes the TAIL first and conses; so does this, so that the
/// order of the interning the candidate test does is the twin's order.
pub fn proj_rec_candidates_from(
    st: &mut AState,
    ctors: &Vec<ProjCtorRec>,
    recs: &Vec<ProjRecRec>,
    types: &Vec<ProjTypeRec>,
    i: usize,
) -> Result<Vec<ProjRecOwner>, CheckError> {
    if i >= types.len() {
        Ok(Vec::new())
    } else {
        match proj_rec_candidates_from(st, ctors, recs, types, i + 1) {
            Err(e) => Err(e),
            Ok(tail) => match proj_rec_candidate_at(st, ctors, recs, &types[i]) {
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
/// Lean twin: `proof/ConRon/Arena/Frontend/ProjRec.lean:458-477
/// projRecCandidates` — the `filterMap`'s body at ONE type record: one
/// constructor, no indices, a syntactic sort under the parameters, not `Prop`.
pub fn proj_rec_candidate_at(
    st: &mut AState,
    ctors: &Vec<ProjCtorRec>,
    recs: &Vec<ProjRecRec>,
    t: &ProjTypeRec,
) -> Result<Option<ProjRecOwner>, CheckError> {
    if t.5.len() != 1 || t.4 != 0 {
        return Ok(None);
    }
    let body = match expr_ops::strip_pis(st, t.3, &t.2) {
        Err(e) => return Err(e),
        Ok(None) => return Ok(None),
        Ok(Some(b)) => b.1,
    };
    let s = match view(st, &body) {
        Err(e) => return Err(e),
        Ok(ENodeView::Sort(s)) => s,
        Ok(_) => return Ok(None),
    };
    let s_p = match read_level(st, &s) {
        Err(e) => return Err(e),
        Ok(v) => v,
    };
    match level::is_equiv(&s_p, &level::zero()) {
        Some(true) => return Ok(None),
        _ => {}
    }
    proj_rec_candidate_rec(st, ctors, recs, t)
}

/// con-leche: ConLeche/Frontend/ProjRec.lean:332-370 projRecOwners
/// Lean twin: `proof/ConRon/Arena/Frontend/ProjRec.lean:469-477
/// projRecCandidates` — past the sort test: the constructor's record, the
/// recursor `T.rec`, and the elimination level parameter its level list must
/// carry.
pub fn proj_rec_candidate_rec(
    st: &mut AState,
    ctors: &Vec<ProjCtorRec>,
    recs: &Vec<ProjRecRec>,
    t: &ProjTypeRec,
) -> Result<Option<ProjRecOwner>, CheckError> {
    let ci = match find_ctor_rec(ctors, &t.5[0]) {
        None => return Ok(None),
        Some(j) => j,
    };
    let rn = match intern_n_node(st, NNodeView::Str(t.0.dup2(), code_points(&M_REC))) {
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
/// Lean twin: `proof/ConRon/Arena/Frontend/ProjRec.lean:498-517
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
/// Lean twin: `proof/ConRon/Arena/Frontend/ProjRec.lean:508 projRecOwners` —
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
/// Lean twin: `proof/ConRon/Arena/Frontend/ProjRec.lean:515 projRecOwners` —
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
/// Lean twin: `proof/ConRon/Arena/Frontend/ProjRec.lean:498-517
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
    st: &mut AState,
    fuel: u64,
    block: &Vec<crate::arena::env::IConstantInfo>,
    types: &Vec<ProjTypeRec>,
    ctors: &Vec<ProjCtorRec>,
    recs: &Vec<ProjRecRec>,
) -> Result<Vec<ProjRecOwner>, CheckError> {
    match proj_rec_candidates(st, ctors, recs, types) {
        Err(e) => Err(e),
        Ok(owners) => {
            if owners.len() == 0 {
                Ok(Vec::new())
            } else {
                proj_rec_owners_guard(st, fuel, block, types, ctors, owners)
            }
        }
    }
}

/// con-leche: ConLeche/Frontend/ProjRec.lean:332-370 projRecOwners
/// Lean twin: `proof/ConRon/Arena/Frontend/ProjRec.lean:506-517 projRecOwners`
/// — the two recogniser guards, run only when there is a candidate to serve.
pub fn proj_rec_owners_guard(
    st: &mut AState,
    fuel: u64,
    block: &Vec<crate::arena::env::IConstantInfo>,
    types: &Vec<ProjTypeRec>,
    ctors: &Vec<ProjCtorRec>,
    owners: Vec<ProjRecOwner>,
) -> Result<Vec<ProjRecOwner>, CheckError> {
    let block_names = type_names(types);
    let mentions = match ctors_mention_block(st, fuel, &block_names, ctors) {
        Err(e) => return Err(e),
        Ok(v) => v,
    };
    let recursive = any_is_rec(types) || mentions;
    let direct = match struct_parts::struct_parts_core(st, block) {
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
    match native_parts::native_parts(st, declared_num_params(types), block) {
        Err(e) => Err(e),
        Ok(Some(_)) => Ok(Vec::new()),
        Ok(None) => Ok(owners),
    }
}
