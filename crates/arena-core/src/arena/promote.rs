//! `arena::promote` — the scratch → persistent copy (DESIGN.md §8.3, task #97-P6-2).
//!
//! The Rust twin of `proof/ConRon/Arena/Promote.lean`, declaration for
//! declaration, under DESIGN.md §8.6's lockstep ruling.
//!
//! DESIGN.md §8.3, "**Phase A runs in the scratch tier too, with promotion**":
//!
//! > The install phase (annotate the type and the value, infer, defeq) was
//! > interning every intermediate into the persistent tier — on `Init` 5.06 M
//! > permanent nodes on top of the parse's 6.14 M (+82 %) […].  The arena's
//! > answer is con-leche #64's: phase A opens the scratch tier like phase B,
//! > and the two handles it must keep (the annotated type, the annotated
//! > value) are **promoted** — a memoised structural copy scratch →
//! > persistent […] before the tier is dropped.  Persistent handles are
//! > promoted to themselves.
//!
//! This module is that copy, at all four handle kinds and lifted to
//! `arena::env`'s declaration layer, plus `promote_new` — the entry
//! `arena::checker`'s two fold steps call, which promotes a step's NEWLY
//! INSTALLED constants in place.
//!
//! ## What it is
//!
//! `view` the node, promote its children, `intern` the result into the
//! PERSISTENT tier (`arena::store`'s `intern_persistent` family, whose section
//! note carries the WF obligations).  Three properties make it cheap and make
//! it right:
//!
//! * **a persistent handle promotes to itself**, by one tier-bit test
//!   (`is_persistent`) and no store access at all.  Most of an annotated term
//!   IS the parsed term — `annotate` rebuilds only the spine it changes — so
//!   the walk stops at the first persistent node on every branch;
//! * **the memo makes it `O(result)`** and not `O(unfolding)`: the subject is
//!   a hash-consed DAG, and an unmemoised structural copy of a DAG is the
//!   mistake task #97g's item 5 found three times over.  The memo is per
//!   DECLARATION — a scratch handle means nothing once the tier is dropped —
//!   and it is threaded as an argument-and-result pair, a moved
//!   `ron::HashMap` returned, which is `frontend::proj_rec`'s spelling for its
//!   `seen` set and `arena::expr_ops`' for the three memoized scope walks;
//! * **`intern_persistent` probes the persistent cons table first**, so
//!   promoting a node twice is a probe and nothing more, and a node the parse
//!   already interned is found rather than copied.
//!
//! ## What it is NOT
//!
//! It is not a garbage collector and it does not compact: the scratch tier is
//! dropped whole by `core::drop_scratch`, which is what actually reclaims.
//! Promotion only decides what crosses the boundary — exactly the handles the
//! environment keeps, and the phase-A record phase B will check.
//!
//! `denote (promote h) = denote h` is the exactness lemma P3 owes.

use crate::arena::env;
use crate::arena::env::{
    IConstantInfo, IConstantVal, IDeclaration, IFEnv, IIndCaps, IProjTable, IRecRule,
    IRecRuleFire,
};
use crate::arena::checker_split::ValueGroup;
use crate::arena::handle::{EIdx, LIdx, LsIdx, NIdx};
use crate::arena::monad::{
    fail, intern_persistent_e, intern_persistent_l, intern_persistent_ls, intern_persistent_n,
    view, view_l, view_ls, view_n, AState,
};
use crate::arena::store::{ENodeView, LNodeView, NNodeView};
use con_ron_core::kernel::core_types::{code_points, CheckError};
use con_ron_core::kernel::env as cenv;
use con_ron_core::ron::hashmap::{Dup};
// The arena's tables are the epoch-stamped open-addressed map
// (DESIGN.md's `Task #97-P6-4b`), aliased so that every use site below
// reads as it did.  `ron::hashmap::HashMap` is still what `crates/con-ron`
// uses, and is still the one with proofs.
use con_ron_core::ron::hashmap2::HashMap2 as HashMap;

// ---------------------------------------------------------------------------
// The messages of this module's declines
// ---------------------------------------------------------------------------

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `"fuel exhausted: promoteN"`, as code points.
const M_FUEL_PROMOTE_N: [u32; 24] = [
    102, 117, 101, 108, 32, 101, 120, 104, 97, 117, 115, 116, 101, 100, 58, 32, 112, 114, 111,
    109, 111, 116, 101, 78,
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `"fuel exhausted: promoteL"`, as code points.
const M_FUEL_PROMOTE_L: [u32; 24] = [
    102, 117, 101, 108, 32, 101, 120, 104, 97, 117, 115, 116, 101, 100, 58, 32, 112, 114, 111,
    109, 111, 116, 101, 76,
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `"fuel exhausted: promoteE"`, as code points.
const M_FUEL_PROMOTE_E: [u32; 24] = [
    102, 117, 101, 108, 32, 101, 120, 104, 97, 117, 115, 116, 101, 100, 58, 32, 112, 114, 111,
    109, 111, 116, 101, 69,
];

// ---------------------------------------------------------------------------
// The memo (`Promote.lean:56-77`)
// ---------------------------------------------------------------------------

/// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Promote.lean:62-72 PMemo
/// The promotion's memo: the persistent handle each promoted scratch handle
/// was copied to, one table per handle kind.  Threaded as an
/// argument-and-result pair (the module note), fresh at every declaration.
pub struct PMemo {
    /// expression handles
    pub e_m: HashMap<EIdx, EIdx>,
    /// name handles
    pub n_m: HashMap<NIdx, NIdx>,
    /// level handles
    pub l_m: HashMap<LIdx, LIdx>,
    /// universe-argument-list handles
    pub ls_m: HashMap<LsIdx, LsIdx>,
}

/// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Promote.lean:74 PMemo.empty
/// The empty promotion memo, which is what every declaration's promotion
/// starts from.  `HashMap::new` allocates nothing (task #35).
impl PMemo {
    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Promote.lean:74 PMemo.empty
    pub fn empty() -> PMemo {
        PMemo {
            e_m: HashMap::new(),
            n_m: HashMap::new(),
            l_m: HashMap::new(),
            ls_m: HashMap::new(),
        }
    }
}

// ---------------------------------------------------------------------------
// The four handle kinds (`Promote.lean:80-208`)
// ---------------------------------------------------------------------------

/// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Promote.lean:89 promoteN
/// Probe the name memo (extraction rule 5: a `HashMap::get` match that
/// produces a value is its own function; never inlined).
pub fn pmemo_get_n(m: &PMemo, h: &NIdx) -> Option<NIdx> {
    match m.n_m.get(h) {
        Some(r) => Some(r.dup2()),
        None => None,
    }
}

/// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Promote.lean:101 promoteN
/// Record a promoted name, on the owned memo.
pub fn pmemo_set_n(m: PMemo, h: &NIdx, r: &NIdx) -> PMemo {
    let mut m2: PMemo = m;
    m2.n_m.insert(h.dup2(), r.dup2());
    m2
}

/// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Promote.lean:84-101 promoteN
/// **Promote a NAME handle.**  A name's children are names, so the recursion
/// is the prefix chain and the fuel is the store's own bound
/// (`core::CORE_WALK_FUEL`, DESIGN.md §8.4 lesson 7).
pub fn promote_n(
    st: &mut AState,
    m: PMemo,
    fuel: u64,
    h: &NIdx,
) -> Result<(PMemo, NIdx), CheckError> {
    if fuel == 0 {
        fail(CheckError::Internal(code_points(&M_FUEL_PROMOTE_N)))
    } else if h.is_persistent() {
        Ok((m, h.dup2()))
    } else {
        match pmemo_get_n(&m, h) {
            Some(r) => Ok((m, r)),
            None => match view_n(st, h) {
                Err(e) => Err(e),
                Ok(v) => match promote_n_node(st, m, fuel - 1, v) {
                    Err(e) => Err(e),
                    Ok((m2, r)) => {
                        let m3: PMemo = pmemo_set_n(m2, h, &r);
                        Ok((m3, r))
                    }
                },
            },
        }
    }
}

/// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Promote.lean:91-100 promoteN
/// The three name arms, past the probe — split off so the `view`'s loans are
/// dead at the memo's join (extraction rule 5).
pub fn promote_n_node(
    st: &mut AState,
    m: PMemo,
    fuel: u64,
    v: NNodeView,
) -> Result<(PMemo, NIdx), CheckError> {
    match v {
        NNodeView::Anonymous => match intern_persistent_n(st, NNodeView::Anonymous) {
            Err(e) => Err(e),
            Ok(r) => Ok((m, r)),
        },
        NNodeView::Str(p, s) => match promote_n(st, m, fuel, &p) {
            Err(e) => Err(e),
            Ok((m2, p2)) => match intern_persistent_n(st, NNodeView::Str(p2, s)) {
                Err(e) => Err(e),
                Ok(r) => Ok((m2, r)),
            },
        },
        NNodeView::Num(p, n) => match promote_n(st, m, fuel, &p) {
            Err(e) => Err(e),
            Ok((m2, p2)) => match intern_persistent_n(st, NNodeView::Num(p2, n)) {
                Err(e) => Err(e),
                Ok(r) => Ok((m2, r)),
            },
        },
    }
}

/// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Promote.lean:109 promoteL
/// Probe the level memo (extraction rule 5).
pub fn pmemo_get_l(m: &PMemo, h: &LIdx) -> Option<LIdx> {
    match m.l_m.get(h) {
        Some(r) => Some(r.dup2()),
        None => None,
    }
}

/// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Promote.lean:128 promoteL
/// Record a promoted level, on the owned memo.
pub fn pmemo_set_l(m: PMemo, h: &LIdx, r: &LIdx) -> PMemo {
    let mut m2: PMemo = m;
    m2.l_m.insert(h.dup2(), r.dup2());
    m2
}

/// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Promote.lean:104-128 promoteL
/// **Promote a LEVEL handle.**
pub fn promote_l(
    st: &mut AState,
    m: PMemo,
    fuel: u64,
    h: &LIdx,
) -> Result<(PMemo, LIdx), CheckError> {
    if fuel == 0 {
        fail(CheckError::Internal(code_points(&M_FUEL_PROMOTE_L)))
    } else if h.is_persistent() {
        Ok((m, h.dup2()))
    } else {
        match pmemo_get_l(&m, h) {
            Some(r) => Ok((m, r)),
            None => match view_l(st, h) {
                Err(e) => Err(e),
                Ok(v) => match promote_l_node(st, m, fuel - 1, v) {
                    Err(e) => Err(e),
                    Ok((m2, r)) => {
                        let m3: PMemo = pmemo_set_l(m2, h, &r);
                        Ok((m3, r))
                    }
                },
            },
        }
    }
}

/// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Promote.lean:112-127 promoteL
/// The five level arms, past the probe (extraction rule 5).
pub fn promote_l_node(
    st: &mut AState,
    m: PMemo,
    fuel: u64,
    v: LNodeView,
) -> Result<(PMemo, LIdx), CheckError> {
    match v {
        LNodeView::Zero => match intern_persistent_l(st, LNodeView::Zero) {
            Err(e) => Err(e),
            Ok(r) => Ok((m, r)),
        },
        LNodeView::Succ(u) => match promote_l(st, m, fuel, &u) {
            Err(e) => Err(e),
            Ok((m2, u2)) => match intern_persistent_l(st, LNodeView::Succ(u2)) {
                Err(e) => Err(e),
                Ok(r) => Ok((m2, r)),
            },
        },
        LNodeView::Max(u, v2) => match promote_l_two(st, m, fuel, &u, &v2) {
            Err(e) => Err(e),
            Ok((m2, a, b)) => match intern_persistent_l(st, LNodeView::Max(a, b)) {
                Err(e) => Err(e),
                Ok(r) => Ok((m2, r)),
            },
        },
        LNodeView::Imax(u, v2) => match promote_l_two(st, m, fuel, &u, &v2) {
            Err(e) => Err(e),
            Ok((m2, a, b)) => match intern_persistent_l(st, LNodeView::Imax(a, b)) {
                Err(e) => Err(e),
                Ok(r) => Ok((m2, r)),
            },
        },
        LNodeView::Param(n) => match promote_n(st, m, fuel, &n) {
            Err(e) => Err(e),
            Ok((m2, n2)) => match intern_persistent_l(st, LNodeView::Param(n2)) {
                Err(e) => Err(e),
                Ok(r) => Ok((m2, r)),
            },
        },
    }
}

/// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Promote.lean:116-123 promoteL
/// The two-child level arms' pair of promotions, in the twin's order.
pub fn promote_l_two(
    st: &mut AState,
    m: PMemo,
    fuel: u64,
    u: &LIdx,
    v: &LIdx,
) -> Result<(PMemo, LIdx, LIdx), CheckError> {
    match promote_l(st, m, fuel, u) {
        Err(e) => Err(e),
        Ok((m2, a)) => match promote_l(st, m2, fuel, v) {
            Err(e) => Err(e),
            Ok((m3, b)) => Ok((m3, a, b)),
        },
    }
}

/// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Promote.lean:133-138 promoteLList
/// Promote the levels of a universe-argument list.
pub fn promote_l_list(
    st: &mut AState,
    m: PMemo,
    fuel: u64,
    us: &Vec<LIdx>,
) -> Result<(PMemo, Vec<LIdx>), CheckError> {
    promote_l_list_from(st, m, fuel, us, 0, Vec::new())
}

/// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Promote.lean:133-138 promoteLList
/// The cursor recursion the cited `List` recursion becomes (DESIGN.md §3.4).
pub fn promote_l_list_from(
    st: &mut AState,
    m: PMemo,
    fuel: u64,
    us: &Vec<LIdx>,
    i: usize,
    out: Vec<LIdx>,
) -> Result<(PMemo, Vec<LIdx>), CheckError> {
    if i >= us.len() {
        Ok((m, out))
    } else {
        match promote_l(st, m, fuel, &us[i]) {
            Err(e) => Err(e),
            Ok((m2, u)) => {
                let mut o: Vec<LIdx> = out;
                o.push(u);
                promote_l_list_from(st, m2, fuel, us, i + 1, o)
            }
        }
    }
}

/// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Promote.lean:144 promoteLs
/// Probe the level-list memo (extraction rule 5).
pub fn pmemo_get_ls(m: &PMemo, h: &LsIdx) -> Option<LsIdx> {
    match m.ls_m.get(h) {
        Some(r) => Some(r.dup2()),
        None => None,
    }
}

/// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Promote.lean:150 promoteLs
/// Record a promoted level list, on the owned memo.
pub fn pmemo_set_ls(m: PMemo, h: &LsIdx, r: &LsIdx) -> PMemo {
    let mut m2: PMemo = m;
    m2.ls_m.insert(h.dup2(), r.dup2());
    m2
}

/// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Promote.lean:142-151 promoteLs
/// **Promote a universe-argument LIST handle.**  The list node has no fuel
/// clause in the twin: its children are levels and the walk is one level down.
pub fn promote_ls(
    st: &mut AState,
    m: PMemo,
    fuel: u64,
    h: &LsIdx,
) -> Result<(PMemo, LsIdx), CheckError> {
    if h.is_persistent() {
        Ok((m, h.dup2()))
    } else {
        match pmemo_get_ls(&m, h) {
            Some(r) => Ok((m, r)),
            None => match view_ls(st, h) {
                Err(e) => Err(e),
                Ok(us) => match promote_l_list(st, m, fuel, &us) {
                    Err(e) => Err(e),
                    Ok((m2, us2)) => match intern_persistent_ls(st, us2) {
                        Err(e) => Err(e),
                        Ok(r) => {
                            let m3: PMemo = pmemo_set_ls(m2, h, &r);
                            Ok((m3, r))
                        }
                    },
                },
            },
        }
    }
}

/// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Promote.lean:162 promoteE
/// Probe the expression memo (extraction rule 5).
pub fn pmemo_get_e(m: &PMemo, h: &EIdx) -> Option<EIdx> {
    match m.e_m.get(h) {
        Some(r) => Some(r.dup2()),
        None => None,
    }
}

/// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Promote.lean:202 promoteE
/// Record a promoted expression, on the owned memo.
pub fn pmemo_set_e(m: PMemo, h: &EIdx, r: &EIdx) -> PMemo {
    let mut m2: PMemo = m;
    m2.e_m.insert(h.dup2(), r.dup2());
    m2
}

/// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Promote.lean:157-202 promoteE
/// **Promote an EXPRESSION handle**: the structural copy of DESIGN.md §8.3,
/// memoised on the node.  Ten clauses, the store's ten constructors, each
/// promoting its own children first — `BinderMeta` and `Literal` are values
/// and carry no handle (DESIGN.md §8.3), so they cross unchanged.
pub fn promote_e(
    st: &mut AState,
    m: PMemo,
    fuel: u64,
    h: &EIdx,
) -> Result<(PMemo, EIdx), CheckError> {
    if fuel == 0 {
        fail(CheckError::Internal(code_points(&M_FUEL_PROMOTE_E)))
    } else if h.is_persistent() {
        Ok((m, h.dup2()))
    } else {
        match pmemo_get_e(&m, h) {
            Some(r) => Ok((m, r)),
            None => match view(st, h) {
                Err(e) => Err(e),
                Ok(v) => match promote_e_node(st, m, fuel - 1, v) {
                    Err(e) => Err(e),
                    Ok((m2, r)) => {
                        let m3: PMemo = pmemo_set_e(m2, h, &r);
                        Ok((m3, r))
                    }
                },
            },
        }
    }
}

/// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Promote.lean:165-201 promoteE
/// The ten expression arms, past the probe (extraction rule 5).
pub fn promote_e_node(
    st: &mut AState,
    m: PMemo,
    fuel: u64,
    v: ENodeView,
) -> Result<(PMemo, EIdx), CheckError> {
    match v {
        ENodeView::BVar(i) => match intern_persistent_e(st, ENodeView::BVar(i)) {
            Err(e) => Err(e),
            Ok(r) => Ok((m, r)),
        },
        ENodeView::FVar(idx, ty) => match promote_e(st, m, fuel, &ty) {
            Err(e) => Err(e),
            Ok((m2, ty2)) => match intern_persistent_e(st, ENodeView::FVar(idx, ty2)) {
                Err(e) => Err(e),
                Ok(r) => Ok((m2, r)),
            },
        },
        ENodeView::Sort(u) => match promote_l(st, m, fuel, &u) {
            Err(e) => Err(e),
            Ok((m2, u2)) => match intern_persistent_e(st, ENodeView::Sort(u2)) {
                Err(e) => Err(e),
                Ok(r) => Ok((m2, r)),
            },
        },
        ENodeView::Const(n, us) => match promote_n(st, m, fuel, &n) {
            Err(e) => Err(e),
            Ok((m2, n2)) => match promote_ls(st, m2, fuel, &us) {
                Err(e) => Err(e),
                Ok((m3, us2)) => match intern_persistent_e(st, ENodeView::Const(n2, us2)) {
                    Err(e) => Err(e),
                    Ok(r) => Ok((m3, r)),
                },
            },
        },
        ENodeView::App(f, a) => match promote_e_two(st, m, fuel, &f, &a) {
            Err(e) => Err(e),
            Ok((m2, x, y)) => match intern_persistent_e(st, ENodeView::App(x, y)) {
                Err(e) => Err(e),
                Ok(r) => Ok((m2, r)),
            },
        },
        ENodeView::Lam(ty, body, bm) => match promote_e_two(st, m, fuel, &ty, &body) {
            Err(e) => Err(e),
            Ok((m2, x, y)) => match intern_persistent_e(st, ENodeView::Lam(x, y, bm)) {
                Err(e) => Err(e),
                Ok(r) => Ok((m2, r)),
            },
        },
        ENodeView::ForallE(ty, body, bm) => match promote_e_two(st, m, fuel, &ty, &body) {
            Err(e) => Err(e),
            Ok((m2, x, y)) => match intern_persistent_e(st, ENodeView::ForallE(x, y, bm)) {
                Err(e) => Err(e),
                Ok(r) => Ok((m2, r)),
            },
        },
        ENodeView::LetE(ty, val, body) => match promote_e_two(st, m, fuel, &ty, &val) {
            Err(e) => Err(e),
            Ok((m2, x, y)) => match promote_e(st, m2, fuel, &body) {
                Err(e) => Err(e),
                Ok((m3, z)) => match intern_persistent_e(st, ENodeView::LetE(x, y, z)) {
                    Err(e) => Err(e),
                    Ok(r) => Ok((m3, r)),
                },
            },
        },
        ENodeView::Lit(l) => match intern_persistent_e(st, ENodeView::Lit(l)) {
            Err(e) => Err(e),
            Ok(r) => Ok((m, r)),
        },
        ENodeView::Proj(n, i, e) => match promote_n(st, m, fuel, &n) {
            Err(e) => Err(e),
            Ok((m2, n2)) => match promote_e(st, m2, fuel, &e) {
                Err(e) => Err(e),
                Ok((m3, e2)) => match intern_persistent_e(st, ENodeView::Proj(n2, i, e2)) {
                    Err(e) => Err(e),
                    Ok(r) => Ok((m3, r)),
                },
            },
        },
    }
}

/// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Promote.lean:173-194 promoteE
/// The two-child expression arms' pair of promotions, in the twin's order.
pub fn promote_e_two(
    st: &mut AState,
    m: PMemo,
    fuel: u64,
    x: &EIdx,
    y: &EIdx,
) -> Result<(PMemo, EIdx, EIdx), CheckError> {
    match promote_e(st, m, fuel, x) {
        Err(e) => Err(e),
        Ok((m2, a)) => match promote_e(st, m2, fuel, y) {
            Err(e) => Err(e),
            Ok((m3, b)) => Ok((m3, a, b)),
        },
    }
}

// ---------------------------------------------------------------------------
// The lists (`Promote.lean:196-212`)
// ---------------------------------------------------------------------------

/// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Promote.lean:205-210 promoteNList
/// Promote a list of name handles.
pub fn promote_n_list(
    st: &mut AState,
    m: PMemo,
    fuel: u64,
    ns: &Vec<NIdx>,
) -> Result<(PMemo, Vec<NIdx>), CheckError> {
    promote_n_list_from(st, m, fuel, ns, 0, Vec::new())
}

/// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Promote.lean:205-210 promoteNList
/// The cursor recursion behind `promote_n_list` (DESIGN.md §3.4).
pub fn promote_n_list_from(
    st: &mut AState,
    m: PMemo,
    fuel: u64,
    ns: &Vec<NIdx>,
    i: usize,
    out: Vec<NIdx>,
) -> Result<(PMemo, Vec<NIdx>), CheckError> {
    if i >= ns.len() {
        Ok((m, out))
    } else {
        match promote_n(st, m, fuel, &ns[i]) {
            Err(e) => Err(e),
            Ok((m2, n)) => {
                let mut o: Vec<NIdx> = out;
                o.push(n);
                promote_n_list_from(st, m2, fuel, ns, i + 1, o)
            }
        }
    }
}

/// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Promote.lean:214-219 promoteEList
/// Promote a list of expression handles at ONE memo, so a block's sharing
/// survives the copy.
pub fn promote_e_list(
    st: &mut AState,
    m: PMemo,
    fuel: u64,
    es: &Vec<EIdx>,
) -> Result<(PMemo, Vec<EIdx>), CheckError> {
    promote_e_list_from(st, m, fuel, es, 0, Vec::new())
}

/// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Promote.lean:214-219 promoteEList
/// The cursor recursion behind `promote_e_list` (DESIGN.md §3.4).
pub fn promote_e_list_from(
    st: &mut AState,
    m: PMemo,
    fuel: u64,
    es: &Vec<EIdx>,
    i: usize,
    out: Vec<EIdx>,
) -> Result<(PMemo, Vec<EIdx>), CheckError> {
    if i >= es.len() {
        Ok((m, out))
    } else {
        match promote_e(st, m, fuel, &es[i]) {
            Err(e) => Err(e),
            Ok((m2, e)) => {
                let mut o: Vec<EIdx> = out;
                o.push(e);
                promote_e_list_from(st, m2, fuel, es, i + 1, o)
            }
        }
    }
}

// ---------------------------------------------------------------------------
// The declaration layer (`Promote.lean:214-366`)
//
// `arena::env`'s records, field for field: every `EIdx`, `NIdx`, `LIdx` and
// `Vec<LIdx>` in them is promoted, and every `u64`, `bool`,
// `ReducibilityHint`, `PropWhen` and `BinderMeta` crosses unchanged (they
// carry no handle — DESIGN.md §8.7's ruling that (B) imports con-leche's
// representation-free types).  The shape is `frontend::readback`'s intern
// direction in the twin, which walks the same records for the same reason.
// ---------------------------------------------------------------------------

/// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Promote.lean:231-237 promoteCV
/// Promote a `ConstantVal`.
pub fn promote_cv(
    st: &mut AState,
    m: PMemo,
    fuel: u64,
    cv: &IConstantVal,
) -> Result<(PMemo, IConstantVal), CheckError> {
    match promote_n(st, m, fuel, &cv.name) {
        Err(e) => Err(e),
        Ok((m2, n)) => match promote_n_list(st, m2, fuel, &cv.level_params) {
            Err(e) => Err(e),
            Ok((m3, lps)) => match promote_e(st, m3, fuel, &cv.ty) {
                Err(e) => Err(e),
                Ok((m4, ty)) => Ok((
                    m4,
                    IConstantVal {
                        name: n,
                        level_params: lps,
                        ty,
                    },
                )),
            },
        },
    }
}

/// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Promote.lean:239-247 promoteFire
/// Promote a rule's firing mode.
pub fn promote_fire(
    st: &mut AState,
    m: PMemo,
    fuel: u64,
    f: &IRecRuleFire,
) -> Result<(PMemo, IRecRuleFire), CheckError> {
    match f {
        IRecRuleFire::Inert => Ok((m, IRecRuleFire::Inert)),
        IRecRuleFire::Plain => Ok((m, IRecRuleFire::Plain)),
        IRecRuleFire::Nested(lvls, pins) => match promote_l_list(st, m, fuel, lvls) {
            Err(e) => Err(e),
            Ok((m2, ls)) => match promote_e_list(st, m2, fuel, pins) {
                Err(e) => Err(e),
                Ok((m3, ps)) => Ok((m3, IRecRuleFire::Nested(ls, ps))),
            },
        },
    }
}

/// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Promote.lean:249-255 promoteRule
/// Promote one recursor rule.
pub fn promote_rule(
    st: &mut AState,
    m: PMemo,
    fuel: u64,
    rl: &IRecRule,
) -> Result<(PMemo, IRecRule), CheckError> {
    match promote_n(st, m, fuel, &rl.ctor) {
        Err(e) => Err(e),
        Ok((m2, c)) => match promote_fire(st, m2, fuel, &rl.fire) {
            Err(e) => Err(e),
            Ok((m3, f)) => match promote_e(st, m3, fuel, &rl.rhs) {
                Err(e) => Err(e),
                Ok((m4, r)) => Ok((
                    m4,
                    IRecRule {
                        ctor: c,
                        nfields: rl.nfields,
                        ctor_params: rl.ctor_params,
                        fire: f,
                        rhs: r,
                        k: rl.k,
                        eta: rl.eta,
                        params_blind: rl.params_blind,
                    },
                )),
            },
        },
    }
}

/// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Promote.lean:257-263 promoteRules
/// Promote a rule list.
pub fn promote_rules(
    st: &mut AState,
    m: PMemo,
    fuel: u64,
    rs: &Vec<IRecRule>,
) -> Result<(PMemo, Vec<IRecRule>), CheckError> {
    promote_rules_from(st, m, fuel, rs, 0, Vec::new())
}

/// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Promote.lean:257-263 promoteRules
/// The cursor recursion behind `promote_rules` (DESIGN.md §3.4).
pub fn promote_rules_from(
    st: &mut AState,
    m: PMemo,
    fuel: u64,
    rs: &Vec<IRecRule>,
    i: usize,
    out: Vec<IRecRule>,
) -> Result<(PMemo, Vec<IRecRule>), CheckError> {
    if i >= rs.len() {
        Ok((m, out))
    } else {
        match promote_rule(st, m, fuel, &rs[i]) {
            Err(e) => Err(e),
            Ok((m2, r)) => {
                let mut o: Vec<IRecRule> = out;
                o.push(r);
                promote_rules_from(st, m2, fuel, rs, i + 1, o)
            }
        }
    }
}

/// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Promote.lean:268-272 promoteCaps
/// Promote an inductive's capabilities.  `sort_z` is a `PropWhen` over
/// con-leche `Name`s and carries no handle.
pub fn promote_caps(
    st: &mut AState,
    m: PMemo,
    fuel: u64,
    c: &IIndCaps,
) -> Result<(PMemo, IIndCaps), CheckError> {
    match promote_n(st, m, fuel, &c.eta_ctor) {
        Err(e) => Err(e),
        Ok((m2, ct)) => {
            let mut caps: IIndCaps = env::i_ind_caps_dup(c);
            caps.eta_ctor = ct;
            Ok((m2, caps))
        }
    }
}

/// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Promote.lean:276-288 promoteProjTable
/// Promote a projection table, `table_name` included (it is a stored handle,
/// not a recomputed name — `arena::env`'s one added field).
pub fn promote_proj_table(
    st: &mut AState,
    m: PMemo,
    fuel: u64,
    t: &IProjTable,
) -> Result<(PMemo, IProjTable), CheckError> {
    match promote_n(st, m, fuel, &t.struct_name) {
        Err(e) => Err(e),
        Ok((m2, sn)) => match promote_n(st, m2, fuel, &t.table_name) {
            Err(e) => Err(e),
            Ok((m3, tn)) => match promote_n_list(st, m3, fuel, &t.level_params) {
                Err(e) => Err(e),
                Ok((m4, lps)) => promote_proj_table_rest(st, m4, fuel, t, sn, tn, lps),
            },
        },
    }
}

/// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Promote.lean:281-288 promoteProjTable
/// The table's second half — the constructor, the sort, the bodies and the
/// guards — split at the twin's own `let` boundary (task #97-P4c's rule).
#[allow(clippy::too_many_arguments)]
pub fn promote_proj_table_rest(
    st: &mut AState,
    m: PMemo,
    fuel: u64,
    t: &IProjTable,
    sn: NIdx,
    tn: NIdx,
    lps: Vec<NIdx>,
) -> Result<(PMemo, IProjTable), CheckError> {
    match promote_n(st, m, fuel, &t.ctor) {
        Err(e) => Err(e),
        Ok((m2, c)) => match promote_l(st, m2, fuel, &t.struct_sort) {
            Err(e) => Err(e),
            Ok((m3, ss)) => match promote_e_list(st, m3, fuel, &t.bodies) {
                Err(e) => Err(e),
                Ok((m4, bs)) => match promote_l_list(st, m4, fuel, &t.guards) {
                    Err(e) => Err(e),
                    Ok((m5, gs)) => Ok((
                        m5,
                        IProjTable {
                            struct_name: sn,
                            table_name: tn,
                            level_params: lps,
                            num_params: t.num_params,
                            ctor: c,
                            num_fields: t.num_fields,
                            struct_sort: ss,
                            bodies: bs,
                            guards: gs,
                            off: t.off,
                        },
                    )),
                },
            },
        },
    }
}

/// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Promote.lean:290-318 promoteCI
/// **Promote a stored constant** — the seven `IConstantInfo` constructors,
/// which is what "the handles the environment keeps" means.
pub fn promote_ci(
    st: &mut AState,
    m: PMemo,
    fuel: u64,
    ci: &IConstantInfo,
) -> Result<(PMemo, IConstantInfo), CheckError> {
    match ci {
        IConstantInfo::AxiomInfo(v) => match promote_cv(st, m, fuel, v) {
            Err(e) => Err(e),
            Ok((m2, cv)) => Ok((m2, IConstantInfo::AxiomInfo(cv))),
        },
        IConstantInfo::DefnInfo(v, e, h) => match promote_cv(st, m, fuel, v) {
            Err(er) => Err(er),
            Ok((m2, cv)) => match promote_e(st, m2, fuel, e) {
                Err(er) => Err(er),
                Ok((m3, x)) => Ok((
                    m3,
                    IConstantInfo::DefnInfo(cv, x, cenv::reducibility_hint_dup(h)),
                )),
            },
        },
        IConstantInfo::ThmInfo(v, e) => match promote_cv(st, m, fuel, v) {
            Err(er) => Err(er),
            Ok((m2, cv)) => match promote_e(st, m2, fuel, e) {
                Err(er) => Err(er),
                Ok((m3, x)) => Ok((m3, IConstantInfo::ThmInfo(cv, x))),
            },
        },
        IConstantInfo::IndInfo(v, c) => match promote_cv(st, m, fuel, v) {
            Err(e) => Err(e),
            Ok((m2, cv)) => match promote_caps(st, m2, fuel, c) {
                Err(e) => Err(e),
                Ok((m3, caps)) => Ok((m3, IConstantInfo::IndInfo(cv, caps))),
            },
        },
        IConstantInfo::CtorInfo(v, n_p, n_f) => match promote_cv(st, m, fuel, v) {
            Err(e) => Err(e),
            Ok((m2, cv)) => Ok((m2, IConstantInfo::CtorInfo(cv, *n_p, *n_f))),
        },
        IConstantInfo::RecInfo(v, m_i, r_p, rs) => match promote_cv(st, m, fuel, v) {
            Err(e) => Err(e),
            Ok((m2, cv)) => match promote_rules(st, m2, fuel, rs) {
                Err(e) => Err(e),
                Ok((m3, rules)) => Ok((m3, IConstantInfo::RecInfo(cv, *m_i, *r_p, rules))),
            },
        },
        IConstantInfo::ProjInfo(t) => match promote_proj_table(st, m, fuel, t) {
            Err(e) => Err(e),
            Ok((m2, tbl)) => Ok((m2, IConstantInfo::ProjInfo(tbl))),
        },
    }
}

/// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Promote.lean:320-326 promoteCIList
/// Promote a block's constants at ONE memo, so that the sharing between a
/// block's members survives.
pub fn promote_ci_list(
    st: &mut AState,
    m: PMemo,
    fuel: u64,
    cs: &Vec<IConstantInfo>,
) -> Result<(PMemo, Vec<IConstantInfo>), CheckError> {
    promote_ci_list_from(st, m, fuel, cs, 0, Vec::new())
}

/// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Promote.lean:320-326 promoteCIList
/// The cursor recursion behind `promote_ci_list` (DESIGN.md §3.4).
pub fn promote_ci_list_from(
    st: &mut AState,
    m: PMemo,
    fuel: u64,
    cs: &Vec<IConstantInfo>,
    i: usize,
    out: Vec<IConstantInfo>,
) -> Result<(PMemo, Vec<IConstantInfo>), CheckError> {
    if i >= cs.len() {
        Ok((m, out))
    } else {
        match promote_ci(st, m, fuel, &cs[i]) {
            Err(e) => Err(e),
            Ok((m2, c)) => {
                let mut o: Vec<IConstantInfo> = out;
                o.push(c);
                promote_ci_list_from(st, m2, fuel, cs, i + 1, o)
            }
        }
    }
}

/// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Promote.lean:332-358 promoteDecl
/// Promote a declaration record.  Not on the fold's path — the records arrive
/// from the parse and are persistent — and written because the layer is
/// twinned whole (the twin's `Frontend/Readback.lean` has the same seven
/// clauses for the intern direction).
pub fn promote_decl(
    st: &mut AState,
    m: PMemo,
    fuel: u64,
    d: &IDeclaration,
) -> Result<(PMemo, IDeclaration), CheckError> {
    match d {
        IDeclaration::AxiomDecl(v) => match promote_cv(st, m, fuel, v) {
            Err(e) => Err(e),
            Ok((m2, cv)) => Ok((m2, IDeclaration::AxiomDecl(cv))),
        },
        IDeclaration::DefnDecl(v, e, h) => match promote_cv(st, m, fuel, v) {
            Err(er) => Err(er),
            Ok((m2, cv)) => match promote_e(st, m2, fuel, e) {
                Err(er) => Err(er),
                Ok((m3, x)) => Ok((
                    m3,
                    IDeclaration::DefnDecl(cv, x, cenv::reducibility_hint_dup(h)),
                )),
            },
        },
        IDeclaration::ThmDecl(v, e) => match promote_cv(st, m, fuel, v) {
            Err(er) => Err(er),
            Ok((m2, cv)) => match promote_e(st, m2, fuel, e) {
                Err(er) => Err(er),
                Ok((m3, x)) => Ok((m3, IDeclaration::ThmDecl(cv, x))),
            },
        },
        IDeclaration::OpaqueDecl(v, e) => match promote_cv(st, m, fuel, v) {
            Err(er) => Err(er),
            Ok((m2, cv)) => match promote_e(st, m2, fuel, e) {
                Err(er) => Err(er),
                Ok((m3, x)) => Ok((m3, IDeclaration::OpaqueDecl(cv, x))),
            },
        },
        IDeclaration::BasisDecl(k) => Ok((m, IDeclaration::BasisDecl(cenv::basis_kind_dup(k)))),
        IDeclaration::IndDecl(block, n_p) => match promote_ci_list(st, m, fuel, block) {
            Err(e) => Err(e),
            Ok((m2, b)) => Ok((m2, IDeclaration::IndDecl(b, *n_p))),
        },
        IDeclaration::QuotDecl(k, v) => match promote_cv(st, m, fuel, v) {
            Err(e) => Err(e),
            Ok((m2, cv)) => Ok((m2, IDeclaration::QuotDecl(cenv::quot_kind_dup(k), cv))),
        },
    }
}

/// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Promote.lean:361-367 promoteVG
/// Promote the datum that crosses the install/check seam
/// (`arena::checker_split`'s `ValueGroup`).  An `opaque`'s value is NOT in the
/// environment — only the pending record holds it — so the seam is promoted
/// beside the environment and at the SAME memo, so that the sharing between a
/// header's type and its value survives the copy.
pub fn promote_vg(
    st: &mut AState,
    m: PMemo,
    fuel: u64,
    g: ValueGroup,
) -> Result<(PMemo, ValueGroup), CheckError> {
    match promote_cv(st, m, fuel, &g.cv_a) {
        Err(e) => Err(e),
        Ok((m2, cv_a)) => match promote_e(st, m2, fuel, &g.jv) {
            Err(e) => Err(e),
            Ok((m3, jv)) => Ok((
                m3,
                ValueGroup {
                    kind: g.kind,
                    cv_a,
                    jv,
                },
            )),
        },
    }
}

// ---------------------------------------------------------------------------
// The fold's entry: a step's newly installed constants
// (`Promote.lean:368-410`)
// ---------------------------------------------------------------------------

/// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Promote.lean:375-379 eraseInstalled
/// Forget the index rows of the constants a step installed — `consts[i..]`,
/// which over this `Vec`'s oldest-first order is the twin's `consts.take k`
/// over its newest-first list.
///
/// They are keyed by the constant's name HANDLE, which promotion may MOVE (a
/// name first interned inside the scratch tier is a scratch handle), and a
/// stale row under a scratch key is not merely useless: `drop_scratch` hands
/// that word back to the next declaration, and `ifenv_find` would answer a
/// different constant under it.
pub fn erase_installed(fe: IFEnv, i: usize) -> IFEnv {
    if i >= fe.env.consts.len() {
        fe
    } else {
        let mut fe2: IFEnv = fe;
        let n: NIdx = env::i_constant_info_name(&fe2.env.consts[i]);
        fe2.idx.remove(&n);
        erase_installed(fe2, i + 1)
    }
}

/// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Promote.lean:383-387 indexPromoted
/// Lean twin: `proof/ConRon/Arena/Promote.lean:399-409 promoteNew`
/// Promote the constants of slots `start..j` and re-index them at the
/// installation counters they were pushed with, walking DOWN — the twin's list
/// is newest-first and its counters run down from `c`, which over this `Vec`
/// is the slot order from the top.  The promoted record is written back into
/// its own slot: the Aeneas subset cannot move an element out of an owned
/// `Vec` (`arena::env`'s note), and rebuilding the list would copy the whole
/// environment at every declaration.
pub fn index_promoted(
    st: &mut AState,
    m: PMemo,
    fuel: u64,
    fe: IFEnv,
    start: usize,
    j: usize,
    c: u64,
) -> Result<(PMemo, IFEnv), CheckError> {
    if j <= start {
        Ok((m, fe))
    } else {
        match promote_ci(st, m, fuel, &fe.env.consts[j - 1]) {
            Err(e) => Err(e),
            Ok((m2, ci)) => {
                let mut fe2: IFEnv = fe;
                // The index row is the SLOT (task #97-P6-5's lever 1), so the
                // re-index is the slot the promoted record is written into and
                // the two stay in step without a second copy.
                fe2.idx
                    .insert(env::i_constant_info_name(&ci), (c - 1, (j - 1) as u64));
                fe2.env.consts[j - 1] = ci;
                index_promoted(st, m2, fuel, fe2, start, j - 1, c - 1)
            }
        }
    }
}

/// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Promote.lean:399-409 promoteNew
/// **The phase-A bracket's promotion half**: the `k` constants the step just
/// installed, copied into the persistent tier and re-indexed, everything below
/// them untouched.
///
/// `k` is `fe.visible_below - n0` for the counter `n0` read BEFORE the step:
/// every install route grows the environment by `ifenv_push` alone
/// (`arena::checker`, `arena::decl_check`, `arena::inductives::*`), so the `k`
/// newest entries are exactly the step's, and the provisional
/// self-environments the recursor installs build (`provision_recs`'s `fe_self`,
/// `check_native_rec`'s `fe_r`) are discarded by their own callers and never
/// reach here.
pub fn promote_new(
    st: &mut AState,
    m: PMemo,
    fuel: u64,
    k: u64,
    fe: IFEnv,
) -> Result<(PMemo, IFEnv), CheckError> {
    if k == 0 {
        Ok((m, fe))
    } else {
        let n: usize = fe.env.consts.len();
        let kk: usize = k as usize;
        if kk > n {
            Ok((m, fe))
        } else {
            let vb: u64 = fe.visible_below;
            let start: usize = n - kk;
            let fe2: IFEnv = erase_installed(fe, start);
            index_promoted(st, m, fuel, fe2, start, n, vb)
        }
    }
}

// ---------------------------------------------------------------------------
// Tests: the promotion's own properties
// ---------------------------------------------------------------------------
//
// `proof/ConRon/Arena/CheckerTest.lean`'s thirty-two promotion `#guard`s — the
// twenty `chkDecls` and the twelve `chkInstall`, each comparing the DENOTED
// environment of the bracketed fold with con-leche's — are `arena::checker`'s
// `mod tests`, where they were already written against the two folds and now
// run through the bracket (`check_decls_pure_agrees_*`, `install_then_check_*`).
//
// What is here is what those cannot see, because a readback cannot tell one
// tier from another: that the handles leaving a bracket are PERSISTENT, that a
// promoted node IS the persistent hash-consed twin of its scratch original
// (handle equality, which over an injective `denote` is term equality), that
// the memo makes a second promotion free, and that `promote_new` repairs the
// index rather than leaving a row under a scratch key.

#[cfg(test)]
mod tests {
    use super::*;
    use crate::arena::core::{drop_scratch, enter_scratch, CORE_WALK_FUEL};
    use crate::arena::env::{i_env_empty, ifenv_find, ifenv_push, mk_ifenv, IEnv};
    use crate::arena::monad::{intern_e, intern_l_node, intern_ls_node, intern_n_node};
    use crate::arena::store::EStore;
    use con_ron_core::kernel::expr::Literal;
    use con_ron_core::ron::hashmap::Eq2;
    use con_ron_core::ron::nat;
    use con_ron_core::ron::ptr::P;

    fn ok<T>(r: Result<T, CheckError>) -> T {
        match r {
            Ok(x) => x,
            Err(_) => panic!("the fixture must not decline"),
        }
    }

    /// A name `anonymous.str s`, interned in whatever tier is live.
    fn nm(st: &mut AState, s: &str) -> NIdx {
        let a = ok(intern_n_node(st, NNodeView::Anonymous));
        ok(intern_n_node(
            st,
            NNodeView::Str(a, s.chars().map(|c| c as u32).collect()),
        ))
    }

    /// `const s []`, interned in whatever tier is live.
    fn cst(st: &mut AState, s: &str) -> EIdx {
        let n = nm(st, s);
        let us = ok(intern_ls_node(st, Vec::new()));
        ok(intern_e(st, ENodeView::Const(n, us)))
    }

    /// A persistent handle promotes to ITSELF, by one tier-bit test and no
    /// store access at all — the property that makes the copy cheap (the
    /// module note's first bullet).
    #[test]
    fn a_persistent_handle_promotes_to_itself() {
        let mut st = AState::init(EStore::empty());
        let f = cst(&mut st, "f");
        let before = st.store.pers_count();
        enter_scratch(&mut st);
        let (m, r) = ok(promote_e(&mut st, PMemo::empty(), CORE_WALK_FUEL, &f));
        assert!(r.eq2(&f), "a persistent handle is its own promotion");
        assert_eq!(st.store.pers_count(), before, "and nothing was appended");
        assert_eq!(m.e_m.len(), 0, "nor was the memo touched");
        drop_scratch(&mut st);
    }

    /// A node BUILT in the scratch tier out of persistent children promotes to
    /// the persistent hash-consed twin of itself: the handle the persistent
    /// tier hands out for the same view once the scratch tier is gone.  Handle
    /// equality is term equality (`denoteE` is injective, DESIGN.md §8.3), so
    /// this is `denote (promote h) = denote h` observed from outside.
    #[test]
    fn a_scratch_node_promotes_to_its_persistent_twin() {
        let mut st = AState::init(EStore::empty());
        let f = cst(&mut st, "f");
        let a = cst(&mut st, "a");
        enter_scratch(&mut st);
        let app = ok(intern_e(&mut st, ENodeView::App(f.dup2(), a.dup2())));
        assert!(!app.is_persistent(), "the fixture must be a scratch node");
        let (m, r) = ok(promote_e(&mut st, PMemo::empty(), CORE_WALK_FUEL, &app));
        assert!(r.is_persistent(), "the promotion is persistent");
        assert!(!r.eq2(&app), "and it is a different word");
        assert_eq!(m.e_m.len(), 1, "one node was copied");
        // the memo answers the second promotion without appending
        let n1 = st.store.pers_count();
        let (_, r2) = ok(promote_e(&mut st, m, CORE_WALK_FUEL, &app));
        assert!(r2.eq2(&r), "the memo answers the second promotion");
        assert_eq!(st.store.pers_count(), n1, "and appends nothing");
        drop_scratch(&mut st);
        let again = ok(intern_e(&mut st, ENodeView::App(f, a)));
        assert!(
            again.eq2(&r),
            "the promoted handle IS what the persistent tier hands out"
        );
    }

    /// The four kinds, and the nesting: a scratch name under a scratch level
    /// under a scratch `sort` promotes whole, every handle in the result
    /// persistent.
    #[test]
    fn the_four_kinds_promote_through_the_nesting() {
        let mut st = AState::init(EStore::empty());
        enter_scratch(&mut st);
        let u = nm(&mut st, "u");
        let p = ok(intern_l_node(&mut st, LNodeView::Param(u)));
        let s = ok(intern_e(&mut st, ENodeView::Sort(p.dup2())));
        let lit = ok(intern_e(
            &mut st,
            ENodeView::Lit(Literal::NatVal(P::new(nat::from_u64(7)))),
        ));
        let pair = ok(intern_e(&mut st, ENodeView::App(s.dup2(), lit)));
        assert!(!pair.is_persistent());
        let (m, r) = ok(promote_e(&mut st, PMemo::empty(), CORE_WALK_FUEL, &pair));
        assert!(r.is_persistent(), "the application");
        assert_eq!(m.e_m.len(), 3, "three expression nodes were copied");
        assert_eq!(m.l_m.len(), 1, "one level node");
        assert_eq!(m.n_m.len(), 2, "two name nodes (`anonymous` and `u`)");
        let (_, rl) = ok(promote_l(&mut st, PMemo::empty(), CORE_WALK_FUEL, &p));
        assert!(rl.is_persistent(), "the level promotes on its own too");
        drop_scratch(&mut st);
    }

    /// `promote_new` promotes the `k` newest constants and REPAIRS the index:
    /// the row under the old (scratch) name handle is gone and the promoted
    /// constant is found under the promoted one, at the counter it was pushed
    /// with.  A stale row would be worse than useless — `drop_scratch` hands
    /// that word to the next declaration.
    #[test]
    fn promote_new_repairs_the_index() {
        let mut st = AState::init(EStore::empty());
        let fe0: IFEnv = mk_ifenv(i_env_empty());
        enter_scratch(&mut st);
        // a constant whose NAME is new, so the name handle is a scratch one
        let n = nm(&mut st, "brandNew");
        assert!(!n.is_persistent(), "the fixture's name must be scratch");
        let ty = cst(&mut st, "T");
        let fe1: IFEnv = ifenv_push(
            fe0,
            IConstantInfo::AxiomInfo(IConstantVal {
                name: n.dup2(),
                level_params: Vec::new(),
                ty,
            }),
        );
        assert!(ifenv_find(&fe1, &n).is_some(), "found under the scratch key");
        let (_, fe2) = ok(promote_new(&mut st, PMemo::empty(), CORE_WALK_FUEL, 1, fe1));
        assert_eq!(fe2.env.consts.len(), 1);
        assert_eq!(fe2.visible_below, 1);
        let n2: NIdx = env::i_constant_info_name(&fe2.env.consts[0]);
        assert!(n2.is_persistent(), "the stored name is persistent now");
        assert!(!n2.eq2(&n), "and it moved");
        assert!(ifenv_find(&fe2, &n2).is_some(), "found under the new key");
        assert!(
            ifenv_find(&fe2, &n).is_none(),
            "and the stale scratch row is gone"
        );
        match &fe2.env.consts[0] {
            IConstantInfo::AxiomInfo(cv) => {
                assert!(cv.ty.is_persistent(), "the type is persistent too")
            }
            _ => panic!("the fixture is an axiom"),
        }
        drop_scratch(&mut st);
    }

    /// `k = 0` is the identity, which is the bracket's own fast path for a
    /// record that installs nothing.
    #[test]
    fn promote_new_at_zero_is_the_identity() {
        let mut st = AState::init(EStore::empty());
        let fe: IFEnv = mk_ifenv(IEnv { consts: Vec::new() });
        let before = st.store.pers_count();
        let (_, fe2) = ok(promote_new(&mut st, PMemo::empty(), CORE_WALK_FUEL, 0, fe));
        assert_eq!(fe2.env.consts.len(), 0);
        assert_eq!(st.store.pers_count(), before);
    }
}
