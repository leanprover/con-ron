//! `ConLeche/Driver/Reach.lean` — a worker's context: the reach of a module,
//! its completion, the capture check (task #166).
//!
//! Phase 4 and 6 of a worker at module `M`: the context `M`'s own records are
//! checked against, as a list of records, and its validation.  Upstream's module
//! docstring states the rules; this module ports its executed code:
//!
//! * **The reach** (`reach_go`): a worklist over names from the names `M`'s own
//!   records read.  A name the name index holds is read at its first copy and
//!   becomes its presented record (`read_record`): a definition with its value,
//!   every other definition, theorem and opaque constant as the axiom of its
//!   statement (the opaque cut), an inductive group whole from its home's
//!   private part (`group_at`).
//! * **The completion** of a name the index lacks: located in the reader's view
//!   (`view_of`, `locate`) and read from its module's private part.
//! * **The capture check** (`capture_one`), **the stored names** (`stored_names_ok`),
//!   **the clash rule** (`clash_agree`), **the read order** (`read_order`),
//!   **the validation** (`validate_ctx`) and **the inferred flags**
//!   (`infer_flags`).
//!
//! ## Deviations
//!
//! * **The state.**  Upstream threads its `ReachCache` through every call and
//!   returns it beside an `Except`; here it is `&mut`, and a failure leaves it as
//!   it stands (every failure propagates out of `reach`, which drops the cache).
//!   Upstream's reads `rd` are `fs, pk, pers, st, sp` (`st.store` is the
//!   reader's `EStore`).  A part's region is kept with the files it was cut from
//!   (`PartRead`): con-ron's region is offsets into bytes held apart.
//! * **Tables, lookups, views and recursor blocks are read in place.**  Upstream's
//!   `tableOf`/`lookOf`/`viewOf`/`recBlocksOf` return the cached map; here each
//!   makes sure it is cached and returns nothing, and its reader looks it up
//!   (`table_get`, `ReachCache::looks`, `views`, `rec_blocks`): the maps are
//!   whole modules' names, and a copy per lookup would be the cost of the reach.
//! * **The inferred flags run after the freeze** (`infer_flags`): con-ron's
//!   kernel reads its environment from the frozen tier (`pers.env`), which the
//!   worker builds over `ctx ++ own` after the reach.  The statements to infer
//!   are returned in `Reach::pending`; the view of the first record storing a
//!   statement's name is upstream's `ctxPart` (the context records are the
//!   index's first ones; the ground hoist moves own records only).  Only the
//!   order in which a module failing two checks reports them differs.
//! * The worklist's stack is a vector with its height (`ReachLog::sp`): the
//!   Aeneas subset has no `pop`.  Upstream's `List.mapM`/`foldl`/`filter` over
//!   a record's names are loops, each loop its own function with every
//!   hash-map lookup in a helper outside the loop body.

use crate::arena::checker_base::{all_level_params_defined, consts_resolve_f_fast};
use crate::arena::core::{
    enter_record, ensure_sort_core, infer_type_core, leave_record, lift_fueled, lit_shape_ok, lvl_eq, zero_level,
    CHECK_FUEL, CORE_WALK_FUEL,
};
use crate::arena::env;
use crate::arena::env::{IConstantInfo, IConstantVal, IDeclaration, IProjTable, IRecRule, IRecRuleFire};
use crate::arena::expr_ops;
use crate::arena::handle::{EIdx, LIdx, NIdx, ETAG_CONST};
use crate::arena::inductives::stream_recs::stream_nested_ok;
use crate::arena::install::{decl_constants, decl_tables};
use crate::arena::justify::decl_label;
use crate::arena::monad::{read_level_m, read_names, view_const_name, AState};
use crate::arena::needs::{needs_const, needs_expr, needs_st_empty, needs_table, NeedsSt};
use crate::arena::pins::pin_sorry_ax;
use crate::arena::store::PersTier;
use crate::arena::stream_index::stream_index_view;
use crate::arena::trust_axioms::reduce_op_names;
use crate::frontend::olean::files;
use crate::frontend::olean::files::OleanFs;
use crate::frontend::olean::group;
use crate::frontend::olean::index;
use crate::frontend::olean::index::{Clash, WorkerReads};
use crate::frontend::olean::lazy::CEntry;
use crate::frontend::olean::levels;
use crate::frontend::olean::levels::HeaderLoads;
use crate::frontend::olean::merge::Merged;
use crate::frontend::olean::present;
use crate::frontend::olean::reads;
use crate::frontend::olean::reads::{NamePosition, NamePositions};
use crate::frontend::olean::region::Region;
use crate::frontend::olean::sparse;
use crate::frontend::olean::sparse::SM;
use crate::frontend::olean::spec::{CEntryF, CKindF, OleanPins, RdErr, StmtRec};
use crate::frontend::olean::view;
use crate::frontend::olean::view::{ModFiles, OLeanLevel, ViewBytes};
use crate::frontend::text;
use crate::kernel::core_types;
use crate::kernel::core_types::CheckError;
use crate::kernel::env::CheckMode;
use crate::kernel::level;
use crate::kernel::name;
use crate::ron::hashmap::{Dup, Eq2, Hashable};
use crate::ron::hashmap2::HashMap2;

// ---------------------------------------------------------------------------
// What a record reads
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Driver/Reach.lean:91-95 recordReads
/// The constants' laws' names, in order.
pub fn record_reads_consts(pers: &PersTier, st: &mut AState, x: NeedsSt, cs: &Vec<IConstantInfo>) -> Result<NeedsSt, CheckError> {
    let mut x = x;
    let mut i = 0usize;
    while i < cs.len() {
        match needs_const(pers, st, x, &cs[i]) {
            Err(e) => return Err(e),
            Ok(x2) => x = x2,
        }
        i += 1;
    }
    Ok(x)
}

/// con-leche: ConLeche/Driver/Reach.lean:91-95 recordReads
/// The tables' names, in order.
pub fn record_reads_tables(pers: &PersTier, st: &mut AState, x: NeedsSt, ts: &Vec<IProjTable>) -> Result<NeedsSt, CheckError> {
    let mut x = x;
    let mut i = 0usize;
    while i < ts.len() {
        match needs_table(pers, st, x, &ts[i]) {
            Err(e) => return Err(e),
            Ok(x2) => x = x2,
        }
        i += 1;
    }
    Ok(x)
}

/// con-leche: ConLeche/Driver/Reach.lean:91-95 recordReads
/// **What a record reads**: its constants' laws' names and its tables', each
/// expression's DAG walked once.
pub fn record_reads(pers: &PersTier, st: &mut AState, d: &IDeclaration) -> Result<Vec<NIdx>, CheckError> {
    let cs = match decl_constants(pers, st, d) {
        Err(e) => return Err(e),
        Ok(cs) => cs,
    };
    let ts = match decl_tables(pers, st, d) {
        Err(e) => return Err(e),
        Ok(ts) => ts,
    };
    match record_reads_consts(pers, st, needs_st_empty(), &cs) {
        Err(e) => Err(e),
        Ok(x) => match record_reads_tables(pers, st, x, &ts) {
            Err(e) => Err(e),
            Ok(x2) => Ok(x2.acc),
        },
    }
}

/// con-leche: ConLeche/Modular.lean:95-96 declNames
/// **The names a record installs**: its constants' names.
pub fn decl_names(pers: &PersTier, st: &mut AState, d: &IDeclaration) -> Result<Vec<NIdx>, CheckError> {
    match decl_constants(pers, st, d) {
        Err(e) => Err(e),
        Ok(cs) => {
            let mut out: Vec<NIdx> = Vec::with_capacity(cs.len());
            let mut i = 0usize;
            while i < cs.len() {
                out.push(env::i_constant_info_name(&cs[i]));
                i += 1;
            }
            Ok(out)
        }
    }
}

// ---------------------------------------------------------------------------
// The validation of a record
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Driver/Reach.lean:105-108 exprOk
/// **An expression's syntactic clauses**: no free variable, no loose bound
/// variable at or past `k`, every level parameter among `lps`.
pub fn expr_ok(pers: &PersTier, st: &mut AState, lps: &Vec<NIdx>, k: u64, e: &EIdx) -> Result<bool, CheckError> {
    match expr_ops::has_fvar_fast(pers, st, CORE_WALK_FUEL, e) {
        Err(er) => Err(er),
        Ok(true) => Ok(false),
        Ok(false) => match expr_ops::loose_bvars_bounded_fast(pers, st, CORE_WALK_FUEL, k, e) {
            Err(er) => Err(er),
            Ok(false) => Ok(false),
            Ok(true) => all_level_params_defined(pers, st, lps, e),
        },
    }
}

/// con-leche: ConLeche/Driver/Reach.lean:110-123 nestedOk
/// `lvls.all (·.allParamsDefined lps)`, at the parameters read back.
pub fn levels_defined(pers: &PersTier, st: &mut AState, ps: &Vec<name::Name>, lvls: &Vec<LIdx>) -> Result<bool, CheckError> {
    let mut i = 0usize;
    while i < lvls.len() {
        match read_level_m(pers, st, &lvls[i]) {
            Err(e) => return Err(e),
            Ok(u) => {
                if !level::all_params_defined(ps, &u) {
                    return Ok(false);
                }
            }
        }
        i += 1;
    }
    Ok(true)
}

/// con-leche: ConLeche/Driver/Reach.lean:110-123 nestedOk
/// `es.all (exprOk lps k)`.
pub fn exprs_ok(pers: &PersTier, st: &mut AState, lps: &Vec<NIdx>, k: u64, es: &Vec<EIdx>) -> Result<bool, CheckError> {
    let mut i = 0usize;
    while i < es.len() {
        match expr_ok(pers, st, lps, k, &es[i]) {
            Err(e) => return Err(e),
            Ok(false) => return Ok(false),
            Ok(true) => {}
        }
        i += 1;
    }
    Ok(true)
}

/// con-leche: ConLeche/Driver/Reach.lean:110-123 nestedOk
/// **A nested rule's datum reads off its recursor's type**: the major's domain
/// is the class's inductive at the rule's levels, applied to the pins lifted
/// past the index binders and then to the index variables (the kernel's
/// `stream_nested_ok`, which is that match).
pub fn nested_ok(pers: &PersTier, st: &mut AState, lps: &Vec<NIdx>, ty: &EIdx, m_i: u64, r_p: u64, fire: &IRecRuleFire) -> Result<bool, CheckError> {
    match fire {
        IRecRuleFire::Nested(lvls, pins) => {
            if !(r_p <= m_i) {
                return Ok(false);
            }
            let ps = match read_names(pers, st, lps) {
                Err(e) => return Err(e),
                Ok(ps) => ps,
            };
            match levels_defined(pers, st, &ps, lvls) {
                Err(e) => return Err(e),
                Ok(false) => return Ok(false),
                Ok(true) => {}
            }
            match exprs_ok(pers, st, lps, r_p, pins) {
                Err(e) => return Err(e),
                Ok(false) => return Ok(false),
                Ok(true) => {}
            }
            stream_nested_ok(pers, st, ty, m_i, r_p, fire)
        }
        _ => Ok(true),
    }
}

/// con-leche: ConLeche/Driver/Reach.lean:125-131 ruleOk
/// A recursor rule's clauses: its right-hand side, what it binds, and its datum
/// if nested.
pub fn rule_ok(pers: &PersTier, st: &mut AState, lps: &Vec<NIdx>, ty: &EIdx, m_i: u64, r_p: u64, r: &IRecRule) -> Result<bool, CheckError> {
    match expr_ok(pers, st, lps, 0, &r.rhs) {
        Err(e) => return Err(e),
        Ok(false) => return Ok(false),
        Ok(true) => {}
    }
    if !(r_p <= m_i) {
        return Ok(false);
    }
    let n = match r_p.checked_add(r.nfields) {
        None => return Ok(false),
        Some(n) => n,
    };
    match expr_ops::strip_lams(pers, st, n, &r.rhs) {
        Err(e) => return Err(e),
        Ok(None) => return Ok(false),
        Ok(Some(_)) => {}
    }
    nested_ok(pers, st, lps, ty, m_i, r_p, &r.fire)
}

/// con-leche: ConLeche/Driver/Reach.lean:140-148 constOk
/// `rules.all (ruleOk lps ty mI rP)`.
pub fn rules_ok(pers: &PersTier, st: &mut AState, lps: &Vec<NIdx>, ty: &EIdx, m_i: u64, r_p: u64, rules: &Vec<IRecRule>) -> Result<bool, CheckError> {
    let mut i = 0usize;
    while i < rules.len() {
        match rule_ok(pers, st, lps, ty, m_i, r_p, &rules[i]) {
            Err(e) => return Err(e),
            Ok(false) => return Ok(false),
            Ok(true) => {}
        }
        i += 1;
    }
    Ok(true)
}

/// con-leche: ConLeche/Driver/Reach.lean:133-138 ctorHeadOk
/// **A constructor's stored family is the one its type concludes in**.
pub fn ctor_head_ok(pers: &PersTier, st: &mut AState, cv: &IConstantVal, induct: &NIdx) -> Result<bool, CheckError> {
    match expr_ops::pi_result(pers, st, CORE_WALK_FUEL, &cv.ty) {
        Err(e) => Err(e),
        Ok(b) => match expr_ops::get_app_fn(pers, st, CORE_WALK_FUEL, &b) {
            Err(e) => Err(e),
            Ok(hd) => {
                if hd.tag() == ETAG_CONST {
                    match view_const_name(pers, st, &hd) {
                        None => Ok(false),
                        Some(t) => Ok(t.eq2(induct)),
                    }
                } else {
                    Ok(false)
                }
            }
        },
    }
}

/// con-leche: ConLeche/Driver/Reach.lean:140-148 constOk
/// **A constant's syntactic clauses**: its type; a definition's value; a
/// recursor's rules; a constructor's family.
pub fn const_ok(pers: &PersTier, st: &mut AState, c: &IConstantInfo) -> Result<bool, CheckError> {
    match c {
        IConstantInfo::DefnInfo(cv, v, _) => match expr_ok(pers, st, &cv.level_params, 0, &cv.ty) {
            Err(e) => Err(e),
            Ok(false) => Ok(false),
            Ok(true) => expr_ok(pers, st, &cv.level_params, 0, v),
        },
        IConstantInfo::RecInfo(cv, m_i, r_p, _, rules) => match expr_ok(pers, st, &cv.level_params, 0, &cv.ty) {
            Err(e) => Err(e),
            Ok(false) => Ok(false),
            Ok(true) => rules_ok(pers, st, &cv.level_params, &cv.ty, *m_i, *r_p, rules),
        },
        IConstantInfo::CtorInfo(cv, _, _, induct) => match expr_ok(pers, st, &cv.level_params, 0, &cv.ty) {
            Err(e) => Err(e),
            Ok(false) => Ok(false),
            Ok(true) => ctor_head_ok(pers, st, cv, induct),
        },
        IConstantInfo::AxiomInfo(cv) => expr_ok(pers, st, &cv.level_params, 0, &cv.ty),
        IConstantInfo::ThmInfo(cv) => expr_ok(pers, st, &cv.level_params, 0, &cv.ty),
        IConstantInfo::IndInfo(cv, _) => expr_ok(pers, st, &cv.level_params, 0, &cv.ty),
    }
}

/// con-leche: ConLeche/Driver/Reach.lean:150-153 tableOk
/// **A table's syntactic clauses**: one body per field, each scoped at the
/// parameters and the subject.
pub fn table_ok(pers: &PersTier, st: &mut AState, t: &IProjTable) -> Result<bool, CheckError> {
    if t.bodies.len() as u64 != t.num_fields {
        return Ok(false);
    }
    match t.num_params.checked_add(1) {
        None => Ok(false),
        Some(k) => exprs_ok(pers, st, &t.level_params, k, &t.bodies),
    }
}

/// con-leche: ConLeche/Driver/Reach.lean:155-158 recordOk
/// `(declConstants d).all (fun c => constOk c && litShapeOk c)`.
pub fn consts_ok(pers: &PersTier, st: &mut AState, cs: &Vec<IConstantInfo>) -> Result<bool, CheckError> {
    let mut i = 0usize;
    while i < cs.len() {
        match const_ok(pers, st, &cs[i]) {
            Err(e) => return Err(e),
            Ok(false) => return Ok(false),
            Ok(true) => {}
        }
        match lit_shape_ok(pers, st, &cs[i]) {
            Err(e) => return Err(e),
            Ok(false) => return Ok(false),
            Ok(true) => {}
        }
        i += 1;
    }
    Ok(true)
}

/// con-leche: ConLeche/Driver/Reach.lean:155-158 recordOk
/// `(declTables d).all tableOk`.
pub fn tables_ok(pers: &PersTier, st: &mut AState, ts: &Vec<IProjTable>) -> Result<bool, CheckError> {
    let mut i = 0usize;
    while i < ts.len() {
        match table_ok(pers, st, &ts[i]) {
            Err(e) => return Err(e),
            Ok(false) => return Ok(false),
            Ok(true) => {}
        }
        i += 1;
    }
    Ok(true)
}

/// con-leche: ConLeche/Driver/Reach.lean:155-158 recordOk
/// **A record validated**: every constant it installs and every table, with the
/// shape a literal's name asks.
pub fn record_ok(pers: &PersTier, st: &mut AState, d: &IDeclaration) -> Result<bool, CheckError> {
    match decl_constants(pers, st, d) {
        Err(e) => Err(e),
        Ok(cs) => match consts_ok(pers, st, &cs) {
            Err(e) => Err(e),
            Ok(false) => Ok(false),
            Ok(true) => match decl_tables(pers, st, d) {
                Err(e) => Err(e),
                Ok(ts) => tables_ok(pers, st, &ts),
            },
        },
    }
}

// ---------------------------------------------------------------------------
// The reach's reads
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Driver/Reach.lean:164-168 PartKey
/// **A part of a view**: a module and a level.
pub struct PartKey {
    pub module: NIdx,
    pub level: OLeanLevel,
}

/// con-leche: ConLeche/Driver/Reach.lean:164-168 PartKey
/// `OLeanLevel`'s derived `Hashable`'s word: the constructor's index.
pub fn level_index(l: &OLeanLevel) -> u64 {
    match l {
        OLeanLevel::Exported => 0,
        OLeanLevel::Server => 1,
        OLeanLevel::Private => 2,
    }
}

/// con-leche: ConLeche/Driver/Reach.lean:164-168 PartKey
/// A level, copied.
pub fn level_dup(l: &OLeanLevel) -> OLeanLevel {
    match l {
        OLeanLevel::Exported => OLeanLevel::Exported,
        OLeanLevel::Server => OLeanLevel::Server,
        OLeanLevel::Private => OLeanLevel::Private,
    }
}

/// con-leche: ConLeche/Driver/Reach.lean:164-168 PartKey
/// The derived `Hashable`: `mixHash` over the fields.
impl Hashable for PartKey {
    /// con-leche: ConLeche/Driver/Reach.lean:164-168 PartKey
    fn hash64(&self) -> u64 {
        name::mix_hash(self.module.hash64(), name::nat_hash(level_index(&self.level)))
    }
}

/// con-leche: ConLeche/Driver/Reach.lean:164-168 PartKey
/// The derived `BEq`.
impl Eq2 for PartKey {
    /// con-leche: ConLeche/Driver/Reach.lean:164-168 PartKey
    fn eq2(&self, other: &PartKey) -> bool {
        self.module.eq2(&other.module) && level_index(&self.level) == level_index(&other.level)
    }
}

/// con-leche: ConLeche/Driver/Reach.lean:164-168 PartKey
/// A part key, copied.
impl Dup for PartKey {
    /// con-leche: ConLeche/Driver/Reach.lean:164-168 PartKey
    fn dup2(&self) -> PartKey {
        PartKey { module: self.module.dup2(), level: level_dup(&self.level) }
    }
}

/// con-leche: ConLeche/Driver/Reach.lean:164-168 PartKey
/// The key of a module's private part.
pub fn priv_key(m: &NIdx) -> PartKey {
    PartKey { module: m.dup2(), level: OLeanLevel::Private }
}

/// con-leche: ConLeche/Driver/Reach.lean:170-173 Spot
/// **A copy of a name**: the part holding it and its name position there.
pub struct Spot {
    pub part: PartKey,
    pub pos: NamePosition,
}

/// con-leche: ConLeche/Frontend/Olean/Reads.lean:55-63 NamePosition
/// A name position, copied.
pub fn name_position_dup(q: &NamePosition) -> NamePosition {
    NamePosition { loc: q.loc, name: q.name.dup2(), tag: q.tag, skipped: q.skipped }
}

/// con-leche: ConLeche/Driver/Reach.lean:170-173 Spot
/// A spot, copied.
pub fn spot_dup(s: &Spot) -> Spot {
    Spot { part: s.part.dup2(), pos: name_position_dup(&s.pos) }
}

/// con-leche: ConLeche/Driver/Reach.lean:175-186 ReachEnv
/// What the reach reads its records with, fixed for the run: the module whose
/// context it is and every copy of each clashing name with its module and
/// statement.  Upstream's `wr` and `own` are parameters of their own beside it
/// (a structure holding references nests borrows, which Aeneas does not
/// join at a loop).
pub struct ReachEnv {
    pub module: NIdx,
    pub copies: HashMap2<NIdx, Vec<(NIdx, StmtRec)>>,
}

/// con-leche: ConLeche/Driver/Reach.lean:188-212 ReachCache
/// A part's files, its view's bytes and region, and its memo (upstream's
/// `Region × SM`; the region's bytes are `view::view_bytes(files, vb)`).
pub struct PartRead {
    pub files: ModFiles,
    pub vb: ViewBytes,
    pub region: Region,
    pub memo: SM,
}

/// con-leche: ConLeche/Driver/Reach.lean:188-212 ReachCache
/// **The reach's caches**: what it has read of the files.
pub struct ReachCache {
    /// name tables of parts read so far (beside the index's)
    pub tables: HashMap2<PartKey, NamePositions>,
    /// name lookups of parts read from
    pub looks: HashMap2<PartKey, HashMap2<NIdx, NamePosition>>,
    /// regions and memos of parts read from
    pub parts: HashMap2<PartKey, PartRead>,
    /// per part, its recursors' locations by their block's first member
    pub rec_blocks: HashMap2<PartKey, HashMap2<NIdx, Vec<u64>>>,
    /// a home's view, for the searches
    pub views: HashMap2<NIdx, HashMap2<NIdx, Spot>>,
    /// the completions: each name's located copy, at its module's private part
    pub located: HashMap2<NIdx, Spot>,
    /// the completed names, each with the home whose view located it
    pub completed: Vec<(NIdx, NIdx)>,
    /// statements whose being a proposition decides an agreement
    pub pending: Vec<(Vec<u32>, NIdx, StmtRec)>,
    /// the names of a proof pair's statement, each with the home that reads it
    pub partners: Vec<(NIdx, NIdx)>,
    /// how many reads were looked for in their reader's view
    pub searches: u64,
}

/// con-leche: ConLeche/Driver/Reach.lean:188-212 ReachCache
/// The empty caches (upstream's `{}`).
pub fn reach_cache_empty() -> ReachCache {
    ReachCache {
        tables: HashMap2::new(),
        looks: HashMap2::new(),
        parts: HashMap2::new(),
        rec_blocks: HashMap2::new(),
        views: HashMap2::new(),
        located: HashMap2::new(),
        completed: Vec::new(),
        pending: Vec::new(),
        partners: Vec::new(),
        searches: 0,
    }
}

/// con-leche: ConLeche/Driver/Reach.lean:214-217 viewKeys
/// **The parts of module `h`'s view**, in order: `h`'s own private part, then
/// the parts its header fixpoint `ld` loads, in its order.
pub fn view_keys(h: &NIdx, ld: &HeaderLoads) -> Vec<PartKey> {
    let mut out: Vec<PartKey> = Vec::with_capacity(ld.order.len() + 1);
    out.push(priv_key(h));
    let mut i = 0usize;
    while i < ld.order.len() && i < ld.flags.len() {
        out.push(PartKey { module: ld.order[i].dup2(), level: levels::load_flags_level(&ld.flags[i]) });
        i += 1;
    }
    out
}

/// con-leche: ConLeche/Driver/Reach.lean:219-223 viewStep
/// **One part's names into a view**, the first copy of each name kept.
pub fn view_step(v: &mut HashMap2<NIdx, Spot>, k: &PartKey, t: &NamePositions) {
    let mut i = 0usize;
    while i < t.consts.len() {
        if !v.contains_key(&t.consts[i].name) {
            v.insert(t.consts[i].name.dup2(), Spot { part: k.dup2(), pos: name_position_dup(&t.consts[i]) });
        }
        i += 1;
    }
}

// ---------------------------------------------------------------------------
// The parts
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Driver/Reach.lean:230-248 tableOf
/// The index's table of a part: where the module is loaded at that level.
pub fn index_table<'a>(wr: &'a WorkerReads, k: &PartKey) -> Option<&'a NamePositions> {
    match wr.loads.index.get(&k.module) {
        None => None,
        Some(i) => {
            if level_index(&index::header_loads_level_at(&wr.loads, *i)) == level_index(&k.level) {
                let j = *i as usize;
                if j < wr.index.parts.len() {
                    Some(&wr.index.parts[j])
                } else {
                    None
                }
            } else {
                None
            }
        }
    }
}

/// con-leche: ConLeche/Driver/Reach.lean:230-248 tableOf
/// **A part's name table, where it is**: read so far, else the index's.
pub fn table_get<'a>(wr: &'a WorkerReads, c: &'a ReachCache, k: &PartKey) -> Option<&'a NamePositions> {
    match c.tables.get(k) {
        Some(t) => Some(t),
        None => index_table(wr, k),
    }
}

/// con-leche: none — an internal failure: a cache entry the reach just made
/// sure of is not there
pub fn cache_lost() -> CheckError {
    core_types::internal({ const M: [u32; 29] = [116, 104, 101, 32, 114, 101, 97, 99, 104, 32, 108, 111, 115, 116, 32, 97, 32, 99, 97, 99, 104, 101, 100, 32, 116, 97, 98, 108, 101]; core_types::code_points(&M) })
}

/// con-leche: ConLeche/Driver/Reach.lean:230-248 tableOf
/// **A part's name table**: the index's where the module is loaded at that
/// level, else read once (`table_get` reads it).
pub fn table_of<F: OleanFs>(fs: &F, pk: &OleanPins, pers: &PersTier, st: &mut AState, sp: &files::Roots, wr: &WorkerReads, c: &mut ReachCache, k: &PartKey) -> Result<(), CheckError> {
    if c.tables.contains_key(k) {
        return Ok(());
    }
    if index_table(wr, k).is_some() {
        return Ok(());
    }
    match files::read_part_names(fs, pk, pers, &mut st.store, sp, &k.module, &k.level) {
        Err(e) => Err(e),
        Ok(t) => {
            c.tables.insert(k.dup2(), t);
            Ok(())
        }
    }
}

/// con-leche: ConLeche/Driver/Reach.lean:250-261 lookOf
/// A table's lookup: each name's position, the last copy of a name kept.
pub fn look_build(t: &NamePositions) -> HashMap2<NIdx, NamePosition> {
    let mut l: HashMap2<NIdx, NamePosition> = HashMap2::with_capacity(t.consts.len());
    let mut i = 0usize;
    while i < t.consts.len() {
        l.insert(t.consts[i].name.dup2(), name_position_dup(&t.consts[i]));
        i += 1;
    }
    l
}

/// con-leche: ConLeche/Driver/Reach.lean:250-261 lookOf
/// **A part's name lookup**, built once (`ReachCache::looks` holds it).
pub fn look_of<F: OleanFs>(fs: &F, pk: &OleanPins, pers: &PersTier, st: &mut AState, sp: &files::Roots, wr: &WorkerReads, c: &mut ReachCache, k: &PartKey) -> Result<(), CheckError> {
    if c.looks.contains_key(k) {
        return Ok(());
    }
    match table_of(fs, pk, pers, st, sp, wr, c, k) {
        Err(e) => return Err(e),
        Ok(()) => {}
    }
    let l = match table_get(wr, c, k) {
        None => return Err(cache_lost()),
        Some(t) => look_build(t),
    };
    c.looks.insert(k.dup2(), l);
    Ok(())
}

/// con-leche: ConLeche/Driver/Reach.lean:250-261 lookOf
/// A name's position in a part's cached lookup.
pub fn look_at(c: &ReachCache, k: &PartKey, n: &NIdx) -> Result<Option<NamePosition>, CheckError> {
    match c.looks.get(k) {
        None => Err(cache_lost()),
        Some(l) => match l.get(n) {
            None => Ok(None),
            Some(q) => Ok(Some(name_position_dup(q))),
        },
    }
}

/// con-leche: ConLeche/Driver/Reach.lean:263-283 withPart
/// **A part taken out of the caches for a read** (upstream's `withPart` up to
/// the read): its files read once, its region cut, an empty memo.
pub fn take_part<F: OleanFs>(fs: &F, pk: &OleanPins, pers: &PersTier, st: &mut AState, sp: &files::Roots, c: &mut ReachCache, k: &PartKey) -> Result<PartRead, CheckError> {
    match c.parts.remove(k) {
        Some(p) => Ok(p),
        None => match files::read_files(fs, pers, &st.store, sp, &k.module, &k.level) {
            Err(e) => Err(e),
            Ok(f) => match view::mod_files_view_region(&f, &k.level) {
                None => Err(view::view_error(pk, pers, &mut st.store, &k.module, &f, &k.level)),
                Some((vb, _)) => {
                    let r = view::view_region_of(&f, &vb);
                    Ok(PartRead { files: f, vb, region: r, memo: sparse::sm_empty() })
                }
            },
        },
    }
}

/// con-leche: ConLeche/Driver/Reach.lean:263-283 withPart
/// **A part put back after a read**: with its memo where the read went
/// through; with an empty memo, and the failure, where it did not.
pub fn put_part<T>(pers: &PersTier, st: &AState, c: &mut ReachCache, k: &PartKey, p: PartRead, r: Result<T, RdErr>) -> Result<T, CheckError> {
    match r {
        Ok(a) => {
            c.parts.insert(k.dup2(), p);
            Ok(a)
        }
        Err(RdErr::Err(e)) => Err(e),
        Err(RdErr::Bad) => {
            let mut p = p;
            p.memo = sparse::sm_empty();
            c.parts.insert(k.dup2(), p);
            Err(view::undecodable(pers, &st.store, &k.module))
        }
    }
}

/// con-leche: ConLeche/Driver/Reach.lean:285-302 loadPart
/// **A part's region and name table off one read of its files**: the region
/// kept with an empty memo, the table the region's, kept where none is yet.
/// Nothing is read where the region is kept already.
pub fn load_part<F: OleanFs>(fs: &F, pk: &OleanPins, pers: &PersTier, st: &mut AState, sp: &files::Roots, c: &mut ReachCache, k: &PartKey) -> Result<(), CheckError> {
    if c.parts.contains_key(k) {
        return Ok(());
    }
    let f = match files::read_files(fs, pers, &st.store, sp, &k.module, &k.level) {
        Err(e) => return Err(e),
        Ok(f) => f,
    };
    match view::mod_files_view_region(&f, &k.level) {
        None => Err(view::view_error(pk, pers, &mut st.store, &k.module, &f, &k.level)),
        Some((vb, a)) => {
            let r = view::view_region_of(&f, &vb);
            if c.tables.contains_key(k) {
                c.parts.insert(k.dup2(), PartRead { files: f, vb, region: r, memo: sparse::sm_empty() });
                return Ok(());
            }
            match reads::name_positions_at(pk, pers, &mut st.store, view::view_bytes(&f, &vb), &r, a) {
                Err(RdErr::Err(e)) => Err(e),
                Err(RdErr::Bad) => Err(view::view_error(pk, pers, &mut st.store, &k.module, &f, &k.level)),
                Ok(t) => {
                    c.parts.insert(k.dup2(), PartRead { files: f, vb, region: r, memo: sparse::sm_empty() });
                    c.tables.insert(k.dup2(), t);
                    Ok(())
                }
            }
        }
    }
}

/// con-leche: ConLeche/Driver/Reach.lean:304-310 entriesWith
/// Several constants with one memo (`entryWith`, in order).
pub fn entries_with(pk: &OleanPins, pers: &PersTier, st: &mut AState, bs: &[u8], r: &Region, m: &mut SM, ls: &Vec<u64>) -> Result<Vec<CEntryF<NIdx, EIdx>>, RdErr> {
    let mut out: Vec<CEntryF<NIdx, EIdx>> = Vec::with_capacity(ls.len());
    let mut i = 0usize;
    while i < ls.len() {
        match present::entry_with(pk, pers, &mut st.store, bs, r, m, ls[i]) {
            Err(e) => return Err(e),
            Ok(e) => out.push(e),
        }
        i += 1;
    }
    Ok(out)
}

/// con-leche: ConLeche/Driver/Reach.lean:263-283 withPart
/// `withPart env c k fun r st => entryWith r st l`.
pub fn part_entry<F: OleanFs>(fs: &F, pk: &OleanPins, pers: &PersTier, st: &mut AState, sp: &files::Roots, c: &mut ReachCache, k: &PartKey, l: u64) -> Result<CEntryF<NIdx, EIdx>, CheckError> {
    let mut p = match take_part(fs, pk, pers, st, sp, c, k) {
        Err(e) => return Err(e),
        Ok(p) => p,
    };
    let r = present::entry_with(pk, pers, &mut st.store, view::view_bytes(&p.files, &p.vb), &p.region, &mut p.memo, l);
    put_part(pers, st, c, k, p, r)
}

/// con-leche: ConLeche/Driver/Reach.lean:263-283 withPart
/// `withPart env c k fun r st => entriesWith r st ls`.
pub fn part_entries<F: OleanFs>(fs: &F, pk: &OleanPins, pers: &PersTier, st: &mut AState, sp: &files::Roots, c: &mut ReachCache, k: &PartKey, ls: &Vec<u64>) -> Result<Vec<CEntryF<NIdx, EIdx>>, CheckError> {
    let mut p = match take_part(fs, pk, pers, st, sp, c, k) {
        Err(e) => return Err(e),
        Ok(p) => p,
    };
    let r = entries_with(pk, pers, st, view::view_bytes(&p.files, &p.vb), &p.region, &mut p.memo, ls);
    put_part(pers, st, c, k, p, r)
}

/// con-leche: ConLeche/Driver/Reach.lean:312-315 stmtAt
/// **A copy's statement and kind** (the kind's expressions left out).
pub fn stmt_at<F: OleanFs>(fs: &F, pk: &OleanPins, pers: &PersTier, st: &mut AState, sp: &files::Roots, c: &mut ReachCache, s: &Spot) -> Result<(StmtRec, CKindF<NIdx, ()>), CheckError> {
    let mut p = match take_part(fs, pk, pers, st, sp, c, &s.part) {
        Err(e) => return Err(e),
        Ok(p) => p,
    };
    let r = present::stmt_with(pk, pers, &mut st.store, view::view_bytes(&p.files, &p.vb), &p.region, &mut p.memo, s.pos.loc);
    put_part(pers, st, c, &s.part, p, r)
}

/// con-leche: ConLeche/Driver/Reach.lean:317-329 privSpot
/// **A copy in a module's private part**: itself, or the private part's
/// constant of its name.
pub fn priv_spot<F: OleanFs>(fs: &F, pk: &OleanPins, pers: &PersTier, st: &mut AState, sp: &files::Roots, wr: &WorkerReads, c: &mut ReachCache, s: &Spot) -> Result<Spot, CheckError> {
    if level_index(&s.part.level) == 2 {
        return Ok(spot_dup(s));
    }
    let k = priv_key(&s.part.module);
    match look_of(fs, pk, pers, st, sp, wr, c, &k) {
        Err(e) => return Err(e),
        Ok(()) => {}
    }
    match look_at(c, &k, &s.pos.name) {
        Err(e) => Err(e),
        Ok(Some(q)) => Ok(Spot { part: k, pos: q }),
        Ok(None) => {
            let t = text::cat({ const M: [u32; 7] = [109, 111, 100, 117, 108, 101, 32]; core_types::code_points(&M) }, &view::name_text(pers, &st.store, &s.part.module));
            let t = text::cat(t, &{ const M: [u32; 26] = [58, 32, 105, 116, 115, 32, 101, 120, 112, 111, 114, 116, 101, 100, 32, 112, 97, 114, 116, 32, 104, 111, 108, 100, 115, 32]; core_types::code_points(&M) });
            let t = text::cat(t, &view::name_text(pers, &st.store, &s.pos.name));
            Err(core_types::invalid(text::cat(t, &{ const M: [u32; 27] = [44, 32, 105, 116, 115, 32, 112, 114, 105, 118, 97, 116, 101, 32, 112, 97, 114, 116, 32, 100, 111, 101, 115, 32, 110, 111, 116]; core_types::code_points(&M) })))
        }
    }
}

// ---------------------------------------------------------------------------
// A home's view, and a search in it
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Driver/Reach.lean:333-341 viewAdd
/// One part's names into a view.
pub fn view_add_one<F: OleanFs>(fs: &F, pk: &OleanPins, pers: &PersTier, st: &mut AState, sp: &files::Roots, wr: &WorkerReads, c: &mut ReachCache, v: &mut HashMap2<NIdx, Spot>, k: &PartKey) -> Result<(), CheckError> {
    match table_of(fs, pk, pers, st, sp, wr, c, k) {
        Err(e) => return Err(e),
        Ok(()) => {}
    }
    match table_get(wr, c, k) {
        None => Err(cache_lost()),
        Some(t) => {
            view_step(v, k, t);
            Ok(())
        }
    }
}

/// con-leche: ConLeche/Driver/Reach.lean:333-341 viewAdd
/// The names of some parts into a view, the first copy kept.
pub fn view_add<F: OleanFs>(fs: &F, pk: &OleanPins, pers: &PersTier, st: &mut AState, sp: &files::Roots, wr: &WorkerReads, c: &mut ReachCache, v: &mut HashMap2<NIdx, Spot>, ks: &Vec<PartKey>) -> Result<(), CheckError> {
    let mut i = 0usize;
    while i < ks.len() {
        match view_add_one(fs, pk, pers, st, sp, wr, c, v, &ks[i]) {
            Err(e) => return Err(e),
            Ok(()) => {}
        }
        i += 1;
    }
    Ok(())
}

/// con-leche: ConLeche/Driver/Reach.lean:343-358 viewOf
/// The header fixpoint of module `h`'s own private part.
pub fn home_loads<F: OleanFs>(fs: &F, pk: &OleanPins, pers: &PersTier, st: &mut AState, sp: &files::Roots, wr: &WorkerReads, c: &ReachCache, k: &PartKey) -> Result<HeaderLoads, CheckError> {
    match table_get(wr, c, k) {
        None => Err(cache_lost()),
        Some(own) => levels::header_fixpoint(fs, pk, pers, &mut st.store, sp, own.header.is_module, &own.header.imports),
    }
}

/// con-leche: ConLeche/Driver/Reach.lean:343-358 viewOf
/// **Module `h`'s view, by name**: `h`'s own private part, then the parts
/// `h`'s header fixpoint loads, in its order, the first copy of each name.
/// Built once per home (`ReachCache::views` holds it).
pub fn view_of<F: OleanFs>(fs: &F, pk: &OleanPins, pers: &PersTier, st: &mut AState, sp: &files::Roots, wr: &WorkerReads, c: &mut ReachCache, h: &NIdx) -> Result<(), CheckError> {
    if c.views.contains_key(h) {
        return Ok(());
    }
    let k = priv_key(h);
    match table_of(fs, pk, pers, st, sp, wr, c, &k) {
        Err(e) => return Err(e),
        Ok(()) => {}
    }
    let ld = match home_loads(fs, pk, pers, st, sp, wr, c, &k) {
        Err(e) => return Err(e),
        Ok(ld) => ld,
    };
    let mut v: HashMap2<NIdx, Spot> = HashMap2::new();
    match view_add(fs, pk, pers, st, sp, wr, c, &mut v, &view_keys(h, &ld)) {
        Err(e) => return Err(e),
        Ok(()) => {}
    }
    c.views.insert(h.dup2(), v);
    Ok(())
}

/// con-leche: ConLeche/Driver/Reach.lean:360-365 locate
/// A name in a home's cached view.
pub fn view_at(c: &ReachCache, h: &NIdx, y: &NIdx) -> Result<Option<Spot>, CheckError> {
    match c.views.get(h) {
        None => Err(cache_lost()),
        Some(v) => match v.get(y) {
            None => Ok(None),
            Some(s) => Ok(Some(spot_dup(s))),
        },
    }
}

/// con-leche: ConLeche/Driver/Reach.lean:360-365 locate
/// **`y` located in `h`'s view.**
pub fn locate<F: OleanFs>(fs: &F, pk: &OleanPins, pers: &PersTier, st: &mut AState, sp: &files::Roots, wr: &WorkerReads, c: &mut ReachCache, h: &NIdx, y: &NIdx) -> Result<Option<Spot>, CheckError> {
    match view_of(fs, pk, pers, st, sp, wr, c, h) {
        Err(e) => return Err(e),
        Ok(()) => {}
    }
    c.searches += 1;
    view_at(c, h, y)
}

/// con-leche: ConLeche/Driver/Reach.lean:367-373 importerSpot
/// **The importer's copy of a loaded name**: its module's position in the load
/// order and the copy.
pub fn importer_spot(pk: &OleanPins, wr: &WorkerReads, y: &NIdx) -> Option<(u64, Spot)> {
    match wr.index.first.get(y) {
        None => None,
        Some(cp) => match index::name_index_at(&wr.index, cp) {
            None => None,
            Some(q) => {
                                let part = PartKey { module: index::header_loads_name_at(pk, &wr.loads, cp.module), level: index::header_loads_level_at(&wr.loads, cp.module) };
                Some((cp.module, Spot { part, pos: name_position_dup(q) }))
            }
        },
    }
}

// ---------------------------------------------------------------------------
// Agreement
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Driver/Reach.lean:377-383 ProofStatus
/// **Is a copy a proof**: `yes`, `no`, or decided by inferring that its
/// statement is a proposition.
pub enum ProofStatus {
    Yes,
    No,
    Infer,
}

/// con-leche: ConLeche/Driver/Reach.lean:385-403 proofStatus
/// **A copy's proof flag**: a theorem is a proof; a definition, opaque
/// constant or axiom is one if its type is a proposition; an exported axiom is
/// what its home's private part declares there.
pub fn proof_status<F: OleanFs>(fs: &F, pk: &OleanPins, pers: &PersTier, st: &mut AState, sp: &files::Roots, wr: &WorkerReads, c: &mut ReachCache, s: &Spot, k: &CKindF<NIdx, ()>) -> Result<ProofStatus, CheckError> {
    match k {
        CKindF::Thm(_, _) => Ok(ProofStatus::Yes),
        CKindF::Defn(_, _, _) => Ok(ProofStatus::Infer),
        CKindF::Opaq(_, _) => Ok(ProofStatus::Infer),
        CKindF::Ax(_) => {
            if level_index(&s.part.level) == 2 {
                return Ok(ProofStatus::Infer);
            }
            match priv_spot(fs, pk, pers, st, sp, wr, c, s) {
                Err(e) => Err(e),
                Ok(p) => {
                    if p.pos.tag == 2 {
                        Ok(ProofStatus::Yes)
                    } else if p.pos.tag == 0 || p.pos.tag == 1 || p.pos.tag == 3 {
                        Ok(ProofStatus::Infer)
                    } else {
                        Ok(ProofStatus::No)
                    }
                }
            }
        }
        _ => Ok(ProofStatus::No),
    }
}

/// con-leche: ConLeche/Driver/Reach.lean:405-407 partnerReads
/// The names a statement reads, each paired with a home, onto `acc`.
pub fn partner_reads(pers: &PersTier, st: &mut AState, acc: &mut Vec<(NIdx, NIdx)>, h: &NIdx, ty: &EIdx) -> Result<(), CheckError> {
    match needs_expr(pers, st, needs_st_empty(), ty) {
        Err(e) => Err(e),
        Ok(x) => {
            let mut i = 0usize;
            while i < x.acc.len() {
                acc.push((h.dup2(), x.acc[i].dup2()));
                i += 1;
            }
            Ok(())
        }
    }
}

/// con-leche: ConLeche/Driver/Reach.lean:409-441 agreeCheck
/// `s!"name capture at {y}, read by module {h}"`.
pub fn capture_what(pers: &PersTier, st: &AState, h: &NIdx, y: &NIdx) -> Vec<u32> {
    let t = text::cat({ const M: [u32; 16] = [110, 97, 109, 101, 32, 99, 97, 112, 116, 117, 114, 101, 32, 97, 116, 32]; core_types::code_points(&M) }, &view::name_text(pers, &st.store, y));
    let t = text::cat(t, &{ const M: [u32; 17] = [44, 32, 114, 101, 97, 100, 32, 98, 121, 32, 109, 111, 100, 117, 108, 101, 32]; core_types::code_points(&M) });
    text::cat(t, &view::name_text(pers, &st.store, h))
}

/// con-leche: ConLeche/Driver/Reach.lean:409-441 agreeCheck
/// The copies of `y` of two modules are not one constant.
pub fn agree_bad(pers: &PersTier, st: &AState, h: &NIdx, y: &NIdx, m1: &NIdx, m2: &NIdx) -> CheckError {
    let t = text::cat(capture_what(pers, st, h, y), &{ const M: [u32; 16] = [58, 32, 116, 104, 101, 32, 99, 111, 112, 105, 101, 115, 32, 111, 102, 32]; core_types::code_points(&M) });
    let t = text::cat(t, &view::name_text(pers, &st.store, y));
    let t = text::cat(t, &{ const M: [u32; 12] = [32, 111, 102, 32, 109, 111, 100, 117, 108, 101, 115, 32]; core_types::code_points(&M) });
    let t = text::cat(t, &view::name_text(pers, &st.store, m1));
    let t = text::cat(t, &{ const M: [u32; 5] = [32, 97, 110, 100, 32]; core_types::code_points(&M) });
    let t = text::cat(t, &view::name_text(pers, &st.store, m2));
    core_types::invalid(text::cat(t, &{ const M: [u32; 55] = [32, 97, 114, 101, 32, 110, 111, 116, 32, 111, 110, 101, 32, 99, 111, 110, 115, 116, 97, 110, 116, 32, 40, 110, 111, 116, 32, 116, 119, 111, 32, 112, 114, 111, 111, 102, 115, 32, 111, 102, 32, 111, 110, 101, 32, 115, 116, 97, 116, 101, 109, 101, 110, 116, 41]; core_types::code_points(&M) }))
}

/// con-leche: ConLeche/Driver/Reach.lean:409-441 agreeCheck
/// Whether a status is `no`, `yes`.
pub fn status_is(p: &ProofStatus, yes: bool) -> bool {
    match p {
        ProofStatus::Yes => yes,
        ProofStatus::No => !yes,
        ProofStatus::Infer => false,
    }
}

/// con-leche: ConLeche/Driver/Reach.lean:409-441 agreeCheck
/// **Two copies of `y` agree**, the context's `s1` and `s2` of home `h`'s
/// view: one module, or both proofs of one statement (one of them a theorem,
/// or else an inference recorded with the statement), whose names `s2`'s
/// module reads as the context does (recorded in `partners`).  The copy `h`
/// reads is not unsafe or partial.
pub fn agree_check<F: OleanFs>(fs: &F, pk: &OleanPins, pers: &PersTier, st: &mut AState, sp: &files::Roots, wr: &WorkerReads, c: &mut ReachCache, h: &NIdx, y: &NIdx, s1: &Spot, s2: &Spot) -> Result<(), CheckError> {
    if s1.part.module.eq2(&s2.part.module) {
        return Ok(());
    }
    if s2.pos.skipped {
        let t = text::cat(capture_what(pers, st, h, y), &{ const M: [u32; 14] = [58, 32, 105, 116, 115, 32, 99, 111, 112, 121, 32, 111, 102, 32]; core_types::code_points(&M) });
        let t = text::cat(t, &view::name_text(pers, &st.store, y));
        let t = text::cat(t, &{ const M: [u32; 12] = [44, 32, 111, 102, 32, 109, 111, 100, 117, 108, 101, 32]; core_types::code_points(&M) });
        let t = text::cat(t, &view::name_text(pers, &st.store, &s2.part.module));
        return Err(core_types::invalid(text::cat(t, &{ const M: [u32; 22] = [44, 32, 105, 115, 32, 117, 110, 115, 97, 102, 101, 32, 111, 114, 32, 112, 97, 114, 116, 105, 97, 108]; core_types::code_points(&M) })));
    }
    let (cv1, k1) = match stmt_at(fs, pk, pers, st, sp, c, s1) {
        Err(e) => return Err(e),
        Ok(p) => p,
    };
    let (cv2, k2) = match stmt_at(fs, pk, pers, st, sp, c, s2) {
        Err(e) => return Err(e),
        Ok(p) => p,
    };
    if !(crate::frontend::olean::module::nidx_list_eq(&cv1.level_params, &cv2.level_params) && cv1.ty.eq2(&cv2.ty)) {
        return Err(agree_bad(pers, st, h, y, &s1.part.module, &s2.part.module));
    }
    let p1 = match proof_status(fs, pk, pers, st, sp, wr, c, s1, &k1) {
        Err(e) => return Err(e),
        Ok(p) => p,
    };
    let p2 = match proof_status(fs, pk, pers, st, sp, wr, c, s2, &k2) {
        Err(e) => return Err(e),
        Ok(p) => p,
    };
    if status_is(&p1, false) || status_is(&p2, false) {
        return Err(agree_bad(pers, st, h, y, &s1.part.module, &s2.part.module));
    }
    match partner_reads(pers, st, &mut c.partners, &s2.part.module, &cv2.ty) {
        Err(e) => return Err(e),
        Ok(()) => {}
    }
    if !(status_is(&p1, true) || status_is(&p2, true)) {
        let what = capture_what(pers, st, h, y);
        c.pending.push((what, y.dup2(), cv1));
    }
    Ok(())
}

/// con-leche: ConLeche/Driver/Reach.lean:443-477 clashAgree
/// A clash's copies the index locates, as spots with their statements and
/// kinds.
pub fn clash_spots(pk: &OleanPins, wr: &WorkerReads, cl: &Clash) -> Vec<(Spot, StmtRec, CKindF<NIdx, ()>)> {
    let mut out: Vec<(Spot, StmtRec, CKindF<NIdx, ()>)> = Vec::with_capacity(cl.copies.len());
    let mut i = 0usize;
    while i < cl.copies.len() {
        match clash_spot(pk, wr, &cl.copies[i]) {
            None => {}
            Some(x) => out.push(x),
        }
        i += 1;
    }
    out
}

/// con-leche: ConLeche/Driver/Reach.lean:443-477 clashAgree
/// One copy of a clash as a spot with its statement and kind, where the index
/// locates it.
pub fn clash_spot(pk: &OleanPins, wr: &WorkerReads, x: &(index::Copy, StmtRec, CKindF<NIdx, ()>)) -> Option<(Spot, StmtRec, CKindF<NIdx, ()>)> {
    match index::name_index_at(&wr.index, &x.0) {
        None => None,
        Some(q) => {
            let part = PartKey { module: index::header_loads_name_at(pk, &wr.loads, x.0.module), level: index::header_loads_level_at(&wr.loads, x.0.module) };
            Some((Spot { part, pos: name_position_dup(q) }, index::stmt_rec_dup(&x.1), index::c_kind_names_dup(&x.2)))
        }
    }
}

/// con-leche: ConLeche/Driver/Reach.lean:443-477 clashAgree
/// `statuses`: each spot's proof flag, in order; whether one is `no`, one
/// `yes` (upstream's `ps.contains`).
pub fn clash_statuses<F: OleanFs>(fs: &F, pk: &OleanPins, pers: &PersTier, st: &mut AState, sp: &files::Roots, wr: &WorkerReads, c: &mut ReachCache, spots: &Vec<(Spot, StmtRec, CKindF<NIdx, ()>)>) -> Result<(bool, bool), CheckError> {
    let mut no = false;
    let mut yes = false;
    let mut i = 0usize;
    while i < spots.len() {
        match proof_status(fs, pk, pers, st, sp, wr, c, &spots[i].0, &spots[i].2) {
            Err(e) => return Err(e),
            Ok(p) => {
                if status_is(&p, false) {
                    no = true;
                }
                if status_is(&p, true) {
                    yes = true;
                }
            }
        }
        i += 1;
    }
    Ok((no, yes))
}

/// con-leche: ConLeche/Driver/Reach.lean:443-477 clashAgree
/// `s!"{spots.map (·.1.part.mod)}"`: the modules, Lean's list rendering.
pub fn spots_text(pers: &PersTier, st: &AState, spots: &Vec<(Spot, StmtRec, CKindF<NIdx, ()>)>) -> Vec<u32> {
    let mut t = { const M: [u32; 1] = [91]; core_types::code_points(&M) };
    let mut i = 0usize;
    while i < spots.len() {
        if i > 0 {
            t = text::cat(t, &{ const M: [u32; 2] = [44, 32]; core_types::code_points(&M) });
        }
        t = text::cat(t, &view::name_text(pers, &st.store, &spots[i].0.part.module));
        i += 1;
    }
    text::cat(t, &{ const M: [u32; 1] = [93]; core_types::code_points(&M) })
}

/// con-leche: ConLeche/Driver/Reach.lean:443-477 clashAgree
/// One clash: its copies must be proofs of one statement; its name onto `acc`.
pub fn clash_agree_one<F: OleanFs>(fs: &F, pk: &OleanPins, pers: &PersTier, st: &mut AState, sp: &files::Roots, wr: &WorkerReads, c: &mut ReachCache, cl: &Clash, acc: &mut Vec<NIdx>) -> Result<(), CheckError> {
    let spots = clash_spots(pk, wr, cl);
    let (no, yes) = match clash_statuses(fs, pk, pers, st, sp, wr, c, &spots) {
        Err(e) => return Err(e),
        Ok(p) => p,
    };
    if no {
        let t = text::cat({ const M: [u32; 19] = [116, 104, 101, 32, 108, 111, 97, 100, 101, 100, 32, 109, 111, 100, 117, 108, 101, 115, 32]; core_types::code_points(&M) }, &spots_text(pers, st, &spots));
        let t = text::cat(t, &{ const M: [u32; 7] = [32, 115, 116, 111, 114, 101, 32]; core_types::code_points(&M) });
        let t = text::cat(t, &view::name_text(pers, &st.store, &cl.name));
        return Err(core_types::invalid(text::cat(t, &{ const M: [u32; 51] = [44, 32, 110, 111, 116, 32, 97, 115, 32, 111, 110, 101, 32, 99, 111, 110, 115, 116, 97, 110, 116, 32, 40, 110, 111, 116, 32, 112, 114, 111, 111, 102, 115, 32, 111, 102, 32, 111, 110, 101, 32, 115, 116, 97, 116, 101, 109, 101, 110, 116, 41]; core_types::code_points(&M) })));
    }
    if yes {
        acc.push(cl.name.dup2());
        return Ok(());
    }
    if spots.len() > 0 {
        let why = text::cat({ const M: [u32; 25] = [116, 119, 111, 32, 108, 111, 97, 100, 101, 100, 32, 109, 111, 100, 117, 108, 101, 115, 32, 115, 116, 111, 114, 101, 32]; core_types::code_points(&M) }, &view::name_text(pers, &st.store, &cl.name));
        c.pending.push((why, cl.name.dup2(), index::stmt_rec_dup(&spots[0].1)));
        acc.push(cl.name.dup2());
    }
    Ok(())
}

/// con-leche: ConLeche/Driver/Reach.lean:443-477 clashAgree
/// **The clash rule**: the copies of every name two loaded modules hold must be
/// proofs of one statement, one of them a theorem or the statement inferred to
/// be a proposition.  Every clashing name is returned, to be reached.
pub fn clash_agree<F: OleanFs>(fs: &F, pk: &OleanPins, pers: &PersTier, st: &mut AState, sp: &files::Roots, wr: &WorkerReads, c: &mut ReachCache, cls: &Vec<Clash>) -> Result<Vec<NIdx>, CheckError> {
    let mut acc: Vec<NIdx> = Vec::new();
    let mut i = 0usize;
    while i < cls.len() {
        match clash_agree_one(fs, pk, pers, st, sp, wr, c, &cls[i], &mut acc) {
            Err(e) => return Err(e),
            Ok(()) => {}
        }
        i += 1;
    }
    Ok(acc)
}

// ---------------------------------------------------------------------------
// The capture check
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Driver/Reach.lean:481-487 inExported
/// **Is `y` in module `m`'s exported part** (`m` loaded at `level`).
pub fn in_exported<F: OleanFs>(fs: &F, pk: &OleanPins, pers: &PersTier, st: &mut AState, sp: &files::Roots, wr: &WorkerReads, c: &mut ReachCache, m: &NIdx, lvl: &OLeanLevel, y: &NIdx) -> Result<bool, CheckError> {
    if level_index(lvl) == 0 {
        return Ok(true);
    }
    let k = PartKey { module: m.dup2(), level: OLeanLevel::Exported };
    match look_of(fs, pk, pers, st, sp, wr, c, &k) {
        Err(e) => return Err(e),
        Ok(()) => {}
    }
    match look_at(c, &k, y) {
        Err(e) => Err(e),
        Ok(o) => Ok(o.is_some()),
    }
}

/// con-leche: ConLeche/Driver/Reach.lean:489-532 captureOne
/// Whether `h`'s public-import closure holds the module at load position `i`.
pub fn pub_has(wr: &WorkerReads, h: &NIdx, i: u64) -> bool {
    match wr.loads.index.get(h) {
        None => false,
        Some(hi) => {
            let j = *hi as usize;
            if j < wr.pub_.len() {
                levels::mod_set_has(&wr.pub_[j], i)
            } else {
                false
            }
        }
    }
}

/// con-leche: ConLeche/Driver/Reach.lean:489-532 captureOne
/// `module {h} reads {y}, which {what}`.
pub fn reads_which(pers: &PersTier, st: &AState, h: &NIdx, y: &NIdx, what: Vec<u32>) -> CheckError {
    let t = text::cat({ const M: [u32; 7] = [109, 111, 100, 117, 108, 101, 32]; core_types::code_points(&M) }, &view::name_text(pers, &st.store, h));
    let t = text::cat(t, &{ const M: [u32; 7] = [32, 114, 101, 97, 100, 115, 32]; core_types::code_points(&M) });
    let t = text::cat(t, &view::name_text(pers, &st.store, y));
    let t = text::cat(t, &{ const M: [u32; 8] = [44, 32, 119, 104, 105, 99, 104, 32]; core_types::code_points(&M) });
    core_types::invalid(text::cat(t, &what))
}

/// con-leche: ConLeche/Driver/Reach.lean:489-532 captureOne
/// A located or loaded copy `s1` of `y` against the copy `h`'s view holds.
pub fn capture_against<F: OleanFs>(fs: &F, pk: &OleanPins, pers: &PersTier, st: &mut AState, sp: &files::Roots, wr: &WorkerReads, c: &mut ReachCache, h: &NIdx, y: &NIdx, s1: &Spot) -> Result<(), CheckError> {
    match locate(fs, pk, pers, st, sp, wr, c, h, y) {
        Err(e) => Err(e),
        Ok(None) => Err(reads_which(pers, st, h, y, { const M: [u32; 22] = [105, 116, 115, 32, 118, 105, 101, 119, 32, 100, 111, 101, 115, 32, 110, 111, 116, 32, 104, 111, 108, 100]; core_types::code_points(&M) })),
        Ok(Some(s2)) => agree_check(fs, pk, pers, st, sp, wr, c, h, y, s1, &s2),
    }
}

/// con-leche: ConLeche/Driver/Reach.lean:489-532 captureOne
/// **The capture check of one read** `y` of a record of home `h`, and the
/// completion of a name the index lacks.
pub fn capture_one<F: OleanFs>(fs: &F, pk: &OleanPins, pers: &PersTier, st: &mut AState, sp: &files::Roots, wr: &WorkerReads, own: &HashMap2<NIdx, bool>, env: &ReachEnv, c: &mut ReachCache, h: &NIdx, y: &NIdx) -> Result<(), CheckError> {
    if own.contains_key(y) {
        let t = text::cat({ const M: [u32; 21] = [110, 97, 109, 101, 32, 99, 97, 112, 116, 117, 114, 101, 58, 32, 109, 111, 100, 117, 108, 101, 32]; core_types::code_points(&M) }, &view::name_text(pers, &st.store, h));
        let t = text::cat(t, &{ const M: [u32; 7] = [32, 114, 101, 97, 100, 115, 32]; core_types::code_points(&M) });
        let t = text::cat(t, &view::name_text(pers, &st.store, y));
        let t = text::cat(t, &{ const M: [u32; 8] = [44, 32, 119, 104, 105, 99, 104, 32]; core_types::code_points(&M) });
        let t = text::cat(t, &view::name_text(pers, &st.store, &env.module));
        return Err(core_types::invalid(text::cat(t, &{ const M: [u32; 9] = [32, 100, 101, 99, 108, 97, 114, 101, 115]; core_types::code_points(&M) })));
    }
    match importer_spot(pk, wr, y) {
        Some((i, s1)) => {
            if s1.part.module.eq2(h) {
                return Ok(());
            }
            let short = if pub_has(wr, h, i) {
                match in_exported(fs, pk, pers, st, sp, wr, c, &s1.part.module, &s1.part.level, y) {
                    Err(e) => return Err(e),
                    Ok(b) => b,
                }
            } else {
                false
            };
            if short {
                return Ok(());
            }
            capture_against(fs, pk, pers, st, sp, wr, c, h, y, &s1)
        }
        None => match located_at(c, y) {
            Some(s1) => {
                if s1.part.module.eq2(h) {
                    return Ok(());
                }
                capture_against(fs, pk, pers, st, sp, wr, c, h, y, &s1)
            }
            None => match locate(fs, pk, pers, st, sp, wr, c, h, y) {
                Err(e) => Err(e),
                Ok(None) => Err(reads_which(pers, st, h, y, { const M: [u32; 27] = [110, 111, 32, 109, 111, 100, 117, 108, 101, 32, 111, 102, 32, 105, 116, 115, 32, 118, 105, 101, 119, 32, 104, 111, 108, 100, 115]; core_types::code_points(&M) })),
                Ok(Some(s)) => match priv_spot(fs, pk, pers, st, sp, wr, c, &s) {
                    Err(e) => Err(e),
                    Ok(p) => {
                        c.located.insert(y.dup2(), p);
                        c.completed.push((y.dup2(), h.dup2()));
                        Ok(())
                    }
                },
            },
        },
    }
}

/// con-leche: ConLeche/Driver/Reach.lean:489-532 captureOne
/// A name's located copy, copied.
pub fn located_at(c: &ReachCache, y: &NIdx) -> Option<Spot> {
    match c.located.get(y) {
        None => None,
        Some(s) => Some(spot_dup(s)),
    }
}

/// con-leche: ConLeche/Driver/Reach.lean:534-559 storedNamesOk
/// `a record read from module {h} stores {n}, which the context reads from
/// module {k}`.
pub fn stored_bad(pers: &PersTier, st: &AState, h: &NIdx, n: &NIdx, k: &NIdx) -> CheckError {
    let t = text::cat({ const M: [u32; 26] = [97, 32, 114, 101, 99, 111, 114, 100, 32, 114, 101, 97, 100, 32, 102, 114, 111, 109, 32, 109, 111, 100, 117, 108, 101, 32]; core_types::code_points(&M) }, &view::name_text(pers, &st.store, h));
    let t = text::cat(t, &{ const M: [u32; 8] = [32, 115, 116, 111, 114, 101, 115, 32]; core_types::code_points(&M) });
    let t = text::cat(t, &view::name_text(pers, &st.store, n));
    let t = text::cat(t, &{ const M: [u32; 38] = [44, 32, 119, 104, 105, 99, 104, 32, 116, 104, 101, 32, 99, 111, 110, 116, 101, 120, 116, 32, 114, 101, 97, 100, 115, 32, 102, 114, 111, 109, 32, 109, 111, 100, 117, 108, 101, 32]; core_types::code_points(&M) });
    core_types::invalid(text::cat(t, &view::name_text(pers, &st.store, k)))
}

/// con-leche: ConLeche/Driver/Reach.lean:534-559 storedNamesOk
/// One name a record of home `h` stores, against the importer's copies.
pub fn stored_name_ok<F: OleanFs>(fs: &F, pk: &OleanPins, pers: &PersTier, st: &mut AState, sp: &files::Roots, wr: &WorkerReads, c: &mut ReachCache, h: &NIdx, n: &NIdx) -> Result<(), CheckError> {
    match importer_spot(pk, wr, n) {
        Some((_, s)) => {
            if s.part.module.eq2(h) {
                Ok(())
            } else {
                Err(stored_bad(pers, st, h, n, &s.part.module))
            }
        }
        None => match located_at(c, n) {
            Some(s) => {
                if s.part.module.eq2(h) {
                    Ok(())
                } else {
                    Err(stored_bad(pers, st, h, n, &s.part.module))
                }
            }
            None => {
                let k = priv_key(h);
                match look_of(fs, pk, pers, st, sp, wr, c, &k) {
                    Err(e) => return Err(e),
                    Ok(()) => {}
                }
                match look_at(c, &k, n) {
                    Err(e) => Err(e),
                    Ok(Some(q)) => {
                        c.located.insert(n.dup2(), Spot { part: k, pos: q });
                        Ok(())
                    }
                    Ok(None) => {
                        let t = text::cat({ const M: [u32; 7] = [109, 111, 100, 117, 108, 101, 32]; core_types::code_points(&M) }, &view::name_text(pers, &st.store, h));
                        let t = text::cat(t, &{ const M: [u32; 38] = [58, 32, 97, 32, 114, 101, 99, 111, 114, 100, 32, 111, 102, 32, 105, 116, 115, 32, 112, 114, 105, 118, 97, 116, 101, 32, 112, 97, 114, 116, 32, 115, 116, 111, 114, 101, 115, 32]; core_types::code_points(&M) });
                        let t = text::cat(t, &view::name_text(pers, &st.store, n));
                        Err(core_types::invalid(text::cat(t, &{ const M: [u32; 38] = [44, 32, 119, 104, 105, 99, 104, 32, 105, 116, 115, 32, 112, 114, 105, 118, 97, 116, 101, 32, 112, 97, 114, 116, 32, 100, 111, 101, 115, 32, 110, 111, 116, 32, 104, 111, 108, 100]; core_types::code_points(&M) })))
                    }
                }
            }
        },
    }
}

/// con-leche: ConLeche/Driver/Reach.lean:534-559 storedNamesOk
/// **The names a record stores, against the importer's copies**: each has no
/// importer copy or one of `h`, and no located copy or one of `h`; one with
/// neither is located at `h`'s private part.
pub fn stored_names_ok<F: OleanFs>(fs: &F, pk: &OleanPins, pers: &PersTier, st: &mut AState, sp: &files::Roots, wr: &WorkerReads, c: &mut ReachCache, h: &NIdx, ns: &Vec<NIdx>) -> Result<(), CheckError> {
    let mut i = 0usize;
    while i < ns.len() {
        match stored_name_ok(fs, pk, pers, st, sp, wr, c, h, &ns[i]) {
            Err(e) => return Err(e),
            Ok(()) => {}
        }
        i += 1;
    }
    Ok(())
}

/// con-leche: ConLeche/Driver/Reach.lean:561-567 clashPartners
/// One stored name's copies, if it clashes, each statement's names as reads of
/// the copy's module.
pub fn clash_partners_one(pers: &PersTier, st: &mut AState, env: &ReachEnv, acc: &mut Vec<(NIdx, NIdx)>, n: &NIdx) -> Result<(), CheckError> {
    match env.copies.get(n) {
        None => Ok(()),
        Some(cs) => copies_partners(pers, st, acc, cs),
    }
}

/// con-leche: ConLeche/Driver/Reach.lean:561-567 clashPartners
/// `cs.foldl (fun acc (k, cv) => acc ++ partnerReads k cv.type) acc`.
pub fn copies_partners(pers: &PersTier, st: &mut AState, acc: &mut Vec<(NIdx, NIdx)>, cs: &Vec<(NIdx, StmtRec)>) -> Result<(), CheckError> {
    let mut i = 0usize;
    while i < cs.len() {
        match partner_reads(pers, st, acc, &cs[i].0, &cs[i].1.ty) {
            Err(e) => return Err(e),
            Ok(()) => {}
        }
        i += 1;
    }
    Ok(())
}

/// con-leche: ConLeche/Driver/Reach.lean:561-567 clashPartners
/// **Every copy of a clashing name the context stores**, its statement's names
/// each as a read of the copy's module, onto `acc`.
pub fn clash_partners(pers: &PersTier, st: &mut AState, env: &ReachEnv, acc: &mut Vec<(NIdx, NIdx)>, ns: &Vec<NIdx>) -> Result<(), CheckError> {
    let mut i = 0usize;
    while i < ns.len() {
        match clash_partners_one(pers, st, env, acc, &ns[i]) {
            Err(e) => return Err(e),
            Ok(()) => {}
        }
        i += 1;
    }
    Ok(())
}

/// con-leche: ConLeche/Driver/Reach.lean:569-576 captureAll
/// The capture check of every read of a record.
pub fn capture_all<F: OleanFs>(fs: &F, pk: &OleanPins, pers: &PersTier, st: &mut AState, sp: &files::Roots, wr: &WorkerReads, own: &HashMap2<NIdx, bool>, env: &ReachEnv, c: &mut ReachCache, h: &NIdx, ys: &Vec<NIdx>) -> Result<(), CheckError> {
    let mut i = 0usize;
    while i < ys.len() {
        match capture_one(fs, pk, pers, st, sp, wr, own, env, c, h, &ys[i]) {
            Err(e) => return Err(e),
            Ok(()) => {}
        }
        i += 1;
    }
    Ok(())
}

/// con-leche: ConLeche/Driver/Reach.lean:578-585 capturePairs
/// **The partners' reads checked**: each name capture-checked as a read of its
/// home.
pub fn capture_pairs<F: OleanFs>(fs: &F, pk: &OleanPins, pers: &PersTier, st: &mut AState, sp: &files::Roots, wr: &WorkerReads, own: &HashMap2<NIdx, bool>, env: &ReachEnv, c: &mut ReachCache, ps: &Vec<(NIdx, NIdx)>) -> Result<(), CheckError> {
    let mut i = 0usize;
    while i < ps.len() {
        match capture_one(fs, pk, pers, st, sp, wr, own, env, c, &ps[i].0, &ps[i].1) {
            Err(e) => return Err(e),
            Ok(()) => {}
        }
        i += 1;
    }
    Ok(())
}

// ---------------------------------------------------------------------------
// A record read
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Driver/Reach.lean:589-596 recBlocksAt
/// One recursor's location onto the block of its first member.
pub fn rec_blocks_add(m: &mut HashMap2<NIdx, Vec<u64>>, l: u64, k: &CKindF<NIdx, ()>) {
    match k {
        CKindF::Recur(all, _, _, _, _, _, _, _) => {
            if all.len() > 0 {
                let mut xs: Vec<u64> = match m.remove(&all[0]) {
                    None => Vec::new(),
                    Some(xs) => xs,
                };
                xs.push(l);
                m.insert(all[0].dup2(), xs);
            }
        }
        _ => {}
    }
}

/// con-leche: ConLeche/Driver/Reach.lean:589-596 recBlocksAt
/// **A part's recursors' locations by their block's first member**, in the
/// part's order: `t` its name table, `r` its region.
pub fn rec_blocks_at(pk: &OleanPins, pers: &PersTier, st: &mut AState, bs: &[u8], r: &Region, t: &NamePositions) -> Result<HashMap2<NIdx, Vec<u64>>, RdErr> {
    let mut m: HashMap2<NIdx, Vec<u64>> = HashMap2::new();
    let mut i = 0usize;
    while i < t.consts.len() {
        if t.consts[i].tag == 7 {
            match reads::kind_names_at(pk, pers, &mut st.store, bs, r, t.consts[i].loc) {
                Err(e) => return Err(e),
                Ok(k) => rec_blocks_add(&mut m, t.consts[i].loc, &k),
            }
        }
        i += 1;
    }
    Ok(m)
}

/// con-leche: ConLeche/Driver/Reach.lean:598-609 recBlocksOf
/// `recBlocksAt` at a part taken out, its table where it is.
pub fn rec_blocks_read(pk: &OleanPins, pers: &PersTier, st: &mut AState, wr: &WorkerReads, c: &ReachCache, k: &PartKey, p: &PartRead) -> Result<HashMap2<NIdx, Vec<u64>>, RdErr> {
    match table_get(wr, c, k) {
        None => Err(RdErr::Err(cache_lost())),
        Some(t) => rec_blocks_at(pk, pers, st, view::view_bytes(&p.files, &p.vb), &p.region, t),
    }
}

/// con-leche: ConLeche/Driver/Reach.lean:598-609 recBlocksOf
/// A part's recursors' locations by their block's first member, read once
/// (`ReachCache::rec_blocks` holds them).
pub fn rec_blocks_of<F: OleanFs>(fs: &F, pk: &OleanPins, pers: &PersTier, st: &mut AState, sp: &files::Roots, wr: &WorkerReads, c: &mut ReachCache, k: &PartKey) -> Result<(), CheckError> {
    if c.rec_blocks.contains_key(k) {
        return Ok(());
    }
    match table_of(fs, pk, pers, st, sp, wr, c, k) {
        Err(e) => return Err(e),
        Ok(()) => {}
    }
    let p = match take_part(fs, pk, pers, st, sp, c, k) {
        Err(e) => return Err(e),
        Ok(p) => p,
    };
    let r = rec_blocks_read(pk, pers, st, wr, c, k, &p);
    match put_part(pers, st, c, k, p, r) {
        Err(e) => Err(e),
        Ok(m) => {
            c.rec_blocks.insert(k.dup2(), m);
            Ok(())
        }
    }
}

/// con-leche: ConLeche/Driver/Reach.lean:611-615 groupCtorNames
/// The constructors a group's types list.
pub fn group_ctor_names(tys: &Vec<CEntryF<NIdx, EIdx>>) -> Vec<NIdx> {
    let mut out: Vec<NIdx> = Vec::new();
    let mut i = 0usize;
    while i < tys.len() {
        match &tys[i].kind {
            CKindF::Induct(_, _, _, cs, _, _, _, _) => {
                let mut j = 0usize;
                while j < cs.len() {
                    out.push(cs[j].dup2());
                    j += 1;
                }
            }
            _ => {}
        }
        i += 1;
    }
    out
}

/// con-leche: ConLeche/Driver/Reach.lean:617-619 groupRecLocs
/// The locations of a group's recursors in a part, by its first member.
pub fn group_rec_locs(rb: &HashMap2<NIdx, Vec<u64>>, all: &Vec<NIdx>) -> Vec<u64> {
    if all.len() == 0 {
        return Vec::new();
    }
    match rb.get(&all[0]) {
        None => Vec::new(),
        Some(xs) => {
            let mut out: Vec<u64> = Vec::with_capacity(xs.len());
            let mut i = 0usize;
            while i < xs.len() {
                out.push(xs[i]);
                i += 1;
            }
            out
        }
    }
}

/// con-leche: ConLeche/Driver/Reach.lean:621-628 groupMerged
/// Whether a constant is kept among a group's rest: a recursor of the block
/// `all`, or not a recursor.
pub fn group_keeps(e: &CEntryF<NIdx, EIdx>, all: &Vec<NIdx>) -> bool {
    match &e.kind {
        CKindF::Recur(all2, _, _, _, _, _, _, _) => crate::frontend::olean::module::nidx_list_eq(all2, all),
        _ => true,
    }
}

/// con-leche: ConLeche/Driver/Reach.lean:621-628 groupMerged
/// A group's constants as a merge: `n`'s type, the types, the constructors and
/// the recursors of the block `all` among `rest`.
pub fn group_merged(pk: &OleanPins, t: CEntryF<NIdx, EIdx>, tys: &Vec<CEntryF<NIdx, EIdx>>, rest: &Vec<CEntryF<NIdx, EIdx>>, all: &Vec<NIdx>) -> Merged {
    let mut cs: Vec<CEntry> = Vec::with_capacity(1 + tys.len() + rest.len());
    cs.push(CEntry { c: t, uses: Vec::new() });
    let mut i = 0usize;
    while i < tys.len() {
        cs.push(CEntry { c: view::c_entry_dup(&tys[i]), uses: Vec::new() });
        i += 1;
    }
    let mut j = 0usize;
    while j < rest.len() {
        if group_keeps(&rest[j], all) {
            cs.push(CEntry { c: view::c_entry_dup(&rest[j]), uses: Vec::new() });
        }
        j += 1;
    }
    group::merged_of_list(pk, &cs)
}

/// con-leche: ConLeche/Driver/Reach.lean:630-668 groupAt
/// The locations of some names in a part's lookup, `none` where one is
/// missing (`ns.mapM (look[·]?)`).
pub fn look_locs(c: &ReachCache, k: &PartKey, ns: &Vec<NIdx>) -> Result<Option<Vec<u64>>, CheckError> {
    match c.looks.get(k) {
        None => Err(cache_lost()),
        Some(l) => Ok(look_locs_in(l, ns)),
    }
}

/// con-leche: ConLeche/Driver/Reach.lean:630-668 groupAt
/// `ns.mapM (look[·]?)` over one lookup.
pub fn look_locs_in(l: &HashMap2<NIdx, NamePosition>, ns: &Vec<NIdx>) -> Option<Vec<u64>> {
    let mut out: Vec<u64> = Vec::with_capacity(ns.len());
    let mut i = 0usize;
    while i < ns.len() {
        match look_loc(l, &ns[i]) {
            None => return None,
            Some(x) => out.push(x),
        }
        i += 1;
    }
    Some(out)
}

/// con-leche: ConLeche/Driver/Reach.lean:630-668 groupAt
/// A name's location in a lookup.
pub fn look_loc(l: &HashMap2<NIdx, NamePosition>, n: &NIdx) -> Option<u64> {
    match l.get(n) {
        None => None,
        Some(q) => Some(q.loc),
    }
}

/// con-leche: ConLeche/Driver/Reach.lean:630-668 groupAt
/// A group's recursors' locations in a cached part.
pub fn rec_locs_at(c: &ReachCache, k: &PartKey, all: &Vec<NIdx>) -> Result<Vec<u64>, CheckError> {
    match c.rec_blocks.get(k) {
        None => Err(cache_lost()),
        Some(rb) => Ok(group_rec_locs(rb, all)),
    }
}

/// con-leche: ConLeche/Driver/Reach.lean:630-668 groupAt
/// **Type `n`'s group, read from one part**: `None` where the part lacks one of
/// its members or constructors.  The part's files are read once, for its table
/// and its region (`load_part`).
pub fn group_at<F: OleanFs>(fs: &F, pk: &OleanPins, pers: &PersTier, st: &mut AState, sp: &files::Roots, wr: &WorkerReads, c: &mut ReachCache, k: &PartKey, n: &NIdx) -> Result<Option<IDeclaration>, CheckError> {
    match load_part(fs, pk, pers, st, sp, c, k) {
        Err(e) => return Err(e),
        Ok(()) => {}
    }
    match look_of(fs, pk, pers, st, sp, wr, c, k) {
        Err(e) => return Err(e),
        Ok(()) => {}
    }
    let q = match look_at(c, k, n) {
        Err(e) => return Err(e),
        Ok(None) => return Ok(None),
        Ok(Some(q)) => q,
    };
    let t = match part_entry(fs, pk, pers, st, sp, c, k, q.loc) {
        Err(e) => return Err(e),
        Ok(t) => t,
    };
    let all: Vec<NIdx> = match &t.kind {
        CKindF::Induct(_, _, all, _, _, _, _, _) => env::nidx_vec_dup(all),
        _ => {
            let m = text::cat({ const M: [u32; 7] = [109, 111, 100, 117, 108, 101, 32]; core_types::code_points(&M) }, &view::name_text(pers, &st.store, &k.module));
            let m = text::cat(m, &{ const M: [u32; 2] = [58, 32]; core_types::code_points(&M) });
            let m = text::cat(m, &view::name_text(pers, &st.store, n));
            return Err(core_types::invalid(text::cat(m, &{ const M: [u32; 25] = [32, 105, 115, 32, 110, 111, 116, 32, 97, 110, 32, 105, 110, 100, 117, 99, 116, 105, 118, 101, 32, 116, 121, 112, 101]; core_types::code_points(&M) })));
        }
    };
    let mqs = match look_locs(c, k, &all) {
        Err(e) => return Err(e),
        Ok(None) => return Ok(None),
        Ok(Some(ls)) => ls,
    };
    let tys = match part_entries(fs, pk, pers, st, sp, c, k, &mqs) {
        Err(e) => return Err(e),
        Ok(tys) => tys,
    };
    let cqs = match look_locs(c, k, &group_ctor_names(&tys)) {
        Err(e) => return Err(e),
        Ok(None) => return Ok(None),
        Ok(Some(ls)) => ls,
    };
    match rec_blocks_of(fs, pk, pers, st, sp, wr, c, k) {
        Err(e) => return Err(e),
        Ok(()) => {}
    }
    let mut locs = cqs;
    match rec_locs_at(c, k, &all) {
        Err(e) => return Err(e),
        Ok(rl) => {
            let mut i = 0usize;
            while i < rl.len() {
                locs.push(rl[i]);
                i += 1;
            }
        }
    }
    let rest = match part_entries(fs, pk, pers, st, sp, c, k, &locs) {
        Err(e) => return Err(e),
        Ok(rest) => rest,
    };
    let mg = group_merged(pk, t, &tys, &rest, &all);
    match group::group_record(pk, pers, &st.store, &mg, n) {
        Err(e) => Err(e),
        Ok(d) => Ok(Some(d)),
    }
}

/// con-leche: ConLeche/Driver/Reach.lean:670-677 groupOfKind
/// The type whose group presents a copy of `x` of kind `k`: `x` itself, a
/// constructor's type, a recursor's block's first member (`x` itself for a
/// recursor of no block); none for any other kind.
pub fn group_of_kind(x: &NIdx, k: &CKindF<NIdx, ()>) -> Option<NIdx> {
    match k {
        CKindF::Induct(_, _, _, _, _, _, _, _) => Some(x.dup2()),
        CKindF::Ctor(ind, _, _, _, _) => Some(ind.dup2()),
        CKindF::Recur(all, _, _, _, _, _, _, _) => {
            if all.len() > 0 {
                Some(all[0].dup2())
            } else {
                Some(x.dup2())
            }
        }
        _ => None,
    }
}

/// con-leche: ConLeche/Driver/Reach.lean:679-692 stmtRecord
/// A statement as an axiom's record.
pub fn axiom_of(cv: StmtRec) -> IDeclaration {
    IDeclaration::AxiomDecl(IConstantVal { name: cv.name, level_params: cv.level_params, ty: cv.ty })
}

/// con-leche: ConLeche/Driver/Reach.lean:679-692 stmtRecord
/// **A copy presented as its statement** (`.axiomDecl cv`).  At a
/// compiler-trust name only where its home's private part declares an opaque
/// constant or an axiom there.
pub fn stmt_record<F: OleanFs>(fs: &F, pk: &OleanPins, pers: &PersTier, st: &mut AState, sp: &files::Roots, wr: &WorkerReads, c: &mut ReachCache, s: &Spot, cv: StmtRec) -> Result<(IDeclaration, NIdx), CheckError> {
    let h = s.part.module.dup2();
    let ops = match reduce_op_names(st) {
        Err(e) => return Err(e),
        Ok(ops) => ops,
    };
    if !env::nidx_vec_contains(&ops, &cv.name) {
        return Ok((axiom_of(cv), h));
    }
    match priv_spot(fs, pk, pers, st, sp, wr, c, s) {
        Err(e) => Err(e),
        Ok(p) => {
            if p.pos.tag == 0 || p.pos.tag == 3 {
                Ok((axiom_of(cv), h))
            } else {
                let t = text::cat({ const M: [u32; 7] = [109, 111, 100, 117, 108, 101, 32]; core_types::code_points(&M) }, &view::name_text(pers, &st.store, &h));
                let t = text::cat(t, &{ const M: [u32; 10] = [32, 100, 101, 99, 108, 97, 114, 101, 115, 32]; core_types::code_points(&M) });
                let t = text::cat(t, &view::name_text(pers, &st.store, &cv.name));
                Err(core_types::invalid(text::cat(t, &{ const M: [u32; 67] = [44, 32, 97, 32, 99, 111, 109, 112, 105, 108, 101, 114, 45, 116, 114, 117, 115, 116, 32, 110, 97, 109, 101, 44, 32, 97, 115, 32, 110, 101, 105, 116, 104, 101, 114, 32, 97, 110, 32, 111, 112, 97, 113, 117, 101, 32, 99, 111, 110, 115, 116, 97, 110, 116, 32, 110, 111, 114, 32, 97, 110, 32, 97, 120, 105, 111, 109]; core_types::code_points(&M) })))
            }
        }
    }
}

/// con-leche: ConLeche/Driver/Reach.lean:694-730 readRecord
/// The copy presenting `x`: the importer's, else a completion's located copy
/// (`true`).
pub fn record_spot(pk: &OleanPins, wr: &WorkerReads, c: &ReachCache, x: &NIdx) -> Option<(Spot, bool)> {
    match importer_spot(pk, wr, x) {
        Some((_, s)) => Some((s, false)),
        None => match located_at(c, x) {
            None => None,
            Some(s) => Some((s, true)),
        },
    }
}

/// con-leche: ConLeche/Driver/Reach.lean:694-730 readRecord
/// **The record presenting `x`, and its home**: read at the importer's copy,
/// or at a completion's located copy as a statement.
pub fn read_record<F: OleanFs>(fs: &F, pk: &OleanPins, pers: &PersTier, st: &mut AState, sp: &files::Roots, wr: &WorkerReads, c: &mut ReachCache, x: &NIdx) -> Result<(IDeclaration, NIdx), CheckError> {
    let (s, completed) = match record_spot(pk, wr, c, x) {
        None => {
            let t = text::cat({ const M: [u32; 17] = [116, 104, 101, 32, 114, 101, 97, 99, 104, 32, 112, 117, 115, 104, 101, 100, 32]; core_types::code_points(&M) }, &view::name_text(pers, &st.store, x));
            return Err(core_types::internal(text::cat(t, &{ const M: [u32; 23] = [44, 32, 119, 104, 105, 99, 104, 32, 110, 111, 116, 104, 105, 110, 103, 32, 108, 111, 99, 97, 116, 101, 115]; core_types::code_points(&M) })));
        }
        Some(p) => p,
    };
    let h = s.part.module.dup2();
    if s.pos.skipped {
        let t = text::cat({ const M: [u32; 23] = [97, 32, 99, 111, 110, 116, 101, 120, 116, 32, 114, 101, 99, 111, 114, 100, 32, 114, 101, 97, 100, 115, 32]; core_types::code_points(&M) }, &view::name_text(pers, &st.store, x));
        let t = text::cat(t, &{ const M: [u32; 4] = [32, 111, 102, 32]; core_types::code_points(&M) });
        let t = text::cat(t, &view::name_text(pers, &st.store, &h));
        return Err(core_types::invalid(text::cat(t, &{ const M: [u32; 28] = [44, 32, 119, 104, 105, 99, 104, 32, 105, 115, 32, 117, 110, 115, 97, 102, 101, 32, 111, 114, 32, 112, 97, 114, 116, 105, 97, 108]; core_types::code_points(&M) })));
    }
    let (cv, k) = match stmt_at(fs, pk, pers, st, sp, c, &s) {
        Err(e) => return Err(e),
        Ok(p) => p,
    };
    match group_of_kind(x, &k) {
        Some(n) => match group_at(fs, pk, pers, st, sp, wr, c, &priv_key(&h), &n) {
            Err(e) => Err(e),
            Ok(Some(d)) => Ok((d, h)),
            Ok(None) => {
                let t = text::cat({ const M: [u32; 7] = [109, 111, 100, 117, 108, 101, 32]; core_types::code_points(&M) }, &view::name_text(pers, &st.store, &h));
                let t = text::cat(t, &{ const M: [u32; 15] = [58, 32, 116, 104, 101, 32, 103, 114, 111, 117, 112, 32, 111, 102, 32]; core_types::code_points(&M) });
                let t = text::cat(t, &view::name_text(pers, &st.store, &n));
                Err(core_types::invalid(text::cat(t, &{ const M: [u32; 32] = [32, 108, 97, 99, 107, 115, 32, 97, 32, 109, 101, 109, 98, 101, 114, 32, 111, 114, 32, 97, 32, 99, 111, 110, 115, 116, 114, 117, 99, 116, 111, 114]; core_types::code_points(&M) })))
            }
        },
        None => match k {
            CKindF::Defn(_, _, _) => {
                if completed {
                    return stmt_record(fs, pk, pers, st, sp, wr, c, &s, cv);
                }
                match part_entry(fs, pk, pers, st, sp, c, &s.part, s.pos.loc) {
                    Err(e) => Err(e),
                    Ok(e) => match present::record_of_entry(pers, &st.store, e) {
                        Err(e2) => Err(e2),
                        Ok(d) => Ok((d, h)),
                    },
                }
            }
            CKindF::Quot(q) => {
                let e = CEntryF { name: cv.name, level_params: cv.level_params, ty: cv.ty, kind: CKindF::Quot(q) };
                match present::record_of_entry(pers, &st.store, e) {
                    Err(e2) => Err(e2),
                    Ok(d) => Ok((d, h)),
                }
            }
            _ => stmt_record(fs, pk, pers, st, sp, wr, c, &s, cv),
        },
    }
}

// ---------------------------------------------------------------------------
// The worklist
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Driver/Reach.lean:736-745 ReachLog
/// **The reach's logical state**: the names pushed so far, the names the
/// context's records install, the records, their homes and what each reads,
/// the names still to read (`stack` up to its height `sp`, the top last).
pub struct ReachLog {
    pub seen: HashMap2<NIdx, bool>,
    pub stored: HashMap2<NIdx, bool>,
    pub ctx: Vec<IDeclaration>,
    pub homes: Vec<NIdx>,
    pub reads: Vec<Vec<NIdx>>,
    pub stack: Vec<NIdx>,
    pub sp: usize,
}

/// con-leche: ConLeche/Driver/Reach.lean:747-753 pushNames
/// One name onto the stack at height `sp`.
pub fn stack_push(stack: &mut Vec<NIdx>, sp: usize, y: &NIdx) -> usize {
    if sp < stack.len() {
        stack[sp] = y.dup2();
    } else {
        stack.push(y.dup2());
    }
    sp + 1
}

/// con-leche: ConLeche/Driver/Reach.lean:747-753 pushNames
/// Push the names not seen yet.
pub fn push_names(seen: &mut HashMap2<NIdx, bool>, stack: &mut Vec<NIdx>, sp: usize, ys: &Vec<NIdx>) -> usize {
    let mut sp = sp;
    let mut i = 0usize;
    while i < ys.len() {
        if !seen.contains_key(&ys[i]) {
            seen.insert(ys[i].dup2(), true);
            sp = stack_push(stack, sp, &ys[i]);
        }
        i += 1;
    }
    sp
}

/// con-leche: ConLeche/Driver/Reach.lean:747-753 pushNames
/// The second names of some pairs (`ps.map (·.2)`).
pub fn pair_seconds(ps: &Vec<(NIdx, NIdx)>) -> Vec<NIdx> {
    let mut out: Vec<NIdx> = Vec::with_capacity(ps.len());
    let mut i = 0usize;
    while i < ps.len() {
        out.push(ps[i].1.dup2());
        i += 1;
    }
    out
}

/// con-leche: ConLeche/Driver/Reach.lean:755-759 ReachLog.add
/// Some names into a set.
pub fn set_add_all(s: &mut HashMap2<NIdx, bool>, ns: &Vec<NIdx>) {
    let mut i = 0usize;
    while i < ns.len() {
        s.insert(ns[i].dup2(), true);
        i += 1;
    }
}

/// con-leche: ConLeche/Driver/Reach.lean:755-759 ReachLog.add
/// **A record added**: its names `ns` stored, what it reads (`rd`) pushed.
pub fn reach_log_add(l: &mut ReachLog, d: IDeclaration, h: NIdx, ns: &Vec<NIdx>, rd: Vec<NIdx>) {
    l.sp = push_names(&mut l.seen, &mut l.stack, l.sp, &rd);
    set_add_all(&mut l.stored, ns);
    l.ctx.push(d);
    l.homes.push(h);
    l.reads.push(rd);
}

/// con-leche: ConLeche/Driver/Reach.lean:761-764 ReachLog.init
/// **The worklist's start**: the roots pushed, nothing read.
pub fn reach_log_init(rs: &Vec<NIdx>) -> ReachLog {
    let mut l = ReachLog { seen: HashMap2::new(), stored: HashMap2::new(), ctx: Vec::new(), homes: Vec::new(), reads: Vec::new(), stack: Vec::new(), sp: 0 };
    l.sp = push_names(&mut l.seen, &mut l.stack, 0, rs);
    l
}

/// con-leche: ConLeche/Driver/Reach.lean:766-777 missingError
/// Why the record read for `x` does not store it (`ns`: its names).
pub fn missing_error(pers: &PersTier, st: &mut AState, d: &IDeclaration, ns: &Vec<NIdx>, x: &NIdx, h: &NIdx) -> CheckError {
    let xs = view::name_text(pers, &st.store, x);
    let hs = view::name_text(pers, &st.store, h);
    let plain = core_types::invalid(text::cat3(text::cat3({ const M: [u32; 20] = [116, 104, 101, 32, 114, 101, 99, 111, 114, 100, 32, 114, 101, 97, 100, 32, 102, 111, 114, 32]; core_types::code_points(&M) }, &xs, &{ const M: [u32; 6] = [32, 102, 114, 111, 109, 32]; core_types::code_points(&M) }), &hs, &{ const M: [u32; 20] = [32, 100, 111, 101, 115, 32, 110, 111, 116, 32, 100, 101, 99, 108, 97, 114, 101, 32, 105, 116]; core_types::code_points(&M) }));
    match d {
        IDeclaration::IndDecl(_, _) => {
            if ns.len() == 0 {
                let t = text::cat3({ const M: [u32; 23] = [116, 104, 101, 32, 105, 110, 100, 117, 99, 116, 105, 118, 101, 32, 103, 114, 111, 117, 112, 32, 111, 102, 32]; core_types::code_points(&M) }, &xs, &{ const M: [u32; 12] = [44, 32, 114, 101, 97, 100, 32, 102, 114, 111, 109, 32]; core_types::code_points(&M) });
                core_types::not_implemented(text::cat3(t, &hs, &{ const M: [u32; 38] = [58, 32, 97, 32, 103, 114, 111, 117, 112, 32, 116, 104, 101, 32, 114, 101, 99, 111, 103, 110, 105, 115, 101, 114, 32, 100, 111, 101, 115, 32, 110, 111, 116, 32, 114, 101, 97, 100]; core_types::code_points(&M) }))
            } else {
                core_types::invalid(text::cat3(text::cat3({ const M: [u32; 19] = [116, 104, 101, 32, 103, 114, 111, 117, 112, 32, 114, 101, 97, 100, 32, 102, 111, 114, 32]; core_types::code_points(&M) }, &xs, &{ const M: [u32; 6] = [32, 102, 114, 111, 109, 32]; core_types::code_points(&M) }), &hs, &{ const M: [u32; 20] = [32, 100, 111, 101, 115, 32, 110, 111, 116, 32, 100, 101, 99, 108, 97, 114, 101, 32, 105, 116]; core_types::code_points(&M) }))
            }
        }
        IDeclaration::AxiomDecl(cv) => match pin_sorry_ax(st) {
            Err(e) => e,
            Ok(s) => {
                if cv.name.eq2(&s) {
                    core_types::not_implemented(text::cat3({ const M: [u32; 23] = [97, 32, 99, 111, 110, 116, 101, 120, 116, 32, 114, 101, 99, 111, 114, 100, 32, 114, 101, 97, 100, 115, 32]; core_types::code_points(&M) }, &xs, &{ const M: [u32; 10] = [32, 40, 115, 111, 114, 114, 121, 65, 120, 41]; core_types::code_points(&M) }))
                } else {
                    plain
                }
            }
        },
        _ => plain,
    }
}

/// con-leche: ConLeche/Driver/Reach.lean:779-783 clashCopiesOf
/// **The copies of every name two loaded modules hold**, by name: each copy's
/// module and statement.
pub fn clash_copies_of(pk: &OleanPins, wr: &WorkerReads) -> HashMap2<NIdx, Vec<(NIdx, StmtRec)>> {
    let mut m: HashMap2<NIdx, Vec<(NIdx, StmtRec)>> = HashMap2::new();
    let mut i = 0usize;
    while i < wr.clashes.len() {
        m.insert(wr.clashes[i].name.dup2(), clash_copy_list(pk, wr, &wr.clashes[i]));
        i += 1;
    }
    m
}

/// con-leche: ConLeche/Driver/Reach.lean:779-783 clashCopiesOf
/// One clash's copies: each copy's module and statement.
pub fn clash_copy_list(pk: &OleanPins, wr: &WorkerReads, cl: &Clash) -> Vec<(NIdx, StmtRec)> {
    let mut out: Vec<(NIdx, StmtRec)> = Vec::with_capacity(cl.copies.len());
    let mut i = 0usize;
    while i < cl.copies.len() {
        out.push((index::header_loads_name_at(pk, &wr.loads, cl.copies[i].0.module), index::stmt_rec_dup(&cl.copies[i].1)));
        i += 1;
    }
    out
}

/// con-leche: ConLeche/Driver/Reach.lean:785-788 inRecord
/// A failed read of the record of `x`, read from `h`, names the record.
pub fn in_record(pers: &PersTier, st: &AState, x: &NIdx, h: &NIdx, e: CheckError) -> CheckError {
    match e {
        CheckError::Invalid(m) => {
            let t = text::cat({ const M: [u32; 14] = [116, 104, 101, 32, 114, 101, 99, 111, 114, 100, 32, 111, 102, 32]; core_types::code_points(&M) }, &view::name_text(pers, &st.store, x));
            let t = text::cat(t, &{ const M: [u32; 12] = [44, 32, 114, 101, 97, 100, 32, 102, 114, 111, 109, 32]; core_types::code_points(&M) });
            let t = text::cat(t, &view::name_text(pers, &st.store, h));
            let t = text::cat(t, &{ const M: [u32; 2] = [58, 32]; core_types::code_points(&M) });
            core_types::invalid(text::cat(t, &m))
        }
        e => e,
    }
}

/// con-leche: ConLeche/Driver/Reach.lean:790-827 reachGo
/// Whether a record stores a name already stored.
pub fn any_stored(stored: &HashMap2<NIdx, bool>, ns: &Vec<NIdx>) -> bool {
    let mut i = 0usize;
    while i < ns.len() {
        if stored.contains_key(&ns[i]) {
            return true;
        }
        i += 1;
    }
    false
}

/// con-leche: ConLeche/Driver/Reach.lean:790-827 reachGo
/// The worklist's step at an empty stack: the partners' reads recorded so far
/// capture-checked and pushed.
pub fn reach_partners<F: OleanFs>(fs: &F, pk: &OleanPins, pers: &PersTier, st: &mut AState, sp: &files::Roots, wr: &WorkerReads, own: &HashMap2<NIdx, bool>, env: &ReachEnv, l: &mut ReachLog, c: &mut ReachCache) -> Result<(), CheckError> {
    let ps: Vec<(NIdx, NIdx)> = core::mem::replace(&mut c.partners, Vec::new());
    match capture_pairs(fs, pk, pers, st, sp, wr, own, env, c, &ps) {
        Err(e) => return Err(e),
        Ok(()) => {}
    }
    l.sp = push_names(&mut l.seen, &mut l.stack, 0, &pair_seconds(&ps));
    Ok(())
}

/// con-leche: ConLeche/Driver/Reach.lean:790-827 reachGo
/// The worklist's step at a name `x` popped: its record read, checked and
/// added, unless a record stores it already.
pub fn reach_read<F: OleanFs>(fs: &F, pk: &OleanPins, pers: &PersTier, st: &mut AState, sp: &files::Roots, wr: &WorkerReads, own: &HashMap2<NIdx, bool>, env: &ReachEnv, l: &mut ReachLog, c: &mut ReachCache, x: &NIdx) -> Result<(), CheckError> {
    if l.stored.contains_key(x) {
        return Ok(());
    }
    let (d, h) = match read_record(fs, pk, pers, st, sp, wr, c, x) {
        Err(e) => return Err(e),
        Ok(p) => p,
    };
    let ns = match decl_names(pers, st, &d) {
        Err(e) => return Err(e),
        Ok(ns) => ns,
    };
    if !env::nidx_vec_contains(&ns, x) {
        return Err(missing_error(pers, st, &d, &ns, x, &h));
    }
    if any_stored(&l.stored, &ns) {
        let t = text::cat({ const M: [u32; 36] = [116, 119, 111, 32, 99, 111, 110, 116, 101, 120, 116, 32, 114, 101, 99, 111, 114, 100, 115, 32, 115, 116, 111, 114, 101, 32, 97, 32, 110, 97, 109, 101, 32, 111, 102, 32]; core_types::code_points(&M) }, &view::name_text(pers, &st.store, x));
        let t = text::cat(t, &{ const M: [u32; 14] = [39, 115, 32, 114, 101, 99, 111, 114, 100, 32, 40, 111, 102, 32]; core_types::code_points(&M) });
        let t = text::cat(t, &view::name_text(pers, &st.store, &h));
        return Err(core_types::invalid(text::cat(t, &{ const M: [u32; 1] = [41]; core_types::code_points(&M) })));
    }
    let rd = match record_reads(pers, st, &d) {
        Err(e) => return Err(e),
        Ok(rd) => rd,
    };
    match capture_all(fs, pk, pers, st, sp, wr, own, env, c, &h, &rd) {
        Err(e) => return Err(in_record(pers, st, x, &h, e)),
        Ok(()) => {}
    }
    match stored_names_ok(fs, pk, pers, st, sp, wr, c, &h, &ns) {
        Err(e) => return Err(e),
        Ok(()) => {}
    }
    reach_log_add(l, d, h, &ns, rd);
    clash_partners(pers, st, env, &mut c.partners, &ns)
}

/// con-leche: ConLeche/Driver/Reach.lean:790-827 reachGo
/// `"the reach ran out of steps"`.
pub fn reach_out_of_steps() -> CheckError {
    core_types::internal({ const M: [u32; 26] = [116, 104, 101, 32, 114, 101, 97, 99, 104, 32, 114, 97, 110, 32, 111, 117, 116, 32, 111, 102, 32, 115, 116, 101, 112, 115]; core_types::code_points(&M) })
}

/// con-leche: ConLeche/Driver/Reach.lean:790-827 reachGo
/// **The reach's worklist**: a name popped and read, or at an empty stack the
/// partners' reads checked, until both are empty; each step spends one fuel.
pub fn reach_go<F: OleanFs>(fs: &F, pk: &OleanPins, pers: &PersTier, st: &mut AState, sp: &files::Roots, wr: &WorkerReads, own: &HashMap2<NIdx, bool>, env: &ReachEnv, l: &mut ReachLog, c: &mut ReachCache, fuel: u64) -> Result<(), CheckError> {
    let mut fuel = fuel;
    while l.sp > 0 || c.partners.len() > 0 {
        if fuel == 0 {
            return Err(reach_out_of_steps());
        }
        fuel -= 1;
        if l.sp == 0 {
            match reach_partners(fs, pk, pers, st, sp, wr, own, env, l, c) {
                Err(e) => return Err(e),
                Ok(()) => {}
            }
        } else {
            l.sp -= 1;
            let x = l.stack[l.sp].dup2();
            match reach_read(fs, pk, pers, st, sp, wr, own, env, l, c, &x) {
                Err(e) => return Err(e),
                Ok(()) => {}
            }
        }
    }
    Ok(())
}

// ---------------------------------------------------------------------------
// The validation and the flags
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Driver/Reach.lean:831-838 validateCtx
/// **Every context record validated** (`record_ok`), the first failure named.
pub fn validate_ctx(pers: &PersTier, st: &mut AState, ds: &Vec<IDeclaration>, hs: &Vec<NIdx>) -> Result<(), CheckError> {
    let mut i = 0usize;
    while i < ds.len() {
        match record_ok(pers, st, &ds[i]) {
            Err(e) => return Err(e),
            Ok(true) => {}
            Ok(false) => return Err(validate_bad(pers, st, &ds[i], hs, i)),
        }
        i += 1;
    }
    Ok(())
}

/// con-leche: ConLeche/Driver/Reach.lean:831-838 validateCtx
/// The malformed record at position `i` named, with its home.
pub fn validate_bad(pers: &PersTier, st: &mut AState, d: &IDeclaration, hs: &Vec<NIdx>, i: usize) -> CheckError {
    if i >= hs.len() {
        return core_types::internal({ const M: [u32; 36] = [97, 32, 109, 97, 108, 102, 111, 114, 109, 101, 100, 32, 99, 111, 110, 116, 101, 120, 116, 32, 114, 101, 99, 111, 114, 100, 32, 110, 111, 116, 32, 102, 111, 117, 110, 100]; core_types::code_points(&M) });
    }
    match decl_label(pers, st, d) {
        Err(e) => e,
        Ok(lbl) => {
            let t = text::cat({ const M: [u32; 11] = [116, 104, 101, 32, 114, 101, 99, 111, 114, 100, 32]; core_types::code_points(&M) }, &lbl);
            let t = text::cat(t, &{ const M: [u32; 11] = [32, 111, 102, 32, 109, 111, 100, 117, 108, 101, 32]; core_types::code_points(&M) });
            let t = text::cat(t, &view::name_text(pers, &st.store, &hs[i]));
            core_types::invalid(text::cat(t, &{ const M: [u32; 142] = [32, 105, 115, 32, 109, 97, 108, 102, 111, 114, 109, 101, 100, 32, 40, 97, 32, 102, 114, 101, 101, 32, 111, 114, 32, 108, 111, 111, 115, 101, 32, 98, 111, 117, 110, 100, 32, 118, 97, 114, 105, 97, 98, 108, 101, 44, 32, 97, 110, 32, 117, 110, 100, 101, 99, 108, 97, 114, 101, 100, 32, 117, 110, 105, 118, 101, 114, 115, 101, 32, 112, 97, 114, 97, 109, 101, 116, 101, 114, 44, 32, 97, 32, 110, 101, 115, 116, 101, 100, 32, 114, 117, 108, 101, 39, 115, 32, 100, 97, 116, 117, 109, 44, 32, 97, 32, 116, 97, 98, 108, 101, 39, 115, 32, 98, 111, 100, 105, 101, 115, 32, 111, 114, 32, 97, 32, 108, 105, 116, 101, 114, 97, 108, 39, 115, 32, 115, 104, 97, 112, 101, 41]; core_types::code_points(&M) }))
        }
    }
}

/// con-leche: ConLeche/Driver/Reach.lean:840-844 typeIsPropC
/// **Is a statement's type a proposition**, by the kernel's inference at `fe`
/// (verified mode).
pub fn type_is_prop_c(pers: &PersTier, st: &mut AState, fe: &env::IFEnv, cv: &StmtRec) -> Result<bool, CheckError> {
    match infer_type_core(pers, st, &CheckMode::Verified, fe, CHECK_FUEL, 0, &cv.ty) {
        Err(e) => Err(e),
        Ok(jsty) => match ensure_sort_core(pers, st, &CheckMode::Verified, fe, CHECK_FUEL, 0, &jsty) {
            Err(e) => Err(e),
            Ok(u) => match zero_level(st) {
                Err(e) => Err(e),
                Ok(z) => match lvl_eq(pers, st, &u, &z) {
                    Err(e) => Err(e),
                    Ok(o) => lift_fueled(o),
                },
            },
        },
    }
}

/// con-leche: ConLeche/Driver/Reach.lean:846-849 ctxPart
/// **Each context name's first record**, by its position: the view of that
/// position is the part of the context below the name.
pub fn first_owner(pers: &PersTier, st: &mut AState, ds: &Vec<IDeclaration>) -> Result<HashMap2<NIdx, u64>, CheckError> {
    let mut m: HashMap2<NIdx, u64> = HashMap2::new();
    let mut j = 0usize;
    while j < ds.len() {
        match decl_names(pers, st, &ds[j]) {
            Err(e) => return Err(e),
            Ok(ns) => first_owner_add(&mut m, &ns, j as u64),
        }
        j += 1;
    }
    Ok(m)
}

/// con-leche: ConLeche/Driver/Reach.lean:846-849 ctxPart
/// A record's names into the first-owner map, a name owned already kept.
pub fn first_owner_add(m: &mut HashMap2<NIdx, u64>, ns: &Vec<NIdx>, j: u64) {
    let mut i = 0usize;
    while i < ns.len() {
        if !m.contains_key(&ns[i]) {
            m.insert(ns[i].dup2(), j);
        }
        i += 1;
    }
}

/// con-leche: ConLeche/Driver/Reach.lean:846-849 ctxPart
/// The position whose view is the part of the context below `y`.
pub fn part_pos(m: &HashMap2<NIdx, u64>, n: u64, y: &NIdx) -> u64 {
    match m.get(y) {
        None => n,
        Some(j) => *j,
    }
}

/// con-leche: none — a message's code points, copied
pub fn cps_dup(a: &Vec<u32>) -> Vec<u32> {
    let mut out: Vec<u32> = Vec::with_capacity(a.len());
    let mut i = 0usize;
    while i < a.len() {
        out.push(a[i]);
        i += 1;
    }
    out
}

/// con-leche: ConLeche/Driver/Reach.lean:851-866 inferFlags
/// One recorded statement inferred, in its record's bracket: its names stored
/// before it, its type a proposition.
pub fn infer_one(pers: &PersTier, st: &mut AState, fe: &env::IFEnv, what: &Vec<u32>, y: &NIdx, cv: &StmtRec) -> Result<(), CheckError> {
    let ok = match expr_ok(pers, st, &cv.level_params, 0, &cv.ty) {
        Err(e) => return Err(e),
        Ok(false) => false,
        Ok(true) => match consts_resolve_f_fast(pers, st, fe, &cv.ty) {
            Err(e) => return Err(e),
            Ok(b) => b,
        },
    };
    if !ok {
        let t = text::cat({ const M: [u32; 17] = [116, 104, 101, 32, 115, 116, 97, 116, 101, 109, 101, 110, 116, 32, 111, 102, 32]; core_types::code_points(&M) }, &view::name_text(pers, &st.store, y));
        return Err(core_types::invalid(text::cat(t, &{ const M: [u32; 50] = [32, 114, 101, 97, 100, 115, 32, 97, 32, 110, 97, 109, 101, 32, 116, 104, 101, 32, 99, 111, 110, 116, 101, 120, 116, 32, 100, 111, 101, 115, 32, 110, 111, 116, 32, 115, 116, 111, 114, 101, 32, 98, 101, 102, 111, 114, 101, 32, 105, 116]; core_types::code_points(&M) })));
    }
    match type_is_prop_c(pers, st, fe, cv) {
        Err(e) => Err(e),
        Ok(true) => Ok(()),
        Ok(false) => {
            let t = text::cat(cps_dup(what), &{ const M: [u32; 16] = [58, 32, 116, 104, 101, 32, 99, 111, 112, 105, 101, 115, 32, 111, 102, 32]; core_types::code_points(&M) });
            let t = text::cat(t, &view::name_text(pers, &st.store, y));
            Err(core_types::invalid(text::cat(t, &{ const M: [u32; 68] = [32, 111, 102, 32, 116, 119, 111, 32, 109, 111, 100, 117, 108, 101, 115, 32, 97, 114, 101, 32, 110, 111, 116, 32, 111, 110, 101, 32, 99, 111, 110, 115, 116, 97, 110, 116, 32, 40, 105, 116, 115, 32, 116, 121, 112, 101, 32, 105, 115, 32, 110, 111, 116, 32, 97, 32, 112, 114, 111, 112, 111, 115, 105, 116, 105, 111, 110, 41]; core_types::code_points(&M) })))
        }
    }
}

/// con-leche: ConLeche/Driver/Reach.lean:851-866 inferFlags
/// **The inferred flags**: every recorded statement a proposition over the
/// part of the context below its name, at the frozen index of `ctx ++ own`
/// (`pers`): the view of the first record storing the name, else of the first
/// own record.  Each inference runs in its own bracket (`enter_record`,
/// `leave_record`), as a job does.
pub fn infer_flags(pers: &PersTier, st: &mut AState, ctx: &Vec<IDeclaration>, pending: &Vec<(Vec<u32>, NIdx, StmtRec)>) -> Result<(), CheckError> {
    if pending.len() == 0 {
        return Ok(());
    }
    let owner = match first_owner(pers, st, ctx) {
        Err(e) => return Err(e),
        Ok(m) => m,
    };
    let n = ctx.len() as u64;
    let mut i = 0usize;
    while i < pending.len() {
        let fe = stream_index_view(pers, part_pos(&owner, n, &pending[i].1));
        enter_record(st);
        let r = infer_one(pers, st, &fe, &pending[i].0, &pending[i].1, &pending[i].2);
        leave_record(st);
        match r {
            Err(e) => return Err(e),
            Ok(()) => {}
        }
        i += 1;
    }
    Ok(())
}

// ---------------------------------------------------------------------------
// The read order
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Driver/Reach.lean:870-873 ownerMap
/// One record's names into the owner map, at position `j`.
pub fn owner_add(m: &mut HashMap2<NIdx, u64>, ns: &Vec<NIdx>, j: u64) {
    let mut i = 0usize;
    while i < ns.len() {
        m.insert(ns[i].dup2(), j);
        i += 1;
    }
}

/// con-leche: ConLeche/Driver/Reach.lean:870-873 ownerMap
/// **Each context name's record**, by its position (the last record storing a
/// name kept).
pub fn owner_map(pers: &PersTier, st: &mut AState, ds: &Vec<IDeclaration>) -> Result<HashMap2<NIdx, u64>, CheckError> {
    let mut m: HashMap2<NIdx, u64> = HashMap2::new();
    let mut j = 0usize;
    while j < ds.len() {
        match decl_names(pers, st, &ds[j]) {
            Err(e) => return Err(e),
            Ok(ns) => owner_add(&mut m, &ns, j as u64),
        }
        j += 1;
    }
    Ok(m)
}

/// con-leche: ConLeche/Driver/Reach.lean:875-878 SortSt
/// **The read order's state**: the positions placed so far, in order, and as
/// a set.
pub struct SortSt {
    pub order: Vec<u64>,
    pub placed: HashMap2<u64, bool>,
}

/// con-leche: ConLeche/Driver/Reach.lean:880-902 sortVisit
/// `"the read order ran out of steps"`.
pub fn sort_out_of_steps() -> CheckError {
    core_types::internal({ const M: [u32; 31] = [116, 104, 101, 32, 114, 101, 97, 100, 32, 111, 114, 100, 101, 114, 32, 114, 97, 110, 32, 111, 117, 116, 32, 111, 102, 32, 115, 116, 101, 112, 115]; core_types::code_points(&M) })
}

/// con-leche: ConLeche/Driver/Reach.lean:880-902 sortVisit
/// The records at positions `i` and `j` read each other through `y`.
pub fn sort_cycle(pers: &PersTier, st: &mut AState, ds: &Vec<IDeclaration>, i: u64, j: u64, y: &NIdx) -> CheckError {
    let a = if (i as usize) < ds.len() {
        match decl_label(pers, st, &ds[i as usize]) {
            Err(e) => return e,
            Ok(t) => t,
        }
    } else {
        Vec::new()
    };
    let b = if (j as usize) < ds.len() {
        match decl_label(pers, st, &ds[j as usize]) {
            Err(e) => return e,
            Ok(t) => t,
        }
    } else {
        Vec::new()
    };
    let t = text::cat3({ const M: [u32; 20] = [116, 104, 101, 32, 99, 111, 110, 116, 101, 120, 116, 32, 114, 101, 99, 111, 114, 100, 115, 32]; core_types::code_points(&M) }, &a, &{ const M: [u32; 5] = [32, 97, 110, 100, 32]; core_types::code_points(&M) });
    let t = text::cat3(t, &b, &{ const M: [u32; 26] = [32, 114, 101, 97, 100, 32, 101, 97, 99, 104, 32, 111, 116, 104, 101, 114, 32, 40, 116, 104, 114, 111, 117, 103, 104, 32]; core_types::code_points(&M) });
    core_types::invalid(text::cat3(t, &view::name_text(pers, &st.store, y), &{ const M: [u32; 1] = [41]; core_types::code_points(&M) }))
}

/// con-leche: ConLeche/Driver/Reach.lean:880-902 sortVisit
/// One read `y` of record `i`: stored by `i` itself or a placed record, else
/// its record placed first, unless on the walk's path.
pub fn sort_visit_one(pers: &PersTier, st: &mut AState, ds: &Vec<IDeclaration>, rds: &Vec<Vec<NIdx>>, owner: &HashMap2<NIdx, u64>, fuel: u64, i: u64, path: &mut HashMap2<u64, bool>, y: &NIdx, ss: &mut SortSt) -> Result<(), CheckError> {
    let j = match owner.get(y) {
        None => {
            let t = text::cat({ const M: [u32; 23] = [97, 32, 99, 111, 110, 116, 101, 120, 116, 32, 114, 101, 99, 111, 114, 100, 32, 114, 101, 97, 100, 115, 32]; core_types::code_points(&M) }, &view::name_text(pers, &st.store, y));
            return Err(core_types::internal(text::cat(t, &{ const M: [u32; 32] = [44, 32, 119, 104, 105, 99, 104, 32, 110, 111, 32, 99, 111, 110, 116, 101, 120, 116, 32, 114, 101, 99, 111, 114, 100, 32, 115, 116, 111, 114, 101, 115]; core_types::code_points(&M) })));
        }
        Some(j) => *j,
    };
    if j == i || ss.placed.contains_key(&j) {
        return Ok(());
    }
    if path.contains_key(&j) {
        return Err(sort_cycle(pers, st, ds, i, j, y));
    }
    path.insert(j, true);
    let r = if (j as usize) < rds.len() {
        sort_visit(pers, st, ds, rds, owner, fuel - 1, j, path, &rds[j as usize], ss)
    } else {
        sort_visit(pers, st, ds, rds, owner, fuel - 1, j, path, &Vec::new(), ss)
    };
    path.remove(&j);
    r
}

/// con-leche: ConLeche/Driver/Reach.lean:880-902 sortVisit
/// **The record at position `i` placed after its reads** `ys` still to place
/// (a post-order walk): a cycle among the records' reads is malformed input.
/// `fuel` bounds the walk's depth.  The path is `&mut`, each record taken off
/// it when its walk returns.
pub fn sort_visit(pers: &PersTier, st: &mut AState, ds: &Vec<IDeclaration>, rds: &Vec<Vec<NIdx>>, owner: &HashMap2<NIdx, u64>, fuel: u64, i: u64, path: &mut HashMap2<u64, bool>, ys: &Vec<NIdx>, ss: &mut SortSt) -> Result<(), CheckError> {
    if fuel == 0 {
        return Err(sort_out_of_steps());
    }
    let mut k = 0usize;
    while k < ys.len() {
        match sort_visit_one(pers, st, ds, rds, owner, fuel, i, path, &ys[k], ss) {
            Err(e) => return Err(e),
            Ok(()) => {}
        }
        k += 1;
    }
    ss.order.push(i);
    ss.placed.insert(i, true);
    Ok(())
}

/// con-leche: ConLeche/Driver/Reach.lean:904-913 sortFrom
/// Record `i` placed, each after its reads, unless placed already.
pub fn sort_from_one(pers: &PersTier, st: &mut AState, ds: &Vec<IDeclaration>, rds: &Vec<Vec<NIdx>>, owner: &HashMap2<NIdx, u64>, fuel: u64, i: u64, ss: &mut SortSt) -> Result<(), CheckError> {
    if ss.placed.contains_key(&i) {
        return Ok(());
    }
    let mut path: HashMap2<u64, bool> = HashMap2::new();
    path.insert(i, true);
    if (i as usize) < rds.len() {
        sort_visit(pers, st, ds, rds, owner, fuel, i, &mut path, &rds[i as usize], ss)
    } else {
        sort_visit(pers, st, ds, rds, owner, fuel, i, &mut path, &Vec::new(), ss)
    }
}

/// con-leche: ConLeche/Driver/Reach.lean:904-913 sortFrom
/// Every record placed, in position order, each after its reads.
pub fn sort_from(pers: &PersTier, st: &mut AState, ds: &Vec<IDeclaration>, rds: &Vec<Vec<NIdx>>, owner: &HashMap2<NIdx, u64>, fuel: u64, ss: &mut SortSt) -> Result<(), CheckError> {
    let mut i = 0usize;
    while i < ds.len() {
        match sort_from_one(pers, st, ds, rds, owner, fuel, i as u64, ss) {
            Err(e) => return Err(e),
            Ok(()) => {}
        }
        i += 1;
    }
    Ok(())
}

/// con-leche: ConLeche/Driver/Reach.lean:915-919 readOrder
/// **The context's records in read order**: their positions, each record after
/// the records storing what it reads (`rds`); a cycle among their reads is
/// malformed input.
pub fn read_order(pers: &PersTier, st: &mut AState, ds: &Vec<IDeclaration>, rds: &Vec<Vec<NIdx>>) -> Result<Vec<u64>, CheckError> {
    let owner = match owner_map(pers, st, ds) {
        Err(e) => return Err(e),
        Ok(m) => m,
    };
    let mut ss = SortSt { order: Vec::new(), placed: HashMap2::new() };
    match sort_from(pers, st, ds, rds, &owner, ds.len() as u64 + 1, &mut ss) {
        Err(e) => Err(e),
        Ok(()) => Ok(ss.order),
    }
}

// ---------------------------------------------------------------------------
// The reach
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Driver/Reach.lean:923-930 Reach
/// **What the reach gives**: the context's records with their homes, the
/// completed names with the homes that located them, its counts, and the
/// statements whose inference `infer_flags` runs after the freeze.
pub struct Reach {
    pub ctx: Vec<IDeclaration>,
    pub homes: Vec<NIdx>,
    pub completed: Vec<(NIdx, NIdx)>,
    pub searches: u64,
    pub inferred: u64,
    pub pending: Vec<(Vec<u32>, NIdx, StmtRec)>,
}

/// con-leche: ConLeche/Driver/Reach.lean:932-961 reach
/// The roots and the clashing names, the own names left out.
pub fn reach_roots(own: &HashMap2<NIdx, bool>, roots: &Vec<NIdx>, extra: &Vec<NIdx>) -> Vec<NIdx> {
    let mut out: Vec<NIdx> = Vec::with_capacity(roots.len() + extra.len());
    let mut i = 0usize;
    while i < roots.len() {
        if !own.contains_key(&roots[i]) {
            out.push(roots[i].dup2());
        }
        i += 1;
    }
    let mut j = 0usize;
    while j < extra.len() {
        if !own.contains_key(&extra[j]) {
            out.push(extra[j].dup2());
        }
        j += 1;
    }
    out
}

/// con-leche: ConLeche/Driver/Reach.lean:932-961 reach
/// The first root no loaded module holds.
pub fn first_unloaded(wr: &WorkerReads, rs: &Vec<NIdx>) -> Option<usize> {
    let mut i = 0usize;
    while i < rs.len() {
        if !wr.index.first.contains_key(&rs[i]) {
            return Some(i);
        }
        i += 1;
    }
    None
}

/// con-leche: ConLeche/Driver/Reach.lean:932-961 reach
/// The records at the read order's positions, with their homes.
pub fn in_read_order(l: &ReachLog, o: &Vec<u64>) -> (Vec<IDeclaration>, Vec<NIdx>) {
    let mut ctx: Vec<IDeclaration> = Vec::with_capacity(o.len());
    let mut homes: Vec<NIdx> = Vec::with_capacity(o.len());
    let mut i = 0usize;
    while i < o.len() {
        let j = o[i] as usize;
        if j < l.ctx.len() && j < l.homes.len() {
            ctx.push(env::i_declaration_dup(&l.ctx[j]));
            homes.push(l.homes[j].dup2());
        }
        i += 1;
    }
    (ctx, homes)
}

/// con-leche: ConLeche/Driver/Reach.lean:932-961 reach
/// **The reach of module `m`** from the names its own records read (`roots`):
/// the clash rule's keys, the worklist, the read order, the context's
/// validation.  The inferred flags are `infer_flags`'s, after the freeze.
pub fn reach<F: OleanFs>(fs: &F, pk: &OleanPins, pers: &PersTier, st: &mut AState, sp: &files::Roots, m: &NIdx, wr: &WorkerReads, own: &HashMap2<NIdx, bool>, roots: &Vec<NIdx>) -> Result<Reach, CheckError> {
    let env = ReachEnv { module: m.dup2(), copies: clash_copies_of(pk, wr) };
    let mut c = reach_cache_empty();
    let extra = match clash_agree(fs, pk, pers, st, sp, wr, &mut c, &wr.clashes) {
        Err(e) => return Err(e),
        Ok(x) => x,
    };
    let rs = reach_roots(own, roots, &extra);
    match first_unloaded(wr, &rs) {
        Some(i) => return Err(reads_which(pers, st, m, &rs[i], { const M: [u32; 24] = [110, 111, 32, 109, 111, 100, 117, 108, 101, 32, 105, 116, 32, 108, 111, 97, 100, 115, 32, 104, 111, 108, 100, 115]; core_types::code_points(&M) })),
        None => {}
    }
    let mut l = reach_log_init(&rs);
    let fuel = wr.index.first.len() as u64 + wr.index.more.len() as u64 + (1 << 24);
    match reach_go(fs, pk, pers, st, sp, wr, own, &env, &mut l, &mut c, fuel) {
        Err(e) => return Err(e),
        Ok(()) => {}
    }
    let o = match read_order(pers, st, &l.ctx, &l.reads) {
        Err(e) => return Err(e),
        Ok(o) => o,
    };
    let (ctx, homes) = in_read_order(&l, &o);
    match validate_ctx(pers, st, &ctx, &homes) {
        Err(e) => return Err(e),
        Ok(()) => {}
    }
    let inferred = c.pending.len() as u64;
    Ok(Reach { ctx, homes, completed: c.completed, searches: c.searches, inferred, pending: c.pending })
}
