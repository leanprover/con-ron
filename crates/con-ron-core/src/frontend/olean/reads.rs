//! `ConLeche/Frontend/Olean/Reads.lean` — taking less of a region (task #142).
//!
//! The reads of a part of a `ModuleData`, at a region and an address.  Deviation:
//! `distinctGo` is at names, the one type it is used at, keyed by handle.

use crate::arena::handle::{EIdx, NIdx};
use crate::arena::store::{EStore, PersTier};
use crate::frontend::olean::fast;
use crate::frontend::olean::region;
use crate::frontend::olean::region::Region;
use crate::frontend::olean::sparse;
use crate::frontend::olean::spec;
use crate::frontend::olean::spec::{CEntryF, CKindF, ImportRec, OleanPins, RdErr, StmtRec};
use crate::frontend::text;
use crate::kernel::core_types::CheckError;
use crate::ron::hashmap::Dup;
use crate::ron::hashmap2::HashMap2;

/// con-leche: ConLeche/Frontend/Olean/Reads.lean:18-24 CKindF.skipped
/// lean4export's filter: unsafe and partial constants are not exported.
pub fn c_kind_skipped<N, E>(k: &CKindF<N, E>) -> bool {
    const S_SAFE: [u32; 4] = [115, 97, 102, 101];
    match k {
        CKindF::Ax(u) => *u,
        CKindF::Opaq(_, u) => *u,
        CKindF::Induct(_, _, _, _, _, _, u, _) => *u,
        CKindF::Ctor(_, _, _, _, u) => *u,
        CKindF::Recur(_, _, _, _, _, _, _, u) => *u,
        CKindF::Defn(_, _, s) => !text::cps_beq(s, &S_SAFE),
        CKindF::Thm(_, _) => false,
        CKindF::Quot(_) => false,
    }
}

/// con-leche: ConLeche/Frontend/Olean/Reads.lean:26-36 CKindF.tag
/// The constructor of a stored constant's kind, as `ConstantInfo` numbers them.
pub fn c_kind_tag<N, E>(k: &CKindF<N, E>) -> u64 {
    match k {
        CKindF::Ax(_) => 0,
        CKindF::Defn(_, _, _) => 1,
        CKindF::Thm(_, _) => 2,
        CKindF::Opaq(_, _) => 3,
        CKindF::Quot(_) => 4,
        CKindF::Induct(_, _, _, _, _, _, _, _) => 5,
        CKindF::Ctor(_, _, _, _, _) => 6,
        CKindF::Recur(_, _, _, _, _, _, _, _) => 7,
    }
}

/// con-leche: ConLeche/Frontend/Olean/Reads.lean:38-45 distinctGo
/// **No two the same**: the positions' names are distinct.
pub fn distinct_go(cs: &Vec<NamePosition>) -> bool {
    let mut s: HashMap2<NIdx, bool> = HashMap2::with_capacity(cs.len());
    let mut i = 0usize;
    while i < cs.len() {
        if s.contains_key(&cs[i].name) {
            return false;
        }
        s.insert(cs[i].name.dup2(), true);
        i += 1;
    }
    true
}

/// con-leche: ConLeche/Frontend/Olean/Reads.lean:49-53 ModHeader
/// A module's flag and imports.
pub struct ModHeader {
    pub is_module: bool,
    pub imports: Vec<ImportRec>,
}

/// con-leche: ConLeche/Frontend/Olean/Reads.lean:55-63 NamePosition
/// What `namePositionsAt` takes of one stored constant.
pub struct NamePosition {
    pub loc: u64,
    pub name: NIdx,
    pub tag: u64,
    pub skipped: bool,
}

/// con-leche: ConLeche/Frontend/Olean/Reads.lean:65-69 NamePositions
/// **The name positions** of a module.
pub struct NamePositions {
    pub header: ModHeader,
    pub consts: Vec<NamePosition>,
}

/// con-leche: ConLeche/Frontend/Olean/Reads.lean:71-74 namePosition
/// One constant's position and name.
pub fn name_position(pk: &OleanPins, pers: &PersTier, ar: &mut EStore, bs: &[u8], r: &Region, c: u64) -> Result<NamePosition, RdErr> {
    match spec::const_skel(bs, r, c) {
        None => Err(RdErr::Bad),
        Some(s) => match spec::name_p(pk, pers, ar, bs, r, s.name) {
            Err(e) => Err(e),
            Ok(n) => Ok(NamePosition { loc: c, name: n, tag: c_kind_tag(&s.kind), skipped: c_kind_skipped(&s.kind) }),
        },
    }
}

/// con-leche: ConLeche/Frontend/Olean/Reads.lean:76-84 namePositionsAt
/// `sk.consts.mapM (namePosition r)`.
pub fn name_positions_go(pk: &OleanPins, pers: &PersTier, ar: &mut EStore, bs: &[u8], r: &Region, consts: &Vec<u64>) -> Result<Vec<NamePosition>, RdErr> {
    let mut out: Vec<NamePosition> = Vec::with_capacity(consts.len());
    let mut i = 0usize;
    while i < consts.len() {
        match name_position(pk, pers, ar, bs, r, consts[i]) {
            Err(e) => return Err(e),
            Ok(p) => out.push(p),
        }
        i += 1;
    }
    Ok(out)
}

/// con-leche: ConLeche/Frontend/Olean/Reads.lean:76-84 namePositionsAt
/// `sk.imports.mapM (ImportF.mapM (nameP r))`.
pub fn imports_named(pk: &OleanPins, pers: &PersTier, ar: &mut EStore, bs: &[u8], r: &Region, imports: &Vec<spec::ImportF<u64>>) -> Result<Vec<ImportRec>, RdErr> {
    let mut out: Vec<ImportRec> = Vec::with_capacity(imports.len());
    let mut i = 0usize;
    while i < imports.len() {
        match spec::import_map(&crate::frontend::olean::header::NamePRead, pk, pers, ar, bs, r, &imports[i]) {
            Err(e) => return Err(e),
            Ok(x) => out.push(x),
        }
        i += 1;
    }
    Ok(out)
}

/// con-leche: ConLeche/Frontend/Olean/Reads.lean:76-84 namePositionsAt
/// **The name positions**: no expression of the module is read.  A name two
/// constants bear fails it.
pub fn name_positions_at(pk: &OleanPins, pers: &PersTier, ar: &mut EStore, bs: &[u8], r: &Region, root: u64) -> Result<NamePositions, RdErr> {
    match spec::module_skel(bs, r, root) {
        None => Err(RdErr::Bad),
        Some(sk) => match imports_named(pk, pers, ar, bs, r, &sk.imports) {
            Err(e) => Err(e),
            Ok(imports) => match name_positions_go(pk, pers, ar, bs, r, &sk.consts) {
                Err(e) => Err(e),
                Ok(cs) => {
                    if distinct_go(&cs) {
                        Ok(NamePositions { header: ModHeader { is_module: sk.is_module, imports }, consts: cs })
                    } else {
                        Err(RdErr::Bad)
                    }
                }
            },
        },
    }
}

/// con-leche: ConLeche/Frontend/Olean/Reads.lean:86-88 entryAt
/// **The constant at location `c`**, read with a memo of its own.
pub fn entry_at(pk: &OleanPins, pers: &PersTier, ar: &mut EStore, bs: &[u8], r: &Region, c: u64) -> Result<CEntryF<NIdx, EIdx>, RdErr> {
    match spec::const_skel(bs, r, c) {
        None => Err(RdErr::Bad),
        Some(s) => match spec::skel_fits(&s) {
            Err(e) => Err(e),
            Ok(()) => sparse::sparse_entry(pk, pers, ar, bs, r, &s),
        },
    }
}

/// con-leche: ConLeche/Frontend/Olean/Reads.lean:90-92 stmtsAt
/// **The statements of the constants at some locations**, read together.
pub fn stmts_at(pk: &OleanPins, pers: &PersTier, ar: &mut EStore, bs: &[u8], r: &Region, cs: &Vec<u64>) -> Result<Vec<StmtRec>, RdErr> {
    match fast::consts_skel(bs, r, cs) {
        Err(e) => Err(e),
        Ok(sks) => fast::stmts_fast(pk, pers, ar, bs, r, &sks),
    }
}

/// con-leche: ConLeche/Frontend/Olean/Reads.lean:96-104 memoAdd
/// One root read into a memo shared by several constants (`sGo`, no
/// frontier).  Deviation: a root that does not read leaves the memo EMPTY,
/// where upstream keeps what was read of it; a memo is speed alone, and the
/// root is read again by the build, on its own, which fails alike.
pub fn memo_add(pk: &OleanPins, pers: &PersTier, ar: &mut EStore, bs: &[u8], r: &Region, k: u8, st: &mut sparse::SM, v: u64) -> Result<(), CheckError> {
    match region::region_loc(r, v) {
        None => Ok(()),
        Some(c) => match sparse::s_go(pk, pers, ar, bs, r, &sparse::frontier_empty(), k, c, st) {
            Ok(()) => Ok(()),
            Err(RdErr::Bad) => {
                *st = sparse::sm_empty();
                Ok(())
            }
            Err(RdErr::Err(e)) => Err(e),
        },
    }
}

/// con-leche: ConLeche/Frontend/Olean/Reads.lean:96-104 memoAdd
/// `vs.foldl (memoAdd r k) st`.
pub fn memo_add_all(pk: &OleanPins, pers: &PersTier, ar: &mut EStore, bs: &[u8], r: &Region, k: u8, st: &mut sparse::SM, vs: &Vec<u64>) -> Result<(), CheckError> {
    let mut i = 0usize;
    while i < vs.len() {
        match memo_add(pk, pers, ar, bs, r, k, st, vs[i]) {
            Err(e) => return Err(e),
            Ok(()) => {}
        }
        i += 1;
    }
    Ok(())
}

/// con-leche: ConLeche/Frontend/Olean/Reads.lean:106-108 memoRoots
/// The roots of a constant's skeleton into the memo: its names, then its
/// expressions.
pub fn memo_roots(pk: &OleanPins, pers: &PersTier, ar: &mut EStore, bs: &[u8], r: &Region, st: &mut sparse::SM, sk: &CEntryF<u64, u64>) -> Result<(), CheckError> {
    let mut names: Vec<u64> = Vec::new();
    fast::c_entry_names(sk, &mut names);
    let mut exprs: Vec<u64> = Vec::new();
    fast::c_entry_exprs(sk, &mut exprs);
    match memo_add_all(pk, pers, ar, bs, r, fast::K_NAME, st, &names) {
        Err(e) => Err(e),
        Ok(()) => memo_add_all(pk, pers, ar, bs, r, fast::K_EXPR, st, &exprs),
    }
}

/// con-leche: ConLeche/Frontend/Olean/Reads.lean:110-118 memoName
/// A name pointer by the memo, else read on its own (`sparseNameP`).
pub fn memo_name(pk: &OleanPins, pers: &PersTier, ar: &mut EStore, bs: &[u8], r: &Region, st: &sparse::SM, v: u64) -> Result<NIdx, RdErr> {
    if v == 1 {
        return Ok(pk.anon.dup2());
    }
    match region::region_loc(r, v) {
        None => Err(RdErr::Bad),
        Some(c) => match st.names.get(&c) {
            Some(n) => Ok(n.dup2()),
            None => sparse::sparse_name_p(pk, pers, ar, bs, r, v),
        },
    }
}

/// con-leche: ConLeche/Frontend/Olean/Reads.lean:120-127 memoExpr
/// An expression pointer by the memo, else read on its own (`sparseExprP`).
pub fn memo_expr(pk: &OleanPins, pers: &PersTier, ar: &mut EStore, bs: &[u8], r: &Region, st: &sparse::SM, v: u64) -> Result<EIdx, RdErr> {
    match region::region_loc(r, v) {
        None => Err(RdErr::Bad),
        Some(c) => match st.exprs.get(&c) {
            Some(e) => Ok(e.dup2()),
            None => sparse::sparse_expr_p(pk, pers, ar, bs, r, v),
        },
    }
}

/// con-leche: ConLeche/Frontend/Olean/Reads.lean:129-135 entriesAt
/// The two reads of `CEntryF.mapM (memoName r st) (memoExpr r st)`, as a
/// pointer read.
pub struct MemoRead<'a> {
    pub st: &'a sparse::SM,
}

/// con-leche: ConLeche/Frontend/Olean/Reads.lean:129-135 entriesAt
impl<'a> spec::PtrRead for MemoRead<'a> {
    /// con-leche: ConLeche/Frontend/Olean/Reads.lean:110-118 memoName
    fn rd_name(&self, pk: &OleanPins, pers: &PersTier, ar: &mut EStore, bs: &[u8], r: &Region, v: u64) -> Result<NIdx, RdErr> {
        memo_name(pk, pers, ar, bs, r, self.st, v)
    }

    /// con-leche: ConLeche/Frontend/Olean/Reads.lean:120-127 memoExpr
    fn rd_expr(&self, pk: &OleanPins, pers: &PersTier, ar: &mut EStore, bs: &[u8], r: &Region, v: u64) -> Result<EIdx, RdErr> {
        memo_expr(pk, pers, ar, bs, r, self.st, v)
    }
}

/// con-leche: ConLeche/Frontend/Olean/Reads.lean:137-142 kindNamesAt
/// A kind's names read, its expressions left out (`s.kind.mapM rd (fun _ =>
/// some ())`).
pub fn c_kind_names<R: spec::PtrRead>(rd: &R, pk: &OleanPins, pers: &PersTier, ar: &mut EStore, bs: &[u8], r: &Region, k: &CKindF<u64, u64>) -> Result<CKindF<NIdx, ()>, RdErr> {
    match k {
        CKindF::Ax(u) => Ok(CKindF::Ax(*u)),
        CKindF::Defn(_, h, s) => Ok(CKindF::Defn((), spec::hints_dup(h), crate::kernel::expr::str_copy(s))),
        CKindF::Thm(_, all) => match spec::names_map(rd, pk, pers, ar, bs, r, all) {
            Err(e) => Err(e),
            Ok(a) => Ok(CKindF::Thm((), a)),
        },
        CKindF::Opaq(_, u) => Ok(CKindF::Opaq((), *u)),
        CKindF::Quot(s) => Ok(CKindF::Quot(crate::kernel::expr::str_copy(s))),
        CKindF::Induct(np, ni, all, cs, nn, ir, iu, irf) => match spec::names_map(rd, pk, pers, ar, bs, r, all) {
            Err(e) => Err(e),
            Ok(a) => match spec::names_map(rd, pk, pers, ar, bs, r, cs) {
                Err(e) => Err(e),
                Ok(c) => Ok(CKindF::Induct(*np, *ni, a, c, *nn, *ir, *iu, *irf)),
            },
        },
        CKindF::Ctor(ind, ci, np, nf, iu) => match rd.rd_name(pk, pers, ar, bs, r, *ind) {
            Err(e) => Err(e),
            Ok(i) => Ok(CKindF::Ctor(i, *ci, *np, *nf, *iu)),
        },
        CKindF::Recur(all, np, ni, nmo, nmi, rules, k2, iu) => match spec::names_map(rd, pk, pers, ar, bs, r, all) {
            Err(e) => Err(e),
            Ok(a) => match rule_names(rd, pk, pers, ar, bs, r, rules) {
                Err(e) => Err(e),
                Ok(rs) => Ok(CKindF::Recur(a, *np, *ni, *nmo, *nmi, rs, *k2, *iu)),
            },
        },
    }
}

/// con-leche: ConLeche/Frontend/Olean/Reads.lean:137-142 kindNamesAt
/// A recursor's rules, their constructors' names read, their right-hand sides
/// left out.
pub fn rule_names<R: spec::PtrRead>(rd: &R, pk: &OleanPins, pers: &PersTier, ar: &mut EStore, bs: &[u8], r: &Region, rs: &Vec<(u64, u64, u64)>) -> Result<Vec<(NIdx, u64, ())>, RdErr> {
    let mut out: Vec<(NIdx, u64, ())> = Vec::with_capacity(rs.len());
    let mut i = 0usize;
    while i < rs.len() {
        match rd.rd_name(pk, pers, ar, bs, r, rs[i].0) {
            Err(e) => return Err(e),
            Ok(n) => out.push((n, rs[i].1, ())),
        }
        i += 1;
    }
    Ok(out)
}

/// con-leche: ConLeche/Frontend/Olean/Reads.lean:137-142 kindNamesAt
/// **The kind of the constant at location `c`, its expressions left out**: what
/// Lean's `subsumesInfo` reads of a kind beside the statement.
pub fn kind_names_at(pk: &OleanPins, pers: &PersTier, ar: &mut EStore, bs: &[u8], r: &Region, c: u64) -> Result<CKindF<NIdx, ()>, RdErr> {
    match spec::const_skel(bs, r, c) {
        None => Err(RdErr::Bad),
        Some(s) => match spec::skel_fits(&s) {
            Err(e) => Err(e),
            Ok(()) => c_kind_names(&sparse::SparseRead, pk, pers, ar, bs, r, &s.kind),
        },
    }
}

/// con-leche: ConLeche/Frontend/Olean/View.lean:169-174 readKinds
/// `cs.mapM (kindNamesAt r)`.
pub fn kinds_at(pk: &OleanPins, pers: &PersTier, ar: &mut EStore, bs: &[u8], r: &Region, cs: &Vec<u64>) -> Result<Vec<CKindF<NIdx, ()>>, RdErr> {
    let mut out: Vec<CKindF<NIdx, ()>> = Vec::with_capacity(cs.len());
    let mut i = 0usize;
    while i < cs.len() {
        match kind_names_at(pk, pers, ar, bs, r, cs[i]) {
            Err(e) => return Err(e),
            Ok(k) => out.push(k),
        }
        i += 1;
    }
    Ok(out)
}
