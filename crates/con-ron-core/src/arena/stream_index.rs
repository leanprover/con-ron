//! `arena::stream_index` — **the index of a stream, and a record's job**.
//!
//! The Rust twin of `proof/ConRon/Arena/StreamIndex.lean`, which is
//! con-leche's `Cached/StreamIndex.lean`.
//!
//! The stream's index is built once, after the parse and before any check,
//! from the records alone (`install::decl_constants`, `install::decl_tables`):
//! every constant with its counter, its position among all the constants of
//! the stream, and every table with its record's position.  It is never written
//! again: `checker::freeze_tier` moves it into the `PersTier`, the base every
//! worker reads by reference (`arena::env`'s `IFEnv` note).
//!
//! The name's FIRST entry wins.  A record whose name an earlier record took
//! sees that entry at its own view, so its check fails with "duplicate
//! declaration", in fold order.
//!
//! A record's **job** is its check at the view of its position
//! (`stream_index_view`): an empty layer over the index with everything from
//! that record on hidden.  The jobs read the frozen index and their own record,
//! so they run independently of one another.
//!
//! **The representation** (a deviation of layout, not of answers): con-leche's
//! `FBase.idx` maps a name to `(counter, constant)`; here every record's
//! constants are pushed onto `consts` in counter order, so a constant's slot IS
//! its counter, and `idx` maps a name to the counter of its first entry.  A
//! later entry of a taken name is stored and never indexed, as con-leche's
//! `insertIfNew` drops it.  `tbls` maps a structure's name to its first table's
//! `(record position, slot)`.
//!
//! **Interning.**  What a record installs is a function of the record, but in
//! the arena a function that builds terms interns them.  The index is built on
//! the driver's store before the freeze, with no scratch tier open, so every
//! handle it holds is persistent: the parse's, or appended here.

use crate::arena::check_decl::check_decl;
use crate::arena::core::{enter_record, leave_record};
use crate::arena::env::{i_constant_info_name, ifenv_layer, IConstantInfo, IDeclaration, IFEnv, IProjTable};
use crate::arena::handle::NIdx;
use crate::arena::install::{decl_constants, decl_tables};
use crate::arena::monad::AState;
use crate::arena::nat_op_pin_set::INatOpPinSet;
use crate::arena::store::PersTier;
use crate::kernel::core_types::{code_points, CheckError};
use crate::kernel::env::CheckMode;
use crate::ron::hashmap::Dup;
use crate::ron::hashmap2::HashMap2 as HashMap;

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `"`And` must be the standard `And`"`, as code points.
pub const M_AND_PIN: [u32; 32] = [
    96, 65, 110, 100, 96, 32, 109, 117, 115, 116, 32, 98, 101, 32, 116, 104, 101, 32, 115,
    116, 97, 110, 100, 97, 114, 100, 32, 96, 65, 110, 100, 96
];

/// con-leche: ConLeche/Cached/StreamIndex.lean:38-43 StreamIndex
/// con-leche: ConLeche/Kernel/FEnv.lean:27-39 FBase
/// Lean twin: `proof/ConRon/Arena/StreamIndex.lean:34-40 IStreamIndex` — the index
/// under construction, and finished: the frozen layer's constants and tables
/// (the module note's layout), each record's first counter, and the next
/// counter.  The layer's bounds are the reading layer's (`IFEnv.base_below`,
/// `IFEnv.base_below_rec`), the index itself being shared.
pub struct IStreamIndex {
    pub consts: Vec<IConstantInfo>,
    pub idx: HashMap<NIdx, u64>,
    pub tables: Vec<IProjTable>,
    pub tbls: HashMap<NIdx, (u64, u64)>,
    pub firsts: Vec<u64>,
    pub next: u64,
}

/// con-leche: none — a `ProjTable` copy; Lean's record is shared by value (DESIGN.md §3.2)
/// A table, copied: the index keeps its own, the record's list being dropped.
pub fn i_proj_table_dup(t: &IProjTable) -> IProjTable {
    IProjTable {
        struct_name: t.struct_name.dup2(),
        level_params: crate::arena::env::nidx_vec_dup(&t.level_params),
        num_params: t.num_params,
        ctor: t.ctor.dup2(),
        num_fields: t.num_fields,
        bodies: crate::arena::env::eidx_vec_dup(&t.bodies),
    }
}

/// con-leche: ConLeche/Cached/StreamIndex.lean:38-43 StreamIndex
/// Lean twin: `proof/ConRon/Arena/StreamIndex.lean:34-40 IStreamIndex` — the empty
/// index, con-leche's `{}`.
pub fn stream_index_empty() -> IStreamIndex {
    IStreamIndex {
        consts: Vec::new(),
        idx: HashMap::new(),
        tables: Vec::new(),
        tbls: HashMap::new(),
        firsts: Vec::new(),
        next: 0,
    }
}

/// con-leche: ConLeche/Cached/StreamIndex.lean:45-49 insertConsts
/// Lean twin: `proof/ConRon/Arena/StreamIndex.lean:42-47 insertConsts` — insert a
/// record's constants from counter `I.next` on, a name's first entry winning;
/// the cursor `i` walks the record's list.
pub fn insert_consts(ix: IStreamIndex, cs: Vec<IConstantInfo>, i: usize) -> IStreamIndex {
    if i >= cs.len() {
        ix
    } else {
        let mut ix = ix;
        let n: NIdx = i_constant_info_name(&cs[i]);
        if !ix.idx.contains_key(&n) {
            ix.idx.insert(n, ix.next);
        }
        ix.consts.push(crate::arena::env::i_constant_info_dup(&cs[i]));
        ix.next = ix.next + 1;
        insert_consts(ix, cs, i + 1)
    }
}

/// con-leche: ConLeche/Cached/StreamIndex.lean:51-55 insertTables
/// Lean twin: `proof/ConRon/Arena/StreamIndex.lean:49-54 insertTables` — insert a
/// record's tables at record position `r`, a name's first entry winning.
pub fn insert_tables(ix: IStreamIndex, r: u64, ts: Vec<IProjTable>, i: usize) -> IStreamIndex {
    if i >= ts.len() {
        ix
    } else {
        let mut ix = ix;
        let n: NIdx = ts[i].struct_name.dup2();
        if !ix.tbls.contains_key(&n) {
            let s: u64 = ix.tables.len() as u64;
            ix.tbls.insert(n, (r, s));
            ix.tables.push(i_proj_table_dup(&ts[i]));
        }
        insert_tables(ix, r, ts, i + 1)
    }
}

/// con-leche: ConLeche/Cached/StreamIndex.lean:57-62 StreamIndex.add
/// Lean twin: `proof/ConRon/Arena/StreamIndex.lean:56-65 IStreamIndex.add` — one
/// record into the index: its first counter, its constants, its tables at its
/// position.
pub fn stream_index_add(
    pers: &PersTier,
    st: &mut AState,
    ix: IStreamIndex,
    pd: &IDeclaration,
) -> Result<IStreamIndex, CheckError> {
    match decl_constants(pers, st, pd) {
        Err(e) => Err(e),
        Ok(cs) => match decl_tables(pers, st, pd) {
            Err(e) => Err(e),
            Ok(ts) => {
                let r: u64 = ix.firsts.len() as u64;
                let mut ix = ix;
                ix.firsts.push(ix.next);
                let ix2: IStreamIndex = insert_consts(ix, cs, 0);
                Ok(insert_tables(ix2, r, ts, 0))
            }
        },
    }
}

/// con-leche: ConLeche/Cached/StreamIndex.lean:64-66 buildIndex
/// Lean twin: `proof/ConRon/Arena/StreamIndex.lean:79-82 buildIndex` — **the index of
/// a stream**, the records folded in order from `i` on.  An `Err` is the
/// store's own failure (a term the install builds could not be interned), never
/// a verdict about the stream; it carries the position of the record whose
/// reading failed, for the error line.
pub fn build_index(
    pers: &PersTier,
    st: &mut AState,
    ix: IStreamIndex,
    ds: &Vec<IDeclaration>,
    i: usize,
) -> Result<IStreamIndex, (CheckError, u64)> {
    if i >= ds.len() {
        Ok(ix)
    } else {
        match stream_index_add(pers, st, ix, &ds[i]) {
            Err(e) => Err((e, i as u64)),
            Ok(ix2) => build_index(pers, st, ix2, ds, i + 1),
        }
    }
}

/// con-leche: ConLeche/Cached/StreamIndex.lean:68-72 StreamIndex.view
/// Lean twin: `proof/ConRon/Arena/StreamIndex.lean:84-89 IStreamIndex.view` — **the
/// view of record `k`**: no constants or tables of its own, the frozen index
/// visible below the record's first counter and its position.
pub fn stream_index_view(pers: &PersTier, k: u64) -> IFEnv {
    let c: u64 = if (k as usize) < pers.env.firsts.len() {
        pers.env.firsts[k as usize]
    } else {
        pers.env.next
    };
    ifenv_layer(c, k)
}

/// con-leche: ConLeche/Cached/StreamIndex.lean:74-81 recordJob
/// Lean twin: `proof/ConRon/Arena/StreamIndex.lean:91-99 recordCheck` — what the
/// fold's step asks of record `pd` at position `k`: the `And` pin, then the
/// record's check at its view.  `record_job` is this in its bracket; an
/// `--olean` run's job reads a theorem's value inside the same bracket first
/// and then calls this (con-leche's `oleanJobRun`).
pub fn record_check(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    pins: &Vec<INatOpPinSet>,
    k: u64,
    pd: &IDeclaration,
) -> Result<(), CheckError> {
    match crate::arena::basis::and_pin_ok(pers, st, pd) {
        Err(e) => Err(e),
        Ok(false) => Err(CheckError::Invalid(code_points(&M_AND_PIN))),
        Ok(true) => match check_decl(pers, st, mode, pins, stream_index_view(pers, k), pd) {
            Err(e) => Err(e),
            Ok(_) => Ok(()),
        },
    }
}

/// con-leche: ConLeche/Cached/StreamIndex.lean:74-81 recordJob
/// Lean twin: `proof/ConRon/Arena/StreamIndex.lean:101-109 recordJob` — **record `pd`'s
/// job, at position `k`**: `record_check` from fresh caches and an empty
/// scratch tier (`enter_record`, the cited `checkDeclStepC`'s fresh `{}`), the
/// tier emptied again after it on both paths.  Nothing the job builds outlives
/// it: the layer and the tier go.
pub fn record_job(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    pins: &Vec<INatOpPinSet>,
    k: u64,
    pd: &IDeclaration,
) -> Result<(), CheckError> {
    enter_record(st);
    let r: Result<(), CheckError> = record_check(pers, st, mode, pins, k, pd);
    leave_record(st);
    r
}
