//! `ConLeche/Frontend/Olean/Records.lean` — the import closure as one record
//! stream (task #142).
//!
//! The reader's pipeline ends in the same records the stream parser produces, so
//! that everything after the parse is the stream path's.  **What is merged is what
//! lean4export exports**: the closure loaded at the private level, merged as Lean's
//! `finalizeImport` merges it, emitted in lean4export's order.
//!
//! A theorem's record holds a reference to its value (`lazy::value_ref`), which
//! its check reads ([`read_value`], upstream task #481), in a worker of the
//! check pool, into that worker's scratch tier.
//!
//! ## Deviations
//!
//! * `declOfF em.nm em.lv em.ex r` is `export_c::process_line_core_d` over a
//!   `StateD` whose name and expression tables ARE the emitter's: the stream
//!   parser's own record builder, which the port runs over tables of handles.
//!   There is no level table, as there is none upstream, since no `DeclRec`
//!   reads one.
//! * **`OleanRead` carries the reader's pins** (`pins`): a worker reads a value
//!   with the same interned names the load used, persistent handles.
//! * **The frontiers are moved out of the merge** into `values`, where upstream
//!   shares them: nothing of the merge reads a frontier.
//! * **A worker's cache is `&mut`** and `read_value` returns the value alone,
//!   where upstream threads `(ValueCache × Except ..)`; the cache a failure
//!   leaves is upstream's (`regionFor` resets it).  It holds the region with
//!   its bytes (`RegionBuf`), the Rust `Region` being the layout alone.
//! * `OleanRead.thmUses ... getD usedConsts`, the driver's `usedOf`, is
//!   `impl UsedConsts for OleanRead` here, a trait the core owns.

use crate::arena::env;
use crate::arena::env::IDeclaration;
use crate::arena::handle::{EIdx, NIdx};
use crate::arena::monad::AState;
use crate::frontend::nat_op_ground;
use crate::frontend::nat_op_ground::UsedConsts;
use crate::frontend::olean::files;
use crate::frontend::olean::lazy;
use crate::frontend::olean::region;
use crate::frontend::olean::region::RegionBuf;
use crate::frontend::olean::sparse;
use crate::frontend::olean::sparse::Frontier;
use crate::frontend::olean::spec::RdErr;
use crate::frontend::olean::view::{ModFiles, OLeanLevel, ViewBytes};
use crate::ron::hashmap::Dup;
use crate::arena::store::{EStore, PersTier};
use crate::frontend::export_c;
use crate::frontend::export_c::{ParseResultD, StateD};
use crate::frontend::olean::closure;
use crate::frontend::olean::emit;
use crate::frontend::olean::emit::Emit;
use crate::frontend::olean::files::OleanFs;
use crate::frontend::olean::merge;
use crate::frontend::olean::merge::Merged;
use crate::frontend::olean::spec;
use crate::frontend::olean::view;
use crate::frontend::scan_types;
use crate::frontend::scan_types::{DeclRec, IdTable};
use crate::frontend::text;
use crate::kernel::core_types;
use crate::kernel::core_types::CheckError;
use crate::ron::hashmap;

/// con-leche: ConLeche/Frontend/Olean/Records.lean:36-40 Emit.nm
/// con-leche: ConLeche/Frontend/Olean/Records.lean:45-49 Emit.ex
/// A table of the emitter's, as the stream reader's table.
pub fn table_of<T>(dense: Vec<T>) -> IdTable<T> {
    IdTable { dense, sparse: hashmap::HashMap::new() }
}

/// con-leche: ConLeche/Frontend/Olean/Records.lean:51-59 declsGo
/// `declsOf`'s walk.
pub fn decls_go(pers: &PersTier, ar: &EStore, st: &mut StateD, out: &Vec<DeclRec>) -> Result<(), (CheckError, u64)> {
    let mut k = 0usize;
    while k < out.len() {
        match export_c::process_line_core_d(pers, ar, st, &out[k]) {
            Err(e) => return Err(export_c::line_err_to_check(e, k as u64)),
            Ok(()) => {}
        }
        k += 1;
    }
    Ok(())
}

/// con-leche: ConLeche/Frontend/Olean/Records.lean:42-43 Emit.lv
/// con-leche: ConLeche/Frontend/Olean/Records.lean:61-65 declsOf
/// **The `Declaration` records**, through the stream reader's builder.  A record's
/// verdict is the stream path's, at the record's position.
pub fn decls_of(pers: &PersTier, ar: &EStore, em: Emit) -> Result<ParseResultD, (CheckError, u64)> {
    let mut st = StateD {
        names: table_of::<NIdx>(em.names),
        levels: scan_types::id_table_empty(),
        exprs: table_of::<EIdx>(em.exprs),
        decls: Vec::new(),
    };
    match decls_go(pers, ar, &mut st, &em.out) {
        Err(e) => Err(e),
        Ok(()) => Ok(export_c::parse_result_of_state(st)),
    }
}

/// con-leche: ConLeche/Frontend/Olean/Records.lean:67-74 rootConstants
/// `cs.find? (!mg.map.contains ·)`, as a position (`cs.len()`: none).
pub fn first_absent(mg: &Merged, cs: &Vec<NIdx>) -> usize {
    let mut i = 0usize;
    while i < cs.len() {
        if !merge::mg_has(mg, &cs[i]) {
            return i;
        }
        i += 1;
    }
    i
}

/// con-leche: ConLeche/Frontend/Olean/Records.lean:67-74 rootConstants
/// The constants the emission starts from: the named ones, each of which the
/// closure must hold, or all of them.
pub fn root_constants(pers: &PersTier, ar: &EStore, mg: &Merged, constants: &Option<Vec<NIdx>>) -> Result<Vec<NIdx>, CheckError> {
    match constants {
        None => Ok(crate::arena::env::nidx_vec_dup(&mg.order)),
        Some(cs) => {
            let i = first_absent(mg, cs);
            if i < cs.len() {
                let t = text::cat({ const M: [u32; 13] = [116, 104, 101, 32, 99, 111, 110, 115, 116, 97, 110, 116, 32]; crate::kernel::core_types::code_points(&M) }, &view::name_text(pers, ar, &cs[i]));
                Err(core_types::internal(text::cat(t, &{ const M: [u32; 29] = [32, 105, 115, 32, 110, 111, 116, 32, 105, 110, 32, 116, 104, 101, 32, 105, 109, 112, 111, 114, 116, 32, 99, 108, 111, 115, 117, 114, 101]; crate::kernel::core_types::code_points(&M) })))
            } else {
                Ok(crate::arena::env::nidx_vec_dup(cs))
            }
        }
    }
}

/// con-leche: ConLeche/Frontend/Olean/Records.lean:76-79 ModRef
/// What a theorem's check needs of a module of the closure's order.
pub struct ModRef {
    pub name: NIdx,
    pub frontier: Frontier,
}

/// con-leche: ConLeche/Frontend/Olean/Records.lean:83-89 OleanRead
/// **What a read gives**: the records, a theorem's value as its reference; what
/// its check needs to read it, by the reference's module; the merged constants,
/// for what a value mentions; and the reader's pins (module note).
pub struct OleanRead {
    pub decls: Vec<IDeclaration>,
    pub values: Vec<ModRef>,
    pub merged: Merged,
    pub pins: spec::OleanPins,
}

/// con-leche: ConLeche/Frontend/Olean/Records.lean:91-95 OleanRead.thmUses
/// con-leche: CHANGED since 701d72ae — re-port, re-test, re-prove records::olean_read_thm_uses_refines, then delete this line
/// **What a theorem's record mentions**, which its reference does not say: what
/// the load read off the file.  `None` for any other record.
pub fn olean_read_thm_uses(rd: &OleanRead, d: &IDeclaration) -> Option<Vec<NIdx>> {
    match d {
        IDeclaration::ThmDecl(cv, _) => match merge::mg_get(&rd.merged, &cv.name) {
            Some(c) => Some(env::nidx_vec_dup(&c.uses)),
            None => None,
        },
        _ => None,
    }
}

/// con-leche: ConLeche/Driver/CheckMain.lean:100-104 usedOf
/// What a record mentions, for the preparation of an `.olean` read: the
/// record's expressions say it, except a theorem's, whose load read it off the
/// file.  Pass `&rd` as `prepare::prepare_d`'s `used_of`.
impl UsedConsts for OleanRead {
    /// con-leche: ConLeche/Driver/CheckMain.lean:100-104 usedOf
    fn used_consts(&self, pers: &PersTier, st: &mut AState, d: &IDeclaration) -> Result<Vec<NIdx>, CheckError> {
        match olean_read_thm_uses(self, d) {
            Some(u) => Ok(u),
            None => nat_op_ground::decl_used_consts(pers, st, d),
        }
    }
}

/// con-leche: ConLeche/Frontend/Olean/Records.lean:97-122 readOleans
/// The frontiers, moved out of the loaded modules: `ls.map fun l => ⟨l.name,
/// l.frontier⟩` (module note).
pub fn mod_refs(mg: &mut Merged) -> Vec<ModRef> {
    let mut out: Vec<ModRef> = Vec::with_capacity(mg.ls.len());
    let mut i = 0usize;
    while i < mg.ls.len() {
        let fr = core::mem::replace(&mut mg.ls[i].frontier, sparse::frontier_empty());
        out.push(ModRef { name: mg.ls[i].name.dup2(), frontier: fr });
        i += 1;
    }
    out
}

/// con-leche: ConLeche/Frontend/Olean/Records.lean:97-122 readOleans
/// **The whole read**: load, merge, emit, build, the heartbeat saying each step
/// (`OleanFs::read_notes_say`).  `constants` names the constants to start from,
/// as lean4export's arguments after `--` do; `None` is every constant of the
/// closure.  A theorem's value is a reference.
pub fn read_oleans<F: OleanFs>(fs: &F, pers: &PersTier, ar: &mut EStore, sp: &Vec<Vec<u32>>, roots: &Vec<NIdx>, constants: &Option<Vec<NIdx>>) -> Result<OleanRead, (CheckError, u64)> {
    let pk = match spec::olean_pins(pers, ar) {
        Err(e) => return Err((e, 0)),
        Ok(p) => p,
    };
    let ls = match closure::load_closure(fs, &pk, pers, ar, sp, roots) {
        Err(e) => return Err((e, 0)),
        Ok(l) => l,
    };
    fs.read_notes_say(&text::cat3({ const M: [u32; 25] = [109, 101, 114, 103, 105, 110, 103, 32, 116, 104, 101, 32, 99, 111, 110, 115, 116, 97, 110, 116, 115, 32, 111, 102, 32]; crate::kernel::core_types::code_points(&M) }, &text::u64_str(ls.len() as u64), &{ const M: [u32; 8] = [32, 109, 111, 100, 117, 108, 101, 115]; crate::kernel::core_types::code_points(&M) }));
    let mut mg = match merge::merge_all(&pk, pers, ar, ls) {
        Err(e) => return Err((e, 0)),
        Ok(m) => m,
    };
    fs.read_notes_say(&text::cat3({ const M: [u32; 23] = [99, 104, 101, 99, 107, 105, 110, 103, 32, 116, 104, 101, 32, 98, 108, 111, 99, 107, 115, 32, 111, 102, 32]; crate::kernel::core_types::code_points(&M) }, &text::u64_str(mg.order.len() as u64), &{ const M: [u32; 10] = [32, 99, 111, 110, 115, 116, 97, 110, 116, 115]; crate::kernel::core_types::code_points(&M) }));
    match emit::blocks_ok(&pk, pers, ar, &mg) {
        Err(e) => return Err((e, 0)),
        Ok(()) => {}
    }
    let cs = match root_constants(pers, ar, &mg, constants) {
        Err(e) => return Err((e, 0)),
        Ok(cs) => cs,
    };
    fs.read_notes_say(&text::cat3({ const M: [u32; 22] = [101, 109, 105, 116, 116, 105, 110, 103, 32, 114, 101, 99, 111, 114, 100, 115, 32, 102, 114, 111, 109, 32]; crate::kernel::core_types::code_points(&M) }, &text::u64_str(cs.len() as u64), &{ const M: [u32; 10] = [32, 99, 111, 110, 115, 116, 97, 110, 116, 115]; crate::kernel::core_types::code_points(&M) }));
    let em = match emit::emit_all(&pk, &mg, &cs) {
        Err(e) => return Err((e, 0)),
        Ok(em) => em,
    };
    match decls_of(pers, ar, em) {
        Err(e) => Err(e),
        Ok(ds) => {
            let values = mod_refs(&mut mg);
            Ok(OleanRead { decls: ds.decls, values, merged: mg, pins: pk })
        }
    }
}

/// con-leche: ConLeche/Frontend/Olean/Records.lean:126-131 ValueCache
/// **What a worker keeps between its checks**: the region of the module it read
/// last, with its bytes.  One per worker of the check pool.
pub struct ValueCache {
    pub idx: u64,
    pub region: Option<RegionBuf>,
}

/// con-leche: ConLeche/Frontend/Olean/Records.lean:126-131 ValueCache
/// The empty cache (the structure's defaults): a worker's initial state.
pub fn value_cache_empty() -> ValueCache {
    ValueCache { idx: 0, region: None }
}

/// con-leche: ConLeche/Frontend/Olean/Records.lean:133-148 regionFor
/// `f.viewRegion .private`, owned: the bytes moved out of the files.
pub fn owned_view(f: ModFiles, vb: ViewBytes) -> RegionBuf {
    match vb {
        ViewBytes::Joined(b) => b,
        ViewBytes::Exported => {
            let r = region::region_single(&f.exported);
            RegionBuf { bytes: f.exported.bytes, region: r }
        }
    }
}

/// con-leche: ConLeche/Frontend/Olean/Records.lean:133-148 regionFor
/// The region of module `idx` (named `m`), from the cache or the files, the
/// cache left to go on with: a failure empties it.
pub fn region_for<F: OleanFs>(fs: &F, pk: &spec::OleanPins, pers: &PersTier, ar: &mut EStore, sp: &Vec<Vec<u32>>, m: &NIdx, idx: u64, c: &mut ValueCache) -> Result<(), CheckError> {
    let hit = match &c.region {
        Some(_) => c.idx == idx,
        None => false,
    };
    if hit {
        return Ok(());
    }
    match files::read_files(fs, pers, ar, sp, m, &OLeanLevel::Private) {
        Err(e) => {
            *c = value_cache_empty();
            Err(e)
        }
        Ok(f) => match view::mod_files_view_region(&f, &OLeanLevel::Private) {
            None => {
                let e = view::view_error(pk, pers, ar, m, &f, &OLeanLevel::Private);
                *c = value_cache_empty();
                Err(e)
            }
            Some((vb, _)) => {
                *c = ValueCache { idx, region: Some(owned_view(f, vb)) };
                Ok(())
            }
        },
    }
}

/// con-leche: ConLeche/Frontend/Olean/Records.lean:150-162 readValue
/// **A theorem's value, from its reference's code**: the files of its module
/// (`region_for`, the worker's cache `c`), then the value, over the module's
/// frontier (`sparse::frontier_expr`), interned into `ar`: a worker's store,
/// so its scratch tier.  `pk` is the read's (`OleanRead.pins`).
pub fn read_value<F: OleanFs>(fs: &F, pk: &spec::OleanPins, pers: &PersTier, ar: &mut EStore, sp: &Vec<Vec<u32>>, values: &Vec<ModRef>, c: &mut ValueCache, code: u64) -> Result<EIdx, CheckError> {
    let i = lazy::ref_module(code);
    if !(i < (values.len() as u64)) {
        let t = text::cat3({ const M: [u32; 28] = [97, 32, 116, 104, 101, 111, 114, 101, 109, 39, 115, 32, 118, 97, 108, 117, 101, 32, 105, 110, 32, 109, 111, 100, 117, 108, 101, 32]; crate::kernel::core_types::code_points(&M) }, &text::u64_str(i), &{ const M: [u32; 5] = [44, 32, 111, 102, 32]; crate::kernel::core_types::code_points(&M) });
        return Err(core_types::internal(text::cat(t, &text::u64_str(values.len() as u64))));
    }
    let md = &values[i as usize];
    match region_for(fs, pk, pers, ar, sp, &md.name, i, c) {
        Err(e) => Err(e),
        Ok(()) => match &c.region {
            None => Err(view::undecodable(pers, ar, &md.name)),
            Some(rb) => match sparse::frontier_expr(pk, pers, ar, &rb.bytes, &rb.region, &md.frontier, lazy::ref_loc(code)) {
                Ok(e) => Ok(e),
                Err(RdErr::Err(e)) => Err(e),
                Err(RdErr::Bad) => Err(view::undecodable(pers, ar, &md.name)),
            },
        },
    }
}

/// con-leche: ConLeche/Frontend/Olean/Records.lean:164-171 fillRecord
/// A record with its theorem's value read, if it is a theorem's whose value is a
/// reference.
pub fn fill_record<F: OleanFs>(fs: &F, pk: &spec::OleanPins, pers: &PersTier, ar: &mut EStore, sp: &Vec<Vec<u32>>, values: &Vec<ModRef>, c: &mut ValueCache, d: &IDeclaration) -> Result<IDeclaration, CheckError> {
    match d {
        IDeclaration::ThmDecl(cv, v) => match ar.view_bvar(pers, v) {
            Some(code) => match read_value(fs, pk, pers, ar, sp, values, c, code) {
                Err(e) => Err(e),
                Ok(e) => Ok(IDeclaration::ThmDecl(env::i_constant_val_dup(cv), e)),
            },
            None => Ok(env::i_declaration_dup(d)),
        },
        _ => Ok(env::i_declaration_dup(d)),
    }
}

/// con-leche: ConLeche/Frontend/Olean/Records.lean:173-180 fillRecords
/// `fillRecord` of each record, in order, one cache.
pub fn fill_records<F: OleanFs>(fs: &F, pk: &spec::OleanPins, pers: &PersTier, ar: &mut EStore, sp: &Vec<Vec<u32>>, values: &Vec<ModRef>, ds: &Vec<IDeclaration>) -> Result<Vec<IDeclaration>, CheckError> {
    let mut c = value_cache_empty();
    let mut acc: Vec<IDeclaration> = Vec::with_capacity(ds.len());
    let mut i = 0usize;
    while i < ds.len() {
        match fill_record(fs, pk, pers, ar, sp, values, &mut c, &ds[i]) {
            Err(e) => return Err(e),
            Ok(d) => acc.push(d),
        }
        i += 1;
    }
    Ok(acc)
}

/// con-leche: ConLeche/Frontend/Olean/Records.lean:182-192 readOleansFull
/// **The records with every theorem's value read**, for the tools that compare
/// them: the checker itself reads a value in its check.
pub fn read_oleans_full<F: OleanFs>(fs: &F, pers: &PersTier, ar: &mut EStore, sp: &Vec<Vec<u32>>, roots: &Vec<NIdx>, constants: &Option<Vec<NIdx>>) -> Result<Vec<IDeclaration>, (CheckError, u64)> {
    match read_oleans(fs, pers, ar, sp, roots, constants) {
        Err(e) => Err(e),
        Ok(rd) => match fill_records(fs, &rd.pins, pers, ar, sp, &rd.values, &rd.decls) {
            Err(e) => Err((e, 0)),
            Ok(ds) => Ok(ds),
        },
    }
}
