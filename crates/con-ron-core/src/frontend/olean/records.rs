//! `ConLeche/Frontend/Olean/Records.lean` — the import closure as one record
//! stream (task #142).
//!
//! The reader's pipeline ends in the same records the stream parser produces, so
//! that everything after the parse is the stream path's.  **What is merged is what
//! lean4export exports**: the closure loaded at the private level, merged as Lean's
//! `finalizeImport` merges it, emitted in lean4export's order.
//!
//! Deviation: `declOfF em.nm em.lv em.ex r` is `export_c::process_line_core_d` over
//! a `StateD` whose name and expression tables ARE the emitter's: the stream
//! parser's own record builder, which the port runs over tables of handles.  There
//! is no level table, as there is none upstream, since no `DeclRec` reads one.

use crate::arena::handle::{EIdx, NIdx};
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

/// con-leche: ConLeche/Frontend/Olean/Records.lean:32-36 Emit.nm
/// con-leche: ConLeche/Frontend/Olean/Records.lean:41-45 Emit.ex
/// A table of the emitter's, as the stream reader's table.
pub fn table_of<T>(dense: Vec<T>) -> IdTable<T> {
    IdTable { dense, sparse: hashmap::HashMap::new() }
}

/// con-leche: ConLeche/Frontend/Olean/Records.lean:47-55 declsGo
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

/// con-leche: ConLeche/Frontend/Olean/Records.lean:57-61 declsOf
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

/// con-leche: ConLeche/Frontend/Olean/Records.lean:63-70 rootConstants
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

/// con-leche: ConLeche/Frontend/Olean/Records.lean:63-70 rootConstants
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

/// con-leche: ConLeche/Frontend/Olean/Records.lean:72-89 readOleans
/// `blocksOk`, `rootConstants` and the walk, over the merged closure.
pub fn emit_merged(pk: &spec::OleanPins, pers: &PersTier, ar: &EStore, mg: &Merged, constants: &Option<Vec<NIdx>>) -> Result<Emit, CheckError> {
    match emit::blocks_ok(pk, pers, ar, mg) {
        Err(e) => Err(e),
        Ok(()) => match root_constants(pers, ar, mg, constants) {
            Err(e) => Err(e),
            Ok(cs) => emit::emit_all(pk, mg, &cs),
        },
    }
}

/// con-leche: ConLeche/Frontend/Olean/Records.lean:72-89 readOleans
/// **The whole read**: load, merge, emit, build.  `constants` names the constants
/// to start from, as lean4export's arguments after `--` do; `None` is every
/// constant of the closure.
pub fn read_oleans<F: OleanFs>(fs: &F, pers: &PersTier, ar: &mut EStore, sp: &Vec<Vec<u32>>, roots: &Vec<NIdx>, constants: &Option<Vec<NIdx>>) -> Result<ParseResultD, (CheckError, u64)> {
    let pk = match spec::olean_pins(pers, ar) {
        Err(e) => return Err((e, 0)),
        Ok(p) => p,
    };
    let ls = match closure::load_closure(fs, &pk, pers, ar, sp, roots) {
        Err(e) => return Err((e, 0)),
        Ok(l) => l,
    };
    let mg = match merge::merge_all(&pk, pers, ar, ls) {
        Err(e) => return Err((e, 0)),
        Ok(m) => m,
    };
    let em = match emit_merged(&pk, pers, ar, &mg, constants) {
        Err(e) => return Err((e, 0)),
        Ok(em) => em,
    };
    decls_of(pers, ar, em)
}
