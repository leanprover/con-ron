//! `ConLeche/Frontend/Olean/Group.lean` — one inductive group's record (task
//! #166).
//!
//! An importer presents an imported inductive group as its record, whole, as
//! its home's emission builds it: `group_record` validates the group as
//! `emit::blocks_ok` validates a merged closure (`emit::block_step` of each of
//! its names) and emits it alone (`emit::emit_block`), through the stream
//! reader's builder (`records::decls_of`).
//!
//! ## Deviations
//!
//! * **`group_parts` gives names**, which `emit::emit_block` takes, where
//!   upstream's gives the entries (`emit`'s module note: the merge holds
//!   positions).
//! * **A merge of a list** (`merged_of_list`) is one loaded module holding the
//!   entries kept, named by the anonymous name, with no frontier
//!   (`merge::Merged` owns its modules).
//! * `readGroup` is not ported: only upstream's tests call it (the reach reads
//!   a group by its own `groupAt`).

use crate::arena::env;
use crate::arena::env::IDeclaration;
use crate::arena::handle::NIdx;
use crate::arena::store::{EStore, PersTier};
use crate::frontend::olean::emit;
use crate::frontend::olean::emit::Emit;
use crate::frontend::olean::lazy::{CEntry, Loaded};
use crate::frontend::olean::merge;
use crate::frontend::olean::merge::Merged;
use crate::frontend::olean::records;
use crate::frontend::olean::sparse;
use crate::frontend::olean::spec::{CKindF, OleanPins};
use crate::frontend::olean::view;
use crate::frontend::text;
use crate::kernel::core_types;
use crate::kernel::core_types::CheckError;
use crate::ron::hashmap::Dup;
use crate::ron::hashmap2::HashMap2;

/// con-leche: ConLeche/Frontend/Olean/Group.lean:31-35 mergedOfList
/// **Some constants as a merge**, in their order (each name once: the first
/// copy kept).
pub fn merged_of_list(pk: &OleanPins, cs: &Vec<CEntry>) -> Merged {
    let mut map: HashMap2<NIdx, (usize, usize)> = HashMap2::with_capacity(cs.len());
    let mut order: Vec<NIdx> = Vec::with_capacity(cs.len());
    let mut kept: Vec<CEntry> = Vec::with_capacity(cs.len());
    let mut i = 0usize;
    while i < cs.len() {
        let n: NIdx = cs[i].c.name.dup2();
        if !map.contains_key(&n) {
            map.insert(n.dup2(), (0, kept.len()));
            order.push(n);
            kept.push(c_entry_dup(&cs[i]));
        }
        i += 1;
    }
    let mut ls: Vec<Loaded> = Vec::with_capacity(1);
    ls.push(Loaded { name: pk.anon.dup2(), constants: kept, frontier: sparse::frontier_empty() });
    Merged { ls, map, order }
}

/// con-leche: ConLeche/Frontend/Olean/Group.lean:31-35 mergedOfList
/// An entry, copied (its handles).
pub fn c_entry_dup(c: &CEntry) -> CEntry {
    CEntry { c: view::c_entry_dup(&c.c), uses: env::nidx_vec_dup(&c.uses) }
}

/// con-leche: ConLeche/Frontend/Olean/Group.lean:37-48 groupParts
/// The constants of `n`'s group the emission takes, if `n` is a stored
/// inductive type: its block's members, their constructors, the recursors under
/// `n`.
pub fn group_parts(mg: &Merged, n: &NIdx) -> Option<(Vec<NIdx>, Vec<NIdx>, Vec<NIdx>)> {
    match merge::mg_get(mg, n) {
        None => None,
        Some(c) => match &c.c.kind {
            CKindF::Induct(_, _, all, _, _, _, _, _) => {
                let tys = emit::block_tys(mg, all);
                let ctors = emit::block_ctors(mg, &tys);
                let recs = emit::block_recs(mg, &emit::rec_map_of(mg), n);
                Some((tys, ctors, recs))
            }
            _ => None,
        },
    }
}

/// con-leche: ConLeche/Frontend/Olean/Group.lean:50-51 groupEmit
/// The emission of `n`'s group alone.
pub fn group_emit(mg: &Merged, tys: &Vec<NIdx>, ctors: &Vec<NIdx>, recs: &Vec<NIdx>) -> Emit {
    let mut em = Emit { visited: HashMap2::new(), names: Vec::new(), exprs: Vec::new(), out: Vec::new() };
    emit::emit_block(&mut em, mg, tys, ctors, recs);
    em
}

/// con-leche: ConLeche/Frontend/Olean/Group.lean:53-69 groupRecord
/// `blockStep` of each of some names.
pub fn block_steps(pk: &OleanPins, pers: &PersTier, ar: &EStore, mg: &Merged, ns: &Vec<NIdx>) -> Result<(), CheckError> {
    let mut i = 0usize;
    while i < ns.len() {
        match emit::block_step(pk, pers, ar, mg, &ns[i]) {
            Err(e) => return Err(e),
            Ok(()) => {}
        }
        i += 1;
    }
    Ok(())
}

/// con-leche: ConLeche/Frontend/Olean/Group.lean:53-69 groupRecord
/// `the inductive group of {n}: …`.
pub fn group_bad(pers: &PersTier, ar: &EStore, n: &NIdx, what: &Vec<u32>) -> CheckError {
    let t = text::cat({ const M: [u32; 23] = [116, 104, 101, 32, 105, 110, 100, 117, 99, 116, 105, 118, 101, 32, 103, 114, 111, 117, 112, 32, 111, 102, 32]; crate::kernel::core_types::code_points(&M) }, &view::name_text(pers, ar, n));
    core_types::internal(text::cat3(t, &{ const M: [u32; 2] = [58, 32]; crate::kernel::core_types::code_points(&M) }, what))
}

/// con-leche: ConLeche/Frontend/Olean/Group.lean:53-69 groupRecord
/// **One inductive group's record, validated**: `n`'s group as the emission
/// builds it, after `blockStep` of `n` and of each of the group's constants.
pub fn group_record(pk: &OleanPins, pers: &PersTier, ar: &EStore, mg: &Merged, n: &NIdx) -> Result<IDeclaration, CheckError> {
    match group_parts(mg, n) {
        None => Err(group_bad(pers, ar, n, &text::cat(view::name_text(pers, ar, n), &{ const M: [u32; 31] = [32, 105, 115, 32, 110, 111, 116, 32, 97, 32, 115, 116, 111, 114, 101, 100, 32, 105, 110, 100, 117, 99, 116, 105, 118, 101, 32, 116, 121, 112, 101]; crate::kernel::core_types::code_points(&M) }))),
        Some((tys, ctors, recs)) => {
            let mut ns: Vec<NIdx> = Vec::with_capacity(1 + tys.len() + ctors.len() + recs.len());
            ns.push(n.dup2());
            let mut i = 0usize;
            while i < tys.len() {
                ns.push(tys[i].dup2());
                i += 1;
            }
            let mut j = 0usize;
            while j < ctors.len() {
                ns.push(ctors[j].dup2());
                j += 1;
            }
            let mut k = 0usize;
            while k < recs.len() {
                ns.push(recs[k].dup2());
                k += 1;
            }
            match block_steps(pk, pers, ar, mg, &ns) {
                Err(e) => Err(e),
                Ok(()) => match records::decls_of(pers, ar, group_emit(mg, &tys, &ctors, &recs)) {
                    Err((e, _)) => Err(e),
                    Ok(pr) => {
                        if pr.decls.len() == 1 {
                            Ok(env::i_declaration_dup(&pr.decls[0]))
                        } else if pr.decls.len() == 0 {
                            Err(group_bad(pers, ar, n, &{ const M: [u32; 9] = [110, 111, 32, 114, 101, 99, 111, 114, 100]; crate::kernel::core_types::code_points(&M) }))
                        } else {
                            Err(group_bad(pers, ar, n, &text::cat(text::u64_str(pr.decls.len() as u64), &{ const M: [u32; 8] = [32, 114, 101, 99, 111, 114, 100, 115]; crate::kernel::core_types::code_points(&M) })))
                        }
                    }
                },
            }
        }
    }
}
