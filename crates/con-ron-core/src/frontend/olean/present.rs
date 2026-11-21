//! `ConLeche/Frontend/Olean/Present.lean` — an imported constant as a context
//! record (task #166).
//!
//! What the reach of a module reads of one constant of its context: its read
//! from a part of a view with one memo per part (`entry_with`, `stmt_with`) —
//! a constant whole, or its statement and its kind without expressions (a
//! theorem's value is never read: the opaque cut) — and a constant as its
//! record, through the stream reader's builder (`record_of_entry`).
//!
//! Deviation: the memo is `&mut`, where upstream threads it through the
//! answer; a read that fails leaves it as `reads::memo_add` does.

use crate::arena::env;
use crate::arena::env::IDeclaration;
use crate::arena::handle::{EIdx, NIdx};
use crate::arena::store::{EStore, PersTier};
use crate::frontend::olean::emit;
use crate::frontend::olean::emit::Emit;
use crate::frontend::olean::fast;
use crate::frontend::olean::lazy::CEntry;
use crate::frontend::olean::reads;
use crate::frontend::olean::records;
use crate::frontend::olean::region::Region;
use crate::frontend::olean::sparse;
use crate::frontend::olean::spec;
use crate::frontend::olean::spec::{CEntryF, CKindF, OleanPins, RdErr, StmtRec};
use crate::frontend::olean::view;
use crate::frontend::text;
use crate::kernel::core_types;
use crate::kernel::core_types::CheckError;
use crate::ron::hashmap::Dup;
use crate::ron::hashmap2::HashMap2;

/// con-leche: ConLeche/Frontend/Olean/Present.lean:25-30 entryWith
/// **The constant at location `c`, read with the part's memo**, which it
/// extends.
pub fn entry_with(pk: &OleanPins, pers: &PersTier, ar: &mut EStore, bs: &[u8], r: &Region, st: &mut sparse::SM, c: u64) -> Result<CEntryF<NIdx, EIdx>, RdErr> {
    match spec::const_skel(bs, r, c) {
        None => Err(RdErr::Bad),
        Some(sk) => match spec::skel_fits(&sk) {
            Err(e) => Err(e),
            Ok(()) => match reads::memo_roots(pk, pers, ar, bs, r, st, &sk) {
                Err(e) => Err(RdErr::Err(e)),
                Ok(()) => spec::c_entry_map(&reads::MemoRead { st: &*st }, pk, pers, ar, bs, r, &sk),
            },
        },
    }
}

/// con-leche: ConLeche/Frontend/Olean/Present.lean:32-42 stmtWith
/// The statement's roots into the memo: the name and the level parameters,
/// then the type.
pub fn stmt_roots(pk: &OleanPins, pers: &PersTier, ar: &mut EStore, bs: &[u8], r: &Region, st: &mut sparse::SM, sk: &CEntryF<u64, u64>) -> Result<(), CheckError> {
    let mut names: Vec<u64> = Vec::with_capacity(1 + sk.level_params.len());
    names.push(sk.name);
    fast::push_all(&sk.level_params, &mut names);
    match reads::memo_add_all(pk, pers, ar, bs, r, fast::K_NAME, st, &names) {
        Err(e) => Err(e),
        Ok(()) => reads::memo_add(pk, pers, ar, bs, r, fast::K_EXPR, st, sk.ty),
    }
}

/// con-leche: ConLeche/Frontend/Olean/Present.lean:32-42 stmtWith
/// **The statement and the kind of the constant at location `c`**, its kind's
/// expressions left out, read with the part's memo: a theorem's value is never
/// read.
pub fn stmt_with(pk: &OleanPins, pers: &PersTier, ar: &mut EStore, bs: &[u8], r: &Region, st: &mut sparse::SM, c: u64) -> Result<(StmtRec, CKindF<NIdx, ()>), RdErr> {
    let sk = match spec::const_skel(bs, r, c) {
        None => return Err(RdErr::Bad),
        Some(sk) => sk,
    };
    match spec::skel_fits(&sk) {
        Err(e) => return Err(e),
        Ok(()) => {}
    }
    match stmt_roots(pk, pers, ar, bs, r, st, &sk) {
        Err(e) => return Err(RdErr::Err(e)),
        Ok(()) => {}
    }
    let rd = reads::MemoRead { st: &*st };
    let n = match reads::memo_name(pk, pers, ar, bs, r, rd.st, sk.name) {
        Err(e) => return Err(e),
        Ok(n) => n,
    };
    let lps = match spec::names_map(&rd, pk, pers, ar, bs, r, &sk.level_params) {
        Err(e) => return Err(e),
        Ok(l) => l,
    };
    let ty = match reads::memo_expr(pk, pers, ar, bs, r, rd.st, sk.ty) {
        Err(e) => return Err(e),
        Ok(t) => t,
    };
    match reads::c_kind_names(&rd, pk, pers, ar, bs, r, &sk.kind) {
        Err(e) => Err(e),
        Ok(k) => Ok((StmtRec { name: n, level_params: lps, ty }, k)),
    }
}

/// con-leche: ConLeche/Frontend/Olean/Present.lean:46-53 recordOfEntry
/// **One constant's record**, through the stream reader's builder (`Emit.one`,
/// `declsOf`).
pub fn record_of_entry(pers: &PersTier, ar: &EStore, c: CEntryF<NIdx, EIdx>) -> Result<IDeclaration, CheckError> {
    let mut em = Emit { visited: HashMap2::new(), names: Vec::new(), exprs: Vec::new(), out: Vec::new() };
    let nm: NIdx = c.name.dup2();
    emit::emit_one(&mut em, &CEntry { c, uses: Vec::new() });
    match records::decls_of(pers, ar, em) {
        Err((e, _)) => Err(e),
        Ok(pr) => {
            if pr.decls.len() == 1 {
                Ok(env::i_declaration_dup(&pr.decls[0]))
            } else {
                let t = text::cat({ const M: [u32; 13] = [116, 104, 101, 32, 99, 111, 110, 115, 116, 97, 110, 116, 32]; crate::kernel::core_types::code_points(&M) }, &view::name_text(pers, ar, &nm));
                Err(core_types::internal(text::cat3(t, &{ const M: [u32; 2] = [58, 32]; crate::kernel::core_types::code_points(&M) }, &text::cat(text::u64_str(pr.decls.len() as u64), &{ const M: [u32; 8] = [32, 114, 101, 99, 111, 114, 100, 115]; crate::kernel::core_types::code_points(&M) }))))
            }
        }
    }
}
