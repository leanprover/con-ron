//! `ConLeche/Driver/Worker.lean` — **the worker: one module checked against
//! the records it is checked against** (task #166).
//!
//! `--olean --module -- M` checks the module `M` alone, in upstream's phases:
//!
//! 1. **The home** (`home_of`): `M`'s private view loaded (`lazy::load_view`,
//!    its theorems' values left in the file) and its three parts checked against
//!    each other (`module::check_views`).
//! 2. **The reads** (`index::worker_reads`): the header fixpoint, the name index
//!    of every loaded part, Lean's clash rule, freshness of `M`'s names.
//! 3. **The own records** (`own_records`): the loaded constants, unsafe and
//!    partial ones left out, emitted from every own constant.
//! 4. **The reach** (`reach::reach`): the context records, from the names the
//!    own records read (`roots_at`); their names distinct.  The ground hoist
//!    (`nat_op_ground::hoist_nat_op_ground`) moves a pinned `Nat` operation's
//!    ground ahead of it.
//! 5. **The jobs** (the driver's): the index of the context's records followed
//!    by the own records (`worker_decls`, `stream_index::build_index` from 0),
//!    and the own records' jobs alone, from position `WorkerRead::start` on.
//!
//! **A compared challenge** (`x`, the imports a run adds to its header: `import
//! all` of its solution): a record of the challenge some name of which a loaded
//! module stores is a **copy** (`copy_recs`), checked against the loaded
//! constant (`copy_check`); every other record is the challenge's own, and none
//! of them may be a hole (`own_holes_ok`).
//!
//! Representation: a name set is `HashMap2<NIdx, bool>`; upstream's `ownUses`
//! (`l.constants.find?`) reads a name index of the load (`OwnUses`); the
//! context's constants a copied block's recursors read are found through one
//! layer holding every context constant (`ctx_layer`, upstream's `ctxConst`
//! over `ownerMap`: the context's names are distinct, checked before).  The
//! theorems' values are read by the jobs from the home's files
//! (`WorkerRead::values`); upstream seeds every job worker with the home's
//! region, con-ron's workers start from the empty cache.

use crate::arena::basis;
use crate::arena::canon::i_constant_info_beq;
use crate::arena::env;
use crate::arena::env::{IConstantInfo, IConstantVal, IDeclaration, IFEnv};
use crate::arena::handle::{EIdx, NIdx};
use crate::arena::inductives::block_shape;
use crate::arena::inductives::iota_read;
use crate::arena::install;
use crate::arena::justify;
use crate::arena::monad::AState;
use crate::arena::nat_op_pin_set::INatOpPinSet;
use crate::arena::needs;
use crate::arena::pins;
use crate::arena::store::{EStore, PersTier};
use crate::arena::decl_check;
use crate::arena::core::{nat_div_mod_names, CORE_WALK_FUEL};
use crate::arena::inductives::positivity::mentions_any_const;
use crate::frontend::compare::{rec_key, rec_kind};
use crate::frontend::modular::reach;
use crate::frontend::modular::reach::Reach;
use crate::frontend::nat_op_ground;
use crate::frontend::nat_op_ground::UsedConsts;
use crate::frontend::olean::emit;
use crate::frontend::olean::files;
use crate::frontend::checker_io::CheckerFs;
use crate::frontend::olean::group;
use crate::frontend::olean::index;
use crate::frontend::olean::index::{NameIndex, WorkerReads};
use crate::frontend::olean::lazy;
use crate::frontend::olean::lazy::{CEntry, Loaded};
use crate::frontend::olean::levels::HeaderLoads;
use crate::frontend::olean::module;
use crate::frontend::olean::module::Expo;
use crate::frontend::olean::records;
use crate::frontend::olean::records::ModRef;
use crate::frontend::olean::sparse;
use crate::frontend::olean::spec;
use crate::frontend::olean::spec::{ImportRec, OleanPins};
use crate::frontend::olean::view;
use crate::frontend::olean::view::{ModFiles, OLeanLevel};
use crate::frontend::text;
use crate::kernel::core_types;
use crate::kernel::core_types::CheckError;
use crate::ron::hashmap::{Dup, Eq2};
use crate::ron::hashmap2::HashMap2;

/// con-leche: ConLeche/Frontend/Olean/Files.lean:385-394 homeOf
/// **A module's home**: its private view loaded (`load_view`, at module index
/// 0) and its three parts checked against each other (`check_views`).
pub fn home_of(pk: &OleanPins, pers: &PersTier, ar: &mut EStore, m: &NIdx, f: &ModFiles) -> Result<(Loaded, Vec<Expo>), CheckError> {
    let l = match lazy::load_view(pk, pers, ar, 0, m, f) {
        Err(e) => return Err(e),
        Ok(l) => l,
    };
    match module::check_views(pk, pers, ar, m, f, &l) {
        Err(e) => Err(e),
        Ok(expo) => Ok((l, expo)),
    }
}

/// con-leche: ConLeche/Driver/Worker.lean:44-51 ownRecords
/// `l.constants.toList.filter (!·.skipped)`, copied.
pub fn unskipped(cs: &Vec<CEntry>) -> Vec<CEntry> {
    let mut out: Vec<CEntry> = Vec::new();
    let mut i = 0usize;
    while i < cs.len() {
        if !lazy::c_entry_skipped(&cs[i]) {
            out.push(group::c_entry_dup(&cs[i]));
        }
        i += 1;
    }
    out
}

/// con-leche: ConLeche/Driver/Worker.lean:44-51 ownRecords
/// **A module's own records**: its loaded constants, unsafe and partial ones
/// left out, their inductive groups checked (`blocks_ok`), emitted from every
/// one of them; a name the emission meets that is not among them is a context
/// read.
pub fn own_records(pk: &OleanPins, pers: &PersTier, ar: &mut EStore, l: &Loaded) -> Result<Vec<IDeclaration>, (CheckError, u64)> {
    let mg = group::merged_of_list(pk, &unskipped(&l.constants));
    match emit::blocks_ok(pk, pers, ar, &mg) {
        Err(e) => return Err((e, 0)),
        Ok(()) => {}
    }
    match emit::emit_all(pk, &mg, &mg.order) {
        Err(e) => Err((e, 0)),
        Ok(em) => match records::decls_of(pers, ar, em) {
            Err(e) => Err(e),
            Ok(p) => Ok(p.decls),
        },
    }
}

/// con-leche: ConLeche/Driver/Worker.lean:53-66 pinGround
/// `go`: one expression's constants into the walk's visited set and names.
pub fn ground_go(pers: &PersTier, st: &AState, seen: &mut HashMap2<EIdx, bool>, acc: Vec<NIdx>, e: &EIdx) -> Result<Vec<NIdx>, CheckError> {
    nat_op_ground::used_consts_go(pers, st, seen, acc, CORE_WALK_FUEL, e)
}

/// con-leche: ConLeche/Driver/Worker.lean:53-66 pinGround
/// `es.foldl go x`.
pub fn ground_go_all(pers: &PersTier, st: &AState, seen: &mut HashMap2<EIdx, bool>, acc: Vec<NIdx>, es: &Vec<EIdx>) -> Result<Vec<NIdx>, CheckError> {
    let mut out = acc;
    let mut i = 0usize;
    while i < es.len() {
        match ground_go(pers, st, seen, out, &es[i]) {
            Err(e) => return Err(e),
            Ok(o) => out = o,
        }
        i += 1;
    }
    Ok(out)
}

/// con-leche: ConLeche/Driver/Worker.lean:53-66 pinGround
/// The certificates' statements: `(divModCertStmts c).foldl (fun x st => go
/// (st.1.foldl go x) st.2) x`.
pub fn ground_stmts(pers: &PersTier, st: &mut AState, seen: &mut HashMap2<EIdx, bool>, acc: Vec<NIdx>, c: &NIdx) -> Result<Vec<NIdx>, CheckError> {
    let stmts = match decl_check::div_mod_cert_stmts(pers, st, c) {
        Err(e) => return Err(e),
        Ok(s) => s,
    };
    let mut out = acc;
    let mut i = 0usize;
    while i < stmts.len() {
        match ground_stmt(pers, st, seen, out, &stmts[i]) {
            Err(e) => return Err(e),
            Ok(o) => out = o,
        }
        i += 1;
    }
    Ok(out)
}

/// con-leche: ConLeche/Driver/Worker.lean:53-66 pinGround
/// One statement: `go (st.1.foldl go x) st.2`.
pub fn ground_stmt(pers: &PersTier, st: &AState, seen: &mut HashMap2<EIdx, bool>, acc: Vec<NIdx>, s: &(Vec<EIdx>, EIdx)) -> Result<Vec<NIdx>, CheckError> {
    match ground_go_all(pers, st, seen, acc, &s.0) {
        Err(e) => Err(e),
        Ok(o) => ground_go(pers, st, seen, o, &s.1),
    }
}

/// con-leche: ConLeche/Driver/Worker.lean:53-66 pinGround
/// One pin variant: its pinned defining expression, its certificates' proofs,
/// then each type pin's name and type.
pub fn ground_variant(pers: &PersTier, st: &mut AState, seen: &mut HashMap2<EIdx, bool>, acc: Vec<NIdx>, ps: &INatOpPinSet, c: &NIdx) -> Result<Vec<NIdx>, CheckError> {
    let dp = match decl_check::div_mod_decl_pin(st, ps, c) {
        Err(e) => return Err(e),
        Ok(d) => d,
    };
    let a1 = match ground_go(pers, st, seen, acc, &dp) {
        Err(e) => return Err(e),
        Ok(a) => a,
    };
    let proofs = match decl_check::div_mod_cert_proofs(st, ps, c) {
        Err(e) => return Err(e),
        Ok(p) => p,
    };
    let a2 = match ground_go_all(pers, st, seen, a1, &proofs) {
        Err(e) => return Err(e),
        Ok(a) => a,
    };
    let tps: &Vec<(NIdx, EIdx)> = match decl_check::div_mod_type_pins(st, ps, c) {
        Err(e) => return Err(e),
        Ok(t) => t,
    };
    let mut out = a2;
    let mut i = 0usize;
    while i < tps.len() {
        out.push(tps[i].0.dup2());
        match ground_go(pers, st, seen, out, &tps[i].1) {
            Err(e) => return Err(e),
            Ok(o) => out = o,
        }
        i += 1;
    }
    Ok(out)
}

/// con-leche: ConLeche/Driver/Worker.lean:53-66 pinGround
/// **A certified operation's pin ground**: the names its install check asks
/// resolved beyond `pin_footprint`, over every pin variant of `pins`: the
/// constants of the certificates' statements, of the variant's pinned defining
/// expression and certificates' proofs, its type pins' names and types, and
/// `Eq`.  Empty at every other name.
pub fn pin_ground(pers: &PersTier, st: &mut AState, pins: &Vec<INatOpPinSet>, c: &NIdx) -> Result<Vec<NIdx>, CheckError> {
    let dms = match nat_div_mod_names(st) {
        Err(e) => return Err(e),
        Ok(d) => d,
    };
    if !env::nidx_vec_contains(&dms, c) {
        return Ok(Vec::new());
    }
    let eq = match pins::pin_eq(st) {
        Err(e) => return Err(e),
        Ok(n) => n,
    };
    let mut seen: HashMap2<EIdx, bool> = HashMap2::new();
    let mut acc: Vec<NIdx> = Vec::new();
    acc.push(eq);
    let mut out = match ground_stmts(pers, st, &mut seen, acc, c) {
        Err(e) => return Err(e),
        Ok(o) => o,
    };
    let mut i = 0usize;
    while i < pins.len() {
        match ground_variant(pers, st, &mut seen, out, &pins[i], c) {
            Err(e) => return Err(e),
            Ok(o) => out = o,
        }
        i += 1;
    }
    Ok(out)
}

/// con-leche: ConLeche/Driver/Worker.lean:68-86 ownRoots
/// `fp`: every name a loaded constant's fast path reads (`pin_footprint`).
pub fn footprints(st: &mut AState, cs: &Vec<CEntry>) -> Result<HashMap2<NIdx, bool>, CheckError> {
    let mut s: HashMap2<NIdx, bool> = HashMap2::new();
    let mut i = 0usize;
    while i < cs.len() {
        match needs::pin_footprint(st, &cs[i].c.name) {
            Err(e) => return Err(e),
            Ok(ns) => {
                let mut k = 0usize;
                while k < ns.len() {
                    s.insert(ns[k].dup2(), true);
                    k += 1;
                }
            }
        }
        i += 1;
    }
    Ok(s)
}

/// con-leche: ConLeche/Driver/Worker.lean:68-86 ownRoots
/// `xs.filter (fun x => ix.first.contains x || !fp.contains x)` pushed onto `out`.
pub fn push_unpinned(out: &mut Vec<NIdx>, ix: &NameIndex, fp: &HashMap2<NIdx, bool>, xs: &Vec<NIdx>) {
    let mut i = 0usize;
    while i < xs.len() {
        if ix.first.contains_key(&xs[i]) || !fp.contains_key(&xs[i]) {
            out.push(xs[i].dup2());
        }
        i += 1;
    }
}

/// con-leche: ConLeche/Driver/Worker.lean:68-86 ownRoots
/// `xs.filter ix.first.contains` pushed onto `out`.
pub fn push_loaded(out: &mut Vec<NIdx>, ix: &NameIndex, xs: &Vec<NIdx>) {
    let mut i = 0usize;
    while i < xs.len() {
        if ix.first.contains_key(&xs[i]) {
            out.push(xs[i].dup2());
        }
        i += 1;
    }
}

/// con-leche: ConLeche/Driver/Worker.lean:68-86 ownRoots
/// **The reach's roots**: what each own record reads (`record_reads`), what
/// each own constant's load read, and the pin ground of each own certified
/// operation that a loaded module holds; an unsafe or partial own constant is
/// no record, and what it reads is no root.  A name a pinned own constant's
/// fast path reads that no loaded module holds is left to that constant's own
/// check.  `cs`: the load's constants (upstream's `l.constants`).
pub fn own_roots(pers: &PersTier, st: &mut AState, pins: &Vec<INatOpPinSet>, ix: &NameIndex, cs: &Vec<CEntry>, ds: &Vec<IDeclaration>) -> Result<Vec<NIdx>, CheckError> {
    let fp = match footprints(st, cs) {
        Err(e) => return Err(e),
        Ok(f) => f,
    };
    let mut out = match records_roots(pers, st, ix, &fp, ds) {
        Err(e) => return Err(e),
        Ok(o) => o,
    };
    let mut k = 0usize;
    while k < cs.len() {
        if !lazy::c_entry_skipped(&cs[k]) {
            push_unpinned(&mut out, ix, &fp, &cs[k].uses);
        }
        k += 1;
    }
    match ground_roots(pers, st, pins, ix, cs, out) {
        Err(e) => Err(e),
        Ok(o) => Ok(o),
    }
}

/// con-leche: ConLeche/Driver/Worker.lean:68-86 ownRoots
/// What each own record reads, filtered (`push_unpinned`).
pub fn records_roots(pers: &PersTier, st: &mut AState, ix: &NameIndex, fp: &HashMap2<NIdx, bool>, ds: &Vec<IDeclaration>) -> Result<Vec<NIdx>, CheckError> {
    let mut out: Vec<NIdx> = Vec::new();
    let mut i = 0usize;
    while i < ds.len() {
        match reach::record_reads(pers, st, &ds[i]) {
            Err(e) => return Err(e),
            Ok(rs) => push_unpinned(&mut out, ix, fp, &rs),
        }
        i += 1;
    }
    Ok(out)
}

/// con-leche: ConLeche/Driver/Worker.lean:68-86 ownRoots
/// The pin ground of each own constant, filtered (`push_loaded`), onto `out`.
pub fn ground_roots(pers: &PersTier, st: &mut AState, pins: &Vec<INatOpPinSet>, ix: &NameIndex, cs: &Vec<CEntry>, out: Vec<NIdx>) -> Result<Vec<NIdx>, CheckError> {
    let mut out = out;
    let mut j = 0usize;
    while j < cs.len() {
        if !lazy::c_entry_skipped(&cs[j]) {
            match pin_ground(pers, st, pins, &cs[j].c.name) {
                Err(e) => return Err(e),
                Ok(g) => push_loaded(&mut out, ix, &g),
            }
        }
        j += 1;
    }
    Ok(out)
}

/// con-leche: ConLeche/Driver/Worker.lean:88-95 ownUses
/// **What an own theorem's record mentions**, which its reference does not
/// say: what the load read off the file (for the ground hoist).  `at` indexes
/// the load's constants by name, the first of each (upstream's `find?`).
pub struct OwnUses<'a> {
    pub cs: &'a Vec<CEntry>,
    pub at: HashMap2<NIdx, u64>,
}

/// con-leche: ConLeche/Driver/Worker.lean:88-95 ownUses
/// The index of a load's constants by name, the first of each.
pub fn own_uses_of(cs: &Vec<CEntry>) -> OwnUses<'_> {
    let mut at: HashMap2<NIdx, u64> = HashMap2::new();
    let mut i = 0usize;
    while i < cs.len() {
        if !at.contains_key(&cs[i].c.name) {
            at.insert(cs[i].c.name.dup2(), i as u64);
        }
        i += 1;
    }
    OwnUses { cs, at }
}

/// con-leche: ConLeche/Driver/Worker.lean:88-95 ownUses
/// A theorem's load-read names: the first constant of its name's `uses`.
pub fn own_uses_thm(u: &OwnUses<'_>, n: &NIdx) -> Option<Vec<NIdx>> {
    match u.at.get(n) {
        Some(i) => {
            if (*i as usize) < u.cs.len() {
                Some(env::nidx_vec_dup(&u.cs[*i as usize].uses))
            } else {
                None
            }
        }
        None => None,
    }
}

/// con-leche: ConLeche/Driver/Worker.lean:88-95 ownUses
impl UsedConsts for OwnUses<'_> {
    /// con-leche: ConLeche/Driver/Worker.lean:88-95 ownUses
    fn used_consts(&self, pers: &PersTier, st: &mut AState, d: &IDeclaration) -> Result<Vec<NIdx>, CheckError> {
        match d {
            IDeclaration::ThmDecl(cv, _) => match own_uses_thm(self, &cv.name) {
                Some(u) => Ok(u),
                None => nat_op_ground::decl_used_consts(pers, st, d),
            },
            _ => nat_op_ground::decl_used_consts(pers, st, d),
        }
    }
}

/// con-leche: ConLeche/Driver/Worker.lean:97-99 ownNames
/// **A module's own names**: every constant of its private view, unsafe and
/// partial ones included (no context record may hold one).
pub fn own_names(cs: &Vec<CEntry>) -> HashMap2<NIdx, bool> {
    let mut s: HashMap2<NIdx, bool> = HashMap2::new();
    let mut i = 0usize;
    while i < cs.len() {
        s.insert(cs[i].c.name.dup2(), true);
        i += 1;
    }
    s
}

/// con-leche: ConLeche/Driver/Worker.lean:101-104 namesNodupGo
/// **No name twice**, one hash set along the list from `i` on.
pub fn names_nodup_go(s: &mut HashMap2<NIdx, bool>, ns: &Vec<NIdx>, i: usize) -> bool {
    let mut k = i;
    while k < ns.len() {
        if s.contains_key(&ns[k]) {
            return false;
        }
        s.insert(ns[k].dup2(), true);
        k += 1;
    }
    true
}

/// con-leche: ConLeche/Driver/Worker.lean:301-344 workerRead
/// `namesNodupGo {} (r.ctx.toList.flatMap Modular.declNames)`.
pub fn ctx_names_nodup(pers: &PersTier, st: &mut AState, ctx: &Vec<IDeclaration>) -> Result<bool, CheckError> {
    let mut s: HashMap2<NIdx, bool> = HashMap2::new();
    let mut i = 0usize;
    while i < ctx.len() {
        match reach::decl_names(pers, st, &ctx[i]) {
            Err(e) => return Err(e),
            Ok(ns) => {
                if !names_nodup_go(&mut s, &ns, 0) {
                    return Ok(false);
                }
            }
        }
        i += 1;
    }
    Ok(true)
}

/// con-leche: ConLeche/Driver/Worker.lean:125-126 loadedRec
/// **A record some name of which a loaded module stores.**
pub fn loaded_rec(pers: &PersTier, st: &mut AState, ix: &NameIndex, d: &IDeclaration) -> Result<bool, CheckError> {
    match reach::decl_names(pers, st, d) {
        Err(e) => Err(e),
        Ok(ns) => Ok(any_loaded(ix, &ns)),
    }
}

/// con-leche: ConLeche/Driver/Worker.lean:125-126 loadedRec
/// `ns.any ix.first.contains`.
pub fn any_loaded(ix: &NameIndex, ns: &Vec<NIdx>) -> bool {
    let mut i = 0usize;
    while i < ns.len() {
        if ix.first.contains_key(&ns[i]) {
            return true;
        }
        i += 1;
    }
    false
}

/// con-leche: ConLeche/Driver/Worker.lean:128-136 ownRecs
/// The emitted records some name of which is loaded (`want`), or none is.
pub fn recs_loaded(pers: &PersTier, st: &mut AState, ix: &NameIndex, ds: &Vec<IDeclaration>, want: bool) -> Result<Vec<IDeclaration>, CheckError> {
    let mut out: Vec<IDeclaration> = Vec::new();
    let mut i = 0usize;
    while i < ds.len() {
        match loaded_rec(pers, st, ix, &ds[i]) {
            Err(e) => return Err(e),
            Ok(b) => {
                if b == want {
                    out.push(env::i_declaration_dup(&ds[i]));
                }
            }
        }
        i += 1;
    }
    Ok(out)
}

/// con-leche: ConLeche/Driver/Worker.lean:128-131 ownRecs
/// **The own records** of a worker that adds the imports `x`, before the
/// hoist: every emitted record; at a compared challenge (`x` not empty), those
/// no name of which is loaded.
pub fn own_recs(pers: &PersTier, st: &mut AState, x: &Vec<ImportRec>, ix: &NameIndex, ds: Vec<IDeclaration>) -> Result<Vec<IDeclaration>, CheckError> {
    if x.len() == 0 {
        Ok(ds)
    } else {
        recs_loaded(pers, st, ix, &ds, false)
    }
}

/// con-leche: ConLeche/Driver/Worker.lean:133-136 copyRecs
/// **The copies**: none, but at a compared challenge, the emitted records some
/// name of which is loaded.
pub fn copy_recs(pers: &PersTier, st: &mut AState, x: &Vec<ImportRec>, ix: &NameIndex, ds: &Vec<IDeclaration>) -> Result<Vec<IDeclaration>, CheckError> {
    if x.len() == 0 {
        Ok(Vec::new())
    } else {
        recs_loaded(pers, st, ix, ds, true)
    }
}

/// con-leche: ConLeche/Driver/Worker.lean:138-142 ownNamesOf
/// **The own names** of a worker that adds the imports `x`: every constant of
/// the private view; at a compared challenge, those no loaded module stores.
pub fn own_names_of(x: &Vec<ImportRec>, ix: &NameIndex, cs: &Vec<CEntry>) -> HashMap2<NIdx, bool> {
    if x.len() == 0 {
        own_names(cs)
    } else {
        let mut s: HashMap2<NIdx, bool> = HashMap2::new();
        let mut i = 0usize;
        while i < cs.len() {
            if !ix.first.contains_key(&cs[i].c.name) {
                s.insert(cs[i].c.name.dup2(), true);
            }
            i += 1;
        }
        s
    }
}

/// con-leche: ConLeche/Driver/Worker.lean:144-154 rootsAt
/// `l.constants.filter (!ix.first.contains ·.name)`, copied.
pub fn unloaded_constants(ix: &NameIndex, cs: &Vec<CEntry>) -> Vec<CEntry> {
    let mut out: Vec<CEntry> = Vec::new();
    let mut i = 0usize;
    while i < cs.len() {
        if !ix.first.contains_key(&cs[i].c.name) {
            out.push(group::c_entry_dup(&cs[i]));
        }
        i += 1;
    }
    out
}

/// con-leche: ConLeche/Driver/Worker.lean:144-154 rootsAt
/// **The reach's roots** of a worker that adds the imports `x`: what the own
/// records read (`own_roots`); at a compared challenge, what the own records
/// and the own constants read, and the copies' names.
#[allow(clippy::too_many_arguments)]
pub fn roots_at(pers: &PersTier, st: &mut AState, pins: &Vec<INatOpPinSet>, x: &Vec<ImportRec>, ix: &NameIndex, cs: &Vec<CEntry>, ds: &Vec<IDeclaration>) -> Result<Vec<NIdx>, CheckError> {
    if x.len() == 0 {
        return own_roots(pers, st, pins, ix, cs, ds);
    }
    let own = match recs_loaded(pers, st, ix, ds, false) {
        Err(e) => return Err(e),
        Ok(o) => o,
    };
    let mut out = match own_roots(pers, st, pins, ix, &unloaded_constants(ix, cs), &own) {
        Err(e) => return Err(e),
        Ok(o) => o,
    };
    let copies = match recs_loaded(pers, st, ix, ds, true) {
        Err(e) => return Err(e),
        Ok(c) => c,
    };
    let mut i = 0usize;
    while i < copies.len() {
        match reach::decl_names(pers, st, &copies[i]) {
            Err(e) => return Err(e),
            Ok(ns) => {
                let mut k = 0usize;
                while k < ns.len() {
                    out.push(ns[k].dup2());
                    k += 1;
                }
            }
        }
        i += 1;
    }
    Ok(out)
}

/// con-leche: ConLeche/Driver/Worker.lean:156-163 copyStmt?
/// **The statement a copy may be read by**: a hole's (an axiom; a definition
/// whose value uses `sorryAx`), a theorem's or an opaque constant's; none for
/// any other record.
pub fn copy_stmt(pers: &PersTier, st: &mut AState, d: &IDeclaration) -> Result<Option<IConstantVal>, CheckError> {
    match d {
        IDeclaration::AxiomDecl(cv) => Ok(Some(env::i_constant_val_dup(cv))),
        IDeclaration::DefnDecl(cv, v, _) => match uses_sorry(pers, st, v) {
            Err(e) => Err(e),
            Ok(true) => Ok(Some(env::i_constant_val_dup(cv))),
            Ok(false) => Ok(None),
        },
        IDeclaration::OpaqueDecl(cv, _) => Ok(Some(env::i_constant_val_dup(cv))),
        IDeclaration::ThmDecl(cv, _) => Ok(Some(env::i_constant_val_dup(cv))),
        _ => Ok(None),
    }
}

/// con-leche: ConLeche/Driver/Worker.lean:156-163 copyStmt?
/// `Expr.mentionsAnyConstC [sorryAxName] v`.
pub fn uses_sorry(pers: &PersTier, st: &mut AState, v: &EIdx) -> Result<bool, CheckError> {
    match pins::pin_sorry_ax(st) {
        Err(e) => Err(e),
        Ok(sa) => {
            let mut ns: Vec<NIdx> = Vec::with_capacity(1);
            ns.push(sa);
            mentions_any_const(pers, st, &ns, v)
        }
    }
}

/// con-leche: ConLeche/Driver/Worker.lean:165-170 sameDefUpToLevels
/// **A definition of the challenge, the loaded one** up to the names of its
/// level parameters (the loaded one renamed).
pub fn same_def_up_to_levels(pers: &PersTier, st: &mut AState, c: &IConstantInfo, c2: &IConstantInfo) -> Result<bool, CheckError> {
    let ps = env::i_constant_info_to_constant_val(c).level_params;
    let ps2 = env::i_constant_info_to_constant_val(c2).level_params;
    if crate::arena::canon::nidx_vec_beq(&ps, &ps2, 0) {
        Ok(i_constant_info_beq(c, c2))
    } else if justify::levels_renaming(&ps, &ps2) {
        match basis::constant_info_at_lps(pers, st, c2, &ps) {
            Err(e) => Err(e),
            Ok(r) => Ok(i_constant_info_beq(&r, c)),
        }
    } else {
        Ok(false)
    }
}

/// con-leche: ConLeche/Driver/Worker.lean:172-175 copyRecEq
/// `listBeqBy ConstantInfo.beqP b b'`.
pub fn infos_beq(b: &Vec<IConstantInfo>, b2: &Vec<IConstantInfo>) -> bool {
    if b.len() != b2.len() {
        return false;
    }
    let mut i = 0usize;
    while i < b.len() {
        if !i_constant_info_beq(&b[i], &b2[i]) {
            return false;
        }
        i += 1;
    }
    true
}

/// con-leche: ConLeche/Driver/Worker.lean:172-175 copyRecEq
/// **Two blocks, the same record.**
pub fn copy_rec_eq(d: &IDeclaration, e: &IDeclaration) -> bool {
    match (d, e) {
        (IDeclaration::IndDecl(b, n), IDeclaration::IndDecl(b2, n2)) => *n == *n2 && infos_beq(b, b2),
        _ => false,
    }
}

/// con-leche: ConLeche/Driver/Worker.lean:177-189 blockReadB
/// `xs.map (·.1.name)` of a list of constructors.
pub fn ctor_names(xs: &Vec<(IConstantVal, u64)>) -> Vec<NIdx> {
    let mut out: Vec<NIdx> = Vec::with_capacity(xs.len());
    let mut i = 0usize;
    while i < xs.len() {
        out.push(xs[i].0.name.dup2());
        i += 1;
    }
    out
}

/// con-leche: ConLeche/Driver/Worker.lean:177-189 blockReadB
/// `cs.map (·.1.name)` of a split's constructors.
pub fn split_ctor_names(cs: &Vec<(IConstantVal, u64, u64)>) -> Vec<NIdx> {
    let mut out: Vec<NIdx> = Vec::with_capacity(cs.len());
    let mut i = 0usize;
    while i < cs.len() {
        out.push(cs[i].0.name.dup2());
        i += 1;
    }
    out
}

/// con-leche: ConLeche/Driver/Worker.lean:177-189 blockReadB
/// **A block the kernel's reader reads** (`read_block`), its constructors'
/// names distinct and in the block's order; true for any other record.
pub fn block_read_b(pers: &PersTier, st: &mut AState, d: &IDeclaration) -> Result<bool, CheckError> {
    match d {
        IDeclaration::IndDecl(block, n_p) => match block_shape::read_block(pers, st, *n_p, block) {
            Err(e) => Err(e),
            Ok(Err(_)) => Ok(false),
            Ok(Ok(p)) => {
                let names = ctor_names(&block_shape::all_ctors(&p.members, 0, Vec::new()));
                let mut s: HashMap2<NIdx, bool> = HashMap2::new();
                if !names_nodup_go(&mut s, &names, 0) {
                    return Ok(false);
                }
                match block_shape::block_split(block, 0, Vec::new()) {
                    Some((_, cs, _)) => Ok(crate::arena::canon::nidx_vec_beq(&names, &split_ctor_names(&cs), 0)),
                    None => Ok(true),
                }
            }
        },
        _ => Ok(true),
    }
}

/// con-leche: ConLeche/Driver/Worker.lean:191-195 ctxConst
/// **The context's constants, one layer** (upstream's `ctxConst` over
/// `ownerMap`, whose names are distinct): every constant of every context
/// record pushed, in order, over the empty base.
pub fn ctx_layer(pers: &PersTier, st: &mut AState, ctx: &Vec<IDeclaration>) -> Result<IFEnv, CheckError> {
    let mut fe: IFEnv = env::ifenv_layer(0, 0, false, false);
    let mut i = 0usize;
    while i < ctx.len() {
        match install::decl_constants(pers, st, &ctx[i]) {
            Err(e) => return Err(e),
            Ok(cs) => fe = push_all(pers, fe, &cs),
        }
        i += 1;
    }
    Ok(fe)
}

/// con-leche: ConLeche/Driver/Worker.lean:191-195 ctxConst
/// Every constant of `cs` pushed onto `fe`.
pub fn push_all(pers: &PersTier, fe: IFEnv, cs: &Vec<IConstantInfo>) -> IFEnv {
    let mut fe = fe;
    let mut i = 0usize;
    while i < cs.len() {
        fe = env::ifenv_push(pers, fe, env::i_constant_info_dup(&cs[i]));
        i += 1;
    }
    fe
}

/// con-leche: ConLeche/Driver/Worker.lean:197-207 copyReadsB
/// **A copied block's recursors read their ι equations off their own types**
/// (`iota_read::recs_read`, upstream's `Cached.blockReadsOkC`), against the
/// context's constants (`fe`, `ctx_layer`); true for any other record.
pub fn copy_reads_b(pers: &PersTier, st: &mut AState, fe: &IFEnv, d: &IDeclaration) -> Result<bool, CheckError> {
    match d {
        IDeclaration::IndDecl(block, n_p) => match block_shape::read_block(pers, st, *n_p, block) {
            Err(e) => Err(e),
            Ok(Err(_)) => Ok(false),
            Ok(Ok(p)) => match install::block_recs(pers, st, &p, &p.recs, 0, Vec::new()) {
                Err(e) => Err(e),
                Ok(recs) => iota_read::recs_read(pers, st, fe, &recs, 0),
            },
        },
        _ => Ok(true),
    }
}

/// con-leche: ConLeche/Driver/Worker.lean:209-241 copyCheck
/// `(declConstants e).find? (·.toConstantVal.name == n)`.
pub fn find_constant(pers: &PersTier, st: &mut AState, e: &IDeclaration, n: &NIdx) -> Result<Option<IConstantInfo>, CheckError> {
    match install::decl_constants(pers, st, e) {
        Err(er) => Err(er),
        Ok(cs) => Ok(find_named(&cs, n)),
    }
}

/// con-leche: ConLeche/Driver/Worker.lean:209-241 copyCheck
/// `cs.find? (·.toConstantVal.name == n)`, copied.
pub fn find_named(cs: &Vec<IConstantInfo>, n: &NIdx) -> Option<IConstantInfo> {
    let mut i = 0usize;
    while i < cs.len() {
        if env::i_constant_info_name(&cs[i]).eq2(n) {
            return Some(env::i_constant_info_dup(&cs[i]));
        }
        i += 1;
    }
    None
}

/// con-leche: ConLeche/Driver/Worker.lean:209-241 copyCheck
/// `{n}: the constant of {h} is not of the statement of {m}'s {recKind d}`, and
/// its two siblings: `{n}: {what} {h} {tail}`.
pub fn copy_msg(pers: &PersTier, ar: &EStore, n: &NIdx, what: Vec<u32>, h: &NIdx, tail: &Vec<u32>) -> Vec<u32> {
    let t = text::cat3(view::name_text(pers, ar, n), &what, &view::name_text(pers, ar, h));
    text::cat(t, tail)
}

/// con-leche: ConLeche/Driver/Worker.lean:209-241 copyCheck
/// The comparison of a copy with the context's record `e` (at home `h`) that
/// holds its name `n`, and that record's constant `ci` of it, past the name
/// tests.
#[allow(clippy::too_many_arguments)]
pub fn copy_against(pers: &PersTier, st: &mut AState, fe: &IFEnv, m: &NIdx, src: &NIdx, n: &NIdx, e: &IDeclaration, h: &NIdx, d: &IDeclaration) -> Result<(), CheckError> {
    let ci = match find_constant(pers, st, e, n) {
        Err(er) => return Err(er),
        Ok(c) => c,
    };
    let cs = match copy_stmt(pers, st, d) {
        Err(er) => return Err(er),
        Ok(c) => c,
    };
    let mt = view::name_text(pers, &st.store, m);
    match cs {
        Some(cv) => match ci {
            Some(ci) => match justify::same_cv_up_to_levels(pers, st, &cv, &env::i_constant_info_to_constant_val(&ci)) {
                Err(er) => Err(er),
                Ok(true) => Ok(()),
                Ok(false) => {
                    let tail = text::cat3({ const M: [u32; 28] = [32, 105, 115, 32, 110, 111, 116, 32, 111, 102, 32, 116, 104, 101, 32, 115, 116, 97, 116, 101, 109, 101, 110, 116, 32, 111, 102, 32]; crate::kernel::core_types::code_points(&M) }, &mt, &text::cat({ const M: [u32; 3] = [39, 115, 32]; crate::kernel::core_types::code_points(&M) }, &rec_kind(d)));
                Err(core_types::invalid(copy_msg(pers, &st.store, n, { const M: [u32; 18] = [58, 32, 116, 104, 101, 32, 99, 111, 110, 115, 116, 97, 110, 116, 32, 111, 102, 32]; crate::kernel::core_types::code_points(&M) }, h, &tail)))
                }
            },
            None => Err(core_types::internal(text::cat(view::name_text(pers, &st.store, n), &{ const M: [u32; 42] = [58, 32, 116, 104, 101, 32, 99, 111, 110, 116, 101, 120, 116, 39, 115, 32, 114, 101, 99, 111, 114, 100, 32, 100, 111, 101, 115, 32, 110, 111, 116, 32, 100, 101, 99, 108, 97, 114, 101, 32, 105, 116]; crate::kernel::core_types::code_points(&M) }))),
        },
        None => match d {
            IDeclaration::DefnDecl(cv, v, hint) => match ci {
                Some(ci) => {
                    let c = IConstantInfo::DefnInfo(env::i_constant_val_dup(cv), v.dup2(), crate::kernel::env::reducibility_hint_dup(hint));
                    match same_def_up_to_levels(pers, st, &c, &ci) {
                        Err(er) => Err(er),
                        Ok(true) => Ok(()),
                        Ok(false) => {
                            let tail = text::cat3({ const M: [u32; 8] = [32, 105, 115, 32, 110, 111, 116, 32]; crate::kernel::core_types::code_points(&M) }, &mt, &{ const M: [u32; 13] = [39, 115, 32, 100, 101, 102, 105, 110, 105, 116, 105, 111, 110]; crate::kernel::core_types::code_points(&M) });
                    Err(core_types::invalid(copy_msg(pers, &st.store, n, { const M: [u32; 18] = [58, 32, 116, 104, 101, 32, 99, 111, 110, 115, 116, 97, 110, 116, 32, 111, 102, 32]; crate::kernel::core_types::code_points(&M) }, h, &tail)))
                        }
                    }
                }
                None => Err(core_types::internal(text::cat(view::name_text(pers, &st.store, n), &{ const M: [u32; 42] = [58, 32, 116, 104, 101, 32, 99, 111, 110, 116, 101, 120, 116, 39, 115, 32, 114, 101, 99, 111, 114, 100, 32, 100, 111, 101, 115, 32, 110, 111, 116, 32, 100, 101, 99, 108, 97, 114, 101, 32, 105, 116]; crate::kernel::core_types::code_points(&M) }))),
            },
            IDeclaration::IndDecl(_, _) => match copy_ind_ok(pers, st, fe, d, e) {
                Err(er) => Err(er),
                Ok(true) => Ok(()),
                Ok(false) => {
                    let tail = text::cat3({ const M: [u32; 9] = [32, 97, 114, 101, 32, 110, 111, 116, 32]; crate::kernel::core_types::code_points(&M) }, &mt, &{ const M: [u32; 17] = [39, 115, 32, 105, 110, 100, 117, 99, 116, 105, 118, 101, 32, 116, 121, 112, 101]; crate::kernel::core_types::code_points(&M) });
                Err(core_types::invalid(copy_msg(pers, &st.store, n, { const M: [u32; 19] = [58, 32, 116, 104, 101, 32, 99, 111, 110, 115, 116, 97, 110, 116, 115, 32, 111, 102, 32]; crate::kernel::core_types::code_points(&M) }, h, &tail)))
                }
            },
            _ => match ci {
                None => Err(core_types::internal(text::cat(view::name_text(pers, &st.store, n), &{ const M: [u32; 42] = [58, 32, 116, 104, 101, 32, 99, 111, 110, 116, 101, 120, 116, 39, 115, 32, 114, 101, 99, 111, 114, 100, 32, 100, 111, 101, 115, 32, 110, 111, 116, 32, 100, 101, 99, 108, 97, 114, 101, 32, 105, 116]; crate::kernel::core_types::code_points(&M) }))),
                Some(_) => {
                    let t = text::cat3({ const M: [u32; 7] = [109, 111, 100, 117, 108, 101, 32]; crate::kernel::core_types::code_points(&M) }, &mt, &text::cat({ const M: [u32; 10] = [32, 100, 101, 99, 108, 97, 114, 101, 115, 32]; crate::kernel::core_types::code_points(&M) }, &view::name_text(pers, &st.store, n)));
            let t = text::cat3(t, &{ const M: [u32; 19] = [44, 32, 119, 104, 105, 99, 104, 32, 116, 104, 101, 32, 109, 111, 100, 117, 108, 101, 32]; crate::kernel::core_types::code_points(&M) }, &view::name_text(pers, &st.store, src));
            Err(core_types::invalid(text::cat(t, &{ const M: [u32; 16] = [32, 105, 116, 32, 108, 111, 97, 100, 115, 32, 115, 116, 111, 114, 101, 115]; crate::kernel::core_types::code_points(&M) })))
                }
            },
        },
    }
}

/// con-leche: ConLeche/Driver/Worker.lean:209-241 copyCheck
/// A copied block: the context's record, read by the kernel's reader, its
/// recursors reading their ι equations (`copy_rec_eq`, `block_read_b`,
/// `copy_reads_b`, in order, each only where the last held).
pub fn copy_ind_ok(pers: &PersTier, st: &mut AState, fe: &IFEnv, d: &IDeclaration, e: &IDeclaration) -> Result<bool, CheckError> {
    if !copy_rec_eq(d, e) {
        return Ok(false);
    }
    match block_read_b(pers, st, d) {
        Err(er) => Err(er),
        Ok(false) => Ok(false),
        Ok(true) => copy_reads_b(pers, st, fe, d),
    }
}

/// con-leche: ConLeche/Driver/Worker.lean:209-241 copyCheck
/// **A copy against the loaded constants of its names** (`r`, the context;
/// `owner`, the record of each of its names; `fe`, its constants, `ctx_layer`).
#[allow(clippy::too_many_arguments)]
pub fn copy_check(pk: &OleanPins, pers: &PersTier, st: &mut AState, m: &NIdx, ld: &HeaderLoads, ix: &NameIndex, r: &Reach, owner: &HashMap2<NIdx, u64>, fe: &IFEnv, d: &IDeclaration) -> Result<(), CheckError> {
    let n: NIdx = match rec_key(d) {
        Some(k) => k,
        None => pk.anon.dup2(),
    };
    let src: NIdx = match ix.first.get(&n) {
        Some(c) => index::header_loads_name_at(pk, ld, c.module),
        None => pk.anon.dup2(),
    };
    let qs = match pins::pin_quot_sound(st) {
        Err(e) => return Err(e),
        Ok(q) => q,
    };
    let sa = match pins::pin_sorry_ax(st) {
        Err(e) => return Err(e),
        Ok(s) => s,
    };
    if n.eq2(&qs) || n.eq2(&sa) {
        let what = if n.eq2(&qs) { { const M: [u32; 20] = [116, 104, 101, 32, 113, 117, 111, 116, 105, 101, 110, 116, 39, 115, 32, 97, 120, 105, 111, 109]; crate::kernel::core_types::code_points(&M) } } else { { const M: [u32; 21] = [116, 104, 101, 32, 112, 108, 97, 99, 101, 104, 111, 108, 100, 101, 114, 32, 97, 120, 105, 111, 109]; crate::kernel::core_types::code_points(&M) } };
        let t = text::cat3(view::name_text(pers, &st.store, &n), &{ const M: [u32; 12] = [58, 32, 97, 32, 104, 111, 108, 101, 32, 97, 116, 32]; crate::kernel::core_types::code_points(&M) }, &what);
        return Err(core_types::not_implemented(text::cat(t, &{ const M: [u32; 62] = [44, 32, 119, 104, 105, 99, 104, 32, 105, 110, 115, 116, 97, 108, 108, 115, 32, 110, 111, 32, 97, 120, 105, 111, 109, 32, 111, 102, 32, 105, 116, 115, 32, 111, 119, 110, 59, 32, 99, 111, 110, 45, 108, 101, 99, 104, 101, 32, 99, 97, 110, 110, 111, 116, 32, 102, 105, 108, 108, 32, 105, 116]; crate::kernel::core_types::code_points(&M) })));
    }
    match basis::basis_names_ok(pers, st, d) {
        Err(e) => return Err(e),
        Ok(true) => {}
        Ok(false) => {
            let t = text::cat3({ const M: [u32; 7] = [109, 111, 100, 117, 108, 101, 32]; crate::kernel::core_types::code_points(&M) }, &view::name_text(pers, &st.store, m), &{ const M: [u32; 10] = [32, 100, 101, 99, 108, 97, 114, 101, 115, 32]; crate::kernel::core_types::code_points(&M) });
            return Err(core_types::invalid(text::cat3(t, &view::name_text(pers, &st.store, &n), &{ const M: [u32; 29] = [44, 32, 97, 32, 110, 97, 109, 101, 32, 116, 104, 101, 32, 99, 104, 101, 99, 107, 101, 114, 32, 114, 101, 115, 101, 114, 118, 101, 115]; crate::kernel::core_types::code_points(&M) })));
        }
    }
    match owner.get(&n) {
        None => Err(core_types::internal(text::cat(view::name_text(pers, &st.store, &n), &{ const M: [u32; 47] = [58, 32, 116, 104, 101, 32, 99, 111, 110, 116, 101, 120, 116, 32, 100, 111, 101, 115, 32, 110, 111, 116, 32, 104, 111, 108, 100, 32, 116, 104, 101, 32, 108, 111, 97, 100, 101, 100, 32, 99, 111, 110, 115, 116, 97, 110, 116]; crate::kernel::core_types::code_points(&M) }))),
        Some(k) => {
            let k = *k as usize;
            if k < r.ctx.len() {
                let h: NIdx = if k < r.homes.len() { r.homes[k].dup2() } else { pk.anon.dup2() };
                copy_against(pers, st, fe, m, &src, &n, &r.ctx[k], &h, d)
            } else {
                Err(core_types::internal(text::cat(view::name_text(pers, &st.store, &n), &{ const M: [u32; 47] = [58, 32, 116, 104, 101, 32, 99, 111, 110, 116, 101, 120, 116, 32, 100, 111, 101, 115, 32, 110, 111, 116, 32, 104, 111, 108, 100, 32, 116, 104, 101, 32, 108, 111, 97, 100, 101, 100, 32, 99, 111, 110, 115, 116, 97, 110, 116]; crate::kernel::core_types::code_points(&M) })))
            }
        }
    }
}

/// con-leche: ConLeche/Driver/Worker.lean:243-249 isHoleRec
/// **A hole** (an axiom other than a built-in one; a definition, opaque
/// constant or theorem whose value uses `sorryAx`; `uses`, what a theorem's
/// value read off the file).
pub fn is_hole_rec<U: UsedConsts>(uses: &U, pers: &PersTier, st: &mut AState, d: &IDeclaration) -> Result<bool, CheckError> {
    match d {
        IDeclaration::AxiomDecl(cv) => match justify::builtin_axiom_name(st, &cv.name) {
            Err(e) => Err(e),
            Ok(b) => Ok(!b),
        },
        IDeclaration::DefnDecl(_, v, _) => uses_sorry(pers, st, v),
        IDeclaration::OpaqueDecl(_, v) => uses_sorry(pers, st, v),
        IDeclaration::ThmDecl(_, _) => match uses.used_consts(pers, st, d) {
            Err(e) => Err(e),
            Ok(us) => match pins::pin_sorry_ax(st) {
                Err(e) => Err(e),
                Ok(sa) => Ok(env::nidx_vec_contains(&us, &sa)),
            },
        },
        _ => Ok(false),
    }
}

/// con-leche: ConLeche/Driver/Worker.lean:251-258 ownHoleOk
/// **A hole of the challenge's own records**: the solution does not fill it.
pub fn own_hole_ok<U: UsedConsts>(pk: &OleanPins, uses: &U, pers: &PersTier, st: &mut AState, m: &NIdx, d: &IDeclaration) -> Result<(), CheckError> {
    match is_hole_rec(uses, pers, st, d) {
        Err(e) => Err(e),
        Ok(false) => Ok(()),
        Ok(true) => {
            let n: NIdx = match rec_key(d) {
                Some(k) => k,
                None => pk.anon.dup2(),
            };
            let t = text::cat3(view::name_text(pers, &st.store, &n), &{ const M: [u32; 12] = [58, 32, 97, 32, 104, 111, 108, 101, 32, 111, 102, 32]; crate::kernel::core_types::code_points(&M) }, &view::name_text(pers, &st.store, m));
            Err(core_types::invalid(text::cat(t, &{ const M: [u32; 67] = [32, 110, 111, 32, 108, 111, 97, 100, 101, 100, 32, 109, 111, 100, 117, 108, 101, 32, 102, 105, 108, 108, 115, 32, 40, 116, 104, 101, 32, 115, 111, 108, 117, 116, 105, 111, 110, 32, 104, 97, 115, 32, 110, 111, 32, 99, 111, 110, 115, 116, 97, 110, 116, 32, 111, 102, 32, 116, 104, 105, 115, 32, 110, 97, 109, 101, 41]; crate::kernel::core_types::code_points(&M) })))
        }
    }
}

/// con-leche: ConLeche/Driver/Worker.lean:260-264 copiesOk
/// Some record of `ds` an inductive block.
pub fn any_ind(ds: &Vec<IDeclaration>) -> bool {
    let mut i = 0usize;
    while i < ds.len() {
        match &ds[i] {
            IDeclaration::IndDecl(_, _) => return true,
            _ => {}
        }
        i += 1;
    }
    false
}

/// con-leche: ConLeche/Driver/Worker.lean:260-264 copiesOk
/// **Every copy against the loaded constants of its names** (`copy_check`).
/// The context's layer is built only where a copy is an inductive block.
#[allow(clippy::too_many_arguments)]
pub fn copies_ok(pk: &OleanPins, pers: &PersTier, st: &mut AState, m: &NIdx, x: &Vec<ImportRec>, wr: &WorkerReads, r: &Reach, ds: &Vec<IDeclaration>) -> Result<(), CheckError> {
    let owner = match reach::owner_map(pers, st, &r.ctx) {
        Err(e) => return Err(e),
        Ok(o) => o,
    };
    let cs = match copy_recs(pers, st, x, &wr.index, ds) {
        Err(e) => return Err(e),
        Ok(c) => c,
    };
    let fe: IFEnv = if any_ind(&cs) {
        match ctx_layer(pers, st, &r.ctx) {
            Err(e) => return Err(e),
            Ok(f) => f,
        }
    } else {
        env::ifenv_layer(0, 0, false, false)
    };
    let mut i = 0usize;
    while i < cs.len() {
        match copy_check(pk, pers, st, m, &wr.loads, &wr.index, r, &owner, &fe, &cs[i]) {
            Err(e) => return Err(e),
            Ok(()) => {}
        }
        i += 1;
    }
    Ok(())
}

/// con-leche: ConLeche/Driver/Worker.lean:266-270 ownHolesOk
/// **No hole among the own records** of a compared challenge (`own_hole_ok`);
/// nothing to ask of any other worker's.
#[allow(clippy::too_many_arguments)]
pub fn own_holes_ok<U: UsedConsts>(pk: &OleanPins, uses: &U, pers: &PersTier, st: &mut AState, m: &NIdx, x: &Vec<ImportRec>, ix: &NameIndex, ds: &Vec<IDeclaration>) -> Result<(), CheckError> {
    if x.len() == 0 {
        return Ok(());
    }
    let own = match recs_loaded(pers, st, ix, ds, false) {
        Err(e) => return Err(e),
        Ok(o) => o,
    };
    let mut i = 0usize;
    while i < own.len() {
        match own_hole_ok(pk, uses, pers, st, m, &own[i]) {
            Err(e) => return Err(e),
            Ok(()) => {}
        }
        i += 1;
    }
    Ok(())
}

/// con-leche: ConLeche/Driver/Worker.lean:272-290 WorkerRead
/// **What a worker has read and checked before its jobs.**
pub struct WorkerRead {
    /// the module's private view, loaded (its frontier moved to `values`)
    pub home: Loaded,
    /// each own constant's exported level (`check_views`)
    pub expo: Vec<Expo>,
    /// the header fixpoint, the name index, the clash rule's copies
    pub reads: WorkerReads,
    /// the own records, as the emission gives them
    pub emitted: Vec<IDeclaration>,
    /// the own records, in the order they are checked
    pub own: Vec<IDeclaration>,
    /// the context
    pub reach: Reach,
    /// the records moved by the ground hoist
    pub hoisted: Vec<NIdx>,
    /// the reader's pins (`OleanRead::pins`'s)
    pub pins: OleanPins,
    /// the module the jobs read the theorems' values from: the home, with its
    /// frontier (upstream's `#[⟨m, w.home.frontier⟩]`)
    pub values: Vec<ModRef>,
    /// the first own job: the context's size
    pub start: u64,
}

/// con-leche: ConLeche/Driver/Worker.lean:301-344 workerRead
/// The home's frontier, moved into the jobs' one value module.
pub fn home_values(m: &NIdx, l: &mut Loaded) -> Vec<ModRef> {
    let fr = core::mem::replace(&mut l.frontier, sparse::frontier_empty());
    let mut out: Vec<ModRef> = Vec::with_capacity(1);
    out.push(ModRef { name: m.dup2(), frontier: fr });
    out
}

/// con-leche: ConLeche/Driver/Worker.lean:301-344 workerRead
/// **Phases 1–4 of the worker at module `m`** (module note); `x` the imports a
/// run adds to its header (a compared challenge's solution: its own records are
/// those no loaded module stores, `own_recs`, and its copies are checked
/// against the loaded constants, `copies_ok`).  `pins`: the run's interned
/// `Nat`-operation pin variants (`checker::intern_all_pins`'s), for the pin
/// ground.  A failure carries the position of the record it names (0 where
/// none).
#[allow(clippy::too_many_arguments)]
pub fn worker_read<F: CheckerFs>(fs: &F, pers: &PersTier, st: &mut AState, sp: &files::Roots, pins: &Vec<INatOpPinSet>, m: &NIdx, x: &Vec<ImportRec>) -> Result<WorkerRead, (CheckError, u64)> {
    let pk = match spec::olean_pins(pers, &mut st.store) {
        Err(e) => return Err((e, 0)),
        Ok(p) => p,
    };
    let f = match files::read_files(fs, pers, &st.store, sp, m, &OLeanLevel::Private) {
        Err(e) => return Err((e, 0)),
        Ok(f) => f,
    };
    let (mut l, expo) = match home_of(&pk, pers, &mut st.store, m, &f) {
        Err(e) => return Err((e, 0)),
        Ok(h) => h,
    };
    let wr = match index::worker_reads(fs, &pk, pers, &mut st.store, sp, m, x) {
        Err(e) => return Err((e, 0)),
        Ok(w) => w,
    };
    if x.len() != 0 && wr.loads.index.contains_key(m) {
        let t = text::cat({ const M: [u32; 11] = [116, 104, 101, 32, 109, 111, 100, 117, 108, 101, 32]; crate::kernel::core_types::code_points(&M) }, &view::name_text(pers, &st.store, m));
        return Err((core_types::invalid(text::cat(t, &{ const M: [u32; 89] = [32, 105, 115, 32, 108, 111, 97, 100, 101, 100, 32, 98, 121, 32, 116, 104, 101, 32, 105, 109, 112, 111, 114, 116, 115, 32, 97, 100, 100, 101, 100, 32, 116, 111, 32, 105, 116, 115, 32, 104, 101, 97, 100, 101, 114, 58, 32, 116, 104, 101, 32, 115, 111, 108, 117, 116, 105, 111, 110, 39, 115, 32, 99, 108, 111, 115, 117, 114, 101, 32, 104, 111, 108, 100, 115, 32, 116, 104, 101, 32, 99, 104, 97, 108, 108, 101, 110, 103, 101]; crate::kernel::core_types::code_points(&M) })), 0));
    }
    let ds = match own_records(&pk, pers, &mut st.store, &l) {
        Err(e) => return Err(e),
        Ok(d) => d,
    };
    let (r, own, hoisted) = match worker_reach(fs, &pk, pers, st, sp, pins, m, x, &wr, &l.constants, &ds) {
        Err(e) => return Err((e, 0)),
        Ok(t) => t,
    };
    let values = home_values(m, &mut l);
    let start = r.ctx.len() as u64;
    Ok(WorkerRead { home: l, expo, reads: wr, emitted: ds, own, reach: r, hoisted, pins: pk, values, start })
}

/// con-leche: ConLeche/Driver/Worker.lean:301-344 workerRead
/// Phase 4 and the hoist, over the load's constants `cs` and the emitted
/// records `ds`: the own holes, the reach, its names distinct, the copies, and
/// the own records hoisted.
#[allow(clippy::too_many_arguments)]
pub fn worker_reach<F: CheckerFs>(fs: &F, pk: &OleanPins, pers: &PersTier, st: &mut AState, sp: &files::Roots, pins: &Vec<INatOpPinSet>, m: &NIdx, x: &Vec<ImportRec>, wr: &WorkerReads, cs: &Vec<CEntry>, ds: &Vec<IDeclaration>) -> Result<(Reach, Vec<IDeclaration>, Vec<NIdx>), CheckError> {
    let uses = own_uses_of(cs);
    match own_holes_ok(pk, &uses, pers, st, m, x, &wr.index, ds) {
        Err(e) => return Err(e),
        Ok(()) => {}
    }
    let roots = match roots_at(pers, st, pins, x, &wr.index, cs, ds) {
        Err(e) => return Err(e),
        Ok(rs) => rs,
    };
    let r = match reach::reach(fs, pk, pers, st, sp, m, wr, &own_names_of(x, &wr.index, cs), &roots) {
        Err(e) => return Err(e),
        Ok(r) => r,
    };
    match ctx_names_nodup(pers, st, &r.ctx) {
        Err(e) => return Err(e),
        Ok(true) => {}
        Ok(false) => return Err(core_types::invalid({ const M: [u32; 48] = [97, 32, 99, 111, 110, 116, 101, 120, 116, 32, 114, 101, 99, 111, 114, 100, 32, 100, 101, 99, 108, 97, 114, 101, 115, 32, 111, 110, 101, 32, 111, 102, 32, 105, 116, 115, 32, 110, 97, 109, 101, 115, 32, 116, 119, 105, 99, 101]; crate::kernel::core_types::code_points(&M) })),
    }
    match copies_ok(pk, pers, st, m, x, wr, &r, ds) {
        Err(e) => return Err(e),
        Ok(()) => {}
    }
    let recs = match own_recs(pers, st, x, &wr.index, decls_dup(ds)) {
        Err(e) => return Err(e),
        Ok(o) => o,
    };
    match nat_op_ground::hoist_nat_op_ground(pers, st, &uses, recs) {
        Err(e) => Err(e),
        Ok((own, hoisted)) => Ok((r, own, hoisted)),
    }
}

/// con-leche: ConLeche/Driver/Worker.lean:301-344 workerRead
/// The emitted records, copied (`ownRecs` filters them; `emitted` keeps them).
pub fn decls_dup(ds: &Vec<IDeclaration>) -> Vec<IDeclaration> {
    let mut out: Vec<IDeclaration> = Vec::with_capacity(ds.len());
    let mut i = 0usize;
    while i < ds.len() {
        out.push(env::i_declaration_dup(&ds[i]));
        i += 1;
    }
    out
}

/// con-leche: ConLeche/Driver/Worker.lean:371-413 checkModuleG
/// **The jobs' records**: the context's, then the own records
/// (`w.reach.ctx ++ w.own`), copied.  The jobs are those from `w.start` on.
pub fn worker_decls(w: &WorkerRead) -> Vec<IDeclaration> {
    let mut out: Vec<IDeclaration> = Vec::with_capacity(w.reach.ctx.len() + w.own.len());
    let mut i = 0usize;
    while i < w.reach.ctx.len() {
        out.push(env::i_declaration_dup(&w.reach.ctx[i]));
        i += 1;
    }
    let mut k = 0usize;
    while k < w.own.len() {
        out.push(env::i_declaration_dup(&w.own[k]));
        k += 1;
    }
    out
}
