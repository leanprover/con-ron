//! `ConLeche/Frontend/Olean/Index.lean` — the names a module's environment
//! holds (task #166).
//!
//! What a worker reads of the modules its header loads (`levels::header_fixpoint`)
//! before its own records: every loaded part's name table, indexed by name, and
//! the two checks Lean's import and kernel make over the whole loaded
//! environment: **the clash rule** (`finalizeImport`, `merge::subsumes_f`) and
//! **freshness** (no constant of the module's own part bears a loaded name).
//!
//! ## Deviations
//!
//! * **`parMapExcept` is the sequential map** (`olean::closure`'s note): the
//!   loaded parts' tables and the copies' statements are read in order, and
//!   upstream's `jobs` is not a parameter.
//! * `clashCopies`' table of each name's copies (`ccStep`) is a list with an
//!   index of its names (`clash_copies_step`): the same names in the same order
//!   (that of their second copies), each with the same copies.
//! * `isPropCheap`'s `headTy` is a lookup in the heads' statements
//!   (`ClashHeads`, a `merge::HeadTy`).

use crate::arena::env;
use crate::arena::handle::{EIdx, NIdx};
use crate::arena::store::{EStore, PersTier};
use crate::frontend::olean::files;
use crate::frontend::checker_io::CheckerFs;
use crate::frontend::olean::levels;
use crate::frontend::olean::levels::HeaderLoads;
use crate::frontend::olean::merge;
use crate::frontend::olean::reads::{ModHeader, NamePosition, NamePositions};
use crate::frontend::olean::spec;
use crate::frontend::olean::spec::{CKindF, ImportRec, OleanPins, RdErr, StmtRec};
use crate::frontend::olean::view;
use crate::frontend::olean::view::OLeanLevel;
use crate::frontend::text;
use crate::kernel::core_types;
use crate::kernel::core_types::CheckError;
use crate::kernel::name;
use crate::ron::hashmap::{Dup, Eq2, Hashable};
use crate::ron::hashmap2::HashMap2;

/// con-leche: ConLeche/Frontend/Olean/Index.lean:35-40 Copy
/// **A copy of a loaded name**: the module (its position in the load order) and
/// the constant's position among that module's name positions.
pub struct Copy {
    pub module: u64,
    pub pos: u64,
}

/// con-leche: ConLeche/Frontend/Olean/Index.lean:35-40 Copy
/// The derived `Hashable`: `mixHash` over the fields.
impl Hashable for Copy {
    /// con-leche: ConLeche/Frontend/Olean/Index.lean:35-40 Copy
    fn hash64(&self) -> u64 {
        name::mix_hash(name::nat_hash(self.module), name::nat_hash(self.pos))
    }
}

/// con-leche: ConLeche/Frontend/Olean/Index.lean:35-40 Copy
/// The derived `BEq`.
impl Eq2 for Copy {
    /// con-leche: ConLeche/Frontend/Olean/Index.lean:35-40 Copy
    fn eq2(&self, other: &Copy) -> bool {
        self.module == other.module && self.pos == other.pos
    }
}

/// con-leche: ConLeche/Frontend/Olean/Index.lean:35-40 Copy
/// A copy, copied.
impl Dup for Copy {
    /// con-leche: ConLeche/Frontend/Olean/Index.lean:35-40 Copy
    fn dup2(&self) -> Copy {
        Copy { module: self.module, pos: self.pos }
    }
}

/// con-leche: ConLeche/Frontend/Olean/Index.lean:42-49 NameIndex
/// **The name index** of the loaded parts.
pub struct NameIndex {
    /// by position in the load order: the loaded part's name positions
    pub parts: Vec<NamePositions>,
    /// each loaded name's first copy in the load order
    pub first: HashMap2<NIdx, Copy>,
    /// every later copy, in the load order
    pub more: Vec<(NIdx, Copy)>,
}

/// con-leche: ConLeche/Frontend/Olean/Index.lean:51-53 NameIndex.at
/// The name position of a copy.
pub fn name_index_at<'a>(ix: &'a NameIndex, c: &Copy) -> Option<&'a NamePosition> {
    let m = c.module as usize;
    if m < ix.parts.len() {
        let p = c.pos as usize;
        if p < ix.parts[m].consts.len() {
            Some(&ix.parts[m].consts[p])
        } else {
            None
        }
    } else {
        None
    }
}

/// con-leche: ConLeche/Frontend/Olean/Index.lean:51-53 NameIndex.at
/// `(ix.at c).map (·.loc)`.
pub fn name_index_loc(ix: &NameIndex, c: &Copy) -> Option<u64> {
    match name_index_at(ix, c) {
        Some(q) => Some(q.loc),
        None => None,
    }
}

/// con-leche: ConLeche/Frontend/Olean/Index.lean:55-66 nameIndexOf
/// **The index of some modules' name positions**, in their order.
pub fn name_index_of(parts: Vec<NamePositions>) -> NameIndex {
    let mut total = 0usize;
    let mut j = 0usize;
    while j < parts.len() {
        total += parts[j].consts.len();
        j += 1;
    }
    let mut first: HashMap2<NIdx, Copy> = HashMap2::with_capacity(total);
    let mut more: Vec<(NIdx, Copy)> = Vec::new();
    let mut i = 0usize;
    while i < parts.len() {
        let cs = &parts[i].consts;
        let mut k = 0usize;
        while k < cs.len() {
            let c = Copy { module: i as u64, pos: k as u64 };
            if first.contains_key(&cs[k].name) {
                more.push((cs[k].name.dup2(), c));
            } else {
                first.insert(cs[k].name.dup2(), c);
            }
            k += 1;
        }
        i += 1;
    }
    NameIndex { parts, first, more }
}

/// con-leche: ConLeche/Frontend/Olean/Index.lean:68-72 Clash
/// **A name two loaded modules hold**: its copies in the load order, each with
/// its statement and its kind (expressions left out).
pub struct Clash {
    pub name: NIdx,
    pub copies: Vec<(Copy, StmtRec, CKindF<NIdx, ()>)>,
}

/// con-leche: ConLeche/Frontend/Olean/Index.lean:68-72 Clash
/// A statement, copied.
pub fn stmt_rec_dup(s: &StmtRec) -> StmtRec {
    StmtRec { name: s.name.dup2(), level_params: env::nidx_vec_dup(&s.level_params), ty: s.ty.dup2() }
}

/// con-leche: ConLeche/Frontend/Olean/Index.lean:68-72 Clash
/// A kind without expressions, copied.
pub fn c_kind_names_dup(k: &CKindF<NIdx, ()>) -> CKindF<NIdx, ()> {
    match k {
        CKindF::Ax(u) => CKindF::Ax(*u),
        CKindF::Defn(_, h, s) => CKindF::Defn((), spec::hints_dup(h), crate::kernel::expr::str_copy(s)),
        CKindF::Thm(_, all) => CKindF::Thm((), env::nidx_vec_dup(all)),
        CKindF::Opaq(_, u) => CKindF::Opaq((), *u),
        CKindF::Quot(s) => CKindF::Quot(crate::kernel::expr::str_copy(s)),
        CKindF::Induct(np, ni, all, cs, nn, ir, iu, irf) => {
            CKindF::Induct(*np, *ni, env::nidx_vec_dup(all), env::nidx_vec_dup(cs), *nn, *ir, *iu, *irf)
        }
        CKindF::Ctor(ind, ci, np, nf, iu) => CKindF::Ctor(ind.dup2(), *ci, *np, *nf, *iu),
        CKindF::Recur(all, np, ni, nmo, nmi, rules, k2, iu) => {
            let mut rs: Vec<(NIdx, u64, ())> = Vec::with_capacity(rules.len());
            let mut i = 0usize;
            while i < rules.len() {
                rs.push((rules[i].0.dup2(), rules[i].1, ()));
                i += 1;
            }
            CKindF::Recur(env::nidx_vec_dup(all), *np, *ni, *nmo, *nmi, rs, *k2, *iu)
        }
    }
}

/// con-leche: ConLeche/Frontend/Olean/Index.lean:110-111 HeaderLoads.nameAt
/// A module's name for messages.
pub fn header_loads_name_at(pk: &OleanPins, ld: &HeaderLoads, i: u64) -> NIdx {
    let k = i as usize;
    if k < ld.order.len() {
        ld.order[k].dup2()
    } else {
        pk.anon.dup2()
    }
}

/// con-leche: ConLeche/Frontend/Olean/Index.lean:76-91 readInfosOf
/// A module's level in the load order (its flags' `level`, the default flags'
/// past the end).
pub fn header_loads_level_at(ld: &HeaderLoads, i: u64) -> OLeanLevel {
    let k = i as usize;
    if k < ld.flags.len() {
        levels::load_flags_level(&ld.flags[k])
    } else {
        OLeanLevel::Exported
    }
}

/// con-leche: ConLeche/Frontend/Olean/Index.lean:76-91 readInfosOf
/// **The statements and kinds of some copies** of module `i`, read together.
pub fn read_infos_of<F: CheckerFs>(fs: &F, pk: &OleanPins, pers: &PersTier, ar: &mut EStore, sp: &files::Roots, ld: &HeaderLoads, ix: &NameIndex, i: u64, cs: &Vec<Copy>) -> Result<Vec<(Copy, StmtRec, CKindF<NIdx, ()>)>, CheckError> {
    let m = header_loads_name_at(pk, ld, i);
    let level = header_loads_level_at(ld, i);
    let mut locs: Vec<u64> = Vec::with_capacity(cs.len());
    let mut j = 0usize;
    while j < cs.len() {
        match name_index_loc(ix, &cs[j]) {
            Some(l) => locs.push(l),
            None => {}
        }
        j += 1;
    }
    let f = match files::read_files(fs, pers, ar, sp, &m, &level) {
        Err(e) => return Err(e),
        Ok(f) => f,
    };
    let ss = match view::read_stmts(pk, pers, ar, &f, &level, &locs) {
        Err(RdErr::Err(e)) => return Err(e),
        Err(RdErr::Bad) => return Err(view::undecodable(pers, ar, &m)),
        Ok(ss) => ss,
    };
    let ks = match view::read_kinds(pk, pers, ar, &f, &level, &locs) {
        Err(RdErr::Err(e)) => return Err(e),
        Err(RdErr::Bad) => return Err(view::undecodable(pers, ar, &m)),
        Ok(ks) => ks,
    };
    if ss.len() != cs.len() || ks.len() != cs.len() {
        return Err(view::undecodable(pers, ar, &m));
    }
    let mut out: Vec<(Copy, StmtRec, CKindF<NIdx, ()>)> = Vec::with_capacity(cs.len());
    let mut k = 0usize;
    while k < cs.len() {
        out.push((cs[k].dup2(), stmt_rec_dup(&ss[k]), c_kind_names_dup(&ks[k])));
        k += 1;
    }
    Ok(out)
}

/// con-leche: ConLeche/Frontend/Olean/Index.lean:93-97 byModule
/// **Copies grouped by module**, the modules ascending, each module's copies in
/// their order.
pub fn by_module(cs: &Vec<Copy>) -> Vec<(u64, Vec<Copy>)> {
    let mut top = 0u64;
    let mut i = 0usize;
    while i < cs.len() {
        if cs[i].module + 1 > top {
            top = cs[i].module + 1;
        }
        i += 1;
    }
    let mut buckets: Vec<Vec<Copy>> = Vec::with_capacity(top as usize);
    let mut b = 0u64;
    while b < top {
        buckets.push(Vec::new());
        b += 1;
    }
    let mut j = 0usize;
    while j < cs.len() {
        buckets[cs[j].module as usize].push(cs[j].dup2());
        j += 1;
    }
    let mut out: Vec<(u64, Vec<Copy>)> = Vec::new();
    let mut k = 0usize;
    while k < buckets.len() {
        if buckets[k].len() > 0 {
            out.push((k as u64, core::mem::replace(&mut buckets[k], Vec::new())));
        }
        k += 1;
    }
    out
}

/// con-leche: ConLeche/Frontend/Olean/Index.lean:99-106 readInfos
/// **The statements and kinds of some copies**, module by module (in order:
/// the module note).
pub fn read_infos<F: CheckerFs>(fs: &F, pk: &OleanPins, pers: &PersTier, ar: &mut EStore, sp: &files::Roots, ld: &HeaderLoads, ix: &NameIndex, cs: &Vec<Copy>) -> Result<HashMap2<Copy, (StmtRec, CKindF<NIdx, ()>)>, CheckError> {
    let groups = by_module(cs);
    let mut m: HashMap2<Copy, (StmtRec, CKindF<NIdx, ()>)> = HashMap2::with_capacity(cs.len());
    let mut i = 0usize;
    while i < groups.len() {
        match read_infos_of(fs, pk, pers, ar, sp, ld, ix, groups[i].0, &groups[i].1) {
            Err(e) => return Err(e),
            Ok(r) => {
                let mut k = 0usize;
                while k < r.len() {
                    m.insert(r[k].0.dup2(), (stmt_rec_dup(&r[k].1), c_kind_names_dup(&r[k].2)));
                    k += 1;
                }
            }
        }
        i += 1;
    }
    Ok(m)
}

/// con-leche: ConLeche/Frontend/Olean/Index.lean:194-242 workerReads
/// **`isPropCheap`'s `headTy` at the clash rule**: by name, the type of its
/// first copy, among the statements read of the heads (`head_tys_of`).
pub struct HeadTys {
    pub m: HashMap2<NIdx, EIdx>,
}

/// con-leche: ConLeche/Frontend/Olean/Index.lean:194-242 workerReads
impl merge::HeadTy for HeadTys {
    /// con-leche: ConLeche/Frontend/Olean/Index.lean:194-242 workerReads
    fn head_ty(&self, n: &NIdx) -> Option<EIdx> {
        match self.m.get(n) {
            None => None,
            Some(t) => Some(t.dup2()),
        }
    }
}

/// con-leche: ConLeche/Frontend/Olean/Index.lean:194-242 workerReads
/// One head's type, by its name: `headTy n = (ix.first[n]?).bind fun c =>
/// (hinfos[c]?).map (·.1.type)`, at the name of a head `c`, which is a first
/// copy.
pub fn head_ty_step(ix: &NameIndex, infos: &HashMap2<Copy, (StmtRec, CKindF<NIdx, ()>)>, m: &mut HashMap2<NIdx, EIdx>, c: &Copy) {
    match name_index_at(ix, c) {
        None => {}
        Some(q) => match ix.first.get(&q.name) {
            None => {}
            Some(f) => match infos.get(f) {
                None => {}
                Some(x) => {
                    m.insert(q.name.dup2(), x.0.ty.dup2());
                }
            },
        },
    }
}

/// con-leche: ConLeche/Frontend/Olean/Index.lean:194-242 workerReads
/// `headTy` as a table over the heads' names.
pub fn head_tys_of(ix: &NameIndex, infos: &HashMap2<Copy, (StmtRec, CKindF<NIdx, ()>)>, heads: &Vec<Copy>) -> HeadTys {
    let mut m: HashMap2<NIdx, EIdx> = HashMap2::with_capacity(heads.len());
    let mut i = 0usize;
    while i < heads.len() {
        head_ty_step(ix, infos, &mut m, &heads[i]);
        i += 1;
    }
    HeadTys { m }
}

/// con-leche: ConLeche/Frontend/Olean/Index.lean:113-127 clashOk
/// The clash rule's reject.
pub fn clash_reject(pk: &OleanPins, pers: &PersTier, ar: &EStore, ld: &HeaderLoads, a: u64, b: u64, n: &NIdx) -> CheckError {
    let t = text::cat({ const M: [u32; 8] = [109, 111, 100, 117, 108, 101, 115, 32]; crate::kernel::core_types::code_points(&M) }, &view::name_text(pers, ar, &header_loads_name_at(pk, ld, a)));
    let t = text::cat3(t, &{ const M: [u32; 5] = [32, 97, 110, 100, 32]; crate::kernel::core_types::code_points(&M) }, &view::name_text(pers, ar, &header_loads_name_at(pk, ld, b)));
    let t = text::cat3(t, &{ const M: [u32; 33] = [32, 115, 116, 111, 114, 101, 32, 100, 105, 102, 102, 101, 114, 101, 110, 116, 32, 99, 111, 110, 115, 116, 97, 110, 116, 115, 32, 110, 97, 109, 101, 100, 32]; crate::kernel::core_types::code_points(&M) }, &view::name_text(pers, ar, n));
    core_types::invalid(text::cat(t, &{ const M: [u32; 21] = [44, 32, 97, 110, 100, 32, 98, 111, 116, 104, 32, 97, 114, 101, 32, 108, 111, 97, 100, 101, 100]; crate::kernel::core_types::code_points(&M) }))
}

/// con-leche: ConLeche/Frontend/Olean/Index.lean:113-127 clashOk
/// **Lean's clash rule over one name's copies**, in the load order: the copy
/// kept so far and the next one, the next kept where it subsumes the kept one,
/// the kept one staying where it subsumes the next, a reject otherwise.
pub fn clash_ok(pk: &OleanPins, pers: &PersTier, ar: &EStore, ld: &HeaderLoads, h: &HeadTys, c: &Clash) -> Result<(), CheckError> {
    let mut kept = 0usize;
    let mut i = 1usize;
    while i < c.copies.len() {
        match clash_step(pk, pers, ar, ld, h, c, kept, i) {
            Err(e) => return Err(e),
            Ok(k) => kept = k,
        }
        i += 1;
    }
    Ok(())
}

/// con-leche: ConLeche/Frontend/Olean/Index.lean:113-127 clashOk
/// One step of the rule: the copy kept after copy `i`, the kept one so far
/// being copy `kept`.
pub fn clash_step(pk: &OleanPins, pers: &PersTier, ar: &EStore, ld: &HeaderLoads, h: &HeadTys, c: &Clash, kept: usize, i: usize) -> Result<usize, CheckError> {
    let next = &c.copies[i];
    let kp = &c.copies[kept];
    match merge::subsumes_f(pk, pers, ar, h, &next.1, &next.2, &kp.1, &kp.2) {
        Err(e) => Err(e),
        Ok(true) => Ok(i),
        Ok(false) => match merge::subsumes_f(pk, pers, ar, h, &kp.1, &kp.2, &next.1, &next.2) {
            Err(e) => Err(e),
            Ok(true) => Ok(kept),
            Ok(false) => Err(clash_reject(pk, pers, ar, ld, kp.0.module, next.0.module, &c.name)),
        },
    }
}

/// con-leche: ConLeche/Frontend/Olean/Index.lean:129-135 freshOk
/// **Freshness**: no constant of the module's own part bears a loaded name.
pub fn fresh_ok(pk: &OleanPins, pers: &PersTier, ar: &EStore, m: &NIdx, ld: &HeaderLoads, ix: &NameIndex, own: &NamePositions) -> Result<(), CheckError> {
    match first_loaded(ix, own) {
        None => Ok(()),
        Some(i) => {
            let q = &own.consts[i];
            let src = match ix.first.get(&q.name) {
                Some(c) => header_loads_name_at(pk, ld, c.module),
                None => pk.anon.dup2(),
            };
            let t = text::cat({ const M: [u32; 7] = [109, 111, 100, 117, 108, 101, 32]; crate::kernel::core_types::code_points(&M) }, &view::name_text(pers, ar, m));
            let t = text::cat3(t, &{ const M: [u32; 10] = [32, 100, 101, 99, 108, 97, 114, 101, 115, 32]; crate::kernel::core_types::code_points(&M) }, &view::name_text(pers, ar, &q.name));
            let t = text::cat3(t, &{ const M: [u32; 19] = [44, 32, 119, 104, 105, 99, 104, 32, 116, 104, 101, 32, 109, 111, 100, 117, 108, 101, 32]; crate::kernel::core_types::code_points(&M) }, &view::name_text(pers, ar, &src));
            Err(core_types::invalid(text::cat(t, &{ const M: [u32; 16] = [32, 105, 116, 32, 108, 111, 97, 100, 115, 32, 115, 116, 111, 114, 101, 115]; crate::kernel::core_types::code_points(&M) })))
        }
    }
}

/// con-leche: ConLeche/Frontend/Olean/Index.lean:129-135 freshOk
/// `own.consts.find? (ix.first.contains ·.name)`, as a position.
pub fn first_loaded(ix: &NameIndex, own: &NamePositions) -> Option<usize> {
    let mut i = 0usize;
    while i < own.consts.len() {
        if ix.first.contains_key(&own.consts[i].name) {
            return Some(i);
        }
        i += 1;
    }
    None
}

/// con-leche: ConLeche/Frontend/Olean/Index.lean:137-146 importsModulesOk
/// Is the part at position `k` of the module system (a part the index lacks is
/// not).
pub fn part_is_module(ix: &NameIndex, k: u64) -> bool {
    let i = k as usize;
    if i < ix.parts.len() {
        ix.parts[i].header.is_module
    } else {
        false
    }
}

/// con-leche: ConLeche/Frontend/Olean/Index.lean:137-146 importsModulesOk
/// **Lean's refusal of a classic import from a module**: every import of a root
/// of the module system is of the module system.
pub fn imports_modules_ok(pers: &PersTier, ar: &EStore, m: &NIdx, is_module: bool, ld: &HeaderLoads, ix: &NameIndex, imports: &Vec<ImportRec>) -> Result<(), CheckError> {
    if !is_module {
        return Ok(());
    }
    match first_classic(ld, ix, imports) {
        None => Ok(()),
        Some(i) => {
            let t = text::cat({ const M: [u32; 7] = [109, 111, 100, 117, 108, 101, 32]; crate::kernel::core_types::code_points(&M) }, &view::name_text(pers, ar, m));
            let t = text::cat3(t, &{ const M: [u32; 30] = [32, 111, 102, 32, 116, 104, 101, 32, 109, 111, 100, 117, 108, 101, 32, 115, 121, 115, 116, 101, 109, 32, 105, 109, 112, 111, 114, 116, 115, 32]; crate::kernel::core_types::code_points(&M) }, &view::name_text(pers, ar, &imports[i].module));
            Err(core_types::invalid(text::cat(t, &{ const M: [u32; 14] = [44, 32, 119, 104, 105, 99, 104, 32, 105, 115, 32, 110, 111, 116]; crate::kernel::core_types::code_points(&M) })))
        }
    }
}

/// con-leche: ConLeche/Frontend/Olean/Index.lean:137-146 importsModulesOk
/// An import of a loaded module outside the module system.
pub fn classic_import(ld: &HeaderLoads, ix: &NameIndex, i: &ImportRec) -> bool {
    match ld.index.get(&i.module) {
        Some(k) => !part_is_module(ix, *k),
        None => false,
    }
}

/// con-leche: ConLeche/Frontend/Olean/Index.lean:137-146 importsModulesOk
/// The first `classic_import`, as a position.
pub fn first_classic(ld: &HeaderLoads, ix: &NameIndex, imports: &Vec<ImportRec>) -> Option<usize> {
    let mut i = 0usize;
    while i < imports.len() {
        if classic_import(ld, ix, &imports[i]) {
            return Some(i);
        }
        i += 1;
    }
    None
}

/// con-leche: ConLeche/Frontend/Olean/Index.lean:150-161 WorkerReads
/// **What a worker reads before its own records.**
pub struct WorkerReads {
    /// the module's own private part's name positions and header
    pub own: NamePositions,
    /// what Lean loads for it
    pub loads: HeaderLoads,
    /// each loaded module's public-import closure (`levels::pub_closures`)
    pub pub_: Vec<Vec<u8>>,
    /// the loaded parts' names
    pub index: NameIndex,
    /// every name two loaded modules hold, its copies merged by Lean's rule
    pub clashes: Vec<Clash>,
}

/// con-leche: ConLeche/Frontend/Olean/Index.lean:179-185 clashCopies
/// **The doubly held names, each with all its copies, in the load order**: the
/// names in the order of their second copies, each with its first copy and then
/// its later ones.
pub fn clash_copies(ix: &NameIndex) -> Vec<(NIdx, Vec<Copy>)> {
    let mut at: HashMap2<NIdx, u64> = HashMap2::new();
    let mut out: Vec<(NIdx, Vec<Copy>)> = Vec::new();
    let mut i = 0usize;
    while i < ix.more.len() {
        clash_copies_step(ix, &mut at, &mut out, &ix.more[i].0, &ix.more[i].1);
        i += 1;
    }
    out
}

/// con-leche: ConLeche/Frontend/Olean/Index.lean:172-177 ccOrderStep
/// One later copy `c` of `n`: onto its name's entry, or a new entry with the
/// first copy and it.
pub fn clash_copies_step(ix: &NameIndex, at: &mut HashMap2<NIdx, u64>, out: &mut Vec<(NIdx, Vec<Copy>)>, n: &NIdx, c: &Copy) {
    match at_of(at, n) {
        Some(k) => out[k as usize].1.push(c.dup2()),
        None => {
            let mut cs: Vec<Copy> = Vec::with_capacity(2);
            cs.push(first_or(ix, n, c));
            cs.push(c.dup2());
            at.insert(n.dup2(), out.len() as u64);
            out.push((n.dup2(), cs));
        }
    }
}

/// con-leche: ConLeche/Frontend/Olean/Index.lean:172-177 ccOrderStep
/// A name's entry in the list so far (`acc.1.contains x.1`).
pub fn at_of(at: &HashMap2<NIdx, u64>, n: &NIdx) -> Option<u64> {
    match at.get(n) {
        Some(k) => Some(*k),
        None => None,
    }
}

/// con-leche: ConLeche/Frontend/Olean/Index.lean:163-170 ccStep
/// `(first[n]?).getD c`.
pub fn first_or(ix: &NameIndex, n: &NIdx, c: &Copy) -> Copy {
    match ix.first.get(n) {
        Some(f) => f.dup2(),
        None => c.dup2(),
    }
}

/// con-leche: ConLeche/Frontend/Olean/Index.lean:187-192 NamePositions.withImports
/// **A worker's own part with imports added** (a compared challenge's): the
/// header's imports followed by `x`, and no constant of its own.  Without
/// imports to add, the part itself.
pub fn name_positions_with_imports(own: NamePositions, x: &Vec<ImportRec>) -> NamePositions {
    if x.len() == 0 {
        own
    } else {
        let mut imports = own.header.imports;
        let mut i = 0usize;
        while i < x.len() {
            imports.push(levels::import_rec_dup(&x[i]));
            i += 1;
        }
        NamePositions { header: ModHeader { is_module: own.header.is_module, imports }, consts: Vec::new() }
    }
}

/// con-leche: ConLeche/Frontend/Olean/Index.lean:194-242 workerReads
/// The loaded parts' name tables, in the load order.
pub fn loaded_parts<F: CheckerFs>(fs: &F, pk: &OleanPins, pers: &PersTier, ar: &mut EStore, sp: &files::Roots, ld: &HeaderLoads) -> Result<Vec<NamePositions>, CheckError> {
    let mut parts: Vec<NamePositions> = Vec::with_capacity(ld.order.len());
    let mut i = 0usize;
    while i < ld.order.len() {
        match files::read_part_names(fs, pk, pers, ar, sp, &ld.order[i], &header_loads_level_at(ld, i as u64)) {
            Err(e) => return Err(e),
            Ok(p) => parts.push(p),
        }
        i += 1;
    }
    Ok(parts)
}

/// con-leche: ConLeche/Frontend/Olean/Index.lean:194-242 workerReads
/// `(infos[c]?).map fun (s, k) => (c, s, k)`.
pub fn info_of(infos: &HashMap2<Copy, (StmtRec, CKindF<NIdx, ()>)>, c: &Copy) -> Option<(Copy, StmtRec, CKindF<NIdx, ()>)> {
    match infos.get(c) {
        Some(x) => Some((c.dup2(), stmt_rec_dup(&x.0), c_kind_names_dup(&x.1))),
        None => None,
    }
}

/// con-leche: ConLeche/Frontend/Olean/Index.lean:194-242 workerReads
/// Every name's copies, read: each with its statement and kind.
pub fn clashes_of(cc: Vec<(NIdx, Vec<Copy>)>, infos: &HashMap2<Copy, (StmtRec, CKindF<NIdx, ()>)>) -> Vec<Clash> {
    let mut out: Vec<Clash> = Vec::with_capacity(cc.len());
    let mut i = 0usize;
    while i < cc.len() {
        let cs = &cc[i].1;
        let mut copies: Vec<(Copy, StmtRec, CKindF<NIdx, ()>)> = Vec::with_capacity(cs.len());
        let mut k = 0usize;
        while k < cs.len() {
            match info_of(infos, &cs[k]) {
                Some(x) => copies.push(x),
                None => {}
            }
            k += 1;
        }
        out.push(Clash { name: cc[i].0.dup2(), copies });
        i += 1;
    }
    out
}

/// con-leche: ConLeche/Frontend/Olean/Index.lean:194-242 workerReads
/// The heads `isPropCheap` asks the type of, at the axiom/axiom pairs: of each
/// clash whose first copy is an axiom, its type's head's first copy.
pub fn clash_heads(pers: &PersTier, ar: &EStore, ix: &NameIndex, clashes: &Vec<Clash>) -> Result<Vec<Copy>, CheckError> {
    let mut acc: Vec<Copy> = Vec::new();
    let mut i = 0usize;
    while i < clashes.len() {
        match clash_head(pers, ar, ix, &clashes[i]) {
            Err(e) => return Err(e),
            Ok(Some(c)) => acc.push(c),
            Ok(None) => {}
        }
        i += 1;
    }
    Ok(acc)
}

/// con-leche: ConLeche/Frontend/Olean/Index.lean:194-242 workerReads
/// The head of one clash: of a clash whose first copy is an axiom, its type's
/// head's first copy.
pub fn clash_head(pers: &PersTier, ar: &EStore, ix: &NameIndex, cl: &Clash) -> Result<Option<Copy>, CheckError> {
    if cl.copies.len() == 0 {
        return Ok(None);
    }
    match &cl.copies[0].2 {
        CKindF::Ax(_) => match merge::is_prop_cheap_head_of(pers, ar, &cl.copies[0].1.ty) {
            Err(e) => Err(e),
            Ok(None) => Ok(None),
            Ok(Some(n)) => match ix.first.get(&n) {
                Some(c) => Ok(Some(c.dup2())),
                None => Ok(None),
            },
        },
        _ => Ok(None),
    }
}

/// con-leche: ConLeche/Frontend/Olean/Index.lean:194-242 workerReads
/// The clash rule over every clash, in order.
pub fn clashes_ok(pk: &OleanPins, pers: &PersTier, ar: &EStore, ld: &HeaderLoads, h: &HeadTys, clashes: &Vec<Clash>) -> Result<(), CheckError> {
    let mut i = 0usize;
    while i < clashes.len() {
        match clash_ok(pk, pers, ar, ld, h, &clashes[i]) {
            Err(e) => return Err(e),
            Ok(()) => {}
        }
        i += 1;
    }
    Ok(())
}

/// con-leche: ConLeche/Frontend/Olean/Index.lean:194-242 workerReads
/// `cc.flatMap (·.2)`.
pub fn all_copies(cc: &Vec<(NIdx, Vec<Copy>)>) -> Vec<Copy> {
    let mut out: Vec<Copy> = Vec::new();
    let mut i = 0usize;
    while i < cc.len() {
        let mut k = 0usize;
        while k < cc[i].1.len() {
            out.push(cc[i].1[k].dup2());
            k += 1;
        }
        i += 1;
    }
    out
}

/// con-leche: ConLeche/Frontend/Olean/Index.lean:194-242 workerReads
/// **Phases 1 and 2 of a worker at module `m`**: its own part's header and
/// names; the header fixpoint; each loaded module's public-import closure; the
/// name index of the loaded parts; Lean's refusal of a classic import from a
/// module, the clash rule over every loaded name and freshness, each a reject
/// (exit 1) naming what it found.  `x`: imports added to the header
/// (`name_positions_with_imports`; a compared challenge's solution).
pub fn worker_reads<F: CheckerFs>(fs: &F, pk: &OleanPins, pers: &PersTier, ar: &mut EStore, sp: &files::Roots, m: &NIdx, x: &Vec<ImportRec>) -> Result<WorkerReads, CheckError> {
    let own = match files::read_part_names(fs, pk, pers, ar, sp, m, &OLeanLevel::Private) {
        Err(e) => return Err(e),
        Ok(o) => name_positions_with_imports(o, x),
    };
    let ld = match levels::header_fixpoint(fs, pk, pers, ar, sp, own.header.is_module, &own.header.imports) {
        Err(e) => return Err(e),
        Ok(ld) => ld,
    };
    let ix = match loaded_parts(fs, pk, pers, ar, sp, &ld) {
        Err(e) => return Err(e),
        Ok(parts) => name_index_of(parts),
    };
    match imports_modules_ok(pers, ar, m, own.header.is_module, &ld, &ix, &own.header.imports) {
        Err(e) => return Err(e),
        Ok(()) => {}
    }
    let cc = clash_copies(&ix);
    let infos = match read_infos(fs, pk, pers, ar, sp, &ld, &ix, &all_copies(&cc)) {
        Err(e) => return Err(e),
        Ok(i) => i,
    };
    let clashes = clashes_of(cc, &infos);
    let heads = match clash_heads(pers, ar, &ix, &clashes) {
        Err(e) => return Err(e),
        Ok(h) => h,
    };
    let hinfos = match read_infos(fs, pk, pers, ar, sp, &ld, &ix, &heads) {
        Err(e) => return Err(e),
        Ok(i) => i,
    };
    match clashes_ok(pk, pers, ar, &ld, &head_tys_of(&ix, &hinfos, &heads), &clashes) {
        Err(e) => return Err(e),
        Ok(()) => {}
    }
    match fresh_ok(pk, pers, ar, m, &ld, &ix, &own) {
        Err(e) => return Err(e),
        Ok(()) => {}
    }
    let pub_ = levels::pub_closures(&ld);
    Ok(WorkerReads { own, loads: ld, pub_, index: ix, clashes })
}
