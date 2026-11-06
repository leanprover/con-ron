//! `ConLeche/Frontend/Olean/View.lean` — a module's views (task #142).
//!
//! A module of the module system has three files, each holding one `ModuleData`,
//! the view of the module at one level.  A view reads the files up to its own.
//! `decodeModuleSpec` is the specification and is `noncomputable`, so it is not
//! ported (`scripts/provenance-skip.txt`).
//!
//! ## Deviations
//!
//! * `ModFiles.viewRegion`'s `Region` borrows a file or owns a concatenation, so
//!   it is [`ViewBytes`], and [`view_bytes_region`] is the region over it.
//! * `(parseAllViews f)` of a classic module holds one decoded value three times
//!   in the Lean; here it is copied (`mod_decoded_dup`): a home's read only.
//! * Module names are handles, rendered through `env::read_name`.

use crate::arena::env;
use crate::arena::handle::{EIdx, NIdx};
use crate::arena::store::{EStore, PersTier};
use crate::frontend::olean::fast;
use crate::frontend::olean::header;
use crate::frontend::olean::reads;
use crate::frontend::olean::reads::NamePositions;
use crate::frontend::olean::region;
use crate::frontend::olean::region::{Part, Region, RegionBuf};
use crate::frontend::olean::spec;
use crate::frontend::olean::spec::{CEntryF, ModDecoded, OleanPins, RdErr, StmtRec};
use crate::frontend::text;
use crate::kernel::core_types;
use crate::kernel::core_types::CheckError;
use crate::kernel::name;

/// con-leche: ConLeche/Frontend/Olean/View.lean:40-46 OLeanLevel
/// **The level of a view.**  Each level includes the previous ones.
pub enum OLeanLevel {
    Exported,
    Server,
    Private,
}

/// con-leche: ConLeche/Frontend/Olean/View.lean:48-53 ModFiles
/// **A module's files**: `M.olean`, and those of the two others at hand.
pub struct ModFiles {
    pub exported: Part,
    pub server: Option<Part>,
    pub private_part: Option<Part>,
}

/// con-leche: ConLeche/Frontend/Olean/View.lean:55-59 ModFiles.isModule
/// Does `M.olean` say it is of a module of the module system.
pub fn mod_files_is_module(f: &ModFiles) -> bool {
    let r: Region = region::region_single(&f.exported);
    match spec::module_skel(&f.exported.bytes, &r, region::part_module_data_addr(&f.exported)) {
        Some(sk) => sk.is_module,
        None => false,
    }
}

/// con-leche: ConLeche/Frontend/Olean/View.lean:61-77 ModFiles.viewRegion
/// A view's bytes: one file, or the files up to its own laid end to end.
pub enum ViewBytes {
    Exported,
    Joined(RegionBuf),
}

/// con-leche: ConLeche/Frontend/Olean/View.lean:61-77 ModFiles.viewRegion
/// The bytes of a view.
pub fn view_bytes<'a>(f: &'a ModFiles, v: &'a ViewBytes) -> &'a [u8] {
    match v {
        ViewBytes::Exported => &f.exported.bytes,
        ViewBytes::Joined(b) => &b.bytes,
    }
}

/// con-leche: ConLeche/Frontend/Olean/View.lean:61-77 ModFiles.viewRegion
/// The region of a view.
pub fn view_region_of(f: &ModFiles, v: &ViewBytes) -> Region {
    match v {
        ViewBytes::Exported => region::region_single(&f.exported),
        ViewBytes::Joined(b) => region_dup(&b.region),
    }
}

/// con-leche: ConLeche/Frontend/Olean/View.lean:61-77 ModFiles.viewRegion
/// A region's record, copied.
pub fn region_dup(r: &Region) -> Region {
    let mut segs: Vec<region::Seg> = Vec::with_capacity(r.segs.len());
    let mut i = 0usize;
    while i < r.segs.len() {
        segs.push(region::Seg { base: r.segs[i].base, off: r.segs[i].off, size: r.segs[i].size });
        i += 1;
    }
    Region { segs }
}

/// con-leche: ConLeche/Frontend/Olean/View.lean:61-77 ModFiles.viewRegion
/// The `.server` arm: both files, when the module has them.
pub fn view_server(f: &ModFiles) -> Option<(ViewBytes, u64)> {
    match &f.server {
        None => None,
        Some(s) => {
            match region::region_of_parts2(&f.exported, s) {
                Err(_) => None,
                Ok(b) => Some((ViewBytes::Joined(b), region::part_module_data_addr(s))),
            }
        }
    }
}

/// con-leche: ConLeche/Frontend/Olean/View.lean:61-77 ModFiles.viewRegion
/// The `.private` arm: all three files, when the module has them.
pub fn view_private(f: &ModFiles) -> Option<(ViewBytes, u64)> {
    match (&f.server, &f.private_part) {
        (Some(s), Some(p)) => {
            match region::region_of_parts3(&f.exported, s, p) {
                Err(_) => None,
                Ok(b) => Some((ViewBytes::Joined(b), region::part_module_data_addr(p))),
            }
        }
        _ => None,
    }
}

/// con-leche: ConLeche/Frontend/Olean/View.lean:61-77 ModFiles.viewRegion
/// **The region and the address of a view**: the files up to its own (the whole
/// of a classic module).
pub fn mod_files_view_region(f: &ModFiles, level: &OLeanLevel) -> Option<(ViewBytes, u64)> {
    match level {
        OLeanLevel::Exported => Some((ViewBytes::Exported, region::part_module_data_addr(&f.exported))),
        OLeanLevel::Server => {
            if mod_files_is_module(f) {
                view_server(f)
            } else {
                Some((ViewBytes::Exported, region::part_module_data_addr(&f.exported)))
            }
        }
        OLeanLevel::Private => {
            if mod_files_is_module(f) {
                view_private(f)
            } else {
                Some((ViewBytes::Exported, region::part_module_data_addr(&f.exported)))
            }
        }
    }
}

/// con-leche: ConLeche/Frontend/Olean/View.lean:87-92 parseView
/// `unless importsPre f.exported.bytes == some d.imports do none`, with `d`.
pub fn check_imports_pre(pk: &OleanPins, pers: &PersTier, ar: &mut EStore, f: &ModFiles, d: ModDecoded) -> Result<ModDecoded, RdErr> {
    match header::imports_pre(pk, pers, ar, &f.exported.bytes) {
        Err(RdErr::Bad) => Err(RdErr::Bad),
        Err(e) => Err(e),
        Ok(pre) => {
            if spec::imports_beq(&pre, &d.imports) {
                Ok(d)
            } else {
                Err(RdErr::Bad)
            }
        }
    }
}

/// con-leche: ConLeche/Frontend/Olean/View.lean:87-92 parseView
/// **One view**, fast: what it reaches, each object once.
pub fn parse_view(pk: &OleanPins, pers: &PersTier, ar: &mut EStore, f: &ModFiles, level: &OLeanLevel) -> Result<ModDecoded, RdErr> {
    match mod_files_view_region(f, level) {
        None => Err(RdErr::Bad),
        Some((vb, a)) => {
            let bs = view_bytes(f, &vb);
            let r: Region = view_region_of(f, &vb);
            match fast::parse_at(pk, pers, ar, bs, &r, a) {
                Err(e) => Err(e),
                Ok(d) => check_imports_pre(pk, pers, ar, f, d),
            }
        }
    }
}

/// con-leche: ConLeche/Frontend/Olean/View.lean:94-98 AllViews
/// All three views of a module.
pub struct AllViews {
    pub exported: ModDecoded,
    pub server: ModDecoded,
    pub private_part: ModDecoded,
}

/// con-leche: ConLeche/Frontend/Olean/View.lean:100-123 parseAllViews
/// A stored constant, copied.
pub fn c_entry_dup(c: &CEntryF<NIdx, EIdx>) -> CEntryF<NIdx, EIdx> {
    use crate::ron::hashmap::Dup;
    CEntryF {
        name: c.name.dup2(),
        level_params: env::nidx_vec_dup(&c.level_params),
        ty: c.ty.dup2(),
        kind: c_kind_dup(&c.kind),
    }
}

/// con-leche: ConLeche/Frontend/Olean/View.lean:100-123 parseAllViews
/// A stored constant's kind, copied.
pub fn c_kind_dup(k: &spec::CKindF<NIdx, EIdx>) -> spec::CKindF<NIdx, EIdx> {
    use crate::ron::hashmap::Dup;
    use spec::CKindF;
    match k {
        CKindF::Ax(u) => CKindF::Ax(*u),
        CKindF::Defn(v, h, s) => CKindF::Defn(v.dup2(), spec::hints_dup(h), crate::kernel::expr::str_copy(s)),
        CKindF::Thm(v, all) => CKindF::Thm(v.dup2(), env::nidx_vec_dup(all)),
        CKindF::Opaq(v, u) => CKindF::Opaq(v.dup2(), *u),
        CKindF::Quot(s) => CKindF::Quot(crate::kernel::expr::str_copy(s)),
        CKindF::Induct(np, ni, all, cs, nn, ir, iu, irf) => {
            CKindF::Induct(*np, *ni, env::nidx_vec_dup(all), env::nidx_vec_dup(cs), *nn, *ir, *iu, *irf)
        }
        CKindF::Ctor(ind, ci, np, nf, iu) => CKindF::Ctor(ind.dup2(), *ci, *np, *nf, *iu),
        CKindF::Recur(all, np, ni, nmo, nmi, rules, k2, iu) => {
            CKindF::Recur(env::nidx_vec_dup(all), *np, *ni, *nmo, *nmi, rules_dup(rules), *k2, *iu)
        }
    }
}

/// con-leche: ConLeche/Frontend/Olean/View.lean:100-123 parseAllViews
/// A recursor's rules, copied.
pub fn rules_dup(rs: &Vec<(NIdx, u64, EIdx)>) -> Vec<(NIdx, u64, EIdx)> {
    use crate::ron::hashmap::Dup;
    let mut out: Vec<(NIdx, u64, EIdx)> = Vec::with_capacity(rs.len());
    let mut i = 0usize;
    while i < rs.len() {
        out.push((rs[i].0.dup2(), rs[i].1, rs[i].2.dup2()));
        i += 1;
    }
    out
}

/// con-leche: ConLeche/Frontend/Olean/View.lean:100-123 parseAllViews
/// A view, copied.
pub fn mod_decoded_dup(d: &ModDecoded) -> ModDecoded {
    use crate::ron::hashmap::Dup;
    let mut imports: Vec<spec::ImportRec> = Vec::with_capacity(d.imports.len());
    let mut i = 0usize;
    while i < d.imports.len() {
        let x = &d.imports[i];
        imports.push(spec::ImportF { module: x.module.dup2(), import_all: x.import_all, is_exported: x.is_exported, is_meta: x.is_meta });
        i += 1;
    }
    let mut constants: Vec<CEntryF<NIdx, EIdx>> = Vec::with_capacity(d.constants.len());
    let mut k = 0usize;
    while k < d.constants.len() {
        constants.push(c_entry_dup(&d.constants[k]));
        k += 1;
    }
    ModDecoded { is_module: d.is_module, imports, constants }
}

/// con-leche: ConLeche/Frontend/Olean/View.lean:100-123 parseAllViews
/// `(r.loc a).isSome`.
pub fn loc_is_some(r: &Region, a: u64) -> bool {
    match region::region_loc(r, a) {
        Some(_) => true,
        None => false,
    }
}

/// con-leche: ConLeche/Frontend/Olean/View.lean:100-123 parseAllViews
/// `(r2.loc as).isSome` in the region of the first two files, which must be one.
pub fn loc_in_two(a: &Part, b: &Part, addr: u64) -> bool {
    match region::region_of_parts2(a, b) {
        Err(_) => false,
        Ok(b2) => loc_is_some(&b2.region, addr),
    }
}

/// con-leche: ConLeche/Frontend/Olean/View.lean:100-123 parseAllViews
/// The module-system arm: one memo over all three files.
pub fn parse_all_views_module(pk: &OleanPins, pers: &PersTier, ar: &mut EStore, f: &ModFiles, s: &Part, p: &Part) -> Result<AllViews, RdErr> {
    let ae = region::part_module_data_addr(&f.exported);
    let a_s = region::part_module_data_addr(s);
    let ap = region::part_module_data_addr(p);
    let r1: Region = region::region_single(&f.exported);
    if !loc_is_some(&r1, ae) {
        return Err(RdErr::Bad);
    }
    if !loc_in_two(&f.exported, s, a_s) {
        return Err(RdErr::Bad);
    }
    let b: RegionBuf = match region::region_of_parts3(&f.exported, s, p) {
        Err(_) => return Err(RdErr::Bad),
        Ok(b) => b,
    };
    let mut addrs: Vec<u64> = Vec::with_capacity(3);
    addrs.push(ae);
    addrs.push(a_s);
    addrs.push(ap);
    let mut ds: Vec<ModDecoded> = match fast::parse_many(pk, pers, ar, &b.bytes, &b.region, &addrs) {
        Err(e) => return Err(e),
        Ok(ds) => ds,
    };
    if ds.len() != 3 {
        return Err(RdErr::Bad);
    }
    let dp = fast::take_decoded(&mut ds, 2);
    let d_s = fast::take_decoded(&mut ds, 1);
    let de = fast::take_decoded(&mut ds, 0);
    match header::imports_pre(pk, pers, ar, &f.exported.bytes) {
        Err(e) => Err(e),
        Ok(pre) => {
            if spec::imports_beq(&pre, &de.imports) && spec::imports_beq(&pre, &d_s.imports) && spec::imports_beq(&pre, &dp.imports) {
                Ok(AllViews { exported: de, server: d_s, private_part: dp })
            } else {
                Err(RdErr::Bad)
            }
        }
    }
}

/// con-leche: ConLeche/Frontend/Olean/View.lean:100-123 parseAllViews
/// **All three views, each object once**, whatever views reach it.
pub fn parse_all_views(pk: &OleanPins, pers: &PersTier, ar: &mut EStore, f: &ModFiles) -> Result<AllViews, RdErr> {
    if mod_files_is_module(f) {
        match (&f.server, &f.private_part) {
            (Some(s), Some(p)) => parse_all_views_module(pk, pers, ar, f, s, p),
            _ => Err(RdErr::Bad),
        }
    } else {
        match parse_view(pk, pers, ar, f, &OLeanLevel::Exported) {
            Err(e) => Err(e),
            Ok(d) => {
                let d2 = mod_decoded_dup(&d);
                let d3 = mod_decoded_dup(&d);
                Ok(AllViews { exported: d, server: d2, private_part: d3 })
            }
        }
    }
}

/// con-leche: ConLeche/Frontend/Olean/View.lean:125-129 AllViews.at
/// A view at a level.
pub fn all_views_at<'a>(v: &'a AllViews, level: &OLeanLevel) -> &'a ModDecoded {
    match level {
        OLeanLevel::Exported => &v.exported,
        OLeanLevel::Server => &v.server,
        OLeanLevel::Private => &v.private_part,
    }
}

/// con-leche: ConLeche/Frontend/Olean/View.lean:131-135 ModFiles.upTo
/// **The files a view reads** of a module's.  Deviation: consumes the record.
pub fn mod_files_up_to(f: ModFiles, level: &OLeanLevel) -> ModFiles {
    match level {
        OLeanLevel::Exported => ModFiles { exported: f.exported, server: None, private_part: None },
        OLeanLevel::Server => ModFiles { exported: f.exported, server: f.server, private_part: None },
        OLeanLevel::Private => f,
    }
}

/// con-leche: ConLeche/Frontend/Olean/View.lean:146-150 readNamePositions
/// **Per constant of a view, its position, name, kind and filter**.
pub fn read_name_positions(pk: &OleanPins, pers: &PersTier, ar: &mut EStore, f: &ModFiles, level: &OLeanLevel) -> Result<NamePositions, RdErr> {
    match mod_files_view_region(f, level) {
        None => Err(RdErr::Bad),
        Some((vb, a)) => {
            let bs = view_bytes(f, &vb);
            let r: Region = view_region_of(f, &vb);
            reads::name_positions_at(pk, pers, ar, bs, &r, a)
        }
    }
}

/// con-leche: ConLeche/Frontend/Olean/View.lean:152-155 readEntry
/// **The constant at a position of a view**, read with a memo of its own.
pub fn read_entry(pk: &OleanPins, pers: &PersTier, ar: &mut EStore, f: &ModFiles, level: &OLeanLevel, c: u64) -> Result<CEntryF<NIdx, EIdx>, RdErr> {
    match mod_files_view_region(f, level) {
        None => Err(RdErr::Bad),
        Some((vb, _)) => {
            let bs = view_bytes(f, &vb);
            let r: Region = view_region_of(f, &vb);
            reads::entry_at(pk, pers, ar, bs, &r, c)
        }
    }
}

/// con-leche: ConLeche/Frontend/Olean/View.lean:157-160 readStmts
/// **The statements of the constants at some positions of a view**, read together.
pub fn read_stmts(pk: &OleanPins, pers: &PersTier, ar: &mut EStore, f: &ModFiles, level: &OLeanLevel, cs: &Vec<u64>) -> Result<Vec<StmtRec>, RdErr> {
    match mod_files_view_region(f, level) {
        None => Err(RdErr::Bad),
        Some((vb, _)) => {
            let bs = view_bytes(f, &vb);
            let r: Region = view_region_of(f, &vb);
            reads::stmts_at(pk, pers, ar, bs, &r, cs)
        }
    }
}

/// con-leche: none — `s!"{m}"` of a module's name, a handle
pub fn name_text(pers: &PersTier, ar: &EStore, m: &NIdx) -> Vec<u32> {
    match env::read_name(pers, ar, m) {
        Ok(n) => name::render(&n),
        Err(_) => { const M: [u32; 1] = [63]; crate::kernel::core_types::code_points(&M) },
    }
}

/// con-leche: ConLeche/Frontend/Olean/View.lean:164-167 undecodable
/// The module's files do not decode.
pub fn undecodable(pers: &PersTier, ar: &EStore, m: &NIdx) -> CheckError {
    let t = text::cat({ const M: [u32; 7] = [109, 111, 100, 117, 108, 101, 32]; crate::kernel::core_types::code_points(&M) }, &name_text(pers, ar, m));
    core_types::internal(text::cat(t, &{ const M: [u32; 105] = [58, 32, 109, 97, 108, 102, 111, 114, 109, 101, 100, 32, 46, 111, 108, 101, 97, 110, 32, 100, 97, 116, 97, 32, 40, 97, 110, 32, 111, 98, 106, 101, 99, 116, 32, 111, 102, 32, 116, 104, 101, 32, 119, 114, 111, 110, 103, 32, 115, 104, 97, 112, 101, 44, 32, 111, 114, 32, 97, 32, 112, 111, 105, 110, 116, 101, 114, 32, 116, 104, 97, 116, 32, 100, 111, 101, 115, 32, 110, 111, 116, 32, 112, 111, 105, 110, 116, 32, 98, 101, 108, 111, 119, 32, 105, 116, 115, 32, 111, 98, 106, 101, 99, 116, 41]; crate::kernel::core_types::code_points(&M) }))
}

/// con-leche: ConLeche/Frontend/Olean/View.lean:40-46 OLeanLevel
/// `repr level`.
pub fn level_repr(level: &OLeanLevel) -> Vec<u32> {
    match level {
        OLeanLevel::Exported => { const M: [u32; 43] = [67, 111, 110, 76, 101, 99, 104, 101, 46, 70, 114, 111, 110, 116, 101, 110, 100, 46, 79, 108, 101, 97, 110, 46, 79, 76, 101, 97, 110, 76, 101, 118, 101, 108, 46, 101, 120, 112, 111, 114, 116, 101, 100]; crate::kernel::core_types::code_points(&M) },
        OLeanLevel::Server => { const M: [u32; 41] = [67, 111, 110, 76, 101, 99, 104, 101, 46, 70, 114, 111, 110, 116, 101, 110, 100, 46, 79, 108, 101, 97, 110, 46, 79, 76, 101, 97, 110, 76, 101, 118, 101, 108, 46, 115, 101, 114, 118, 101, 114]; crate::kernel::core_types::code_points(&M) },
        OLeanLevel::Private => { const M: [u32; 42] = [67, 111, 110, 76, 101, 99, 104, 101, 46, 70, 114, 111, 110, 116, 101, 110, 100, 46, 79, 108, 101, 97, 110, 46, 79, 76, 101, 97, 110, 76, 101, 118, 101, 108, 46, 112, 114, 105, 118, 97, 116, 101]; crate::kernel::core_types::code_points(&M) },
    }
}

/// con-leche: ConLeche/Frontend/Olean/View.lean:169-181 viewError
/// Why a view does not read.
pub fn view_error(pk: &OleanPins, pers: &PersTier, ar: &mut EStore, m: &NIdx, f: &ModFiles, level: &OLeanLevel) -> CheckError {
    let pre = text::cat({ const M: [u32; 7] = [109, 111, 100, 117, 108, 101, 32]; crate::kernel::core_types::code_points(&M) }, &name_text(pers, ar, m));
    match mod_files_view_region(f, level) {
        None => core_types::internal(text::cat(pre, &{ const M: [u32; 38] = [58, 32, 116, 104, 101, 32, 46, 111, 108, 101, 97, 110, 32, 102, 105, 108, 101, 115, 32, 111, 102, 32, 97, 32, 109, 111, 100, 117, 108, 101, 32, 111, 118, 101, 114, 108, 97, 112]; crate::kernel::core_types::code_points(&M) })),
        Some((vb, a)) => {
            let bs = view_bytes(f, &vb);
            let r: Region = view_region_of(f, &vb);
            match spec::const_names_ok(pk, pers, ar, bs, &r, a) {
                Err(e) => e,
                Ok(false) => {
                    let t = text::cat(pre, &{ const M: [u32; 6] = [58, 32, 116, 104, 101, 32]; crate::kernel::core_types::code_points(&M) });
                    let t = text::cat(t, &level_repr(level));
                    core_types::internal(text::cat(t, &{ const M: [u32; 77] = [32, 112, 97, 114, 116, 39, 115, 32, 110, 97, 109, 101, 32, 116, 97, 98, 108, 101, 32, 40, 99, 111, 110, 115, 116, 78, 97, 109, 101, 115, 41, 32, 100, 111, 101, 115, 32, 110, 111, 116, 32, 108, 105, 115, 116, 32, 105, 116, 115, 32, 99, 111, 110, 115, 116, 97, 110, 116, 115, 39, 32, 110, 97, 109, 101, 115, 44, 32, 101, 97, 99, 104, 32, 111, 110, 99, 101]; crate::kernel::core_types::code_points(&M) }))
                }
                Ok(true) => match fast::parse_at(pk, pers, ar, bs, &r, a) {
                    Ok(_) => {
                        let t = text::cat(pre, &{ const M: [u32; 6] = [58, 32, 116, 104, 101, 32]; crate::kernel::core_types::code_points(&M) });
                        let t = text::cat(t, &level_repr(level));
                        core_types::internal(text::cat(t, &{ const M: [u32; 56] = [32, 112, 97, 114, 116, 39, 115, 32, 105, 109, 112, 111, 114, 116, 115, 32, 97, 114, 101, 32, 110, 111, 116, 32, 116, 104, 111, 115, 101, 32, 97, 116, 32, 116, 104, 101, 32, 115, 116, 97, 114, 116, 32, 111, 102, 32, 105, 116, 115, 32, 46, 111, 108, 101, 97, 110]; crate::kernel::core_types::code_points(&M) }))
                    }
                    Err(RdErr::Err(e)) => e,
                    Err(RdErr::Bad) => undecodable(pers, ar, m),
                },
            }
        }
    }
}
