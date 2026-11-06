//! `ConLeche/Frontend/Olean/Header.lean` — a module's imports from the start of
//! its file (task #142).
//!
//! The root `ModuleData` is the last object of an `.olean`, but its imports are
//! its first field and the compactor copies depth first, so the imports' names,
//! the `Import` objects and the imports array are the file's first objects.  The
//! imports can be read off a prefix of the file.
//!
//! Deviation: `importsPre` interns the names it reads, so it takes the store;
//! `b.extract 0 e` is a subslice, no copy.

use crate::arena::store::{EStore, PersTier};
use crate::frontend::olean::region;
use crate::frontend::olean::region::{Region, Seg};
use crate::frontend::olean::spec;
use crate::frontend::olean::spec::{ImportRec, OleanPins, PtrRead, RdErr};
use crate::arena::handle::{EIdx, NIdx};

/// con-leche: ConLeche/Frontend/Olean/Header.lean:31-38 HdrWalk
/// The outcome of the walk to the imports array.
pub enum HdrWalk {
    Found(u64, u64),
    Short,
    Bad,
}

/// con-leche: ConLeche/Frontend/Olean/Header.lean:40-41 wordUp
/// An object size rounded up to a word (`u64::MAX` past the last word, as
/// `sat_add`).
pub fn word_up(n: u64) -> u64 {
    let k = region::sat_add(n, 7);
    if k == u64::MAX {
        u64::MAX
    } else {
        k / 8 * 8
    }
}

/// con-leche: ConLeche/Frontend/Olean/Header.lean:43-48 hdrAdv
/// The bytes an object of the import section takes at location `g`.
pub fn hdr_adv(b: &[u8], g: u64) -> u64 {
    if (region::rd_u8(b, g + 7) as u64) == region::TAG_STRING {
        word_up(region::sat_add(32, region::rd_u64(b, g + 8)))
    } else {
        word_up((region::rd_u8(b, g + 4) as u64) + 256 * (region::rd_u8(b, g + 5) as u64))
    }
}

/// con-leche: ConLeche/Frontend/Olean/Header.lean:50-65 hdrWalk
/// **The walk to the imports array** from location `g`.
pub fn hdr_walk(b: &[u8], g: u64) -> HdrWalk {
    let mut g = g;
    let size = b.len() as u64;
    loop {
        if region::sat_add(g, 16) > size {
            return HdrWalk::Short;
        }
        let t = region::rd_u8(b, g + 7) as u64;
        if t == region::TAG_ARRAY {
            let e = region::sat_add(g + 24, region::sat_mul8(region::rd_u64(b, g + 8)));
            if e <= size {
                return HdrWalk::Found(g, e);
            }
            return HdrWalk::Short;
        } else if t <= 243 || t == region::TAG_STRING || t == region::TAG_MPZ {
            let adv = hdr_adv(b, g);
            if adv < 8 {
                return HdrWalk::Bad;
            }
            g = region::sat_add(g, adv);
        } else {
            return HdrWalk::Bad;
        }
    }
}

/// con-leche: ConLeche/Frontend/Olean/Header.lean:67-73 importsIn
/// The `nameP` of `ImportF.mapM (nameP r)`, as a pointer read.
pub struct NamePRead;

/// con-leche: ConLeche/Frontend/Olean/Header.lean:67-73 importsIn
impl PtrRead for NamePRead {
    /// con-leche: ConLeche/Frontend/Olean/Header.lean:67-73 importsIn
    fn rd_name(&self, pk: &OleanPins, pers: &PersTier, ar: &mut EStore, bs: &[u8], r: &Region, v: u64) -> Result<NIdx, RdErr> {
        spec::name_p(pk, pers, ar, bs, r, v)
    }

    /// con-leche: ConLeche/Frontend/Olean/Header.lean:67-73 importsIn
    /// Never asked: an import holds no expression.
    fn rd_expr(&self, _pk: &OleanPins, _pers: &PersTier, _ar: &mut EStore, _bs: &[u8], _r: &Region, _v: u64) -> Result<EIdx, RdErr> {
        Err(RdErr::Bad)
    }
}

/// con-leche: ConLeche/Frontend/Olean/Header.lean:67-73 importsIn
/// `imps.mapM fun i => importSkel r i >>= ImportF.mapM (nameP r)`.
pub fn imports_read(pk: &OleanPins, pers: &PersTier, ar: &mut EStore, bs: &[u8], r: &Region, imps: &Vec<u64>) -> Result<Vec<ImportRec>, RdErr> {
    let mut out: Vec<ImportRec> = Vec::with_capacity(imps.len());
    let mut i = 0usize;
    while i < imps.len() {
        match spec::import_skel(bs, r, imps[i]) {
            None => return Err(RdErr::Bad),
            Some(sk) => match spec::import_map(&NamePRead, pk, pers, ar, bs, r, &sk) {
                Err(e) => return Err(e),
                Ok(x) => out.push(x),
            },
        }
        i += 1;
    }
    Ok(out)
}

/// con-leche: ConLeche/Frontend/Olean/Header.lean:67-73 importsIn
/// The imports array at location `c` of a region, decoded.
pub fn imports_in(pk: &OleanPins, pers: &PersTier, ar: &mut EStore, bs: &[u8], r: &Region, c: u64) -> Result<Vec<ImportRec>, RdErr> {
    if region::region_tag(bs, c) != region::TAG_ARRAY {
        return Err(RdErr::Bad);
    }
    let n = region::rd_u64(bs, c + 8);
    if region::sat_add(c + 24, region::sat_mul8(n)) > region::region_file_end(r, c) {
        return Err(RdErr::Bad);
    }
    match region::region_obj_array_go(bs, r, c, c + 24, n, Vec::with_capacity(n as usize)) {
        None => Err(RdErr::Bad),
        Some(imps) => imports_read(pk, pers, ar, bs, r, &imps),
    }
}

/// con-leche: ConLeche/Frontend/Olean/Header.lean:75-83 importsPre
/// **A module's imports from the start of its exported file**: the walk to the
/// imports array, and the array decoded in the region of the bytes up to its end
/// (the base address from the header).
pub fn imports_pre(pk: &OleanPins, pers: &PersTier, ar: &mut EStore, b: &[u8]) -> Result<Vec<ImportRec>, RdErr> {
    match hdr_walk(b, region::DATA_START) {
        HdrWalk::Found(c, e) => {
            let pre: &[u8] = &b[0..(e as usize)];
            let mut segs: Vec<Seg> = Vec::with_capacity(1);
            segs.push(Seg { base: region::rd_u64(pre, 80), off: 0, size: e });
            imports_in(pk, pers, ar, pre, &Region { segs }, c)
        }
        _ => Err(RdErr::Bad),
    }
}
