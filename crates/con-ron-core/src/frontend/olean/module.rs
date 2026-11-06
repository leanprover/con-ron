//! `ConLeche/Frontend/Olean/Module.lean` — a module's views against each other
//! (task #142): what a module's home can check of its three views, read together.
//! A mismatch is malformed input (`.internal`, exit 3).
//!
//! Deviation: `Except String` is [`ExpoErr`], which also holds the store's capacity
//! decline.  "Expressions by the checker's equality" is handle equality: the store
//! is hash-consed, so that it is both pointer-equal first and structural.

use crate::arena::env;
use crate::arena::handle::{EIdx, NIdx};
use crate::arena::store::{EStore, PersTier};
use crate::frontend::olean::reads;
use crate::frontend::olean::region;
use crate::frontend::olean::region::{Part, Region, RegionBuf};
use crate::frontend::olean::spec;
use crate::frontend::olean::spec::{CEntryF, CKindF, OleanPins, RdErr};
use crate::frontend::olean::view;
use crate::frontend::olean::view::{AllViews, ModFiles};
use crate::frontend::scan_types::HintsRec;
use crate::frontend::text;
use crate::kernel::core_types;
use crate::kernel::core_types::CheckError;
use crate::kernel::name;
use crate::ron::hashmap::Dup;
use crate::ron::hashmap::Eq2;
use crate::ron::hashmap2::HashMap2;

/// con-leche: ConLeche/Frontend/Olean/Module.lean:30-39 Expo
/// **A private constant at the exported level.**
pub enum Expo {
    Same,
    Hidden,
    Absent,
}

/// con-leche: ConLeche/Frontend/Olean/Module.lean:30-39 Expo
/// `deriving` `Inhabited`'s copy.
pub fn expo_dup(e: &Expo) -> Expo {
    match e {
        Expo::Same => Expo::Same,
        Expo::Hidden => Expo::Hidden,
        Expo::Absent => Expo::Absent,
    }
}

/// con-leche: ConLeche/Frontend/Olean/Module.lean:41-44 hintsEq
pub fn hints_eq(a: &HintsRec, b: &HintsRec) -> bool {
    match (a, b) {
        (HintsRec::Abbrev, HintsRec::Abbrev) => true,
        (HintsRec::Opaque, HintsRec::Opaque) => true,
        (HintsRec::Regular(x), HintsRec::Regular(y)) => *x == *y,
        _ => false,
    }
}

/// con-leche: ConLeche/Frontend/Olean/Module.lean:46-49 rulesEq
pub fn rules_eq(a: &Vec<(NIdx, u64, EIdx)>, b: &Vec<(NIdx, u64, EIdx)>) -> bool {
    if a.len() != b.len() {
        return false;
    }
    let mut i = 0usize;
    while i < a.len() {
        if !(a[i].0.eq2(&b[i].0) && a[i].1 == b[i].1 && a[i].2.eq2(&b[i].2)) {
            return false;
        }
        i += 1;
    }
    true
}

/// con-leche: none — `List NIdx`'s `==`
pub fn nidx_list_eq(a: &Vec<NIdx>, b: &Vec<NIdx>) -> bool {
    if a.len() != b.len() {
        return false;
    }
    let mut i = 0usize;
    while i < a.len() {
        if !a[i].eq2(&b[i]) {
            return false;
        }
        i += 1;
    }
    true
}

/// con-leche: none — `List UInt64`'s `==`
pub fn u64_list_eq(a: &Vec<u64>, b: &Vec<u64>) -> bool {
    if a.len() != b.len() {
        return false;
    }
    let mut i = 0usize;
    while i < a.len() {
        if a[i] != b[i] {
            return false;
        }
        i += 1;
    }
    true
}

/// con-leche: ConLeche/Frontend/Olean/Module.lean:51-67 entrySame
/// The `match` of `entrySame`: the kinds.
pub fn kinds_same(a: &CKindF<NIdx, EIdx>, b: &CKindF<NIdx, EIdx>) -> bool {
    match (a, b) {
        (CKindF::Ax(u), CKindF::Ax(u2)) => *u == *u2,
        (CKindF::Defn(v, h, s), CKindF::Defn(v2, h2, s2)) => {
            v.eq2(v2) && hints_eq(h, h2) && crate::kernel::name::str_eq(s, s2)
        }
        (CKindF::Thm(v, al), CKindF::Thm(v2, al2)) => v.eq2(v2) && nidx_list_eq(al, al2),
        (CKindF::Opaq(v, u), CKindF::Opaq(v2, u2)) => v.eq2(v2) && *u == *u2,
        (CKindF::Quot(k), CKindF::Quot(k2)) => crate::kernel::name::str_eq(k, k2),
        (CKindF::Induct(x1, x2, x3, x4, x5, x6, x7, x8), CKindF::Induct(y1, y2, y3, y4, y5, y6, y7, y8)) => {
            *x1 == *y1 && *x2 == *y2 && nidx_list_eq(x3, y3) && nidx_list_eq(x4, y4) && *x5 == *y5 && *x6 == *y6 && *x7 == *y7 && *x8 == *y8
        }
        (CKindF::Ctor(x1, x2, x3, x4, x5), CKindF::Ctor(y1, y2, y3, y4, y5)) => {
            x1.eq2(y1) && *x2 == *y2 && *x3 == *y3 && *x4 == *y4 && *x5 == *y5
        }
        (CKindF::Recur(x1, x2, x3, x4, x5, x6, x7, x8), CKindF::Recur(y1, y2, y3, y4, y5, y6, y7, y8)) => {
            nidx_list_eq(x1, y1) && *x2 == *y2 && *x3 == *y3 && *x4 == *y4 && *x5 == *y5 && rules_eq(x6, y6) && *x7 == *y7 && *x8 == *y8
        }
        _ => false,
    }
}

/// con-leche: ConLeche/Frontend/Olean/Module.lean:51-67 entrySame
/// Structural equality of two stored constants.
pub fn entry_same(a: &CEntryF<NIdx, EIdx>, b: &CEntryF<NIdx, EIdx>) -> bool {
    a.name.eq2(&b.name) && nidx_list_eq(&a.level_params, &b.level_params) && a.ty.eq2(&b.ty) && kinds_same(&a.kind, &b.kind)
}

/// con-leche: ConLeche/Frontend/Olean/Module.lean:69-78 kindWord
/// A stored constant's kind, for messages.
pub fn kind_word(k: &CKindF<NIdx, EIdx>) -> Vec<u32> {
    match k {
        CKindF::Ax(u) => {
            if *u {
                { const M: [u32; 14] = [97, 120, 105, 111, 109, 32, 40, 117, 110, 115, 97, 102, 101, 41]; crate::kernel::core_types::code_points(&M) }
            } else {
                { const M: [u32; 5] = [97, 120, 105, 111, 109]; crate::kernel::core_types::code_points(&M) }
            }
        }
        CKindF::Defn(_, _, s) => text::cat(text::cat({ const M: [u32; 12] = [100, 101, 102, 105, 110, 105, 116, 105, 111, 110, 32, 40]; crate::kernel::core_types::code_points(&M) }, s), &{ const M: [u32; 1] = [41]; crate::kernel::core_types::code_points(&M) }),
        CKindF::Thm(_, _) => { const M: [u32; 7] = [116, 104, 101, 111, 114, 101, 109]; crate::kernel::core_types::code_points(&M) },
        CKindF::Opaq(_, u) => {
            if *u {
                { const M: [u32; 15] = [111, 112, 97, 113, 117, 101, 32, 40, 117, 110, 115, 97, 102, 101, 41]; crate::kernel::core_types::code_points(&M) }
            } else {
                { const M: [u32; 6] = [111, 112, 97, 113, 117, 101]; crate::kernel::core_types::code_points(&M) }
            }
        }
        CKindF::Quot(_) => { const M: [u32; 8] = [113, 117, 111, 116, 105, 101, 110, 116]; crate::kernel::core_types::code_points(&M) },
        CKindF::Induct(_, _, _, _, _, _, _, _) => { const M: [u32; 9] = [105, 110, 100, 117, 99, 116, 105, 118, 101]; crate::kernel::core_types::code_points(&M) },
        CKindF::Ctor(_, _, _, _, _) => { const M: [u32; 11] = [99, 111, 110, 115, 116, 114, 117, 99, 116, 111, 114]; crate::kernel::core_types::code_points(&M) },
        CKindF::Recur(_, _, _, _, _, _, _, _) => { const M: [u32; 8] = [114, 101, 99, 117, 114, 115, 111, 114]; crate::kernel::core_types::code_points(&M) },
    }
}

/// con-leche: ConLeche/Frontend/Olean/Module.lean:80-94 expoOf
/// The axiom Lean exports in place of a constant: unsafe exactly when the
/// definition is not safe or the opaque constant is unsafe.
pub fn hidden_kind<N, E, N2, E2>(ex: &CKindF<N, E>, priv_k: &CKindF<N2, E2>) -> bool {
    const S_SAFE: [u32; 4] = [115, 97, 102, 101];
    match (ex, priv_k) {
        (CKindF::Ax(u), CKindF::Defn(_, _, s)) => *u == !text::cps_beq(s, &S_SAFE),
        (CKindF::Ax(u), CKindF::Thm(_, _)) => !*u,
        (CKindF::Ax(u), CKindF::Opaq(_, u2)) => *u == *u2,
        _ => false,
    }
}

/// con-leche: ConLeche/Frontend/Olean/Module.lean:80-94 expoOf
/// **The exported level of one private constant**, given the exported part's
/// constant of that name; `None` is a constant the exported part does not refine.
pub fn expo_of(priv_c: &CEntryF<NIdx, EIdx>, ex: &CEntryF<NIdx, EIdx>) -> Option<Expo> {
    if entry_same(priv_c, ex) {
        Some(Expo::Same)
    } else if priv_c.name.eq2(&ex.name) && nidx_list_eq(&priv_c.level_params, &ex.level_params) && priv_c.ty.eq2(&ex.ty) && hidden_kind(&ex.kind, &priv_c.kind) {
        Some(Expo::Hidden)
    } else {
        None
    }
}

/// con-leche: ConLeche/Frontend/Olean/Module.lean:96-136 expoOfParts
/// The two failures of `expoOfParts`: its message, and the store's capacity.
pub enum ExpoErr {
    Msg(Vec<u32>),
    Err(CheckError),
}

/// con-leche: ConLeche/Frontend/Olean/Module.lean:96-136 expoOfParts
/// `skP.consts.foldl …`: a private constant's location to its position, and the
/// array of locations.
pub fn priv_loc_of(consts: &Vec<u64>) -> HashMap2<u64, u64> {
    let mut m: HashMap2<u64, u64> = HashMap2::with_capacity(consts.len());
    let mut i = 0usize;
    while i < consts.len() {
        m.insert(consts[i], i as u64);
        i += 1;
    }
    m
}

/// con-leche: ConLeche/Frontend/Olean/Module.lean:96-136 expoOfParts
/// `cs.size.fold …`: a private constant's name to its position.
pub fn priv_idx_of(cs: &Vec<CEntryF<NIdx, EIdx>>) -> HashMap2<NIdx, u64> {
    let mut m: HashMap2<NIdx, u64> = HashMap2::with_capacity(cs.len());
    let mut i = 0usize;
    while i < cs.len() {
        m.insert(cs[i].name.dup2(), i as u64);
        i += 1;
    }
    m
}

/// con-leche: ConLeche/Frontend/Olean/Module.lean:96-136 expoOfParts
/// `cs.map fun _ => .absent`, or another constant value.
pub fn expo_fill(n: usize, e: &Expo) -> Vec<Expo> {
    let mut out: Vec<Expo> = Vec::with_capacity(n);
    let mut i = 0usize;
    while i < n {
        out.push(expo_dup(e));
        i += 1;
    }
    out
}

/// con-leche: ConLeche/Frontend/Olean/Module.lean:96-136 expoOfParts
/// A `malformed …` message.
pub fn msg_err<T>(m: Vec<u32>) -> Result<T, ExpoErr> {
    Err(ExpoErr::Msg(m))
}

/// con-leche: ConLeche/Frontend/Olean/Module.lean:96-136 expoOfParts
/// One exported constant `c` against the private ones, not the same object as any.
pub fn expo_step(pk: &OleanPins, pers: &PersTier, ar: &mut EStore, bs: &[u8], r: &Region, c: u64, priv_idx: &HashMap2<NIdx, u64>, priv_locs: &Vec<u64>, cs: &Vec<CEntryF<NIdx, EIdx>>, expo: &mut Vec<Expo>) -> Result<(), ExpoErr> {
    let se = match spec::const_skel(bs, r, c) {
        None => return msg_err({ const M: [u32; 27] = [109, 97, 108, 102, 111, 114, 109, 101, 100, 32, 101, 120, 112, 111, 114, 116, 101, 100, 32, 99, 111, 110, 115, 116, 97, 110, 116]; crate::kernel::core_types::code_points(&M) }),
        Some(s) => s,
    };
    let en = match spec::name_p(pk, pers, ar, bs, r, se.name) {
        Err(RdErr::Bad) => return msg_err({ const M: [u32; 27] = [109, 97, 108, 102, 111, 114, 109, 101, 100, 32, 101, 120, 112, 111, 114, 116, 101, 100, 32, 99, 111, 110, 115, 116, 97, 110, 116]; crate::kernel::core_types::code_points(&M) }),
        Err(RdErr::Err(e)) => return Err(ExpoErr::Err(e)),
        Ok(n) => n,
    };
    let en_text = match env::read_name(pers, ar, &en) {
        Err(e) => return Err(ExpoErr::Err(e)),
        Ok(n) => name::render(&n),
    };
    let i: u64 = match priv_idx.get(&en) {
        None => {
            let t = text::cat({ const M: [u32; 22] = [116, 104, 101, 32, 101, 120, 112, 111, 114, 116, 101, 100, 32, 99, 111, 110, 115, 116, 97, 110, 116, 32]; crate::kernel::core_types::code_points(&M) }, &en_text);
            return msg_err(text::cat(t, &{ const M: [u32; 35] = [32, 105, 115, 32, 110, 111, 116, 32, 115, 116, 111, 114, 101, 100, 32, 97, 116, 32, 116, 104, 101, 32, 112, 114, 105, 118, 97, 116, 101, 32, 108, 101, 118, 101, 108]; crate::kernel::core_types::code_points(&M) }));
        }
        Some(i) => *i,
    };
    let iu = i as usize;
    let sp = if iu < priv_locs.len() {
        match spec::const_skel(bs, r, priv_locs[iu]) {
            None => return msg_err({ const M: [u32; 26] = [109, 97, 108, 102, 111, 114, 109, 101, 100, 32, 112, 114, 105, 118, 97, 116, 101, 32, 99, 111, 110, 115, 116, 97, 110, 116]; crate::kernel::core_types::code_points(&M) }),
            Some(s) => s,
        }
    } else {
        return msg_err({ const M: [u32; 26] = [109, 97, 108, 102, 111, 114, 109, 101, 100, 32, 112, 114, 105, 118, 97, 116, 101, 32, 99, 111, 110, 115, 116, 97, 110, 116]; crate::kernel::core_types::code_points(&M) });
    };
    let same_ptrs = se.ty == sp.ty && u64_list_eq(&se.level_params, &sp.level_params);
    if hidden_kind(&se.kind, &sp.kind) && same_ptrs {
        expo[iu] = Expo::Hidden;
        return Ok(());
    }
    let e = match reads::entry_at(pk, pers, ar, bs, r, c) {
        Err(RdErr::Bad) => return msg_err({ const M: [u32; 27] = [109, 97, 108, 102, 111, 114, 109, 101, 100, 32, 101, 120, 112, 111, 114, 116, 101, 100, 32, 99, 111, 110, 115, 116, 97, 110, 116]; crate::kernel::core_types::code_points(&M) }),
        Err(RdErr::Err(e)) => return Err(ExpoErr::Err(e)),
        Ok(e) => e,
    };
    if iu >= cs.len() {
        return msg_err({ const M: [u32; 26] = [109, 97, 108, 102, 111, 114, 109, 101, 100, 32, 112, 114, 105, 118, 97, 116, 101, 32, 99, 111, 110, 115, 116, 97, 110, 116]; crate::kernel::core_types::code_points(&M) });
    }
    match expo_of(&cs[iu], &e) {
        Some(x) => {
            expo[iu] = x;
            Ok(())
        }
        None => {
            let t = text::cat({ const M: [u32; 21] = [116, 104, 101, 32, 101, 120, 112, 111, 114, 116, 101, 100, 32, 118, 105, 101, 119, 32, 111, 102, 32]; crate::kernel::core_types::code_points(&M) }, &en_text);
            let t = text::cat(t, &{ const M: [u32; 46] = [32, 105, 115, 32, 110, 111, 116, 32, 97, 32, 114, 101, 102, 105, 110, 101, 109, 101, 110, 116, 32, 111, 102, 32, 105, 116, 115, 32, 112, 114, 105, 118, 97, 116, 101, 32, 99, 111, 110, 115, 116, 97, 110, 116, 32, 40]; crate::kernel::core_types::code_points(&M) });
            let t = text::cat(t, &kind_word(&cs[iu].kind));
            let t = text::cat(t, &{ const M: [u32; 3] = [32, 47, 32]; crate::kernel::core_types::code_points(&M) });
            let t = text::cat(t, &kind_word(&e.kind));
            msg_err(text::cat(t, &{ const M: [u32; 1] = [41]; crate::kernel::core_types::code_points(&M) }))
        }
    }
}

/// con-leche: ConLeche/Frontend/Olean/Module.lean:96-136 expoOfParts
/// The `for c in skE.consts` of `expoOfParts`.
pub fn expo_loop(pk: &OleanPins, pers: &PersTier, ar: &mut EStore, bs: &[u8], r: &Region, e_consts: &Vec<u64>, priv_loc: &HashMap2<u64, u64>, priv_idx: &HashMap2<NIdx, u64>, priv_locs: &Vec<u64>, cs: &Vec<CEntryF<NIdx, EIdx>>, expo: &mut Vec<Expo>) -> Result<(), ExpoErr> {
    let mut k = 0usize;
    while k < e_consts.len() {
        let c = e_consts[k];
        match priv_loc.get(&c) {
            Some(i) => {
                expo[*i as usize] = Expo::Same;
            }
            None => match expo_step(pk, pers, ar, bs, r, c, priv_idx, priv_locs, cs, expo) {
                Err(e) => return Err(e),
                Ok(()) => {}
            },
        }
        k += 1;
    }
    Ok(())
}

/// con-leche: ConLeche/Frontend/Olean/Module.lean:96-136 expoOfParts
/// **The exported level of a module's private constants**: for each exported
/// constant, the private constant it stands for.
pub fn expo_of_parts(pk: &OleanPins, pers: &PersTier, ar: &mut EStore, bs: &[u8], r: &Region, priv_addr: u64, exp_addr: u64, cs: &Vec<CEntryF<NIdx, EIdx>>) -> Result<Vec<Expo>, ExpoErr> {
    let sk_p = match spec::module_skel(bs, r, priv_addr) {
        None => return msg_err({ const M: [u32; 22] = [109, 97, 108, 102, 111, 114, 109, 101, 100, 32, 112, 114, 105, 118, 97, 116, 101, 32, 112, 97, 114, 116]; crate::kernel::core_types::code_points(&M) }),
        Some(s) => s,
    };
    let sk_e = match spec::module_skel(bs, r, exp_addr) {
        None => return msg_err({ const M: [u32; 23] = [109, 97, 108, 102, 111, 114, 109, 101, 100, 32, 101, 120, 112, 111, 114, 116, 101, 100, 32, 112, 97, 114, 116]; crate::kernel::core_types::code_points(&M) }),
        Some(s) => s,
    };
    let priv_loc = priv_loc_of(&sk_p.consts);
    let priv_idx = priv_idx_of(cs);
    let mut expo: Vec<Expo> = expo_fill(cs.len(), &Expo::Absent);
    match expo_loop(pk, pers, ar, bs, r, &sk_e.consts, &priv_loc, &priv_idx, &sk_p.consts, cs, &mut expo) {
        Err(e) => Err(e),
        Ok(()) => Ok(expo),
    }
}

/// con-leche: ConLeche/Frontend/Olean/Module.lean:140-159 checkViews
/// `module {m}: {what}`.
pub fn bad_module(pers: &PersTier, ar: &EStore, m: &NIdx, what: Vec<u32>) -> CheckError {
    let t = text::cat({ const M: [u32; 7] = [109, 111, 100, 117, 108, 101, 32]; crate::kernel::core_types::code_points(&M) }, &view::name_text(pers, ar, m));
    let t = text::cat(t, &{ const M: [u32; 2] = [58, 32]; crate::kernel::core_types::code_points(&M) });
    core_types::internal(text::cat(t, &what))
}

/// con-leche: ConLeche/Frontend/Olean/Module.lean:140-159 checkViews
/// The module-system arm of `checkViews`.
pub fn check_views_module(pk: &OleanPins, pers: &PersTier, ar: &mut EStore, m: &NIdx, f: &ModFiles, v: &AllViews, s: &Part, p: &Part) -> Result<Vec<Expo>, CheckError> {
    let b: RegionBuf = match region::region_of_parts3(&f.exported, s, p) {
        Err(e) => return Err(e),
        Ok(b) => b,
    };
    if !v.server.is_module {
        return Err(bad_module(pers, ar, m, { const M: [u32; 77] = [116, 104, 101, 32, 115, 101, 114, 118, 101, 114, 32, 112, 97, 114, 116, 32, 105, 115, 32, 110, 111, 116, 32, 111, 102, 32, 97, 32, 109, 111, 100, 117, 108, 101, 32, 111, 102, 32, 116, 104, 101, 32, 109, 111, 100, 117, 108, 101, 32, 115, 121, 115, 116, 101, 109, 44, 32, 116, 104, 101, 32, 101, 120, 112, 111, 114, 116, 101, 100, 32, 112, 97, 114, 116, 32, 105, 115]; crate::kernel::core_types::code_points(&M) }));
    }
    if !v.private_part.is_module {
        return Err(bad_module(pers, ar, m, { const M: [u32; 78] = [116, 104, 101, 32, 112, 114, 105, 118, 97, 116, 101, 32, 112, 97, 114, 116, 32, 105, 115, 32, 110, 111, 116, 32, 111, 102, 32, 97, 32, 109, 111, 100, 117, 108, 101, 32, 111, 102, 32, 116, 104, 101, 32, 109, 111, 100, 117, 108, 101, 32, 115, 121, 115, 116, 101, 109, 44, 32, 116, 104, 101, 32, 101, 120, 112, 111, 114, 116, 101, 100, 32, 112, 97, 114, 116, 32, 105, 115]; crate::kernel::core_types::code_points(&M) }));
    }
    let ap = region::part_module_data_addr(p);
    let expo = match expo_of_parts(pk, pers, ar, &b.bytes, &b.region, ap, region::part_module_data_addr(&f.exported), &v.private_part.constants) {
        Err(ExpoErr::Err(e)) => return Err(e),
        Err(ExpoErr::Msg(msg)) => Err(msg),
        Ok(x) => Ok(x),
    };
    match expo_of_parts(pk, pers, ar, &b.bytes, &b.region, ap, region::part_module_data_addr(s), &v.private_part.constants) {
        Err(ExpoErr::Err(e)) => Err(e),
        Err(ExpoErr::Msg(msg2)) => match expo {
            Err(msg) => Err(bad_module(pers, ar, m, text::cat({ const M: [u32; 19] = [116, 104, 101, 32, 101, 120, 112, 111, 114, 116, 101, 100, 32, 112, 97, 114, 116, 58, 32]; crate::kernel::core_types::code_points(&M) }, &msg))),
            Ok(_) => { let msg = msg2; Err(bad_module(pers, ar, m, text::cat({ const M: [u32; 17] = [116, 104, 101, 32, 115, 101, 114, 118, 101, 114, 32, 112, 97, 114, 116, 58, 32]; crate::kernel::core_types::code_points(&M) }, &msg))) }
        },
        Ok(_) => match expo {
            Err(msg) => Err(bad_module(pers, ar, m, text::cat({ const M: [u32; 19] = [116, 104, 101, 32, 101, 120, 112, 111, 114, 116, 101, 100, 32, 112, 97, 114, 116, 58, 32]; crate::kernel::core_types::code_points(&M) }, &msg))),
            Ok(x) => Ok(x),
        },
    }
}

/// con-leche: ConLeche/Frontend/Olean/Module.lean:140-159 checkViews
/// **The views of a module against each other**: for each private constant, its
/// exported level.  Every constant is `.same` in a classic module.
pub fn check_views(pk: &OleanPins, pers: &PersTier, ar: &mut EStore, m: &NIdx, f: &ModFiles, v: &AllViews) -> Result<Vec<Expo>, CheckError> {
    match (&f.server, &f.private_part) {
        (Some(s), Some(p)) => {
            if !view::mod_files_is_module(f) {
                return Ok(expo_fill(v.private_part.constants.len(), &Expo::Same));
            }
            check_views_module(pk, pers, ar, m, f, v, s, p)
        }
        _ => Ok(expo_fill(v.private_part.constants.len(), &Expo::Same)),
    }
}
