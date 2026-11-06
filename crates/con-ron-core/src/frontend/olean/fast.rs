//! `ConLeche/Frontend/Olean/Fast.lean` — the fast decoder (task #142).
//!
//! Each object once, in two passes over the module's region, by the node
//! functions of `spec`.  **Mark, downwards**: the objects the module's constants
//! need are marked with the kind they are read as, the roots first, and the
//! region is swept from its last word to its first, a marked object's fields
//! marking in turn.  **Build, upwards**: every marked object is read by its node
//! function, the values of the objects it points to taken from the memo.  There
//! is no recursion, so nothing depends on how deep the values nest.
//!
//! ## Deviations
//!
//! * **The memo holds handles**, as words: `Vec::resize` is the bulk fill the
//!   extraction models and `u32` is the `Clone` it asks for, and the word `0` is
//!   a handle that decodes (`handle.rs`).  It is never read before the object
//!   below it was built.
//! * **Across modules things ARE shared, in the store**: a node of an earlier
//!   module is found by `intern`.  Upstream's values are per module.
//! * `DS.setName` and friends are field writes, and the `ByteArray.set!` of
//!   `mark` a guarded index; a location below the highest root is always in range.
//! * `buildKind`'s `(st, ok)` pair is `Result`; a failed read stops the sweep at
//!   once, where upstream's finishes the slot's other kinds and gives `none`.

use crate::arena::handle::{EIdx, LIdx, LsIdx, NIdx};
use crate::arena::store::{EStore, PersTier};
use crate::frontend::olean::region;
use crate::frontend::olean::region::Region;
use crate::frontend::olean::spec;
use crate::frontend::olean::spec::{CEntryF, CKindF, ModDecoded, ModSkel, OleanPins, PtrRead, RdErr, StmtRec, Sub};
use crate::kernel::core_types::CheckError;
use crate::ron::hashmap::Dup;

/// con-leche: ConLeche/Frontend/Olean/Fast.lean:56-64 zeros
/// `n` zero bytes.  Deviation: `Vec::resize`, not by doubling.
pub fn zeros(n: usize) -> Vec<u8> {
    let mut m: Vec<u8> = Vec::new();
    m.resize(n, 0u8);
    m
}

/// con-leche: ConLeche/Frontend/Olean/Fast.lean:66-67 kName
pub const K_NAME: u8 = 1;
/// con-leche: ConLeche/Frontend/Olean/Fast.lean:68-68 kLevel
pub const K_LEVEL: u8 = 2;
/// con-leche: ConLeche/Frontend/Olean/Fast.lean:69-69 kExpr
pub const K_EXPR: u8 = 4;
/// con-leche: ConLeche/Frontend/Olean/Fast.lean:70-70 kLevels
pub const K_LEVELS: u8 = 8;

/// con-leche: ConLeche/Frontend/Olean/Fast.lean:76-79 marksAt
/// The mark byte of slot `s`.
#[inline(always)]
pub fn marks_at(m: &Vec<u8>, s: u64) -> u8 {
    region::rd_u8(m, s)
}

/// con-leche: ConLeche/Frontend/Olean/Fast.lean:81-82 marked
/// Is the object at slot `s` read as kind `k`?
#[inline(always)]
pub fn marked(m: &Vec<u8>, k: u8, s: u64) -> bool {
    marks_at(m, s) & k != 0
}

/// con-leche: ConLeche/Frontend/Olean/Fast.lean:84-87 mark
/// Mark the object at slot `s` as kind `k`.
#[inline(always)]
pub fn mark(m: &mut Vec<u8>, k: u8, s: u64) {
    let i = s as usize;
    if i < m.len() {
        m[i] = m[i] | k;
    }
}

/// con-leche: ConLeche/Frontend/Olean/Fast.lean:89-94 DS
/// The decoder's values, per slot, one array per kind (module note).
pub struct DS {
    pub names: Vec<u32>,
    pub levels: Vec<u32>,
    pub exprs: Vec<u32>,
    pub lists: Vec<u32>,
}

/// con-leche: ConLeche/Frontend/Olean/Fast.lean:96-102 DS.fresh
/// Fresh values for `n` slots.
pub fn ds_fresh(n: usize) -> DS {
    let mut names: Vec<u32> = Vec::new();
    names.resize(n, 0u32);
    let mut levels: Vec<u32> = Vec::new();
    levels.resize(n, 0u32);
    let mut exprs: Vec<u32> = Vec::new();
    exprs.resize(n, 0u32);
    let mut lists: Vec<u32> = Vec::new();
    lists.resize(n, 0u32);
    DS { names, levels, exprs, lists }
}

/// con-leche: ConLeche/Frontend/Olean/Fast.lean:120-121 DS.nameV
/// The memoized values of the object at location `c`.
impl Sub for DS {
    /// con-leche: ConLeche/Frontend/Olean/Fast.lean:120-121 DS.nameV
    #[inline(always)]
    fn sub_name(&self, c: u64) -> Option<NIdx> {
        Some(NIdx::of_word(self.names[(c / 8) as usize]))
    }

    /// con-leche: ConLeche/Frontend/Olean/Fast.lean:122 DS.levelV
    #[inline(always)]
    fn sub_level(&self, c: u64) -> Option<LIdx> {
        Some(LIdx::of_word(self.levels[(c / 8) as usize]))
    }

    /// con-leche: ConLeche/Frontend/Olean/Fast.lean:124 DS.levelsV
    #[inline(always)]
    fn sub_levels(&self, c: u64) -> Option<LsIdx> {
        Some(LsIdx::of_word(self.lists[(c / 8) as usize]))
    }

    /// con-leche: ConLeche/Frontend/Olean/Fast.lean:123 DS.exprV
    #[inline(always)]
    fn sub_expr(&self, c: u64) -> Option<EIdx> {
        Some(EIdx::of_word(self.exprs[(c / 8) as usize]))
    }
}

/// con-leche: ConLeche/Frontend/Olean/Fast.lean:133-134 failM
/// Record a failure: bit 7 of slot 0's byte.
#[inline(always)]
pub fn fail_m(m: &mut Vec<u8>) {
    m[0] = 0x80;
}

/// con-leche: ConLeche/Frontend/Olean/Fast.lean:136-137 failedM
/// Has the marking failed?
#[inline(always)]
pub fn failed_m(m: &Vec<u8>) -> bool {
    marks_at(m, 0) & 0x80 != 0
}

/// con-leche: ConLeche/Frontend/Olean/Fast.lean:139-147 markPtr
/// Mark the object a pointer field of the object at `g` leads to, as kind `k`;
/// `nil` says the kind's nullary constructor is the scalar `0`.
#[inline(always)]
pub fn mark_ptr(r: &Region, m: &mut Vec<u8>, g: u64, k: u8, nil: bool, v: u64) {
    if !(nil && v == 1) {
        match region::region_down(r, g, v) {
            Some(c) => mark(m, k, c / 8),
            None => fail_m(m),
        }
    }
}

/// con-leche: ConLeche/Frontend/Olean/Fast.lean:178-195 markExpr
/// The arms of two followed fields: the shape's field count `want`, and the field,
/// kind and `nil` of each.
#[inline(always)]
pub fn mark_two(bs: &[u8], r: &Region, g: u64, m: &mut Vec<u8>, n: u64, want: u64, k1: u8, nil1: bool, f1: u64, k2: u8, nil2: bool, f2: u64) {
    if n == want {
        mark_ptr(r, m, g, k1, nil1, region::region_fld(bs, g, f1));
        mark_ptr(r, m, g, k2, nil2, region::region_fld(bs, g, f2));
    } else {
        fail_m(m);
    }
}

/// con-leche: ConLeche/Frontend/Olean/Fast.lean:149-156 markName
/// The fields of a `Name` object.
pub fn mark_name(bs: &[u8], r: &Region, g: u64, m: &mut Vec<u8>) {
    if region::region_fits(bs, r, g) && spec::name_shape(region::region_tag(bs, g), region::region_nobjs(bs, g)) {
        mark_ptr(r, m, g, K_NAME, true, region::region_fld(bs, g, 0));
    } else {
        fail_m(m);
    }
}

/// con-leche: ConLeche/Frontend/Olean/Fast.lean:158-168 markLevel
/// The fields of a `Level` object.
pub fn mark_level(bs: &[u8], r: &Region, g: u64, m: &mut Vec<u8>) {
    if !region::region_fits(bs, r, g) {
        fail_m(m);
        return;
    }
    let n = region::region_nobjs(bs, g);
    match region::region_tag(bs, g) {
        0 => {
            if n != 0 {
                fail_m(m);
            }
        }
        1 => {
            if n == 1 {
                mark_ptr(r, m, g, K_LEVEL, true, region::region_fld(bs, g, 0));
            } else {
                fail_m(m);
            }
        }
        2 => mark_two(bs, r, g, m, n, 2, K_LEVEL, true, 0, K_LEVEL, true, 1),
        3 => mark_two(bs, r, g, m, n, 2, K_LEVEL, true, 0, K_LEVEL, true, 1),
        4 => {
            if n == 1 {
                mark_ptr(r, m, g, K_NAME, true, region::region_fld(bs, g, 0));
            } else {
                fail_m(m);
            }
        }
        _ => fail_m(m),
    }
}

/// con-leche: ConLeche/Frontend/Olean/Fast.lean:170-176 markLevels
/// The fields of a `List Level` cell.
pub fn mark_levels(bs: &[u8], r: &Region, g: u64, m: &mut Vec<u8>) {
    if region::region_fits(bs, r, g) && region::region_tag(bs, g) == 1 {
        mark_two(bs, r, g, m, region::region_nobjs(bs, g), 2, K_LEVEL, true, 0, K_LEVELS, true, 1);
    } else {
        fail_m(m);
    }
}

/// con-leche: ConLeche/Frontend/Olean/Fast.lean:178-195 markExpr
/// The fields of an `Expr` object; the fields holding a `Nat` or a `Literal` are
/// read by the build alone.
pub fn mark_expr(bs: &[u8], r: &Region, g: u64, m: &mut Vec<u8>) {
    if !region::region_fits(bs, r, g) {
        fail_m(m);
        return;
    }
    let n = region::region_nobjs(bs, g);
    match region::region_tag(bs, g) {
        5 => mark_two(bs, r, g, m, n, 2, K_EXPR, false, 0, K_EXPR, false, 1),
        0 => {
            if n != 1 {
                fail_m(m);
            }
        }
        3 => {
            if n == 1 {
                mark_ptr(r, m, g, K_LEVEL, true, region::region_fld(bs, g, 0));
            } else {
                fail_m(m);
            }
        }
        4 => mark_two(bs, r, g, m, n, 2, K_NAME, true, 0, K_LEVELS, true, 1),
        6 => mark_two(bs, r, g, m, n, 3, K_EXPR, false, 1, K_EXPR, false, 2),
        7 => mark_two(bs, r, g, m, n, 3, K_EXPR, false, 1, K_EXPR, false, 2),
        8 => {
            if n == 4 {
                mark_ptr(r, m, g, K_EXPR, false, region::region_fld(bs, g, 1));
                mark_ptr(r, m, g, K_EXPR, false, region::region_fld(bs, g, 2));
                mark_ptr(r, m, g, K_EXPR, false, region::region_fld(bs, g, 3));
            } else {
                fail_m(m);
            }
        }
        9 => {
            if n != 1 {
                fail_m(m);
            }
        }
        10 => {
            if n == 2 {
                mark_ptr(r, m, g, K_EXPR, false, region::region_fld(bs, g, 1));
            } else {
                fail_m(m);
            }
        }
        11 => mark_two(bs, r, g, m, n, 3, K_NAME, true, 0, K_EXPR, false, 2),
        _ => fail_m(m),
    }
}

/// con-leche: ConLeche/Frontend/Olean/Fast.lean:197-200 markKind
/// con-leche: ConLeche/Frontend/Olean/Fast.lean:202-205 markSlot
/// One slot of the downward sweep: its marked kinds' fields.  `markKind`'s
/// `markK` argument is written out, kind by kind, in `markSlot`'s order
/// (name, level, levels, expression, the innermost first).
#[inline(always)]
pub fn mark_slot(bs: &[u8], r: &Region, p: u64, m: &mut Vec<u8>) {
    if marked(m, K_NAME, p) {
        mark_name(bs, r, 8 * p, m);
    }
    if marked(m, K_LEVEL, p) {
        mark_level(bs, r, 8 * p, m);
    }
    if marked(m, K_LEVELS, p) {
        mark_levels(bs, r, 8 * p, m);
    }
    if marked(m, K_EXPR, p) {
        mark_expr(bs, r, 8 * p, m);
    }
}

/// con-leche: ConLeche/Frontend/Olean/Fast.lean:207-215 markPass
/// **The downward sweep** over the slots below `p`; it stops at the first failure.
pub fn mark_pass(bs: &[u8], r: &Region, m: &mut Vec<u8>, p: u64) {
    let mut p = p;
    while p > 0 {
        p -= 1;
        if marks_at(m, p) != 0 {
            mark_slot(bs, r, p, m);
            if failed_m(m) {
                return;
            }
        }
    }
}

/// con-leche: ConLeche/Frontend/Olean/Fast.lean:219-220 buildName
/// con-leche: ConLeche/Frontend/Olean/Fast.lean:104-106 DS.setName
/// con-leche: ConLeche/Frontend/Olean/Fast.lean:232-241 buildKind
/// Slot `p`'s value as a name, if it is marked so.
pub fn build_kind_name(pk: &OleanPins, pers: &PersTier, ar: &mut EStore, bs: &[u8], r: &Region, m: &Vec<u8>, st: &mut DS, p: u64) -> Result<(), RdErr> {
    if marked(m, K_NAME, p) {
        match spec::name_node(pk, pers, ar, bs, r, 8 * p, &*st) {
            Err(e) => Err(e),
            Ok(h) => {
                st.names[p as usize] = h.word;
                Ok(())
            }
        }
    } else {
        Ok(())
    }
}

/// con-leche: ConLeche/Frontend/Olean/Fast.lean:222-223 buildLevel
/// con-leche: ConLeche/Frontend/Olean/Fast.lean:108-110 DS.setLevel
/// con-leche: ConLeche/Frontend/Olean/Fast.lean:232-241 buildKind
/// Slot `p`'s value as a level, if it is marked so.
pub fn build_kind_level(pk: &OleanPins, pers: &PersTier, ar: &mut EStore, bs: &[u8], r: &Region, m: &Vec<u8>, st: &mut DS, p: u64) -> Result<(), RdErr> {
    if marked(m, K_LEVEL, p) {
        match spec::level_node(pk, pers, ar, bs, r, 8 * p, &*st) {
            Err(e) => Err(e),
            Ok(h) => {
                st.levels[p as usize] = h.word;
                Ok(())
            }
        }
    } else {
        Ok(())
    }
}

/// con-leche: ConLeche/Frontend/Olean/Fast.lean:225-226 buildLevels
/// con-leche: ConLeche/Frontend/Olean/Fast.lean:116-118 DS.setLevels
/// con-leche: ConLeche/Frontend/Olean/Fast.lean:232-241 buildKind
/// Slot `p`'s value as a list of levels, if it is marked so.
pub fn build_kind_levels(pk: &OleanPins, pers: &PersTier, ar: &mut EStore, bs: &[u8], r: &Region, m: &Vec<u8>, st: &mut DS, p: u64) -> Result<(), RdErr> {
    if marked(m, K_LEVELS, p) {
        match spec::levels_node(pk, pers, ar, bs, r, 8 * p, &*st) {
            Err(e) => Err(e),
            Ok(h) => {
                st.lists[p as usize] = h.word;
                Ok(())
            }
        }
    } else {
        Ok(())
    }
}

/// con-leche: ConLeche/Frontend/Olean/Fast.lean:228-230 buildExpr
/// con-leche: ConLeche/Frontend/Olean/Fast.lean:112-114 DS.setExpr
/// con-leche: ConLeche/Frontend/Olean/Fast.lean:232-241 buildKind
/// Slot `p`'s value as an expression, if it is marked so.
pub fn build_kind_expr(pk: &OleanPins, pers: &PersTier, ar: &mut EStore, bs: &[u8], r: &Region, m: &Vec<u8>, st: &mut DS, p: u64) -> Result<(), RdErr> {
    if marked(m, K_EXPR, p) {
        match spec::expr_node(pk, pers, ar, bs, r, 8 * p, &*st) {
            Err(e) => Err(e),
            Ok(h) => {
                st.exprs[p as usize] = h.word;
                Ok(())
            }
        }
    } else {
        Ok(())
    }
}

/// con-leche: ConLeche/Frontend/Olean/Fast.lean:243-255 buildPass
/// One marked slot: each marked kind's value into the memo, in `buildPass`'s order.
pub fn build_slot(pk: &OleanPins, pers: &PersTier, ar: &mut EStore, bs: &[u8], r: &Region, m: &Vec<u8>, st: &mut DS, p: u64) -> Result<(), RdErr> {
    match build_kind_name(pk, pers, ar, bs, r, m, st, p) {
        Err(e) => Err(e),
        Ok(()) => match build_kind_level(pk, pers, ar, bs, r, m, st, p) {
            Err(e) => Err(e),
            Ok(()) => match build_kind_levels(pk, pers, ar, bs, r, m, st, p) {
                Err(e) => Err(e),
                Ok(()) => build_kind_expr(pk, pers, ar, bs, r, m, st, p),
            },
        },
    }
}

/// con-leche: ConLeche/Frontend/Olean/Fast.lean:243-255 buildPass
/// A slot, if anything marks it.
pub fn build_marked(pk: &OleanPins, pers: &PersTier, ar: &mut EStore, bs: &[u8], r: &Region, m: &Vec<u8>, st: &mut DS, p: u64) -> Result<(), RdErr> {
    if marks_at(m, p) != 0 {
        build_slot(pk, pers, ar, bs, r, m, st, p)
    } else {
        Ok(())
    }
}

/// con-leche: ConLeche/Frontend/Olean/Fast.lean:243-255 buildPass
/// **The upward sweep** over the slots from `p` to `n`: each slot's marked kinds'
/// values.
pub fn build_pass(pk: &OleanPins, pers: &PersTier, ar: &mut EStore, bs: &[u8], r: &Region, m: &Vec<u8>, n: u64, st: &mut DS, p: u64) -> Result<(), RdErr> {
    let mut p = p;
    while p < n {
        match build_marked(pk, pers, ar, bs, r, m, st, p) {
            Err(e) => return Err(e),
            Ok(()) => {}
        }
        p += 1;
    }
    Ok(())
}

/// con-leche: ConLeche/Frontend/Olean/Fast.lean:259-265 markRoot
/// Mark a root: a name (`nil`) or an expression the skeletons hold.  Whether it
/// is one.
#[inline(always)]
pub fn mark_root(r: &Region, k: u8, nil: bool, m: &mut Vec<u8>, v: u64) -> bool {
    if nil && v == 1 {
        true
    } else {
        match region::region_loc(r, v) {
            Some(c) => {
                mark(m, k, c / 8);
                true
            }
            None => false,
        }
    }
}

/// con-leche: ConLeche/Frontend/Olean/Fast.lean:259-265 markRoot
/// `foldlM (markRoot r k nil)`.
pub fn mark_roots(r: &Region, k: u8, nil: bool, m: &mut Vec<u8>, vs: &Vec<u64>) -> bool {
    let mut i = 0usize;
    while i < vs.len() {
        if !mark_root(r, k, nil, m, vs[i]) {
            return false;
        }
        i += 1;
    }
    true
}

/// con-leche: ConLeche/Frontend/Olean/Fast.lean:267-269 maxLoc
/// The highest location of a root.
pub fn max_loc(r: &Region, vs: &Vec<u64>, m: u64) -> u64 {
    let mut m = m;
    let mut i = 0usize;
    while i < vs.len() {
        let g = region::region_loc_go(r, vs[i], r.segs.len());
        if g > m {
            m = g;
        }
        i += 1;
    }
    m
}

/// con-leche: ConLeche/Frontend/Olean/Fast.lean:271-279 runPasses
/// **Both passes** from the given name and expression roots.  Every object they
/// reach lies at or below the highest root, so the memo ends there.
pub fn run_passes(pk: &OleanPins, pers: &PersTier, ar: &mut EStore, bs: &[u8], r: &Region, names: &Vec<u64>, exprs: &Vec<u64>) -> Result<DS, RdErr> {
    let n: u64 = max_loc(r, exprs, max_loc(r, names, 0)) / 8 + 1;
    let mut m: Vec<u8> = zeros(n as usize);
    if !mark_roots(r, K_NAME, true, &mut m, names) {
        return Err(RdErr::Bad);
    }
    if !mark_roots(r, K_EXPR, false, &mut m, exprs) {
        return Err(RdErr::Bad);
    }
    mark_pass(bs, r, &mut m, n);
    if failed_m(&m) {
        return Err(RdErr::Bad);
    }
    let mut st: DS = ds_fresh(n as usize);
    match build_pass(pk, pers, ar, bs, r, &m, n, &mut st, 0) {
        Err(e) => Err(e),
        Ok(()) => Ok(st),
    }
}

/// con-leche: ConLeche/Frontend/Olean/Fast.lean:281-286 DS.nameOf
/// con-leche: ConLeche/Frontend/Olean/Fast.lean:288-291 DS.exprOf
/// A root's value, from the memo.
impl PtrRead for DS {
    /// con-leche: ConLeche/Frontend/Olean/Fast.lean:281-286 DS.nameOf
    #[inline(always)]
    fn rd_name(&self, pk: &OleanPins, _pers: &PersTier, _ar: &mut EStore, _bs: &[u8], r: &Region, v: u64) -> Result<NIdx, RdErr> {
        if v == 1 {
            Ok(pk.anon.dup2())
        } else {
            match region::region_loc(r, v) {
                Some(c) => Ok(NIdx::of_word(self.names[(c / 8) as usize])),
                None => Err(RdErr::Bad),
            }
        }
    }

    /// con-leche: ConLeche/Frontend/Olean/Fast.lean:288-291 DS.exprOf
    #[inline(always)]
    fn rd_expr(&self, _pk: &OleanPins, _pers: &PersTier, _ar: &mut EStore, _bs: &[u8], r: &Region, v: u64) -> Result<EIdx, RdErr> {
        match region::region_loc(r, v) {
            Some(c) => Ok(EIdx::of_word(self.exprs[(c / 8) as usize])),
            None => Err(RdErr::Bad),
        }
    }
}

/// con-leche: ConLeche/Frontend/Olean/Fast.lean:293-301 CEntryF.names
/// The names a constant's skeleton holds, onto `out`.
pub fn c_entry_names(c: &CEntryF<u64, u64>, out: &mut Vec<u64>) {
    out.push(c.name);
    push_all(&c.level_params, out);
    match &c.kind {
        CKindF::Thm(_, all) => push_all(all, out),
        CKindF::Induct(_, _, all, cs, _, _, _, _) => {
            push_all(all, out);
            push_all(cs, out);
        }
        CKindF::Ctor(ind, _, _, _, _) => out.push(*ind),
        CKindF::Recur(all, _, _, _, _, rules, _, _) => {
            push_all(all, out);
            let mut i = 0usize;
            while i < rules.len() {
                out.push(rules[i].0);
                i += 1;
            }
        }
        _ => {}
    }
}

/// con-leche: ConLeche/Frontend/Olean/Fast.lean:293-301 CEntryF.names
/// `++`.
pub fn push_all(xs: &Vec<u64>, out: &mut Vec<u64>) {
    let mut i = 0usize;
    while i < xs.len() {
        out.push(xs[i]);
        i += 1;
    }
}

/// con-leche: ConLeche/Frontend/Olean/Fast.lean:303-309 CEntryF.exprs
/// The expressions a constant's skeleton holds, onto `out`.
pub fn c_entry_exprs(c: &CEntryF<u64, u64>, out: &mut Vec<u64>) {
    out.push(c.ty);
    match &c.kind {
        CKindF::Defn(v, _, _) => out.push(*v),
        CKindF::Thm(v, _) => out.push(*v),
        CKindF::Opaq(v, _) => out.push(*v),
        CKindF::Recur(_, _, _, _, _, rules, _, _) => {
            let mut i = 0usize;
            while i < rules.len() {
                out.push(rules[i].2);
                i += 1;
            }
        }
        _ => {}
    }
}

/// con-leche: ConLeche/Frontend/Olean/Fast.lean:311-316 ModSkel.read
/// A module's value from its skeletons, given what its pointers stand for.
pub fn mod_skel_read<R: PtrRead>(rd: &R, pk: &OleanPins, pers: &PersTier, ar: &mut EStore, bs: &[u8], r: &Region, sk: &ModSkel, cs: &Vec<CEntryF<u64, u64>>) -> Result<ModDecoded, RdErr> {
    match mod_skel_imports(rd, pk, pers, ar, bs, r, sk) {
        Err(e) => Err(e),
        Ok(imports) => match mod_skel_constants(rd, pk, pers, ar, bs, r, cs) {
            Err(e) => Err(e),
            Ok(constants) => Ok(ModDecoded { is_module: sk.is_module, imports, constants }),
        },
    }
}

/// con-leche: ConLeche/Frontend/Olean/Fast.lean:311-316 ModSkel.read
/// `sk.imports.mapM (ImportF.mapM nm)`.
pub fn mod_skel_imports<R: PtrRead>(rd: &R, pk: &OleanPins, pers: &PersTier, ar: &mut EStore, bs: &[u8], r: &Region, sk: &ModSkel) -> Result<Vec<spec::ImportRec>, RdErr> {
    let mut imports: Vec<spec::ImportRec> = Vec::with_capacity(sk.imports.len());
    let mut i = 0usize;
    while i < sk.imports.len() {
        match spec::import_map(rd, pk, pers, ar, bs, r, &sk.imports[i]) {
            Err(e) => return Err(e),
            Ok(x) => imports.push(x),
        }
        i += 1;
    }
    Ok(imports)
}

/// con-leche: ConLeche/Frontend/Olean/Fast.lean:311-316 ModSkel.read
/// `cs.mapM (CEntryF.mapM nm ex)`.
pub fn mod_skel_constants<R: PtrRead>(rd: &R, pk: &OleanPins, pers: &PersTier, ar: &mut EStore, bs: &[u8], r: &Region, cs: &Vec<CEntryF<u64, u64>>) -> Result<Vec<CEntryF<NIdx, EIdx>>, RdErr> {
    let mut out: Vec<CEntryF<NIdx, EIdx>> = Vec::with_capacity(cs.len());
    let mut i = 0usize;
    while i < cs.len() {
        match spec::c_entry_map(rd, pk, pers, ar, bs, r, &cs[i]) {
            Err(e) => return Err(e),
            Ok(c) => out.push(c),
        }
        i += 1;
    }
    Ok(out)
}

/// con-leche: ConLeche/Frontend/Olean/Fast.lean:318-328 parseMany
/// `addrs.all (constNamesOk r)`.
pub fn all_const_names_ok(pk: &OleanPins, pers: &PersTier, ar: &mut EStore, bs: &[u8], r: &Region, addrs: &Vec<u64>) -> Result<bool, CheckError> {
    let mut i = 0usize;
    while i < addrs.len() {
        match spec::const_names_ok(pk, pers, ar, bs, r, addrs[i]) {
            Err(e) => return Err(e),
            Ok(false) => return Ok(false),
            Ok(true) => {}
        }
        i += 1;
    }
    Ok(true)
}

/// con-leche: ConLeche/Frontend/Olean/Fast.lean:318-328 parseMany
/// `sk.consts.mapM (constSkel r)`, each skeleton's numbers checked to fit
/// (`spec::skel_fits`).
pub fn consts_skel(bs: &[u8], r: &Region, consts: &Vec<u64>) -> Result<Vec<CEntryF<u64, u64>>, RdErr> {
    let mut out: Vec<CEntryF<u64, u64>> = Vec::with_capacity(consts.len());
    let mut i = 0usize;
    while i < consts.len() {
        match spec::const_skel(bs, r, consts[i]) {
            None => return Err(RdErr::Bad),
            Some(c) => match spec::skel_fits(&c) {
                Err(e) => return Err(e),
                Ok(()) => out.push(c),
            },
        }
        i += 1;
    }
    Ok(out)
}

/// con-leche: ConLeche/Frontend/Olean/Fast.lean:318-328 parseMany
/// `addrs.mapM (moduleSkel r)`, and each module's constants' skeletons.
pub fn many_skels(bs: &[u8], r: &Region, addrs: &Vec<u64>) -> Result<(Vec<ModSkel>, Vec<Vec<CEntryF<u64, u64>>>), RdErr> {
    let mut sks: Vec<ModSkel> = Vec::with_capacity(addrs.len());
    let mut skels: Vec<Vec<CEntryF<u64, u64>>> = Vec::with_capacity(addrs.len());
    let mut i = 0usize;
    while i < addrs.len() {
        match spec::module_skel(bs, r, addrs[i]) {
            None => return Err(RdErr::Bad),
            Some(sk) => match consts_skel(bs, r, &sk.consts) {
                Err(e) => return Err(e),
                Ok(cs) => {
                    sks.push(sk);
                    skels.push(cs);
                }
            },
        }
        i += 1;
    }
    Ok((sks, skels))
}

/// con-leche: ConLeche/Frontend/Olean/Fast.lean:318-328 parseMany
/// The roots of `runPasses`: the imports' names and the constants' names, and
/// the constants' expressions.
pub fn many_roots(sks: &Vec<ModSkel>, skels: &Vec<Vec<CEntryF<u64, u64>>>) -> (Vec<u64>, Vec<u64>) {
    let mut names: Vec<u64> = Vec::new();
    let mut exprs: Vec<u64> = Vec::new();
    let mut i = 0usize;
    while i < sks.len() {
        let mut j = 0usize;
        while j < sks[i].imports.len() {
            names.push(sks[i].imports[j].module);
            j += 1;
        }
        i += 1;
    }
    let mut a = 0usize;
    while a < skels.len() {
        let mut b = 0usize;
        while b < skels[a].len() {
            c_entry_names(&skels[a][b], &mut names);
            c_entry_exprs(&skels[a][b], &mut exprs);
            b += 1;
        }
        a += 1;
    }
    (names, exprs)
}

/// con-leche: ConLeche/Frontend/Olean/Fast.lean:318-328 parseMany
/// `(sks.zip skels).mapM fun p => p.1.read (st.nameOf r) (st.exprOf r) p.2`.
pub fn many_read(st: &DS, pk: &OleanPins, pers: &PersTier, ar: &mut EStore, bs: &[u8], r: &Region, sks: &Vec<ModSkel>, skels: &Vec<Vec<CEntryF<u64, u64>>>) -> Result<Vec<ModDecoded>, RdErr> {
    let mut out: Vec<ModDecoded> = Vec::with_capacity(sks.len());
    let mut i = 0usize;
    while i < sks.len() {
        match mod_skel_read(st, pk, pers, ar, bs, r, &sks[i], &skels[i]) {
            Err(e) => return Err(e),
            Ok(d) => out.push(d),
        }
        i += 1;
    }
    Ok(out)
}

/// con-leche: ConLeche/Frontend/Olean/Fast.lean:318-328 parseMany
/// **The `ModuleData`s at some addresses of a region, each object read once**,
/// whichever of them reaches it: the name tables checked, both passes from all
/// their names' and expressions' pointers, and one memo.
pub fn parse_many(pk: &OleanPins, pers: &PersTier, ar: &mut EStore, bs: &[u8], r: &Region, addrs: &Vec<u64>) -> Result<Vec<ModDecoded>, RdErr> {
    match all_const_names_ok(pk, pers, ar, bs, r, addrs) {
        Err(e) => return Err(RdErr::Err(e)),
        Ok(false) => return Err(RdErr::Bad),
        Ok(true) => {}
    }
    let (sks, skels) = match many_skels(bs, r, addrs) {
        Err(e) => return Err(e),
        Ok(p) => p,
    };
    let (names, exprs) = many_roots(&sks, &skels);
    match run_passes(pk, pers, ar, bs, r, &names, &exprs) {
        Err(e) => Err(e),
        Ok(st) => many_read(&st, pk, pers, ar, bs, r, &sks, &skels),
    }
}

/// con-leche: ConLeche/Frontend/Olean/Fast.lean:330-334 parseAt
/// **The `ModuleData` at one address**, fast.
pub fn parse_at(pk: &OleanPins, pers: &PersTier, ar: &mut EStore, bs: &[u8], r: &Region, addr: u64) -> Result<ModDecoded, RdErr> {
    let mut addrs: Vec<u64> = Vec::with_capacity(1);
    addrs.push(addr);
    match parse_many(pk, pers, ar, bs, r, &addrs) {
        Err(e) => Err(e),
        Ok(ds) => {
            if ds.len() == 1 {
                let mut ds = ds;
                Ok(take_decoded(&mut ds, 0))
            } else {
                Err(RdErr::Bad)
            }
        }
    }
}

/// con-leche: ConLeche/Frontend/Olean/Fast.lean:330-334 parseAt
/// Entry `i` of a list of views, moved out.
pub fn take_decoded(ds: &mut Vec<ModDecoded>, i: usize) -> ModDecoded {
    core::mem::replace(&mut ds[i], ModDecoded { is_module: false, imports: Vec::new(), constants: Vec::new() })
}

/// con-leche: ConLeche/Frontend/Olean/Fast.lean:336-342 stmtsFast
/// The roots of `stmtsFast`.
pub fn stmts_roots(sks: &Vec<CEntryF<u64, u64>>) -> (Vec<u64>, Vec<u64>) {
    let mut names: Vec<u64> = Vec::new();
    let mut exprs: Vec<u64> = Vec::with_capacity(sks.len());
    let mut i = 0usize;
    while i < sks.len() {
        names.push(sks[i].name);
        push_all(&sks[i].level_params, &mut names);
        exprs.push(sks[i].ty);
        i += 1;
    }
    (names, exprs)
}

/// con-leche: ConLeche/Frontend/Olean/Fast.lean:336-342 stmtsFast
/// The statements read back out of the memo.
pub fn stmts_read(st: &DS, pk: &OleanPins, pers: &PersTier, ar: &mut EStore, bs: &[u8], r: &Region, sks: &Vec<CEntryF<u64, u64>>) -> Result<Vec<StmtRec>, RdErr> {
    let mut out: Vec<StmtRec> = Vec::with_capacity(sks.len());
    let mut i = 0usize;
    while i < sks.len() {
        match st.rd_name(pk, pers, ar, bs, r, sks[i].name) {
            Err(e) => return Err(e),
            Ok(n) => match spec::names_map(st, pk, pers, ar, bs, r, &sks[i].level_params) {
                Err(e) => return Err(e),
                Ok(lps) => match st.rd_expr(pk, pers, ar, bs, r, sks[i].ty) {
                    Err(e) => return Err(e),
                    Ok(t) => out.push(StmtRec { name: n, level_params: lps, ty: t }),
                },
            },
        }
        i += 1;
    }
    Ok(out)
}

/// con-leche: ConLeche/Frontend/Olean/Fast.lean:336-342 stmtsFast
/// **The statements of some constants, read once**: both passes from the chosen
/// constants' roots alone.
pub fn stmts_fast(pk: &OleanPins, pers: &PersTier, ar: &mut EStore, bs: &[u8], r: &Region, sks: &Vec<CEntryF<u64, u64>>) -> Result<Vec<StmtRec>, RdErr> {
    let (names, exprs) = stmts_roots(sks);
    match run_passes(pk, pers, ar, bs, r, &names, &exprs) {
        Err(e) => Err(e),
        Ok(st) => stmts_read(&st, pk, pers, ar, bs, r, sks),
    }
}
