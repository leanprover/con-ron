//! `ConLeche/Frontend/Olean/Lazy.lean` — a module's load, its theorems' values
//! left in the file (upstream task #481).
//!
//! Most of what a module stores is the values of its theorems, and a theorem's
//! value is read by one thing only: the check of that theorem.  So the load
//! ([`load_at`]) reads everything of a module except those values:
//!
//! * **a theorem's value is a reference** ([`value_ref`]) to where it is stored:
//!   a `bvar` whose index codes the module's position in the closure's order and
//!   the value's location;
//! * **what a constant mentions is read off the file** ([`uses_of`]), without
//!   building anything;
//! * **the frontier** ([`frontier_of`]) is what the load keeps of its memo: the
//!   objects it read that a value reaches directly.  A later read of a value
//!   takes those from it (`sparse::frontier_expr`).
//!
//! ## Deviations
//!
//! * **The walks carry fuel** (§3.4): `usesGo` and `frontierWalk` are `partial`
//!   upstream; here they take `closure::CLOSURE_FUEL`, spent being a failed read.
//! * **A `List`/`Array` used as a stack is a `Vec` and its top index**, as in
//!   `closure.rs`: the extraction's `Vec` has no `pop`.
//! * `stamps[s]!` and `set!` past the end are `0` and nothing, as Lean's are.
//! * **`Nat` is `u64`**: a reference's code `g * 2^32 + i` needs `g < 2^32` as
//!   well as upstream's `i < 2^32`; a location past it is a failed read (no
//!   region of one module comes near it).
//! * `nm`/`ex` are the passes' memo (`DS`, a `PtrRead`), and the literal names
//!   `mkN [...]` are the reader's interned pins (`OleanPins`).

use crate::arena::handle::{EIdx, NIdx};
use crate::arena::store::{EStore, PersTier};
use crate::frontend::olean::closure;
use crate::frontend::olean::fast;
use crate::frontend::olean::fast::DS;
use crate::frontend::olean::header;
use crate::frontend::olean::region;
use crate::frontend::olean::region::Region;
use crate::frontend::olean::sparse;
use crate::frontend::olean::sparse::{Frontier, Table};
use crate::frontend::olean::spec;
use crate::frontend::olean::spec::{CEntryF, CKindF, ImportRec, OleanPins, PtrRead, RdErr, Sub};
use crate::frontend::olean::view;
use crate::frontend::olean::view::{ModFiles, OLeanLevel};
use crate::kernel::core_types::CheckError;
use crate::ron::hashmap::Dup;
use crate::ron::hashmap2::HashMap2;

/// con-leche: ConLeche/Frontend/Olean/Lazy.lean:45-47 usesNat
/// A numeral's mark in `usesGo`'s output.
pub const USES_NAT: u64 = 0;
/// con-leche: ConLeche/Frontend/Olean/Lazy.lean:48-49 usesStr
/// A string's mark in `usesGo`'s output.
pub const USES_STR: u64 = 2;

/// con-leche: none — `Array.push` onto a stack with its top at `sp` (module note)
/// The new top.
#[inline(always)]
pub fn push_at(stack: &mut Vec<u64>, sp: usize, x: u64) -> usize {
    if sp < stack.len() {
        stack[sp] = x;
    } else {
        stack.push(x);
    }
    sp + 1
}

/// con-leche: ConLeche/Frontend/Olean/Lazy.lean:51-59 pushKid
/// The kid in field `i` of the expression object at `g`, onto the walk's stack;
/// the new top, `None` where the field does not point below `g`.
#[inline(always)]
pub fn push_kid(bs: &[u8], r: &Region, g: u64, i: u64, stack: &mut Vec<u64>, sp: Option<usize>) -> Option<usize> {
    match sp {
        None => None,
        Some(s) => match region::region_down(r, g, region::region_fld(bs, g, i)) {
            Some(c) => Some(push_at(stack, s, c)),
            None => None,
        },
    }
}

/// con-leche: none — `stamps[s]!`, `0` past the end
#[inline(always)]
pub fn stamp_at(stamps: &Vec<u64>, s: u64) -> u64 {
    if s < (stamps.len() as u64) {
        stamps[s as usize]
    } else {
        0
    }
}

/// con-leche: ConLeche/Frontend/Olean/Lazy.lean:61-104 usesGo
/// **The DAG walk of what an expression mentions**, from the `sp` entries on the
/// stack: each object once in a walk (`stamps`, by slot, holds the walk that saw
/// it last), left to right, every constant's name field into `out`, as it stands
/// in the file, and `USES_NAT`/`USES_STR` at a literal.  `false` at an object no
/// expression is stored as.
pub fn uses_go(bs: &[u8], r: &Region, stamps: &mut Vec<u64>, stamp: u64, stack: &mut Vec<u64>, sp: usize, out: &mut Vec<u64>) -> bool {
    let mut sp = sp;
    let mut fuel = closure::CLOSURE_FUEL;
    while sp > 0 {
        if fuel == 0 {
            return false;
        }
        fuel -= 1;
        sp -= 1;
        let g = stack[sp];
        let s = g / 8;
        if stamp_at(stamps, s) != stamp {
            if s < (stamps.len() as u64) {
                stamps[s as usize] = stamp;
            }
            if !region::region_fits(bs, r, g) {
                return false;
            }
            let t = region::region_tag(bs, g);
            let n = region::region_nobjs(bs, g);
            let next: Option<usize> = if (t == 0 && n == 1) || (t == 3 && n == 1) {
                Some(sp)
            } else if t == 4 && n == 2 {
                out.push(region::region_fld(bs, g, 0));
                Some(sp)
            } else if t == 5 && n == 2 {
                let a = push_kid(bs, r, g, 1, stack, Some(sp));
                push_kid(bs, r, g, 0, stack, a)
            } else if (t == 6 || t == 7) && n == 3 {
                let a = push_kid(bs, r, g, 2, stack, Some(sp));
                push_kid(bs, r, g, 1, stack, a)
            } else if t == 8 && n == 4 {
                let a = push_kid(bs, r, g, 3, stack, Some(sp));
                let b = push_kid(bs, r, g, 2, stack, a);
                push_kid(bs, r, g, 1, stack, b)
            } else if t == 9 && n == 1 {
                match region::region_down(r, g, region::region_fld(bs, g, 0)) {
                    Some(c) => {
                        if region::region_is_ctor(bs, r, c, 0, 1) {
                            out.push(USES_NAT);
                            Some(sp)
                        } else if region::region_is_ctor(bs, r, c, 1, 1) {
                            out.push(USES_STR);
                            Some(sp)
                        } else {
                            None
                        }
                    }
                    None => None,
                }
            } else if t == 10 && n == 2 {
                push_kid(bs, r, g, 1, stack, Some(sp))
            } else if t == 11 && n == 3 {
                push_kid(bs, r, g, 2, stack, Some(sp))
            } else {
                None
            };
            match next {
                None => return false,
                Some(s2) => sp = s2,
            }
        }
    }
    true
}

/// con-leche: ConLeche/Frontend/Olean/Lazy.lean:106-116 usesRoots
/// One constant's expressions, in order, one walk.
pub fn uses_roots(bs: &[u8], r: &Region, stamps: &mut Vec<u64>, stamp: u64, out: &mut Vec<u64>, vs: &Vec<u64>) -> bool {
    let mut stack: Vec<u64> = Vec::new();
    let mut i = 0usize;
    while i < vs.len() {
        match region::region_loc(r, vs[i]) {
            None => return false,
            Some(g) => {
                let sp = push_at(&mut stack, 0, g);
                if !uses_go(bs, r, stamps, stamp, &mut stack, sp, out) {
                    return false;
                }
            }
        }
        i += 1;
    }
    true
}

/// con-leche: ConLeche/Frontend/Olean/Lazy.lean:118-126 usesOf
/// **What each constant mentions**, as `usesGo` writes it: its statement and its
/// values (`CEntryF.exprs`), a walk of its own per constant, `stamp` counting
/// the walks.
pub fn uses_of(bs: &[u8], r: &Region, stamps: &mut Vec<u64>, stamp: u64, cs: &Vec<CEntryF<u64, u64>>) -> Option<Vec<Vec<u64>>> {
    let mut outs: Vec<Vec<u64>> = Vec::with_capacity(cs.len());
    let mut stamp = stamp;
    let mut i = 0usize;
    while i < cs.len() {
        let mut es: Vec<u64> = Vec::new();
        fast::c_entry_exprs(&cs[i], &mut es);
        let mut out: Vec<u64> = Vec::new();
        if !uses_roots(bs, r, stamps, stamp, &mut out, &es) {
            return None;
        }
        outs.push(out);
        stamp += 1;
        i += 1;
    }
    Some(outs)
}

/// con-leche: ConLeche/Frontend/Olean/Lazy.lean:128-132 usesNames
/// The names in `usesGo`'s outputs, onto `acc`: roots of the load, so that the
/// walk's output can be read off its memo.
pub fn uses_names(outs: &Vec<Vec<u64>>, acc: &mut Vec<u64>) {
    let mut i = 0usize;
    while i < outs.len() {
        let mut j = 0usize;
        while j < outs[i].len() {
            let v = outs[i][j];
            if !(v == USES_NAT || v == USES_STR) {
                acc.push(v);
            }
            j += 1;
        }
        i += 1;
    }
}

/// con-leche: ConLeche/Frontend/Olean/Lazy.lean:134-137 addUse
/// A name once, in first-visit order.
#[inline(always)]
pub fn add_use(seen: &mut HashMap2<NIdx, bool>, out: &mut Vec<NIdx>, n: &NIdx) {
    if !seen.contains_key(n) {
        seen.insert(n.dup2(), true);
        out.push(n.dup2());
    }
}

/// con-leche: ConLeche/Frontend/Olean/Lazy.lean:139-150 usesRead
/// con-leche: CHANGED since 701d72ae — re-port, re-test, re-prove lazy::uses_read_refines, then delete this line
/// **What a constant mentions, as names**: in first-visit order, each once, and
/// the literal dependencies lean4export adds: `Nat` for a numeral, `Char.ofNat`
/// and `String.ofList` for a string.  Where a name does not read, it is left out.
pub fn uses_read(pk: &OleanPins, pers: &PersTier, ar: &mut EStore, bs: &[u8], r: &Region, nm: &DS, out: &Vec<u64>) -> Vec<NIdx> {
    let mut seen: HashMap2<NIdx, bool> = HashMap2::with_capacity(64);
    let mut acc: Vec<NIdx> = Vec::new();
    let mut i = 0usize;
    while i < out.len() {
        let v = out[i];
        if v == USES_NAT {
            add_use(&mut seen, &mut acc, &pk.n_nat);
        } else if v == USES_STR {
            add_use(&mut seen, &mut acc, &pk.n_char_of_nat);
            add_use(&mut seen, &mut acc, &pk.n_string_of_list);
        } else {
            match nm.rd_name(pk, pers, ar, bs, r, v) {
                Ok(n) => add_use(&mut seen, &mut acc, &n),
                Err(_) => {}
            }
        }
        i += 1;
    }
    acc
}

/// con-leche: ConLeche/Frontend/Olean/Lazy.lean:164-168 CEntry
/// con-leche: CHANGED since 701d72ae — re-port, re-test, re-prove lazy::CEntry_refines, then delete this line
/// **One stored constant**, as the merge and the emitter need it: the constant
/// read (`lazy_entry`: a theorem's value is its reference) and the constants its
/// type and values mention, in first-visit order.
pub struct CEntry {
    pub c: CEntryF<NIdx, EIdx>,
    pub uses: Vec<NIdx>,
}

/// con-leche: ConLeche/Frontend/Olean/Lazy.lean:172-173 CEntry.skipped
/// `CKindF.skipped` of a stored constant.
pub fn c_entry_skipped(c: &CEntry) -> bool {
    crate::frontend::olean::reads::c_kind_skipped(&c.c.kind)
}

/// con-leche: ConLeche/Frontend/Olean/Lazy.lean:175-180 Loaded
/// **A loaded module**: its constants at the private level, and the frontier its
/// theorems' values are read over.
pub struct Loaded {
    pub name: NIdx,
    pub constants: Vec<CEntry>,
    pub frontier: Frontier,
}

/// con-leche: ConLeche/Frontend/Olean/Lazy.lean:184-185 refBase
/// What separates the two parts of a reference.
pub const REF_BASE: u64 = 1 << 32;

/// con-leche: ConLeche/Frontend/Olean/Lazy.lean:187-190 valueRef
/// **A theorem's value, until its check reads it**: the value at location `g` of
/// module `i` of the closure's order, as an expression (`i`, `g` below `2^32`).
pub fn value_ref(pers: &PersTier, ar: &mut EStore, i: u64, g: u64) -> Result<EIdx, CheckError> {
    ar.intern_bvar(pers, g * REF_BASE + i)
}

/// con-leche: ConLeche/Frontend/Olean/Lazy.lean:192-193 refModule
/// The module a reference's code names.
pub fn ref_module(code: u64) -> u64 {
    code % REF_BASE
}

/// con-leche: ConLeche/Frontend/Olean/Lazy.lean:195-196 refLoc
/// The location a reference's code names.
pub fn ref_loc(code: u64) -> u64 {
    code / REF_BASE
}

/// con-leche: ConLeche/Frontend/Olean/Lazy.lean:198-202 lazyRoots
/// The expressions the load reads of a constant, onto `out`: all but a
/// theorem's value.
pub fn lazy_roots(c: &CEntryF<u64, u64>, out: &mut Vec<u64>) {
    match &c.kind {
        CKindF::Thm(_, _) => out.push(c.ty),
        _ => fast::c_entry_exprs(c, out),
    }
}

/// con-leche: ConLeche/Frontend/Olean/Lazy.lean:204-216 lazyEntry
/// **A constant read, a theorem's value as its reference.**
pub fn lazy_entry(pk: &OleanPins, pers: &PersTier, ar: &mut EStore, bs: &[u8], r: &Region, st: &DS, i: u64, s: &CEntryF<u64, u64>) -> Result<CEntryF<NIdx, EIdx>, RdErr> {
    match &s.kind {
        CKindF::Thm(v, all) => {
            if !(i < REF_BASE) {
                return Err(RdErr::Bad);
            }
            let g = match region::region_loc(r, *v) {
                None => return Err(RdErr::Bad),
                Some(g) => g,
            };
            if !(g < REF_BASE) {
                return Err(RdErr::Bad);
            }
            let name = match st.rd_name(pk, pers, ar, bs, r, s.name) {
                Err(e) => return Err(e),
                Ok(n) => n,
            };
            let lps = match spec::names_map(st, pk, pers, ar, bs, r, &s.level_params) {
                Err(e) => return Err(e),
                Ok(x) => x,
            };
            let ty = match st.rd_expr(pk, pers, ar, bs, r, s.ty) {
                Err(e) => return Err(e),
                Ok(t) => t,
            };
            let all2 = match spec::names_map(st, pk, pers, ar, bs, r, all) {
                Err(e) => return Err(e),
                Ok(x) => x,
            };
            match value_ref(pers, ar, i, g) {
                Err(e) => Err(RdErr::Err(e)),
                Ok(vr) => Ok(CEntryF { name, level_params: lps, ty, kind: CKindF::Thm(vr, all2) }),
            }
        }
        _ => spec::c_entry_map(st, pk, pers, ar, bs, r, s),
    }
}

/// con-leche: ConLeche/Frontend/Olean/Lazy.lean:218-231 lazyEntries
/// con-leche: CHANGED since 701d72ae — re-port, re-test, re-prove lazy::lazy_entries_refines, then delete this line
/// `lazyEntry` of every constant, each with what it mentions (`outs`, by
/// position).
pub fn lazy_entries(pk: &OleanPins, pers: &PersTier, ar: &mut EStore, bs: &[u8], r: &Region, st: &DS, i: u64, outs: &Vec<Vec<u64>>, ss: &Vec<CEntryF<u64, u64>>) -> Result<Vec<CEntry>, RdErr> {
    let mut es: Vec<CEntry> = Vec::with_capacity(ss.len());
    let mut k = 0usize;
    while k < ss.len() {
        match lazy_entry(pk, pers, ar, bs, r, st, i, &ss[k]) {
            Err(e) => return Err(e),
            Ok(c) => {
                let uses = if k < outs.len() {
                    uses_read(pk, pers, ar, bs, r, st, &outs[k])
                } else {
                    Vec::new()
                };
                es.push(CEntry { c, uses });
            }
        }
        k += 1;
    }
    Ok(es)
}

/// con-leche: ConLeche/Frontend/Olean/Lazy.lean:235-237 kindCode
/// A kind as a stack entry's low bits.
#[inline(always)]
pub fn kind_code(k: u8) -> u64 {
    if k == fast::K_NAME {
        0
    } else if k == fast::K_LEVEL {
        1
    } else if k == fast::K_LEVELS {
        2
    } else {
        3
    }
}

/// con-leche: ConLeche/Frontend/Olean/Lazy.lean:239-241 kindOfCode
/// The kind of a stack entry's low bits.
#[inline(always)]
pub fn kind_of_code(c: u64) -> u8 {
    if c == 0 {
        fast::K_NAME
    } else if c == 1 {
        fast::K_LEVEL
    } else if c == 2 {
        fast::K_LEVELS
    } else {
        fast::K_EXPR
    }
}

/// con-leche: ConLeche/Frontend/Olean/Lazy.lean:243-266 frontierWalk
/// **The objects the load read that the values reach directly**: a walk from the
/// `sp` entries on the stack over what the load did not read (each object once,
/// `seen`), stopping at what it did (`env`), which goes into `fr`.  Entries are a
/// location and a kind's code.  Fuel spent leaves `fr` as it is: the frontier is
/// a matter of speed alone.
pub fn frontier_walk(bs: &[u8], r: &Region, env: &Vec<u8>, seen: &mut Vec<u8>, fr: &mut Vec<u8>, stack: &mut Vec<u64>, sp: usize) {
    let mut sp = sp;
    let mut fuel = closure::CLOSURE_FUEL;
    while sp > 0 && fuel > 0 {
        fuel -= 1;
        sp -= 1;
        let e = stack[sp];
        let g = e / 8 * 8;
        let k = kind_of_code(e % 8);
        let s = g / 8;
        if fast::marked(env, k, s) {
            fast::mark(fr, k, s);
        } else if !fast::marked(seen, k, s) {
            fast::mark(seen, k, s);
            match sparse::kid_table(k, region::region_tag(bs, g), region::region_nobjs(bs, g)) {
                None => {}
                Some(fs) => {
                    let mut j = 0usize;
                    while j < fs.len() {
                        let v = region::region_fld(bs, g, fs[j].0);
                        if !(fs[j].2 && v == 1) {
                            match region::region_down(r, g, v) {
                                Some(c) => sp = push_at(stack, sp, c + kind_code(fs[j].1)),
                                None => {}
                            }
                        }
                        j += 1;
                    }
                }
            }
        }
    }
}

/// con-leche: ConLeche/Frontend/Olean/Lazy.lean:268-271 Table.add
/// A table with one more entry, at the end.
#[inline(always)]
pub fn table_add<T>(t: &mut Table<T>, c: u64, v: T) {
    t.keys.push(c);
    t.vals.push(v);
}

/// con-leche: ConLeche/Frontend/Olean/Lazy.lean:273-282 frontierStep
/// Slot `p` of `fr`, where the marks `m` hold it too, into the frontier.
pub fn frontier_step(m: &Vec<u8>, fr: &Vec<u8>, st: &DS, p: u64, b: &mut Frontier) {
    if fast::marks_at(fr, p) == 0 {
        return;
    }
    let c = 8 * p;
    if fast::marked(fr, fast::K_NAME, p) && fast::marked(m, fast::K_NAME, p) {
        match st.sub_name(c) {
            Some(v) => table_add(&mut b.names, c, v),
            None => {}
        }
    }
    if fast::marked(fr, fast::K_LEVEL, p) && fast::marked(m, fast::K_LEVEL, p) {
        match st.sub_level(c) {
            Some(v) => table_add(&mut b.levels, c, v),
            None => {}
        }
    }
    if fast::marked(fr, fast::K_LEVELS, p) && fast::marked(m, fast::K_LEVELS, p) {
        match st.sub_levels(c) {
            Some(v) => table_add(&mut b.lists, c, v),
            None => {}
        }
    }
    if fast::marked(fr, fast::K_EXPR, p) && fast::marked(m, fast::K_EXPR, p) {
        match st.sub_expr(c) {
            Some(v) => table_add(&mut b.exprs, c, v),
            None => {}
        }
    }
}

/// con-leche: ConLeche/Frontend/Olean/Lazy.lean:284-288 frontierOf
/// **The frontier**: the slots from `p` to `n` of `fr` that the marks `m` hold,
/// with their values in the passes' memo.  Ascending, so each table's keys are.
pub fn frontier_of(m: &Vec<u8>, fr: &Vec<u8>, st: &DS, n: u64, p: u64, b: Frontier) -> Frontier {
    let mut b = b;
    let mut p = p;
    while p < n {
        frontier_step(m, fr, st, p, &mut b);
        p += 1;
    }
    b
}

/// con-leche: ConLeche/Frontend/Olean/Lazy.lean:292-311 loadAt
/// con-leche: CHANGED since 701d72ae — re-port, re-test, re-prove lazy::load_roots_refines, then delete this line
/// The name and expression roots of the load, the walk's outputs' names among
/// them.
pub fn load_roots(sk: &spec::ModSkel, skels: &Vec<CEntryF<u64, u64>>) -> (Vec<u64>, Vec<u64>) {
    let mut names: Vec<u64> = Vec::new();
    let mut j = 0usize;
    while j < sk.imports.len() {
        names.push(sk.imports[j].module);
        j += 1;
    }
    let mut exprs: Vec<u64> = Vec::new();
    let mut i = 0usize;
    while i < skels.len() {
        fast::c_entry_names(&skels[i], &mut names);
        fast::c_entry_exprs(&skels[i], &mut exprs);
        i += 1;
    }
    (names, exprs)
}

/// con-leche: ConLeche/Frontend/Olean/Lazy.lean:292-311 loadAt
/// con-leche: CHANGED since 701d72ae — re-port, re-test, re-prove lazy::load_imports_refines, then delete this line
/// `sk.imports.mapM (ImportF.mapM (st.nameOf r))`, then `importsPre f.exported.bytes
/// == some imports`.
pub fn load_imports(pk: &OleanPins, pers: &PersTier, ar: &mut EStore, bs: &[u8], r: &Region, st: &DS, sk: &spec::ModSkel, f: &ModFiles) -> Result<(), RdErr> {
    let mut imports: Vec<ImportRec> = Vec::with_capacity(sk.imports.len());
    let mut i = 0usize;
    while i < sk.imports.len() {
        match spec::import_map(st, pk, pers, ar, bs, r, &sk.imports[i]) {
            Err(e) => return Err(e),
            Ok(x) => imports.push(x),
        }
        i += 1;
    }
    match header::imports_pre(pk, pers, ar, &f.exported.bytes) {
        Err(e) => Err(e),
        Ok(pre) => {
            if spec::imports_beq(&pre, &imports) {
                Ok(())
            } else {
                Err(RdErr::Bad)
            }
        }
    }
}

/// con-leche: ConLeche/Frontend/Olean/Lazy.lean:292-311 loadAt
/// con-leche: CHANGED since 701d72ae — re-port, re-test, re-prove lazy::value_roots_refines, then delete this line
/// The values' locations, each with the expression kind's code: the walk's
/// start.
pub fn value_roots(r: &Region, skels: &Vec<CEntryF<u64, u64>>) -> Vec<u64> {
    value_roots_from(r, skels, 0, Vec::new())
}

/// con-leche: ConLeche/Frontend/Olean/Lazy.lean:292-311 loadAt
/// con-leche: CHANGED since 701d72ae — re-port, re-test, re-prove lazy::value_roots_from_refines, then delete this line
/// The cursor recursion behind `value_roots`.
pub fn value_roots_from(r: &Region, skels: &Vec<CEntryF<u64, u64>>, i: usize, out: Vec<u64>) -> Vec<u64> {
    if i >= skels.len() {
        out
    } else {
        let g: Option<u64> = match &skels[i].kind {
            CKindF::Thm(v, _) => region::region_loc(r, *v),
            _ => None,
        };
        let mut out = out;
        match g {
            Some(g) => out.push(g + kind_code(fast::K_EXPR)),
            None => (),
        }
        value_roots_from(r, skels, i + 1, out)
    }
}

/// con-leche: ConLeche/Frontend/Olean/Lazy.lean:292-311 loadAt
/// con-leche: CHANGED since 701d72ae — re-port, re-test, re-prove lazy::load_at_refines, then delete this line
/// **The load of a module's private view**, everything but its theorems'
/// values.  `RdErr::Bad` where the part of the view it reads does not read:
/// `view_error` says why.
pub fn load_at(pk: &OleanPins, pers: &PersTier, ar: &mut EStore, i: u64, m: &NIdx, f: &ModFiles) -> Result<Loaded, RdErr> {
    let (vb, a) = match view::mod_files_view_region(f, &OLeanLevel::Private) {
        None => return Err(RdErr::Bad),
        Some(p) => p,
    };
    let bs: &[u8] = view::view_bytes(f, &vb);
    let r: Region = view::view_region_of(f, &vb);
    match spec::const_names_ok(pk, pers, ar, bs, &r, a) {
        Err(e) => return Err(RdErr::Err(e)),
        Ok(false) => return Err(RdErr::Bad),
        Ok(true) => {}
    }
    let sk = match spec::module_skel(bs, &r, a) {
        None => return Err(RdErr::Bad),
        Some(sk) => sk,
    };
    let skels = match fast::consts_skel(bs, &r, &sk.consts) {
        Err(e) => return Err(e),
        Ok(v) => v,
    };
    let (names_b, exprs_all) = load_roots(&sk, &skels);
    let n: u64 = fast::max_loc(&r, &exprs_all, fast::max_loc(&r, &names_b, 0)) / 8 + 1;
    let mut stamps: Vec<u64> = Vec::new();
    stamps.resize(n as usize, 0u64);
    let outs = match uses_of(bs, &r, &mut stamps, 1, &skels) {
        None => return Err(RdErr::Bad),
        Some(o) => o,
    };
    let mut names = names_b;
    uses_names(&outs, &mut names);
    let mut lazy: Vec<u64> = Vec::new();
    let mut k = 0usize;
    while k < skels.len() {
        lazy_roots(&skels[k], &mut lazy);
        k += 1;
    }
    let (nm, ms, st) = match fast::run_marked(pk, pers, ar, bs, &r, &names, &lazy) {
        Err(e) => return Err(e),
        Ok(x) => x,
    };
    match load_imports(pk, pers, ar, bs, &r, &st, &sk, f) {
        Err(e) => return Err(e),
        Ok(()) => {}
    }
    let cs = match lazy_entries(pk, pers, ar, bs, &r, &st, i, &outs, &skels) {
        Err(e) => return Err(e),
        Ok(cs) => cs,
    };
    let mut values = value_roots(&r, &skels);
    let sp = values.len();
    let mut seen: Vec<u8> = fast::zeros(n as usize);
    let mut fr: Vec<u8> = fast::zeros(n as usize);
    frontier_walk(bs, &r, &ms, &mut seen, &mut fr, &mut values, sp);
    let frontier = frontier_of(&ms, &fr, &st, nm, 0, sparse::frontier_empty());
    Ok(Loaded { name: m.dup2(), constants: cs, frontier })
}

/// con-leche: ConLeche/Frontend/Olean/Lazy.lean:313-317 loadView
/// **The load, with the reason where it does not read.**
pub fn load_view(pk: &OleanPins, pers: &PersTier, ar: &mut EStore, i: u64, m: &NIdx, f: &ModFiles) -> Result<Loaded, CheckError> {
    match load_at(pk, pers, ar, i, m, f) {
        Ok(l) => Ok(l),
        Err(RdErr::Err(e)) => Err(e),
        Err(RdErr::Bad) => Err(view::view_error(pk, pers, ar, m, f, &OLeanLevel::Private)),
    }
}
