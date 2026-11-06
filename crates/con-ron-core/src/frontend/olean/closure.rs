//! `ConLeche/Frontend/Olean/Closure.lean` — the import closure (task #142).
//!
//! The closure's module order from the headers alone, then every module read in
//! full.
//!
//! ## Deviations
//!
//! * **`parMapExcept` is the sequential map** (`load_closure`).  The store has one
//!   writer and the reader interns as it reads; DESIGN.md's `### Task #142` weighs
//!   the alternatives with the numbers.  The class's model says the two are one.
//! * **A `List` used as a stack is a `Vec` and its top**: the head of the Lean's
//!   list is the last live element.  The extraction's `Vec` has no `pop`, so the
//!   top is an index and a popped slot stays until it is overwritten.
//! * **Every walk carries fuel** (§3.4, "recursion carries the same explicit
//!   fuel"): `constsGo` is `partial` upstream and `emitLoop` well-founded on a
//!   measure over hash maps; both take [`CLOSURE_FUEL`] here, as `closureGo` does
//!   upstream, spent being an `Internal` error.
//! * **`constsGo`'s two sets are reused between constants** (`ConstsWork`), by the
//!   epoch-stamped `clear`, where the Lean allocates them per constant.  Nothing
//!   outlives a constant: this is an allocation, not a cache.

use crate::arena::handle::{EIdx, NIdx, ETAG_APP, ETAG_BVAR, ETAG_CONST, ETAG_FORALL_E, ETAG_FVAR, ETAG_LAM, ETAG_LET_E, ETAG_LIT, ETAG_PROJ, ETAG_SORT};
use crate::arena::monad;
use crate::arena::store::{EStore, PersTier};
use crate::frontend::olean::files;
use crate::frontend::olean::files::OleanFs;
use crate::frontend::olean::spec::{CEntryF, CKindF, ImportRec, ModDecoded, OleanPins};
use crate::frontend::olean::view;
use crate::frontend::olean::view::OLeanLevel;
use crate::frontend::text;
use crate::kernel::core_types;
use crate::kernel::core_types::CheckError;
use crate::kernel::expr::Literal;
use crate::ron::hashmap::Dup;
use crate::ron::hashmap2::HashMap2;

/// con-leche: ConLeche/Frontend/Olean/Closure.lean:25-62 constsGo
/// The two sets and the stack of `constsGo`, reused between constants.
pub struct ConstsWork {
    pub stack: Vec<EIdx>,
    pub seen: HashMap2<EIdx, bool>,
    pub seen_n: HashMap2<NIdx, bool>,
}

/// con-leche: ConLeche/Frontend/Olean/Closure.lean:64-69 constsOf
/// Fresh work space.
pub fn consts_work_empty() -> ConstsWork {
    ConstsWork { stack: Vec::new(), seen: HashMap2::new(), seen_n: HashMap2::new() }
}

/// con-leche: ConLeche/Frontend/Olean/Closure.lean:25-62 constsGo
/// Push onto a stack with its top at `sp`; the new top.
#[inline(always)]
pub fn stack_push(stack: &mut Vec<EIdx>, sp: usize, x: EIdx) -> usize {
    if sp < stack.len() {
        stack[sp] = x;
    } else {
        stack.push(x);
    }
    sp + 1
}

/// con-leche: ConLeche/Frontend/Olean/Closure.lean:25-62 constsGo
/// A name, once: "written out at each leaf" upstream.
#[inline(always)]
pub fn add_n(seen_n: &mut HashMap2<NIdx, bool>, out: &mut Vec<NIdx>, n: &NIdx) {
    if !seen_n.contains_key(n) {
        seen_n.insert(n.dup2(), true);
        out.push(n.dup2());
    }
}

/// con-leche: ConLeche/Frontend/Olean/Closure.lean:125-127 closureFuel
/// The walks' step bound: far beyond any closure.
pub const CLOSURE_FUEL: u64 = 1 << 40;

/// con-leche: none — a walk's fuel spent
pub fn out_of_fuel<T>() -> Result<T, CheckError> {
    Err(core_types::internal({ const M: [u32; 42] = [116, 104, 101, 32, 105, 109, 112, 111, 114, 116, 32, 99, 108, 111, 115, 117, 114, 101, 39, 115, 32, 119, 97, 108, 107, 32, 114, 97, 110, 32, 111, 117, 116, 32, 111, 102, 32, 115, 116, 101, 112, 115]; crate::kernel::core_types::code_points(&M) }))
}

/// con-leche: ConLeche/Frontend/Olean/Closure.lean:25-62 constsGo
/// A compound node's children, onto the stack; the new top.  A first visit.
pub fn consts_children(pers: &PersTier, ar: &EStore, stack: &mut Vec<EIdx>, sp: usize, e: &EIdx, t: u32) -> Result<usize, CheckError> {
    if t == ETAG_APP {
        match ar.view_app(pers, e) {
            None => monad::fail_dangling_e(),
            Some((f, a)) => {
                let s = stack_push(stack, sp, a);
                Ok(stack_push(stack, s, f))
            }
        }
    } else if t == ETAG_LAM || t == ETAG_FORALL_E {
        match ar.view_bind(pers, e) {
            None => monad::fail_dangling_e(),
            Some((ty, b)) => {
                let s = stack_push(stack, sp, b);
                Ok(stack_push(stack, s, ty))
            }
        }
    } else if t == ETAG_LET_E {
        match ar.view_let(pers, e) {
            None => monad::fail_dangling_e(),
            Some((ty, v, b)) => {
                let s = stack_push(stack, sp, b);
                let s = stack_push(stack, s, v);
                Ok(stack_push(stack, s, ty))
            }
        }
    } else if t == ETAG_PROJ {
        match ar.view_proj(pers, e) {
            None => monad::fail_dangling_e(),
            Some((_, _, x)) => Ok(stack_push(stack, sp, x)),
        }
    } else if t == ETAG_FVAR {
        match ar.view_fvar_ty(pers, e) {
            None => monad::fail_dangling_e(),
            Some(ty) => Ok(stack_push(stack, sp, ty)),
        }
    } else {
        Ok(sp)
    }
}

/// con-leche: ConLeche/Frontend/Olean/Closure.lean:25-62 constsGo
/// The DAG walk of `constsOf`, from the `sp` entries on the stack.
pub fn consts_go(pk: &OleanPins, pers: &PersTier, ar: &EStore, w: &mut ConstsWork, sp: usize, out: Vec<NIdx>) -> Result<Vec<NIdx>, CheckError> {
    let mut sp = sp;
    let mut out = out;
    let mut fuel = CLOSURE_FUEL;
    while sp > 0 {
        if fuel == 0 {
            return out_of_fuel();
        }
        fuel -= 1;
        sp -= 1;
        let e: EIdx = w.stack[sp].dup2();
        let t: u32 = e.tag();
        if t == ETAG_CONST {
            match ar.view_const_name(pers, &e) {
                None => return monad::fail_dangling_e(),
                Some(n) => add_n(&mut w.seen_n, &mut out, &n),
            }
        } else if t == ETAG_LIT {
            match ar.view_lit(pers, &e) {
                None => return monad::fail_dangling_e(),
                Some(Literal::NatVal(_)) => add_n(&mut w.seen_n, &mut out, &pk.n_nat),
                Some(Literal::StrVal(_)) => {
                    add_n(&mut w.seen_n, &mut out, &pk.n_char_of_nat);
                    add_n(&mut w.seen_n, &mut out, &pk.n_string_of_list);
                }
            }
        } else if !(t == ETAG_BVAR || t == ETAG_SORT) {
            if !w.seen.contains_key(&e) {
                w.seen.insert(e.dup2(), true);
                match consts_children(pers, ar, &mut w.stack, sp, &e, t) {
                    Err(x) => return Err(x),
                    Ok(s) => sp = s,
                }
            }
        }
    }
    Ok(out)
}

/// con-leche: ConLeche/Frontend/Olean/Closure.lean:64-69 constsOf
/// **The constants the expressions on `es` mention**, in first-visit order, and
/// the literal dependencies lean4export adds.
pub fn consts_of(pk: &OleanPins, pers: &PersTier, ar: &EStore, w: &mut ConstsWork, es: &Vec<EIdx>) -> Result<Vec<NIdx>, CheckError> {
    w.seen.clear();
    w.seen_n.clear();
    let mut sp = 0usize;
    let mut i = es.len();
    while i > 0 {
        i -= 1;
        sp = stack_push(&mut w.stack, sp, es[i].dup2());
    }
    consts_go(pk, pers, ar, w, sp, Vec::new())
}

/// con-leche: ConLeche/Frontend/Olean/Closure.lean:71-75 CEntry
/// **One stored constant**, as the merge and the emitter need it.
pub struct CEntry {
    pub c: CEntryF<NIdx, EIdx>,
    pub uses: Vec<NIdx>,
}

/// con-leche: ConLeche/Frontend/Olean/Closure.lean:79-80 CEntry.skipped
/// `CKindF.skipped` of a stored constant.
pub fn c_entry_skipped(c: &CEntry) -> bool {
    crate::frontend::olean::reads::c_kind_skipped(&c.c.kind)
}

/// con-leche: ConLeche/Frontend/Olean/Closure.lean:82-87 CEntry.deps
/// The expressions a record depends on.
pub fn c_entry_deps(c: &CEntryF<NIdx, EIdx>) -> Vec<EIdx> {
    let mut out: Vec<EIdx> = Vec::new();
    out.push(c.ty.dup2());
    match &c.kind {
        CKindF::Defn(v, _, _) => out.push(v.dup2()),
        CKindF::Thm(v, _) => out.push(v.dup2()),
        CKindF::Opaq(v, _) => out.push(v.dup2()),
        CKindF::Recur(_, _, _, _, _, rules, _, _) => {
            let mut i = 0usize;
            while i < rules.len() {
                out.push(rules[i].2.dup2());
                i += 1;
            }
        }
        _ => {}
    }
    out
}

/// con-leche: ConLeche/Frontend/Olean/Closure.lean:89-92 CEntry.ofRead
/// A constant with what it mentions.
pub fn c_entry_of_read(pk: &OleanPins, pers: &PersTier, ar: &EStore, w: &mut ConstsWork, c: CEntryF<NIdx, EIdx>) -> Result<CEntry, CheckError> {
    let es = c_entry_deps(&c);
    match consts_of(pk, pers, ar, w, &es) {
        Err(e) => Err(e),
        Ok(uses) => Ok(CEntry { c, uses }),
    }
}

/// con-leche: ConLeche/Frontend/Olean/Closure.lean:96-123 closureGo
/// The cycle check of `closureGo`: the first import of `m` on the walk's current
/// path, if any.
pub fn import_on_path<'a>(imps: &'a Vec<ImportRec>, seen: &HashMap2<NIdx, bool>, done: &HashMap2<NIdx, bool>) -> Option<&'a NIdx> {
    let mut i = 0usize;
    while i < imps.len() {
        let c = &imps[i].module;
        if seen.contains_key(c) && !done.contains_key(c) {
            return Some(c);
        }
        i += 1;
    }
    None
}

/// con-leche: ConLeche/Frontend/Olean/Closure.lean:96-123 closureGo
/// Push onto the walk's stack with its top at `sp`; the new top.
pub fn walk_push(stack: &mut Vec<(NIdx, bool)>, sp: usize, x: (NIdx, bool)) -> usize {
    if sp < stack.len() {
        stack[sp] = x;
    } else {
        stack.push(x);
    }
    sp + 1
}

/// con-leche: ConLeche/Frontend/Olean/Closure.lean:96-123 closureGo
/// `kids ++ (m, true) :: rest`, onto the stack; the new top.
pub fn walk_expand(stack: &mut Vec<(NIdx, bool)>, sp: usize, m: &NIdx, imps: &Vec<ImportRec>, seen: &HashMap2<NIdx, bool>) -> usize {
    let mut s = walk_push(stack, sp, (m.dup2(), true));
    let mut i = imps.len();
    while i > 0 {
        i -= 1;
        if !seen.contains_key(&imps[i].module) {
            s = walk_push(stack, s, (imps[i].module.dup2(), false));
        }
    }
    s
}

/// con-leche: ConLeche/Frontend/Olean/Closure.lean:96-123 closureGo
/// **The import closure, in Lean's module order**: a module after everything it
/// imports, a depth-first post-order, by an explicit stack.  A module whose imports
/// are being expanded is on the walk's current path, so an import of it is a cycle.
pub fn closure_go<F: OleanFs>(fs: &F, pk: &OleanPins, pers: &PersTier, ar: &mut EStore, sp_dirs: &Vec<Vec<u32>>, stack: Vec<(NIdx, bool)>, top: usize) -> Result<Vec<NIdx>, CheckError> {
    let mut stack = stack;
    let mut sp = top;
    let mut fuel = CLOSURE_FUEL;
    let mut seen: HashMap2<NIdx, bool> = HashMap2::new();
    let mut done: HashMap2<NIdx, bool> = HashMap2::new();
    let mut out: Vec<NIdx> = Vec::new();
    while sp > 0 {
        if fuel == 0 {
            return out_of_fuel();
        }
        fuel -= 1;
        sp -= 1;
        let m: NIdx = stack[sp].0.dup2();
        if stack[sp].1 {
            done.insert(m.dup2(), true);
            out.push(m);
        } else if !seen.contains_key(&m) {
            match files::module_imports(fs, pk, pers, ar, sp_dirs, &m) {
                Err(e) => return Err(e),
                Ok(imps) => {
                    seen.insert(m.dup2(), true);
                    match import_on_path(&imps, &seen, &done) {
                        Some(c) => {
                            let t = text::cat({ const M: [u32; 14] = [105, 109, 112, 111, 114, 116, 32, 99, 121, 99, 108, 101, 58, 32]; crate::kernel::core_types::code_points(&M) }, &view::name_text(pers, ar, &m));
                            let t = text::cat(t, &{ const M: [u32; 9] = [32, 105, 109, 112, 111, 114, 116, 115, 32]; crate::kernel::core_types::code_points(&M) });
                            return Err(core_types::internal(text::cat(t, &view::name_text(pers, ar, c))));
                        }
                        None => sp = walk_expand(&mut stack, sp, &m, &imps, &seen),
                    }
                }
            }
        }
    }
    Ok(out)
}

/// con-leche: ConLeche/Frontend/Olean/Closure.lean:129-131 closureOrder
/// The closure's module order from the roots.
pub fn closure_order<F: OleanFs>(fs: &F, pk: &OleanPins, pers: &PersTier, ar: &mut EStore, sp_dirs: &Vec<Vec<u32>>, roots: &Vec<NIdx>) -> Result<Vec<NIdx>, CheckError> {
    let mut stack: Vec<(NIdx, bool)> = Vec::with_capacity(roots.len());
    let mut sp = 0usize;
    let mut i = roots.len();
    while i > 0 {
        i -= 1;
        sp = walk_push(&mut stack, sp, (roots[i].dup2(), false));
    }
    closure_go(fs, pk, pers, ar, sp_dirs, stack, sp)
}

/// con-leche: ConLeche/Frontend/Olean/Closure.lean:135-138 Loaded
/// A loaded module: its constants at the private level.
pub struct Loaded {
    pub name: NIdx,
    pub constants: Vec<CEntry>,
}

/// con-leche: ConLeche/Frontend/Olean/Closure.lean:140-146 loadModule
/// `d.constants.map CEntry.ofRead`.
pub fn entries_of_read(pk: &OleanPins, pers: &PersTier, ar: &EStore, w: &mut ConstsWork, d: ModDecoded) -> Result<Vec<CEntry>, CheckError> {
    let mut cs = d.constants;
    let mut out: Vec<CEntry> = Vec::with_capacity(cs.len());
    let mut i = 0usize;
    while i < cs.len() {
        let c = core::mem::replace(
            &mut cs[i],
            CEntryF { name: pk.anon.dup2(), level_params: Vec::new(), ty: EIdx::of_word(0), kind: CKindF::Ax(false) },
        );
        match c_entry_of_read(pk, pers, ar, w, c) {
            Err(e) => return Err(e),
            Ok(x) => out.push(x),
        }
        i += 1;
    }
    Ok(out)
}

/// con-leche: ConLeche/Frontend/Olean/Closure.lean:140-146 loadModule
/// **Load one module** for the merge: its private view, what Lean's own import
/// outside the module system and lean4export load.
pub fn load_module<F: OleanFs>(fs: &F, pk: &OleanPins, pers: &PersTier, ar: &mut EStore, w: &mut ConstsWork, sp_dirs: &Vec<Vec<u32>>, m: &NIdx) -> Result<Loaded, CheckError> {
    match files::read_view(fs, pk, pers, ar, sp_dirs, m, &OLeanLevel::Private) {
        Err(e) => Err(e),
        Ok(d) => match entries_of_read(pk, pers, ar, w, d) {
            Err(e) => Err(e),
            Ok(constants) => Ok(Loaded { name: m.dup2(), constants }),
        },
    }
}

/// con-leche: ConLeche/Frontend/Olean/Closure.lean:148-158 loadClosure
/// `order.toList`, loaded in order, up to the first failure.
pub fn load_all<F: OleanFs>(fs: &F, pk: &OleanPins, pers: &PersTier, ar: &mut EStore, sp_dirs: &Vec<Vec<u32>>, order: &Vec<NIdx>) -> Result<Vec<Loaded>, CheckError> {
    let mut w: ConstsWork = consts_work_empty();
    let mut out: Vec<Loaded> = Vec::with_capacity(order.len());
    let mut i = 0usize;
    while i < order.len() {
        match load_module(fs, pk, pers, ar, &mut w, sp_dirs, &order[i]) {
            Err(e) => return Err(e),
            Ok(l) => out.push(l),
        }
        i += 1;
    }
    Ok(out)
}

/// con-leche: ConLeche/Frontend/Olean/Closure.lean:148-158 loadClosure
/// **The closure, loaded**: its modules in Lean's order, decoded (module note on
/// `parMapExcept`).
pub fn load_closure<F: OleanFs>(fs: &F, pk: &OleanPins, pers: &PersTier, ar: &mut EStore, sp_dirs: &Vec<Vec<u32>>, roots: &Vec<NIdx>) -> Result<Vec<Loaded>, CheckError> {
    match closure_order(fs, pk, pers, ar, sp_dirs, roots) {
        Err(e) => Err(e),
        Ok(order) => load_all(fs, pk, pers, ar, sp_dirs, &order),
    }
}
