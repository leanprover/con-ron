//! `ConLeche/Frontend/Olean/Merge.lean` — the closure's constants merged (task
//! #142).
//!
//! A name stored by two modules is kept once, by `subsumesInfo`'s rule: the later
//! copy replaces the earlier one when it subsumes it, the earlier stays when it
//! subsumes the later, and otherwise the closure is invalid.
//!
//! Deviation: **the merged map holds a constant's position, not the constant**:
//! `(module, index)` into the loaded modules, which `Merged` owns.  Nothing is
//! copied or moved, and [`mg_get`] is `mg.map[n]?`.  `isPropCheap`'s structural
//! recursions are walks over store views, with fuel.

use crate::arena::env;
use crate::arena::handle::{EIdx, NIdx};
use crate::arena::monad;
use crate::arena::store::{ENodeView, EStore, PersTier};
use crate::frontend::olean::closure;
use crate::frontend::olean::closure::{CEntry, Loaded};
use crate::frontend::olean::module;
use crate::frontend::olean::spec::{CKindF, OleanPins};
use crate::frontend::text;
use crate::kernel::core_types;
use crate::kernel::core_types::CheckError;
use crate::kernel::name;
use crate::ron::hashmap::Dup;
use crate::ron::hashmap::Eq2;
use crate::ron::hashmap2::HashMap2;

/// con-leche: ConLeche/Frontend/Olean/Merge.lean:54-57 Merged
/// The merged constants and the order they were first stored in.
pub struct Merged {
    pub ls: Vec<Loaded>,
    pub map: HashMap2<NIdx, (usize, usize)>,
    pub order: Vec<NIdx>,
}

/// con-leche: ConLeche/Frontend/Olean/Merge.lean:54-57 Merged
/// `mg.map[n]?`.
pub fn mg_get<'a>(mg: &'a Merged, n: &NIdx) -> Option<&'a CEntry> {
    match mg.map.get(n) {
        None => None,
        Some(p) => Some(&mg.ls[p.0].constants[p.1]),
    }
}

/// con-leche: ConLeche/Frontend/Olean/Merge.lean:54-57 Merged
/// `mg.map.contains n`.
pub fn mg_has(mg: &Merged, n: &NIdx) -> bool {
    mg.map.contains_key(n)
}

/// con-leche: ConLeche/Frontend/Olean/Merge.lean:21-43 isPropCheap.body
/// The result of a telescope.
pub fn is_prop_body(pers: &PersTier, ar: &EStore, ty: &EIdx) -> Result<EIdx, CheckError> {
    let mut e: EIdx = ty.dup2();
    let mut fuel = closure::CLOSURE_FUEL;
    while fuel > 0 {
        fuel -= 1;
        match ar.view(pers, &e) {
            None => return monad::fail_dangling_e(),
            Some(ENodeView::ForallE(_, b)) => e = b,
            Some(_) => return Ok(e),
        }
    }
    Ok(e)
}

/// con-leche: ConLeche/Frontend/Olean/Merge.lean:21-43 isPropCheap.head
/// The head constant of an application, and its argument count.
pub fn is_prop_head(pers: &PersTier, ar: &EStore, e: &EIdx) -> Result<Option<(NIdx, u64)>, CheckError> {
    let mut x: EIdx = e.dup2();
    let mut k = 0u64;
    let mut fuel = closure::CLOSURE_FUEL;
    while fuel > 0 {
        fuel -= 1;
        match ar.view(pers, &x) {
            None => return monad::fail_dangling_e(),
            Some(ENodeView::App(f, _)) => {
                x = f;
                k += 1;
            }
            Some(ENodeView::Const(n, _)) => return Ok(Some((n, k))),
            Some(_) => return Ok(None),
        }
    }
    Ok(None)
}

/// con-leche: ConLeche/Frontend/Olean/Merge.lean:21-43 isPropCheap.drop
/// A telescope's result after `k` binders.
pub fn is_prop_drop(pers: &PersTier, ar: &EStore, e: &EIdx, k: u64) -> Result<Option<EIdx>, CheckError> {
    let mut x: EIdx = e.dup2();
    let mut k = k;
    while k > 0 {
        k -= 1;
        match ar.view(pers, &x) {
            None => return monad::fail_dangling_e(),
            Some(ENodeView::ForallE(_, b)) => x = b,
            Some(_) => return Ok(None),
        }
    }
    Ok(Some(x))
}

/// con-leche: ConLeche/Frontend/Olean/Merge.lean:21-43 isPropCheap
/// The end of `isPropCheap`: the head's type after `k` binders is `Prop`.
pub fn is_prop_tail(pk: &OleanPins, pers: &PersTier, ar: &EStore, ty: &EIdx, k: u64) -> Result<bool, CheckError> {
    match is_prop_drop(pers, ar, ty, k) {
        Err(e) => Err(e),
        Ok(None) => Ok(false),
        Ok(Some(x)) => match ar.view(pers, &x) {
            None => monad::fail_dangling_e(),
            Some(ENodeView::Sort(u)) => Ok(u.eq2(&pk.zero)),
            Some(_) => Ok(false),
        },
    }
}

/// con-leche: ConLeche/Frontend/Olean/Merge.lean:21-43 isPropCheap
/// Lean's `isPropCheap`: the statement is a telescope over a constant applied to
/// as many arguments as its own type has binders before a `Prop` result.
pub fn is_prop_cheap(pk: &OleanPins, pers: &PersTier, ar: &EStore, mg: &Merged, ty: &EIdx) -> Result<bool, CheckError> {
    let b = match is_prop_body(pers, ar, ty) {
        Err(e) => return Err(e),
        Ok(b) => b,
    };
    match is_prop_head(pers, ar, &b) {
        Err(e) => Err(e),
        Ok(None) => Ok(false),
        Ok(Some((n, k))) => match mg_get(mg, &n) {
            None => Ok(false),
            Some(d) => is_prop_tail(pk, pers, ar, &d.c.ty, k),
        },
    }
}

/// con-leche: ConLeche/Frontend/Olean/Merge.lean:45-52 subsumes
/// `subsumesInfo`: may `c₁` stand for `c₂`?
pub fn subsumes(pk: &OleanPins, pers: &PersTier, ar: &EStore, mg: &Merged, c1: &CEntry, c2: &CEntry) -> Result<bool, CheckError> {
    if !(c1.c.name.eq2(&c2.c.name) && c1.c.ty.eq2(&c2.c.ty) && module::nidx_list_eq(&c1.c.level_params, &c2.c.level_params)) {
        return Ok(false);
    }
    match (&c1.c.kind, &c2.c.kind) {
        (CKindF::Thm(_, a1), CKindF::Thm(_, a2)) => Ok(module::nidx_list_eq(a1, a2)),
        (CKindF::Thm(_, a1), CKindF::Ax(u2)) => Ok(a1.len() == 1 && a1[0].eq2(&c2.c.name) && !*u2),
        (CKindF::Ax(u1), CKindF::Ax(u2)) => {
            if *u1 == *u2 {
                is_prop_cheap(pk, pers, ar, mg, &c1.c.ty)
            } else {
                Ok(false)
            }
        }
        _ => Ok(false),
    }
}

/// con-leche: ConLeche/Frontend/Olean/Merge.lean:59-70 mergeEntry
/// **Merge one constant**, the `i`-th of module `m`.
pub fn merge_entry(pk: &OleanPins, pers: &PersTier, ar: &EStore, mg: &mut Merged, m: usize, i: usize) -> Result<(), CheckError> {
    let n: NIdx = mg.ls[m].constants[i].c.name.dup2();
    match mg_get(mg, &n) {
        None => {
            mg.map.insert(n.dup2(), (m, i));
            mg.order.push(n);
            Ok(())
        }
        Some(prev) => {
            let c = &mg.ls[m].constants[i];
            let later = match subsumes(pk, pers, ar, mg, c, prev) {
                Err(e) => return Err(e),
                Ok(b) => b,
            };
            if later {
                mg.map.insert(n, (m, i));
                Ok(())
            } else {
                match subsumes(pk, pers, ar, mg, prev, c) {
                    Err(e) => Err(e),
                    Ok(true) => Ok(()),
                    Ok(false) => merge_conflict(pers, ar, &n),
                }
            }
        }
    }
}

/// con-leche: ConLeche/Frontend/Olean/Merge.lean:59-70 mergeEntry
/// Two modules store different constants of one name.
pub fn merge_conflict(pers: &PersTier, ar: &EStore, n: &NIdx) -> Result<(), CheckError> {
    match env::read_name(pers, ar, n) {
        Err(e) => Err(e),
        Ok(x) => {
            let t = text::cat({ const M: [u32; 44] = [116, 119, 111, 32, 109, 111, 100, 117, 108, 101, 115, 32, 115, 116, 111, 114, 101, 32, 100, 105, 102, 102, 101, 114, 101, 110, 116, 32, 99, 111, 110, 115, 116, 97, 110, 116, 115, 32, 110, 97, 109, 101, 100, 32]; crate::kernel::core_types::code_points(&M) }, &name::render(&x));
            Err(core_types::invalid(t))
        }
    }
}

/// con-leche: ConLeche/Frontend/Olean/Merge.lean:72-73 mergeAll
/// `l.constants.foldlM mergeEntry mg`, the constants of module `m`.
pub fn merge_module(pk: &OleanPins, pers: &PersTier, ar: &EStore, mg: &mut Merged, m: usize) -> Result<(), CheckError> {
    let n = mg.ls[m].constants.len();
    let mut i = 0usize;
    while i < n {
        match merge_entry(pk, pers, ar, mg, m, i) {
            Err(e) => return Err(e),
            Ok(()) => {}
        }
        i += 1;
    }
    Ok(())
}

/// con-leche: ConLeche/Frontend/Olean/Merge.lean:72-73 mergeAll
/// The closure's constants merged.
pub fn merge_all(pk: &OleanPins, pers: &PersTier, ar: &EStore, ls: Vec<Loaded>) -> Result<Merged, CheckError> {
    let n = ls.len();
    let mut mg = Merged { ls, map: HashMap2::new(), order: Vec::new() };
    let mut m = 0usize;
    while m < n {
        match merge_module(pk, pers, ar, &mut mg, m) {
            Err(e) => return Err(e),
            Ok(()) => {}
        }
        m += 1;
    }
    Ok(mg)
}
