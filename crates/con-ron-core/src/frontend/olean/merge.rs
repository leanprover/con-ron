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

use crate::arena::handle::{EIdx, NIdx, ETAG_APP, ETAG_CONST, ETAG_FORALL_E};
use crate::arena::store::{EStore, PersTier};
use crate::frontend::olean::closure;
use crate::frontend::olean::closure::{CEntry, Loaded};
use crate::frontend::olean::module;
use crate::frontend::olean::spec::{CKindF, OleanPins};
use crate::frontend::olean::view;
use crate::frontend::text;
use crate::kernel::core_types;
use crate::kernel::core_types::CheckError;
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
pub fn is_prop_body(pers: &PersTier, ar: &EStore, ty: &EIdx) -> EIdx {
    let mut e: EIdx = ty.dup2();
    let mut fuel = closure::CLOSURE_FUEL;
    while fuel > 0 && e.tag() == ETAG_FORALL_E {
        fuel -= 1;
        match ar.view_bind(pers, &e) {
            None => return e,
            Some((_, b)) => e = b,
        }
    }
    e
}

/// con-leche: ConLeche/Frontend/Olean/Merge.lean:21-43 isPropCheap.head
/// The head constant of an application, and its argument count.
pub fn is_prop_head(pers: &PersTier, ar: &EStore, e: &EIdx) -> Option<(NIdx, u64)> {
    let mut x: EIdx = e.dup2();
    let mut k = 0u64;
    let mut fuel = closure::CLOSURE_FUEL;
    while fuel > 0 {
        fuel -= 1;
        let t = x.tag();
        if t == ETAG_APP {
            match ar.view_app(pers, &x) {
                None => return None,
                Some((f, _)) => {
                    x = f;
                    k += 1;
                }
            }
        } else if t == ETAG_CONST {
            return match ar.view_const_name(pers, &x) {
                None => None,
                Some(n) => Some((n, k)),
            };
        } else {
            return None;
        }
    }
    None
}

/// con-leche: ConLeche/Frontend/Olean/Merge.lean:21-43 isPropCheap.drop
/// A telescope's result after `k` binders.
pub fn is_prop_drop(pers: &PersTier, ar: &EStore, e: &EIdx, k: u64) -> Option<EIdx> {
    let mut x: EIdx = e.dup2();
    let mut k = k;
    while k > 0 {
        if x.tag() != ETAG_FORALL_E {
            return None;
        }
        k -= 1;
        match ar.view_bind(pers, &x) {
            None => return None,
            Some((_, b)) => x = b,
        }
    }
    Some(x)
}

/// con-leche: ConLeche/Frontend/Olean/Merge.lean:21-43 isPropCheap
/// Lean's `isPropCheap`: the statement is a telescope over a constant applied to
/// as many arguments as its own type has binders before a `Prop` result.
pub fn is_prop_cheap(pk: &OleanPins, pers: &PersTier, ar: &EStore, mg: &Merged, ty: &EIdx) -> bool {
    let b = is_prop_body(pers, ar, ty);
    match is_prop_head(pers, ar, &b) {
        None => false,
        Some((n, k)) => match mg_get(mg, &n) {
            None => false,
            Some(d) => match is_prop_drop(pers, ar, &d.c.ty, k) {
                None => false,
                Some(r) => match ar.view_sort(pers, &r) {
                    None => false,
                    Some(u) => u.eq2(&pk.zero),
                },
            },
        },
    }
}

/// con-leche: ConLeche/Frontend/Olean/Merge.lean:45-52 subsumes
/// `subsumesInfo`: may `c₁` stand for `c₂`?
pub fn subsumes(pk: &OleanPins, pers: &PersTier, ar: &EStore, mg: &Merged, c1: &CEntry, c2: &CEntry) -> bool {
    if !(c1.c.name.eq2(&c2.c.name) && c1.c.ty.eq2(&c2.c.ty) && module::nidx_list_eq(&c1.c.level_params, &c2.c.level_params)) {
        return false;
    }
    match (&c1.c.kind, &c2.c.kind) {
        (CKindF::Thm(_, a1), CKindF::Thm(_, a2)) => module::nidx_list_eq(a1, a2),
        (CKindF::Thm(_, a1), CKindF::Ax(u2)) => a1.len() == 1 && a1[0].eq2(&c2.c.name) && !*u2,
        (CKindF::Ax(u1), CKindF::Ax(u2)) => *u1 == *u2 && is_prop_cheap(pk, pers, ar, mg, &c1.c.ty),
        _ => false,
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
            if subsumes(pk, pers, ar, mg, c, prev) {
                mg.map.insert(n, (m, i));
                Ok(())
            } else if subsumes(pk, pers, ar, mg, prev, c) {
                Ok(())
            } else {
                let t = text::cat({ const M: [u32; 44] = [116, 119, 111, 32, 109, 111, 100, 117, 108, 101, 115, 32, 115, 116, 111, 114, 101, 32, 100, 105, 102, 102, 101, 114, 101, 110, 116, 32, 99, 111, 110, 115, 116, 97, 110, 116, 115, 32, 110, 97, 109, 101, 100, 32]; crate::kernel::core_types::code_points(&M) }, &view::name_text(pers, ar, &n));
                Err(core_types::invalid(t))
            }
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
