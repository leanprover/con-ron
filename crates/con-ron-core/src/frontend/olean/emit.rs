//! `ConLeche/Frontend/Olean/Emit.lean` — the merged constants in lean4export's
//! order (task #142).
//!
//! lean4export's `dumpConstant` walk from the given roots: every constant is
//! emitted after the constants its type and value mention, an inductive block as
//! one record, the quotient package as its four records after `Eq`, unsafe and
//! partial constants left out.  Its output is the record stream in the stream
//! reader's own syntax (`DeclRec`).
//!
//! ## Deviations
//!
//! * **A `Work` item names constants instead of holding them**: they are read out
//!   of the merge when emitted.  The merge does not change during the walk.
//! * **`emitLoop` carries fuel**, not upstream's measure (`closure`'s module note);
//!   the theorems that prove its termination upstream are not ported.  The stack is
//!   a `Vec` and its top.
//! * `Emit.unvisited` and the termination lemmas are proof apparatus (§3.1), listed
//!   in `scripts/provenance-skip.txt`.

use crate::arena::handle::{EIdx, NIdx};
use crate::arena::store::{EStore, PersTier};
use crate::frontend::olean::closure;
use crate::frontend::olean::lazy;
use crate::frontend::olean::lazy::CEntry;
use crate::frontend::olean::merge;
use crate::frontend::olean::merge::Merged;
use crate::frontend::olean::module;
use crate::frontend::olean::reads;
use crate::frontend::olean::spec::{CKindF, OleanPins};
use crate::frontend::olean::view;
use crate::frontend::scan_types::{CVRec, DeclRec, IndCtorRec, IndRecRec, IndTypeRec, RuleRec};
use crate::frontend::text;
use crate::kernel::core_types;
use crate::kernel::core_types::CheckError;
use crate::kernel::expr;
use crate::ron::hashmap::Dup;
use crate::ron::hashmap::Eq2;
use crate::ron::hashmap2::HashMap2;

/// con-leche: ConLeche/Frontend/Olean/Emit.lean:23-28 Work
/// One step of the emission walk.
pub enum Work {
    Visit(NIdx),
    One(NIdx),
    Quot(Vec<NIdx>),
    Block(Vec<NIdx>, Vec<NIdx>, Vec<NIdx>),
}

/// con-leche: ConLeche/Frontend/Olean/Emit.lean:30-36 Emit
/// The emitter's output: the record stream in the stream reader's syntax.
pub struct Emit {
    pub visited: HashMap2<NIdx, bool>,
    pub names: Vec<NIdx>,
    pub exprs: Vec<EIdx>,
    pub out: Vec<DeclRec>,
}

/// con-leche: ConLeche/Frontend/Olean/Emit.lean:42-45 Emit.name
pub fn emit_name(st: &mut Emit, n: &NIdx) -> u64 {
    let i = st.names.len() as u64;
    st.names.push(n.dup2());
    i
}

/// con-leche: ConLeche/Frontend/Olean/Emit.lean:47-50 Emit.expr
pub fn emit_expr(st: &mut Emit, e: &EIdx) -> u64 {
    let i = st.exprs.len() as u64;
    st.exprs.push(e.dup2());
    i
}

/// con-leche: ConLeche/Frontend/Olean/Emit.lean:56-58 Emit.mark
pub fn emit_mark(st: &mut Emit, n: &NIdx) {
    st.visited.insert(n.dup2(), true);
}

/// con-leche: ConLeche/Frontend/Olean/Emit.lean:67-70 Emit.names'
pub fn emit_names(st: &mut Emit, ns: &Vec<NIdx>) -> Vec<u64> {
    let mut acc: Vec<u64> = Vec::with_capacity(ns.len());
    let mut i = 0usize;
    while i < ns.len() {
        acc.push(emit_name(st, &ns[i]));
        i += 1;
    }
    acc
}

/// con-leche: ConLeche/Frontend/Olean/Emit.lean:60-65 Emit.cv
pub fn emit_cv(st: &mut Emit, c: &CEntry) -> CVRec {
    let n = emit_name(st, &c.c.name);
    let lps = emit_names(st, &c.c.level_params);
    let t = emit_expr(st, &c.c.ty);
    CVRec { name: n, level_params: lps, ty: t }
}

/// con-leche: ConLeche/Frontend/Olean/Emit.lean:52-54 Emit.push
/// con-leche: ConLeche/Frontend/Olean/Emit.lean:72-84 Emit.one
/// **One constant's record.**
pub fn emit_one(st: &mut Emit, c: &CEntry) {
    let cv = emit_cv(st, c);
    match &c.c.kind {
        CKindF::Ax(u) => st.out.push(DeclRec::Ax(cv, *u)),
        CKindF::Defn(v, h, s) => {
            let i = emit_expr(st, v);
            st.out.push(DeclRec::Defn(cv, i, crate::frontend::olean::spec::hints_dup(h), expr::str_copy(s)));
        }
        CKindF::Thm(v, _) => {
            let i = emit_expr(st, v);
            st.out.push(DeclRec::Thm(cv, i));
        }
        CKindF::Opaq(v, u) => {
            let i = emit_expr(st, v);
            st.out.push(DeclRec::Opaq(cv, i, *u));
        }
        CKindF::Quot(k) => st.out.push(DeclRec::Quot(cv, expr::str_copy(k))),
        _ => {}
    }
}

/// con-leche: ConLeche/Frontend/Olean/Emit.lean:86-95 Emit.tyStep
/// One inductive type of a block's record.
pub fn emit_ty_step(st: &mut Emit, acc: &mut Vec<IndTypeRec>, c: &CEntry) {
    match &c.c.kind {
        CKindF::Induct(np, ni, _, cs, nn, ir, iu, irf) => {
            let cv = emit_cv(st, c);
            let ctors = emit_names(st, cs);
            acc.push(IndTypeRec {
                cv,
                ctors,
                is_rec: *ir,
                is_reflexive: *irf,
                is_unsafe: *iu,
                num_indices: *ni,
                num_nested: *nn,
                num_params: *np,
            });
        }
        _ => {}
    }
}

/// con-leche: ConLeche/Frontend/Olean/Emit.lean:97-106 Emit.ctorStep
/// One constructor of a block's record.
pub fn emit_ctor_step(st: &mut Emit, acc: &mut Vec<IndCtorRec>, c: &CEntry) {
    match &c.c.kind {
        CKindF::Ctor(ind, cidx, np, nf, iu) => {
            let cv = emit_cv(st, c);
            let ii = emit_name(st, ind);
            acc.push(IndCtorRec {
                cv,
                is_unsafe: *iu,
                num_fields: *nf,
                num_params: *np,
                cidx: Some(*cidx),
                induct: Some(ii),
            });
        }
        _ => {}
    }
}

/// con-leche: ConLeche/Frontend/Olean/Emit.lean:108-114 Emit.ruleStep
/// One rule of a recursor's record.
pub fn emit_rule_step(st: &mut Emit, acc: &mut Vec<RuleRec>, r: &(NIdx, u64, EIdx)) {
    let ci = emit_name(st, &r.0);
    let ri = emit_expr(st, &r.2);
    acc.push(RuleRec { ctor: ci, nfields: r.1, rhs: ri });
}

/// con-leche: ConLeche/Frontend/Olean/Emit.lean:116-125 Emit.recStep
/// One recursor of a block's record.
pub fn emit_rec_step(st: &mut Emit, acc: &mut Vec<IndRecRec>, c: &CEntry) {
    match &c.c.kind {
        CKindF::Recur(_, np, ni, nmo, nmi, rules, k, iu) => {
            let cv = emit_cv(st, c);
            let mut rr: Vec<RuleRec> = Vec::with_capacity(rules.len());
            let mut i = 0usize;
            while i < rules.len() {
                emit_rule_step(st, &mut rr, &rules[i]);
                i += 1;
            }
            acc.push(IndRecRec {
                cv,
                is_unsafe: *iu,
                k: *k,
                num_indices: *ni,
                num_minors: *nmi,
                num_motives: *nmo,
                num_params: *np,
                rules: rr,
            });
        }
        _ => {}
    }
}

/// con-leche: ConLeche/Frontend/Olean/Emit.lean:86-95 Emit.tyStep
/// The step at a constant of the merge, by name.
pub fn ty_named(st: &mut Emit, mg: &Merged, acc: &mut Vec<IndTypeRec>, n: &NIdx) {
    match merge::mg_get(mg, n) {
        Some(c) => emit_ty_step(st, acc, c),
        None => {}
    }
}

/// con-leche: ConLeche/Frontend/Olean/Emit.lean:97-106 Emit.ctorStep
/// The step at a constant of the merge, by name.
pub fn ctor_named(st: &mut Emit, mg: &Merged, acc: &mut Vec<IndCtorRec>, n: &NIdx) {
    match merge::mg_get(mg, n) {
        Some(c) => emit_ctor_step(st, acc, c),
        None => {}
    }
}

/// con-leche: ConLeche/Frontend/Olean/Emit.lean:116-125 Emit.recStep
/// The step at a constant of the merge, by name.
pub fn rec_named(st: &mut Emit, mg: &Merged, acc: &mut Vec<IndRecRec>, n: &NIdx) {
    match merge::mg_get(mg, n) {
        Some(c) => emit_rec_step(st, acc, c),
        None => {}
    }
}

/// con-leche: ConLeche/Frontend/Olean/Emit.lean:72-84 Emit.one
/// One constant's record, by name.
pub fn one_named(st: &mut Emit, mg: &Merged, n: &NIdx) {
    match merge::mg_get(mg, n) {
        Some(c) => emit_one(st, c),
        None => {}
    }
}

/// con-leche: ConLeche/Frontend/Olean/Emit.lean:127-132 Emit.block
/// **An inductive block's record**: lean4export's `inductive` object.  The names
/// `tys`, `ctors`, `recs` were found in the merge by `blockTys` and friends.
pub fn emit_block(st: &mut Emit, mg: &Merged, tys: &Vec<NIdx>, ctors: &Vec<NIdx>, recs: &Vec<NIdx>) {
    let mut ts: Vec<IndTypeRec> = Vec::with_capacity(tys.len());
    let mut i = 0usize;
    while i < tys.len() {
        ty_named(st, mg, &mut ts, &tys[i]);
        i += 1;
    }
    let mut cts: Vec<IndCtorRec> = Vec::with_capacity(ctors.len());
    let mut j = 0usize;
    while j < ctors.len() {
        ctor_named(st, mg, &mut cts, &ctors[j]);
        j += 1;
    }
    let mut rs: Vec<IndRecRec> = Vec::with_capacity(recs.len());
    let mut k = 0usize;
    while k < recs.len() {
        rec_named(st, mg, &mut rs, &recs[k]);
        k += 1;
    }
    st.out.push(DeclRec::Ind(ts, cts, rs));
}

/// con-leche: ConLeche/Frontend/Olean/Emit.lean:265-266 blockTys
/// The constants of an inductive block's members: those of `all` stored.
pub fn block_tys(mg: &Merged, all: &Vec<NIdx>) -> Vec<NIdx> {
    let mut out: Vec<NIdx> = Vec::with_capacity(all.len());
    let mut i = 0usize;
    while i < all.len() {
        if merge::mg_has(mg, &all[i]) {
            out.push(all[i].dup2());
        }
        i += 1;
    }
    out
}

/// con-leche: ConLeche/Frontend/Olean/Emit.lean:268-272 blockCtors
/// The stored constructors of one member, onto `out`.
pub fn block_ctors_of(mg: &Merged, n: &NIdx, out: &mut Vec<NIdx>) {
    match merge::mg_get(mg, n) {
        Some(t) => match &t.c.kind {
            CKindF::Induct(_, _, _, cs, _, _, _, _) => push_stored(mg, cs, out),
            _ => {}
        },
        None => {}
    }
}

/// con-leche: ConLeche/Frontend/Olean/Emit.lean:268-272 blockCtors
/// `cs.filterMap (mg.map[·]?)`, as names, onto `out`.
pub fn push_stored(mg: &Merged, cs: &Vec<NIdx>, out: &mut Vec<NIdx>) {
    let mut j = 0usize;
    while j < cs.len() {
        if merge::mg_has(mg, &cs[j]) {
            out.push(cs[j].dup2());
        }
        j += 1;
    }
}

/// con-leche: ConLeche/Frontend/Olean/Emit.lean:268-272 blockCtors
/// The constructors of a block's members.
pub fn block_ctors(mg: &Merged, tys: &Vec<NIdx>) -> Vec<NIdx> {
    let mut out: Vec<NIdx> = Vec::new();
    let mut i = 0usize;
    while i < tys.len() {
        block_ctors_of(mg, &tys[i], &mut out);
        i += 1;
    }
    out
}

/// con-leche: ConLeche/Frontend/Olean/Emit.lean:274-276 blockRecs
/// The recursors of a block.
pub fn block_recs(mg: &Merged, rec_map: &HashMap2<NIdx, Vec<NIdx>>, n: &NIdx) -> Vec<NIdx> {
    match rec_map.get(n) {
        None => Vec::new(),
        Some(a) => block_tys(mg, a),
    }
}

/// con-leche: ConLeche/Frontend/Olean/Emit.lean:278-280 quotNames
/// The quotient package's names.
pub fn quot_names(pk: &OleanPins) -> Vec<NIdx> {
    let mut v: Vec<NIdx> = Vec::with_capacity(4);
    v.push(pk.n_quot.dup2());
    v.push(pk.n_quot_mk.dup2());
    v.push(pk.n_quot_lift.dup2());
    v.push(pk.n_quot_ind.dup2());
    v
}

/// con-leche: ConLeche/Frontend/Olean/Emit.lean:282-283 quotConstants
/// The quotient package's constants.
pub fn quot_constants(pk: &OleanPins, mg: &Merged) -> Vec<NIdx> {
    block_tys(mg, &quot_names(pk))
}

/// con-leche: ConLeche/Frontend/Olean/Emit.lean:294-338 emitLoop
/// Push onto the walk's stack with its top at `sp`; the new top.
pub fn work_push(stack: &mut Vec<Work>, sp: usize, x: Work) -> usize {
    if sp < stack.len() {
        stack[sp] = x;
    } else {
        stack.push(x);
    }
    sp + 1
}

/// con-leche: ConLeche/Frontend/Olean/Emit.lean:285-286 Work.usesOf
/// Visits of what one constant mentions, onto the stack (the last visit first, so
/// that the first is on top); the new top.
pub fn push_uses(stack: &mut Vec<Work>, sp: usize, c: &CEntry) -> usize {
    let mut s = sp;
    let mut i = c.uses.len();
    while i > 0 {
        i -= 1;
        s = work_push(stack, s, Work::Visit(c.uses[i].dup2()));
    }
    s
}

/// con-leche: ConLeche/Frontend/Olean/Emit.lean:285-286 Work.usesOf
/// Visits of what some constants mention, the first constant's on top.
pub fn push_uses_of(stack: &mut Vec<Work>, sp: usize, mg: &Merged, ns: &Vec<NIdx>) -> usize {
    let mut s = sp;
    let mut i = ns.len();
    while i > 0 {
        i -= 1;
        s = push_uses_named(stack, s, mg, &ns[i]);
    }
    s
}

/// con-leche: ConLeche/Frontend/Olean/Emit.lean:285-286 Work.usesOf
/// Visits of what one constant mentions, by name.
pub fn push_uses_named(stack: &mut Vec<Work>, sp: usize, mg: &Merged, n: &NIdx) -> usize {
    match merge::mg_get(mg, n) {
        Some(c) => push_uses(stack, sp, c),
        None => sp,
    }
}

/// con-leche: ConLeche/Frontend/Olean/Emit.lean:288-289 Work.visits
/// Visits of some names, the first on top.
pub fn push_visits(stack: &mut Vec<Work>, sp: usize, ns: &Vec<NIdx>) -> usize {
    let mut s = sp;
    let mut i = ns.len();
    while i > 0 {
        i -= 1;
        s = work_push(stack, s, Work::Visit(ns[i].dup2()));
    }
    s
}

/// con-leche: ConLeche/Frontend/Olean/Emit.lean:291-292 Emit.ones
/// Some constants' records.
pub fn emit_ones(st: &mut Emit, mg: &Merged, cs: &Vec<NIdx>) {
    let mut i = 0usize;
    while i < cs.len() {
        one_named(st, mg, &cs[i]);
        i += 1;
    }
}

/// con-leche: ConLeche/Frontend/Olean/Emit.lean:294-338 emitLoop
/// `(tys ++ ctors ++ recs).foldl (fun st x => st.mark x.name) st`, one list.
pub fn mark_all(st: &mut Emit, ns: &Vec<NIdx>) {
    let mut i = 0usize;
    while i < ns.len() {
        emit_mark(st, &ns[i]);
        i += 1;
    }
}

/// con-leche: ConLeche/Frontend/Olean/Emit.lean:294-338 emitLoop
/// A `visit` of a name stored and not filtered out: what it pushes; the new top.
pub fn visit_step(pk: &OleanPins, mg: &Merged, rec_map: &HashMap2<NIdx, Vec<NIdx>>, stack: &mut Vec<Work>, sp: usize, st: &mut Emit, n: &NIdx, c: &CEntry) -> usize {
    emit_mark(st, n);
    match &c.c.kind {
        CKindF::Quot(_) => {
            let qs = quot_constants(pk, mg);
            mark_all(st, &qs);
            let s = work_push(stack, sp, Work::Quot(qs));
            work_push(stack, s, Work::Visit(pk.n_eq.dup2()))
        }
        CKindF::Ctor(ind, _, _, _, _) => work_push(stack, sp, Work::Visit(ind.dup2())),
        CKindF::Recur(all, _, _, _, _, _, _, _) => push_visits(stack, sp, all),
        CKindF::Induct(_, _, all, _, _, _, _, _) => {
            let tys = block_tys(mg, all);
            let ctors = block_ctors(mg, &tys);
            let recs = block_recs(mg, rec_map, n);
            mark_all(st, &tys);
            mark_all(st, &ctors);
            mark_all(st, &recs);
            push_uses_block(stack, sp, mg, tys, ctors, recs)
        }
        _ => {
            let s = work_push(stack, sp, Work::One(n.dup2()));
            push_uses(stack, s, c)
        }
    }
}

/// con-leche: ConLeche/Frontend/Olean/Emit.lean:294-338 emitLoop
/// `Work.usesOf (tys ++ ctors ++ recs) ++ Work.block tys ctors recs :: rest`: the
/// block item, then the visits above it, the types' on top.
pub fn push_uses_block(stack: &mut Vec<Work>, sp: usize, mg: &Merged, tys: Vec<NIdx>, ctors: Vec<NIdx>, recs: Vec<NIdx>) -> usize {
    let t2 = crate::arena::env::nidx_vec_dup(&tys);
    let c2 = crate::arena::env::nidx_vec_dup(&ctors);
    let r2 = crate::arena::env::nidx_vec_dup(&recs);
    let s = work_push(stack, sp, Work::Block(tys, ctors, recs));
    let s = push_uses_of(stack, s, mg, &r2);
    let s = push_uses_of(stack, s, mg, &c2);
    push_uses_of(stack, s, mg, &t2)
}

/// con-leche: ConLeche/Frontend/Olean/Emit.lean:294-338 emitLoop
/// A `visit n`: nothing if it is visited, not stored or filtered out; the new top.
pub fn visit_named(pk: &OleanPins, mg: &Merged, rec_map: &HashMap2<NIdx, Vec<NIdx>>, stack: &mut Vec<Work>, sp: usize, st: &mut Emit, n: &NIdx) -> usize {
    if st.visited.contains_key(n) {
        sp
    } else {
        match merge::mg_get(mg, n) {
            None => sp,
            Some(c) => {
                if lazy::c_entry_skipped(c) {
                    sp
                } else {
                    visit_step(pk, mg, rec_map, stack, sp, st, n, c)
                }
            }
        }
    }
}

/// con-leche: ConLeche/Frontend/Olean/Emit.lean:294-338 emitLoop
/// One popped item; the new top.
pub fn work_step(pk: &OleanPins, mg: &Merged, rec_map: &HashMap2<NIdx, Vec<NIdx>>, stack: &mut Vec<Work>, sp: usize, st: &mut Emit, w: Work) -> usize {
    match w {
        Work::One(n) => {
            one_named(st, mg, &n);
            sp
        }
        Work::Quot(cs) => {
            emit_ones(st, mg, &cs);
            sp
        }
        Work::Block(ts, cs, rs) => {
            emit_block(st, mg, &ts, &cs, &rs);
            sp
        }
        Work::Visit(n) => visit_named(pk, mg, rec_map, stack, sp, st, &n),
    }
}

/// con-leche: ConLeche/Frontend/Olean/Emit.lean:294-338 emitLoop
/// **The emission walk** (lean4export's `dumpConstant`, iterative): `visit n` emits
/// `n`'s record after its dependencies.
pub fn emit_loop(pk: &OleanPins, mg: &Merged, rec_map: &HashMap2<NIdx, Vec<NIdx>>, stack: &mut Vec<Work>, top: usize, st: &mut Emit) -> Result<(), CheckError> {
    let mut sp = top;
    let mut fuel = closure::CLOSURE_FUEL;
    while sp > 0 {
        if fuel == 0 {
            return closure::out_of_fuel();
        }
        fuel -= 1;
        sp -= 1;
        let w = core::mem::replace(&mut stack[sp], Work::Visit(pk.anon.dup2()));
        sp = work_step(pk, mg, rec_map, stack, sp, st, w);
    }
    Ok(())
}

/// con-leche: ConLeche/Frontend/Olean/Emit.lean:340-345 recMapAdd
/// A recursor under one member of its block.
pub fn rec_map_add(m: &mut HashMap2<NIdx, Vec<NIdx>>, n: &NIdx, i: &NIdx) {
    match m.remove(i) {
        None => {
            let mut a: Vec<NIdx> = Vec::with_capacity(1);
            a.push(n.dup2());
            m.insert(i.dup2(), a);
        }
        Some(a) => {
            let mut a = a;
            if !crate::arena::env::nidx_vec_contains(&a, n) {
                a.push(n.dup2());
            }
            m.insert(i.dup2(), a);
        }
    }
}

/// con-leche: ConLeche/Frontend/Olean/Emit.lean:347-352 recMapStep
/// `all.foldl (recMapAdd n) m`.
pub fn rec_map_all(m: &mut HashMap2<NIdx, Vec<NIdx>>, n: &NIdx, all: &Vec<NIdx>) {
    let mut i = 0usize;
    while i < all.len() {
        rec_map_add(m, n, &all[i]);
        i += 1;
    }
}

/// con-leche: ConLeche/Frontend/Olean/Emit.lean:347-352 recMapStep
/// A constant's name under each member of its block, if it is a recursor.
pub fn rec_map_step(mg: &Merged, m: &mut HashMap2<NIdx, Vec<NIdx>>, n: &NIdx) {
    match merge::mg_get(mg, n) {
        Some(c) => match &c.c.kind {
            CKindF::Recur(all, _, _, _, _, _, _, _) => rec_map_all(m, n, all),
            _ => {}
        },
        None => {}
    }
}

/// con-leche: ConLeche/Frontend/Olean/Emit.lean:354-355 recMapOf
/// The recursors of every member of a block.
pub fn rec_map_of(mg: &Merged) -> HashMap2<NIdx, Vec<NIdx>> {
    let mut m: HashMap2<NIdx, Vec<NIdx>> = HashMap2::new();
    let mut i = 0usize;
    while i < mg.order.len() {
        rec_map_step(mg, &mut m, &mg.order[i]);
        i += 1;
    }
    m
}

/// con-leche: ConLeche/Frontend/Olean/Emit.lean:357-359 emitAll
/// **The record stream of the merged closure**, from the given constants.
pub fn emit_all(pk: &OleanPins, mg: &Merged, roots: &Vec<NIdx>) -> Result<Emit, CheckError> {
    let rec_map = rec_map_of(mg);
    let mut st = Emit { visited: HashMap2::new(), names: Vec::new(), exprs: Vec::new(), out: Vec::new() };
    let mut stack: Vec<Work> = Vec::with_capacity(roots.len());
    let top = push_visits(&mut stack, 0, roots);
    match emit_loop(pk, mg, &rec_map, &mut stack, top, &mut st) {
        Err(e) => Err(e),
        Ok(()) => Ok(st),
    }
}

/// con-leche: ConLeche/Frontend/Olean/Emit.lean:363-376 blockMemberOk
/// The `the inductive data of {n}: …` of `blockStep` and its two helpers.
pub fn block_bad(pers: &PersTier, ar: &EStore, n: &NIdx, what: Vec<u32>) -> CheckError {
    let t = text::cat({ const M: [u32; 22] = [116, 104, 101, 32, 105, 110, 100, 117, 99, 116, 105, 118, 101, 32, 100, 97, 116, 97, 32, 111, 102, 32]; crate::kernel::core_types::code_points(&M) }, &view::name_text(pers, ar, n));
    let t = text::cat(t, &{ const M: [u32; 2] = [58, 32]; crate::kernel::core_types::code_points(&M) });
    core_types::internal(text::cat(t, &what))
}

/// con-leche: ConLeche/Frontend/Olean/Emit.lean:363-376 blockMemberOk
/// A block member `x` of the inductive type `n`, whose block is `all`.
pub fn block_member_ok(pers: &PersTier, ar: &EStore, mg: &Merged, n: &NIdx, all: &Vec<NIdx>, sk: bool, x: &NIdx) -> Result<(), CheckError> {
    let pre = text::cat({ const M: [u32; 17] = [105, 116, 115, 32, 98, 108, 111, 99, 107, 32, 109, 101, 109, 98, 101, 114, 32]; crate::kernel::core_types::code_points(&M) }, &view::name_text(pers, ar, x));
    match merge::mg_get(mg, x) {
        None => Err(block_bad(pers, ar, n, text::cat(pre, &{ const M: [u32; 14] = [32, 105, 115, 32, 110, 111, 116, 32, 115, 116, 111, 114, 101, 100]; crate::kernel::core_types::code_points(&M) }))),
        Some(m) => match &m.c.kind {
            CKindF::Induct(_, _, all2, _, _, _, _, _) => {
                if module::nidx_list_eq(all2, all) {
                    if lazy::c_entry_skipped(m) == sk {
                        Ok(())
                    } else {
                        Err(block_bad(pers, ar, n, text::cat(pre, &{ const M: [u32; 40] = [32, 105, 115, 32, 115, 97, 102, 101, 32, 111, 114, 32, 117, 110, 115, 97, 102, 101, 32, 119, 104, 101, 114, 101, 32, 116, 104, 101, 32, 116, 121, 112, 101, 32, 105, 115, 32, 110, 111, 116]; crate::kernel::core_types::code_points(&M) })))
                    }
                } else {
                    Err(block_bad(pers, ar, n, text::cat(pre, &{ const M: [u32; 20] = [32, 110, 97, 109, 101, 115, 32, 97, 110, 111, 116, 104, 101, 114, 32, 98, 108, 111, 99, 107]; crate::kernel::core_types::code_points(&M) })))
                }
            }
            _ => Err(block_bad(pers, ar, n, text::cat(pre, &{ const M: [u32; 25] = [32, 105, 115, 32, 110, 111, 116, 32, 97, 110, 32, 105, 110, 100, 117, 99, 116, 105, 118, 101, 32, 116, 121, 112, 101]; crate::kernel::core_types::code_points(&M) }))),
        },
    }
}

/// con-leche: ConLeche/Frontend/Olean/Emit.lean:378-390 blockCtorOk
/// A listed constructor `x` of the inductive type `n`.
pub fn block_ctor_ok(pers: &PersTier, ar: &EStore, mg: &Merged, n: &NIdx, sk: bool, x: &NIdx) -> Result<(), CheckError> {
    let pre = text::cat({ const M: [u32; 16] = [105, 116, 115, 32, 99, 111, 110, 115, 116, 114, 117, 99, 116, 111, 114, 32]; crate::kernel::core_types::code_points(&M) }, &view::name_text(pers, ar, x));
    match merge::mg_get(mg, x) {
        None => Err(block_bad(pers, ar, n, text::cat(pre, &{ const M: [u32; 14] = [32, 105, 115, 32, 110, 111, 116, 32, 115, 116, 111, 114, 101, 100]; crate::kernel::core_types::code_points(&M) }))),
        Some(m) => match &m.c.kind {
            CKindF::Ctor(ind, _, _, _, _) => {
                if ind.eq2(n) {
                    if lazy::c_entry_skipped(m) == sk {
                        Ok(())
                    } else {
                        Err(block_bad(pers, ar, n, text::cat(pre, &{ const M: [u32; 40] = [32, 105, 115, 32, 115, 97, 102, 101, 32, 111, 114, 32, 117, 110, 115, 97, 102, 101, 32, 119, 104, 101, 114, 101, 32, 116, 104, 101, 32, 116, 121, 112, 101, 32, 105, 115, 32, 110, 111, 116]; crate::kernel::core_types::code_points(&M) })))
                    }
                } else {
                    Err(block_bad(pers, ar, n, text::cat(pre, &{ const M: [u32; 19] = [32, 110, 97, 109, 101, 115, 32, 97, 110, 111, 116, 104, 101, 114, 32, 116, 121, 112, 101]; crate::kernel::core_types::code_points(&M) })))
                }
            }
            _ => Err(block_bad(pers, ar, n, text::cat(pre, &{ const M: [u32; 21] = [32, 105, 115, 32, 110, 111, 116, 32, 97, 32, 99, 111, 110, 115, 116, 114, 117, 99, 116, 111, 114]; crate::kernel::core_types::code_points(&M) }))),
        },
    }
}

/// con-leche: ConLeche/Frontend/Olean/Emit.lean:392-438 blockStep
/// `all.forM (blockMemberOk mg n all c.skipped)`.
pub fn block_members_ok(pers: &PersTier, ar: &EStore, mg: &Merged, n: &NIdx, all: &Vec<NIdx>, sk: bool) -> Result<(), CheckError> {
    let mut i = 0usize;
    while i < all.len() {
        match block_member_ok(pers, ar, mg, n, all, sk, &all[i]) {
            Err(e) => return Err(e),
            Ok(()) => {}
        }
        i += 1;
    }
    Ok(())
}

/// con-leche: ConLeche/Frontend/Olean/Emit.lean:392-438 blockStep
/// `cs.forM (blockCtorOk mg n c.skipped)`.
pub fn block_ctors_ok(pers: &PersTier, ar: &EStore, mg: &Merged, n: &NIdx, cs: &Vec<NIdx>, sk: bool) -> Result<(), CheckError> {
    let mut j = 0usize;
    while j < cs.len() {
        match block_ctor_ok(pers, ar, mg, n, sk, &cs[j]) {
            Err(e) => return Err(e),
            Ok(()) => {}
        }
        j += 1;
    }
    Ok(())
}

/// con-leche: ConLeche/Frontend/Olean/Emit.lean:392-438 blockStep
/// The inductive-type arm of `blockStep`.
pub fn block_step_induct(pers: &PersTier, ar: &EStore, mg: &Merged, n: &NIdx, all: &Vec<NIdx>, cs: &Vec<NIdx>, sk: bool) -> Result<(), CheckError> {
    if !crate::arena::env::nidx_vec_contains(all, n) {
        return Err(block_bad(pers, ar, n, { const M: [u32; 26] = [105, 116, 115, 32, 98, 108, 111, 99, 107, 32, 100, 111, 101, 115, 32, 110, 111, 116, 32, 108, 105, 115, 116, 32, 105, 116]; crate::kernel::core_types::code_points(&M) }));
    }
    match block_members_ok(pers, ar, mg, n, all, sk) {
        Err(e) => Err(e),
        Ok(()) => block_ctors_ok(pers, ar, mg, n, cs, sk),
    }
}

/// con-leche: ConLeche/Frontend/Olean/Emit.lean:392-438 blockStep
/// The constructor arm of `blockStep`.
pub fn block_step_ctor(pers: &PersTier, ar: &EStore, mg: &Merged, n: &NIdx, ind: &NIdx) -> Result<(), CheckError> {
    let pre = text::cat({ const M: [u32; 9] = [105, 116, 115, 32, 116, 121, 112, 101, 32]; crate::kernel::core_types::code_points(&M) }, &view::name_text(pers, ar, ind));
    match merge::mg_get(mg, ind) {
        None => Err(block_bad(pers, ar, n, text::cat(pre, &{ const M: [u32; 14] = [32, 105, 115, 32, 110, 111, 116, 32, 115, 116, 111, 114, 101, 100]; crate::kernel::core_types::code_points(&M) }))),
        Some(t) => match &t.c.kind {
            CKindF::Induct(_, _, _, cs, _, _, _, _) => {
                if crate::arena::env::nidx_vec_contains(cs, n) {
                    Ok(())
                } else {
                    Err(block_bad(pers, ar, n, text::cat(pre, &{ const M: [u32; 17] = [32, 100, 111, 101, 115, 32, 110, 111, 116, 32, 108, 105, 115, 116, 32, 105, 116]; crate::kernel::core_types::code_points(&M) })))
                }
            }
            _ => Err(block_bad(pers, ar, n, text::cat(pre, &{ const M: [u32; 25] = [32, 105, 115, 32, 110, 111, 116, 32, 97, 110, 32, 105, 110, 100, 117, 99, 116, 105, 118, 101, 32, 116, 121, 112, 101]; crate::kernel::core_types::code_points(&M) }))),
        },
    }
}

/// con-leche: ConLeche/Frontend/Olean/Emit.lean:392-438 blockStep
/// The recursor arm of `blockStep`.
pub fn block_step_recur(pers: &PersTier, ar: &EStore, mg: &Merged, n: &NIdx, all: &Vec<NIdx>, sk: bool) -> Result<(), CheckError> {
    if all.len() == 0 {
        return Err(block_bad(pers, ar, n, { const M: [u32; 27] = [116, 104, 101, 32, 114, 101, 99, 117, 114, 115, 111, 114, 32, 110, 97, 109, 101, 115, 32, 110, 111, 32, 98, 108, 111, 99, 107]; crate::kernel::core_types::code_points(&M) }));
    }
    let t = &all[0];
    let tt = view::name_text(pers, ar, t);
    match merge::mg_get(mg, t) {
        None => {
            let m = text::cat({ const M: [u32; 28] = [116, 104, 101, 32, 114, 101, 99, 117, 114, 115, 111, 114, 39, 115, 32, 98, 108, 111, 99, 107, 32, 109, 101, 109, 98, 101, 114, 32]; crate::kernel::core_types::code_points(&M) }, &tt);
            Err(block_bad(pers, ar, n, text::cat(m, &{ const M: [u32; 14] = [32, 105, 115, 32, 110, 111, 116, 32, 115, 116, 111, 114, 101, 100]; crate::kernel::core_types::code_points(&M) })))
        }
        Some(m) => match &m.c.kind {
            CKindF::Induct(_, _, all2, _, _, _, _, _) => {
                if module::nidx_list_eq(all2, all) {
                    if lazy::c_entry_skipped(m) == sk {
                        Ok(())
                    } else {
                        let x = text::cat({ const M: [u32; 37] = [116, 104, 101, 32, 114, 101, 99, 117, 114, 115, 111, 114, 32, 105, 115, 32, 115, 97, 102, 101, 32, 111, 114, 32, 117, 110, 115, 97, 102, 101, 32, 119, 104, 101, 114, 101, 32]; crate::kernel::core_types::code_points(&M) }, &tt);
                        Err(block_bad(pers, ar, n, text::cat(x, &{ const M: [u32; 7] = [32, 105, 115, 32, 110, 111, 116]; crate::kernel::core_types::code_points(&M) })))
                    }
                } else {
                    let x = text::cat({ const M: [u32; 28] = [116, 104, 101, 32, 114, 101, 99, 117, 114, 115, 111, 114, 39, 115, 32, 98, 108, 111, 99, 107, 32, 105, 115, 32, 110, 111, 116, 32]; crate::kernel::core_types::code_points(&M) }, &tt);
                    Err(block_bad(pers, ar, n, text::cat(x, &{ const M: [u32; 2] = [39, 115]; crate::kernel::core_types::code_points(&M) })))
                }
            }
            _ => {
                let x = text::cat({ const M: [u32; 28] = [116, 104, 101, 32, 114, 101, 99, 117, 114, 115, 111, 114, 39, 115, 32, 98, 108, 111, 99, 107, 32, 109, 101, 109, 98, 101, 114, 32]; crate::kernel::core_types::code_points(&M) }, &tt);
                Err(block_bad(pers, ar, n, text::cat(x, &{ const M: [u32; 25] = [32, 105, 115, 32, 110, 111, 116, 32, 97, 110, 32, 105, 110, 100, 117, 99, 116, 105, 118, 101, 32, 116, 121, 112, 101]; crate::kernel::core_types::code_points(&M) })))
            }
        },
    }
}

/// con-leche: ConLeche/Frontend/Olean/Emit.lean:392-438 blockStep
/// `(quotConstants mg).all (·.kind.tag == 4)`.
pub fn quot_all_quot(pk: &OleanPins, mg: &Merged) -> bool {
    let qs = quot_constants(pk, mg);
    let mut i = 0usize;
    while i < qs.len() {
        if !quot_named(mg, &qs[i]) {
            return false;
        }
        i += 1;
    }
    true
}

/// con-leche: ConLeche/Frontend/Olean/Emit.lean:392-438 blockStep
/// `(·.kind.tag == 4)`, by name.
pub fn quot_named(mg: &Merged, n: &NIdx) -> bool {
    match merge::mg_get(mg, n) {
        Some(c) => reads::c_kind_tag(&c.c.kind) == 4,
        None => true,
    }
}

/// con-leche: ConLeche/Frontend/Olean/Emit.lean:392-438 blockStep
/// **One stored constant's part in its block.**
pub fn block_step(pk: &OleanPins, pers: &PersTier, ar: &EStore, mg: &Merged, n: &NIdx) -> Result<(), CheckError> {
    match merge::mg_get(mg, n) {
        None => Ok(()),
        Some(c) => match &c.c.kind {
            CKindF::Induct(_, _, all, cs, _, _, _, _) => block_step_induct(pers, ar, mg, n, all, cs, lazy::c_entry_skipped(c)),
            CKindF::Ctor(ind, _, _, _, _) => block_step_ctor(pers, ar, mg, n, ind),
            CKindF::Recur(all, _, _, _, _, _, _, _) => block_step_recur(pers, ar, mg, n, all, lazy::c_entry_skipped(c)),
            CKindF::Quot(_) => {
                if n.eq2(&pk.n_quot) || n.eq2(&pk.n_quot_mk) || n.eq2(&pk.n_quot_lift) || n.eq2(&pk.n_quot_ind) {
                    if quot_all_quot(pk, mg) {
                        Ok(())
                    } else {
                        Err(block_bad(pers, ar, n, { const M: [u32; 53] = [116, 104, 101, 32, 113, 117, 111, 116, 105, 101, 110, 116, 32, 112, 97, 99, 107, 97, 103, 101, 32, 104, 111, 108, 100, 115, 32, 97, 32, 99, 111, 110, 115, 116, 97, 110, 116, 32, 111, 102, 32, 97, 110, 111, 116, 104, 101, 114, 32, 107, 105, 110, 100]; crate::kernel::core_types::code_points(&M) }))
                    }
                } else {
                    Err(block_bad(pers, ar, n, { const M: [u32; 48] = [97, 32, 113, 117, 111, 116, 105, 101, 110, 116, 32, 99, 111, 110, 115, 116, 97, 110, 116, 32, 111, 117, 116, 115, 105, 100, 101, 32, 116, 104, 101, 32, 113, 117, 111, 116, 105, 101, 110, 116, 32, 112, 97, 99, 107, 97, 103, 101]; crate::kernel::core_types::code_points(&M) }))
                }
            }
            _ => Ok(()),
        },
    }
}

/// con-leche: ConLeche/Frontend/Olean/Emit.lean:440-441 blocksOk
/// `blockStep` for every stored constant, before the walk.
pub fn blocks_ok(pk: &OleanPins, pers: &PersTier, ar: &EStore, mg: &Merged) -> Result<(), CheckError> {
    let mut i = 0usize;
    while i < mg.order.len() {
        match block_step(pk, pers, ar, mg, &mg.order[i]) {
            Err(e) => return Err(e),
            Ok(()) => {}
        }
        i += 1;
    }
    Ok(())
}
