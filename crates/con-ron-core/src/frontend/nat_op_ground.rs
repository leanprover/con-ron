//! `frontend::nat_op_ground` — hoisting a pinned `Nat` operation's
//! stream-certified ground, over handles.
//!
//! The Rust twin of `proof/ConRon/Arena/Frontend/NatOpGround.lean`, which is
//! con-leche's `Frontend/NatOpGround.lean`.  It is the second half of
//! con-leche's order-insensitivity fix, beside the built-in prelude: a
//! pin-certified operation's certificate statements are spelled over the
//! STRUCTURAL `Nat` operations (`natOpDeps`), the install guard
//! `divModEnvGuard` requires those stored, and they are not in the operation's
//! own dependency closure — so an export that orders declarations by a DFS
//! from arbitrary roots declines at the install unless the parsed stream is
//! REORDERED.
//!
//! The pass is a no-op — the vector returned as it is, no reorder — on every
//! stream whose ground precedes its operations (the toolchain's own export
//! order: `init-full`, Mathlib), so it costs one name-index build and nothing
//! else there.
//!
//! ## What the handles change, and what `con-ron-core`'s port already had
//!
//! * `usedConstsGo`'s `Std.HashSet Expr` is a `ron::HashMap<EIdx, bool>` whose
//!   hash IS the handle word (DESIGN.md §8.3's identity hashing), so a shared
//!   subterm costs one probe.  `con_ron_core::frontend::nat_op_ground` keys the
//!   same set by `Expr` VALUE and its module note explains at length why not by
//!   address; over handles the question is gone — a handle IS the value, because
//!   `denoteE` is injective.
//! * **The sort is a bucket pass**, `con_ron_core::frontend::nat_op_ground`'s
//!   deviation 2, and it is a deviation from the Lean twin as well.  The twin
//!   keeps `List.mergeSort` with a comparator, on the ground that "a SORT's
//!   comparator is a function value both `List.mergeSort` and Rust's `sort_by`
//!   take"; §3.4 has neither closures nor `sort_by_key`, and a merge sort
//!   written out here would be a second model to refine.  The key's first
//!   component IS an index into the stream, so the same total order comes out
//!   of one pass over the positions `t`: at `t`, first the moved records
//!   targeted at `t` in increasing original index, then the record `t` itself
//!   unless it is moved.  `hoist_key` and `hoist_lt` — the twin's key and its
//!   order — are therefore the SPECIFICATION of what `hoist_order` computes,
//!   and are spelled out below so that P3 has them by name.
//! * **A reordered record is COPIED, not moved**: the subset has no
//!   `Vec::remove`, no `Vec::pop` and no `into_iter`, so the reorder reads
//!   `&ds[k]` and pushes `i_declaration_dup` (the same deviation, at the same
//!   place, as `frontend::prepare`'s).
//! * the twin's two `for`/`mut` loops and its fuelled worklist recursion are
//!   loops here: this directory has DESIGN.md §3.4's loop exemption, and
//!   `-loops-to-rec` gives each one back as the twin's recursion.

use crate::arena::core::{nat_div_mod_names, nat_op_deps, nat_op_names, CORE_WALK_FUEL};
use crate::arena::env::{
    i_constant_info_to_constant_val, i_declaration_dup, i_declaration_names, IConstantInfo,
    IDeclaration, IRecRule,
};
use crate::arena::handle::{EIdx, NIdx};
use crate::arena::monad::{fail, view, AState};
use crate::arena::store::ENodeView;
use crate::kernel::core_types::{code_points, CheckError};
use crate::ron::hashmap::{Dup, Eq2};
// The arena's tables are the epoch-stamped open-addressed map
// (DESIGN.md's `Task #97-P6-4b`), aliased so that every use site below
// reads as it did.  `ron::hashmap::HashMap` is still what `crates/con-ron`
// uses, and is still the one with proofs.
use crate::ron::hashmap2::HashMap2 as HashMap;
use crate::arena::store::PersTier;

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `"fuel exhausted: usedConsts"`, as code points.
pub const M_FUEL_USED_CONSTS: [u32; 26] = [
    102, 117, 101, 108, 32, 101, 120, 104, 97, 117, 115, 116, 101, 100, 58, 32, 117, 115,
    101, 100, 67, 111, 110, 115, 116, 115
];

// ---------------------------------------------------------------------------
// The constants a record references (`NatOpGround.lean:44-116` of the twin)
// ---------------------------------------------------------------------------

/// con-leche: none — probe the visited set (task #97-P4c's extraction rule 5)
/// A `HashMap::get` match that produces a value is its own function; never
/// inlined.
pub fn seen_has(seen: &HashMap<EIdx, bool>, e: &EIdx) -> bool {
    match seen.get(e) {
        Some(_) => true,
        None => false,
    }
}

/// con-leche: ConLeche/Frontend/NatOpGround.lean:54-77 usedConstsGo
/// Lean twin: `proof/ConRon/Arena/Frontend/NatOpGround.lean:46-70 usedConstsGo`
/// — the constants an expression DAG references, each node visited once.
pub fn used_consts_go(
    pers: &PersTier,
    st: &AState,
    seen: &mut HashMap<EIdx, bool>,
    acc: Vec<NIdx>,
    fuel: u64,
    e: &EIdx,
) -> Result<Vec<NIdx>, CheckError> {
    if fuel == 0 {
        fail(CheckError::Internal(code_points(&M_FUEL_USED_CONSTS)))
    } else if seen_has(seen, e) {
        Ok(acc)
    } else {
        seen.insert(e.dup2(), true);
        used_consts_node(pers, st, seen, acc, fuel - 1, e)
    }
}

/// con-leche: ConLeche/Frontend/NatOpGround.lean:54-77 usedConstsGo
/// Lean twin: `proof/ConRon/Arena/Frontend/NatOpGround.lean:46-70 usedConstsGo`
/// — the arms, past the visited test.
pub fn used_consts_node(
    pers: &PersTier,
    st: &AState,
    seen: &mut HashMap<EIdx, bool>,
    acc: Vec<NIdx>,
    fuel: u64,
    e: &EIdx,
) -> Result<Vec<NIdx>, CheckError> {
    match view(pers, st, e) {
        Err(er) => Err(er),
        Ok(ENodeView::Const(n, _)) => {
            let mut out = acc;
            out.push(n);
            Ok(out)
        }
        Ok(ENodeView::App(f, a)) => used_consts_two(pers, st, seen, acc, fuel, &f, &a),
        Ok(ENodeView::Lam(ty, b, _)) => used_consts_two(pers, st, seen, acc, fuel, &ty, &b),
        Ok(ENodeView::ForallE(ty, b, _)) => used_consts_two(pers, st, seen, acc, fuel, &ty, &b),
        Ok(ENodeView::LetE(ty, v, b)) => match used_consts_two(pers, st, seen, acc, fuel, &ty, &v)
        {
            Err(er) => Err(er),
            Ok(a2) => used_consts_go(pers, st, seen, a2, fuel, &b),
        },
        Ok(ENodeView::Proj(sn, _, x)) => {
            let mut out = acc;
            out.push(sn);
            used_consts_go(pers, st, seen, out, fuel, &x)
        }
        Ok(ENodeView::FVar(_, ty)) => used_consts_go(pers, st, seen, acc, fuel, &ty),
        Ok(_) => Ok(acc),
    }
}

/// con-leche: ConLeche/Frontend/NatOpGround.lean:54-77 usedConstsGo
/// The twin's two-child arms, which it spells three times.
pub fn used_consts_two(
    pers: &PersTier,
    st: &AState,
    seen: &mut HashMap<EIdx, bool>,
    acc: Vec<NIdx>,
    fuel: u64,
    a: &EIdx,
    b: &EIdx,
) -> Result<Vec<NIdx>, CheckError> {
    match used_consts_go(pers, st, seen, acc, fuel, a) {
        Err(e) => Err(e),
        Ok(a2) => used_consts_go(pers, st, seen, a2, fuel, b),
    }
}

/// con-leche: ConLeche/Frontend/NatOpGround.lean:79-95 Declaration.usedConsts
/// Lean twin: `proof/ConRon/Arena/Frontend/NatOpGround.lean:72-82 usedConstsRules`
/// — a recursor's rules, folded over ONE visited set.
pub fn used_consts_rules(
    pers: &PersTier,
    st: &AState,
    seen: &mut HashMap<EIdx, bool>,
    acc: Vec<NIdx>,
    rules: &Vec<IRecRule>,
) -> Result<Vec<NIdx>, CheckError> {
    let mut out = acc;
    let n = rules.len();
    let mut i: usize = 0;
    while i < n {
        match used_consts_go(pers, st, seen, out, CORE_WALK_FUEL, &rules[i].rhs) {
            Err(e) => return Err(e),
            Ok(a2) => {
                out = a2;
            }
        }
        i += 1;
    }
    Ok(out)
}

/// con-leche: ConLeche/Frontend/NatOpGround.lean:79-95 Declaration.usedConsts
/// Lean twin: `proof/ConRon/Arena/Frontend/NatOpGround.lean:84-95 usedConstsBlock`
/// — an inductive block's members, folded over ONE visited set: the type of
/// each member and, for a recursor, every rule's right-hand side.
pub fn used_consts_block(
    pers: &PersTier,
    st: &mut AState,
    seen: &mut HashMap<EIdx, bool>,
    acc: Vec<NIdx>,
    block: &Vec<IConstantInfo>,
) -> Result<Vec<NIdx>, CheckError> {
    let mut out = acc;
    let n = block.len();
    let mut i: usize = 0;
    while i < n {
        let ci = crate::arena::env::i_constant_info_dup(&block[i]);
        let ty = match i_constant_info_to_constant_val(pers, &mut st.store, &ci) {
            Err(e) => return Err(e),
            Ok(cv) => cv.ty,
        };
        match used_consts_go(pers, st, seen, out, CORE_WALK_FUEL, &ty) {
            Err(e) => return Err(e),
            Ok(a2) => {
                out = a2;
            }
        }
        match &block[i] {
            IConstantInfo::RecInfo(_, _, _, rules) => {
                match used_consts_rules(pers, st, seen, out, rules) {
                    Err(e) => return Err(e),
                    Ok(a3) => {
                        out = a3;
                    }
                }
            }
            _ => {}
        }
        i += 1;
    }
    Ok(out)
}

/// con-leche: ConLeche/Frontend/NatOpGround.lean:79-95 Declaration.usedConsts
/// Lean twin: `proof/ConRon/Arena/Frontend/NatOpGround.lean:97-106
/// IDeclaration.usedConsts` — the constants a parsed record references (types,
/// values, recursor rule right-hand sides; a basis block references nothing the
/// stream declares).
pub fn decl_used_consts(
    pers: &PersTier,
    st: &mut AState,
    d: &IDeclaration,
) -> Result<Vec<NIdx>, CheckError> {
    let mut seen: HashMap<EIdx, bool> = HashMap::new();
    match d {
        IDeclaration::AxiomDecl(cv) => {
            used_consts_go(pers, st, &mut seen, Vec::new(), CORE_WALK_FUEL, &cv.ty)
        }
        IDeclaration::DefnDecl(cv, v, _) => {
            decl_used_consts_value(pers, st, &mut seen, &cv.ty, v)
        }
        IDeclaration::ThmDecl(cv, v) => decl_used_consts_value(pers, st, &mut seen, &cv.ty, v),
        IDeclaration::OpaqueDecl(cv, v) => decl_used_consts_value(pers, st, &mut seen, &cv.ty, v),
        IDeclaration::IndDecl(block, _) => {
            used_consts_block(pers, st, &mut seen, Vec::new(), block)
        }
        IDeclaration::BasisDecl(_) => Ok(Vec::new()),
        IDeclaration::QuotDecl(_, _) => Ok(Vec::new()),
    }
}

/// con-leche: ConLeche/Frontend/NatOpGround.lean:79-95 Declaration.usedConsts
/// Lean twin: `proof/ConRon/Arena/Frontend/NatOpGround.lean:97-106
/// IDeclaration.usedConsts` — the three value kinds' clause, which the twin
/// spells once with an `|` pattern: the type and the value, at one visited set.
pub fn decl_used_consts_value(
    pers: &PersTier,
    st: &AState,
    seen: &mut HashMap<EIdx, bool>,
    ty: &EIdx,
    v: &EIdx,
) -> Result<Vec<NIdx>, CheckError> {
    match used_consts_go(pers, st, seen, Vec::new(), CORE_WALK_FUEL, ty) {
        Err(e) => Err(e),
        Ok(acc) => used_consts_go(pers, st, seen, acc, CORE_WALK_FUEL, v),
    }
}

/// con-leche: ConLeche/Frontend/NatOpGround.lean:97-104 isNatOpRecord
/// Lean twin: `proof/ConRon/Arena/Frontend/NatOpGround.lean:108-116
/// isNatOpRecord` — the pinned `Nat` operation records whose ground the pass
/// serves: the pin-certified WF operations and the structural ones.
pub fn is_nat_op_record(
    st: &mut AState,
    d: &IDeclaration,
) -> Result<Option<NIdx>, CheckError> {
    match d {
        IDeclaration::DefnDecl(cv, _, _) => match nat_div_mod_names(st) {
            Err(e) => Err(e),
            Ok(ds) => match nat_op_names(st) {
                Err(e) => Err(e),
                Ok(ns) => {
                    if nidx_contains(&ds, &cv.name) || nidx_contains(&ns, &cv.name) {
                        Ok(Some(cv.name.dup2()))
                    } else {
                        Ok(None)
                    }
                }
            },
        },
        _ => Ok(None),
    }
}

/// con-leche: none — `List.contains` over a name-handle list
/// A handle comparison is word equality (DESIGN.md §8.3).
pub fn nidx_contains(ns: &Vec<NIdx>, n: &NIdx) -> bool {
    let m = ns.len();
    let mut i: usize = 0;
    while i < m {
        if ns[i].eq2(n) {
            return true;
        }
        i += 1;
    }
    false
}

// ---------------------------------------------------------------------------
// Which records must move, and how far (`NatOpGround.lean:118-209`)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Frontend/NatOpGround.lean:106-136 hoistTargets
/// Lean twin: `proof/ConRon/Arena/Frontend/NatOpGround.lean:129-138 nameIndex`
/// — name ↦ the index of the record declaring it; the FIRST record declaring a
/// name wins (a duplicate is rejected by the fold anyway).
pub fn hoist_name_index(ds: &Vec<IDeclaration>) -> HashMap<NIdx, u64> {
    let mut idx: HashMap<NIdx, u64> = HashMap::new();
    let n = ds.len();
    let mut i: usize = 0;
    while i < n {
        let ns = i_declaration_names(&ds[i]);
        let m = ns.len();
        let mut j: usize = 0;
        while j < m {
            if !idx.contains_key(&ns[j]) {
                idx.insert(ns[j].dup2(), i as u64);
            }
            j += 1;
        }
        i += 1;
    }
    idx
}

/// con-leche: none — `Std.HashMap.getElem?` at a handle key, `Nat` values
/// The **owning** probe of the name index (extraction rule 5): it answers a
/// `u64`, not a borrow into the map, so no `idx` borrow is alive when the
/// caller branches.
pub fn idx_get(idx: &HashMap<NIdx, u64>, n: &NIdx) -> Option<u64> {
    match idx.get(n) {
        Some(j) => Some(*j),
        None => None,
    }
}

/// con-leche: none — `Std.HashMap.getElem?` at a `Nat` key, as a test
/// The **owning** probe of the target map: the twin's `match target[k]? with |
/// some t => if t ≤ i then …`.
pub fn target_done(target: &HashMap<u64, u64>, k: u64, i: u64) -> bool {
    match target.get(&k) {
        Some(t) => *t <= i,
        None => false,
    }
}

/// con-leche: ConLeche/Frontend/NatOpGround.lean:106-136 hoistTargets
/// Lean twin: `proof/ConRon/Arena/Frontend/NatOpGround.lean:189-197 hoistClosure.pushOne` —
/// the twin's inner `for n in ds[k]!.usedConsts` loop: the references of the
/// record just targeted that lie after `i` go on the worklist.
pub fn hoist_push_deps(
    idx: &HashMap<NIdx, u64>,
    used: &Vec<NIdx>,
    stack: Vec<u64>,
    sp: usize,
    i: u64,
    k: u64,
) -> (Vec<u64>, usize) {
    let mut stack = stack;
    let mut sp = sp;
    let n = used.len();
    let mut u: usize = 0;
    while u < n {
        match idx_get(idx, &used[u]) {
            Some(m) => {
                if m > i && m != k {
                    let r = stack_push_u64(stack, sp, m);
                    stack = r.0;
                    sp = r.1;
                }
            }
            None => {}
        }
        u += 1;
    }
    (stack, sp)
}

/// con-leche: none — `Array.push` on the index worklist of `hoistTargets`
/// Lean twin: `proof/ConRon/Arena/Frontend/NatOpGround.lean:189-197 hoistClosure.pushOne` —
/// a worklist push.  `Vec::pop` is not in the Aeneas subset, so the walk
/// carries its own top-of-stack index and overwrites the slot at it — a
/// `Vec::push` only when the stack has never been that deep.  The vector and
/// the top travel together (§3.4: accumulators by value), which is
/// `con_ron_core::frontend::nat_op_ground::stack_push_u64` exactly.
pub fn stack_push_u64(stack: Vec<u64>, sp: usize, x: u64) -> (Vec<u64>, usize) {
    let mut stack = stack;
    if sp < stack.len() {
        stack[sp] = x;
    } else {
        stack.push(x);
    }
    (stack, sp + 1)
}

/// con-leche: ConLeche/Frontend/NatOpGround.lean:106-136 hoistTargets
/// Lean twin: `proof/ConRon/Arena/Frontend/NatOpGround.lean:155-197
/// hoistClosure` — the worklist: the closure of the ground record `j` within
/// the records after `i`, each reached record marked as having to precede `i`.
/// This loop is unfuelled.  The twin's fuel counts MARKING pops only (at most
/// `ds.size`), the rest are dropped structurally, and `hoistClosure_fuel_succ`
/// proves that fuel sufficient: the twin runs exactly this loop's pops.
pub fn hoist_close(
    pers: &PersTier,
    st: &mut AState,
    ds: &Vec<IDeclaration>,
    idx: &HashMap<NIdx, u64>,
    target: HashMap<u64, u64>,
    j: u64,
    i: u64,
) -> Result<HashMap<u64, u64>, CheckError> {
    let mut target = target;
    let mut stack: Vec<u64> = Vec::new();
    stack.push(j);
    let mut sp: usize = 1;
    while sp > 0 {
        sp -= 1;
        let k = stack[sp];
        if !target_done(&target, k, i) {
            target.insert(k, i);
            let d = i_declaration_dup(&ds[k as usize]);
            match decl_used_consts(pers, st, &d) {
                Err(e) => return Err(e),
                Ok(used) => {
                    let r = hoist_push_deps(idx, &used, stack, sp, i, k);
                    stack = r.0;
                    sp = r.1;
                }
            }
        }
    }
    Ok(target)
}

/// con-leche: ConLeche/Frontend/NatOpGround.lean:106-136 hoistTargets
/// Lean twin: `proof/ConRon/Arena/Frontend/NatOpGround.lean:341-354 hoistTargetsGo.hoistDeps`
/// — the twin's inner `for g in natOpDeps c` loop of one operation record at
/// index `i`: each ground declared LATER carries its closure with it.
pub fn hoist_targets_at(
    pers: &PersTier,
    st: &mut AState,
    ds: &Vec<IDeclaration>,
    idx: &HashMap<NIdx, u64>,
    target: HashMap<u64, u64>,
    c: &NIdx,
    i: u64,
) -> Result<HashMap<u64, u64>, CheckError> {
    let mut target = target;
    let gs = match nat_op_deps(st, c) {
        Err(e) => return Err(e),
        Ok(v) => v,
    };
    let m = gs.len();
    let mut k: usize = 0;
    while k < m {
        match idx_get(idx, &gs[k]) {
            Some(j) => {
                if j > i {
                    match hoist_close(pers, st, ds, idx, target, j, i) {
                        Err(e) => return Err(e),
                        Ok(t) => {
                            target = t;
                        }
                    }
                }
            }
            None => {}
        }
        k += 1;
    }
    Ok(target)
}

/// con-leche: ConLeche/Frontend/NatOpGround.lean:106-136 hoistTargets
/// Lean twin: `proof/ConRon/Arena/Frontend/NatOpGround.lean:356-361
/// hoistTargets` — **which records must move, and how far**: the map from a
/// record's index to the earliest pinned-operation index it must precede.
/// Empty — and then the hoist is the identity — on every stream whose ground
/// precedes its operations.
pub fn hoist_targets(
    pers: &PersTier,
    st: &mut AState,
    ds: &Vec<IDeclaration>,
) -> Result<HashMap<u64, u64>, CheckError> {
    let idx = hoist_name_index(ds);
    let mut target: HashMap<u64, u64> = HashMap::new();
    let n = ds.len();
    let mut i: usize = 0;
    while i < n {
        let d = i_declaration_dup(&ds[i]);
        match is_nat_op_record(st, &d) {
            Err(e) => return Err(e),
            Ok(Some(c)) => match hoist_targets_at(pers, st, ds, &idx, target, &c, i as u64) {
                Err(e) => return Err(e),
                Ok(t) => {
                    target = t;
                }
            },
            Ok(None) => {}
        }
        i += 1;
    }
    Ok(target)
}

// ---------------------------------------------------------------------------
// The reorder (`NatOpGround.lean:211-265` of the twin)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Frontend/NatOpGround.lean:138-162 applyHoist
/// Lean twin: `proof/ConRon/Arena/Frontend/NatOpGround.lean:365-373 hoistKey` —
/// a moved record sorts at its target, just ahead of the operation record there
/// (key `(t, 0, k)` against the operation's `(t, 1, t)`); everything else keeps
/// its position (`(k, 1, k)`).  **The specification** of the order
/// `hoist_order` computes (the module note's bucket pass); nothing calls it.
pub fn hoist_key(target: &HashMap<u64, u64>, k: u64) -> (u64, u64, u64) {
    match target.get(&k) {
        Some(t) => (*t, 0, k),
        None => (k, 1, k),
    }
}

/// con-leche: ConLeche/Frontend/NatOpGround.lean:138-162 applyHoist
/// Lean twin: `proof/ConRon/Arena/Frontend/NatOpGround.lean:375-381 hoistLt` —
/// the strict order on those keys.  **The specification**, as `hoist_key` is.
pub fn hoist_lt(target: &HashMap<u64, u64>, a: u64, b: u64) -> bool {
    let ka = hoist_key(target, a);
    let kb = hoist_key(target, b);
    ka.0 < kb.0 || (ka.0 == kb.0 && (ka.1 < kb.1 || (ka.1 == kb.1 && ka.2 < kb.2)))
}

/// con-leche: ConLeche/Frontend/NatOpGround.lean:138-162 applyHoist
/// Lean twin: `proof/ConRon/Arena/Frontend/NatOpGround.lean:402-407 applyHoist`
/// — the moved records' indices, increasing.
pub fn hoist_moved_idxs(n: usize, target: &HashMap<u64, u64>) -> Vec<u64> {
    let mut out: Vec<u64> = Vec::new();
    let mut k: usize = 0;
    while k < n {
        if target.contains_key(&(k as u64)) {
            out.push(k as u64);
        }
        k += 1;
    }
    out
}

/// con-leche: none — `Std.HashMap.getElem?` at a `Nat` key, as a test
/// The **owning** probe behind the bucket pass: is `k` a moved record whose
/// target is exactly `t`?
pub fn target_is(target: &HashMap<u64, u64>, k: u64, t: u64) -> bool {
    match target.get(&k) {
        Some(tt) => *tt == t,
        None => false,
    }
}

/// con-leche: ConLeche/Frontend/NatOpGround.lean:138-162 applyHoist
/// Lean twin: `proof/ConRon/Arena/Frontend/NatOpGround.lean:402-407 applyHoist` —
/// the twin's `(List.range ds.size).mergeSort (hoistLt …)`, as the module
/// note's bucket pass: at each position `t`, first the moved records targeted
/// at `t` (increasing original index, which is dependency order), then the
/// record `t` itself unless it is one of them.  The two orders are the same,
/// because `hoist_key`'s first component IS a position of the stream.
pub fn hoist_order(n: usize, target: &HashMap<u64, u64>, moved: &Vec<u64>) -> Vec<u64> {
    let mut order: Vec<u64> = Vec::with_capacity(n);
    let mut t: usize = 0;
    while t < n {
        let m = moved.len();
        let mut a: usize = 0;
        while a < m {
            if target_is(target, moved[a], t as u64) {
                order.push(moved[a]);
            }
            a += 1;
        }
        if !target.contains_key(&(t as u64)) {
            order.push(t as u64);
        }
        t += 1;
    }
    order
}

/// con-leche: ConLeche/Frontend/NatOpGround.lean:138-162 applyHoist
/// Lean twin: `proof/ConRon/Arena/Frontend/NatOpGround.lean:393-400 reorder` —
/// the records in the sorted order, one COPY per record (the module note's
/// third deviation).
pub fn hoist_reorder(ds: &Vec<IDeclaration>, order: &Vec<u64>) -> Vec<IDeclaration> {
    let n = order.len();
    let mut out: Vec<IDeclaration> = Vec::with_capacity(n);
    let mut i: usize = 0;
    while i < n {
        out.push(i_declaration_dup(&ds[order[i] as usize]));
        i += 1;
    }
    out
}

/// con-leche: ConLeche/Frontend/NatOpGround.lean:138-162 applyHoist
/// Lean twin: `proof/ConRon/Arena/Frontend/NatOpGround.lean:383-391 movedNames`
/// — the names of the records that moved, in index order: the driver's receipt.
pub fn hoist_moved_names(ds: &Vec<IDeclaration>, moved: &Vec<u64>) -> Vec<NIdx> {
    let mut out: Vec<NIdx> = Vec::new();
    let n = moved.len();
    let mut a: usize = 0;
    while a < n {
        let ns = i_declaration_names(&ds[moved[a] as usize]);
        let m = ns.len();
        let mut j: usize = 0;
        while j < m {
            out.push(ns[j].dup2());
            j += 1;
        }
        a += 1;
    }
    out
}

/// con-leche: ConLeche/Frontend/NatOpGround.lean:138-162 applyHoist
/// Lean twin: `proof/ConRon/Arena/Frontend/NatOpGround.lean:402-407 applyHoist`
/// — **the reorder**: the sorted record array and the names of the records
/// moved.
pub fn apply_hoist(
    ds: &Vec<IDeclaration>,
    target: &HashMap<u64, u64>,
) -> (Vec<IDeclaration>, Vec<NIdx>) {
    let moved = hoist_moved_idxs(ds.len(), target);
    let order = hoist_order(ds.len(), target, &moved);
    let out = hoist_reorder(ds, &order);
    let names = hoist_moved_names(ds, &moved);
    (out, names)
}

/// con-leche: ConLeche/Frontend/NatOpGround.lean:164-169 hoistNatOpGround
/// Lean twin: `proof/ConRon/Arena/Frontend/NatOpGround.lean:409-416
/// hoistNatOpGround` — **the hoist.**  Returns the reordered records and the
/// names of the records moved (empty, and the array untouched and uncopied,
/// when no operation's ground is declared after it).
pub fn hoist_nat_op_ground(
    pers: &PersTier,
    st: &mut AState,
    ds: Vec<IDeclaration>,
) -> Result<(Vec<IDeclaration>, Vec<NIdx>), CheckError> {
    match hoist_targets(pers, st, &ds) {
        Err(e) => Err(e),
        Ok(target) => {
            if target.len() == 0 {
                Ok((ds, Vec::new()))
            } else {
                Ok(apply_hoist(&ds, &target))
            }
        }
    }
}
