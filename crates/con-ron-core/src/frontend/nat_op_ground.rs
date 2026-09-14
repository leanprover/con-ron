//! `ConLeche/Frontend/NatOpGround.lean` — hoisting a pinned `Nat`
//! operation's stream-certified ground.
//!
//! A pin-certified operation's certificate *statements* are spelled over the
//! structural `Nat` operations (`nat_op_deps`: `Nat.shiftLeft`'s over
//! `Nat.ble` and `Nat.sub`, `Nat.land`'s over `Nat.mul`, …), and the install
//! guard requires those stored.  They are NOT in the operation's own
//! dependency closure, so an export that orders declarations by a DFS from
//! arbitrary roots declined at the install.  They cannot go into the prelude
//! either (the structural operations are certified at install by
//! *definitional* recurrence equations, so that a stream from another
//! toolchain still installs them), so instead the parsed stream is
//! REORDERED: for every pinned operation record whose ground is declared
//! LATER in the stream, the ground's transitive dependency closure (within
//! the stream) is moved ahead of the operation.  A dependency-closed set
//! moved earlier is still a valid stream, so the checker's verdict on a valid
//! stream is the official kernel's whatever order the export chose.
//!
//! Like the prelude prepend it sits beside, this is a pure transformation of
//! the parsed list below the verified fold — a **step of `prepare_prelude`**
//! (`crate::frontend::prepare`), not of the parse: nothing in the kernel or
//! the proofs knows it happened.  The pass is a no-op — the vector is returned
//! as it is, no sort — on every stream whose ground precedes its operations
//! (the toolchain's own export order: `init`, Mathlib).
//!
//! **The pass is two halves** (con-leche task #293): `hoist_targets` computes
//! the map from a record's index to the earliest pinned-operation index it
//! must precede, and `apply_hoist` does the reorder.  Behaviour is unchanged;
//! the split exists so that con-leche's permutation proof does not have to
//! walk the `Id.run do` that computes the targets.
//!
//! **Three deviations of the port into the verified core** (task #84).
//!
//! 1. `usedConstsGo`'s `Std.HashSet Expr` is `HashMap<Expr, bool>`
//!    (`crate::ron::hashmap`, the port's `Std.HashMap`; DESIGN.md §3.4 keeps
//!    `std::collections` out of the core).  The key is the `Expr` itself, so
//!    the dictionary is con-leche's own — `Hashable Expr` is `Expr.hash` and
//!    `Eq2 Expr` is `Expr.beq` (`kernel/expr.rs`'s two impls) — where the
//!    unverified frontend keyed an `ExprKey` newtype by the node's ADDRESS.
//!    Value identity is the coarser partition, so the walk visits no more
//!    nodes; what it costs is that a probe whose truncated hash collides runs
//!    `Expr.beq` on a pair that is not equal, which task #37 measured as
//!    exponential on `tests/e2e/tower_beqpair.ndjson`.  That is a
//!    `kernel::expr::beq` memo-key matter (task #37's finding, DESIGN.md), not
//!    this module's, and every other `Expr`-keyed table in the core
//!    (`struct_parts::mentions_const`, `expr_ops`' memos) already keys by
//!    value; keying by address here would put a second, incompatible notion of
//!    `Expr` equality into the model for no gain.
//! 2. **The sort is a bucket pass.**  con-leche sorts `List.range ds.size` by
//!    the key `(t, s, k)` with `List.mergeSort`; §3.4 has neither closures nor
//!    `sort_by_key`, and a merge sort written out here would be a second
//!    model to refine.  The key's first component *is* an index into the
//!    stream, so the same total order comes out of one pass over the
//!    positions `t` (`hoist_order`): at `t`, first the moved records targeted
//!    at `t` in increasing original index, then the record `t` itself unless
//!    it is moved.  The moved set is a `Nat` operation's ground closure, i.e.
//!    a handful of records, so the pass is `O(n · |moved|)` and runs at all
//!    only when the stream needs the hoist.
//! 3. **A reordered record is COPIED, not moved.**  The subset has no
//!    `Vec::remove`, no `Vec::pop` and no `into_iter` (nothing that moves an
//!    element out of a `Vec`), so `apply_hoist` reads `&ds[k]` and pushes
//!    `declaration_dup`.  A `Declaration`'s `dup` is its spine — names, level
//!    parameter lists, rule vectors and `P` handle bumps on the shared `Expr`
//!    DAG — so this is one pass proportional to the records, not to the terms
//!    they mention.  `hoist_nat_op_ground` still returns the vector it was
//!    given, untouched and uncopied, on every stream that needs no hoist.
//!
//! con-leche's `instance : Inhabited DeclC` went with task #293 and had no
//! Rust counterpart anyway (it existed for Lean's `ds[i]!`).

use crate::kernel::core_k;
use crate::kernel::env;
use crate::kernel::env::{ConstantInfo, Declaration};
use crate::kernel::expr;
use crate::kernel::expr::{Expr, ExprKind};
use crate::kernel::name;
use crate::kernel::name::Name;
use crate::ron::hashmap::HashMap;

// ---------------------------------------------------------------------------
// Copying a record (the subset has no way to move one out of a `Vec`)
// ---------------------------------------------------------------------------

/// con-leche: none — Lean's value semantics on `Array Declaration`
/// A copy of a parsed record.  Lean copies a record out of an array for free;
/// `Declaration` derives nothing in the port (`Clone` included, task #10's
/// note) and the subset has no `Vec::remove`/`Vec::pop`, so the two
/// reorderings of `prepare_prelude` — this module's hoist and the prelude
/// prepend — read `&ds[k]` and copy.  The copy is the record's spine: the
/// `Expr` fields are `P` handles (DESIGN.md §3.2) and are shared, not walked.
pub fn declaration_dup(d: &Declaration) -> Declaration {
    match d {
        Declaration::AxiomDecl(cv) => Declaration::AxiomDecl(env::constant_val_dup(cv)),
        Declaration::DefnDecl(cv, v, h) => Declaration::DefnDecl(
            env::constant_val_dup(cv),
            expr::dup(v),
            env::reducibility_hint_dup(h),
        ),
        Declaration::ThmDecl(cv, v) => {
            Declaration::ThmDecl(env::constant_val_dup(cv), expr::dup(v))
        }
        Declaration::OpaqueDecl(cv, v) => {
            Declaration::OpaqueDecl(env::constant_val_dup(cv), expr::dup(v))
        }
        Declaration::BasisDecl(k) => Declaration::BasisDecl(env::basis_kind_dup(k)),
        Declaration::IndDecl(block, n) => {
            Declaration::IndDecl(block_copy(block, 0, Vec::new()), *n)
        }
        Declaration::QuotDecl(k, cv) => {
            Declaration::QuotDecl(env::quot_kind_dup(k), env::constant_val_dup(cv))
        }
    }
}

/// con-leche: none — the index recursion behind `declaration_dup`'s block arm
/// The accumulator is passed by value and returned (§3.4 reserves `&mut` for
/// the state parameter; task #6's rule).
pub fn block_copy(
    block: &Vec<ConstantInfo>,
    i: usize,
    out: Vec<ConstantInfo>,
) -> Vec<ConstantInfo> {
    if i >= block.len() {
        out
    } else {
        let mut out = out;
        out.push(env::constant_info_dup(&block[i]));
        block_copy(block, i + 1, out)
    }
}

// ---------------------------------------------------------------------------
// The two worklists (`Vec` is the store, `sp` is the top)
// ---------------------------------------------------------------------------

/// con-leche: none — `Array.push` on a worklist whose top is an index
/// A worklist push.  `Vec::pop` is not in the subset, so the two walks below
/// carry their own top-of-stack index and overwrite the slot at it — a
/// `Vec::push` only when the stack has never been that deep.  The vector and
/// the top are returned together (§3.4: accumulators travel by value).
pub fn stack_push_expr(stack: Vec<Expr>, sp: usize, x: Expr) -> (Vec<Expr>, usize) {
    let mut stack = stack;
    if sp < stack.len() {
        stack[sp] = x;
    } else {
        stack.push(x);
    }
    (stack, sp + 1)
}

/// con-leche: none — `Array.push` on the index worklist of `hoistTargets`
/// `stack_push_expr` for the closure walk's `Nat` stack.
pub fn stack_push_u64(stack: Vec<u64>, sp: usize, x: u64) -> (Vec<u64>, usize) {
    let mut stack = stack;
    if sp < stack.len() {
        stack[sp] = x;
    } else {
        stack.push(x);
    }
    (stack, sp + 1)
}

// ---------------------------------------------------------------------------
// The constants a record references
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Frontend/NatOpGround.lean:54-77 usedConstsGo
/// The constants an `Expr` DAG references, each node visited once.
/// Deviation: an explicit worklist rather than structural recursion —
/// `app-lam` reaches term depths in the thousands and the Lean recursion runs
/// on a 1 GiB stack the frontend thread does not have to reserve for this.
/// Visit order is preserved (children pushed so the first child is visited
/// first), because `acc`'s order is the hoist's tie-break.
pub fn used_consts_go(seen: &mut HashMap<Expr, bool>, acc: Vec<Name>, e: &Expr) -> Vec<Name> {
    let mut acc = acc;
    let mut stack: Vec<Expr> = Vec::new();
    stack.push(expr::dup(e));
    let mut sp: usize = 1;
    while sp > 0 {
        sp -= 1;
        let x = expr::dup(&stack[sp]);
        if !seen.contains_key(&x) {
            seen.insert(expr::dup(&x), true);
            match &x.0.kind {
                ExprKind::Const(n, _) => acc.push(name::dup(n)),
                ExprKind::App(f, a) => {
                    let r1 = stack_push_expr(stack, sp, expr::dup(a));
                    let r2 = stack_push_expr(r1.0, r1.1, expr::dup(f));
                    stack = r2.0;
                    sp = r2.1;
                }
                ExprKind::Lam(ty, b, _) | ExprKind::ForallE(ty, b, _) => {
                    let r1 = stack_push_expr(stack, sp, expr::dup(b));
                    let r2 = stack_push_expr(r1.0, r1.1, expr::dup(ty));
                    stack = r2.0;
                    sp = r2.1;
                }
                ExprKind::LetE(ty, v, b) => {
                    let r1 = stack_push_expr(stack, sp, expr::dup(b));
                    let r2 = stack_push_expr(r1.0, r1.1, expr::dup(v));
                    let r3 = stack_push_expr(r2.0, r2.1, expr::dup(ty));
                    stack = r3.0;
                    sp = r3.1;
                }
                ExprKind::Proj(sn, _, sub) => {
                    acc.push(name::dup(sn));
                    let r1 = stack_push_expr(stack, sp, expr::dup(sub));
                    stack = r1.0;
                    sp = r1.1;
                }
                ExprKind::Fvar(_, ty) => {
                    let r1 = stack_push_expr(stack, sp, expr::dup(ty));
                    stack = r1.0;
                    sp = r1.1;
                }
                ExprKind::Bvar(_) => {}
                ExprKind::Sort(_) => {}
                ExprKind::Lit(_) => {}
            }
        }
    }
    acc
}

/// con-leche: ConLeche/Frontend/NatOpGround.lean:79-95 Declaration.usedConsts
/// The constants a parsed record references (types, values, recursor rule
/// right-hand sides; a basis block and a quotient record reference nothing the
/// stream declares).
pub fn decl_used_consts(d: &Declaration) -> Vec<Name> {
    let mut seen: HashMap<Expr, bool> = HashMap::new();
    let acc: Vec<Name> = Vec::new();
    match d {
        Declaration::AxiomDecl(cv) => used_consts_go(&mut seen, acc, &cv.ty),
        Declaration::DefnDecl(cv, v, _)
        | Declaration::ThmDecl(cv, v)
        | Declaration::OpaqueDecl(cv, v) => {
            let acc = used_consts_go(&mut seen, acc, &cv.ty);
            used_consts_go(&mut seen, acc, v)
        }
        Declaration::IndDecl(block, _) => block_used_consts(&mut seen, acc, block),
        Declaration::BasisDecl(_) => acc,
        Declaration::QuotDecl(_, _) => acc,
    }
}

/// con-leche: ConLeche/Frontend/NatOpGround.lean:79-95 Declaration.usedConsts
/// The cited `block.foldl` of the `indDecl` arm: each member's type, and a
/// recursor's rule right-hand sides.  Split off so the fold is a loop of its
/// own and `decl_used_consts` stays the `match` con-leche writes.
pub fn block_used_consts(
    seen: &mut HashMap<Expr, bool>,
    acc: Vec<Name>,
    block: &Vec<ConstantInfo>,
) -> Vec<Name> {
    let mut acc = acc;
    let n = block.len();
    let mut i: usize = 0;
    while i < n {
        let cv = env::to_constant_val(&block[i]);
        acc = used_consts_go(seen, acc, &cv.ty);
        match &block[i] {
            ConstantInfo::RecInfo(_, _, _, rules) => {
                let m = rules.len();
                let mut j: usize = 0;
                while j < m {
                    acc = used_consts_go(seen, acc, &rules[j].rhs);
                    j += 1;
                }
            }
            _ => {}
        }
        i += 1;
    }
    acc
}

/// con-leche: ConLeche/Frontend/NatOpGround.lean:97-104 isNatOpRecord
/// The pinned `Nat` operation records whose ground the pass serves: the
/// pin-certified WF operations and the structural ones (whose `natOpDeps` are
/// in their own closures already — kept uniform).
pub fn is_nat_op_record(d: &Declaration) -> Option<Name> {
    match d {
        Declaration::DefnDecl(cv, _, _) => {
            if name::contains(&core_k::nat_div_mod_names(), &cv.name)
                || name::contains(&core_k::nat_op_names(), &cv.name)
            {
                Some(name::dup(&cv.name))
            } else {
                None
            }
        }
        _ => None,
    }
}

// ---------------------------------------------------------------------------
// Which records must move, and how far
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Frontend/NatOpGround.lean:106-136 hoistTargets
/// The cited `for i in [0:ds.size] do for n in ds[i]!.names`: name ↦ the index
/// of the record declaring it (the first, on a duplicate — the fold rejects
/// the second anyway).
pub fn hoist_name_index(ds: &Vec<Declaration>) -> HashMap<Name, u64> {
    let mut idx: HashMap<Name, u64> = HashMap::new();
    let n = ds.len();
    let mut i: usize = 0;
    while i < n {
        let ns = env::declaration_names(&ds[i]);
        let m = ns.len();
        let mut j: usize = 0;
        while j < m {
            if !idx.contains_key(&ns[j]) {
                idx.insert(name::dup(&ns[j]), i as u64);
            }
            j += 1;
        }
        i += 1;
    }
    idx
}

/// con-leche: ConLeche/Frontend/NatOpGround.lean:106-136 hoistTargets
/// **Which records must move, and how far**: the map from a record's index to
/// the earliest pinned-operation index it must precede.  Empty — and then the
/// hoist is the identity — on every stream whose ground precedes its
/// operations.
pub fn hoist_targets(ds: &Vec<Declaration>) -> HashMap<u64, u64> {
    let idx = hoist_name_index(ds);
    let mut target: HashMap<u64, u64> = HashMap::new();
    let n = ds.len();
    let mut i: usize = 0;
    while i < n {
        match is_nat_op_record(&ds[i]) {
            Some(c) => {
                target = hoist_targets_at(ds, &idx, target, &c, i as u64);
            }
            None => {}
        }
        i += 1;
    }
    target
}

/// con-leche: ConLeche/Frontend/NatOpGround.lean:106-136 hoistTargets
/// The cited `for g in natOpDeps c` of one operation record at index `i`: each
/// ground declared LATER carries its closure with it.  Split off so the loop's
/// tail is one line (`-loops-to-rec` copies whatever follows a loop into every
/// exit).
pub fn hoist_targets_at(
    ds: &Vec<Declaration>,
    idx: &HashMap<Name, u64>,
    target: HashMap<u64, u64>,
    c: &Name,
    i: u64,
) -> HashMap<u64, u64> {
    let mut target = target;
    let gs = core_k::nat_op_deps(c);
    let m = gs.len();
    let mut k: usize = 0;
    while k < m {
        match idx.get(&gs[k]) {
            Some(j) => {
                let j = *j;
                if j > i {
                    target = hoist_close(ds, idx, target, j, i);
                }
            }
            None => {}
        }
        k += 1;
    }
    target
}

/// con-leche: ConLeche/Frontend/NatOpGround.lean:106-136 hoistTargets
/// The cited `while h : stack.size > 0` — the closure of the ground record `j`
/// within the records after `i`, every member targeted at `i`.
pub fn hoist_close(
    ds: &Vec<Declaration>,
    idx: &HashMap<Name, u64>,
    target: HashMap<u64, u64>,
    j: u64,
    i: u64,
) -> HashMap<u64, u64> {
    let mut target = target;
    let mut stack: Vec<u64> = Vec::new();
    stack.push(j);
    let mut sp: usize = 1;
    while sp > 0 {
        sp -= 1;
        let k = stack[sp];
        let done = match target.get(&k) {
            Some(t) => *t <= i,
            None => false,
        };
        if !done {
            target.insert(k, i);
            let used = decl_used_consts(&ds[k as usize]);
            let nu = used.len();
            let mut u: usize = 0;
            while u < nu {
                match idx.get(&used[u]) {
                    Some(m) => {
                        let m = *m;
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
        }
    }
    target
}

// ---------------------------------------------------------------------------
// The reorder
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Frontend/NatOpGround.lean:138-162 applyHoist
/// The cited `(Array.range ds.size).filter (target.contains ·)`: the moved
/// records' indices, increasing.
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

/// con-leche: ConLeche/Frontend/NatOpGround.lean:138-162 applyHoist
/// The cited `(List.range ds.size).mergeSort` at the key `(t, s, k)`, as the
/// bucket pass of the module note's deviation 2: at each position `t`, first
/// the moved records targeted at `t` (increasing original index, which is
/// dependency order), then the record `t` itself unless it is one of them.
pub fn hoist_order(n: usize, target: &HashMap<u64, u64>, moved: &Vec<u64>) -> Vec<u64> {
    let mut order: Vec<u64> = Vec::with_capacity(n);
    let nm = moved.len();
    let mut t: usize = 0;
    while t < n {
        let mut a: usize = 0;
        while a < nm {
            match target.get(&moved[a]) {
                Some(tt) => {
                    if *tt == (t as u64) {
                        order.push(moved[a]);
                    }
                }
                None => {}
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
/// The cited `(order.map (ds[·]!)).toArray`, by the module note's deviation 3:
/// a copy per record rather than a move.
pub fn hoist_reorder(ds: &Vec<Declaration>, order: &Vec<u64>) -> Vec<Declaration> {
    let n = order.len();
    let mut out: Vec<Declaration> = Vec::with_capacity(n);
    let mut i: usize = 0;
    while i < n {
        out.push(declaration_dup(&ds[order[i] as usize]));
        i += 1;
    }
    out
}

/// con-leche: ConLeche/Frontend/NatOpGround.lean:138-162 applyHoist
/// The cited `moved.flatMap fun k => (ds[k]!.names).toArray` — the driver's
/// receipt.
pub fn hoist_moved_names(ds: &Vec<Declaration>, moved: &Vec<u64>) -> Vec<Name> {
    let mut out: Vec<Name> = Vec::new();
    let n = moved.len();
    let mut a: usize = 0;
    while a < n {
        let ns = env::declaration_names(&ds[moved[a] as usize]);
        let m = ns.len();
        let mut j: usize = 0;
        while j < m {
            out.push(name::dup(&ns[j]));
            j += 1;
        }
        a += 1;
    }
    out
}

/// con-leche: ConLeche/Frontend/NatOpGround.lean:138-162 applyHoist
/// **The reorder**: a moved record sorts at its target, just ahead of the
/// operation record there (key `(t, 0, k)` against the operation's
/// `(t, 1, t)`); everything else keeps its position (`(k, 1, k)`).  Moved
/// records with the same target keep their relative order, which is dependency
/// order.
///
/// con-leche sorts with `List.mergeSort` rather than `Array.qsort` because
/// core proves `mergeSort_perm` and proves nothing about `qsort`; the keys are
/// pairwise distinct (each carries its own index), so the order is the same
/// one `qsort` produced — and the module note's deviation 2 says why the port
/// produces that order without a sort at all.
pub fn apply_hoist(
    ds: &Vec<Declaration>,
    target: &HashMap<u64, u64>,
) -> (Vec<Declaration>, Vec<Name>) {
    let moved = hoist_moved_idxs(ds.len(), target);
    let order = hoist_order(ds.len(), target, &moved);
    let out = hoist_reorder(ds, &order);
    let names = hoist_moved_names(ds, &moved);
    (out, names)
}

/// con-leche: ConLeche/Frontend/NatOpGround.lean:164-169 hoistNatOpGround
/// **The hoist.**  Returns the reordered records and the names of the records
/// moved (empty, and the vector untouched, when no operation's ground is
/// declared after it).
pub fn hoist_nat_op_ground(ds: Vec<Declaration>) -> (Vec<Declaration>, Vec<Name>) {
    let target = hoist_targets(&ds);
    if target.len() == 0 {
        (ds, Vec::new())
    } else {
        apply_hoist(&ds, &target)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::kernel::basis_builder::{bn, cnst, srt};
    use crate::kernel::env::{BasisKind, ConstantVal, ReducibilityHint};
    use crate::kernel::level;

    fn nm(s: &str) -> Name {
        bn(s.chars().map(|c| c as u32).collect())
    }

    fn dotted(a: &str, b: &str) -> Name {
        name::mk_str(nm(a), b.chars().map(|c| c as u32).collect())
    }

    fn defn(n: Name, body: Expr) -> Declaration {
        Declaration::DefnDecl(
            ConstantVal {
                name: n,
                level_params: Vec::new(),
                ty: srt(level::zero()),
            },
            body,
            ReducibilityHint::Regular(0),
        )
    }

    fn names_of(ds: &[Declaration]) -> Vec<String> {
        ds.iter()
            .flat_map(env::declaration_names)
            .map(|n| {
                let cps = crate::frontend::text::name_str(&n);
                cps.iter().filter_map(|c| char::from_u32(*c)).collect()
            })
            .collect()
    }

    /// The pass is a no-op on a stream whose ground precedes its operations,
    /// and the vector comes back untouched (the `target.isEmpty` arm).
    #[test]
    fn no_op_when_the_ground_precedes() {
        let ds = vec![
            defn(dotted("Nat", "ble"), srt(level::zero())),
            defn(dotted("Nat", "sub"), srt(level::zero())),
            defn(dotted("Nat", "shiftLeft"), srt(level::zero())),
        ];
        let (out, moved) = hoist_nat_op_ground(ds);
        assert!(moved.is_empty());
        assert_eq!(names_of(&out), vec!["Nat.ble", "Nat.sub", "Nat.shiftLeft"]);
    }

    /// A ground declared LATER is moved ahead of the operation, with its own
    /// closure.  `Nat.shiftLeft`'s ground is `Nat.ble`/`Nat.sub`
    /// (`core_k::nat_op_deps`), and `Nat.sub` here references `Helper`, so
    /// the closure takes that too.
    #[test]
    fn a_later_ground_is_hoisted_with_its_closure() {
        let ds = vec![
            defn(dotted("Nat", "shiftLeft"), srt(level::zero())),
            defn(dotted("Nat", "ble"), srt(level::zero())),
            defn(dotted("Nat", "sub"), cnst(nm("Helper"), Vec::new())),
            defn(nm("Helper"), srt(level::zero())),
        ];
        let (out, moved) = hoist_nat_op_ground(ds);
        let got = names_of(&out);
        let pos = |s: &str| got.iter().position(|x| x == s).unwrap();
        // the sort key is `(target, 0, original index)` for a moved record
        // and `(index, 1, index)` for the operation, so the three moved
        // records keep their relative stream order ahead of it
        assert_eq!(
            got,
            vec!["Nat.ble", "Nat.sub", "Helper", "Nat.shiftLeft"],
            "{:?}",
            got
        );
        assert!(pos("Helper") < pos("Nat.shiftLeft"));
        assert_eq!(moved.len(), 3);
    }

    /// `usedConsts` walks a DAG once per node: a shared node reached twice
    /// contributes its constant once.
    #[test]
    fn used_consts_visits_each_node_once() {
        let c = cnst(nm("C"), Vec::new());
        let shared = expr::app(expr::dup(&c), expr::dup(&c));
        let e = expr::app(expr::dup(&shared), expr::dup(&shared));
        let d = defn(nm("D"), e);
        let used = decl_used_consts(&d);
        // `C` once, plus nothing from the type (`Sort 0`)
        assert_eq!(used.len(), 1);
        assert!(name::beq(&used[0], &nm("C")));
    }

    /// A basis block declares no name and references nothing.
    #[test]
    fn a_basis_block_is_invisible_to_the_hoist() {
        let d = Declaration::BasisDecl(BasisKind::NatK);
        assert!(env::declaration_names(&d).is_empty());
        assert!(decl_used_consts(&d).is_empty());
    }

    /// `declaration_dup` copies the record: the names come back, and the
    /// `Expr` fields are the same shared nodes.
    #[test]
    fn a_copied_record_declares_the_same_names() {
        let d = defn(dotted("Nat", "sub"), cnst(nm("Helper"), Vec::new()));
        let c = declaration_dup(&d);
        assert_eq!(names_of(&[d]), names_of(&[c]));
    }
}
