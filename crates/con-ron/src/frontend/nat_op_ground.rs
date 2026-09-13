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
//! Like the prelude and the projection rewrite, this is a pure
//! transformation of the parsed list below the verified fold: nothing in the
//! kernel or the proofs knows it happened.  The pass is a no-op — the vector
//! is returned as it is, no sort — on every stream whose ground precedes its
//! operations (the toolchain's own export order: `init`, Mathlib).
//!
//! Two deviations: `instance : Inhabited DeclC` (`:55`) has no Rust
//! counterpart — it exists for Lean's `ds[i]!` and Rust indexes a `Vec`
//! directly — and `usedConstsGo`'s `Std.HashSet ExprC` becomes a
//! `HashSet<ExprKey>` over the core's own `hash`/`beq`, which is the same
//! set (con-leche's `Hashable ExprC` IS `Expr.hash`, its `BEq` IS
//! `Expr.beq`).

use std::collections::{HashMap, HashSet};

use con_ron_core::cached::parsed_c::DeclC;
use con_ron_core::kernel::core_k;
use con_ron_core::kernel::env::ConstantInfo;
use con_ron_core::kernel::expr;
use con_ron_core::kernel::expr::{Expr, ExprKind, ExprNode};
use con_ron_core::kernel::name;
use con_ron_core::kernel::name::Name;

/// con-leche: none — `Std.HashSet ExprC`'s key.
///
/// **A deliberate deviation, and the reason for it.**  con-leche keys this set
/// by VALUE (its `Hashable ExprC` is `Expr.hash`, its `BEq ExprC` the
/// pointer-and-hash-guarded `Expr.beq`); this one keys it by the node's
/// ADDRESS.  Two reasons, and the second is a bug this port hit:
///
/// 1. The export shares by index, so the DAG's nodes are distinct objects and
///    address identity is exactly the dedupe that makes a walk linear in the
///    DAG.  Value identity merges structurally equal *distinct* nodes too, so
///    it visits no more nodes than this does — it is a strictly coarser
///    partition — and the only observable of the two walks that use this set
///    is a `false` (`occurs_const_go`) or the multiset of names in `acc`
///    (`used_consts_go`), which feeds `hoist_nat_op_ground`'s idempotent
///    stack pushes.
/// 2. `Expr.beq` memoises completed `true`s only, so a comparison that comes
///    out FALSE is re-walked in full — and on `tests/e2e/tower_beqpair.ndjson`
///    (con-leche task #240: a shared depth-60 tower and an alternating pair of
///    them, three arguments deep) a false comparison of two such towers is
///    exponential.  A hash table calls its key's `eq` whenever a probe's
///    truncated hash matches, so a VALUE-keyed set puts `Expr.beq` on pairs
///    that are NOT equal — measured on that fixture: one such probe spins for
///    minutes inside `expr::beq_go`.  Address equality cannot do that; it is
///    one machine-word comparison.
///
/// Nothing here dereferences a pointer (`con-ron-dump`'s `dag::census` keeps
/// the same discipline, task #19): the address is hashed and compared, never
/// read, and there is no `unsafe`.
pub struct ExprKey(pub Expr);

/// con-leche: none — the `Hash` half of `ExprKey`: the node's address.
impl std::hash::Hash for ExprKey {
    /// con-leche: none — the node's address as the hash.
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        state.write_usize(&*self.0 .0 as *const ExprNode as usize);
    }
}

/// con-leche: none — the `Eq` half of `ExprKey`: address identity.
impl PartialEq for ExprKey {
    /// con-leche: none — `Expr.beqPtr` without the structural fallback (the
    /// struct's note says why).
    fn eq(&self, other: &ExprKey) -> bool {
        &*self.0 .0 as *const ExprNode == &*other.0 .0 as *const ExprNode
    }
}

/// con-leche: none — address identity is an equivalence relation.
impl Eq for ExprKey {}

/// con-leche: none — `Std.HashMap Name`'s key, i.e. con-leche's `Hashable
/// Name`/`BEq Name` (`Name.hashData` and the pointer-guarded `Name.beq`).
pub struct NameKey(pub Name);

/// con-leche: none — the `Hash` half of `NameKey`.
impl std::hash::Hash for NameKey {
    /// con-leche: none — `Hashable Name`, i.e. `Name.hashData`.
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        state.write_u64(name::hash_data(&self.0));
    }
}

/// con-leche: none — the `Eq` half of `NameKey`.
impl PartialEq for NameKey {
    /// con-leche: none — `BEq Name`, i.e. the pointer-guarded `Name.beq`.
    fn eq(&self, other: &NameKey) -> bool {
        name::beq(&self.0, &other.0)
    }
}

/// con-leche: none — `NameKey`'s equality is `Name.beq`.
impl Eq for NameKey {}

/// con-leche: ConLeche/Frontend/NatOpGround.lean:57-62 DeclC.names
/// con-leche: CHANGED since 405d06b7 — re-port, re-test, re-prove nat_op_ground::decl_names_refines, then delete this line
/// The names a parsed declaration declares (the prelude index and the hoist's
/// name index; basis blocks are indexed by kind instead).
pub fn decl_names(d: &DeclC) -> Vec<Name> {
    match d {
        DeclC::AxiomDecl(cv)
        | DeclC::DefnDecl(cv, _, _)
        | DeclC::ThmDecl(cv, _)
        | DeclC::OpaqueDecl(cv, _) => vec![name::dup(&cv.name)],
        DeclC::IndDecl(block, _) => block
            .iter()
            .map(con_ron_core::kernel::env::constant_info_name)
            .collect(),
        DeclC::BasisDecl(_) => Vec::new(),
    }
}

/// con-leche: ConLeche/Frontend/NatOpGround.lean:54-77 usedConstsGo
/// con-leche: CHANGED since 405d06b7 — re-port, re-test, re-prove nat_op_ground::used_consts_go_refines, then delete this line
/// The constants an `Expr` DAG references, each node visited once.
/// Deviation: an explicit worklist rather than structural recursion —
/// `app-lam` reaches term depths in the thousands and the Lean recursion runs
/// on a 1 GiB stack the frontend thread does not have to reserve for this.
/// Visit order is preserved (children pushed so the first child is visited
/// first), because `acc`'s order is the hoist's tie-break.
pub fn used_consts_go(seen: &mut HashSet<ExprKey>, acc: &mut Vec<Name>, e: &Expr) {
    let mut stack: Vec<Expr> = vec![expr::dup(e)];
    while let Some(x) = stack.pop() {
        if !seen.insert(ExprKey(expr::dup(&x))) {
            continue;
        }
        match &x.0.kind {
            ExprKind::Const(n, _) => acc.push(name::dup(n)),
            ExprKind::App(f, a) => {
                stack.push(expr::dup(a));
                stack.push(expr::dup(f));
            }
            ExprKind::Lam(ty, b, _) | ExprKind::ForallE(ty, b, _) => {
                stack.push(expr::dup(b));
                stack.push(expr::dup(ty));
            }
            ExprKind::LetE(ty, v, b) => {
                stack.push(expr::dup(b));
                stack.push(expr::dup(v));
                stack.push(expr::dup(ty));
            }
            ExprKind::Proj(sn, _, sub) => {
                acc.push(name::dup(sn));
                stack.push(expr::dup(sub));
            }
            ExprKind::Fvar(_, ty) => stack.push(expr::dup(ty)),
            _ => {}
        }
    }
}

/// con-leche: ConLeche/Frontend/NatOpGround.lean:89-105 DeclC.usedConsts
/// con-leche: CHANGED since 405d06b7 — re-port, re-test, re-prove nat_op_ground::decl_used_consts_refines, then delete this line
/// The constants a parsed record references (types, values, recursor rule
/// right-hand sides; a basis block references nothing the stream declares).
pub fn decl_used_consts(d: &DeclC) -> Vec<Name> {
    let mut seen: HashSet<ExprKey> = HashSet::new();
    let mut acc: Vec<Name> = Vec::new();
    match d {
        DeclC::AxiomDecl(cv) => used_consts_go(&mut seen, &mut acc, &cv.ty),
        DeclC::DefnDecl(cv, v, _) | DeclC::ThmDecl(cv, v) | DeclC::OpaqueDecl(cv, v) => {
            used_consts_go(&mut seen, &mut acc, &cv.ty);
            used_consts_go(&mut seen, &mut acc, v);
        }
        DeclC::IndDecl(block, _) => {
            for ci in block {
                used_consts_go(
                    &mut seen,
                    &mut acc,
                    &con_ron_core::kernel::env::to_constant_val(ci).ty,
                );
                if let ConstantInfo::RecInfo(_, _, _, rules) = ci {
                    for r in rules {
                        used_consts_go(&mut seen, &mut acc, &r.rhs);
                    }
                }
            }
        }
        DeclC::BasisDecl(_) => {}
    }
    acc
}

/// con-leche: ConLeche/Frontend/NatOpGround.lean:97-104 isNatOpRecord
/// con-leche: CHANGED since 405d06b7 — re-port, re-test, re-prove nat_op_ground::is_nat_op_record_refines, then delete this line
/// The pinned `Nat` operation records whose ground the pass serves: the
/// pin-certified WF operations and the structural ones (whose `natOpDeps` are
/// in their own closures already — kept uniform).
pub fn is_nat_op_record(d: &DeclC) -> Option<Name> {
    match d {
        DeclC::DefnDecl(cv, _, _) => {
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

/// con-leche: ConLeche/Frontend/NatOpGround.lean:164-169 hoistNatOpGround
/// con-leche: CHANGED since 405d06b7 — re-port, re-test, re-prove nat_op_ground::hoist_nat_op_ground_refines, then delete this line
/// **The hoist.**  Returns the reordered records and the names of the records
/// moved (empty, and the vector untouched, when no operation's ground is
/// declared after it).
pub fn hoist_nat_op_ground(ds: Vec<DeclC>) -> (Vec<DeclC>, Vec<Name>) {
    // name ↦ the index of the record declaring it (the first, on a
    // duplicate — the fold rejects the second anyway)
    let mut idx: HashMap<NameKey, usize> = HashMap::new();
    for (i, d) in ds.iter().enumerate() {
        for n in decl_names(d) {
            idx.entry(NameKey(n)).or_insert(i);
        }
    }
    // moved record ↦ the earliest operation index it must precede
    let mut target: HashMap<usize, usize> = HashMap::new();
    for i in 0..ds.len() {
        let c = match is_nat_op_record(&ds[i]) {
            None => continue,
            Some(c) => c,
        };
        for g in core_k::nat_op_deps(&c) {
            let j = match idx.get(&NameKey(g)) {
                None => continue,
                Some(j) => *j,
            };
            if j <= i {
                continue;
            }
            // the closure of `j` within the records after `i`
            let mut stack: Vec<usize> = vec![j];
            while let Some(k) = stack.pop() {
                if let Some(t) = target.get(&k) {
                    if *t <= i {
                        continue;
                    }
                }
                target.insert(k, i);
                for n in decl_used_consts(&ds[k]) {
                    if let Some(m) = idx.get(&NameKey(n)) {
                        if *m > i && *m != k {
                            stack.push(*m);
                        }
                    }
                }
            }
        }
    }
    if target.is_empty() {
        return (ds, Vec::new());
    }
    // the order: a moved record sorts at its target, just ahead of the
    // operation record there (key `(t, 0, k)` against the operation's
    // `(t, 1, t)`); everything else keeps its position (`(k, 1, k)`).
    // Moved records with the same target keep their relative order, which is
    // dependency order.
    let key = |k: usize| -> (usize, usize, usize) {
        match target.get(&k) {
            Some(t) => (*t, 0, k),
            None => (k, 1, k),
        }
    };
    let mut order: Vec<usize> = (0..ds.len()).collect();
    order.sort_by_key(|k| key(*k));
    let mut moved: Vec<Name> = Vec::new();
    for k in 0..ds.len() {
        if target.contains_key(&k) {
            moved.extend(decl_names(&ds[k]));
        }
    }
    let mut slots: Vec<Option<DeclC>> = ds.into_iter().map(Some).collect();
    let out: Vec<DeclC> = order
        .into_iter()
        .map(|k| slots[k].take().expect("each index is used once"))
        .collect();
    (out, moved)
}

#[cfg(test)]
mod tests {
    use super::*;
    use con_ron_core::kernel::basis_builder::{bn, cnst, srt};
    use con_ron_core::kernel::env::{BasisKind, ConstantVal, ReducibilityHint};
    use con_ron_core::kernel::level;

    fn nm(s: &str) -> Name {
        bn(s.chars().map(|c| c as u32).collect())
    }

    fn dotted(a: &str, b: &str) -> Name {
        name::mk_str(nm(a), b.chars().map(|c| c as u32).collect())
    }

    fn defn(n: Name, body: Expr) -> DeclC {
        DeclC::DefnDecl(
            ConstantVal {
                name: n,
                level_params: Vec::new(),
                ty: srt(level::zero()),
            },
            body,
            ReducibilityHint::Regular(0),
        )
    }

    fn names_of(ds: &[DeclC]) -> Vec<String> {
        ds.iter()
            .flat_map(|d| decl_names(d))
            .map(|n| {
                // enough for the test: a one- or two-component name
                match &n.0.kind {
                    con_ron_core::kernel::name::NameKind::Str(p, s) => {
                        let tail: String = s.iter().filter_map(|c| char::from_u32(*c)).collect();
                        match &p.0.kind {
                            con_ron_core::kernel::name::NameKind::Str(_, ps) => {
                                let head: String =
                                    ps.iter().filter_map(|c| char::from_u32(*c)).collect();
                                format!("{}.{}", head, tail)
                            }
                            _ => tail,
                        }
                    }
                    _ => "?".to_string(),
                }
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
        assert_eq!(
            names_of(&out),
            vec!["Nat.ble", "Nat.sub", "Nat.shiftLeft"]
        );
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
        let shared = con_ron_core::kernel::expr::app(expr::dup(&c), expr::dup(&c));
        let e = con_ron_core::kernel::expr::app(expr::dup(&shared), expr::dup(&shared));
        let d = defn(nm("D"), e);
        let used = decl_used_consts(&d);
        // `C` once, plus nothing from the type (`Sort 0`)
        assert_eq!(used.len(), 1);
        assert!(name::beq(&used[0], &nm("C")));
    }

    /// A basis block declares no name and references nothing.
    #[test]
    fn a_basis_block_is_invisible_to_the_hoist() {
        let d = DeclC::BasisDecl(BasisKind::NatK);
        assert!(decl_names(&d).is_empty());
        assert!(decl_used_consts(&d).is_empty());
    }
}

#[cfg(test)]
mod beq_pair_finding {
    //! The finding of task #37, kept as an executable demonstration: the
    //! `tower_beqpair` shape (con-leche task #240) is EXPONENTIAL in
    //! `con-ron-core`'s `expr::beq`, because task #11's memo key mixes the two
    //! nodes' *hash words* where con-leche mixes their *addresses*.
    //!
    //! A shared ternary tower `S = g S S S` and an alternating pair
    //! `P = g P Q P` / `Q = g Q P Q` are all structurally equal, so they have
    //! the same `Expr.hash` at every level, so `beq_key(hash a, hash b)` is
    //! ONE key per level for all three pairings.  `probe_hit` then verifies
    //! the stored pair by identity, misses, and the walk is re-done: three
    //! full sub-walks per level, i.e. `3^depth`.  con-leche's address key
    //! gives the three pairings three different keys and two entries per
    //! level.
    //!
    //! Why no earlier task saw it: every `Expr` the port had been given came
    //! out of the Lean declaration dump of task #10 (retired at task #80),
    //! whose writer interns by VALUE,
    //! so `S`, `P` and `Q` arrive as ONE node and the pairing never happens.
    //! A Rust frontend builds the stream's own DAG, where they are three.
    //!
    //! This is a `con-ron-core` matter (task #37 may not touch that crate), so
    //! it is reported rather than fixed; DESIGN.md's task-#37 entry carries
    //! the numbers `beq_on_the_tower_pair_is_exponential` prints.
    use super::*;
    use con_ron_core::kernel::basis_builder::{bn, cnst};

    fn tri(g: &Expr, a: &Expr, b: &Expr, c: &Expr) -> Expr {
        expr::app(
            expr::app(expr::app(expr::dup(g), expr::dup(a)), expr::dup(b)),
            expr::dup(c),
        )
    }

    /// `(S_k, P_k)`: the shared tower and one of the alternating pair.
    fn towers(k: u32) -> (Expr, Expr) {
        let g = cnst(bn("g".chars().map(|c| c as u32).collect()), Vec::new());
        let z = cnst(bn("z".chars().map(|c| c as u32).collect()), Vec::new());
        let mut s = expr::dup(&z);
        let mut p = expr::dup(&z);
        let mut q = expr::dup(&z);
        for _ in 0..k {
            let s2 = tri(&g, &s, &s, &s);
            let p2 = tri(&g, &p, &q, &p);
            let q2 = tri(&g, &q, &p, &q);
            s = s2;
            p = p2;
            q = q2;
        }
        (s, p)
    }

    /// The towers really are structurally equal — `beq` says `true`, at a
    /// depth small enough for the exponential walk to finish.
    #[test]
    fn the_towers_are_structurally_equal() {
        let (s, p) = towers(6);
        assert!(expr::beq(&s, &p));
    }

    /// The cost table.  `cargo test -p con-ron -- --ignored --nocapture
    /// beq_on_the_tower_pair` prints it; it is not in the gate because it is a
    /// measurement, and an exponential one.
    #[test]
    #[ignore]
    fn beq_on_the_tower_pair_is_exponential() {
        for k in 6..15u32 {
            let (s, p) = towers(k);
            let t = std::time::Instant::now();
            let r = expr::beq(&s, &p);
            println!("depth {:2}  beq = {}  {:?}", k, r, t.elapsed());
        }
    }
}
