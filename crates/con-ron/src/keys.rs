//! `std::collections` keys for `Expr` and `Name`: the two newtypes the
//! unverified crate needs and the verified core must not have.  No con-leche
//! file of its own.
//!
//! `con_ron_core::ron::hashmap` keys by its own `Hashable`/`Eq2` traits, and
//! `Expr` and `Name` implement both — so *inside* the core a table is keyed by
//! the value and no newtype exists.  This crate is outside DESIGN.md §3.4's
//! subset and uses `std::collections`, which wants `std::hash::Hash` and
//! `Eq`; `Expr` and `Name` implement neither, and giving them a `PartialEq`
//! would put `core::cmp::PartialEq` and a `StructuralPartialEq` impl into the
//! core's model (`ron/hashmap.rs`'s note on `Eq2`).  Hence the two wrappers.
//!
//! Before task #84 they lived in `crate::frontend::nat_op_ground`, beside the
//! ground hoist.  The ground hoist is in the verified core now and keys its
//! sets by `Expr` and `Name` directly; what is left here is the modeller's
//! use of them.
//!
//! **`ExprKey` keys by the node's ADDRESS**, where con-leche keys its own
//! `Std.HashSet ExprC` by VALUE.  That is sound here and costs nothing: the
//! export shares by index, so the DAG's nodes are distinct objects and address
//! identity is exactly the dedupe that makes a walk linear in the DAG; value
//! identity merges structurally equal *distinct* nodes too, so it is a
//! strictly coarser partition and visits no more nodes than this does, and
//! the one consumer left — the nested rung's `(ExprKey, u64)` instantiation
//! memo — observes only the term a hit returns.
//!
//! The *other* reason this newtype existed is **spent, and the record should
//! say so** (task #84).  It used to argue that a value-keyed set puts
//! `Expr.beq` on pairs that are not equal, and that on
//! `tests/e2e/tower_beqpair.ndjson` — con-leche task #240's shared depth-60
//! tower and the alternating pair of them — such a comparison spun for
//! minutes inside `expr::beq_go`.  Task #38 fixed the cause: `BeqMap` keeps a
//! *bucket* per key, so `(S,Q)` no longer evicts what `(S,P)` proved.
//! Re-measured at task #84 on that very shape, `expr::beq`, `decl_used_consts`
//! and `occurs_const_fast` are all **linear** in the depth — 0.18 ms at depth
//! 60 against 20 µs at depth 4 — which is why the verified core's ground hoist
//! keys its `seen` set by `Expr` and needs no address at all
//! (`con_ron_core::frontend::nat_op_ground`, and its own test
//! `the_tower_pair_does_not_blow_up_the_seen_table`).
//!
//! Nothing here dereferences a pointer (`con-ron-dump`'s `dag::census` keeps
//! the same discipline, task #19): the address is hashed and compared, never
//! read, and there is no `unsafe`.

use con_ron_core::kernel::expr::Expr;
use con_ron_core::kernel::expr::ExprNode;
use con_ron_core::kernel::name;
use con_ron_core::kernel::name::Name;

/// con-leche: none — `Std.HashSet ExprC`'s key, by the node's address (the
/// module note says why, and why the difference is invisible to the callers).
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
    /// module note says why).
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
