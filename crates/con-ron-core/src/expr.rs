//! Port of `ConLeche/Kernel/Expr.lean` — the checker's term representation.
//!
//! The `Level` half of that file (lines 35-139: the `Level` inductive, its
//! `Hashable`/`BEq` instances, `levelHasParam`, `levelsHaveParam`,
//! `levelHash` and `levelsHash`) was ported at task #3 and lives in
//! `crate::level`; this module is everything from `BinderMeta` on.
//!
//! Conventions, as in `name.rs` and `level.rs`: an `Expr` is an `Rc` tree
//! whose node stores the `@[computed_field] data` word, written by the smart
//! constructors below and by nothing else (DESIGN.md §3.2); arguments come in
//! by shared reference and results go out owned; Lean's `List` is a `Vec`
//! walked by an index (§3.3, §3.4 — no loops); the `Nat` indices con-leche
//! never lets grow (`bvar i`, `fvar idx`, `proj i`) are `u64` (§3.3).
//!
//! Two naming notes.  `const` is a Rust keyword, so the `.const` smart
//! constructor is `mk_const`; the other nine keep their constructor's name
//! (this is task #6's `modulo` rule).  `Expr.hash` is `hash`, and the stored
//! word itself is `data`.
//!
//! The packed word's arithmetic is transliterated with `wrapping_*`, because
//! Lean's `UInt64` `+`/`*` wrap: the port must be bit-exact here, since the
//! word is what `beq` rejects on and what the memo tables bucket by.

use crate::hashmap::Eq2;
use crate::hashmap::Hashable;
use crate::level;
use crate::level::Level;
use crate::name;
use crate::name::Name;
use crate::nat;
use crate::prop_when;
use crate::prop_when::PropWhen;
use std::rc::Rc;

// ---------------------------------------------------------------------------
// Binder metadata and literals (`Expr.lean:93-112`)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/Expr.lean:93-104 BinderMeta
/// The one datum a binder carries: the codomain prop-ness annotation, which
/// the untrusted annotate pass writes and the checker validates.
pub struct BinderMeta {
    pub pw: PropWhen,
}

/// con-leche: ConLeche/Kernel/Expr.lean:93-104 BinderMeta
/// The cited `deriving DecidableEq`, spelled out so that the comparison goes
/// through `PropWhen.decEq` rather than a derived structural walk.
pub fn binder_meta_beq(a: &BinderMeta, b: &BinderMeta) -> bool {
    prop_when::beq(&a.pw, &b.pw)
}

/// con-leche: ConLeche/Kernel/Expr.lean:93-104 BinderMeta
/// The cited `deriving Hashable`: the constructor index (a structure has
/// one, `0`) then `mixHash` folded over the fields
/// (`Lean/Elab/Deriving/Hashable.lean:50`).  Nothing in this file calls it —
/// the packed word hashes `m.pw` directly — but it is what a memo keyed by a
/// `BinderMeta` would probe with.
pub fn binder_meta_hash(m: &BinderMeta) -> u64 {
    name::mix_hash(0, prop_when::hash_pw(&m.pw))
}

/// con-leche: none — the value copy that Lean's value semantics hides (DESIGN.md §3.2)
/// Share a binder datum.
pub fn binder_meta_dup(m: &BinderMeta) -> BinderMeta {
    BinderMeta { pw: prop_when::dup(&m.pw) }
}

/// con-leche: ConLeche/Kernel/Expr.lean:108-112 Literal
/// The two literals.  Deviation (DESIGN.md §3.3): `natVal`'s `Nat` is
/// `crate::nat::Nat`, the crate's own bignum, and `strVal`'s `String` is a
/// `Vec<u32>` of code points.
pub enum Literal {
    NatVal(nat::Nat),
    StrVal(Vec<u32>),
}

/// con-leche: ConLeche/Kernel/Expr.lean:108-112 Literal
/// The cited `deriving DecidableEq`.
pub fn literal_beq(a: &Literal, b: &Literal) -> bool {
    match (a, b) {
        (Literal::NatVal(m), Literal::NatVal(n)) => nat::beq(m, n),
        (Literal::StrVal(s), Literal::StrVal(t)) => name::str_eq(s, t),
        _ => false,
    }
}

/// con-leche: ConLeche/Kernel/Expr.lean:108-112 Literal
/// The cited `deriving Hashable`: the constructor index then `mixHash` over
/// the field.  Deviation: the `Nat` and `String` hashes are the crate's own
/// (`nat::hash64`, `name::str_hash`), which already differ from Lean's — a
/// free choice by DESIGN.md §3.2, where a hash need only be a function of
/// the value.
pub fn literal_hash(l: &Literal) -> u64 {
    match l {
        Literal::NatVal(n) => name::mix_hash(0, nat::hash64(n)),
        Literal::StrVal(s) => name::mix_hash(1, name::str_hash(s)),
    }
}

/// con-leche: none — the value copy that Lean's value semantics hides (DESIGN.md §3.2)
/// Share a literal.  The `Nat` copies its limbs, the string its code points.
pub fn literal_dup(l: &Literal) -> Literal {
    match l {
        Literal::NatVal(n) => Literal::NatVal(nat::clone(n)),
        Literal::StrVal(s) => Literal::StrVal(str_copy(s)),
    }
}

/// con-leche: none — a `Vec<u32>` copy; Lean's strings are shared values (DESIGN.md §3.3)
/// The entry point of the index recursion below.
pub fn str_copy(s: &Vec<u32>) -> Vec<u32> {
    str_copy_from(s, 0, Vec::new())
}

/// con-leche: none — the index recursion behind `str_copy`
/// The accumulator is passed by value and returned: DESIGN.md §3.4 reserves
/// `&mut` for the state parameter (task #6).
pub fn str_copy_from(s: &Vec<u32>, i: usize, out: Vec<u32>) -> Vec<u32> {
    if i >= s.len() {
        out
    } else {
        let mut o: Vec<u32> = out;
        o.push(s[i]);
        str_copy_from(s, i + 1, o)
    }
}

// ---------------------------------------------------------------------------
// The packed node word (`Expr.lean:141-206`)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/Expr.lean:173-175 satRange
/// Saturation value of the two 15-bit range fields: a stored `satRange`
/// reads as "at least `satRange`".
pub fn sat_range() -> u64 {
    32767
}

/// con-leche: none — `max` on `UInt64`; Lean writes `max`, whose `Ord UInt64` instance is not in the Aeneas subset
/// The packed word's range fields join by `max`.
pub fn max_u64(a: u64, b: u64) -> u64 {
    if a < b {
        b
    } else {
        a
    }
}

/// con-leche: ConLeche/Kernel/Expr.lean:177-182 packData
/// Assemble the packed word: `hash` (32) ǀ reserved (1) ǀ `bvarB` (15) ǀ
/// `fvarB` (15) ǀ `hasLP` (1).  Deviation: `wrapping_mul`/`wrapping_add`
/// spell Lean's wrapping `UInt64` arithmetic, which plain `*`/`+` would turn
/// into an Aeneas `fail` on an out-of-range field.
pub fn pack_data(h: u64, b: u64, f: u64, lp: bool) -> u64 {
    let t: u64 = if lp { 1 } else { 0 };
    let hs: u64 = h.wrapping_mul(4294967296);
    let bs: u64 = b.wrapping_mul(65536);
    let fs: u64 = f.wrapping_mul(2);
    hs.wrapping_add(bs).wrapping_add(fs).wrapping_add(t)
}

/// con-leche: ConLeche/Kernel/Expr.lean:184-185 hashOfData
/// Hash field of a packed word (bits 63…32).
pub fn hash_of_data(w: u64) -> u64 {
    w / 4294967296
}

/// con-leche: ConLeche/Kernel/Expr.lean:187-188 bvarOfData
/// Loose-bvar-bound field of a packed word (bits 30…16).
pub fn bvar_of_data(w: u64) -> u64 {
    w / 65536 % 32768
}

/// con-leche: ConLeche/Kernel/Expr.lean:190-191 fvarOfData
/// Fvar-range field of a packed word (bits 15…1).
pub fn fvar_of_data(w: u64) -> u64 {
    w / 2 % 32768
}

/// con-leche: ConLeche/Kernel/Expr.lean:193-194 lpOfData
/// Has-level-param field of a packed word (bit 0).
pub fn lp_of_data(w: u64) -> bool {
    w % 2 == 1
}

/// con-leche: ConLeche/Kernel/Expr.lean:196-197 hash32
/// Truncate a mixed hash to the packed word's 32 bits.
pub fn hash32(w: u64) -> u64 {
    w % 4294967296
}

/// con-leche: ConLeche/Kernel/Expr.lean:199-200 satSucc
/// A leaf's range field: `n + 1`, saturating.  Deviation: Lean's
/// `min (n + 1) satRange` is on a `Nat`; on a `u64` the `n + 1` would
/// overflow at `u64::MAX`, so the saturation test comes first — the same
/// function of the same value, for every `u64`.
pub fn sat_succ(n: u64) -> u64 {
    if n >= 32766 {
        32767
    } else {
        n + 1
    }
}

/// con-leche: ConLeche/Kernel/Expr.lean:202-206 satPred
/// A binder's range field: the body's bound less one, saturating (a
/// saturated body keeps a saturated bound — the stored value means "at
/// least", and subtracting from it would under-approximate).
pub fn sat_pred(x: u64) -> u64 {
    if x == 32767 {
        32767
    } else if x == 0 {
        0
    } else {
        x - 1
    }
}

// ---------------------------------------------------------------------------
// The term (`Expr.lean:285-403`)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/Expr.lean:285-403 Expr
/// The ten constructors of `inductive Expr`; the cited
/// `@[computed_field] data` word sits in `ExprNode` (DESIGN.md §3.2).
/// Deviation: the `Nat` indices are `u64` (§3.3), and `const`'s `List Level`
/// is a `Vec<Level>`.
pub enum ExprKind {
    Bvar(u64),
    Fvar(u64, Expr),
    Sort(Level),
    Const(Name, Vec<Level>),
    App(Expr, Expr),
    Lam(Expr, Expr, BinderMeta),
    ForallE(Expr, Expr, BinderMeta),
    LetE(Expr, Expr, Expr),
    Lit(Literal),
    Proj(Name, u64, Expr),
}

/// con-leche: ConLeche/Kernel/Expr.lean:285-403 Expr
/// The heap node of an `Expr`: the cited inductive's `@[computed_field]
/// data` beside the constructor data.
pub struct ExprNode {
    pub data: u64,
    pub kind: ExprKind,
}

/// con-leche: ConLeche/Kernel/Expr.lean:285-403 Expr
/// A kernel expression, as an `Rc` tree — Lean's value semantics made
/// sharing (DESIGN.md §3.2).
pub struct Expr(pub Rc<ExprNode>);

/// con-leche: ConLeche/Kernel/Expr.lean:285-403 Expr
/// The cached `@[computed_field] data`, an `O(1)` field read.
pub fn data(e: &Expr) -> u64 {
    e.0.data
}

/// con-leche: none — the `Rc` bump that Lean's value semantics hides (DESIGN.md §3.2)
/// Share a term.
pub fn dup(e: &Expr) -> Expr {
    Expr(Rc::clone(&e.0))
}

/// con-leche: ConLeche/Kernel/Expr.lean:285-403 Expr
/// `Expr.bvar`, with the cited `data` equation
/// `packData (hash32 (mixHash 3 (hash i))) (satSucc i) 0 false`.
pub fn bvar(i: u64) -> Expr {
    let h: u64 = hash32(name::mix_hash(3, name::nat_hash(i)));
    let d: u64 = pack_data(h, sat_succ(i), 0, false);
    Expr(Rc::new(ExprNode { data: d, kind: ExprKind::Bvar(i) }))
}

/// con-leche: ConLeche/Kernel/Expr.lean:285-403 Expr
/// `Expr.fvar`: hash tag 5; the fvar range is `satSucc idx`, the bvar bound
/// is `0` (a type annotation is never descended by the abstraction walks)
/// and the level-param bit is the type's.
pub fn fvar(idx: u64, ty: Expr) -> Expr {
    let dt: u64 = data(&ty);
    let h: u64 = hash32(name::mix_hash(
        5,
        name::mix_hash(name::nat_hash(idx), hash_of_data(dt)),
    ));
    let d: u64 = pack_data(h, 0, sat_succ(idx), lp_of_data(dt));
    Expr(Rc::new(ExprNode { data: d, kind: ExprKind::Fvar(idx, ty) }))
}

/// con-leche: ConLeche/Kernel/Expr.lean:285-403 Expr
/// `Expr.sort`: hash tag 7 over the level's own cached hash; both ranges are
/// `0` and the level-param bit is `levelHasParam u`.
pub fn sort(u: Level) -> Expr {
    let h: u64 = hash32(name::mix_hash(7, level::level_hash(&u)));
    let d: u64 = pack_data(h, 0, 0, level::level_has_param(&u));
    Expr(Rc::new(ExprNode { data: d, kind: ExprKind::Sort(u) }))
}

/// con-leche: ConLeche/Kernel/Expr.lean:285-403 Expr
/// `Expr.const`: hash tag 11 over the name's hash and `levelsHash us`.
/// Deviation: `const` is a Rust keyword, so the smart constructor is
/// `mk_const`.
pub fn mk_const(n: Name, us: Vec<Level>) -> Expr {
    let h: u64 = hash32(name::mix_hash(
        11,
        name::mix_hash(name::hash_data(&n), level::levels_hash(&us)),
    ));
    let d: u64 = pack_data(h, 0, 0, level::levels_have_param(&us));
    Expr(Rc::new(ExprNode { data: d, kind: ExprKind::Const(n, us) }))
}

/// con-leche: ConLeche/Kernel/Expr.lean:285-403 Expr
/// `Expr.app`: hash tag 17; both ranges are the componentwise `max` and the
/// level-param bit the disjunction.
pub fn app(f: Expr, a: Expr) -> Expr {
    let df: u64 = data(&f);
    let da: u64 = data(&a);
    let h: u64 = hash32(name::mix_hash(
        17,
        name::mix_hash(hash_of_data(df), hash_of_data(da)),
    ));
    let d: u64 = pack_data(
        h,
        max_u64(bvar_of_data(df), bvar_of_data(da)),
        max_u64(fvar_of_data(df), fvar_of_data(da)),
        lp_of_data(df) || lp_of_data(da),
    );
    Expr(Rc::new(ExprNode { data: d, kind: ExprKind::App(f, a) }))
}

/// con-leche: ConLeche/Kernel/Expr.lean:285-403 Expr
/// `Expr.lam`: hash tag 19 over the type, the body and the binder datum; the
/// bvar bound drops the bound occurrence (`satPred` on the body's), the fvar
/// range does not, and the level-param bit picks up `m.pw.hasParams`.
pub fn lam(ty: Expr, body: Expr, m: BinderMeta) -> Expr {
    let dt: u64 = data(&ty);
    let db: u64 = data(&body);
    let h: u64 = hash32(name::mix_hash(
        19,
        name::mix_hash(
            hash_of_data(dt),
            name::mix_hash(hash_of_data(db), prop_when::hash_pw(&m.pw)),
        ),
    ));
    let d: u64 = pack_data(
        h,
        max_u64(bvar_of_data(dt), sat_pred(bvar_of_data(db))),
        max_u64(fvar_of_data(dt), fvar_of_data(db)),
        lp_of_data(dt) || lp_of_data(db) || prop_when::has_params(&m.pw),
    );
    Expr(Rc::new(ExprNode { data: d, kind: ExprKind::Lam(ty, body, m) }))
}

/// con-leche: ConLeche/Kernel/Expr.lean:285-403 Expr
/// `Expr.forallE`: `lam`'s equation with hash tag 23.
pub fn forall_e(ty: Expr, body: Expr, m: BinderMeta) -> Expr {
    let dt: u64 = data(&ty);
    let db: u64 = data(&body);
    let h: u64 = hash32(name::mix_hash(
        23,
        name::mix_hash(
            hash_of_data(dt),
            name::mix_hash(hash_of_data(db), prop_when::hash_pw(&m.pw)),
        ),
    ));
    let d: u64 = pack_data(
        h,
        max_u64(bvar_of_data(dt), sat_pred(bvar_of_data(db))),
        max_u64(fvar_of_data(dt), fvar_of_data(db)),
        lp_of_data(dt) || lp_of_data(db) || prop_when::has_params(&m.pw),
    );
    Expr(Rc::new(ExprNode { data: d, kind: ExprKind::ForallE(ty, body, m) }))
}

/// con-leche: ConLeche/Kernel/Expr.lean:285-403 Expr
/// `Expr.letE`: hash tag 29 over type, value and body; only the body is
/// under the binder, so only its bvar bound is `satPred`ed.
pub fn let_e(ty: Expr, value: Expr, body: Expr) -> Expr {
    let dt: u64 = data(&ty);
    let dv: u64 = data(&value);
    let db: u64 = data(&body);
    let h: u64 = hash32(name::mix_hash(
        29,
        name::mix_hash(
            hash_of_data(dt),
            name::mix_hash(hash_of_data(dv), hash_of_data(db)),
        ),
    ));
    let d: u64 = pack_data(
        h,
        max_u64(
            max_u64(bvar_of_data(dt), bvar_of_data(dv)),
            sat_pred(bvar_of_data(db)),
        ),
        max_u64(max_u64(fvar_of_data(dt), fvar_of_data(dv)), fvar_of_data(db)),
        lp_of_data(dt) || lp_of_data(dv) || lp_of_data(db),
    );
    Expr(Rc::new(ExprNode { data: d, kind: ExprKind::LetE(ty, value, body) }))
}

/// con-leche: ConLeche/Kernel/Expr.lean:285-403 Expr
/// `Expr.lit`: hash tag 31; a literal is closed, so both ranges are `0` and
/// the level-param bit is `false`.
pub fn lit(l: Literal) -> Expr {
    let h: u64 = hash32(name::mix_hash(31, literal_hash(&l)));
    let d: u64 = pack_data(h, 0, 0, false);
    Expr(Rc::new(ExprNode { data: d, kind: ExprKind::Lit(l) }))
}

/// con-leche: ConLeche/Kernel/Expr.lean:285-403 Expr
/// `Expr.proj`: hash tag 37 over the structure name, the field index and the
/// subterm; the ranges and the level-param bit are the subterm's unchanged.
pub fn proj(struct_name: Name, idx: u64, e: Expr) -> Expr {
    let de: u64 = data(&e);
    let h: u64 = hash32(name::mix_hash(
        37,
        name::mix_hash(
            name::hash_data(&struct_name),
            name::mix_hash(name::nat_hash(idx), hash_of_data(de)),
        ),
    ));
    let d: u64 = pack_data(h, bvar_of_data(de), fvar_of_data(de), lp_of_data(de));
    Expr(Rc::new(ExprNode {
        data: d,
        kind: ExprKind::Proj(struct_name, idx, e),
    }))
}

// ---------------------------------------------------------------------------
// The packed word's accessors (`Expr.lean:405-440`)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/Expr.lean:417-421 Expr.hash
/// The node's 32-bit hash (`O(1)`).
pub fn hash(e: &Expr) -> u64 {
    hash_of_data(data(e))
}

/// con-leche: ConLeche/Kernel/Expr.lean:423-425 Expr.hasLP
/// Has-level-param: is level instantiation ever non-trivial here?  One bit,
/// so this read is *exact*.
pub fn has_lp(e: &Expr) -> bool {
    lp_of_data(data(e))
}

/// con-leche: ConLeche/Kernel/Expr.lean:427-428 Expr.bvarBRaw
/// The stored loose-bvar bound, saturating at `satRange`.  Deviation: a
/// `u64` rather than the `Nat` the cited `.toNat` produces (DESIGN.md §3.3).
/// The *exact* accessor `Expr.bvarB`, which recovers exactness on the
/// saturated branch with a memoized walk, lives in `Kernel/ExprOps.lean` and
/// is not part of this file.
pub fn bvar_b_raw(e: &Expr) -> u64 {
    bvar_of_data(data(e))
}

/// con-leche: ConLeche/Kernel/Expr.lean:430-431 Expr.fvarBRaw
/// The stored fvar range, saturating at `satRange`.
pub fn fvar_b_raw(e: &Expr) -> u64 {
    fvar_of_data(data(e))
}

// ---------------------------------------------------------------------------
// Equality (`Expr.lean:678-988`)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/Expr.lean:729-737 Expr.beqRecursive
/// `true` for the nodes whose comparison recurses.  In con-leche this is the
/// pair memo's gate; here nothing reads it (the memo is not ported, see
/// `beq_go`), but it is one line and keeping it in step with its source is
/// what a later measurement would start from.
pub fn beq_recursive(e: &Expr) -> bool {
    match &e.0.kind {
        ExprKind::Fvar(_, _) => true,
        ExprKind::App(_, _) => true,
        ExprKind::Lam(_, _, _) => true,
        ExprKind::ForallE(_, _, _) => true,
        ExprKind::LetE(_, _, _) => true,
        ExprKind::Proj(_, _, _) => true,
        _ => false,
    }
}

/// con-leche: ConLeche/Kernel/Expr.lean:955-960 Expr.beqMemo
/// The pointer test behind the cited `withPtrEq`.  Deviation: modeled as
/// `false` in the generated Lean (DESIGN.md §3.2), where the reflexivity of
/// the walk is what discharges the fast path.
pub fn ptr_eq(a: &Expr, b: &Expr) -> bool {
    Rc::ptr_eq(&a.0, &b.0)
}

/// con-leche: none — `List Level` equality (`us == vs` in `beqGo`'s `.const` arm)
/// The entry point of the index recursion below.
pub fn levels_beq(ls: &Vec<Level>, rs: &Vec<Level>) -> bool {
    if ls.len() != rs.len() {
        false
    } else {
        levels_beq_from(ls, rs, 0)
    }
}

/// con-leche: none — the index recursion behind `levels_beq`
/// Lean's `List.beq` over `BEq Level`; no loops (DESIGN.md §3.4).
pub fn levels_beq_from(ls: &Vec<Level>, rs: &Vec<Level>, i: usize) -> bool {
    if i >= ls.len() {
        true
    } else if level::beq(&ls[i], &rs[i]) {
        levels_beq_from(ls, rs, i + 1)
    } else {
        false
    }
}

/// con-leche: ConLeche/Kernel/Expr.lean:818-949 Expr.beqGo
/// The structural descent, in the official kernel's shape: pointer identity,
/// then the computed word (a mismatch *is* an inequality), then the
/// constructor cases in the cited arm order.
///
/// **Deviation (DESIGN.md §3.2, the standing ruling).**  con-leche's
/// address-keyed pair memo is *not* ported: `EqPair`, `BeqMap`, `beqKey`,
/// `beqBudget`, `BeqRes`/`BeqOut`, `withAddr`, `ptrDec`, `probeHit` and the
/// `finish` write-back all fall away, and with them the `fuel` and `map`
/// parameters and the `Decidable`-valued result.  Aeneas has no addresses,
/// so an address-keyed cache cannot be modeled at all; what is left is
/// exactly the three steps above, which is what §3.2 licenses.  The pointer
/// fast path is kept at every level of the descent, as in `name::beq` and
/// `level::beq`, and its transparency is the reflexivity obligation §3.2
/// states.  Should measurement want the pair memo back, it returns as one
/// opaque function with a trust argument, not as this function's parameters.
pub fn beq_go(a: &Expr, b: &Expr) -> bool {
    if ptr_eq(a, b) {
        true
    } else if data(a) != data(b) {
        false
    } else {
        match (&a.0.kind, &b.0.kind) {
            (ExprKind::Bvar(i), ExprKind::Bvar(j)) => i == j,
            (ExprKind::Fvar(i, t), ExprKind::Fvar(j, u)) => {
                if i == j {
                    beq_go(t, u)
                } else {
                    false
                }
            }
            (ExprKind::Sort(u), ExprKind::Sort(v)) => level::beq(u, v),
            (ExprKind::Const(n, us), ExprKind::Const(m, vs)) => {
                if name::beq(n, m) {
                    levels_beq(us, vs)
                } else {
                    false
                }
            }
            (ExprKind::App(f, x), ExprKind::App(g, y)) => {
                if beq_go(f, g) {
                    beq_go(x, y)
                } else {
                    false
                }
            }
            (ExprKind::Lam(t1, b1, m1), ExprKind::Lam(t2, b2, m2)) => {
                if binder_meta_beq(m1, m2) {
                    if beq_go(t1, t2) {
                        beq_go(b1, b2)
                    } else {
                        false
                    }
                } else {
                    false
                }
            }
            (ExprKind::ForallE(t1, b1, m1), ExprKind::ForallE(t2, b2, m2)) => {
                if binder_meta_beq(m1, m2) {
                    if beq_go(t1, t2) {
                        beq_go(b1, b2)
                    } else {
                        false
                    }
                } else {
                    false
                }
            }
            (ExprKind::LetE(t1, v1, b1), ExprKind::LetE(t2, v2, b2)) => {
                if beq_go(t1, t2) {
                    if beq_go(v1, v2) {
                        beq_go(b1, b2)
                    } else {
                        false
                    }
                } else {
                    false
                }
            }
            (ExprKind::Lit(l1), ExprKind::Lit(l2)) => literal_beq(l1, l2),
            (ExprKind::Proj(s1, i1, e1), ExprKind::Proj(s2, i2, e2)) => {
                if name::beq(s1, s2) {
                    if i1 == i2 {
                        beq_go(e1, e2)
                    } else {
                        false
                    }
                } else {
                    false
                }
            }
            _ => false,
        }
    }
}

/// con-leche: ConLeche/Kernel/Expr.lean:955-960 Expr.beqMemo
/// con-leche: ConLeche/Kernel/Expr.lean:972-976 Expr.beq
/// `Expr.beqMemo` is the *executed* `Expr.beq` (`@[csimp]`-substituted):
/// pointer test, computed-word test, then the descent.  Deviation: the
/// descent is the memo-free `beq_go` above, and `beqDec`, `beqBudget` and
/// the `Decidable`-valued plumbing are gone with it; `beq_go` opens with the
/// same two guards, so this is the cited composition with the state
/// threading erased.
pub fn beq(a: &Expr, b: &Expr) -> bool {
    beq_go(a, b)
}

// ---------------------------------------------------------------------------
// The `bvar` smart constructor (`Expr.lean:990-1037`)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/Expr.lean:1022-1023 Expr.bvarPoolSize
/// Size of con-leche's static `bvar` pool.  Kept for the record; nothing
/// here reads it, because the pool itself is not ported (see `mk_bvar`).
pub fn bvar_pool_size() -> u64 {
    4096
}

/// con-leche: ConLeche/Kernel/Expr.lean:1025-1026 Expr.bvarPool
/// con-leche: ConLeche/Kernel/Expr.lean:1028-1031 Expr.mkBvar
/// con-leche: ConLeche/Kernel/Expr.lean:1033-1037 Expr.mkBvar_eq
/// The `bvar` smart constructor.
///
/// **Deviation: the pool is not ported.**  `bvarPool` is a closed top-level
/// `def` of type `Array Expr` that Lean's runtime builds once at module
/// initialization and marks persistent.  Rust has no such thing inside the
/// Aeneas subset: a `static`/`const` cannot allocate an `Rc` tree, and the
/// lazy alternatives (`OnceLock`, `lazy_static`, an `unsafe` mutable
/// `static`) are all outside DESIGN.md §3.4 — and Charon would in any case
/// have to model a global whose value is an allocation performed before
/// `main`.  Threading a pool through the checker's state instead would
/// change every signature below this one, for a pure allocation win.
///
/// The cited `mkBvar_eq` is the transparency argument that makes dropping it
/// free: `mkBvar i = .bvar i` on the Lean side, so the pooled and the fresh
/// node are the same value and no statement anywhere changes.  What is lost
/// is the allocation saving; it can come back in P1.6 as a Rust-side arena
/// without touching the model, since the model is `.bvar i` either way.
pub fn mk_bvar(i: u64) -> Expr {
    bvar(i)
}

/* Not ported from `Expr.lean` (DESIGN.md §3.2 and §3.1):
   * the pair memo and everything that exists only for it — `EqPair` (:744),
     `EqPair.dflt` (:753), `BeqMap` (:756), `beqKey` (:764), `beqBudget`
     (:773), `BeqRes` (:777), `BeqOut` (:786), `BeqOut.mk` (:788),
     `withAddr` (:795), `ptrDec` (:801), `probeHit` (:809) and `beqDec`
     (:952).  §3.2's standing ruling: Aeneas has no addresses, so an
     address-keyed cache cannot be modeled.  (`bvarPool` is dropped too, but
     it is *cited* on `mk_bvar` above, where its deviation is argued.)
   * every `theorem` — the packing roundtrip (:210-283), the
     constructor-wise range and `hasLP` equations (:450-675), `beqMemo_eq`
     (:965), `mkBvar_eq` (:1033) — plus the `@[csimp]` lemma
     `beq_eq_beqMemo` (:980) and the `LawfulBEq Expr` instance (:986).
     These are the *spec* this port will be proved against.
   * `deriving Repr` and the `Repr` instances: rendering only, and §3.1 says
     message strings need not match.
   * `deriving Inhabited` on `Expr` and `instance : Inhabited BinderMeta`
     (:106): Lean needs a default for `Array.get!`-style partiality; the port
     does not, since `Vec` indexing is checked in the model.
   * the `Level` half (:35-139) — ported at task #3, in `crate::level`.
   * the accessors this file's docstring points at but does not contain
     (`Expr.bvarB`, `Expr.fvarB`, `bvarBoundMemo`, `fvarRangeMemo`, and the
     `isApp`/`getAppFn` family) live in `Kernel/ExprOps.lean`, a later
     task. */

// ---------------------------------------------------------------------------
// The hash-map dictionaries (`crate::hashmap`'s own traits, task #7)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/Expr.lean:435-440 _
/// The cited `instance : Hashable Expr := ⟨Expr.hash⟩`, as the key
/// dictionary of `crate::hashmap` — what `memoE`/`memoB` and every other
/// `Expr`-keyed table will probe with.  Deviation: `Hashable` is our own
/// one-method trait rather than Lean's class (task #7).
impl Hashable for Expr {
    /// con-leche: ConLeche/Kernel/Expr.lean:417-421 Expr.hash
    /// The stored word's hash field, an `O(1)` read.
    fn hash64(&self) -> u64 {
        hash(self)
    }
}

/// con-leche: ConLeche/Kernel/Expr.lean:983 _
/// The cited `instance : BEq Expr := ⟨Expr.beq⟩`, as the key dictionary of
/// `crate::hashmap`.  Deviation: `Eq2` is our own one-method trait rather
/// than `core::cmp::PartialEq` — which is exactly what lets the instance be
/// `beq` with its pointer and computed-word fast paths (task #7).
impl Eq2 for Expr {
    /// con-leche: ConLeche/Kernel/Expr.lean:972-976 Expr.beq
    /// `Expr.beq`, i.e. the `@[csimp]`-substituted `Expr.beqMemo`.
    fn eq2(&self, other: &Self) -> bool {
        beq(self, other)
    }
}

#[cfg(test)]
mod tests {
    use crate::expr;
    use crate::expr::BinderMeta;
    use crate::expr::Expr;
    use crate::expr::ExprKind;
    use crate::expr::Literal;
    use crate::hashmap::Eq2;
    use crate::hashmap::Hashable;
    use crate::level;
    use crate::level::Level;
    use crate::name;
    use crate::name::Name;
    use crate::nat;
    use crate::prop_when;

    /// A single `str` component under `anonymous` — `nm("foo")` is `` `foo ``.
    fn nm(s: &str) -> Name {
        let cs: Vec<u32> = s.chars().map(|c| c as u32).collect();
        name::mk_str(name::anonymous(), cs)
    }

    fn cps(s: &str) -> Vec<u32> {
        s.chars().map(|c| c as u32).collect()
    }

    /// `BinderMeta` with the `never` datum — the parser's default.
    fn bm_never() -> BinderMeta {
        BinderMeta { pw: prop_when::never() }
    }

    /// `BinderMeta` claiming "prop when these parameters are zero".
    fn bm(ps: &[&str]) -> BinderMeta {
        let mut v: Vec<Name> = Vec::new();
        for s in ps {
            v.push(nm(s));
        }
        BinderMeta { pw: prop_when::if_all_zero(v) }
    }

    /// A representative battery of terms, each built from scratch.
    fn battery() -> Vec<Expr> {
        let mut v: Vec<Expr> = Vec::new();
        v.push(expr::bvar(0));
        v.push(expr::bvar(7));
        v.push(expr::fvar(3, expr::sort(level::zero())));
        v.push(expr::sort(level::zero()));
        v.push(expr::sort(level::succ(level::param(nm("u")))));
        v.push(expr::mk_const(nm("Nat"), Vec::new()));
        v.push(expr::mk_const(
            nm("List"),
            vec![level::param(nm("u")), level::zero()],
        ));
        v.push(expr::app(
            expr::mk_const(nm("Nat.succ"), Vec::new()),
            expr::bvar(0),
        ));
        v.push(expr::lam(expr::sort(level::zero()), expr::bvar(0), bm_never()));
        v.push(expr::forall_e(
            expr::sort(level::zero()),
            expr::bvar(1),
            bm(&["u"]),
        ));
        v.push(expr::let_e(
            expr::sort(level::zero()),
            expr::bvar(2),
            expr::bvar(0),
        ));
        v.push(expr::lit(Literal::NatVal(nat::from_u64(42))));
        v.push(expr::lit(Literal::StrVal(cps("hello"))));
        v.push(expr::proj(nm("Prod"), 1, expr::bvar(0)));
        v
    }

    // -----------------------------------------------------------------------
    // The packed word
    // -----------------------------------------------------------------------

    #[test]
    fn the_packed_word_round_trips() {
        // The four fields come back exactly, for every combination of a
        // 32-bit hash, two 15-bit ranges and the flag.
        let hs: [u64; 6] = [0, 1, 65535, 65536, 2147483648, 4294967295];
        let bs: [u64; 6] = [0, 1, 255, 32766, 32767, 12345];
        let fs: [u64; 6] = [0, 1, 4096, 32766, 32767, 777];
        for h in hs.iter() {
            for b in bs.iter() {
                for f in fs.iter() {
                    for lp in [false, true].iter() {
                        let w = expr::pack_data(*h, *b, *f, *lp);
                        assert_eq!(expr::hash_of_data(w), *h);
                        assert_eq!(expr::bvar_of_data(w), *b);
                        assert_eq!(expr::fvar_of_data(w), *f);
                        assert_eq!(expr::lp_of_data(w), *lp);
                        // Bit 31 is reserved and stays clear.
                        assert_eq!(w / 2147483648 % 2, 0);
                    }
                }
            }
        }
    }

    #[test]
    fn hash32_and_pack_data_agree_on_the_hash_field() {
        // `hashOfData (packData h …) = hash32 h`, the cited roundtrip lemma:
        // a wider `h` is truncated by the multiply, exactly as `hash32` does.
        let ws: [u64; 5] = [0, 1, 4294967295, 4294967296, 0x0123456789abcdef];
        for w in ws.iter() {
            let packed = expr::pack_data(expr::hash32(*w), 5, 6, true);
            assert_eq!(expr::hash_of_data(packed), expr::hash32(*w));
            assert_eq!(expr::hash32(*w), *w % 4294967296);
        }
    }

    #[test]
    fn sat_succ_and_sat_pred_saturate_at_32767() {
        assert_eq!(expr::sat_range(), 32767);
        assert_eq!(expr::sat_succ(0), 1);
        assert_eq!(expr::sat_succ(32764), 32765);
        assert_eq!(expr::sat_succ(32765), 32766);
        assert_eq!(expr::sat_succ(32766), 32767);
        assert_eq!(expr::sat_succ(32767), 32767);
        assert_eq!(expr::sat_succ(1000000), 32767);
        assert_eq!(expr::sat_succ(u64::MAX), 32767);
        assert_eq!(expr::sat_pred(0), 0);
        assert_eq!(expr::sat_pred(1), 0);
        assert_eq!(expr::sat_pred(32766), 32765);
        assert_eq!(expr::sat_pred(32767), 32767);
        // Every stored range stays inside its 15-bit field.
        for n in [0u64, 1, 32766, 32767, 99999, u64::MAX].iter() {
            assert!(expr::sat_succ(*n) < 32768);
            assert!(expr::sat_pred(expr::sat_succ(*n)) < 32768);
        }
    }

    #[test]
    fn bvar_b_saturates_at_32767() {
        // A leaf below the bound is exact...
        assert_eq!(expr::bvar_b_raw(&expr::bvar(0)), 1);
        assert_eq!(expr::bvar_b_raw(&expr::bvar(4095)), 4096);
        assert_eq!(expr::bvar_b_raw(&expr::bvar(32765)), 32766);
        // ... and from `satRange - 1` on it pins to `satRange`.
        assert_eq!(expr::bvar_b_raw(&expr::bvar(32766)), 32767);
        assert_eq!(expr::bvar_b_raw(&expr::bvar(32767)), 32767);
        assert_eq!(expr::bvar_b_raw(&expr::bvar(1000000)), 32767);
        // A binder drops one — but a saturated body stays saturated, since
        // the stored value means "at least".
        let ty = expr::sort(level::zero());
        let deep = expr::lam(expr::dup(&ty), expr::bvar(1000000), bm_never());
        assert_eq!(expr::bvar_b_raw(&deep), 32767);
        let shallow = expr::lam(expr::dup(&ty), expr::bvar(5), bm_never());
        assert_eq!(expr::bvar_b_raw(&shallow), 5);
        let closed = expr::lam(expr::dup(&ty), expr::bvar(0), bm_never());
        assert_eq!(expr::bvar_b_raw(&closed), 0);
        // The fvar range saturates the same way, and does not descend into
        // an `fvar`'s type annotation.
        assert_eq!(expr::fvar_b_raw(&expr::fvar(9, expr::dup(&ty))), 10);
        assert_eq!(expr::fvar_b_raw(&expr::fvar(1000000, ty)), 32767);
    }

    #[test]
    fn the_ranges_and_the_level_param_bit_follow_the_recurrence() {
        let u = level::param(nm("u"));
        let s0 = expr::sort(level::zero());
        let su = expr::sort(level::dup(&u));
        // `sort`: both ranges 0, the bit is `levelHasParam`.
        assert_eq!(expr::bvar_b_raw(&s0), 0);
        assert_eq!(expr::fvar_b_raw(&s0), 0);
        assert!(!expr::has_lp(&s0));
        assert!(expr::has_lp(&su));
        // `const`: the bit is `levelsHaveParam`.
        assert!(!expr::has_lp(&expr::mk_const(nm("Nat"), Vec::new())));
        let lu: Vec<Level> = vec![level::dup(&u)];
        assert!(expr::has_lp(&expr::mk_const(nm("List"), lu)));
        // `app`: componentwise max, disjunction.
        let a = expr::app(expr::bvar(2), expr::fvar(4, expr::dup(&s0)));
        assert_eq!(expr::bvar_b_raw(&a), 3);
        assert_eq!(expr::fvar_b_raw(&a), 5);
        assert!(!expr::has_lp(&a));
        assert!(expr::has_lp(&expr::app(expr::dup(&su), expr::bvar(0))));
        // `letE`: only the body is under the binder.
        let l = expr::let_e(expr::bvar(3), expr::bvar(1), expr::bvar(6));
        assert_eq!(expr::bvar_b_raw(&l), 6);
        assert_eq!(expr::fvar_b_raw(&l), 0);
        // `lam`'s bit picks up the binder datum's parameters.
        let m = expr::lam(expr::dup(&s0), expr::bvar(0), bm(&["u"]));
        assert!(expr::has_lp(&m));
        let m2 = expr::lam(expr::dup(&s0), expr::bvar(0), bm_never());
        assert!(!expr::has_lp(&m2));
        // `proj` copies its subterm's fields.
        let p = expr::proj(nm("Prod"), 0, expr::dup(&a));
        assert_eq!(expr::bvar_b_raw(&p), expr::bvar_b_raw(&a));
        assert_eq!(expr::fvar_b_raw(&p), expr::fvar_b_raw(&a));
        assert_eq!(expr::has_lp(&p), expr::has_lp(&a));
        // `lit` is closed.
        let li = expr::lit(Literal::NatVal(nat::from_u64(7)));
        assert_eq!(expr::bvar_b_raw(&li), 0);
        assert_eq!(expr::fvar_b_raw(&li), 0);
        assert!(!expr::has_lp(&li));
    }

    // -----------------------------------------------------------------------
    // Equality and hashing
    // -----------------------------------------------------------------------

    #[test]
    fn beq_on_shared_and_on_unshared_equal_dags() {
        for e in battery().iter() {
            // Shared: the pointer fast path fires at the root.
            let s = expr::dup(e);
            assert!(expr::ptr_eq(e, &s));
            assert!(expr::beq(e, &s));
        }
        // Unshared but equal: every pair of the battery, rebuilt from
        // scratch, compares equal to its twin and unequal to the others.
        let xs = battery();
        let ys = battery();
        for i in 0..xs.len() {
            for j in 0..ys.len() {
                assert!(!expr::ptr_eq(&xs[i], &ys[j]));
                assert_eq!(expr::beq(&xs[i], &ys[j]), i == j);
            }
        }
    }

    #[test]
    fn beq_descends_through_shared_subterms() {
        // A DAG that shares a subterm with itself, against the same term
        // built without any sharing: `beq` must still say `true`, and it
        // must reject a one-node change anywhere in the tree.
        let ty = expr::sort(level::zero());
        let shared = expr::app(expr::bvar(0), expr::bvar(1));
        let dag = expr::lam(
            expr::app(expr::dup(&shared), expr::dup(&shared)),
            expr::app(expr::dup(&shared), expr::bvar(2)),
            bm(&["u"]),
        );
        let tree = expr::lam(
            expr::app(
                expr::app(expr::bvar(0), expr::bvar(1)),
                expr::app(expr::bvar(0), expr::bvar(1)),
            ),
            expr::app(expr::app(expr::bvar(0), expr::bvar(1)), expr::bvar(2)),
            bm(&["u"]),
        );
        assert!(!expr::ptr_eq(&dag, &tree));
        assert!(expr::beq(&dag, &tree));
        assert_eq!(expr::data(&dag), expr::data(&tree));
        // A different binder datum, a different body, a different type.
        let other_meta = expr::lam(
            expr::app(expr::dup(&shared), expr::dup(&shared)),
            expr::app(expr::dup(&shared), expr::bvar(2)),
            bm(&["v"]),
        );
        assert!(!expr::beq(&dag, &other_meta));
        let other_body = expr::lam(
            expr::app(expr::dup(&shared), expr::dup(&shared)),
            expr::app(expr::dup(&shared), expr::bvar(3)),
            bm(&["u"]),
        );
        assert!(!expr::beq(&dag, &other_body));
        let other_ty = expr::lam(expr::dup(&ty), expr::dup(&shared), bm_never());
        assert!(!expr::beq(&dag, &other_ty));
    }

    #[test]
    fn beq_separates_every_constructor_and_every_field() {
        let z = level::zero();
        let one = level::succ(level::zero());
        // Same constructor, one field apart.
        assert!(!expr::beq(&expr::bvar(0), &expr::bvar(1)));
        assert!(!expr::beq(
            &expr::fvar(0, expr::sort(level::dup(&z))),
            &expr::fvar(1, expr::sort(level::dup(&z)))
        ));
        assert!(!expr::beq(
            &expr::fvar(0, expr::sort(level::dup(&z))),
            &expr::fvar(0, expr::sort(level::dup(&one)))
        ));
        assert!(!expr::beq(
            &expr::sort(level::dup(&z)),
            &expr::sort(level::dup(&one))
        ));
        assert!(!expr::beq(
            &expr::mk_const(nm("Nat"), Vec::new()),
            &expr::mk_const(nm("Int"), Vec::new())
        ));
        // A `const`'s level list: different lengths, and different entries.
        let l1: Vec<Level> = vec![level::dup(&z)];
        let l2: Vec<Level> = vec![level::dup(&one)];
        let l3: Vec<Level> = vec![level::dup(&z), level::dup(&one)];
        let l4: Vec<Level> = vec![level::dup(&z), level::dup(&one)];
        assert!(!expr::beq(
            &expr::mk_const(nm("List"), l1),
            &expr::mk_const(nm("List"), Vec::new())
        ));
        assert!(!expr::beq(
            &expr::mk_const(nm("List"), vec![level::dup(&z)]),
            &expr::mk_const(nm("List"), l2)
        ));
        assert!(expr::beq(
            &expr::mk_const(nm("List"), l3),
            &expr::mk_const(nm("List"), l4)
        ));
        // Literals.
        assert!(expr::beq(
            &expr::lit(Literal::NatVal(nat::from_u64(5))),
            &expr::lit(Literal::NatVal(nat::from_u64(5)))
        ));
        assert!(!expr::beq(
            &expr::lit(Literal::NatVal(nat::from_u64(5))),
            &expr::lit(Literal::NatVal(nat::from_u64(6)))
        ));
        assert!(!expr::beq(
            &expr::lit(Literal::StrVal(cps("a"))),
            &expr::lit(Literal::StrVal(cps("b")))
        ));
        assert!(!expr::beq(
            &expr::lit(Literal::NatVal(nat::zero())),
            &expr::lit(Literal::StrVal(Vec::new()))
        ));
        // `proj`: the structure name and the field index.
        assert!(!expr::beq(
            &expr::proj(nm("Prod"), 0, expr::bvar(0)),
            &expr::proj(nm("Prod"), 1, expr::bvar(0))
        ));
        assert!(!expr::beq(
            &expr::proj(nm("Prod"), 0, expr::bvar(0)),
            &expr::proj(nm("Sigma"), 0, expr::bvar(0))
        ));
        // `lam` and `forallE` are different constructors with the same
        // fields — the tag (and the hash) must separate them.
        let l = expr::lam(expr::sort(level::dup(&z)), expr::bvar(0), bm_never());
        let f = expr::forall_e(expr::sort(level::dup(&z)), expr::bvar(0), bm_never());
        assert!(!expr::beq(&l, &f));
        assert_ne!(expr::hash(&l), expr::hash(&f));
    }

    #[test]
    fn structurally_equal_terms_built_separately_hash_alike() {
        let xs = battery();
        let ys = battery();
        for i in 0..xs.len() {
            assert_eq!(expr::data(&xs[i]), expr::data(&ys[i]));
            assert_eq!(expr::hash(&xs[i]), expr::hash(&ys[i]));
            assert_eq!(expr::has_lp(&xs[i]), expr::has_lp(&ys[i]));
            assert_eq!(expr::bvar_b_raw(&xs[i]), expr::bvar_b_raw(&ys[i]));
            assert_eq!(expr::fvar_b_raw(&xs[i]), expr::fvar_b_raw(&ys[i]));
        }
        // The hash is 32 bits and the ten tags are distinct, so the battery
        // has no collision — not required of a hash, but a mistyped tag or a
        // forgotten field would show up here first.
        for i in 0..xs.len() {
            for j in 0..xs.len() {
                if i != j {
                    assert_ne!(expr::hash(&xs[i]), expr::hash(&xs[j]));
                }
            }
        }
        // A shared subterm and its rebuilt twin give the same word, which is
        // what makes the word a function of the value and not of the DAG.
        let sub = expr::app(expr::bvar(0), expr::bvar(1));
        let a = expr::app(expr::dup(&sub), expr::dup(&sub));
        let b = expr::app(
            expr::app(expr::bvar(0), expr::bvar(1)),
            expr::app(expr::bvar(0), expr::bvar(1)),
        );
        assert_eq!(expr::data(&a), expr::data(&b));
    }

    #[test]
    fn the_hash_map_dictionaries_are_hash_and_beq() {
        let a = expr::app(expr::mk_const(nm("f"), Vec::new()), expr::bvar(0));
        let b = expr::app(expr::mk_const(nm("f"), Vec::new()), expr::bvar(0));
        let c = expr::app(expr::mk_const(nm("f"), Vec::new()), expr::bvar(1));
        assert!(a.eq2(&b));
        assert!(!a.eq2(&c));
        assert_eq!(a.hash64(), expr::hash(&b));
    }

    // -----------------------------------------------------------------------
    // The rest
    // -----------------------------------------------------------------------

    #[test]
    fn beq_recursive_is_the_six_descending_constructors() {
        let ty = expr::sort(level::zero());
        assert!(expr::beq_recursive(&expr::fvar(0, expr::dup(&ty))));
        assert!(expr::beq_recursive(&expr::app(expr::bvar(0), expr::bvar(0))));
        assert!(expr::beq_recursive(&expr::lam(
            expr::dup(&ty),
            expr::bvar(0),
            bm_never()
        )));
        assert!(expr::beq_recursive(&expr::forall_e(
            expr::dup(&ty),
            expr::bvar(0),
            bm_never()
        )));
        assert!(expr::beq_recursive(&expr::let_e(
            expr::dup(&ty),
            expr::bvar(0),
            expr::bvar(0)
        )));
        assert!(expr::beq_recursive(&expr::proj(nm("P"), 0, expr::bvar(0))));
        assert!(!expr::beq_recursive(&expr::bvar(0)));
        assert!(!expr::beq_recursive(&ty));
        assert!(!expr::beq_recursive(&expr::mk_const(nm("Nat"), Vec::new())));
        assert!(!expr::beq_recursive(&expr::lit(Literal::NatVal(nat::zero()))));
    }

    #[test]
    fn mk_bvar_is_the_bare_constructor() {
        // `mkBvar_eq`: the pool is not ported, so what is a transparency
        // lemma in Lean is an outright equality here.
        assert_eq!(expr::bvar_pool_size(), 4096);
        for i in [0u64, 1, 4095, 4096, 100000].iter() {
            let a = expr::mk_bvar(*i);
            let b = expr::bvar(*i);
            assert!(expr::beq(&a, &b));
            assert_eq!(expr::data(&a), expr::data(&b));
            match &a.0.kind {
                ExprKind::Bvar(j) => assert_eq!(*j, *i),
                _ => assert!(false),
            }
        }
    }

    #[test]
    fn binder_meta_and_literal_helpers() {
        let m1 = bm(&["u", "v"]);
        let m2 = bm(&["v", "u"]);
        // `PropWhen` is canonical, so the two orderings are one datum.
        assert!(expr::binder_meta_beq(&m1, &m2));
        assert_eq!(expr::binder_meta_hash(&m1), expr::binder_meta_hash(&m2));
        assert!(!expr::binder_meta_beq(&m1, &bm_never()));
        let d = expr::binder_meta_dup(&m1);
        assert!(expr::binder_meta_beq(&m1, &d));
        let l = Literal::StrVal(cps("héllo"));
        let l2 = expr::literal_dup(&l);
        assert!(expr::literal_beq(&l, &l2));
        assert_eq!(expr::literal_hash(&l), expr::literal_hash(&l2));
        let n = Literal::NatVal(nat::from_u64(1 << 40));
        let n2 = expr::literal_dup(&n);
        assert!(expr::literal_beq(&n, &n2));
        assert_eq!(expr::literal_hash(&n), expr::literal_hash(&n2));
        assert_eq!(expr::str_copy(&cps("abc")), cps("abc"));
    }
}
