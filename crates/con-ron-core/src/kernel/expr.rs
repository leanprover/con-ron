//! Port of `ConLeche/Kernel/Expr.lean` — the checker's term representation.
//!
//! The `Level` half of that file (lines 35-139: the `Level` inductive, its
//! `Hashable`/`BEq` instances, `levelHasParam`, `levelsHaveParam`,
//! `levelHash` and `levelsHash`) was ported at task #3 and lives in
//! `crate::kernel::level`; this module is everything from `BinderMeta` on.
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
//!
//! # The structural-equality pair memo, and why it needs no new hole
//!
//! (con-leche's own argument for the memo is `Expr.lean:678-728`, the
//! `Expr.beq` module note, and `Expr.lean:767-773`, `beqBudget`; the
//! citation lines proper are on the items below, since a `//!` one would
//! cover the whole file and switch the per-item gate off.)
//!
//! `beq_go` carries con-leche's pair memo (`EqPair`, `BeqMap`, `beqKey`,
//! `probeHit` and `beqGo`'s write-back, `Expr.lean:744-949`), which task #11
//! left out and task #28 measured the need for: eight fixture streams compare
//! two pointer-distinct copies of a depth-60 shared tower, where an
//! unmemoised descent is `O(tree)` on `2^60` nodes and does not finish.  One
//! thing changes.  con-leche keys the table by the two **addresses**, which
//! Aeneas cannot model at all; this port keys it by the two stored **hash
//! words** (`beq_key`, a field read each).  The key is a filter either way —
//! a stored pair is verified by *identity* on both components (`ptr_eq`,
//! i.e. `Rc::ptr_eq`), as con-leche verifies it (`probeHit`) — so a collision
//! between distinct pairs costs an entry, never an answer.
//!
//! **The trust argument (DESIGN.md §3.2).**  `ptr_eq` is modeled as `false`,
//! so `probe_hit` is `false` at *every* probe in the model: the memo is a
//! state that is written and never read, and the model's `beq` is exactly the
//! structural descent `Refine/Expr.lean` proves exact.  In the binary a probe
//! hits only when the stored pair is *the very two objects* being compared —
//! the entry holds them, so their identity stays theirs for the life of the
//! comparison — and that entry was written by a **completed `true`** of this
//! same deterministic walk on those same two objects (a `false` aborts the
//! comparison at every level, so no unequal pair is ever stored).  A hit
//! therefore repeats an answer this walk has already produced for that pair;
//! the binary and the model agree, for the same reason and by the same
//! reflexivity obligation that makes the pointer fast path transparent.
//! Nothing here is opaque: the table is `ron::HashMap`, verified at task #16,
//! and the external holes stay exactly §3.2's four `Rc` axioms.
//!
//! **`beqBudget` is not ported.**  con-leche materialises the table only
//! after 4 096 nodes, because in Lean the table's allocation and its
//! reference-count traffic cost "a third of `init-prelude`" on the
//! comparisons that a pointer test or the computed word decides outright.
//! Here `beq` performs those two guards *before* it allocates anything
//! (which is what the cited `beqMemo = withPtrEq a b (fun _ => a.data ==
//! b.data && …)` does), so a decided-outright comparison allocates no
//! table at all and the budget has nothing left to buy; task #30's numbers
//! (DESIGN.md) are the measurement that says so.

use crate::ron::hashmap::Eq2;
use crate::ron::hashmap::HashMap;
use crate::ron::hashmap::Hashable;
use crate::kernel::level;
use crate::kernel::level::Level;
use crate::kernel::name;
use crate::kernel::name::Name;
use crate::ron::nat;
use crate::kernel::prop_when;
use crate::kernel::prop_when::PropWhen;
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
/// `crate::ron::nat::Nat`, the crate's own bignum, and `strVal`'s `String` is a
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
/// `true` for the nodes whose comparison recurses, i.e. the pair memo's
/// gate: a `bvar`, `sort`, `const` or `lit` pair is decided without a
/// descent, so an entry for it can never save a walk and every one of them
/// would cost a probe and a write — and leaves are the majority of the nodes
/// of a real term.  `beq_go` consults and writes the memo only here.
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

/// con-leche: ConLeche/Kernel/Expr.lean:739-749 EqPair
/// A memo entry: the pair of objects a completed descent proved equal.
/// Deviations, both of them things Rust has not got: the two stored
/// *addresses* (con-leche's cheap probe filter — here the key does that job)
/// and the *proof* `fst = snd`.  What is left is the pair itself, which is
/// what `probe_hit` verifies against, and holding it is what keeps the two
/// `Rc`s alive, hence their identity theirs, for the life of the comparison.
/// The alias is erased before Charon sees anything (as `cached::core_c`'s
/// `InferLamEntry` is).
pub type EqPair = (Expr, Expr);

/// con-leche: ConLeche/Kernel/Expr.lean:755-756 BeqMap
/// The memo, keyed by `beq_key`: one slot per key, last write wins, as the
/// cited `Std.HashMap` does.  `ron::HashMap` is the crate's own table
/// (DESIGN.md §3.3), verified at task #16.
pub type BeqMap = HashMap<u64, EqPair>;

/// con-leche: ConLeche/Kernel/Expr.lean:758-765 Expr.beqKey
/// The memo key of a pair, packed into one word.
///
/// **Deviation (the one change the port makes to the memo, see the module
/// note).**  con-leche mixes the two *addresses*, which Aeneas cannot model;
/// this mixes the two stored *hash words*, which are field reads.  Either
/// way the packing need not be injective — `probe_hit` verifies the stored
/// pair itself — so a collision between distinct pairs costs an entry, never
/// an answer.  The cited `&&& 0x3FFFFFFFFFFFFFFF` goes with the `Nat` it
/// existed for (Lean wants a tagged scalar below `2^62`; a `u64` is one),
/// and the multiplication wraps as the cited `USize` one does (task #11).
pub fn beq_key(ha: u64, hb: u64) -> u64 {
    ha ^ hb.wrapping_mul(0x9E3779B97F4A7C15)
}

/// con-leche: ConLeche/Kernel/Expr.lean:804-816 Expr.probeHit
/// Does the entry at `key` identify the pair `(a, b)`?  The stored objects,
/// tested by *identity*, are the verification — con-leche's stored addresses
/// are the filter that the key has become.  A `true` here is `a = b` because
/// the entry was written by a completed `true` of this same walk on these
/// same two objects (the module note's trust argument).
///
/// In the model `ptr_eq` is `false` (DESIGN.md §3.2), so this is `false` at
/// every probe and the memo is never read: the model's descent is the plain
/// structural one, which is the whole point of keying by the hash words.
pub fn probe_hit(m: &BeqMap, key: u64, a: &Expr, b: &Expr) -> bool {
    match m.get(&key) {
        None => false,
        Some(p) => {
            if ptr_eq(&p.0, a) {
                ptr_eq(&p.1, b)
            } else {
                false
            }
        }
    }
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

/// con-leche: none — `List Expr` equality (the `==` of a `List Expr` field)
/// The twin of `levels_beq` one level up: what Lean's `BEq (List Expr)`
/// decides, and what the `deriving DecidableEq`s of `Kernel/Env.lean`'s
/// stored-constant records (`env::rec_rule_fire_beq`, `env::proj_table_beq`)
/// and the inductive recognisers' `==` conjuncts read.  Entry point of the
/// index recursion below.
pub fn exprs_beq(xs: &Vec<Expr>, ys: &Vec<Expr>) -> bool {
    if xs.len() == ys.len() {
        exprs_beq_from(xs, ys, 0)
    } else {
        false
    }
}

/// con-leche: none — the index recursion behind `exprs_beq`
/// Lean's `List.beq` over `BEq Expr`; no loops (DESIGN.md §3.4).
pub fn exprs_beq_from(xs: &Vec<Expr>, ys: &Vec<Expr>, i: usize) -> bool {
    if i >= xs.len() {
        true
    } else if beq(&xs[i], &ys[i]) {
        exprs_beq_from(xs, ys, i + 1)
    } else {
        false
    }
}

/// con-leche: ConLeche/Kernel/Expr.lean:818-949 Expr.beqGo
/// The memoised structural descent, in the cited shape: pointer identity,
/// then the computed word (a mismatch *is* an inequality), then the memo
/// probe, then the constructor cases in the cited arm order, then the
/// write-back of a completed `true` at a recursive node (con-leche's
/// `finish`).  A `false` aborts the comparison at every level, so only
/// proved-equal pairs are ever stored — as in the official kernel's
/// `expr_eq_fn`.
///
/// **Deviations (task #30; the module note holds the trust argument).**
/// The memo is keyed by the two stored hash words rather than by the two
/// addresses (`beq_key`) and a probe verifies the stored pair by identity
/// (`probe_hit`), so in the model — where `ptr_eq` is `false` — the table is
/// written and never read and this is the plain structural descent.  Gone
/// with Lean's proof plumbing: `BeqRes`/`BeqOut`/`BeqOut.mk` and the
/// `Squash` quotient (the result is a `bool`, not a `Decidable (a = b)`),
/// `withAddr`/`ptrDec` (`ptr_eq` above), `EqPair.dflt` (`get` returns an
/// `Option`) and the `fuel`/`beqBudget` pair (the module note: `beq`'s two
/// guards run before the table is allocated, so there is nothing left for a
/// budget to save).  The pointer fast path is kept at every level, as in
/// `name::beq` and `level::beq`, and its transparency is the reflexivity
/// obligation of DESIGN.md §3.2.
///
/// The table goes in and comes back out **by value**, as the cited `map`
/// does and as task #6's accumulator rule says; a `&mut` parameter is the
/// same thing in the generated Lean (`Result (Bool × BeqMap)` either way),
/// but Aeneas cannot join the two branches of an arm's `if` when one of them
/// reborrows the table and the shared borrows of `a` and `b` are still live
/// ("Could not match the contexts", measured on the `fvar` arm).
pub fn beq_go(m: BeqMap, a: &Expr, b: &Expr) -> (bool, BeqMap) {
    if ptr_eq(a, b) {
        (true, m)
    } else if data(a) != data(b) {
        (false, m)
    } else {
        let rec: bool = beq_recursive(a);
        let key: u64 = beq_key(hash(a), hash(b));
        if rec && probe_hit(&m, key, a, b) {
            (true, m)
        } else {
            let rm: (bool, BeqMap) = beq_arm(m, a, b);
            beq_finish(rm.0, rm.1, rec, key, a, b)
        }
    }
}

/// con-leche: ConLeche/Kernel/Expr.lean:818-949 Expr.beqGo
/// `beqGo`'s constructor cases, in the cited arm order: the ten diagonal
/// pairs and the wildcard, each one expression (the helpers below are why —
/// see `beq_when`).  Its own function for two reasons.  It is where the
/// *specification* lives: `beq_go`'s wrapper — identity, the computed word,
/// the probe and the write-back — is a fixed frame around it, so
/// `Refine/Expr.lean` peels the frame once (`beq_go_arm`) and the
/// hundred-case constructor induction is about this function, which is the
/// memo-free descent task #11 proved.  And Aeneas otherwise *duplicates* the
/// whole match, once per branch of `if rec`.
pub fn beq_arm(m: BeqMap, a: &Expr, b: &Expr) -> (bool, BeqMap) {
    match (&a.0.kind, &b.0.kind) {
        (ExprKind::Bvar(i), ExprKind::Bvar(j)) => (i == j, m),
        (ExprKind::Fvar(i, t), ExprKind::Fvar(j, u)) => beq_when(m, i == j, t, u),
        (ExprKind::Sort(u), ExprKind::Sort(v)) => (level::beq(u, v), m),
        (ExprKind::Const(n, us), ExprKind::Const(n2, vs)) => (const_beq(n, us, n2, vs), m),
        (ExprKind::App(f, x), ExprKind::App(g, y)) => beq_both(m, f, g, x, y),
        (ExprKind::Lam(t1, b1, m1), ExprKind::Lam(t2, b2, m2)) => {
            beq_both_when(m, binder_meta_beq(m1, m2), t1, t2, b1, b2)
        }
        (ExprKind::ForallE(t1, b1, m1), ExprKind::ForallE(t2, b2, m2)) => {
            beq_both_when(m, binder_meta_beq(m1, m2), t1, t2, b1, b2)
        }
        (ExprKind::LetE(t1, v1, b1), ExprKind::LetE(t2, v2, b2)) => {
            beq_three(m, t1, t2, v1, v2, b1, b2)
        }
        (ExprKind::Lit(l1), ExprKind::Lit(l2)) => (literal_beq(l1, l2), m),
        (ExprKind::Proj(s1, i1, e1), ExprKind::Proj(s2, i2, e2)) => {
            beq_when(m, proj_head_beq(s1, *i1, s2, *i2), e1, e2)
        }
        _ => (false, m),
    }
}

/// con-leche: ConLeche/Kernel/Expr.lean:818-949 Expr.beqGo
/// `beqGo`'s `finish`: a completed `true` at a recursive node is recorded,
/// everything else passes through.
///
/// Two shapes this function is deliberately *not*.  It is a tail call rather
/// than a `let` followed by a branch on the arm's `(bool, BeqMap)`, which is
/// what Aeneas's `simplify_let_branching` pass raises an internal error on;
/// and it takes the decision and the table as two parameters rather than the
/// pair, because a pattern-matching `let` on a tuple parameter comes out as a
/// `match` in the generated Lean that no `simp` set of `Refine/Expr.lean`
/// sees through.
pub fn beq_finish(
    r: bool,
    m: BeqMap,
    rec: bool,
    key: u64,
    a: &Expr,
    b: &Expr,
) -> (bool, BeqMap) {
    if r {
        if rec {
            (true, beq_record(m, key, a, b))
        } else {
            (true, m)
        }
    } else {
        (false, m)
    }
}

/// con-leche: ConLeche/Kernel/Expr.lean:818-949 Expr.beqGo
/// `beqGo`'s `finish`, the write-back: record a completed `true` at a
/// recursive node under that node's own key.  Its own function so that the
/// table's `mut` binding is one line long and `beq_go`'s arms stay
/// expressions (the accumulator goes in and comes back out by value, task
/// #6's rule).
pub fn beq_record(m: BeqMap, key: u64, a: &Expr, b: &Expr) -> BeqMap {
    let mut m: BeqMap = m;
    m.insert(key, (dup(a), dup(b)));
    m
}

/// con-leche: ConLeche/Kernel/Expr.lean:818-949 Expr.beqGo
/// The cited `.fvar`/`.proj` arms' shape: a field comparison that decides
/// the arm on its own, then the one recursive call.
///
/// **Why this is a function and not an `if` inside the arm** (the shape task
/// #11 had): Aeneas cannot join the two branches of an `if` inside an arm of
/// the *pair* match when one of them consumes the memo through a call taking
/// borrows out of both `a` and `b` and the other does not — "Could not match
/// the contexts", measured on the `fvar` arm both with `&mut BeqMap` and
/// with the table by value.  With the children as plain parameters the join
/// is between two `(bool, BeqMap)`s and no loan tree of `a` or `b` is live,
/// which Aeneas handles (`state_c::consts_resolve_fc_node` is the
/// single-scrutinee precedent).  The five helpers below are the same
/// `beqGo` arms, one call deeper.
pub fn beq_when(m: BeqMap, cond: bool, x: &Expr, y: &Expr) -> (bool, BeqMap) {
    if cond {
        beq_go(m, x, y)
    } else {
        (false, m)
    }
}

/// con-leche: ConLeche/Kernel/Expr.lean:818-949 Expr.beqGo
/// The cited `.app` arm: the two children in order, aborting on the first
/// `false` (which is what keeps an unequal pair out of the memo).
pub fn beq_both(m: BeqMap, x1: &Expr, y1: &Expr, x2: &Expr, y2: &Expr) -> (bool, BeqMap) {
    let (r1, m1): (bool, BeqMap) = beq_go(m, x1, y1);
    if r1 {
        beq_go(m1, x2, y2)
    } else {
        (false, m1)
    }
}

/// con-leche: ConLeche/Kernel/Expr.lean:818-949 Expr.beqGo
/// The cited `.lam`/`.forallE` arms: the binder datum decides the arm, then
/// the domain and the body.
pub fn beq_both_when(
    m: BeqMap,
    cond: bool,
    x1: &Expr,
    y1: &Expr,
    x2: &Expr,
    y2: &Expr,
) -> (bool, BeqMap) {
    if cond {
        beq_both(m, x1, y1, x2, y2)
    } else {
        (false, m)
    }
}

/// con-leche: ConLeche/Kernel/Expr.lean:818-949 Expr.beqGo
/// The cited `.letE` arm: the type, the value, the body.
pub fn beq_three(
    m: BeqMap,
    x1: &Expr,
    y1: &Expr,
    x2: &Expr,
    y2: &Expr,
    x3: &Expr,
    y3: &Expr,
) -> (bool, BeqMap) {
    let (r1, m1): (bool, BeqMap) = beq_go(m, x1, y1);
    if r1 {
        beq_both(m1, x2, y2, x3, y3)
    } else {
        (false, m1)
    }
}

/// con-leche: ConLeche/Kernel/Expr.lean:818-949 Expr.beqGo
/// The cited `.const` arm's `n == m && us == vs`, as one `bool` so that the
/// arm is a single expression (see `beq_when`).  Neither conjunct recurses.
pub fn const_beq(n: &Name, us: &Vec<Level>, n2: &Name, vs: &Vec<Level>) -> bool {
    if name::beq(n, n2) {
        levels_beq(us, vs)
    } else {
        false
    }
}

/// con-leche: ConLeche/Kernel/Expr.lean:818-949 Expr.beqGo
/// The cited `.proj` arm's `s == s' && i == i'`, the part that decides the
/// arm before its one recursive call (see `beq_when`).
pub fn proj_head_beq(s1: &Name, i1: u64, s2: &Name, i2: u64) -> bool {
    if name::beq(s1, s2) {
        i1 == i2
    } else {
        false
    }
}

/// con-leche: ConLeche/Kernel/Expr.lean:950-952 Expr.beqDec
/// con-leche: ConLeche/Kernel/Expr.lean:955-960 Expr.beqMemo
/// con-leche: ConLeche/Kernel/Expr.lean:972-976 Expr.beq
/// `Expr.beqMemo` is the *executed* `Expr.beq` (`@[csimp]`-substituted):
/// the pointer test, the computed-word test, then `beqDec`, which is the
/// descent from a fresh state.  The memo is therefore **local to this
/// call** — a comparison never sees another one's entries, which is what
/// makes "the entry holds the two objects" true for the life of the
/// comparison (the module note) — and the two guards run *first*, so a
/// comparison decided by identity or by the word allocates no table at all.
/// That placement is the cited `withPtrEq a b (fun _ => a.data == b.data &&
/// …)`, and it is what the port has instead of `beqBudget`.
pub fn beq(a: &Expr, b: &Expr) -> bool {
    if ptr_eq(a, b) {
        true
    } else if data(a) != data(b) {
        false
    } else {
        let m: BeqMap = HashMap::new();
        let (r, _m): (bool, BeqMap) = beq_go(m, a, b);
        r
    }
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
   * what exists only for Lean's proof plumbing or for addresses, now that
     task #30 has ported the memo itself (`EqPair`, `BeqMap`, `beqKey`,
     `probeHit` above, and `beqDec` cited on `beq`): `EqPair.dflt` (:753) —
     `get` returns an `Option`, so a probe needs no default; `BeqRes`
     (:777), `BeqOut` (:786) and `BeqOut.mk` (:788) — the `Squash`ed
     `Decidable (a = b)` is a `bool` here; `withAddr` (:795) and `ptrDec`
     (:801) — `expr::ptr_eq` is both, and `withPtrAddr`'s subsingleton side
     condition is what the `Squash` existed for; and `beqBudget` (:773) —
     the module note: `beq`'s two guards run before the table is allocated,
     so the budget has nothing left to buy (task #30 measured it).
     (`bvarPool` is dropped too, but it is *cited* on `mk_bvar` above, where
     its deviation is argued.)
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
   * the `Level` half (:35-139) — ported at task #3, in `crate::kernel::level`.
   * the accessors this file's docstring points at but does not contain
     (`Expr.bvarB`, `Expr.fvarB`, `bvarBoundMemo`, `fvarRangeMemo`, and the
     `isApp`/`getAppFn` family) live in `Kernel/ExprOps.lean`, a later
     task. */

// ---------------------------------------------------------------------------
// The hash-map dictionaries (`crate::ron::hashmap`'s own traits, task #7)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/Expr.lean:435-440 _
/// The cited `instance : Hashable Expr := ⟨Expr.hash⟩`, as the key
/// dictionary of `crate::ron::hashmap` — what `memoE`/`memoB` and every other
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
/// `crate::ron::hashmap`.  Deviation: `Eq2` is our own one-method trait rather
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
    use crate::kernel::expr;
    use crate::kernel::expr::BinderMeta;
    use crate::kernel::expr::Expr;
    use crate::kernel::expr::ExprKind;
    use crate::kernel::expr::Literal;
    use crate::ron::hashmap::Eq2;
    use crate::ron::hashmap::HashMap;
    use crate::ron::hashmap::Hashable;
    use crate::kernel::level;
    use crate::kernel::level::Level;
    use crate::kernel::name;
    use crate::kernel::name::Name;
    use crate::ron::nat;
    use crate::kernel::prop_when;

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

    /// A shared "tower": `d 0 = bvar 0`, `d (k+1) = app (d k) (d k)` with
    /// *one* `Rc` per level, so `d k` is `2^k` nodes as a tree and `k+1`
    /// nodes as a DAG.  These are task #28's eight blow-up fixtures in one
    /// line, and the reason the pair memo exists.
    fn tower(k: u64) -> Expr {
        if k == 0 {
            expr::bvar(0)
        } else {
            let d = tower(k - 1);
            expr::app(expr::dup(&d), d)
        }
    }

    #[test]
    fn beq_on_two_rebuilt_dag_towers_is_memoised() {
        // Two independently built towers: pointer-distinct at every level,
        // so the pointer fast path never fires and only the memo keeps the
        // descent off the 2^60-node tree.  Without it this test does not
        // finish (task #28 measured 300 s+ on the same shape).
        let a = tower(60);
        let b = tower(60);
        assert!(!expr::ptr_eq(&a, &b));
        assert_eq!(expr::data(&a), expr::data(&b));
        assert!(expr::beq(&a, &b));
        // The `Eq2` dictionary is the memoised `beq`, so a hash-map key
        // comparison is memoised too.
        assert!(a.eq2(&b));
        // A one-node change at the *root* of the tower is rejected by the
        // word guard; a change at the bottom aborts the descent at the
        // first mismatching child, which is why `false` needs no memo.
        let a1 = tower(59);
        let perturbed = expr::app(expr::dup(&a1), expr::app(expr::bvar(1), expr::bvar(0)));
        assert!(!expr::beq(&a, &perturbed));
        let mut deep: Expr = expr::bvar(1);
        let mut i: u64 = 0;
        while i < 60 {
            deep = expr::app(expr::dup(&deep), deep);
            i += 1;
        }
        assert!(!expr::beq(&a, &deep));
    }

    #[test]
    fn probe_hit_verifies_by_identity_not_by_structure() {
        // The trust argument in one test: an entry is read back only for
        // the very objects it was stored for.  A structurally equal but
        // pointer-distinct rebuild does *not* hit, which is why the model —
        // where `ptr_eq` is `false` — never reads the table at all.
        let a = expr::app(expr::bvar(0), expr::bvar(1));
        let b = expr::app(expr::bvar(0), expr::bvar(1));
        let key = expr::beq_key(expr::hash(&a), expr::hash(&b));
        let mut m: expr::BeqMap = HashMap::new();
        assert!(!expr::probe_hit(&m, key, &a, &b));
        m.insert(key, (expr::dup(&a), expr::dup(&b)));
        assert!(expr::probe_hit(&m, key, &a, &b));
        // Same key (the word is the same), different objects: no hit.
        let a2 = expr::app(expr::bvar(0), expr::bvar(1));
        assert_eq!(expr::hash(&a2), expr::hash(&a));
        assert!(!expr::probe_hit(&m, key, &a2, &b));
        assert!(!expr::probe_hit(&m, key, &a, &a2));
        // Swapped sides: the stored pair is ordered, as con-leche's is.
        assert!(!expr::probe_hit(&m, key, &b, &a));
        // A key nothing was stored under: no hit.
        assert!(!expr::probe_hit(&m, key ^ 1, &a, &b));
        // `beq_key` is a function of the two words and mixes them, so the
        // two sides are not interchangeable.
        assert_eq!(expr::beq_key(3, 5), expr::beq_key(3, 5));
        assert_ne!(expr::beq_key(3, 5), expr::beq_key(5, 3));
    }

    #[test]
    fn beq_go_records_only_recursive_nodes_and_only_true() {
        // `beq_recursive` is the memo's gate and a `false` is never stored.
        let m: expr::BeqMap = HashMap::new();
        let l1 = expr::bvar(7);
        let l2 = expr::bvar(7);
        let (r, m) = expr::beq_go(m, &l1, &l2);
        assert!(r);
        assert_eq!(m.len(), 0, "a leaf pair is never recorded");
        let a = expr::app(expr::bvar(0), expr::bvar(1));
        let b = expr::app(expr::bvar(0), expr::bvar(1));
        let (r, m) = expr::beq_go(m, &a, &b);
        assert!(r);
        assert_eq!(m.len(), 1, "one entry: the `app` pair, not its leaves");
        assert!(expr::probe_hit(
            &m,
            expr::beq_key(expr::hash(&a), expr::hash(&b)),
            &a,
            &b
        ));
        // A completed `false` stores nothing.
        let m2: expr::BeqMap = HashMap::new();
        let c = expr::app(expr::bvar(0), expr::bvar(2));
        let (r2, m2) = expr::beq_go(m2, &a, &c);
        assert!(!r2);
        assert_eq!(m2.len(), 0);
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
