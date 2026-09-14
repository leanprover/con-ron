//! con-leche: none — the per-kind heap node of DESIGN.md §3.2, spike task #94.
//!
//! `ron::node` — **the tagged handle and the ten `Expr` nodes**.
//!
//! This module is the one place in the core where `unsafe` is written
//! (task #94's brief; `scripts/lint-rust-style.sh` exempts this path and
//! nothing else).  It exists for one reason, which is arithmetic: until
//! task #94 every `Expr` node was a `P<ExprNode>`, i.e. a block as wide as
//! the *widest* `ExprKind` arm plus a kind word plus `Arc`'s two counts —
//! 64 bytes for an `app`, which is 65 % of the nodes of a real term and
//! needs 32.  Lean's own representation does not do that: the kind is in
//! the object header, and each constructor's object is as wide as its own
//! fields.
//!
//! So the kind moves **into the handle**.  Every node is allocated
//! `align(16)`, which leaves the low four bits of its address free; ten
//! kinds fit in four bits; and `Expr` becomes one machine word again — a
//! `NonNull<u8>` whose low bits say which of the ten node structs the rest
//! of it points at.  The node structs are then free to differ in size:
//!
//! | tag | node | `size_of` | mimalloc class |
//! |---:|---|---:|---:|
//! | 0 | [`NodeBvar`] | 32 | 32 |
//! | 1 | [`NodeFvar`] | 32 | 32 |
//! | 2 | [`NodeSort`] | 32 | 32 |
//! | 3 | [`NodeConst`] | 32 | 32 |
//! | 4 | [`NodeApp`] | 32 | 32 |
//! | 5, 6 | [`NodeBinder`] (`lam`, `forallE`) | 48 | 48 |
//! | 7 | [`NodeLetE`] | 48 | 48 |
//! | 8 | [`NodeLit`] | 32 | 32 |
//! | 9 | [`NodeProj`] | 48 | 48 |
//!
//! against 64 bytes for all ten before.  `con-ron-dump`'s `node_sizes` test
//! pins the table.
//!
//! # Why hand-rolled and not `tagptr`/`tagged-pointer`
//!
//! Both crates model *a pointer to one type `T` plus a tag*: `TagPtr<T, N>`
//! derefs to `T` and the tag is a payload beside it.  What this module needs
//! is the opposite — the tag **chooses** the pointee type, and the ten types
//! have different sizes, so there is no `T` to be generic in.  Either crate
//! would therefore be used only as a bit-twiddling helper over
//! `NonNull<u8>`, which is four lines (`TAG_MASK`, `tag_of`, `addr_of`,
//! `word_of`), and would add a dependency whose own `unsafe` is *larger*
//! than the surface it removes.  Hand-rolled is the smaller surface; the
//! whole pointer arithmetic is the three functions below the constants.
//!
//! # The header, and why it is one count and not two
//!
//! [`NodeHeader`] is `{ count: AtomicUsize, data: u64 }` — the same atomic
//! strong count `std::sync::Arc` has, the same `@[computed_field] data` word
//! `ExprNode` had, and **no weak count**: the core never makes a `Weak`
//! (`ron::ptr`'s module note, and §3.4's lint gates `downgrade`), so the
//! second word `Arc` reserves for one is eight bytes per node of nothing.
//! That is the saving `triomphe::Arc` also offers, taken here without
//! triomphe's instruction cost (DESIGN.md's task-#92 entry: +29.3 % on
//! Mathlib) because the four operations are written out rather than reached
//! through a generic `Arc<T>`'s `Deref`/`Drop`.
//!
//! # The model (DESIGN.md §3.2)
//!
//! Nothing here changes what the proof tier sees.  §3.2's rule is "an `Arc`
//! is its contents"; the same rule reads here as **"an `Expr` is the
//! constructor it was allocated from"**: [`view`] is the projection
//! (`Expr.rec`'s scrutinee), the ten `alloc_*` are the constructors, and
//! [`data`] is the `@[computed_field]`.  The Lean model is the ordinary
//! inductive it already is, with [`view`]'s ten equations —
//! `view (alloc_app d f a) = App f a` and so on — as the external holes,
//! in place of the two `Arc` holes this module replaces.  See task #94's
//! report for the count.
//!
//! # Soundness
//!
//! Every cast below is `addr_of(e) as *const NodeX` where `X` is the struct
//! the tag names.  It is sound because a tagged handle is **only ever made
//! by `alloc_*`**, which writes the tag and the struct together
//! ([`new_node`] is the single place a tag is attached, and it is generic in
//! the struct so the pair cannot drift), the field is private so no other
//! module can synthesise one, and a node is immutable for its whole life
//! except for the atomic count.  The count discipline is `Arc`'s, verbatim:
//! `Relaxed` increment, `Release` decrement, `Acquire` fence before the
//! single thread that saw the count reach zero drops the payload.

use std::alloc::Layout;
use std::ptr::NonNull;
use std::sync::atomic;
use std::sync::atomic::AtomicUsize;
use std::sync::atomic::Ordering;

use crate::kernel::expr::BinderMeta;
use crate::kernel::expr::Expr;
use crate::kernel::expr::Literal;
use crate::kernel::level::Level;
use crate::kernel::name::Name;
use crate::ron::ptr::P;

// ---------------------------------------------------------------------------
// The tags
// ---------------------------------------------------------------------------

/// con-leche: none — the tag of `Expr.bvar` in the handle (DESIGN.md §3.2)
pub const TAG_BVAR: usize = 0;
/// con-leche: none — the tag of `Expr.fvar` in the handle (DESIGN.md §3.2)
pub const TAG_FVAR: usize = 1;
/// con-leche: none — the tag of `Expr.sort` in the handle (DESIGN.md §3.2)
pub const TAG_SORT: usize = 2;
/// con-leche: none — the tag of `Expr.const` in the handle (DESIGN.md §3.2)
pub const TAG_CONST: usize = 3;
/// con-leche: none — the tag of `Expr.app` in the handle (DESIGN.md §3.2)
pub const TAG_APP: usize = 4;
/// con-leche: none — the tag of `Expr.lam` in the handle (DESIGN.md §3.2)
pub const TAG_LAM: usize = 5;
/// con-leche: none — the tag of `Expr.forallE` in the handle (DESIGN.md §3.2)
pub const TAG_FORALL_E: usize = 6;
/// con-leche: none — the tag of `Expr.letE` in the handle (DESIGN.md §3.2)
pub const TAG_LET_E: usize = 7;
/// con-leche: none — the tag of `Expr.lit` in the handle (DESIGN.md §3.2)
pub const TAG_LIT: usize = 8;
/// con-leche: none — the tag of `Expr.proj` in the handle (DESIGN.md §3.2)
pub const TAG_PROJ: usize = 9;

/// con-leche: none — the four tag bits a 16-aligned node leaves free (DESIGN.md §3.2)
/// Ten kinds need four bits; `align(16)` on every node struct is what makes
/// those four bits always zero in a node's own address.
pub const TAG_MASK: usize = 15;

// ---------------------------------------------------------------------------
// The handle
// ---------------------------------------------------------------------------

/// con-leche: none — the counted handle of DESIGN.md §3.2, with the kind in it
/// A one-word handle to one of the ten nodes below: the node's address with
/// its kind in the low four bits.
///
/// The field is private, so the *only* way to obtain one is [`new_node`],
/// which writes a node and its tag together; that is the invariant every
/// cast in this module rests on.
pub struct ExprPtr {
    p: NonNull<u8>,
}

/// con-leche: none — `Send` for the handle (DESIGN.md §3.2, task #45)
/// Sound for the same reason `std::sync::Arc<T>: Send` is: the count is
/// atomic and the node is immutable otherwise, so no two threads can race on
/// anything but the count, and every field a node holds is itself
/// `Send + Sync` (`tests/send_sync.rs` is the standing assertion).
unsafe impl Send for ExprPtr {}

/// con-leche: none — `Sync` for the handle (DESIGN.md §3.2, task #45)
/// See [`ExprPtr`]'s `Send`: a shared `&Expr` exposes only immutable fields
/// and the atomic count.
unsafe impl Sync for ExprPtr {}

/// con-leche: none — the kind bits of a handle
#[inline]
fn tag_of(e: &Expr) -> usize {
    (e.0.p.as_ptr() as usize) & TAG_MASK
}

/// con-leche: none — the node address of a handle
#[inline]
fn addr_of(e: &Expr) -> *mut u8 {
    ((e.0.p.as_ptr() as usize) & !TAG_MASK) as *mut u8
}

/// con-leche: none — the raw word of a handle, for `ptr_eq` and for hashing
#[inline]
fn word_of(e: &Expr) -> usize {
    e.0.p.as_ptr() as usize
}

// ---------------------------------------------------------------------------
// The ten nodes
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/Expr.lean:285-403 Expr
/// The two words every node begins with: the strong count (no weak count —
/// see the module note) and the cited `@[computed_field] data`.
///
/// `align(16)` here is what frees the handle's four tag bits; every node
/// struct repeats it, since the language does not promise that a `repr(C)`
/// struct inherits a prefix field's alignment as its own.
#[repr(C, align(16))]
pub struct NodeHeader {
    pub count: AtomicUsize,
    pub data: u64,
}

/// con-leche: ConLeche/Kernel/Expr.lean:285-403 Expr
/// `Expr.bvar i`.
#[repr(C, align(16))]
pub struct NodeBvar {
    pub h: NodeHeader,
    pub i: u64,
}

/// con-leche: ConLeche/Kernel/Expr.lean:285-403 Expr
/// `Expr.fvar idx ty`.
#[repr(C, align(16))]
pub struct NodeFvar {
    pub h: NodeHeader,
    pub idx: u64,
    pub ty: Expr,
}

/// con-leche: ConLeche/Kernel/Expr.lean:285-403 Expr
/// `Expr.sort u`.
#[repr(C, align(16))]
pub struct NodeSort {
    pub h: NodeHeader,
    pub u: Level,
}

/// con-leche: ConLeche/Kernel/Expr.lean:285-403 Expr
/// `Expr.const n us`; the level list is behind a handle as it was in
/// `ExprKind::Const` (task #38).
#[repr(C, align(16))]
pub struct NodeConst {
    pub h: NodeHeader,
    pub n: Name,
    pub us: P<Vec<Level>>,
}

/// con-leche: ConLeche/Kernel/Expr.lean:285-403 Expr
/// `Expr.app f a` — 65 % of the live nodes of a real term (task #88's
/// census), and the reason this module exists: 32 bytes rather than 64.
#[repr(C, align(16))]
pub struct NodeApp {
    pub h: NodeHeader,
    pub f: Expr,
    pub a: Expr,
}

/// con-leche: ConLeche/Kernel/Expr.lean:285-403 Expr
/// `Expr.lam ty body m` and `Expr.forallE ty body m`: the two binders have
/// the same fields, so they share a struct and differ only in the tag.
#[repr(C, align(16))]
pub struct NodeBinder {
    pub h: NodeHeader,
    pub ty: Expr,
    pub body: Expr,
    pub m: BinderMeta,
}

/// con-leche: ConLeche/Kernel/Expr.lean:285-403 Expr
/// `Expr.letE ty value body`.
#[repr(C, align(16))]
pub struct NodeLetE {
    pub h: NodeHeader,
    pub ty: Expr,
    pub value: Expr,
    pub body: Expr,
}

/// con-leche: ConLeche/Kernel/Expr.lean:285-403 Expr
/// `Expr.lit l`.
#[repr(C, align(16))]
pub struct NodeLit {
    pub h: NodeHeader,
    pub l: Literal,
}

/// con-leche: ConLeche/Kernel/Expr.lean:285-403 Expr
/// `Expr.proj n idx e`.
#[repr(C, align(16))]
pub struct NodeProj {
    pub h: NodeHeader,
    pub n: Name,
    pub idx: u64,
    pub e: Expr,
}

// ---------------------------------------------------------------------------
// The view
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/Expr.lean:285-403 Expr
/// The ten constructors as a **borrowed** enum: what a reader matches on.
///
/// Every arm holds references, including the scalar ones (`&u64`), so that a
/// `match view(e)` binds exactly what `match &e.0.kind` bound before this
/// task — the mechanical rewrite of the 302 reader sites is then the
/// scrutinee and the enum's name, nothing else.
///
/// In the model this is the projection: `view` has one equation per
/// `alloc_*`, and those ten equations are the whole of the external hole
/// (DESIGN.md §3.2 and the module note).
pub enum ExprView<'a> {
    Bvar(&'a u64),
    Fvar(&'a u64, &'a Expr),
    Sort(&'a Level),
    Const(&'a Name, &'a P<Vec<Level>>),
    App(&'a Expr, &'a Expr),
    Lam(&'a Expr, &'a Expr, &'a BinderMeta),
    ForallE(&'a Expr, &'a Expr, &'a BinderMeta),
    LetE(&'a Expr, &'a Expr, &'a Expr),
    Lit(&'a Literal),
    Proj(&'a Name, &'a u64, &'a Expr),
}

/// con-leche: ConLeche/Kernel/Expr.lean:285-403 Expr
/// Look at a term's constructor: the `match` every reader of the core does.
///
/// Sound by the module note's invariant — the tag was written by `alloc_*`
/// beside the struct it names — and the `_` arm is unreachable for the same
/// reason: a tag is never anything but the ten constants above.
#[inline]
pub fn view<'a>(e: &'a Expr) -> ExprView<'a> {
    let t: usize = tag_of(e);
    let p: *mut u8 = addr_of(e);
    unsafe {
        match t {
            TAG_BVAR => {
                let n: &NodeBvar = &*(p as *const NodeBvar);
                ExprView::Bvar(&n.i)
            }
            TAG_FVAR => {
                let n: &NodeFvar = &*(p as *const NodeFvar);
                ExprView::Fvar(&n.idx, &n.ty)
            }
            TAG_SORT => {
                let n: &NodeSort = &*(p as *const NodeSort);
                ExprView::Sort(&n.u)
            }
            TAG_CONST => {
                let n: &NodeConst = &*(p as *const NodeConst);
                ExprView::Const(&n.n, &n.us)
            }
            TAG_APP => {
                let n: &NodeApp = &*(p as *const NodeApp);
                ExprView::App(&n.f, &n.a)
            }
            TAG_LAM => {
                let n: &NodeBinder = &*(p as *const NodeBinder);
                ExprView::Lam(&n.ty, &n.body, &n.m)
            }
            TAG_FORALL_E => {
                let n: &NodeBinder = &*(p as *const NodeBinder);
                ExprView::ForallE(&n.ty, &n.body, &n.m)
            }
            TAG_LET_E => {
                let n: &NodeLetE = &*(p as *const NodeLetE);
                ExprView::LetE(&n.ty, &n.value, &n.body)
            }
            TAG_LIT => {
                let n: &NodeLit = &*(p as *const NodeLit);
                ExprView::Lit(&n.l)
            }
            TAG_PROJ => {
                let n: &NodeProj = &*(p as *const NodeProj);
                ExprView::Proj(&n.n, &n.idx, &n.e)
            }
            _ => std::hint::unreachable_unchecked(),
        }
    }
}

// ---------------------------------------------------------------------------
// Allocation
// ---------------------------------------------------------------------------

/// con-leche: none — the one place a node and its tag are written together
/// Allocate `node` with 16-byte alignment and hand back the tagged handle.
///
/// Generic in the struct so that the `(tag, struct)` pairing lives in the ten
/// one-line `alloc_*` below and nowhere else; the count starts at one, as
/// `Arc::new`'s does.
#[inline]
unsafe fn new_node<T>(node: T, tag: usize) -> Expr {
    let l: Layout = Layout::new::<T>();
    let p: *mut u8 = std::alloc::alloc(l);
    if p.is_null() {
        std::alloc::handle_alloc_error(l);
    }
    std::ptr::write(p as *mut T, node);
    Expr(ExprPtr {
        p: NonNull::new_unchecked(((p as usize) | tag) as *mut u8),
    })
}

/// con-leche: none — the common header of a freshly allocated node
#[inline]
fn hdr(data: u64) -> NodeHeader {
    NodeHeader { count: AtomicUsize::new(1), data }
}

/// con-leche: ConLeche/Kernel/Expr.lean:285-403 Expr
/// `Expr.bvar`'s node, with the packed word its smart constructor computed.
#[inline]
pub fn alloc_bvar(data: u64, i: u64) -> Expr {
    unsafe { new_node(NodeBvar { h: hdr(data), i }, TAG_BVAR) }
}

/// con-leche: ConLeche/Kernel/Expr.lean:285-403 Expr
/// `Expr.fvar`'s node.
#[inline]
pub fn alloc_fvar(data: u64, idx: u64, ty: Expr) -> Expr {
    unsafe { new_node(NodeFvar { h: hdr(data), idx, ty }, TAG_FVAR) }
}

/// con-leche: ConLeche/Kernel/Expr.lean:285-403 Expr
/// `Expr.sort`'s node.
#[inline]
pub fn alloc_sort(data: u64, u: Level) -> Expr {
    unsafe { new_node(NodeSort { h: hdr(data), u }, TAG_SORT) }
}

/// con-leche: ConLeche/Kernel/Expr.lean:285-403 Expr
/// `Expr.const`'s node; the level list arrives already behind its handle.
#[inline]
pub fn alloc_const(data: u64, n: Name, us: P<Vec<Level>>) -> Expr {
    unsafe { new_node(NodeConst { h: hdr(data), n, us }, TAG_CONST) }
}

/// con-leche: ConLeche/Kernel/Expr.lean:285-403 Expr
/// `Expr.app`'s node — the hot one.
#[inline]
pub fn alloc_app(data: u64, f: Expr, a: Expr) -> Expr {
    unsafe { new_node(NodeApp { h: hdr(data), f, a }, TAG_APP) }
}

/// con-leche: ConLeche/Kernel/Expr.lean:285-403 Expr
/// `Expr.lam`'s node.
#[inline]
pub fn alloc_lam(data: u64, ty: Expr, body: Expr, m: BinderMeta) -> Expr {
    unsafe { new_node(NodeBinder { h: hdr(data), ty, body, m }, TAG_LAM) }
}

/// con-leche: ConLeche/Kernel/Expr.lean:285-403 Expr
/// `Expr.forallE`'s node: [`NodeBinder`] again, a different tag.
#[inline]
pub fn alloc_forall_e(data: u64, ty: Expr, body: Expr, m: BinderMeta) -> Expr {
    unsafe { new_node(NodeBinder { h: hdr(data), ty, body, m }, TAG_FORALL_E) }
}

/// con-leche: ConLeche/Kernel/Expr.lean:285-403 Expr
/// `Expr.letE`'s node.
#[inline]
pub fn alloc_let_e(data: u64, ty: Expr, value: Expr, body: Expr) -> Expr {
    unsafe { new_node(NodeLetE { h: hdr(data), ty, value, body }, TAG_LET_E) }
}

/// con-leche: ConLeche/Kernel/Expr.lean:285-403 Expr
/// `Expr.lit`'s node.
#[inline]
pub fn alloc_lit(data: u64, l: Literal) -> Expr {
    unsafe { new_node(NodeLit { h: hdr(data), l }, TAG_LIT) }
}

/// con-leche: ConLeche/Kernel/Expr.lean:285-403 Expr
/// `Expr.proj`'s node.
#[inline]
pub fn alloc_proj(data: u64, n: Name, idx: u64, e: Expr) -> Expr {
    unsafe { new_node(NodeProj { h: hdr(data), n, idx, e }, TAG_PROJ) }
}

// ---------------------------------------------------------------------------
// The four pointer operations (DESIGN.md §3.2)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/Expr.lean:285-403 Expr
/// The cached `@[computed_field] data`, an `O(1)` field read — the header is
/// at the node's address whatever the tag, so this needs no dispatch.
#[inline]
pub fn data(e: &Expr) -> u64 {
    unsafe { (*(addr_of(e) as *const NodeHeader)).data }
}

/// con-leche: none — the count bump that Lean's value semantics hides (DESIGN.md §3.2)
/// Share a term: `Arc::clone`'s `Relaxed` increment, verbatim.
#[inline]
pub fn dup(e: &Expr) -> Expr {
    unsafe {
        (*(addr_of(e) as *const NodeHeader))
            .count
            .fetch_add(1, Ordering::Relaxed);
    }
    Expr(ExprPtr { p: e.0.p })
}

/// con-leche: ConLeche/Kernel/Expr.lean:955-960 Expr.beqMemo
/// Do the two handles point at the same node?  Modeled as `false`
/// (DESIGN.md §3.2), so each fast path needs its reflexivity lemma.
///
/// Comparing the *tagged* words is the same test as comparing the addresses:
/// a node's tag is a function of the node.
#[inline]
pub fn ptr_eq(a: &Expr, b: &Expr) -> bool {
    word_of(a) == word_of(b)
}

/// con-leche: none — the address `con-ron`'s ground-term table hashes (task #89)
/// The handle as an integer.  Outside the verified core's reach: nothing in
/// `kernel/` or `cached/` calls it, and the model has no address at all.
#[inline]
pub fn addr_word(e: &Expr) -> usize {
    word_of(e)
}

// ---------------------------------------------------------------------------
// Release
// ---------------------------------------------------------------------------

/// con-leche: none — `Arc`'s `Drop`, written out per kind (DESIGN.md §3.2)
/// Release one handle: `Arc::drop`'s protocol exactly — a `Release`
/// decrement, and the single thread that observes the old count as one takes
/// an `Acquire` fence and then drops the payload and frees the block.
///
/// Dropping the payload drops the children, so this recurses to the depth of
/// the term, as `Arc<ExprNode>`'s derived drop did before task #94: the
/// stack depth question is unchanged, not introduced (task #94's report).
#[inline]
fn release(e: &Expr) {
    unsafe {
        let p: *mut u8 = addr_of(e);
        if (*(p as *const NodeHeader)).count.fetch_sub(1, Ordering::Release) != 1 {
            return;
        }
        atomic::fence(Ordering::Acquire);
        free_node(p, tag_of(e));
    }
}

/// con-leche: none — the per-kind half of [`release`]
/// Drop the payload in place and return the block, with the struct the tag
/// names and hence the `Layout` it was allocated with.
#[inline(never)]
unsafe fn free_node(p: *mut u8, t: usize) {
    match t {
        TAG_BVAR => drop_as::<NodeBvar>(p),
        TAG_FVAR => drop_as::<NodeFvar>(p),
        TAG_SORT => drop_as::<NodeSort>(p),
        TAG_CONST => drop_as::<NodeConst>(p),
        TAG_APP => drop_as::<NodeApp>(p),
        TAG_LAM => drop_as::<NodeBinder>(p),
        TAG_FORALL_E => drop_as::<NodeBinder>(p),
        TAG_LET_E => drop_as::<NodeLetE>(p),
        TAG_LIT => drop_as::<NodeLit>(p),
        TAG_PROJ => drop_as::<NodeProj>(p),
        _ => std::hint::unreachable_unchecked(),
    }
}

/// con-leche: none — drop-in-place plus deallocate, at one type
#[inline]
unsafe fn drop_as<T>(p: *mut u8) {
    std::ptr::drop_in_place(p as *mut T);
    std::alloc::dealloc(p, Layout::new::<T>());
}

/// con-leche: none — the `Drop` that makes an `Expr` an owning handle
/// What `Arc<ExprNode>`'s own `Drop` did until task #94.
impl Drop for Expr {
    fn drop(&mut self) {
        release(self);
    }
}
