//! con-leche: none — `Expr`'s instantiation of `ron::tagged` (DESIGN.md §3.2, task #94).
//!
//! `ron::node` — **the ten `Expr` cells, as a table**.
//!
//! Until task #94 every `Expr` node was a `P<ExprNode>`: a block as wide as
//! the *widest* `ExprKind` arm, plus a kind word, plus `Arc`'s two counts —
//! 64 bytes for an `app`, which is 65 % of the live nodes of a real term
//! (task #88's census) and needs 32.  Lean's own representation does not do
//! that: the kind is in the object header, and each constructor's object is
//! as wide as its own fields.
//!
//! So the kind moved into the handle, and `ron::tagged` is the machinery that
//! puts it there.  **This file has no `unsafe` in it** — it is a table of ten
//! `tag => variant: type` lines, ten struct declarations, and thin wrappers:
//!
//! | tag | cell | payload | `size_of<Block<…>>` | mimalloc class |
//! |---:|---|---|---:|---:|
//! | 0 | [`NodeBvar`] | `u64` | **32** | 32 |
//! | 1 | [`NodeFvar`] | `u64, Expr` | **32** | 32 |
//! | 2 | [`NodeSort`] | `Level` | **32** | 32 |
//! | 3 | [`NodeConst`] | `Name, P<Vec<Level>>` | **32** | 32 |
//! | 4 | [`NodeApp`] | `Expr, Expr` | **32** | 32 |
//! | 5 | [`NodeLam`] | `Expr, Expr, BinderMeta` | **48** | 48 |
//! | 6 | [`NodeForallE`] | the same three | **48** | 48 |
//! | 7 | [`NodeLetE`] | `Expr, Expr, Expr` | **48** | 48 |
//! | 8 | [`NodeLit`] | `Literal` | **32** | 32 |
//! | 9 | [`NodeProj`] | `Name, u64, Expr` | **48** | 48 |
//!
//! against **64 bytes for all ten** before; `con-ron-dump`'s `node_sizes`
//! test pins every row and its alignment.  The header (the atomic count and
//! con-leche's `@[computed_field] data`) is `ron::tagged::Block`'s, so a node
//! struct here holds only the constructor's own fields.
//!
//! `lam` and `forallE` have the same fields but are **two types**, not one
//! type with two tags: the `Kind` trait keys the cast on the type, and two
//! names cost nothing at run time (the layouts are identical) while making
//! the table say what it means.
//!
//! # The model (DESIGN.md §3.2)
//!
//! §3.2's rule for the pointer is "an `Arc` is its contents".  The same rule
//! reads here as **"an `Expr` is the constructor it was allocated from"**:
//! [`view`] is the projection, the ten `alloc_*` are the constructors, and
//! [`data`] is the `@[computed_field]`.  `ron::tagged::Raw<T>` carries
//! `ExprNode` as its modeled `T`, so `Generated/Types.lean`'s
//! `ExprKind`/`ExprNode`/`Expr` block is **unchanged** and the type-level hole
//! is the one line `Raw T := T`.  Both this module and `ron::tagged` are
//! opaque to Charon (`crates/con-ron-core/Cargo.toml`'s
//! `[package.metadata.charon]`); `ExprView` is pulled back to transparent,
//! because every reader in the core matches on it.

use crate::kernel::expr::BinderMeta;
use crate::kernel::expr::Expr;
use crate::kernel::expr::ExprNode;
use crate::kernel::expr::Literal;
use crate::kernel::level::Level;
use crate::kernel::name::Name;
use crate::ron::ptr::P;

// ---------------------------------------------------------------------------
// The ten cells
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/Expr.lean:285-403 Expr
/// `Expr.bvar i`.
#[repr(C)]
pub struct NodeBvar {
    pub i: u64,
}

/// con-leche: ConLeche/Kernel/Expr.lean:285-403 Expr
/// `Expr.fvar idx ty`.
#[repr(C)]
pub struct NodeFvar {
    pub idx: u64,
    pub ty: Expr,
}

/// con-leche: ConLeche/Kernel/Expr.lean:285-403 Expr
/// `Expr.sort u`.
#[repr(C)]
pub struct NodeSort {
    pub u: Level,
}

/// con-leche: ConLeche/Kernel/Expr.lean:285-403 Expr
/// `Expr.const n us`; the level list is behind a handle as it was in
/// `ExprKind::Const` (task #38).
#[repr(C)]
pub struct NodeConst {
    pub n: Name,
    pub us: P<Vec<Level>>,
}

/// con-leche: ConLeche/Kernel/Expr.lean:285-403 Expr
/// `Expr.app f a` — 65 % of the live nodes of a real term (task #88's
/// census), and the reason this module exists: 32 bytes rather than 64.
#[repr(C)]
pub struct NodeApp {
    pub f: Expr,
    pub a: Expr,
}

/// con-leche: ConLeche/Kernel/Expr.lean:285-403 Expr
/// `Expr.lam ty body m`.
#[repr(C)]
pub struct NodeLam {
    pub ty: Expr,
    pub body: Expr,
    pub m: BinderMeta,
}

/// con-leche: ConLeche/Kernel/Expr.lean:285-403 Expr
/// `Expr.forallE ty body m`: [`NodeLam`]'s fields under its own name, so that
/// the table keys the cast on the constructor rather than on a shared struct.
#[repr(C)]
pub struct NodeForallE {
    pub ty: Expr,
    pub body: Expr,
    pub m: BinderMeta,
}

/// con-leche: ConLeche/Kernel/Expr.lean:285-403 Expr
/// `Expr.letE ty value body`.
#[repr(C)]
pub struct NodeLetE {
    pub ty: Expr,
    pub value: Expr,
    pub body: Expr,
}

/// con-leche: ConLeche/Kernel/Expr.lean:285-403 Expr
/// `Expr.lit l`.
#[repr(C)]
pub struct NodeLit {
    pub l: Literal,
}

/// con-leche: ConLeche/Kernel/Expr.lean:285-403 Expr
/// `Expr.proj n idx e`.
#[repr(C)]
pub struct NodeProj {
    pub n: Name,
    pub idx: u64,
    pub e: Expr,
}

// ---------------------------------------------------------------------------
// The table
// ---------------------------------------------------------------------------

// **The ten constructors, as the ten tags** (con-leche:
// ConLeche/Kernel/Expr.lean:285-403 Expr, the cited inductive's constructors).
// `ron::tagged`'s macro turns this table into the `unsafe impl Kind`s, a
// compile-time check that the tags are in range and pairwise distinct, the
// `ExprHandle` alias, one `pub const` per kind (the names `view` matches on)
// and the scheme's `release`.  Nothing below this line is `unsafe`, and nothing above it is
// either.  (A `//` comment rather than a `///` one: a doc comment on a macro
// invocation attaches to nothing, and `provenance.py` reads the items the
// macro *expands to* through `ron::tagged`'s own citations.)
crate::tagged_kinds! {
    handle ExprHandle, release release, modeled ExprNode;
    0 => TAG_BVAR:    NodeBvar,
    1 => TAG_FVAR:    NodeFvar,
    2 => TAG_SORT:    NodeSort,
    3 => TAG_CONST:   NodeConst,
    4 => TAG_APP:     NodeApp,
    5 => TAG_LAM:     NodeLam,
    6 => TAG_FORALL_E: NodeForallE,
    7 => TAG_LET_E:    NodeLetE,
    8 => TAG_LIT:     NodeLit,
    9 => TAG_PROJ:    NodeProj,
}

// ---------------------------------------------------------------------------
// The view
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/Expr.lean:285-403 Expr
/// The ten constructors as a **borrowed** enum: what a reader matches on.
///
/// Every arm holds references, including the scalar ones (`&u64`), so that a
/// `match view(e)` binds exactly what `match &e.0.kind` bound before task #94
/// — the rewrite of the core's 303 reader sites was the scrutinee and this
/// enum's name, nothing else.
///
/// In the model this is the projection's target: [`view`] has one equation per
/// `alloc_*` (DESIGN.md §3.2 and the module note).
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
/// Safe code: the arm names are the table's own `pub const`s, `Raw::cast` is
/// total, and the default arm is a *call* to `ron::tagged::bad_tag` — the one
/// place that says a handle's tag is always its table's — rather than an
/// `unreachable!` here.  So this file needs neither `unsafe` nor a lint
/// exemption.  What it compiles to is a tag mask and an indirect branch.
#[inline]
pub fn view(e: &Expr) -> ExprView<'_> {
    match e.0.tag() {
        TAG_BVAR => ExprView::Bvar(&e.0.cast::<NodeBvar>().i),
        TAG_FVAR => {
            let c: &NodeFvar = e.0.cast::<NodeFvar>();
            ExprView::Fvar(&c.idx, &c.ty)
        }
        TAG_SORT => ExprView::Sort(&e.0.cast::<NodeSort>().u),
        TAG_CONST => {
            let c: &NodeConst = e.0.cast::<NodeConst>();
            ExprView::Const(&c.n, &c.us)
        }
        TAG_APP => {
            let c: &NodeApp = e.0.cast::<NodeApp>();
            ExprView::App(&c.f, &c.a)
        }
        TAG_LAM => {
            let c: &NodeLam = e.0.cast::<NodeLam>();
            ExprView::Lam(&c.ty, &c.body, &c.m)
        }
        TAG_FORALL_E => {
            let c: &NodeForallE = e.0.cast::<NodeForallE>();
            ExprView::ForallE(&c.ty, &c.body, &c.m)
        }
        TAG_LET_E => {
            let c: &NodeLetE = e.0.cast::<NodeLetE>();
            ExprView::LetE(&c.ty, &c.value, &c.body)
        }
        TAG_LIT => ExprView::Lit(&e.0.cast::<NodeLit>().l),
        TAG_PROJ => {
            let c: &NodeProj = e.0.cast::<NodeProj>();
            ExprView::Proj(&c.n, &c.idx, &c.e)
        }
        t => crate::ron::tagged::bad_tag(t),
    }
}

// ---------------------------------------------------------------------------
// Allocation
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/Expr.lean:285-403 Expr
/// `Expr.bvar`'s cell, with the packed word its smart constructor computed.
#[inline]
pub fn alloc_bvar(data: u64, i: u64) -> Expr {
    Expr(ExprHandle::alloc(data, NodeBvar { i }))
}

/// con-leche: ConLeche/Kernel/Expr.lean:285-403 Expr
/// `Expr.fvar`'s cell.
#[inline]
pub fn alloc_fvar(data: u64, idx: u64, ty: Expr) -> Expr {
    Expr(ExprHandle::alloc(data, NodeFvar { idx, ty }))
}

/// con-leche: ConLeche/Kernel/Expr.lean:285-403 Expr
/// `Expr.sort`'s cell.
#[inline]
pub fn alloc_sort(data: u64, u: Level) -> Expr {
    Expr(ExprHandle::alloc(data, NodeSort { u }))
}

/// con-leche: ConLeche/Kernel/Expr.lean:285-403 Expr
/// `Expr.const`'s cell; the level list arrives already behind its handle.
#[inline]
pub fn alloc_const(data: u64, n: Name, us: P<Vec<Level>>) -> Expr {
    Expr(ExprHandle::alloc(data, NodeConst { n, us }))
}

/// con-leche: ConLeche/Kernel/Expr.lean:285-403 Expr
/// `Expr.app`'s cell — the hot one.
#[inline]
pub fn alloc_app(data: u64, f: Expr, a: Expr) -> Expr {
    Expr(ExprHandle::alloc(data, NodeApp { f, a }))
}

/// con-leche: ConLeche/Kernel/Expr.lean:285-403 Expr
/// `Expr.lam`'s cell.
#[inline]
pub fn alloc_lam(data: u64, ty: Expr, body: Expr, m: BinderMeta) -> Expr {
    Expr(ExprHandle::alloc(data, NodeLam { ty, body, m }))
}

/// con-leche: ConLeche/Kernel/Expr.lean:285-403 Expr
/// `Expr.forallE`'s cell.
#[inline]
pub fn alloc_forall_e(data: u64, ty: Expr, body: Expr, m: BinderMeta) -> Expr {
    Expr(ExprHandle::alloc(data, NodeForallE { ty, body, m }))
}

/// con-leche: ConLeche/Kernel/Expr.lean:285-403 Expr
/// `Expr.letE`'s cell.
#[inline]
pub fn alloc_let_e(data: u64, ty: Expr, value: Expr, body: Expr) -> Expr {
    Expr(ExprHandle::alloc(data, NodeLetE { ty, value, body }))
}

/// con-leche: ConLeche/Kernel/Expr.lean:285-403 Expr
/// `Expr.lit`'s cell.
#[inline]
pub fn alloc_lit(data: u64, l: Literal) -> Expr {
    Expr(ExprHandle::alloc(data, NodeLit { l }))
}

/// con-leche: ConLeche/Kernel/Expr.lean:285-403 Expr
/// `Expr.proj`'s cell.
#[inline]
pub fn alloc_proj(data: u64, n: Name, idx: u64, e: Expr) -> Expr {
    Expr(ExprHandle::alloc(data, NodeProj { n, idx, e }))
}

// ---------------------------------------------------------------------------
// The pointer operations (DESIGN.md §3.2)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/Expr.lean:285-403 Expr
/// The cached `@[computed_field] data`, an `O(1)` field read: the header is at
/// the cell's address whatever the tag, so this needs no dispatch.
#[inline]
pub fn data(e: &Expr) -> u64 {
    e.0.header().data
}

/// con-leche: none — the count bump that Lean's value semantics hides (DESIGN.md §3.2)
/// Share a term: `Arc::clone`'s `Relaxed` increment, through the handle.
#[inline]
pub fn dup(e: &Expr) -> Expr {
    Expr(e.0.bump())
}

/// con-leche: ConLeche/Kernel/Expr.lean:955-960 Expr.beqMemo
/// Do the two handles point at the same cell?  Modeled as `false`
/// (DESIGN.md §3.2), so each fast path needs its reflexivity lemma.
#[inline]
pub fn ptr_eq(a: &Expr, b: &Expr) -> bool {
    ExprHandle::ptr_eq(&a.0, &b.0)
}

/// con-leche: none — `Arc`'s `Drop`, through the table's `release` (DESIGN.md §3.2)
/// An `Expr` is the owner of its share; `ron::tagged::Raw` has none, because
/// releasing needs the tag→type table only the table above has.  Releasing a
/// block drops its payload, which drops the children, so this recurses to the
/// depth of the term — as `Arc<ExprNode>`'s derived drop did before task #94.
/// The stack-depth question is unchanged, not introduced.
impl Drop for Expr {
    fn drop(&mut self) {
        release(&self.0)
    }
}

/// con-leche: none — the address `con-ron`'s ground-term table hashes (task #89)
/// The handle as an integer.  Outside the verified core's reach: nothing in
/// `kernel/` or `cached/` calls it, and the model has no address at all.
#[inline]
pub fn addr_word(e: &Expr) -> usize {
    e.0.addr_word()
}
