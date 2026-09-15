//! con-leche: none — the tagged counted handle of DESIGN.md §3.2 (task #94).
//!
//! `ron::tagged` — **the crate's only `unsafe`, and it does not know what an
//! `Expr` is**.
//!
//! One counted handle, one word wide, whose low four bits say which of a
//! *scheme's* node types the rest of it points at.  Every block is allocated
//! 16-aligned, which is what frees those four bits; sixteen kinds fit, and
//! each kind's block is as wide as that kind needs rather than as wide as the
//! widest.  That is the whole idea, and the measurement behind it is task
//! #94's report: `Expr`'s nodes go from a flat 64-byte block to 32 or 48
//! bytes, which is −45 % of Mathlib's peak.
//!
//! **This module is generic.**  It names no term type, no constructor and no
//! kind: a *scheme* is a table, and [`tagged_kinds!`] turns it into the
//! tag→type dispatch and the release.  `ron::node` is the one instantiation
//! today (`Expr`'s ten blocks); `Name`, `Level` and `PropWhen` keep
//! `ron::ptr::P` (DESIGN.md §3.2 — their nodes are not the bulk, and a
//! uniform block costs them nothing).
//!
//! # This module is `pub(crate)`, and that is a safety property
//!
//! An external review of 2026-09-15 found three holes in an earlier cut of
//! this file, all of them in what it *exposed* rather than in what it does.
//! They are worth stating, because the shape of the module is now their fix:
//!
//! 1. **A safe use-after-free.**  [`Raw::alloc`], `bump`, `drop_share`, the
//!    address accessors and a scheme's generated `release` were `pub` and
//!    safe, so any downstream crate — including this workspace's own
//!    `con-ron` — could allocate a handle, release it and then read its
//!    header, with no `unsafe` written anywhere.  **Fixed by visibility**: the
//!    module is `pub(crate)`, every method on [`Raw`] is `pub(crate)` at most,
//!    and `ron::node`'s `release`/`free_block` are private to that module.
//!    The public API of the representation is now exactly `Expr`'s ten
//!    `alloc_*`, `view`, `data`, `dup`, `ptr_eq` and `addr_word` — none of
//!    which can release a block or hand out an address that could be.
//! 2. **Type confusion across schemes.**  [`Raw::get`] checked `K::TAG` and
//!    nothing else, and the macro was `#[macro_export]`, so a *second* scheme
//!    with a kind at tag 0 could read an `Expr` block as that kind.  **Fixed
//!    by the type system**: [`Kind`] names its [`Model`], `Raw<M>` is the
//!    handle of model `M`, and `get`/`cast` demand `K: Kind<Model = M>`.  A
//!    handle can only be cast to a kind of its own scheme, by construction and
//!    not by discipline.  The macro is no longer exported.
//! 3. **Auto traits asserted, not derived.**  `unsafe impl<T> Send for
//!    Raw<T>` said nothing about what a block holds.  **Fixed by deriving
//!    them**: a scheme's [`Model`] carries every payload type as
//!    [`Model::Payloads`], and the impls are conditioned on it, so the
//!    compiler checks each kind's fields.  `tests/send_sync.rs` now means
//!    something.
//!
//! The accounting that follows from those three: the handle is **no worse
//! than `Arc` for a user of the crate**, and it is that by construction — no
//! safe release, no cross-scheme cast, and auto traits derived from the
//! payloads rather than promised.
//!
//! # The `unsafe` surface, in full
//!
//! `scripts/lint-rust-style.sh` exempts this path and no other, so what
//! follows is the entire audit:
//!
//! | # | where | what |
//! |---|---|---|
//! | 1 | [`Raw::alloc`] | `Box::leak`, then `byte_add` of the tag |
//! | 2 | [`Raw::block_addr`] | `byte_sub`, the inverse of (1)'s `byte_add` |
//! | 3 | [`Raw::header`] | the address as `*const Header` |
//! | 4 | [`Raw::get`] | the address as `*const Block<K>`, **after** a tag check |
//! | 5 | [`drop_block`] | `Box::from_raw` at `Block<K>` |
//! | 6, 7 | [`Raw`] | `unsafe impl Send` / `Sync`, conditioned on the payloads |
//! | 8, 9 | [`tagged_kinds!`] | the `unsafe impl Kind` / `unsafe impl Model` it writes, and its call to (5) |
//!
//! Nine sites, **twelve lines** with the word on them, and nothing else in
//! the crate has any.
//!
//! # Why it is sound
//!
//! A handle is **only ever made by [`Raw::alloc`]**, which writes the block
//! and attaches `K::TAG` in the same expression and is the sole writer of the
//! private `p` field; nothing outside this module can build or alter one, and
//! since the module is `pub(crate)` nothing outside the crate can name one.
//! So a handle's tag is always the `TAG` of the `Kind` whose `Block` the
//! address holds, *and* that kind belongs to the handle's own model, because
//! `alloc` demands `K: Kind<Model = M>`.  (4)'s cast is then the tag check
//! made into a type — it is safe code's job to ask for the right `K`, and
//! asking for the wrong one is a `None`, not undefined behaviour.  (3) needs
//! no check at all: every `Block<T>` begins with its [`Header`], `#[repr(C)]`
//! says so, and the alignment is the same 16 for every one of them.
//!
//! `Kind::TAG` is a *safety* contract, which is why [`Kind`] is an `unsafe
//! trait`: it must be ≤ [`TAG_MASK`] and distinct from every other `Kind` of
//! the same model, or (4) would cast a block to the wrong type.
//! [`tagged_kinds!`] is the only sanctioned implementor and it checks both
//! **at compile time** ([`tags_distinct`] in a `const` assertion); a
//! hand-written `unsafe impl Kind` outside this file is what the style lint
//! catches.
//!
//! **Alignment is checked, not assumed.**  [`Block`] is `#[repr(C,
//! align(16))]`, so a conforming allocator hands back an address with four
//! zero low bits and masking them recovers it exactly.  mimalloc's own
//! guarantee covers this by a wide margin — `MI_MAX_ALIGN_SIZE` is 16
//! (`mimalloc/types.h`: "Minimal alignment necessary.  On most platforms 16
//! bytes are needed due to SSE registers for example") and
//! `MI_MAX_ALIGN_GUARANTEE` is `8 * MI_MAX_ALIGN_SIZE` = 128 with the comment
//! "blocks up to this size are always allocated aligned", against blocks of 32
//! and 48 here — but a *violated* allocator contract must never become a
//! corrupted tag, so `alloc` tests the address it got and calls
//! `std::process::abort` if the low bits are not zero.  Not a `debug_assert`,
//! and not a panic: there is nothing to unwind to.
//!
//! The count is `std::sync::Arc`'s, verbatim — `Relaxed` increment with the
//! same `isize::MAX` overflow guard, `Release` decrement, `Acquire` fence
//! before the single thread that observed the old count as one releases the
//! block.
//!
//! # The model (DESIGN.md §3.2)
//!
//! `Raw<M>` carries its **modelled contents** as the phantom `M`: no bytes,
//! never read, there so that Charon sees the shape §3.2 already models for
//! `Arc<T>`.  `M` is also the scheme marker, which is why the handle still has
//! exactly one type parameter and the hole is still the one line
//! `def ron.tagged.Raw (T : Type) : Type := T` — the proof tier's `Expr` stays
//! `mk : … ExprNode`, unchanged.

use std::marker::PhantomData;
use std::ptr::NonNull;
use std::sync::atomic;
use std::sync::atomic::AtomicUsize;
use std::sync::atomic::Ordering;

// ---------------------------------------------------------------------------
// Tags, models and kinds
// ---------------------------------------------------------------------------

/// con-leche: none — the four tag bits a 16-aligned block leaves free (DESIGN.md §3.2)
/// Sixteen kinds fit; `Expr` uses ten.
pub(crate) const TAG_MASK: usize = 15;

/// con-leche: none — `std::sync::Arc`'s own ceiling on a reference count
/// A count past this is a leak that has wrapped; `Arc` aborts there and so
/// does [`Raw::bump`].
const MAX_REFCOUNT: usize = isize::MAX as usize;

/// con-leche: none — a scheme, named by the type its handle is modelled as
/// The marker a family of [`Kind`]s belongs to.  It is the *modelled
/// contents* — `Raw<M>` is the handle of model `M` — so that the handle keeps
/// one type parameter and §3.2's hole keeps one line, and it is the *scheme*
/// at the same time, which is what stops a handle being cast to a kind of some
/// other family.
///
/// **`unsafe` because [`Payloads`](Model::Payloads) is a safety contract**: it
/// must mention every type that is a [`Kind`] of this model, since the
/// `Send`/`Sync` impls on [`Raw`] are conditioned on it and on nothing else.
/// [`tagged_kinds!`] is the only sanctioned implementor, and it writes the
/// tuple from the same table it writes the kinds from.
pub(crate) unsafe trait Model {
    /// con-leche: none — every payload type of this scheme, as one tuple
    /// What `Raw<Self>`'s auto traits are derived from.
    type Payloads;
}

/// con-leche: none — a scheme's node type, and the tag that names it
/// One of a model's block payloads.
///
/// **`unsafe` because `TAG` is a safety contract**: it must be `<= TAG_MASK`
/// and distinct from every other `Kind` of the same [`Model`], or
/// [`Raw::get`] would hand out a reference at the wrong type.  Implement it
/// only through [`tagged_kinds!`], which checks both at compile time.
pub(crate) unsafe trait Kind: Sized {
    /// con-leche: none — the scheme this kind belongs to
    type Model: Model;
    /// con-leche: none — this kind's tag within its model
    const TAG: usize;
}

/// con-leche: none — the tag-distinctness check [`tagged_kinds!`] runs at compile time
/// `true` when every tag is in range and no two are equal.
pub(crate) const fn tags_distinct(tags: &[usize]) -> bool {
    tags_distinct_from(tags, 0)
}

/// con-leche: none — the index recursion behind [`tags_distinct`]
/// DESIGN.md §3.4 is recursion, not loops, in `const` code as anywhere else.
pub(crate) const fn tags_distinct_from(tags: &[usize], i: usize) -> bool {
    if i >= tags.len() {
        true
    } else if tags[i] > TAG_MASK {
        false
    } else if !tag_absent_after(tags, i, i + 1) {
        false
    } else {
        tags_distinct_from(tags, i + 1)
    }
}

/// con-leche: none — "no later tag equals `tags[i]`", the inner recursion
pub(crate) const fn tag_absent_after(tags: &[usize], i: usize, j: usize) -> bool {
    if j >= tags.len() {
        true
    } else if tags[i] == tags[j] {
        false
    } else {
        tag_absent_after(tags, i, j + 1)
    }
}

/// con-leche: none — the one place that says a tag is always one of the scheme's
/// A handle carries a tag its model claims, because [`Raw::alloc`] wrote it
/// beside the block and nothing else can write one.  This is the branch that
/// says so; a scheme's generated dispatch ends here and never arrives.
#[cold]
pub(crate) fn bad_tag(tag: usize) -> ! {
    unreachable!("ron::tagged: a handle carries tag {tag}, which its model does not claim") // lint: allow
}

/// con-leche: none — the allocator broke its alignment contract
/// `Block<K>` is `align(16)` and every allocator on the shortlist gives at
/// least that for a block this small (the module note cites mimalloc's
/// `MI_MAX_ALIGN_GUARANTEE`), but the tag lives in the bits that alignment
/// frees, so a violated contract would silently corrupt it.  **Abort**, not
/// panic: there is no state to unwind to and nothing to report to.
#[cold]
#[inline(never)]
fn misaligned_block() -> ! {
    std::process::abort()
}

/// con-leche: none — the reference count has run away (`std::sync::Arc`'s guard)
/// A count past `isize::MAX` is a leak that would wrap, and a wrapped count
/// frees a live block.  `std::sync::Arc::clone` aborts here and so does
/// [`Raw::bump`]; out of line and `#[cold]`, so the guard costs a
/// predicted-not-taken branch on the hot path and nothing else.
#[cold]
#[inline(never)]
fn count_overflow() -> ! {
    std::process::abort()
}

// ---------------------------------------------------------------------------
// The block
// ---------------------------------------------------------------------------

/// con-leche: none — the two words every block begins with (DESIGN.md §3.2)
/// The strong count (no weak count — the crate never makes a `Weak`, and
/// `ron::ptr`'s module note plus §3.4's lint are why) and the one `u64` a
/// scheme may cache per node, which for `Expr` is con-leche's
/// `@[computed_field] data`.
#[repr(C, align(16))]
pub(crate) struct Header {
    pub(crate) count: AtomicUsize,
    pub(crate) data: u64,
}

/// con-leche: none — a heap block: the header, then the kind's own payload
/// Named `Block` and not `Cell` on purpose: `Cell<` is what §3.4's lint bans
/// (std's interior-mutability cell), and "block" is what the rest of the
/// project calls the bytes an allocator charges for.  `#[repr(C)]` is what
/// makes [`Raw::header`] sound at every kind, and `align(16)` is what frees
/// the tag bits.  Its `size_of` is the block the allocator charges for —
/// `ron::node::block_sizes` reports one row per kind, and that table is the
/// point of the whole module.
#[repr(C, align(16))]
pub(crate) struct Block<T> {
    pub(crate) h: Header,
    pub(crate) t: T,
}

// ---------------------------------------------------------------------------
// The handle
// ---------------------------------------------------------------------------

/// con-leche: none — the counted handle of DESIGN.md §3.2, with the kind in it
/// A block's address with its kind in the low four bits: **one machine word**.
///
/// `M` is the **modelled contents** and the **scheme** at once — a
/// `PhantomData`, no bytes, never read.  As the modelled contents it is what
/// Charon sees the handle carry, so the hole stays the one line §3.2 already
/// writes for `Arc`; as the scheme it is what keeps a handle from being cast
/// to a kind of some other family (the module note, finding 2).
///
/// **A `Raw` is a share of a count, not an owner.**  It has no `Drop`, because
/// releasing needs the tag→type table only a scheme has; the owner is whatever
/// newtype wraps it, and that newtype's `Drop` must call the scheme's
/// `release` (which [`tagged_kinds!`] writes, privately) exactly once.
/// `ron::node` is the only wrapper in this crate and `Expr` is the only owner.
pub(crate) struct Raw<M> {
    p: NonNull<u8>,
    modeled: PhantomData<M>,
}

/// con-leche: none — `Send` for the handle (DESIGN.md §3.2, task #45)
/// `std::sync::Arc<T>`'s argument: the count is atomic and the block is
/// immutable otherwise, so no two threads can race on anything else.  What
/// makes that an argument rather than an assertion is the bound: the payloads
/// are every type a block of this model can hold, and the compiler checks
/// them (the module note, finding 3).  `tests/send_sync.rs` is the standing
/// statement of what it buys.
unsafe impl<M: Model> Send for Raw<M> where M::Payloads: Send + Sync {}

/// con-leche: none — `Sync` for the handle (DESIGN.md §3.2, task #45)
/// See the `Send` impl: a shared `&Raw` exposes only immutable fields and the
/// atomic count, and the payloads carry the same bound.
unsafe impl<M: Model> Sync for Raw<M> where M::Payloads: Send + Sync {}

impl<M: Model> Raw<M> {
    /// con-leche: none — the one place a block and its tag are written together
    /// Allocate a block of kind `K` with `data` in its header and take the
    /// first handle to it.
    ///
    /// This is `unsafe` expression (1) of the module note, and it is the
    /// invariant every other one rests on: the tag attached is `K::TAG`, in
    /// the same expression that puts a `Block<K>` at that address, and `K` is
    /// a kind of *this* model because the bound says so.  The alignment the
    /// tag needs is checked here rather than assumed — see the module note.
    #[inline]
    pub(crate) fn alloc<K: Kind<Model = M>>(data: u64, t: K) -> Self {
        let block: Box<Block<K>> = Box::new(Block {
            h: Header { count: AtomicUsize::new(1), data },
            t,
        });
        let raw: NonNull<Block<K>> = NonNull::from(Box::leak(block));
        if raw.addr().get() & TAG_MASK != 0 {
            misaligned_block();
        }
        // Strict provenance, and the cheapest form of it: the tag is an
        // *offset* into the block rather than an address computed from an
        // integer, so the pointer keeps the provenance `Box::leak` gave it
        // with one `add` and no `usize` round trip.  In bounds because
        // `K::TAG <= TAG_MASK` is 15 and every block is at least 32 bytes
        // (`Header` alone is 16), and exact because the address is 16-aligned,
        // which the test above has just established.
        Raw { p: unsafe { raw.cast::<u8>().byte_add(K::TAG) }, modeled: PhantomData }
    }

    /// con-leche: none — the kind bits of a handle
    /// Which of the model's kinds this block is.
    #[inline]
    pub(crate) fn tag(&self) -> usize {
        self.p.addr().get() & TAG_MASK
    }

    /// con-leche: none — the block's own address, the tag masked off
    /// `unsafe` expression (2).  The inverse of the `byte_add` in
    /// [`Raw::alloc`]: that added `K::TAG` to a 16-aligned address, which
    /// [`Raw::tag`] reads back exactly, so subtracting it lands on the block's
    /// own first byte — in bounds, non-null, and with the allocation's
    /// provenance intact.
    #[inline]
    fn block_addr(&self) -> NonNull<u8> {
        unsafe { self.p.byte_sub(self.tag()) }
    }

    /// con-leche: none — the header, which every kind's block begins with
    /// `unsafe` expression (3): sound at *any* tag, because `Block<T>` is
    /// `#[repr(C)]` with `Header` first and the same alignment for every `T`.
    #[inline]
    pub(crate) fn header(&self) -> &Header {
        unsafe { self.block_addr().cast::<Header>().as_ref() }
    }

    /// con-leche: none — the payload, at the kind the tag names
    /// `unsafe` expression (4), and two checks stand in front of it: the tag
    /// test here, and the `K: Kind<Model = M>` bound, which is what says `K`
    /// is a kind of *this* scheme and not of one that happens to use the same
    /// tag.  Safe code that asks for the wrong kind of the right scheme gets
    /// `None`; asking for a kind of another scheme does not compile.
    #[inline]
    pub(crate) fn get<K: Kind<Model = M>>(&self) -> Option<&K> {
        if self.tag() == K::TAG {
            Some(unsafe { &self.block_addr().cast::<Block<K>>().as_ref().t })
        } else {
            None
        }
    }

    /// con-leche: none — [`Raw::get`] where the tag has already been read
    /// The total form a generated dispatch uses: it has just matched the tag,
    /// so `None` is [`bad_tag`]'s branch and never taken.  **No `unsafe` and
    /// no panic at the call site**, which is what keeps every instantiation of
    /// this module inside the style lint unexempted.
    #[inline]
    pub(crate) fn cast<K: Kind<Model = M>>(&self) -> &K {
        match self.get::<K>() {
            Some(k) => k,
            None => bad_tag(self.tag()),
        }
    }

    /// con-leche: none — `Arc::clone`, a `Relaxed` increment (DESIGN.md §3.2)
    /// Share the block: another handle to the same address and tag.  Not a
    /// `Clone` impl, because a `Raw` is not an owner (see the type's note) and
    /// `#[derive]`-style copying is exactly what must not happen by accident.
    ///
    /// The overflow guard is `std::sync::Arc::clone`'s, verbatim: a count that
    /// passes `isize::MAX` is a leak that would wrap, and wrapping would free
    /// a live block, so abort instead.
    #[inline]
    pub(crate) fn bump(&self) -> Self {
        let old: usize = self.header().count.fetch_add(1, Ordering::Relaxed);
        if old > MAX_REFCOUNT {
            count_overflow();
        }
        Raw { p: self.p, modeled: PhantomData }
    }

    /// con-leche: none — `Arc::drop`'s count half (DESIGN.md §3.2)
    /// Give up one share.  `true` when this thread was the last and must now
    /// release the block — which is the scheme's job, since only it knows the
    /// tag→type table.  The protocol is `std::sync::Arc`'s verbatim: a
    /// `Release` decrement, then an `Acquire` fence on the one thread that
    /// saw the old count as one.
    #[inline]
    pub(crate) fn drop_share(&self) -> bool {
        if self.header().count.fetch_sub(1, Ordering::Release) != 1 {
            return false;
        }
        atomic::fence(Ordering::Acquire);
        true
    }

    /// con-leche: none — the block address, for a scheme's `free_block`
    /// The one caller is the generated release dispatch, which hands it to
    /// [`drop_block`]; it is a bare address and dereferencing it is that
    /// function's `unsafe`, not this one's.  `pub(crate)` and no further: an
    /// address that can be freed is not something the crate hands out.
    #[inline]
    pub(crate) fn addr(&self) -> *mut u8 {
        self.block_addr().as_ptr()
    }

    /// con-leche: none — `Arc::ptr_eq`, modeled as `false` (DESIGN.md §3.2)
    /// Do the two handles point at the same block?  Comparing the *tagged*
    /// addresses is the same test as comparing the blocks': a block's tag is a
    /// function of the block.
    #[inline]
    pub(crate) fn ptr_eq(a: &Self, b: &Self) -> bool {
        a.p.addr() == b.p.addr()
    }

    /// con-leche: none — the handle as an integer, for an address-keyed table
    /// Outside the verified core's reach: nothing in `kernel/` or `cached/`
    /// calls it, and the model has no address at all.  `con-ron`'s frontend
    /// ground-term table and `con-ron-dump`'s DAG census are the two callers,
    /// through `ron::node::addr_word`, and what they get is an integer they
    /// hash and compare — never a pointer they could dereference or free.
    #[inline]
    pub(crate) fn addr_word(&self) -> usize {
        self.p.addr().get()
    }
}

/// con-leche: none — drop the payload and free the block, at one kind
/// `unsafe` expression (5), and the only one a scheme's generated `release`
/// reaches.  **The caller must pass the address of a live `Block<K>` whose
/// count has just reached zero**, which is what [`Raw::drop_share`] returning
/// `true` means and the only thing that calls it.
pub(crate) unsafe fn drop_block<K: Kind>(block: *mut u8) {
    drop(Box::from_raw(block as *mut Block<K>));
}

// ---------------------------------------------------------------------------
// The table
// ---------------------------------------------------------------------------

/// con-leche: none — the scheme table: ten lines in, the unsafe impls out
/// Write a scheme from its `tag => type` table.
///
/// ```ignore
/// crate::ron::tagged::tagged_kinds! {
///     handle ExprHandle, release release, modeled ExprNode;
///     0 => TAG_BVAR: NodeBvar,
///     …
///     9 => TAG_PROJ: NodeProj,
/// }
/// ```
///
/// generates, for that table and nothing else:
///
/// * one `unsafe impl Kind` per type, carrying its tag and naming the
///   model — **the only sanctioned implementor of that trait**;
/// * the `unsafe impl Model` for the modelled type, whose `Payloads` tuple is
///   every kind in the table, which is what [`Raw`]'s `Send`/`Sync` are
///   conditioned on;
/// * a `const` assertion that the tags are in range and pairwise distinct,
///   which is [`Kind`]'s safety contract checked at compile time;
/// * the scheme's handle alias and one `const` per kind, so that the caller's
///   projection is `match h.tag() { TAG_BVAR => h.cast::<NodeBvar>(), … }` —
///   **safe code**, since [`Raw::cast`] is total and [`bad_tag`] is a function
///   rather than an `unreachable!` at the call site;
/// * `release` and `free_block`, **both private to the caller's module**, one
///   [`drop_block`] per tag, which the owning newtype's `Drop` calls.
///
/// The `unsafe` is here, in one file, written once; an instantiation is a
/// table.  The macro is *not* exported: it is crate-internal, and a scheme
/// outside this crate is exactly the type confusion the module note's finding
/// 2 is about.
macro_rules! tagged_kinds {
    (
        handle $handle:ident, release $release:ident, modeled $modeled:ty;
        $( $tag:literal => $var:ident : $kind:ty, )*
    ) => {
        $(
            unsafe impl $crate::ron::tagged::Kind for $kind {
                type Model = $modeled;
                const TAG: usize = $tag;
            }
        )*

        unsafe impl $crate::ron::tagged::Model for $modeled {
            type Payloads = ( $($kind,)* );
        }

        const _: () = {
            assert!(
                $crate::ron::tagged::tags_distinct(&[ $($tag),* ]),
                "tagged_kinds!: the tags must be <= TAG_MASK and pairwise distinct"
            );
        };

        /// con-leche: none — the scheme's handle: `ron::tagged::Raw` at this scheme's modelled type
        /// One machine word (DESIGN.md §3.2, task #94).
        pub(crate) type $handle = $crate::ron::tagged::Raw<$modeled>;

        $(
            /// con-leche: none — this kind's tag, as a `match` pattern
            /// The table's own constant, so that a reader's `match
            /// handle.tag()` names the kinds rather than the numbers.
            const $var: usize = $tag;
        )*

        /// con-leche: none — give up one share, and free the block if it was the last
        /// The owning newtype's `Drop` calls this and nothing else does — it
        /// is private to this module, because a safe `release` anyone can call
        /// twice is a use-after-free (`ron::tagged`'s module note, finding 1).
        /// Only the scheme knows which type a tag names, which is the whole
        /// reason `ron::tagged::Raw` has no `Drop` of its own.
        ///
        /// **Split, and the split is worth 10 % of the binary.**  The common
        /// case is a shared node whose count does not reach zero, so the
        /// decrement is inlined into the caller and only the freeing is a
        /// call — `std::sync::Arc`'s own `drop`/`drop_slow` shape, and
        /// measured: fusing the two cost +1.8 % instructions on `init`
        /// because every drop then paid a call and return (task #94).
        #[inline]
        fn $release(h: &$handle) {
            if h.drop_share() {
                free_block(h)
            }
        }

        /// con-leche: none — the per-kind half of `release`, out of line
        /// Drop the payload and return the block, at the type the tag names.
        #[inline(never)]
        fn free_block(h: &$handle) {
            match h.tag() {
                $( $tag => unsafe {
                    $crate::ron::tagged::drop_block::<$kind>(h.addr())
                }, )*
                // Unreachable (the arms above are all the scheme's tags); a
                // no-op rather than a panic, because leaking an impossible
                // block is safe and panicking in a `Drop` is not.
                _ => {}
            }
        }
    };
}

pub(crate) use tagged_kinds;
