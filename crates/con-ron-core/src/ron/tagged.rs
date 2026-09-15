//! con-leche: none — the tagged counted handle of DESIGN.md §3.2 (task #94).
//!
//! `ron::tagged` — **the crate's only `unsafe`, and it does not know what an
//! `Expr` is**.
//!
//! One counted handle, one word wide, whose low four bits say which of a
//! *scheme's* node types the rest of it points at.  Every node is allocated
//! 16-aligned, which is what frees those four bits; sixteen kinds fit, and
//! each kind's cell is as wide as that kind needs rather than as wide as the
//! widest.  That is the whole idea, and the measurement behind it is task
//! #94's report: `Expr`'s nodes go from a flat 64-byte block to 32 or 48
//! bytes, which is −41 % of Mathlib's peak.
//!
//! **This module is generic.**  It names no term type, no constructor and no
//! kind: a *scheme* is a table, and [`tagged_kinds!`] turns it into the
//! tag→type dispatch and the release.  `ron::node` is
//! the one instantiation today (`Expr`'s ten nodes); `Name`, `Level` and
//! `PropWhen` keep `ron::ptr::P` (DESIGN.md §3.2 — their nodes are not the
//! bulk, and a uniform block costs them nothing).
//!
//! # The `unsafe` surface, in full
//!
//! `scripts/lint-rust-style.sh` exempts this path and no other, so what
//! follows is the entire audit:
//!
//! | # | where | what |
//! |---|---|---|
//! | 1 | [`Raw::alloc`] | `Box::into_raw`, then the tag into the low bits |
//! | 2 | [`Raw::header`] | the address as `*const Header` |
//! | 3 | [`Raw::get`] | the address as `*const Block<K>`, **after** a tag check |
//! | 4 | [`drop_block`] | `Box::from_raw` at `Block<K>` |
//! | 5, 6 | [`Raw`] | `unsafe impl Send` / `Sync` |
//! | 7 | [`tagged_kinds!`] | the `unsafe impl Kind` it writes, and its call to (4) |
//!
//! Four expressions, two impls and one macro.  Nothing else in the crate
//! writes `unsafe`, and a caller of this module never needs to.
//!
//! # Why it is sound
//!
//! A handle is **only ever made by [`Raw::alloc`]**, which writes the block
//! and attaches `K::TAG` in the same expression and is the sole writer of the
//! private `p` field; nothing outside this module can build or alter one.
//! So a handle's tag is always the `TAG` of the `Kind` whose `Block` the
//! address holds, and (3)'s cast is the tag check made into a type — it is
//! safe code's job to ask for the right `K`, and asking for the wrong one is
//! a `None`, not undefined behaviour.  (2) needs no check at all: every
//! `Block<T>` begins with its [`Header`], `#[repr(C)]` says so, and the
//! alignment is the same 16 for every one of them.
//!
//! `Kind::TAG` is a *safety* contract, which is why [`Kind`] is an `unsafe
//! trait`: it must be ≤ [`TAG_MASK`] and distinct within its scheme, or (3)
//! would cast a cell to the wrong type.  [`tagged_kinds!`] is the only
//! sanctioned implementor and it checks both **at compile time**
//! ([`tags_distinct`] in a `const` assertion); a hand-written `unsafe impl
//! Kind` outside this file is what the style lint catches.
//!
//! Alignment: [`Block`] is `#[repr(C, align(16))]`, so every allocation has
//! four zero low bits and masking them recovers the address exactly.
//!
//! The count is `std::sync::Arc`'s, verbatim — `Relaxed` increment, `Release`
//! decrement, `Acquire` fence before the single thread that observed the old
//! count as one releases the cell — and that, with every field a cell holds
//! being itself `Send + Sync`, is the whole of (5) and (6).
//!
//! # The model (DESIGN.md §3.2)
//!
//! `Raw<T>` carries its **modeled contents** as the phantom `T`: no bytes,
//! never read, there so that Charon sees the shape §3.2 already models for
//! `Arc<T>`.  The hole is the same one line —
//! `def ron.tagged.Raw (T : Type) : Type := T` — and the proof tier's
//! `Expr` stays `mk : … ExprNode`, unchanged.  `ron::node`'s `alloc_*` are
//! then the constructors and its `view` the projection; `Generated/Types.lean`
//! does not move.

use std::marker::PhantomData;
use std::ptr::NonNull;
use std::sync::atomic;
use std::sync::atomic::AtomicUsize;
use std::sync::atomic::Ordering;

// ---------------------------------------------------------------------------
// Tags
// ---------------------------------------------------------------------------

/// con-leche: none — the four tag bits a 16-aligned cell leaves free (DESIGN.md §3.2)
/// Sixteen kinds fit; `Expr` uses ten.
pub const TAG_MASK: usize = 15;

/// con-leche: none — a scheme's node type, and the tag that names it
/// One of a scheme's cell payloads.
///
/// **`unsafe` because `TAG` is a safety contract**: it must be `<= TAG_MASK`
/// and distinct from every other `Kind` of the same scheme, or [`Handle::get`]
/// would hand out a reference at the wrong type.  Implement it only through
/// [`tagged_kinds!`], which checks both at compile time.
pub unsafe trait Kind: Sized {
    /// con-leche: none — this kind's tag within its scheme
    const TAG: usize;
}

/// con-leche: none — the tag-distinctness check [`tagged_kinds!`] runs at compile time
/// `true` when every tag is in range and no two are equal.
pub const fn tags_distinct(tags: &[usize]) -> bool {
    tags_distinct_from(tags, 0)
}

/// con-leche: none — the index recursion behind [`tags_distinct`]
/// DESIGN.md §3.4 is recursion, not loops, in `const` code as anywhere else.
pub const fn tags_distinct_from(tags: &[usize], i: usize) -> bool {
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
pub const fn tag_absent_after(tags: &[usize], i: usize, j: usize) -> bool {
    if j >= tags.len() {
        true
    } else if tags[i] == tags[j] {
        false
    } else {
        tag_absent_after(tags, i, j + 1)
    }
}

/// con-leche: none — the one place that says a tag is always one of the scheme's
/// A handle carries a tag its scheme claims, because [`Handle::alloc`] wrote
/// it beside the cell and nothing else can write one.  This is the branch that
/// says so; a scheme's generated dispatch ends here and never arrives.
#[cold]
pub fn bad_tag(tag: usize) -> ! {
    unreachable!("ron::tagged: a handle carries tag {tag}, which its scheme does not claim") // lint: allow
}

// ---------------------------------------------------------------------------
// The block
// ---------------------------------------------------------------------------

/// con-leche: none — the two words every cell begins with (DESIGN.md §3.2)
/// The strong count (no weak count — the crate never makes a `Weak`, and
/// `ron::ptr`'s module note plus §3.4's lint are why) and the one `u64` a
/// scheme may cache per node, which for `Expr` is con-leche's
/// `@[computed_field] data`.
#[repr(C, align(16))]
pub struct Header {
    pub count: AtomicUsize,
    pub data: u64,
}

/// con-leche: none — a heap block: the header, then the kind's own payload
/// Named `Block` and not `Cell` on purpose: `Cell<` is what §3.4's lint
/// bans (std's interior-mutability cell), and "block" is what the rest of
/// the project calls the bytes an allocator charges for.
/// `#[repr(C)]` is what makes [`Handle::header`] sound at every kind, and
/// `align(16)` is what frees the tag bits.  Its `size_of` is the block the
/// allocator charges for — `con-ron-dump`'s `node_sizes` prints one row per
/// kind, and that table is the point of the whole module.
#[repr(C, align(16))]
pub struct Block<T> {
    pub h: Header,
    pub t: T,
}

// ---------------------------------------------------------------------------
// The handle
// ---------------------------------------------------------------------------

/// con-leche: none — the counted handle of DESIGN.md §3.2, with the kind in it
/// A block's address with its kind in the low four bits: **one machine word**.
///
/// `T` is the **modeled contents** — a `PhantomData`, no bytes, never read,
/// there so that Charon sees the shape §3.2 already models for `Arc<T>`.  The
/// hole is the same one line, `def ron.tagged.Raw (T : Type) : Type := T`, and
/// the proof tier's `Expr` stays `mk : … ExprNode`, unchanged.
///
/// **A `Raw` is a share of a count, not an owner.**  It has no `Drop`, because
/// releasing needs the tag→type table only a scheme has; the owner is whatever
/// newtype wraps it, and that newtype's `Drop` must call the scheme's
/// `release` (which [`tagged_kinds!`] writes) exactly once.  `ron::node` is
/// the only wrapper in this crate and `Expr` is the only owner.
pub struct Raw<T> {
    p: NonNull<u8>,
    modeled: PhantomData<T>,
}

/// con-leche: none — `Send` for the handle (DESIGN.md §3.2, task #45)
/// `std::sync::Arc<T>`'s argument: the count is atomic and the block is
/// immutable otherwise, so no two threads can race on anything else.  `T` is
/// phantom — no value of it is ever stored — so what this asserts is about the
/// *kinds*: every field a block holds must itself be `Send + Sync`, which
/// `tests/send_sync.rs` is the standing check on.
unsafe impl<T> Send for Raw<T> {}

/// con-leche: none — `Sync` for the handle (DESIGN.md §3.2, task #45)
/// See the `Send` impl: a shared `&Raw` exposes only immutable fields and the
/// atomic count.
unsafe impl<T> Sync for Raw<T> {}

impl<T> Raw<T> {
    /// con-leche: none — the one place a block and its tag are written together
    /// Allocate a block of kind `K` with `data` in its header and take the
    /// first handle to it.
    ///
    /// This is `unsafe` expression (1) of the module note, and it is the
    /// invariant every other one rests on: the tag attached is `K::TAG`, in
    /// the same expression that puts a `Block<K>` at that address.
    #[inline]
    pub fn alloc<K: Kind>(data: u64, t: K) -> Self {
        let block: Box<Block<K>> = Box::new(Block {
            h: Header { count: AtomicUsize::new(1), data },
            t,
        });
        let raw: *mut Block<K> = Box::into_raw(block);
        let tagged: usize = (raw as usize) | K::TAG;
        Raw {
            p: unsafe { NonNull::new_unchecked(tagged as *mut u8) },
            modeled: PhantomData,
        }
    }

    /// con-leche: none — the kind bits of a handle
    /// Which of the scheme's kinds this block is.
    #[inline]
    pub fn tag(&self) -> usize {
        (self.p.as_ptr() as usize) & TAG_MASK
    }

    /// con-leche: none — the block address of a handle
    /// Public because a scheme's generated `release` hands it to
    /// [`drop_block`]; it is a bare address and dereferencing it is that
    /// function's `unsafe`, not this one's.
    #[inline]
    pub fn addr(&self) -> *mut u8 {
        ((self.p.as_ptr() as usize) & !TAG_MASK) as *mut u8
    }

    /// con-leche: none — the header, which every kind's block begins with
    /// `unsafe` expression (2): sound at *any* tag, because `Block<T>` is
    /// `#[repr(C)]` with `Header` first and the same alignment for every `T`.
    #[inline]
    pub fn header(&self) -> &Header {
        unsafe { &*(self.addr() as *const Header) }
    }

    /// con-leche: none — the payload, at the kind the tag names
    /// `unsafe` expression (3), and the tag check in front of it is what makes
    /// it sound: `Some` exactly when the block really is a `Block<K>`.  Safe
    /// code that asks for the wrong kind gets `None`.
    #[inline]
    pub fn get<K: Kind>(&self) -> Option<&K> {
        if self.tag() == K::TAG {
            Some(unsafe { &(*(self.addr() as *const Block<K>)).t })
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
    pub fn cast<K: Kind>(&self) -> &K {
        match self.get::<K>() {
            Some(k) => k,
            None => bad_tag(self.tag()),
        }
    }

    /// con-leche: none — `Arc::clone`, a `Relaxed` increment (DESIGN.md §3.2)
    /// Share the block: another handle to the same address and tag.  Not a
    /// `Clone` impl, because a `Raw` is not an owner (see the type's note) and
    /// `#[derive]`-style copying is exactly what must not happen by accident.
    #[inline]
    pub fn bump(&self) -> Self {
        self.header().count.fetch_add(1, Ordering::Relaxed);
        Raw { p: self.p, modeled: PhantomData }
    }

    /// con-leche: none — `Arc::drop`'s count half (DESIGN.md §3.2)
    /// Give up one share.  `true` when this thread was the last and must now
    /// release the block — which is the scheme's job, since only it knows the
    /// tag→type table.  The protocol is `std::sync::Arc`'s verbatim: a
    /// `Release` decrement, then an `Acquire` fence on the one thread that
    /// saw the old count as one.
    #[inline]
    pub fn drop_share(&self) -> bool {
        if self.header().count.fetch_sub(1, Ordering::Release) != 1 {
            return false;
        }
        atomic::fence(Ordering::Acquire);
        true
    }

    /// con-leche: none — `Arc::ptr_eq`, modeled as `false` (DESIGN.md §3.2)
    /// Do the two handles point at the same block?  Comparing the *tagged*
    /// words is the same test as comparing the addresses: a block's tag is a
    /// function of the block.
    #[inline]
    pub fn ptr_eq(a: &Self, b: &Self) -> bool {
        a.p.as_ptr() == b.p.as_ptr()
    }

    /// con-leche: none — the handle as an integer, for an address-keyed table
    /// Outside the verified core's reach: nothing in `kernel/` or `cached/`
    /// calls it, and the model has no address at all.  `con-ron`'s frontend
    /// ground-term table and `con-ron-dump`'s DAG census are the two callers.
    #[inline]
    pub fn addr_word(&self) -> usize {
        self.p.as_ptr() as usize
    }
}

/// con-leche: none — drop the payload and free the block, at one kind
/// `unsafe` expression (4), and the only one a scheme's generated `release`
/// reaches.  **The caller must pass the address of a live `Block<K>` whose
/// count has just reached zero**, which is what [`Raw::drop_share`] returning
/// `true` means and the only thing that calls it.
pub unsafe fn drop_block<K: Kind>(block: *mut u8) {
    drop(Box::from_raw(block as *mut Block<K>));
}

// ---------------------------------------------------------------------------
// The table
// ---------------------------------------------------------------------------

/// con-leche: none — the scheme table: ten lines in, the unsafe impls out
/// Write a scheme from its `tag => type` table.
///
/// ```ignore
/// tagged_kinds! {
///     handle ExprHandle, release release, modeled ExprNode;
///     0 => Bvar: NodeBvar,
///     …
///     9 => Proj: NodeProj,
/// }
/// ```
///
/// generates, for that table and nothing else:
///
/// * one `unsafe impl Kind` per type, carrying its tag — **the only
///   sanctioned implementor of that trait**;
/// * a `const` assertion that the tags are in range and pairwise distinct,
///   which is [`Kind`]'s safety contract checked at compile time;
/// * the scheme's `handle` alias and one `pub const` per kind, so that the
///   caller's projection is `match h.tag() { Bvar => h.cast::<NodeBvar>(), … }`
///   — **safe code**, since [`Raw::cast`] is total and [`bad_tag`] is a
///   function rather than an `unreachable!` at the call site;
/// * `release`, one [`drop_block`] per tag, which the owning newtype's `Drop`
///   calls.
///
/// The `unsafe` is here, in one file, written once; an instantiation is a
/// table.
#[macro_export]
macro_rules! tagged_kinds {
    (
        handle $handle:ident, release $release:ident, modeled $modeled:ty;
        $( $tag:literal => $var:ident : $kind:ty, )*
    ) => {
        $(
            unsafe impl $crate::ron::tagged::Kind for $kind {
                const TAG: usize = $tag;
            }
        )*

        const _: () = {
            assert!(
                $crate::ron::tagged::tags_distinct(&[ $($tag),* ]),
                "tagged_kinds!: the tags must be <= TAG_MASK and pairwise distinct"
            );
        };

        /// con-leche: none — the scheme's handle: `ron::tagged::Raw` at this scheme's modeled type
        /// One machine word (DESIGN.md §3.2, task #94).
        pub type $handle = $crate::ron::tagged::Raw<$modeled>;

        $(
            /// con-leche: none — this kind's tag, as a `match` pattern
            /// The table's own constant, so that a reader's `match
            /// handle.tag()` names the kinds rather than the numbers.
            pub const $var: usize = $tag;
        )*

        /// con-leche: none — give up one share, and free the block if it was the last
        /// The owning newtype's `Drop` calls this and nothing else does: only
        /// the scheme knows which type a tag names, which is the whole reason
        /// `ron::tagged::Raw` has no `Drop` of its own.
        ///
        /// **Split, and the split is worth 10 % of the binary.**  The common
        /// case is a shared node whose count does not reach zero, so the
        /// decrement is inlined into the caller and only the freeing is a
        /// call — `std::sync::Arc`'s own `drop`/`drop_slow` shape, and
        /// measured: fusing the two cost +1.8 % instructions on `init`
        /// because every drop then paid a call and return (task #94).
        #[inline]
        pub fn $release(h: &$handle) {
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
