//! The arena's handles (DESIGN.md §8.3, task #97 P4a), transliterated from
//! `proof/ConRon/Arena/Handle.lean` line for line.
//!
//! One 32-bit word per handle:
//!
//! ```text
//! bits 31…28   ctor tag   (4 bits, high)
//! bit  27      tier       (0 = persistent, 1 = scratch)
//! bits 26…0    index      into THAT CONSTRUCTOR'S array of THAT TIER
//! ```
//!
//! so 134 217 728 nodes per constructor per tier, and — the point of putting
//! the tier *above* the index rather than in the low bit (con-leche's lesson
//! 6) — a persistent handle's bits never change when the scratch tier comes
//! and goes.
//!
//! ## Arithmetic, not bit operations
//!
//! The Lean packs with `*`, `/` and `%` by powers of two rather than
//! `<<<`/`&&&`/`|||`, because the bitwise roundtrip lemmas are not
//! `omega`-provable and `bv_decide` **adds an axiom** to the trust surface
//! (DESIGN.md §8's task #97a, "Deviations from §8.3 / §8.4").  This module
//! mirrors that spelling exactly, so that the extracted model is the twin's
//! term for term: `word_mk` is a multiply-and-add, `word_tag` a divide,
//! `word_index` a remainder.  LLVM emits the same shift-and-mask either way.
//!
//! ## Four newtypes, not one phantom-typed handle
//!
//! The Lean has one `Idx k` over a phantom `IdxKind`, which is nanoda's
//! `Ptr<A>` with `PhantomData<A>` spelled as a type index.  The Rust has four
//! one-field structures instead, because task #97 P4a's brief fixes them —
//! **not** because the phantom shape would not extract: a probe crate with
//! `struct Idx<K> { word: u32, kind: PhantomData<K> }` translates with no
//! error and no hole (Aeneas models `core::marker::PhantomData T` as `Unit`),
//! measured at P4a.  What the four newtypes buy is that no type parameter
//! threads through `Tbl`, the four `*Tables` and every signature below them;
//! what they cost is these wrappers and twelve dictionary impls.
//!
//! The *word* arithmetic is still written once, as the five `word_*`
//! functions below; each newtype's six operations are one-line wrappers over
//! them, so the `k`-generic Lean lemmas
//! (`Idx.tag_mk`/`tier_mk`/`index_mk`/`eta`) transfer to the Rust as lemmas
//! about `word_*` that each newtype's wrapper then inherits.
//!
//! The twin's `Idx.mk` is spelled `pack` here, and `Idx.ofWord` is `of_word`:
//! Aeneas names a structure's own constructor `EIdx.mk`, so an associated
//! function of that name collides with it in the generated Lean.  The Lean
//! twin avoids the same collision from the other side, by naming `Idx`'s
//! constructor `ofWord`.
//!
//! No handle type is `Copy`: DESIGN.md §3.4 forbids `#[derive]`, and a
//! hand-written `Clone`/`Copy` pair would drag `core::clone::Clone` into the
//! model for a `u32` field.  Copying a handle is `dup2()`, the crate's
//! standard spelling of the value copy Lean's semantics hides.

use crate::ron::hashmap::Dup;
use crate::ron::hashmap::Eq2;
use crate::ron::hashmap::Hashable;

// ---------------------------------------------------------------------------
// The layout constants (`Handle.lean:91-103`)
// ---------------------------------------------------------------------------

/// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Handle.lean:102-103 Idx.tierP
/// The persistent tier's bit value (DESIGN.md §8.3).
pub const TIER_P: u32 = 0;

/// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Handle.lean:104-105 Idx.tierS
/// The scratch tier's bit value (DESIGN.md §8.3).
pub const TIER_S: u32 = 1;

/// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Handle.lean:107-110 Idx.idxCap
/// `2^27`: the per-constructor, per-tier node capacity.  `intern` raises
/// `CheckError::Native` at it (DESIGN.md §8.3: "the Rust raises `Native` at
/// the limit, the Lean `throw`s the same kind"); the Lean's `capOK` is the
/// `Prop` that says the check passed.
pub const IDX_CAP: u32 = 134217728;

/// con-leche: none — arena infrastructure; the tag field's weight, `2^28`, spelled out of `Handle.lean:104-105 Idx.mk`
/// The Lean writes the two literals inline; Rust names them so that the
/// three field readers cannot drift apart.
pub const TAG_SPAN: u32 = 268435456;

// ---------------------------------------------------------------------------
// The word arithmetic (`Handle.lean:104-127`), written once for all four kinds
// ---------------------------------------------------------------------------

/// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Handle.lean:112-117 Idx.mk
/// Assemble a handle word from its three fields.  `+`, not `|`: the fields
/// are disjoint, so addition *is* the bitwise join, and the arithmetic form
/// is what makes the roundtrip lemmas `omega`-provable.
///
/// Deviation from the Lean: `UInt32` multiplication wraps, Rust's is checked
/// (`overflow-checks = true`, DESIGN.md §3.4), so the model is a `fail` on
/// `tag >= 16`.  Every caller passes one of the nineteen tag constants
/// below, and `tag * TAG_SPAN + tier * IDX_CAP + idx` is at most
/// `u32::MAX` for `tag < 16`, `tier < 2`, `idx < IDX_CAP` — the same three
/// hypotheses the Lean lemmas carry.
pub fn word_mk(tag: u32, tier: u32, idx: u32) -> u32 {
    tag * TAG_SPAN + tier * IDX_CAP + idx
}

/// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Handle.lean:119-120 Idx.tag
/// The constructor tag (bits 31…28).
pub fn word_tag(w: u32) -> u32 {
    w / TAG_SPAN
}

/// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Handle.lean:122-123 Idx.tier
/// The tier bit (bit 27).
pub fn word_tier(w: u32) -> u32 {
    w / IDX_CAP % 2
}

/// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Handle.lean:125-126 Idx.index
/// The index into the constructor's array (bits 26…0).
pub fn word_index(w: u32) -> u32 {
    w % IDX_CAP
}

/// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Handle.lean:128-130 Idx.isPersistent
/// Is this handle in the persistent tier?  A persistent handle survives
/// `drop_scratch`; a scratch one does not (DESIGN.md §8.3).
pub fn word_is_persistent(w: u32) -> bool {
    word_tier(w) == 0
}

/// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Handle.lean:132-133 Idx.idxNat
/// A handle's index, as the `usize` every array read wants.  The Lean's
/// `idxNat : Nat` is `i.index.toNat`; `IDX_CAP` bounds it, so the cast is
/// exact on every platform the crate builds for.
pub fn word_idx_nat(w: u32) -> usize {
    word_index(w) as usize
}

// ---------------------------------------------------------------------------
// The four handle kinds (`Handle.lean:59-75`)
// ---------------------------------------------------------------------------

/// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Handle.lean:65-66 EIdx
/// An expression handle (DESIGN.md §8.3).
pub struct EIdx {
    pub word: u32,
}

/// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Handle.lean:67-68 NIdx
/// A name handle (DESIGN.md §8.3).
pub struct NIdx {
    pub word: u32,
}

/// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Handle.lean:69-70 LIdx
/// A level handle (DESIGN.md §8.3).
pub struct LIdx {
    pub word: u32,
}

/// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Handle.lean:71-72 LsIdx
/// A level-list handle (DESIGN.md §8.3).
pub struct LsIdx {
    pub word: u32,
}

/// con-leche: ConLeche/Kernel/Expr.lean:94-105 BinderMeta
/// Lean twin: `proof/ConRon/Arena/Handle.lean:73-83 BMIdx` — `BMIdx`, a handle
/// into the **binder datum store**: the same word layout as the other four (tag
/// 0, the tier bit, the index), for a store with ONE constructor and so no tag
/// to spend.
///
/// DESIGN.md §8.3 gives `lam`/`forallE` a `BinderMeta` INSIDE the node
/// record, which makes the record twenty-four bytes with a `PropWhen` — and
/// a `PropWhen` is `Arc`-carrying at `one`/`two`/`many`, so every `dup2` of a
/// binder record is a reference count and every cons probe of the binder
/// tables compares one (task #97-P6-10 §3 priced the pair at 2–3 % of
/// `Init`).  With the datum interned the record is three `u32`s of POD, its
/// hash is `pack2`-shaped like the other nine, and its `eq2` is three word
/// comparisons.
pub struct BMIdx {
    pub word: u32,
}

// ---------------------------------------------------------------------------
// Per-kind operations: `Handle.lean`'s `Idx.*` at each of the four kinds
// ---------------------------------------------------------------------------

/// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Handle.lean:57-63 Idx
/// `Idx.mk`/`tag`/`tier`/`index`/`isPersistent`/`idxNat` at `k = .expr`.
impl EIdx {
    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Handle.lean:112-117 Idx.mk
    /// `pack`, not `mk`: Aeneas names a structure's own constructor
    /// `EIdx.mk`, and an associated `mk` would collide with it in the
    /// generated Lean (measured, P4a — "Name clash detected: … bound to the
    /// same name").  The Lean twin dodges the same collision from the other
    /// side, by naming `Idx`'s constructor `ofWord` so that `Idx.mk` is free.
    pub fn pack(tag: u32, tier: u32, idx: u32) -> EIdx {
        EIdx { word: word_mk(tag, tier, idx) }
    }

    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Handle.lean:61 Idx.ofWord
    pub fn of_word(w: u32) -> EIdx {
        EIdx { word: w }
    }

    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Handle.lean:119-120 Idx.tag
    pub fn tag(&self) -> u32 {
        word_tag(self.word)
    }

    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Handle.lean:122-123 Idx.tier
    pub fn tier(&self) -> u32 {
        word_tier(self.word)
    }

    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Handle.lean:125-126 Idx.index
    pub fn index(&self) -> u32 {
        word_index(self.word)
    }

    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Handle.lean:128-130 Idx.isPersistent
    pub fn is_persistent(&self) -> bool {
        word_is_persistent(self.word)
    }

    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Handle.lean:132-133 Idx.idxNat
    pub fn idx_nat(&self) -> usize {
        word_idx_nat(self.word)
    }
}

/// con-leche: ConLeche/Kernel/Expr.lean:94-105 BinderMeta
/// Lean twin: `proof/ConRon/Arena/Handle.lean:112-117 Idx.mk` —
/// `Idx.mk`/`tier`/`index`/`isPersistent`/`idxNat` at the binder-datum store.
/// The tag field is always `0`: the store has one constructor.
impl BMIdx {
    /// con-leche: ConLeche/Kernel/Expr.lean:94-105 BinderMeta
    /// Lean twin: `proof/ConRon/Arena/Handle.lean:112-117 Idx.mk` — `Idx.mk` at
    /// the binder-datum store.
    pub fn pack(tier: u32, idx: u32) -> BMIdx {
        BMIdx { word: word_mk(0, tier, idx) }
    }

    /// con-leche: ConLeche/Kernel/Expr.lean:94-105 BinderMeta
    /// Lean twin: `proof/ConRon/Arena/Handle.lean:61 Idx.ofWord` — `Idx.ofWord`
    /// at the binder-datum store.
    pub fn of_word(w: u32) -> BMIdx {
        BMIdx { word: w }
    }

    /// con-leche: ConLeche/Kernel/Expr.lean:94-105 BinderMeta
    /// Lean twin: `proof/ConRon/Arena/Handle.lean:128-130 Idx.isPersistent` —
    /// `Idx.isPersistent` at the binder-datum store.
    pub fn is_persistent(&self) -> bool {
        word_is_persistent(self.word)
    }

    /// con-leche: ConLeche/Kernel/Expr.lean:94-105 BinderMeta
    /// Lean twin: `proof/ConRon/Arena/Handle.lean:132-133 Idx.idxNat` —
    /// `Idx.idxNat` at the binder-datum store.
    pub fn idx_nat(&self) -> usize {
        word_idx_nat(self.word)
    }
}

/// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Handle.lean:57-63 Idx
/// `Idx.mk`/`tag`/`tier`/`index`/`isPersistent`/`idxNat` at `k = .name`.
impl NIdx {
    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Handle.lean:112-117 Idx.mk
    /// `pack`, not `mk`: Aeneas names a structure's own constructor
    /// `EIdx.mk`, and an associated `mk` would collide with it in the
    /// generated Lean (measured, P4a — "Name clash detected: … bound to the
    /// same name").  The Lean twin dodges the same collision from the other
    /// side, by naming `Idx`'s constructor `ofWord` so that `Idx.mk` is free.
    pub fn pack(tag: u32, tier: u32, idx: u32) -> NIdx {
        NIdx { word: word_mk(tag, tier, idx) }
    }

    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Handle.lean:61 Idx.ofWord
    pub fn of_word(w: u32) -> NIdx {
        NIdx { word: w }
    }

    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Handle.lean:119-120 Idx.tag
    pub fn tag(&self) -> u32 {
        word_tag(self.word)
    }

    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Handle.lean:122-123 Idx.tier
    pub fn tier(&self) -> u32 {
        word_tier(self.word)
    }

    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Handle.lean:125-126 Idx.index
    pub fn index(&self) -> u32 {
        word_index(self.word)
    }

    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Handle.lean:128-130 Idx.isPersistent
    pub fn is_persistent(&self) -> bool {
        word_is_persistent(self.word)
    }

    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Handle.lean:132-133 Idx.idxNat
    pub fn idx_nat(&self) -> usize {
        word_idx_nat(self.word)
    }
}

/// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Handle.lean:57-63 Idx
/// `Idx.mk`/`tag`/`tier`/`index`/`isPersistent`/`idxNat` at `k = .level`.
impl LIdx {
    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Handle.lean:112-117 Idx.mk
    /// `pack`, not `mk`: Aeneas names a structure's own constructor
    /// `EIdx.mk`, and an associated `mk` would collide with it in the
    /// generated Lean (measured, P4a — "Name clash detected: … bound to the
    /// same name").  The Lean twin dodges the same collision from the other
    /// side, by naming `Idx`'s constructor `ofWord` so that `Idx.mk` is free.
    pub fn pack(tag: u32, tier: u32, idx: u32) -> LIdx {
        LIdx { word: word_mk(tag, tier, idx) }
    }

    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Handle.lean:61 Idx.ofWord
    pub fn of_word(w: u32) -> LIdx {
        LIdx { word: w }
    }

    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Handle.lean:119-120 Idx.tag
    pub fn tag(&self) -> u32 {
        word_tag(self.word)
    }

    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Handle.lean:122-123 Idx.tier
    pub fn tier(&self) -> u32 {
        word_tier(self.word)
    }

    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Handle.lean:125-126 Idx.index
    pub fn index(&self) -> u32 {
        word_index(self.word)
    }

    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Handle.lean:128-130 Idx.isPersistent
    pub fn is_persistent(&self) -> bool {
        word_is_persistent(self.word)
    }

    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Handle.lean:132-133 Idx.idxNat
    pub fn idx_nat(&self) -> usize {
        word_idx_nat(self.word)
    }
}

/// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Handle.lean:57-63 Idx
/// `Idx.mk`/`tag`/`tier`/`index`/`isPersistent`/`idxNat` at `k = .levels`.
impl LsIdx {
    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Handle.lean:112-117 Idx.mk
    /// `pack`, not `mk`: Aeneas names a structure's own constructor
    /// `EIdx.mk`, and an associated `mk` would collide with it in the
    /// generated Lean (measured, P4a — "Name clash detected: … bound to the
    /// same name").  The Lean twin dodges the same collision from the other
    /// side, by naming `Idx`'s constructor `ofWord` so that `Idx.mk` is free.
    pub fn pack(tag: u32, tier: u32, idx: u32) -> LsIdx {
        LsIdx { word: word_mk(tag, tier, idx) }
    }

    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Handle.lean:61 Idx.ofWord
    pub fn of_word(w: u32) -> LsIdx {
        LsIdx { word: w }
    }

    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Handle.lean:119-120 Idx.tag
    pub fn tag(&self) -> u32 {
        word_tag(self.word)
    }

    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Handle.lean:122-123 Idx.tier
    pub fn tier(&self) -> u32 {
        word_tier(self.word)
    }

    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Handle.lean:125-126 Idx.index
    pub fn index(&self) -> u32 {
        word_index(self.word)
    }

    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Handle.lean:128-130 Idx.isPersistent
    pub fn is_persistent(&self) -> bool {
        word_is_persistent(self.word)
    }

    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Handle.lean:132-133 Idx.idxNat
    pub fn idx_nat(&self) -> usize {
        word_idx_nat(self.word)
    }
}

// ---------------------------------------------------------------------------
// The dictionaries a `ron::HashMap` keyed by a handle needs (`Handle.lean:78-88`)
// ---------------------------------------------------------------------------

/// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Handle.lean:98-100 instHashableIdx
/// **The word IS the hash**: nanoda's identity hasher (`unique_hasher.rs`),
/// no mixing at all.
impl Hashable for EIdx {
    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Handle.lean:98-100 instHashableIdx
    fn hash64(&self) -> u64 {
        self.word as u64
    }
}

/// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Handle.lean:98-100 instHashableIdx
impl Hashable for NIdx {
    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Handle.lean:98-100 instHashableIdx
    fn hash64(&self) -> u64 {
        self.word as u64
    }
}

/// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Handle.lean:98-100 instHashableIdx
impl Hashable for LIdx {
    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Handle.lean:98-100 instHashableIdx
    fn hash64(&self) -> u64 {
        self.word as u64
    }
}

/// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Handle.lean:98-100 instHashableIdx
impl Hashable for LsIdx {
    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Handle.lean:98-100 instHashableIdx
    fn hash64(&self) -> u64 {
        self.word as u64
    }
}

/// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Handle.lean:89-90 instBEqIdx
/// Structural equality of handles is equality of the word (and it is lawful,
/// `Handle.lean:82-84`, which is what makes a handle-keyed table a partial
/// function on words).
impl Eq2 for EIdx {
    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Handle.lean:89-90 instBEqIdx
    fn eq2(&self, other: &EIdx) -> bool {
        self.word == other.word
    }
}

/// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Handle.lean:89-90 instBEqIdx
impl Eq2 for NIdx {
    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Handle.lean:89-90 instBEqIdx
    fn eq2(&self, other: &NIdx) -> bool {
        self.word == other.word
    }
}

/// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Handle.lean:89-90 instBEqIdx
impl Eq2 for LIdx {
    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Handle.lean:89-90 instBEqIdx
    fn eq2(&self, other: &LIdx) -> bool {
        self.word == other.word
    }
}

/// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Handle.lean:89-90 instBEqIdx
impl Eq2 for LsIdx {
    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Handle.lean:89-90 instBEqIdx
    fn eq2(&self, other: &LsIdx) -> bool {
        self.word == other.word
    }
}

/// con-leche: none — the value copy that Lean's value semantics hides (DESIGN.md §3.2)
/// A handle is one word; copying it is reading it.  Spelled out rather than
/// derived, because DESIGN.md §3.4 keeps `core::clone::Clone` out of the
/// model.
impl Dup for EIdx {
    /// con-leche: none — the value copy that Lean's value semantics hides (DESIGN.md §3.2)
    fn dup2(&self) -> EIdx {
        EIdx { word: self.word }
    }
}

/// con-leche: none — the value copy that Lean's value semantics hides (DESIGN.md §3.2)
impl Dup for NIdx {
    /// con-leche: none — the value copy that Lean's value semantics hides (DESIGN.md §3.2)
    fn dup2(&self) -> NIdx {
        NIdx { word: self.word }
    }
}

/// con-leche: none — the value copy that Lean's value semantics hides (DESIGN.md §3.2)
impl Dup for LIdx {
    /// con-leche: none — the value copy that Lean's value semantics hides (DESIGN.md §3.2)
    fn dup2(&self) -> LIdx {
        LIdx { word: self.word }
    }
}

/// con-leche: none — the value copy that Lean's value semantics hides (DESIGN.md §3.2)
impl Dup for LsIdx {
    /// con-leche: none — the value copy that Lean's value semantics hides (DESIGN.md §3.2)
    fn dup2(&self) -> LsIdx {
        LsIdx { word: self.word }
    }
}

/// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Handle.lean:89-90 instBEqIdx
impl Eq2 for BMIdx {
    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Handle.lean:89-90 instBEqIdx
    fn eq2(&self, other: &BMIdx) -> bool {
        self.word == other.word
    }
}

/// con-leche: none — the value copy that Lean's value semantics hides (DESIGN.md §3.2)
impl Dup for BMIdx {
    /// con-leche: none — the value copy that Lean's value semantics hides (DESIGN.md §3.2)
    fn dup2(&self) -> BMIdx {
        BMIdx { word: self.word }
    }
}

// ---------------------------------------------------------------------------
// The constructor tags (`Handle.lean:204-279`)
// ---------------------------------------------------------------------------
//
// One block per store, values fixed by con-leche's own constructor order so
// that a reader can line the two up by eye.  Each tag cites the parent
// inductive and names the constructor it stands for.

/// con-leche: ConLeche/Kernel/Expr.lean:344-354 Expr
/// Lean twin: `proof/ConRon/Arena/Handle.lean:219-221 ETag.bvar` — the `bvar`
/// constructor, line 344.
pub const ETAG_BVAR: u32 = 0;

/// con-leche: ConLeche/Kernel/Expr.lean:344-354 Expr
/// Lean twin: `proof/ConRon/Arena/Handle.lean:222-224 ETag.fvar` — the `fvar`
/// constructor, line 345.
pub const ETAG_FVAR: u32 = 1;

/// con-leche: ConLeche/Kernel/Expr.lean:344-354 Expr
/// Lean twin: `proof/ConRon/Arena/Handle.lean:225-227 ETag.sort` — the `sort`
/// constructor, line 346.
pub const ETAG_SORT: u32 = 2;

/// con-leche: ConLeche/Kernel/Expr.lean:344-354 Expr
/// Lean twin: `proof/ConRon/Arena/Handle.lean:228-230 ETag.const` — the `const`
/// constructor, line 347.
pub const ETAG_CONST: u32 = 3;

/// con-leche: ConLeche/Kernel/Expr.lean:344-354 Expr
/// Lean twin: `proof/ConRon/Arena/Handle.lean:231-233 ETag.app` — the `app`
/// constructor, line 348.
pub const ETAG_APP: u32 = 4;

/// con-leche: ConLeche/Kernel/Expr.lean:344-354 Expr
/// Lean twin: `proof/ConRon/Arena/Handle.lean:234-236 ETag.lam` — the `lam`
/// constructor, line 349.
pub const ETAG_LAM: u32 = 5;

/// con-leche: ConLeche/Kernel/Expr.lean:344-354 Expr
/// Lean twin: `proof/ConRon/Arena/Handle.lean:237-239 ETag.forallE` — the
/// `forallE` constructor, line 350.
pub const ETAG_FORALL_E: u32 = 6;

/// con-leche: ConLeche/Kernel/Expr.lean:344-354 Expr
/// Lean twin: `proof/ConRon/Arena/Handle.lean:240-242 ETag.letE` — the `letE`
/// constructor, line 351.
pub const ETAG_LET_E: u32 = 7;

/// con-leche: ConLeche/Kernel/Expr.lean:344-354 Expr
/// Lean twin: `proof/ConRon/Arena/Handle.lean:243-245 ETag.lit` — the `lit`
/// constructor, line 352.
pub const ETAG_LIT: u32 = 8;

/// con-leche: ConLeche/Kernel/Expr.lean:344-354 Expr
/// Lean twin: `proof/ConRon/Arena/Handle.lean:246-248 ETag.proj` — the `proj`
/// constructor, line 353.
pub const ETAG_PROJ: u32 = 9;

/// con-leche: ConLeche/Kernel/Expr.lean:344-354 Expr
/// Lean twin: `proof/ConRon/Arena/Handle.lean:250-257 ETag.isBind` —
/// `ETag.isBind`: `lam` or `forallE`, the two constructors that share the
/// `BindNode` record shape. A named predicate rather than the disjunction
/// written at the use site: a two-way `||` inside a `match` arm that still
/// holds loans is what task #97-P4a's extraction rule 2 is about, and the walks
/// that dispatch on this tag hold the handle.
pub fn e_tag_is_bind(t: u32) -> bool {
    t == ETAG_LAM || t == ETAG_FORALL_E
}

/// con-leche: ConLeche/Kernel/Name.lean:34-37 Name
/// Lean twin: `proof/ConRon/Arena/Handle.lean:262-264 NTag.anonymous` — the
/// `anonymous` constructor, line 35.
pub const NTAG_ANONYMOUS: u32 = 0;

/// con-leche: ConLeche/Kernel/Name.lean:34-37 Name
/// Lean twin: `proof/ConRon/Arena/Handle.lean:265-267 NTag.str` — the `str`
/// constructor, line 36.
pub const NTAG_STR: u32 = 1;

/// con-leche: ConLeche/Kernel/Name.lean:34-37 Name
/// Lean twin: `proof/ConRon/Arena/Handle.lean:268-270 NTag.num` — the `num`
/// constructor, line 37.
pub const NTAG_NUM: u32 = 2;

/// con-leche: ConLeche/Kernel/Expr.lean:41-46 Level
/// Lean twin: `proof/ConRon/Arena/Handle.lean:275-277 LTag.zero` — the `zero`
/// constructor, line 41.
pub const LTAG_ZERO: u32 = 0;

/// con-leche: ConLeche/Kernel/Expr.lean:41-46 Level
/// Lean twin: `proof/ConRon/Arena/Handle.lean:278-280 LTag.succ` — the `succ`
/// constructor, line 42.
pub const LTAG_SUCC: u32 = 1;

/// con-leche: ConLeche/Kernel/Expr.lean:41-46 Level
/// Lean twin: `proof/ConRon/Arena/Handle.lean:281-283 LTag.max` — the `max`
/// constructor, line 43.
pub const LTAG_MAX: u32 = 2;

/// con-leche: ConLeche/Kernel/Expr.lean:41-46 Level
/// Lean twin: `proof/ConRon/Arena/Handle.lean:284-286 LTag.imax` — the `imax`
/// constructor, line 44.
pub const LTAG_IMAX: u32 = 3;

/// con-leche: ConLeche/Kernel/Expr.lean:41-46 Level
/// Lean twin: `proof/ConRon/Arena/Handle.lean:287-289 LTag.param` — the `param`
/// constructor, line 45.
pub const LTAG_PARAM: u32 = 4;

/// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Handle.lean:294-297 LsTag.list
/// Level *lists* are interned as one object (nanoda's `LevelsPtr`), so the
/// store has a single constructor and a single tag.
pub const LSTAG_LIST: u32 = 0;
