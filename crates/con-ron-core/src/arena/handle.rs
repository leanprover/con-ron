//! The arena's handles (DESIGN.md §8.3, task #97 P4a), transliterated from
//! `proof/ConRon/Arena/Handle.lean` line for line.
//!
//! One 32-bit word per handle, in one of two shapes.  The top bit is the tier
//! in both; bit 30 says which shape the rest is:
//!
//! ```text
//! wide   (expression `app` only)        narrow (every other node)
//! bit  31      tier                     bit  31      tier
//! bit  30      1                        bit  30      0
//! bits 29…0    index                    bits 29…26   ctor tag   (4 bits)
//!                                       bits 25…0    index
//! ```
//!
//! (tier 0 = persistent, 1 = scratch; the index is into THAT CONSTRUCTOR'S
//! array of THAT TIER).  The zero word is a narrow handle — tag 0,
//! persistent, slot 0 — which is the twin's `default : Idx k` and every
//! `of_word(0)` below: the anonymous name, the level `zero`, a handle that
//! decodes.  An expression `app` array holds 2^30 = 1 073 741 824 nodes per
//! tier and every other constructor array 2^26 =
//! 67 108 864: apps are 85 % of an export's expression nodes, so they are the
//! array that runs out first, and they get the room.  Only the expression
//! `app` tag is wide — a level `param` handle is narrow although `LTAG_PARAM`
//! has `ETAG_APP`'s value — and `word_tag` reads `ETAG_APP` off a word with
//! bit 30 set, so the tag of a handle is read the same way for all four
//! kinds.
//!
//! The tier is the TOP bit, above both shapes' index, so a persistent
//! handle's bits never change when the scratch tier comes and goes
//! (con-leche's lesson 6).
//!
//! ## Arithmetic, not bit operations
//!
//! The Lean packs with `*`, `/` and `%` by powers of two rather than
//! `<<<`/`&&&`/`|||`, because the roundtrip lemmas are then `grind`'s linear
//! arithmetic over `UInt32` (division and remainder by a literal), while the
//! bitwise ones would need `bv_decide`, which **adds an axiom** to the trust
//! surface (DESIGN.md §8's task #97a, "Deviations from §8.3 / §8.4").  This
//! module mirrors that spelling exactly, so that the extracted model is the
//! twin's term for term: `word_mk` and `word_mk_wide` are a multiply-and-add,
//! `word_tier` a divide, `word_index` a remainder.  LLVM emits the same
//! shift-and-mask either way.
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
//! The *word* arithmetic is still written once, as the `word_*` functions
//! below; each newtype's operations are one-line wrappers over them, so the
//! `k`-generic Lean lemmas (`Idx.tag_mk`/`tier_mk`/`index_mk`/`eta` and the
//! `mkWide` ones) transfer to the Rust as lemmas about `word_*` that each
//! newtype's wrapper then inherits.
//!
//! The twin's `Idx.mk` is spelled `pack` here (and `Idx.mkWide` is
//! `pack_wide`), and `Idx.ofWord` is `of_word`: Aeneas names a structure's
//! own constructor `EIdx.mk`, so an associated function of that name collides
//! with it in the generated Lean.  The Lean twin avoids the same collision
//! from the other side, by naming `Idx`'s constructor `ofWord`.
//!
//! No handle type is `Copy`: DESIGN.md §3.4 forbids `#[derive]`, and a
//! hand-written `Clone`/`Copy` pair would drag `core::clone::Clone` into the
//! model for a `u32` field.  Copying a handle is `dup2()`, the crate's
//! standard spelling of the value copy Lean's semantics hides.

use crate::ron::hashmap::Dup;
use crate::ron::hashmap::Eq2;
use crate::ron::hashmap::Hashable;

// ---------------------------------------------------------------------------
// The layout constants (`Handle.lean:112-125`)
// ---------------------------------------------------------------------------

/// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Handle.lean:116-117 Idx.tierP
/// The persistent tier's bit value (DESIGN.md §8.3).
pub const TIER_P: u32 = 0;

/// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Handle.lean:118-119 Idx.tierS
/// The scratch tier's bit value (DESIGN.md §8.3).
pub const TIER_S: u32 = 1;

/// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Handle.lean:121-125 Idx.idxCap
/// `2^26`: the per-constructor, per-tier node capacity of every constructor
/// but the expression `app` (a narrow handle's index field), and the weight
/// of a narrow handle's tag field.  `intern` raises `CheckError::Native` at
/// it (DESIGN.md §8.3: "the Rust raises `Native` at the limit, the Lean
/// `throw`s the same kind"); the Lean's `capOK` is the `Prop` that says the
/// check passed.
pub const IDX_CAP: u32 = 67108864;

/// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Handle.lean:127-129 Idx.wideCap
/// `2^30`: the expression `app` array's per-tier capacity (a wide handle's
/// index field), and the weight of bit 30, the bit that is set in a wide
/// handle.
pub const WIDE_CAP: u32 = 1073741824;

/// con-leche: none — arena infrastructure; the tier bit's weight, `2^31`, spelled out of `Handle.lean:124-130 Idx.mk`
/// The Lean writes the literals inline; Rust names them so that the field
/// readers cannot drift apart.
pub const TIER_SPAN: u32 = 2147483648;

// ---------------------------------------------------------------------------
// The word arithmetic (`Handle.lean:127-162`), written once for all four kinds
// ---------------------------------------------------------------------------

/// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Handle.lean:131-137 Idx.mk
/// Assemble a NARROW handle word from its three fields: the tier on top, bit
/// 30 clear, the tag in bits 29…26, the index below.  `+`, not `|`: the fields
/// are disjoint, so addition *is* the bitwise join, and the arithmetic form
/// is what makes the roundtrip lemmas `grind`-provable.
///
/// Deviation from the Lean: `UInt32` multiplication wraps, Rust's is checked
/// (`overflow-checks = true`, DESIGN.md §3.4), so the model is a `fail`
/// where the Lean would wrap.  Every caller passes one of the tag constants
/// below and a tier constant, and the sum is at most `u32::MAX` for
/// `tag < 16`, `tier < 2`, `idx < IDX_CAP` — the same three hypotheses the
/// Lean lemmas carry.
pub fn word_mk(tag: u32, tier: u32, idx: u32) -> u32 {
    tier * TIER_SPAN + tag * IDX_CAP + idx
}

/// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Handle.lean:139-142 Idx.mkWide
/// Assemble a WIDE handle word — an expression `app` — from its two fields:
/// the tier on top, bit 30 set, the index in bits 29…0.  The Lean lemmas'
/// hypotheses are `tier < 2`, `idx < WIDE_CAP`.
pub fn word_mk_wide(tier: u32, idx: u32) -> u32 {
    tier * TIER_SPAN + WIDE_CAP + idx
}

/// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Handle.lean:144-146 Idx.isWide
/// Is this a wide word (bit 30 set), i.e. an expression `app` handle?
pub fn word_is_wide(w: u32) -> bool {
    w / WIDE_CAP % 2 == 1
}

/// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Handle.lean:148-151 Idx.tag
/// The constructor tag: `ETAG_APP` for a wide word, bits 29…26 of a narrow
/// one.
pub fn word_tag(w: u32) -> u32 {
    if word_is_wide(w) {
        ETAG_APP
    } else {
        w / IDX_CAP % 16
    }
}

/// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Handle.lean:153-154 Idx.tier
/// The tier bit (bit 31).
pub fn word_tier(w: u32) -> u32 {
    w / TIER_SPAN
}

/// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Handle.lean:156-159 Idx.index
/// The index into the constructor's array: bits 29…0 of a wide word, bits
/// 25…0 of a narrow one.
pub fn word_index(w: u32) -> u32 {
    if word_is_wide(w) {
        w % WIDE_CAP
    } else {
        w % IDX_CAP
    }
}

/// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Handle.lean:161-163 Idx.isPersistent
/// Is this handle in the persistent tier?  A persistent handle survives
/// `drop_scratch`; a scratch one does not (DESIGN.md §8.3).
pub fn word_is_persistent(w: u32) -> bool {
    word_tier(w) == 0
}

/// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Handle.lean:165-166 Idx.idxNat
/// A handle's index, as the `usize` every array read wants.  The Lean's
/// `idxNat : Nat` is `i.index.toNat`; `WIDE_CAP` bounds it, so the cast is
/// exact on every platform the crate builds for.
pub fn word_idx_nat(w: u32) -> usize {
    word_index(w) as usize
}

// ---------------------------------------------------------------------------
// The four handle kinds (`Handle.lean:78-93`)
// ---------------------------------------------------------------------------

/// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Handle.lean:90-91 EIdx
/// An expression handle (DESIGN.md §8.3).
pub struct EIdx {
    pub word: u32,
}

/// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Handle.lean:92-93 NIdx
/// A name handle (DESIGN.md §8.3).
pub struct NIdx {
    pub word: u32,
}

/// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Handle.lean:94-95 LIdx
/// A level handle (DESIGN.md §8.3).
pub struct LIdx {
    pub word: u32,
}

/// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Handle.lean:96-97 LsIdx
/// A level-list handle (DESIGN.md §8.3).
pub struct LsIdx {
    pub word: u32,
}


// ---------------------------------------------------------------------------
// Per-kind operations: `Handle.lean`'s `Idx.*` at each of the four kinds
// ---------------------------------------------------------------------------

/// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Handle.lean:82-88 Idx
/// `Idx.mk`/`tag`/`tier`/`index`/`isPersistent`/`idxNat` at `k = .expr`.
impl EIdx {
    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Handle.lean:131-137 Idx.mk
    /// `pack`, not `mk`: Aeneas names a structure's own constructor
    /// `EIdx.mk`, and an associated `mk` would collide with it in the
    /// generated Lean (measured, P4a — "Name clash detected: … bound to the
    /// same name").  The Lean twin dodges the same collision from the other
    /// side, by naming `Idx`'s constructor `ofWord` so that `Idx.mk` is free.
    pub fn pack(tag: u32, tier: u32, idx: u32) -> EIdx {
        EIdx { word: word_mk(tag, tier, idx) }
    }

    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Handle.lean:139-142 Idx.mkWide
    /// The handle of an expression `app` node, the one wide shape (DESIGN.md
    /// §8.3).
    pub fn pack_wide(tier: u32, idx: u32) -> EIdx {
        EIdx { word: word_mk_wide(tier, idx) }
    }

    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Handle.lean:86 Idx.ofWord
    pub fn of_word(w: u32) -> EIdx {
        EIdx { word: w }
    }

    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Handle.lean:148-151 Idx.tag
    pub fn tag(&self) -> u32 {
        word_tag(self.word)
    }

    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Handle.lean:153-154 Idx.tier
    pub fn tier(&self) -> u32 {
        word_tier(self.word)
    }

    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Handle.lean:144-146 Idx.isWide
    pub fn is_wide(&self) -> bool {
        word_is_wide(self.word)
    }

    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Handle.lean:161-163 Idx.isPersistent
    pub fn is_persistent(&self) -> bool {
        word_is_persistent(self.word)
    }

    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Handle.lean:165-166 Idx.idxNat
    pub fn idx_nat(&self) -> usize {
        word_idx_nat(self.word)
    }
}


/// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Handle.lean:82-88 Idx
/// `Idx.mk`/`tag`/`tier`/`index`/`isPersistent`/`idxNat` at `k = .name`.
impl NIdx {
    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Handle.lean:131-137 Idx.mk
    /// `pack`, not `mk`: Aeneas names a structure's own constructor
    /// `EIdx.mk`, and an associated `mk` would collide with it in the
    /// generated Lean (measured, P4a — "Name clash detected: … bound to the
    /// same name").  The Lean twin dodges the same collision from the other
    /// side, by naming `Idx`'s constructor `ofWord` so that `Idx.mk` is free.
    pub fn pack(tag: u32, tier: u32, idx: u32) -> NIdx {
        NIdx { word: word_mk(tag, tier, idx) }
    }

    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Handle.lean:86 Idx.ofWord
    pub fn of_word(w: u32) -> NIdx {
        NIdx { word: w }
    }

    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Handle.lean:148-151 Idx.tag
    pub fn tag(&self) -> u32 {
        word_tag(self.word)
    }

    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Handle.lean:153-154 Idx.tier
    pub fn tier(&self) -> u32 {
        word_tier(self.word)
    }

    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Handle.lean:161-163 Idx.isPersistent
    pub fn is_persistent(&self) -> bool {
        word_is_persistent(self.word)
    }

    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Handle.lean:165-166 Idx.idxNat
    pub fn idx_nat(&self) -> usize {
        word_idx_nat(self.word)
    }
}

/// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Handle.lean:82-88 Idx
/// `Idx.mk`/`tag`/`tier`/`index`/`isPersistent`/`idxNat` at `k = .level`.
impl LIdx {
    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Handle.lean:131-137 Idx.mk
    /// `pack`, not `mk`: Aeneas names a structure's own constructor
    /// `EIdx.mk`, and an associated `mk` would collide with it in the
    /// generated Lean (measured, P4a — "Name clash detected: … bound to the
    /// same name").  The Lean twin dodges the same collision from the other
    /// side, by naming `Idx`'s constructor `ofWord` so that `Idx.mk` is free.
    pub fn pack(tag: u32, tier: u32, idx: u32) -> LIdx {
        LIdx { word: word_mk(tag, tier, idx) }
    }

    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Handle.lean:86 Idx.ofWord
    pub fn of_word(w: u32) -> LIdx {
        LIdx { word: w }
    }

    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Handle.lean:148-151 Idx.tag
    pub fn tag(&self) -> u32 {
        word_tag(self.word)
    }

    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Handle.lean:153-154 Idx.tier
    pub fn tier(&self) -> u32 {
        word_tier(self.word)
    }

    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Handle.lean:144-146 Idx.isWide
    pub fn is_wide(&self) -> bool {
        word_is_wide(self.word)
    }

    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Handle.lean:161-163 Idx.isPersistent
    pub fn is_persistent(&self) -> bool {
        word_is_persistent(self.word)
    }

    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Handle.lean:165-166 Idx.idxNat
    pub fn idx_nat(&self) -> usize {
        word_idx_nat(self.word)
    }
}

/// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Handle.lean:82-88 Idx
/// `Idx.mk`/`tag`/`tier`/`index`/`isPersistent`/`idxNat` at `k = .levels`.
impl LsIdx {
    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Handle.lean:131-137 Idx.mk
    /// `pack`, not `mk`: Aeneas names a structure's own constructor
    /// `EIdx.mk`, and an associated `mk` would collide with it in the
    /// generated Lean (measured, P4a — "Name clash detected: … bound to the
    /// same name").  The Lean twin dodges the same collision from the other
    /// side, by naming `Idx`'s constructor `ofWord` so that `Idx.mk` is free.
    pub fn pack(tag: u32, tier: u32, idx: u32) -> LsIdx {
        LsIdx { word: word_mk(tag, tier, idx) }
    }

    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Handle.lean:86 Idx.ofWord
    pub fn of_word(w: u32) -> LsIdx {
        LsIdx { word: w }
    }

    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Handle.lean:148-151 Idx.tag
    pub fn tag(&self) -> u32 {
        word_tag(self.word)
    }

    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Handle.lean:153-154 Idx.tier
    pub fn tier(&self) -> u32 {
        word_tier(self.word)
    }

    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Handle.lean:161-163 Idx.isPersistent
    pub fn is_persistent(&self) -> bool {
        word_is_persistent(self.word)
    }

    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Handle.lean:165-166 Idx.idxNat
    pub fn idx_nat(&self) -> usize {
        word_idx_nat(self.word)
    }
}

// ---------------------------------------------------------------------------
// The dictionaries a `ron::HashMap` keyed by a handle needs (`Handle.lean:99-110`)
// ---------------------------------------------------------------------------

/// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Handle.lean:112-114 instHashableIdx
/// **The word IS the hash**: nanoda's identity hasher (`unique_hasher.rs`),
/// no mixing at all.
impl Hashable for EIdx {
    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Handle.lean:112-114 instHashableIdx
    fn hash64(&self) -> u64 {
        self.word as u64
    }
}

/// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Handle.lean:112-114 instHashableIdx
impl Hashable for NIdx {
    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Handle.lean:112-114 instHashableIdx
    fn hash64(&self) -> u64 {
        self.word as u64
    }
}

/// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Handle.lean:112-114 instHashableIdx
impl Hashable for LIdx {
    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Handle.lean:112-114 instHashableIdx
    fn hash64(&self) -> u64 {
        self.word as u64
    }
}

/// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Handle.lean:112-114 instHashableIdx
impl Hashable for LsIdx {
    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Handle.lean:112-114 instHashableIdx
    fn hash64(&self) -> u64 {
        self.word as u64
    }
}

/// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Handle.lean:103-104 instBEqIdx
/// Structural equality of handles is equality of the word (and it is lawful,
/// `Handle.lean:82-84`, which is what makes a handle-keyed table a partial
/// function on words).
impl Eq2 for EIdx {
    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Handle.lean:103-104 instBEqIdx
    fn eq2(&self, other: &EIdx) -> bool {
        self.word == other.word
    }
}

/// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Handle.lean:103-104 instBEqIdx
impl Eq2 for NIdx {
    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Handle.lean:103-104 instBEqIdx
    fn eq2(&self, other: &NIdx) -> bool {
        self.word == other.word
    }
}

/// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Handle.lean:103-104 instBEqIdx
impl Eq2 for LIdx {
    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Handle.lean:103-104 instBEqIdx
    fn eq2(&self, other: &LIdx) -> bool {
        self.word == other.word
    }
}

/// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Handle.lean:103-104 instBEqIdx
impl Eq2 for LsIdx {
    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Handle.lean:103-104 instBEqIdx
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



// ---------------------------------------------------------------------------
// The constructor tags (`Handle.lean:253-340`)
// ---------------------------------------------------------------------------
//
// One block per store, values fixed by con-leche's own constructor order so
// that a reader can line the two up by eye.  Each tag cites the parent
// inductive and names the constructor it stands for.

/// con-leche: ConLeche/Kernel/Expr.lean:341-460 Expr
/// Lean twin: `proof/ConRon/Arena/Handle.lean:264-266 ETag.bvar` — the `bvar`
/// constructor, line 401.
pub const ETAG_BVAR: u32 = 0;

/// con-leche: ConLeche/Kernel/Expr.lean:341-460 Expr
/// Lean twin: `proof/ConRon/Arena/Handle.lean:267-269 ETag.fvar` — the `fvar`
/// constructor, line 402.
pub const ETAG_FVAR: u32 = 1;

/// con-leche: ConLeche/Kernel/Expr.lean:341-460 Expr
/// Lean twin: `proof/ConRon/Arena/Handle.lean:270-272 ETag.sort` — the `sort`
/// constructor, line 403.
pub const ETAG_SORT: u32 = 2;

/// con-leche: ConLeche/Kernel/Expr.lean:341-460 Expr
/// Lean twin: `proof/ConRon/Arena/Handle.lean:273-275 ETag.const` — the `const`
/// constructor, line 404.
pub const ETAG_CONST: u32 = 3;

/// con-leche: ConLeche/Kernel/Expr.lean:341-460 Expr
/// Lean twin: `proof/ConRon/Arena/Handle.lean:276-278 ETag.app` — the `app`
/// constructor, line 405.
pub const ETAG_APP: u32 = 4;

/// con-leche: ConLeche/Kernel/Expr.lean:341-460 Expr
/// Lean twin: `proof/ConRon/Arena/Handle.lean:279-281 ETag.lam` — the `lam`
/// constructor, line 406.
pub const ETAG_LAM: u32 = 5;

/// con-leche: ConLeche/Kernel/Expr.lean:341-460 Expr
/// Lean twin: `proof/ConRon/Arena/Handle.lean:282-284 ETag.forallE` — the
/// `forallE` constructor, line 407.
pub const ETAG_FORALL_E: u32 = 6;

/// con-leche: ConLeche/Kernel/Expr.lean:341-460 Expr
/// Lean twin: `proof/ConRon/Arena/Handle.lean:285-287 ETag.letE` — the `letE`
/// constructor, line 408.
pub const ETAG_LET_E: u32 = 7;

/// con-leche: ConLeche/Kernel/Expr.lean:341-460 Expr
/// Lean twin: `proof/ConRon/Arena/Handle.lean:288-290 ETag.lit` — the `lit`
/// constructor, line 409.
pub const ETAG_LIT: u32 = 8;

/// con-leche: ConLeche/Kernel/Expr.lean:341-460 Expr
/// Lean twin: `proof/ConRon/Arena/Handle.lean:291-293 ETag.proj` — the `proj`
/// constructor, line 410.
pub const ETAG_PROJ: u32 = 9;

/// con-leche: ConLeche/Kernel/Expr.lean:341-460 Expr
/// Lean twin: `proof/ConRon/Arena/Handle.lean:295-302 ETag.isBind` —
/// `ETag.isBind`: `lam` or `forallE`, the two constructors that share the
/// `BindNode` record shape. A named predicate rather than the disjunction
/// written at the use site: a two-way `||` inside a `match` arm that still
/// holds loans is what task #97-P4a's extraction rule 2 is about, and the walks
/// that dispatch on this tag hold the handle.
pub fn e_tag_is_bind(t: u32) -> bool {
    t == ETAG_LAM || t == ETAG_FORALL_E
}

/// con-leche: ConLeche/Kernel/Name.lean:27-30 Name
/// Lean twin: `proof/ConRon/Arena/Handle.lean:307-309 NTag.anonymous` — the
/// `anonymous` constructor, line 28.
pub const NTAG_ANONYMOUS: u32 = 0;

/// con-leche: ConLeche/Kernel/Name.lean:27-30 Name
/// Lean twin: `proof/ConRon/Arena/Handle.lean:310-312 NTag.str` — the `str`
/// constructor, line 29.
pub const NTAG_STR: u32 = 1;

/// con-leche: ConLeche/Kernel/Name.lean:27-30 Name
/// Lean twin: `proof/ConRon/Arena/Handle.lean:313-315 NTag.num` — the `num`
/// constructor, line 30.
pub const NTAG_NUM: u32 = 2;

/// con-leche: ConLeche/Kernel/Expr.lean:38-43 Level
/// Lean twin: `proof/ConRon/Arena/Handle.lean:320-322 LTag.zero` — the `zero`
/// constructor, line 39.
pub const LTAG_ZERO: u32 = 0;

/// con-leche: ConLeche/Kernel/Expr.lean:38-43 Level
/// Lean twin: `proof/ConRon/Arena/Handle.lean:323-325 LTag.succ` — the `succ`
/// constructor, line 40.
pub const LTAG_SUCC: u32 = 1;

/// con-leche: ConLeche/Kernel/Expr.lean:38-43 Level
/// Lean twin: `proof/ConRon/Arena/Handle.lean:326-328 LTag.max` — the `max`
/// constructor, line 41.
pub const LTAG_MAX: u32 = 2;

/// con-leche: ConLeche/Kernel/Expr.lean:38-43 Level
/// Lean twin: `proof/ConRon/Arena/Handle.lean:329-331 LTag.imax` — the `imax`
/// constructor, line 42.
pub const LTAG_IMAX: u32 = 3;

/// con-leche: ConLeche/Kernel/Expr.lean:38-43 Level
/// Lean twin: `proof/ConRon/Arena/Handle.lean:332-334 LTag.param` — the `param`
/// constructor, line 43.
pub const LTAG_PARAM: u32 = 4;

/// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Handle.lean:339-342 LsTag.list
/// Level *lists* are interned as one object (nanoda's `LevelsPtr`), so the
/// store has a single constructor and a single tag.
pub const LSTAG_LIST: u32 = 0;

// ---------------------------------------------------------------------------
// Tests: the word arithmetic at the edges of both shapes (task #133)
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    /// Every narrow field round-trips at the corners of its range, at every
    /// tag value a store uses, in both tiers.
    #[test]
    fn narrow_roundtrip_at_the_edges() {
        let tags: [u32; 16] = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15];
        for &tag in tags.iter() {
            for &tier in [TIER_P, TIER_S].iter() {
                for &idx in [0, 1, IDX_CAP / 2, IDX_CAP - 2, IDX_CAP - 1].iter() {
                    let w = word_mk(tag, tier, idx);
                    assert!(!word_is_wide(w), "tag {tag} tier {tier} idx {idx}");
                    assert_eq!(word_tag(w), tag);
                    assert_eq!(word_tier(w), tier);
                    assert_eq!(word_index(w), idx);
                    assert_eq!(word_idx_nat(w), idx as usize);
                    assert_eq!(word_is_persistent(w), tier == TIER_P);
                }
            }
        }
        // the largest narrow word sits just below the scratch wide range
        assert_eq!(word_mk(15, TIER_S, IDX_CAP - 1), TIER_SPAN + WIDE_CAP - 1);
    }

    /// The wide shape: `app` handles up to `2^30 - 1`, past the `2^27` the
    /// layout before task #133 gave every constructor.
    #[test]
    fn wide_roundtrip_at_the_edges() {
        for &tier in [TIER_P, TIER_S].iter() {
            for &idx in [0, 1, IDX_CAP - 1, IDX_CAP, 134217727, 134217728, WIDE_CAP - 1].iter() {
                let h = EIdx::pack_wide(tier, idx);
                assert!(h.is_wide());
                assert_eq!(h.tag(), ETAG_APP);
                assert_eq!(h.tier(), tier);
                assert_eq!(h.idx_nat(), idx as usize);
                assert_eq!(h.is_persistent(), tier == TIER_P);
            }
        }
        assert_eq!(word_mk_wide(TIER_P, 0), WIDE_CAP);
        assert_eq!(word_mk_wide(TIER_S, WIDE_CAP - 1), u32::MAX);
        // the zero word is narrow: tag 0, persistent, slot 0
        assert!(!word_is_wide(0));
        assert_eq!(word_tag(0), 0);
        assert_eq!(word_index(0), 0);
        assert!(word_is_persistent(0));
    }

    /// The two shapes never share a word, and a level `param` handle (tag 4,
    /// `ETAG_APP`'s value) is narrow.
    #[test]
    fn shapes_are_disjoint() {
        for &tier in [TIER_P, TIER_S].iter() {
            for &idx in [0, 1, IDX_CAP - 1].iter() {
                let wide = word_mk_wide(tier, idx);
                let narrow = word_mk(ETAG_APP, tier, idx);
                assert_ne!(wide, narrow);
                assert_eq!(word_tag(wide), word_tag(narrow));
                assert_eq!(word_index(wide), word_index(narrow));
                let p = LIdx::pack(LTAG_PARAM, tier, idx);
                assert!(!p.is_wide());
                assert_eq!(p.tag(), LTAG_PARAM);
            }
        }
    }

    /// A persistent handle's bits are the scratch tier's bits minus the top
    /// one: the tier is the only field the tier changes.
    #[test]
    fn tier_is_the_top_bit() {
        for &idx in [0, 5, IDX_CAP - 1].iter() {
            assert_eq!(word_mk(ETAG_LAM, TIER_S, idx) - word_mk(ETAG_LAM, TIER_P, idx), TIER_SPAN);
        }
        assert_eq!(word_mk_wide(TIER_S, 7) - word_mk_wide(TIER_P, 7), TIER_SPAN);
    }
}
