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

use con_ron_core::ron::hashmap::Dup;
use con_ron_core::ron::hashmap::Eq2;
use con_ron_core::ron::hashmap::Hashable;

// ---------------------------------------------------------------------------
// The layout constants (`Handle.lean:91-103`)
// ---------------------------------------------------------------------------

/// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Handle.lean:91 Idx.tierP
/// The persistent tier's bit value (DESIGN.md §8.3).
pub const TIER_P: u32 = 0;

/// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Handle.lean:93 Idx.tierS
/// The scratch tier's bit value (DESIGN.md §8.3).
pub const TIER_S: u32 = 1;

/// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Handle.lean:98 Idx.idxCap
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

/// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Handle.lean:104-105 Idx.mk
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

/// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Handle.lean:108 Idx.tag
/// The constructor tag (bits 31…28).
pub fn word_tag(w: u32) -> u32 {
    w / TAG_SPAN
}

/// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Handle.lean:111 Idx.tier
/// The tier bit (bit 27).
pub fn word_tier(w: u32) -> u32 {
    w / IDX_CAP % 2
}

/// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Handle.lean:114 Idx.index
/// The index into the constructor's array (bits 26…0).
pub fn word_index(w: u32) -> u32 {
    w % IDX_CAP
}

/// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Handle.lean:118 Idx.isPersistent
/// Is this handle in the persistent tier?  A persistent handle survives
/// `drop_scratch`; a scratch one does not (DESIGN.md §8.3).
pub fn word_is_persistent(w: u32) -> bool {
    word_tier(w) == 0
}

/// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Handle.lean:121 Idx.idxNat
/// A handle's index, as the `usize` every array read wants.  The Lean's
/// `idxNat : Nat` is `i.index.toNat`; `IDX_CAP` bounds it, so the cast is
/// exact on every platform the crate builds for.
pub fn word_idx_nat(w: u32) -> usize {
    word_index(w) as usize
}

// ---------------------------------------------------------------------------
// The four handle kinds (`Handle.lean:59-75`)
// ---------------------------------------------------------------------------

/// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Handle.lean:65 EIdx
/// An expression handle (DESIGN.md §8.3).
pub struct EIdx {
    pub word: u32,
}

/// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Handle.lean:67 NIdx
/// A name handle (DESIGN.md §8.3).
pub struct NIdx {
    pub word: u32,
}

/// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Handle.lean:69 LIdx
/// A level handle (DESIGN.md §8.3).
pub struct LIdx {
    pub word: u32,
}

/// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Handle.lean:71 LsIdx
/// A level-list handle (DESIGN.md §8.3).
pub struct LsIdx {
    pub word: u32,
}

// ---------------------------------------------------------------------------
// Per-kind operations: `Handle.lean`'s `Idx.*` at each of the four kinds
// ---------------------------------------------------------------------------

/// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Handle.lean:104-127 Idx
/// `Idx.mk`/`tag`/`tier`/`index`/`isPersistent`/`idxNat` at `k = .expr`.
impl EIdx {
    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Handle.lean:104-105 Idx.mk
    /// `pack`, not `mk`: Aeneas names a structure's own constructor
    /// `EIdx.mk`, and an associated `mk` would collide with it in the
    /// generated Lean (measured, P4a — "Name clash detected: … bound to the
    /// same name").  The Lean twin dodges the same collision from the other
    /// side, by naming `Idx`'s constructor `ofWord` so that `Idx.mk` is free.
    pub fn pack(tag: u32, tier: u32, idx: u32) -> EIdx {
        EIdx { word: word_mk(tag, tier, idx) }
    }

    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Handle.lean:59-62 Idx.ofWord
    pub fn of_word(w: u32) -> EIdx {
        EIdx { word: w }
    }

    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Handle.lean:108 Idx.tag
    pub fn tag(&self) -> u32 {
        word_tag(self.word)
    }

    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Handle.lean:111 Idx.tier
    pub fn tier(&self) -> u32 {
        word_tier(self.word)
    }

    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Handle.lean:114 Idx.index
    pub fn index(&self) -> u32 {
        word_index(self.word)
    }

    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Handle.lean:118 Idx.isPersistent
    pub fn is_persistent(&self) -> bool {
        word_is_persistent(self.word)
    }

    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Handle.lean:121 Idx.idxNat
    pub fn idx_nat(&self) -> usize {
        word_idx_nat(self.word)
    }
}

/// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Handle.lean:104-127 Idx
/// `Idx.mk`/`tag`/`tier`/`index`/`isPersistent`/`idxNat` at `k = .name`.
impl NIdx {
    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Handle.lean:104-105 Idx.mk
    /// `pack`, not `mk`: Aeneas names a structure's own constructor
    /// `EIdx.mk`, and an associated `mk` would collide with it in the
    /// generated Lean (measured, P4a — "Name clash detected: … bound to the
    /// same name").  The Lean twin dodges the same collision from the other
    /// side, by naming `Idx`'s constructor `ofWord` so that `Idx.mk` is free.
    pub fn pack(tag: u32, tier: u32, idx: u32) -> NIdx {
        NIdx { word: word_mk(tag, tier, idx) }
    }

    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Handle.lean:59-62 Idx.ofWord
    pub fn of_word(w: u32) -> NIdx {
        NIdx { word: w }
    }

    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Handle.lean:108 Idx.tag
    pub fn tag(&self) -> u32 {
        word_tag(self.word)
    }

    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Handle.lean:111 Idx.tier
    pub fn tier(&self) -> u32 {
        word_tier(self.word)
    }

    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Handle.lean:114 Idx.index
    pub fn index(&self) -> u32 {
        word_index(self.word)
    }

    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Handle.lean:118 Idx.isPersistent
    pub fn is_persistent(&self) -> bool {
        word_is_persistent(self.word)
    }

    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Handle.lean:121 Idx.idxNat
    pub fn idx_nat(&self) -> usize {
        word_idx_nat(self.word)
    }
}

/// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Handle.lean:104-127 Idx
/// `Idx.mk`/`tag`/`tier`/`index`/`isPersistent`/`idxNat` at `k = .level`.
impl LIdx {
    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Handle.lean:104-105 Idx.mk
    /// `pack`, not `mk`: Aeneas names a structure's own constructor
    /// `EIdx.mk`, and an associated `mk` would collide with it in the
    /// generated Lean (measured, P4a — "Name clash detected: … bound to the
    /// same name").  The Lean twin dodges the same collision from the other
    /// side, by naming `Idx`'s constructor `ofWord` so that `Idx.mk` is free.
    pub fn pack(tag: u32, tier: u32, idx: u32) -> LIdx {
        LIdx { word: word_mk(tag, tier, idx) }
    }

    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Handle.lean:59-62 Idx.ofWord
    pub fn of_word(w: u32) -> LIdx {
        LIdx { word: w }
    }

    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Handle.lean:108 Idx.tag
    pub fn tag(&self) -> u32 {
        word_tag(self.word)
    }

    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Handle.lean:111 Idx.tier
    pub fn tier(&self) -> u32 {
        word_tier(self.word)
    }

    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Handle.lean:114 Idx.index
    pub fn index(&self) -> u32 {
        word_index(self.word)
    }

    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Handle.lean:118 Idx.isPersistent
    pub fn is_persistent(&self) -> bool {
        word_is_persistent(self.word)
    }

    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Handle.lean:121 Idx.idxNat
    pub fn idx_nat(&self) -> usize {
        word_idx_nat(self.word)
    }
}

/// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Handle.lean:104-127 Idx
/// `Idx.mk`/`tag`/`tier`/`index`/`isPersistent`/`idxNat` at `k = .levels`.
impl LsIdx {
    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Handle.lean:104-105 Idx.mk
    /// `pack`, not `mk`: Aeneas names a structure's own constructor
    /// `EIdx.mk`, and an associated `mk` would collide with it in the
    /// generated Lean (measured, P4a — "Name clash detected: … bound to the
    /// same name").  The Lean twin dodges the same collision from the other
    /// side, by naming `Idx`'s constructor `ofWord` so that `Idx.mk` is free.
    pub fn pack(tag: u32, tier: u32, idx: u32) -> LsIdx {
        LsIdx { word: word_mk(tag, tier, idx) }
    }

    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Handle.lean:59-62 Idx.ofWord
    pub fn of_word(w: u32) -> LsIdx {
        LsIdx { word: w }
    }

    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Handle.lean:108 Idx.tag
    pub fn tag(&self) -> u32 {
        word_tag(self.word)
    }

    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Handle.lean:111 Idx.tier
    pub fn tier(&self) -> u32 {
        word_tier(self.word)
    }

    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Handle.lean:114 Idx.index
    pub fn index(&self) -> u32 {
        word_index(self.word)
    }

    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Handle.lean:118 Idx.isPersistent
    pub fn is_persistent(&self) -> bool {
        word_is_persistent(self.word)
    }

    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Handle.lean:121 Idx.idxNat
    pub fn idx_nat(&self) -> usize {
        word_idx_nat(self.word)
    }
}

// ---------------------------------------------------------------------------
// The dictionaries a `ron::HashMap` keyed by a handle needs (`Handle.lean:78-88`)
// ---------------------------------------------------------------------------

/// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Handle.lean:88 instHashableIdx
/// **The word IS the hash**: nanoda's identity hasher (`unique_hasher.rs`),
/// no mixing at all.
impl Hashable for EIdx {
    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Handle.lean:88 instHashableIdx
    fn hash64(&self) -> u64 {
        self.word as u64
    }
}

/// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Handle.lean:88 instHashableIdx
impl Hashable for NIdx {
    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Handle.lean:88 instHashableIdx
    fn hash64(&self) -> u64 {
        self.word as u64
    }
}

/// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Handle.lean:88 instHashableIdx
impl Hashable for LIdx {
    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Handle.lean:88 instHashableIdx
    fn hash64(&self) -> u64 {
        self.word as u64
    }
}

/// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Handle.lean:88 instHashableIdx
impl Hashable for LsIdx {
    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Handle.lean:88 instHashableIdx
    fn hash64(&self) -> u64 {
        self.word as u64
    }
}

/// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Handle.lean:78 instBEqIdx
/// Structural equality of handles is equality of the word (and it is lawful,
/// `Handle.lean:82-84`, which is what makes a handle-keyed table a partial
/// function on words).
impl Eq2 for EIdx {
    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Handle.lean:78 instBEqIdx
    fn eq2(&self, other: &EIdx) -> bool {
        self.word == other.word
    }
}

/// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Handle.lean:78 instBEqIdx
impl Eq2 for NIdx {
    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Handle.lean:78 instBEqIdx
    fn eq2(&self, other: &NIdx) -> bool {
        self.word == other.word
    }
}

/// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Handle.lean:78 instBEqIdx
impl Eq2 for LIdx {
    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Handle.lean:78 instBEqIdx
    fn eq2(&self, other: &LIdx) -> bool {
        self.word == other.word
    }
}

/// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Handle.lean:78 instBEqIdx
impl Eq2 for LsIdx {
    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Handle.lean:78 instBEqIdx
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
// The constructor tags (`Handle.lean:204-279`)
// ---------------------------------------------------------------------------
//
// One block per store, values fixed by con-leche's own constructor order so
// that a reader can line the two up by eye.  Each tag cites the parent
// inductive and names the constructor it stands for.

/// con-leche: ConLeche/Kernel/Expr.lean:343-353 Expr
/// Lean twin: `proof/ConRon/Arena/Handle.lean:209 ETag.bvar` — the `bvar`
/// constructor, line 344.
pub const ETAG_BVAR: u32 = 0;

/// con-leche: ConLeche/Kernel/Expr.lean:343-353 Expr
/// Lean twin: `proof/ConRon/Arena/Handle.lean:212 ETag.fvar` — the `fvar`
/// constructor, line 345.
pub const ETAG_FVAR: u32 = 1;

/// con-leche: ConLeche/Kernel/Expr.lean:343-353 Expr
/// Lean twin: `proof/ConRon/Arena/Handle.lean:215 ETag.sort` — the `sort`
/// constructor, line 346.
pub const ETAG_SORT: u32 = 2;

/// con-leche: ConLeche/Kernel/Expr.lean:343-353 Expr
/// Lean twin: `proof/ConRon/Arena/Handle.lean:218 ETag.const` — the `const`
/// constructor, line 347.
pub const ETAG_CONST: u32 = 3;

/// con-leche: ConLeche/Kernel/Expr.lean:343-353 Expr
/// Lean twin: `proof/ConRon/Arena/Handle.lean:221 ETag.app` — the `app`
/// constructor, line 348.
pub const ETAG_APP: u32 = 4;

/// con-leche: ConLeche/Kernel/Expr.lean:343-353 Expr
/// Lean twin: `proof/ConRon/Arena/Handle.lean:224 ETag.lam` — the `lam`
/// constructor, line 349.
pub const ETAG_LAM: u32 = 5;

/// con-leche: ConLeche/Kernel/Expr.lean:343-353 Expr
/// Lean twin: `proof/ConRon/Arena/Handle.lean:227 ETag.forallE` — the
/// `forallE` constructor, line 350.
pub const ETAG_FORALL_E: u32 = 6;

/// con-leche: ConLeche/Kernel/Expr.lean:343-353 Expr
/// Lean twin: `proof/ConRon/Arena/Handle.lean:230 ETag.letE` — the `letE`
/// constructor, line 351.
pub const ETAG_LET_E: u32 = 7;

/// con-leche: ConLeche/Kernel/Expr.lean:343-353 Expr
/// Lean twin: `proof/ConRon/Arena/Handle.lean:233 ETag.lit` — the `lit`
/// constructor, line 352.
pub const ETAG_LIT: u32 = 8;

/// con-leche: ConLeche/Kernel/Expr.lean:343-353 Expr
/// Lean twin: `proof/ConRon/Arena/Handle.lean:236 ETag.proj` — the `proj`
/// constructor, line 353.
pub const ETAG_PROJ: u32 = 9;

/// con-leche: ConLeche/Kernel/Name.lean:34-37 Name
/// Lean twin: `proof/ConRon/Arena/Handle.lean:243 NTag.anonymous` — the
/// `anonymous` constructor, line 35.
pub const NTAG_ANONYMOUS: u32 = 0;

/// con-leche: ConLeche/Kernel/Name.lean:34-37 Name
/// Lean twin: `proof/ConRon/Arena/Handle.lean:246 NTag.str` — the `str`
/// constructor, line 36.
pub const NTAG_STR: u32 = 1;

/// con-leche: ConLeche/Kernel/Name.lean:34-37 Name
/// Lean twin: `proof/ConRon/Arena/Handle.lean:249 NTag.num` — the `num`
/// constructor, line 37.
pub const NTAG_NUM: u32 = 2;

/// con-leche: ConLeche/Kernel/Expr.lean:40-45 Level
/// Lean twin: `proof/ConRon/Arena/Handle.lean:256 LTag.zero` — the `zero`
/// constructor, line 41.
pub const LTAG_ZERO: u32 = 0;

/// con-leche: ConLeche/Kernel/Expr.lean:40-45 Level
/// Lean twin: `proof/ConRon/Arena/Handle.lean:259 LTag.succ` — the `succ`
/// constructor, line 42.
pub const LTAG_SUCC: u32 = 1;

/// con-leche: ConLeche/Kernel/Expr.lean:40-45 Level
/// Lean twin: `proof/ConRon/Arena/Handle.lean:262 LTag.max` — the `max`
/// constructor, line 43.
pub const LTAG_MAX: u32 = 2;

/// con-leche: ConLeche/Kernel/Expr.lean:40-45 Level
/// Lean twin: `proof/ConRon/Arena/Handle.lean:265 LTag.imax` — the `imax`
/// constructor, line 44.
pub const LTAG_IMAX: u32 = 3;

/// con-leche: ConLeche/Kernel/Expr.lean:40-45 Level
/// Lean twin: `proof/ConRon/Arena/Handle.lean:268 LTag.param` — the `param`
/// constructor, line 45.
pub const LTAG_PARAM: u32 = 4;

/// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Handle.lean:276 LsTag.list
/// Level *lists* are interned as one object (nanoda's `LevelsPtr`), so the
/// store has a single constructor and a single tag.
pub const LSTAG_LIST: u32 = 0;
