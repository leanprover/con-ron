//! `ConLeche/Frontend/Scan/Types.lean` — the lean4export dialect's *syntax*:
//! one record per line shape, in **stream indices**, with nothing resolved
//! and no representation in sight.  `scan_fast` produces these; `export_c`
//! consumes them.
//!
//! **Four standing deviations**, all of them §3.3's machine-word split or
//! Rust spelling:
//!
//! 1. **Stream indices and counts are `u64`**, not `Nat`.  A number in the
//!    stream that does not fit is a *scan* failure (`ErrTag::IndexOverflow`,
//!    the one tag con-leche's `ErrTag` has no counterpart for), never a
//!    silent truncation — exactly the rule task #19 pinned for the dump
//!    reader.
//! 2. **A `natVal` literal keeps its decimal digits** (as `Vec<u8>`, the
//!    bytes of the literal) rather than becoming a `Nat` here: it is the one
//!    unbounded number of the dialect (§3.3), and `export_c` turns it into a
//!    `ron::Nat` when it builds the node.
//! 3. **`ScanRes α` is `Result<(α, usize), ScanErr>`.**  con-leche's
//!    one-constructor `ScanRes` exists to keep a scan allocation-free in
//!    Lean (its doc comment says so: "an `Except ScanErr (α × USize)` would
//!    be three heap objects per scan"); in Rust a `Result` of a tuple of a
//!    machine word is already flat.
//! 4. **`IdTable` is one `Vec` plus a `ron::HashMap`**, and its operations are
//!    free functions rather than methods, as in the rest of the core.  The
//!    three laws `Types.lean` proves beside the structure
//!    (`get?_empty`/`get?_singleton`/`get?_insert`) are the *specification* of
//!    those functions; they are theorems and are not ported (§3.1 — a `Prop`
//!    is not code), but `id_table_is_its_naive_map` in this module's tests
//!    exercises all three as executable checks.
//!
//! **Task #84's own deviation**: every Lean `String` of a record is a
//! `Vec<u32>` of code points, and the two the dialect carries as *spelling* —
//! a definition's `safety` and a quotient record's `kind`, both reported back
//! to the user verbatim — are `Vec<u32>` too.  Nothing here derives `Clone`,
//! `Copy`, `Debug` or `PartialEq`: the core's house style is an explicit
//! `foo_dup` and `foo_beq` per type (DESIGN.md §3.4).

use crate::kernel::core_types;
use crate::ron::hashmap::HashMap;

/// con-leche: ConLeche/Frontend/Scan/Types.lean:47-93 ErrTag
/// What went wrong, as a static tag: the recogniser reports a position and one
/// of these, and the driver renders the sentence.  No formatting runs while a
/// stream is being read.
///
/// Deviation: `IndexOverflow` is con-ron's own (deviation 1 of the module
/// note) — a stream index or a count too large for a `u64`.  con-leche reads
/// every number as a `Nat` and has nothing to report there.
pub enum ErrTag {
    ExpectedObject,
    ExpectedKey,
    ExpectedColon,
    ExpectedComma,
    ExpectedList,
    UnknownKey,
    DuplicateKey,
    MissingKey,
    MixedKeys,
    ExpectedNat,
    ExpectedString,
    ExpectedBool,
    BadEscape,
    BadUtf8,
    BadBinderInfo,
    BadHints,
    BadPw,
    BadNatVal,
    Trailing,
    NoProgress,
    IndexOverflow,
}

/// con-leche: none — the copy of a payload-free enum (Lean's value semantics;
/// DESIGN.md §3.4 forbids `#[derive(Clone)]`)
pub fn err_tag_dup(t: &ErrTag) -> ErrTag {
    match t {
        ErrTag::ExpectedObject => ErrTag::ExpectedObject,
        ErrTag::ExpectedKey => ErrTag::ExpectedKey,
        ErrTag::ExpectedColon => ErrTag::ExpectedColon,
        ErrTag::ExpectedComma => ErrTag::ExpectedComma,
        ErrTag::ExpectedList => ErrTag::ExpectedList,
        ErrTag::UnknownKey => ErrTag::UnknownKey,
        ErrTag::DuplicateKey => ErrTag::DuplicateKey,
        ErrTag::MissingKey => ErrTag::MissingKey,
        ErrTag::MixedKeys => ErrTag::MixedKeys,
        ErrTag::ExpectedNat => ErrTag::ExpectedNat,
        ErrTag::ExpectedString => ErrTag::ExpectedString,
        ErrTag::ExpectedBool => ErrTag::ExpectedBool,
        ErrTag::BadEscape => ErrTag::BadEscape,
        ErrTag::BadUtf8 => ErrTag::BadUtf8,
        ErrTag::BadBinderInfo => ErrTag::BadBinderInfo,
        ErrTag::BadHints => ErrTag::BadHints,
        ErrTag::BadPw => ErrTag::BadPw,
        ErrTag::BadNatVal => ErrTag::BadNatVal,
        ErrTag::Trailing => ErrTag::Trailing,
        ErrTag::NoProgress => ErrTag::NoProgress,
        ErrTag::IndexOverflow => ErrTag::IndexOverflow,
    }
}

/// con-leche: none — the tag's ordinal, which `err_tag_beq` compares
/// (DESIGN.md §3.4 forbids `#[derive(PartialEq)]`: a derived `eq` would put
/// `core::cmp::PartialEq` and a `StructuralPartialEq` impl into the model).
pub fn err_tag_code(t: &ErrTag) -> u64 {
    match t {
        ErrTag::ExpectedObject => 0,
        ErrTag::ExpectedKey => 1,
        ErrTag::ExpectedColon => 2,
        ErrTag::ExpectedComma => 3,
        ErrTag::ExpectedList => 4,
        ErrTag::UnknownKey => 5,
        ErrTag::DuplicateKey => 6,
        ErrTag::MissingKey => 7,
        ErrTag::MixedKeys => 8,
        ErrTag::ExpectedNat => 9,
        ErrTag::ExpectedString => 10,
        ErrTag::ExpectedBool => 11,
        ErrTag::BadEscape => 12,
        ErrTag::BadUtf8 => 13,
        ErrTag::BadBinderInfo => 14,
        ErrTag::BadHints => 15,
        ErrTag::BadPw => 16,
        ErrTag::BadNatVal => 17,
        ErrTag::Trailing => 18,
        ErrTag::NoProgress => 19,
        ErrTag::IndexOverflow => 20,
    }
}

/// con-leche: none — `ErrTag`'s `DecidableEq`, as a `beq`
pub fn err_tag_beq(a: &ErrTag, b: &ErrTag) -> bool {
    err_tag_code(a) == err_tag_code(b)
}

/// con-leche: ConLeche/Frontend/Scan/Types.lean:95-99 ScanErr
/// Where the recogniser stopped, and why.  `offset` is a byte offset from the
/// start of the *chunk*; the caller subtracts the line's start, as
/// `feed_chunk` does.
pub struct ScanErr {
    pub offset: usize,
    pub what: ErrTag,
}

/// con-leche: none — the copy of a `ScanErr` (Lean's value semantics)
pub fn scan_err_dup(e: &ScanErr) -> ScanErr {
    ScanErr {
        offset: e.offset,
        what: err_tag_dup(&e.what),
    }
}

/// con-leche: ConLeche/Frontend/Scan/Types.lean:101-122 ErrTag.describe
/// The sentence the driver prints for a syntactic failure.
pub fn err_tag_describe(t: &ErrTag) -> Vec<u32> {
    match t {
        ErrTag::ExpectedObject => {
            const M: [u32; 22] = [
                101, 120, 112, 101, 99, 116, 101, 100, 32, 97, 32, 74, 83,
                79, 78, 32, 111, 98, 106, 101, 99, 116,
            ];
            core_types::code_points(&M)
        }
        ErrTag::ExpectedKey => {
            const M: [u32; 14] = [
                101, 120, 112, 101, 99, 116, 101, 100, 32, 97, 32, 107,
                101, 121,
            ];
            core_types::code_points(&M)
        }
        ErrTag::ExpectedColon => {
            const M: [u32; 24] = [
                101, 120, 112, 101, 99, 116, 101, 100, 32, 39, 58, 39, 32,
                97, 102, 116, 101, 114, 32, 97, 32, 107, 101, 121,
            ];
            core_types::code_points(&M)
        }
        ErrTag::ExpectedComma => {
            const M: [u32; 19] = [
                101, 120, 112, 101, 99, 116, 101, 100, 32, 39, 44, 39, 32,
                111, 114, 32, 39, 125, 39,
            ];
            core_types::code_points(&M)
        }
        ErrTag::ExpectedList => {
            const M: [u32; 20] = [
                101, 120, 112, 101, 99, 116, 101, 100, 32, 97, 32, 74, 83,
                79, 78, 32, 108, 105, 115, 116,
            ];
            core_types::code_points(&M)
        }
        ErrTag::UnknownKey => {
            const M: [u32; 11] = [
                117, 110, 107, 110, 111, 119, 110, 32, 107, 101, 121,
            ];
            core_types::code_points(&M)
        }
        ErrTag::DuplicateKey => {
            const M: [u32; 13] = [
                100, 117, 112, 108, 105, 99, 97, 116, 101, 32, 107, 101,
                121,
            ];
            core_types::code_points(&M)
        }
        ErrTag::MissingKey => {
            const M: [u32; 11] = [
                109, 105, 115, 115, 105, 110, 103, 32, 107, 101, 121,
            ];
            core_types::code_points(&M)
        }
        ErrTag::MixedKeys => {
            const M: [u32; 46] = [
                107, 101, 121, 115, 32, 111, 102, 32, 116, 119, 111, 32,
                100, 105, 102, 102, 101, 114, 101, 110, 116, 32, 114, 101,
                99, 111, 114, 100, 32, 107, 105, 110, 100, 115, 32, 105,
                110, 32, 111, 110, 101, 32, 108, 105, 110, 101,
            ];
            core_types::code_points(&M)
        }
        ErrTag::ExpectedNat => {
            const M: [u32; 25] = [
                101, 120, 112, 101, 99, 116, 101, 100, 32, 97, 32, 100,
                101, 99, 105, 109, 97, 108, 32, 110, 117, 109, 98, 101,
                114,
            ];
            core_types::code_points(&M)
        }
        ErrTag::ExpectedString => {
            const M: [u32; 22] = [
                101, 120, 112, 101, 99, 116, 101, 100, 32, 97, 32, 74, 83,
                79, 78, 32, 115, 116, 114, 105, 110, 103,
            ];
            core_types::code_points(&M)
        }
        ErrTag::ExpectedBool => {
            const M: [u32; 22] = [
                101, 120, 112, 101, 99, 116, 101, 100, 32, 116, 114, 117,
                101, 32, 111, 114, 32, 102, 97, 108, 115, 101,
            ];
            core_types::code_points(&M)
        }
        ErrTag::BadEscape => {
            const M: [u32; 21] = [
                117, 110, 107, 110, 111, 119, 110, 32, 115, 116, 114, 105,
                110, 103, 32, 101, 115, 99, 97, 112, 101,
            ];
            core_types::code_points(&M)
        }
        ErrTag::BadUtf8 => {
            const M: [u32; 25] = [
                115, 116, 114, 105, 110, 103, 32, 105, 115, 32, 110, 111,
                116, 32, 118, 97, 108, 105, 100, 32, 85, 84, 70, 45, 56,
            ];
            core_types::code_points(&M)
        }
        ErrTag::BadBinderInfo => {
            const M: [u32; 18] = [
                117, 110, 107, 110, 111, 119, 110, 32, 98, 105, 110, 100,
                101, 114, 73, 110, 102, 111,
            ];
            core_types::code_points(&M)
        }
        ErrTag::BadHints => {
            const M: [u32; 21] = [
                109, 97, 108, 102, 111, 114, 109, 101, 100, 32, 104, 105,
                110, 116, 115, 32, 102, 105, 101, 108, 100,
            ];
            core_types::code_points(&M)
        }
        ErrTag::BadPw => {
            const M: [u32; 18] = [
                109, 97, 108, 102, 111, 114, 109, 101, 100, 32, 112, 119,
                32, 102, 105, 101, 108, 100,
            ];
            core_types::code_points(&M)
        }
        ErrTag::BadNatVal => {
            const M: [u32; 24] = [
                109, 97, 108, 102, 111, 114, 109, 101, 100, 32, 110, 97,
                116, 86, 97, 108, 32, 108, 105, 116, 101, 114, 97, 108,
            ];
            core_types::code_points(&M)
        }
        ErrTag::Trailing => {
            const M: [u32; 31] = [
                116, 114, 97, 105, 108, 105, 110, 103, 32, 98, 121, 116,
                101, 115, 32, 97, 102, 116, 101, 114, 32, 116, 104, 101,
                32, 114, 101, 99, 111, 114, 100,
            ];
            core_types::code_points(&M)
        }
        ErrTag::NoProgress => {
            const M: [u32; 26] = [
                97, 32, 115, 99, 97, 110, 110, 101, 114, 32, 109, 97, 100,
                101, 32, 110, 111, 32, 112, 114, 111, 103, 114, 101, 115,
                115,
            ];
            core_types::code_points(&M)
        }
        ErrTag::IndexOverflow => {
            const M: [u32; 51] = [
                110, 117, 109, 98, 101, 114, 32, 100, 111, 101, 115, 32,
                110, 111, 116, 32, 102, 105, 116, 32, 97, 32, 54, 52, 45,
                98, 105, 116, 32, 105, 110, 100, 101, 120, 32, 40, 68, 69,
                83, 73, 71, 78, 46, 109, 100, 32, 167, 51, 46, 51, 41,
            ];
            core_types::code_points(&M)
        }
    }
}

/// con-leche: ConLeche/Frontend/Scan/Types.lean:124-131 ScanRes
/// A scanner's result: the value and the position after it, or a failure
/// (deviation 3 of the module note).
pub type ScanRes<T> = Result<(T, usize), ScanErr>;

/// con-leche: ConLeche/Frontend/Scan/Types.lean:133-135 ScanErr.render
/// The parse-error message, at the byte offset in the line:
/// `s!"{e.what.describe} (byte {e.offset})"`.
pub fn scan_err_render(e: &ScanErr) -> Vec<u32> {
    const OPEN: [u32; 7] = [32, 40, 98, 121, 116, 101, 32];
    const CLOSE: [u32; 1] = [41];
    let a = crate::frontend::text::cat(
        err_tag_describe(&e.what),
        &core_types::code_points(&OPEN),
    );
    let b = crate::frontend::text::cat(a, &crate::frontend::text::u64_str(e.offset as u64));
    crate::frontend::text::cat(b, &core_types::code_points(&CLOSE))
}

/// con-leche: ConLeche/Frontend/Scan/Types.lean:139-143 NameRec
/// A name-table entry: `{"in":i,"str":{"pre":p,"str":s}}` or
/// `{"in":i,"num":{"i":n,"pre":p}}`.
pub enum NameRec {
    Str(u64, Vec<u32>),
    Num(u64, u64),
}

/// con-leche: ConLeche/Frontend/Scan/Types.lean:145-150 LevelRec
/// A level-table entry.
pub enum LevelRec {
    Succ(u64),
    Max(u64, u64),
    Imax(u64, u64),
    Param(u64),
}

/// con-leche: ConLeche/Frontend/Scan/Types.lean:152-156 PwRec
/// The `pw` datum a binder may carry (the checker's own annotated output;
/// absent in a raw export, which is `never`).  Name indices.
pub enum PwRec {
    Never,
    IfAllZero(Vec<u64>),
}

/// con-leche: ConLeche/Frontend/Scan/Types.lean:158-172 ExprRec
/// An expression-table entry.  The binder `name` index is required to be
/// present and well-formed and is then DROPPED (task #203: parsed binders are
/// anonymous), as is `binderInfo` (task #142) and `letE`'s `nondep`.
///
/// Deviation: `NatVal` carries the literal's decimal digits (module note,
/// deviation 2), as the bytes the scanner read.
pub enum ExprRec {
    Bvar(u64),
    Sort(u64),
    Const(u64, Vec<u64>),
    App(u64, u64),
    Lam(u64, u64, PwRec),
    ForallE(u64, u64, PwRec),
    LetE(u64, u64, u64),
    Proj(u64, u64, u64),
    NatVal(Vec<u8>),
    StrVal(Vec<u32>),
}

/// con-leche: ConLeche/Frontend/Scan/Types.lean:174-178 CVRec
/// A declaration's common data, in stream indices.
pub struct CVRec {
    pub name: u64,
    pub level_params: Vec<u64>,
    pub ty: u64,
}

/// con-leche: ConLeche/Frontend/Scan/Types.lean:180-184 HintsRec
/// A definition's reducibility hint.
pub enum HintsRec {
    Abbrev,
    Opaque,
    Regular(u64),
}

/// con-leche: ConLeche/Frontend/Scan/Types.lean:186-190 RuleRec
/// One recursor rule.
pub struct RuleRec {
    pub ctor: u64,
    pub nfields: u64,
    pub rhs: u64,
}

/// con-leche: ConLeche/Frontend/Scan/Types.lean:192-201 IndTypeRec
/// One member of an inductive block's `types`.
pub struct IndTypeRec {
    pub cv: CVRec,
    pub ctors: Vec<u64>,
    pub is_rec: bool,
    pub is_reflexive: bool,
    pub is_unsafe: bool,
    pub num_indices: u64,
    pub num_nested: u64,
    pub num_params: u64,
}

/// con-leche: ConLeche/Frontend/Scan/Types.lean:203-216 IndCtorRec
/// One member of an inductive block's `ctors`.  `cidx` and `induct` are the
/// format's REDUNDANT fields (task #271, issues #5 and #7): the block's own
/// records determine both, and the parse validates what the stream claims
/// against them.  They are optional in the dialect — a record that omits one
/// carries `None` and is not contradicted.
pub struct IndCtorRec {
    pub cv: CVRec,
    pub is_unsafe: bool,
    pub num_fields: u64,
    pub num_params: u64,
    pub cidx: Option<u64>,
    pub induct: Option<u64>,
}

/// con-leche: ConLeche/Frontend/Scan/Types.lean:218-227 IndRecRec
/// One member of an inductive block's `recs`.
pub struct IndRecRec {
    pub cv: CVRec,
    pub is_unsafe: bool,
    pub k: bool,
    pub num_indices: u64,
    pub num_minors: u64,
    pub num_motives: u64,
    pub num_params: u64,
    pub rules: Vec<RuleRec>,
}

/// con-leche: ConLeche/Frontend/Scan/Types.lean:229-239 DeclRec
/// A declaration record.  `safety` and `kind` keep their spelling (as code
/// points): both are reported back to the user verbatim (an unsupported
/// safety is a DECLINE naming it).
pub enum DeclRec {
    Ax(CVRec, bool),
    Defn(CVRec, u64, HintsRec, Vec<u32>),
    Thm(CVRec, u64),
    Opaq(CVRec, u64, bool),
    Quot(CVRec, Vec<u32>),
    Ind(Vec<IndTypeRec>, Vec<IndCtorRec>, Vec<IndRecRec>),
}

/// con-leche: ConLeche/Frontend/Scan/Types.lean:241-250 LineRec
/// One line of the stream.
pub enum LineRec {
    Name(u64, NameRec),
    Level(u64, LevelRec),
    Expr(u64, ExprRec),
    Decl(DeclRec),
    /// the header record, validated loosely and skipped
    Header,
    /// whitespace only
    Blank,
}

/// con-leche: ConLeche/Frontend/Scan/Types.lean:254-328 Key
/// Every key of the dialect, as a no-argument enumeration.  A key outside this
/// alphabet is an error — the recogniser knows the whole format, and a key it
/// does not know is a stream it does not know.
pub enum Key {
    KUnknown,
    KAll,
    KApp,
    KArg,
    KAxiom,
    KBinderInfo,
    KBody,
    KBvar,
    KCidx,
    KConst,
    KCtor,
    KCtors,
    KDef,
    KFn,
    KForallE,
    KHints,
    KI,
    KIdx,
    KIe,
    KIl,
    KImax,
    KIn,
    KInduct,
    KInductive,
    KIsRec,
    KIsReflexive,
    KIsUnsafe,
    KK,
    KKind,
    KLam,
    KLetE,
    KLevelParams,
    KMax,
    KMeta,
    KName,
    KNatVal,
    KNfields,
    KNondep,
    KNum,
    KNumFields,
    KNumIndices,
    KNumMinors,
    KNumMotives,
    KNumNested,
    KNumParams,
    KOpaque,
    KParam,
    KPre,
    KProj,
    KPw,
    KQuot,
    KRecs,
    KRegular,
    KRhs,
    KRules,
    KSafety,
    KSort,
    KStr,
    KStrVal,
    KStruct,
    KSucc,
    KThm,
    KType,
    KTypeName,
    KTypes,
    KUs,
    KValue,
}

/// con-leche: none — `Key`'s ordinal, which `key_beq` compares (DESIGN.md
/// §3.4 forbids `#[derive(PartialEq)]`)
pub fn key_code(k: &Key) -> u64 {
    match k {
        Key::KUnknown => 0,
        Key::KAll => 1,
        Key::KApp => 2,
        Key::KArg => 3,
        Key::KAxiom => 4,
        Key::KBinderInfo => 5,
        Key::KBody => 6,
        Key::KBvar => 7,
        Key::KCidx => 8,
        Key::KConst => 9,
        Key::KCtor => 10,
        Key::KCtors => 11,
        Key::KDef => 12,
        Key::KFn => 13,
        Key::KForallE => 14,
        Key::KHints => 15,
        Key::KI => 16,
        Key::KIdx => 17,
        Key::KIe => 18,
        Key::KIl => 19,
        Key::KImax => 20,
        Key::KIn => 21,
        Key::KInduct => 22,
        Key::KInductive => 23,
        Key::KIsRec => 24,
        Key::KIsReflexive => 25,
        Key::KIsUnsafe => 26,
        Key::KK => 27,
        Key::KKind => 28,
        Key::KLam => 29,
        Key::KLetE => 30,
        Key::KLevelParams => 31,
        Key::KMax => 32,
        Key::KMeta => 33,
        Key::KName => 34,
        Key::KNatVal => 35,
        Key::KNfields => 36,
        Key::KNondep => 37,
        Key::KNum => 38,
        Key::KNumFields => 39,
        Key::KNumIndices => 40,
        Key::KNumMinors => 41,
        Key::KNumMotives => 42,
        Key::KNumNested => 43,
        Key::KNumParams => 44,
        Key::KOpaque => 45,
        Key::KParam => 46,
        Key::KPre => 47,
        Key::KProj => 48,
        Key::KPw => 49,
        Key::KQuot => 50,
        Key::KRecs => 51,
        Key::KRegular => 52,
        Key::KRhs => 53,
        Key::KRules => 54,
        Key::KSafety => 55,
        Key::KSort => 56,
        Key::KStr => 57,
        Key::KStrVal => 58,
        Key::KStruct => 59,
        Key::KSucc => 60,
        Key::KThm => 61,
        Key::KType => 62,
        Key::KTypeName => 63,
        Key::KTypes => 64,
        Key::KUs => 65,
        Key::KValue => 66,
    }
}

/// con-leche: none — `Key`'s `DecidableEq`, as a `beq`
pub fn key_beq(a: &Key, b: &Key) -> bool {
    key_code(a) == key_code(b)
}

/// con-leche: ConLeche/Frontend/Scan/Types.lean:341-344 IdTable
/// A stream-index-keyed partial map: dense prefix, sparse overflow.
/// lean4export emits ids densely and in order, so the common insert is a push
/// onto the dense `Vec`; a gap or an out-of-order id goes to the sparse
/// overflow map, which is what keeps the hand-written arena fixtures with gaps
/// and out-of-order ids working.
pub struct IdTable<T> {
    pub dense: Vec<T>,
    pub sparse: HashMap<u64, T>,
}

/// con-leche: ConLeche/Frontend/Scan/Types.lean:341-344 IdTable
/// The empty table (Lean's field defaults `dense := #[]`, `sparse := {}`).
pub fn id_table_empty<T>() -> IdTable<T> {
    IdTable {
        dense: Vec::new(),
        sparse: HashMap::new(),
    }
}

/// con-leche: ConLeche/Frontend/Scan/Types.lean:346-348 IdTable.get?
/// The value at a stream index, dense `Vec` first.
pub fn id_table_get<T>(t: &IdTable<T>, i: u64) -> Option<&T> {
    let k = i as usize;
    if (k as u64) == i && k < t.dense.len() {
        Some(&t.dense[k])
    } else {
        t.sparse.get(&i)
    }
}

/// con-leche: ConLeche/Frontend/Scan/Types.lean:350-357 IdTable.insert
/// Bind a stream index.  The dense case is a push; a rebinding below the
/// frontier overwrites; anything beyond the frontier goes sparse.
pub fn id_table_insert<T>(t: &mut IdTable<T>, i: u64, x: T) {
    let n = t.dense.len() as u64;
    if i == n {
        t.dense.push(x);
    } else if i < n {
        t.dense[i as usize] = x;
    } else {
        t.sparse.insert(i, x);
    }
}

/// con-leche: ConLeche/Frontend/Scan/Types.lean:359-361 IdTable.singleton
/// A table with index 0 bound (the implicit `Name.anonymous` / `Level.zero` of
/// the format).
pub fn id_table_singleton<T>(x: T) -> IdTable<T> {
    let mut dense: Vec<T> = Vec::new();
    dense.push(x);
    IdTable {
        dense,
        sparse: HashMap::new(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn s(v: &[u32]) -> String {
        v.iter().filter_map(|c| char::from_u32(*c)).collect()
    }

    /// The dense/sparse table behaves as the naive `u64 -> T` map
    /// `Types.lean`'s three laws specify.
    #[test]
    fn id_table_is_its_naive_map() {
        let mut t: IdTable<u64> = id_table_empty();
        assert!(id_table_get(&t, 0).is_none());
        // dense pushes, in order
        for i in 0..8u64 {
            id_table_insert(&mut t, i, i * 10);
        }
        for i in 0..8u64 {
            assert_eq!(id_table_get(&t, i), Some(&(i * 10)));
        }
        assert_eq!(t.dense.len(), 8);
        // a gap goes sparse
        id_table_insert(&mut t, 100, 1000);
        assert_eq!(id_table_get(&t, 100), Some(&1000));
        assert!(id_table_get(&t, 50).is_none());
        assert_eq!(t.dense.len(), 8);
        // a rebinding below the frontier overwrites
        id_table_insert(&mut t, 3, 999);
        assert_eq!(id_table_get(&t, 3), Some(&999));
        // singleton binds exactly index 0
        let u: IdTable<u64> = id_table_singleton(7);
        assert_eq!(id_table_get(&u, 0), Some(&7));
        assert!(id_table_get(&u, 1).is_none());
    }

    #[test]
    fn err_tag_eq_is_by_ordinal() {
        assert!(err_tag_beq(&ErrTag::BadUtf8, &ErrTag::BadUtf8));
        assert!(!err_tag_beq(&ErrTag::BadUtf8, &ErrTag::BadEscape));
        assert!(err_tag_beq(
            &err_tag_dup(&ErrTag::IndexOverflow),
            &ErrTag::IndexOverflow
        ));
    }

    #[test]
    fn key_eq_is_by_ordinal() {
        assert!(key_beq(&Key::KValue, &Key::KValue));
        assert!(!key_beq(&Key::KValue, &Key::KUs));
    }

    #[test]
    fn render_names_the_tag_and_the_offset() {
        let e = ScanErr {
            offset: 17,
            what: ErrTag::ExpectedColon,
        };
        assert_eq!(s(&scan_err_render(&e)), "expected ':' after a key (byte 17)");
        let f = ScanErr {
            offset: 0,
            what: ErrTag::UnknownKey,
        };
        assert_eq!(s(&scan_err_render(&f)), "unknown key (byte 0)");
    }

    /// Every tag renders non-empty and distinctly.
    #[test]
    fn describe_is_total_and_injective() {
        let tags = [
            ErrTag::ExpectedObject,
            ErrTag::ExpectedKey,
            ErrTag::ExpectedColon,
            ErrTag::ExpectedComma,
            ErrTag::ExpectedList,
            ErrTag::UnknownKey,
            ErrTag::DuplicateKey,
            ErrTag::MissingKey,
            ErrTag::MixedKeys,
            ErrTag::ExpectedNat,
            ErrTag::ExpectedString,
            ErrTag::ExpectedBool,
            ErrTag::BadEscape,
            ErrTag::BadUtf8,
            ErrTag::BadBinderInfo,
            ErrTag::BadHints,
            ErrTag::BadPw,
            ErrTag::BadNatVal,
            ErrTag::Trailing,
            ErrTag::NoProgress,
            ErrTag::IndexOverflow,
        ];
        let mut seen: Vec<String> = Vec::new();
        for t in tags.iter() {
            let d = s(&err_tag_describe(t));
            assert!(!d.is_empty());
            assert!(!seen.contains(&d), "duplicate description {}", d);
            seen.push(d);
        }
        assert_eq!(seen.len(), 21);
    }
}
