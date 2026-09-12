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
//! 2. **A `natVal` literal keeps its decimal digits** (`String`) rather than
//!    becoming a `Nat` here: it is the one unbounded number of the dialect
//!    (§3.3), and `export_c` turns it into a `ron::Nat` through
//!    `con_ron_dump::natdec::from_decimal` when it builds the node.
//! 3. **`ScanRes α` is `Result<(α, usize), ScanErr>`.**  con-leche's
//!    one-constructor `ScanRes` exists to keep a scan allocation-free in
//!    Lean (its doc comment says so: "an `Except ScanErr (α × USize)` would
//!    be three heap objects per scan"); in Rust a `Result` of a tuple of a
//!    machine word is already flat, and `?` is what makes the scanners
//!    readable.
//! 4. **`IdTable` is one `Vec` plus a `HashMap`**, and its three operations
//!    are free functions rather than methods, as in `con-ron-core`.  The
//!    three laws `Types.lean` proves beside the structure
//!    (`get?_empty`/`get?_singleton`/`get?_insert`) are the *specification*
//!    of those functions; they are theorems and are not ported (§3.1 — a
//!    `Prop` is not code), but `id_table_is_its_naive_map` in this module's
//!    tests exercises all three as executable checks.

use std::collections::HashMap;

/// con-leche: ConLeche/Frontend/Scan/Types.lean:47-93 ErrTag
/// What went wrong, as a static tag: the recogniser reports a position and one
/// of these, and the driver renders the sentence.  No formatting runs while a
/// stream is being read.
///
/// Deviation: `IndexOverflow` is con-ron's own (deviation 1 of the module
/// note) — a stream index or a count too large for a `u64`.  con-leche reads
/// every number as a `Nat` and has nothing to report there.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
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

/// con-leche: ConLeche/Frontend/Scan/Types.lean:95-99 ScanErr
/// Where the recogniser stopped, and why.  `offset` is a byte offset from the
/// start of the *chunk*; the caller subtracts the line's start, as
/// `feed_chunk` does.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ScanErr {
    pub offset: usize,
    pub what: ErrTag,
}

/// con-leche: ConLeche/Frontend/Scan/Types.lean:101-122 ErrTag.describe
/// The sentence the driver prints for a syntactic failure.
pub fn err_tag_describe(t: ErrTag) -> &'static str {
    match t {
        ErrTag::ExpectedObject => "expected a JSON object",
        ErrTag::ExpectedKey => "expected a key",
        ErrTag::ExpectedColon => "expected ':' after a key",
        ErrTag::ExpectedComma => "expected ',' or '}'",
        ErrTag::ExpectedList => "expected a JSON list",
        ErrTag::UnknownKey => "unknown key",
        ErrTag::DuplicateKey => "duplicate key",
        ErrTag::MissingKey => "missing key",
        ErrTag::MixedKeys => "keys of two different record kinds in one line",
        ErrTag::ExpectedNat => "expected a decimal number",
        ErrTag::ExpectedString => "expected a JSON string",
        ErrTag::ExpectedBool => "expected true or false",
        ErrTag::BadEscape => "unknown string escape",
        ErrTag::BadUtf8 => "string is not valid UTF-8",
        ErrTag::BadBinderInfo => "unknown binderInfo",
        ErrTag::BadHints => "malformed hints field",
        ErrTag::BadPw => "malformed pw field",
        ErrTag::BadNatVal => "malformed natVal literal",
        ErrTag::Trailing => "trailing bytes after the record",
        ErrTag::NoProgress => "a scanner made no progress",
        ErrTag::IndexOverflow => "number does not fit a 64-bit index (DESIGN.md §3.3)",
    }
}

/// con-leche: ConLeche/Frontend/Scan/Types.lean:124-131 ScanRes
/// A scanner's result: the value and the position after it, or a failure
/// (deviation 3 of the module note).
pub type ScanRes<T> = Result<(T, usize), ScanErr>;

/// con-leche: ConLeche/Frontend/Scan/Types.lean:133-135 ScanErr.render
/// The parse-error message, at the byte offset in the line.
pub fn scan_err_render(e: &ScanErr) -> String {
    format!("{} (byte {})", err_tag_describe(e.what), e.offset)
}

/// con-leche: ConLeche/Frontend/Scan/Types.lean:139-143 NameRec
/// A name-table entry: `{"in":i,"str":{"pre":p,"str":s}}` or
/// `{"in":i,"num":{"i":n,"pre":p}}`.
#[derive(Debug, Clone)]
pub enum NameRec {
    Str(u64, Vec<u32>),
    Num(u64, u64),
}

/// con-leche: ConLeche/Frontend/Scan/Types.lean:145-150 LevelRec
/// A level-table entry.
#[derive(Debug, Clone, Copy)]
pub enum LevelRec {
    Succ(u64),
    Max(u64, u64),
    Imax(u64, u64),
    Param(u64),
}

/// con-leche: ConLeche/Frontend/Scan/Types.lean:152-156 PwRec
/// The `pw` datum a binder may carry (the checker's own annotated output;
/// absent in a raw export, which is `never`).  Name indices.
#[derive(Debug, Clone)]
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
/// deviation 2).
#[derive(Debug, Clone)]
pub enum ExprRec {
    Bvar(u64),
    Sort(u64),
    Const(u64, Vec<u64>),
    App(u64, u64),
    Lam(u64, u64, PwRec),
    ForallE(u64, u64, PwRec),
    LetE(u64, u64, u64),
    Proj(u64, u64, u64),
    NatVal(String),
    StrVal(Vec<u32>),
}

/// con-leche: ConLeche/Frontend/Scan/Types.lean:174-178 CVRec
/// A declaration's common data, in stream indices.
#[derive(Debug, Clone)]
pub struct CVRec {
    pub name: u64,
    pub level_params: Vec<u64>,
    pub ty: u64,
}

/// con-leche: ConLeche/Frontend/Scan/Types.lean:180-184 HintsRec
/// A definition's reducibility hint.
#[derive(Debug, Clone, Copy)]
pub enum HintsRec {
    Abbrev,
    Opaque,
    Regular(u64),
}

/// con-leche: ConLeche/Frontend/Scan/Types.lean:186-190 RuleRec
/// One recursor rule.
#[derive(Debug, Clone, Copy)]
pub struct RuleRec {
    pub ctor: u64,
    pub nfields: u64,
    pub rhs: u64,
}

/// con-leche: ConLeche/Frontend/Scan/Types.lean:192-201 IndTypeRec
/// One member of an inductive block's `types`.
#[derive(Debug, Clone)]
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
#[derive(Debug, Clone)]
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
#[derive(Debug, Clone)]
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
/// A declaration record.  `safety` and `kind` keep their spelling: both are
/// reported back to the user verbatim (an unsupported safety is a DECLINE
/// naming it).
#[derive(Debug, Clone)]
pub enum DeclRec {
    Ax(CVRec, bool),
    Defn(CVRec, u64, HintsRec, String),
    Thm(CVRec, u64),
    Opaq(CVRec, u64, bool),
    Quot(CVRec, String),
    Ind(Vec<IndTypeRec>, Vec<IndCtorRec>, Vec<IndRecRec>),
}

/// con-leche: ConLeche/Frontend/Scan/Types.lean:241-250 LineRec
/// One line of the stream.
#[derive(Debug, Clone)]
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
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
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
    match usize::try_from(i) {
        Ok(k) if k < t.dense.len() => Some(&t.dense[k]),
        _ => t.sparse.get(&i),
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
    IdTable {
        dense: vec![x],
        sparse: HashMap::new(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// `IdTable.get?_empty`, `get?_singleton` and `get?_insert`
    /// (`Types.lean:364-411`) as executable checks: nothing about the dense
    /// frontier or the overflow map is visible through `get?`.
    #[test]
    fn id_table_is_its_naive_map() {
        let t: IdTable<u64> = id_table_empty();
        assert!(id_table_get(&t, 0).is_none());
        let s = id_table_singleton(7u64);
        assert_eq!(id_table_get(&s, 0), Some(&7));
        assert!(id_table_get(&s, 1).is_none());
        // a dense push, an out-of-order id (sparse), then a rebinding below
        // the frontier
        let mut t: IdTable<u64> = id_table_empty();
        id_table_insert(&mut t, 0, 10);
        id_table_insert(&mut t, 1, 11);
        id_table_insert(&mut t, 9, 19);
        id_table_insert(&mut t, 0, 20);
        assert_eq!(t.dense.len(), 2);
        assert_eq!(t.sparse.len(), 1);
        for (i, want) in [(0u64, Some(20u64)), (1, Some(11)), (2, None), (9, Some(19))] {
            assert_eq!(id_table_get(&t, i).copied(), want);
        }
    }
}
