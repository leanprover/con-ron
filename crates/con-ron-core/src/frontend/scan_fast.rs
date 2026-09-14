//! `ConLeche/Frontend/Scan/Fast.lean` — the byte recogniser for the
//! lean4export dialect.  The stream arrives as byte chunks and is read here
//! directly: no line `String`, no JSON DOM, no key lookups.  `scan_line_fwd`
//! decodes one line into a `scan_types::LineRec` and reports where the next
//! line begins; `export_c::apply_line` applies the record.
//!
//! **`Scan/Naive.lean` is the specification.**  con-leche has two recognisers
//! — the naive reference one over `List UInt8` and this byte scanner — and a
//! kernel-checked equality between them (`Scan/Equiv*.lean`, `@[csimp]`).
//! There is ONE Rust recogniser, so every item below cites the `Naive`
//! declaration that *specifies* it beside the `Fast` one it ports.  Where the
//! two disagree in shape, the Rust follows whichever is the honest
//! description of the Rust: see deviations 2 and 3.
//!
//! **Six standing deviations.**
//!
//! 1. **Recursion becomes `loop`.**  Every `scan*Loop` of `Fast.lean` is
//!    tail-recursive because Lean must prove termination from
//!    `b.size - i.toNat`; the Rust is a `while`/`loop` over the same
//!    positions (DESIGN.md §3.4's loop relaxation for this directory,
//!    task #84), and the `noProgress` guard — con-leche's "unreachable, and
//!    it is what makes the measure a theorem rather than a comment" — is kept
//!    verbatim, because in Rust it is what makes the loop terminate.  Every
//!    loop here either *is* the whole function body or has a one-line tail:
//!    Aeneas' `-loops-to-rec` copies the code after a loop into every exit,
//!    so a long tail would be copied per `break`.
//! 2. **`keyAt` keeps the first-byte switch and compares with `matchLit`.**
//!    `Fast.lean` classifies a key by its first byte and its length and then
//!    compares the rest with an UNROLLED chain of byte literals
//!    (`lit1`…`lit10`, task #264) because a Lean string literal in that
//!    position is a heap object the code generator materialises through a
//!    `lean_obj_once` cell.  The port keeps the switch — it is what keeps
//!    `"i"` from being read as `"ie"` — and spells the compare as one
//!    `match_lit` against a `[u8; N]` constant, which a Rust build turns into
//!    an inline compare against a `.rodata` slice.  `key_at` therefore carries
//!    the citations of `keyAt` and of all ten `litN` helpers (§3.7: "several
//!    lines are allowed when a Rust item merges … Lean ones").
//!
//!    **Every literal of this module is a `[u8; N]`, never a `&str`**
//!    (task #86).  Aeneas renders a `&str` constant as `toStr "…"` and
//!    discharges `toStr`'s size bound with `by decide +native` *in the
//!    constant's own definition*, so a `&str` key table puts one
//!    `_native.decide.ax_1` per key into `#print axioms` of every theorem that
//!    reaches `scan_line_fwd` — 68 of them, counted by task #85
//!    (AENEAS_FINDINGS §3.8).  A byte array carries no axiom, costs nothing at
//!    this size (the longest key is eleven bytes), and is what F17 had already
//!    forced on the seven literals that end in a double quote.
//! 3. **The slot loop is factored out once** (`next_member`), as
//!    `naiveObjLoop` factors it in the specification, instead of being
//!    written out per object as `Fast.lean` does.  Each `scan_*_loop` is
//!    still its own function with its own `seen` bits and its own required
//!    mask, so it lines up with its Lean twin key for key.
//! 4. **Numbers are `u64`** and a `natVal` literal keeps its digits
//!    (`scan_types`' module note): `readNat`/`readNat64`/`readNatAt` collapse
//!    into one `read_nat_at` that fails with `ErrTag::IndexOverflow` rather
//!    than growing into a bignum, and `scan_quoted_nat` returns the digit
//!    BYTES.
//! 5. **The port carries its own UTF-8 codec** (task #84).  con-leche's
//!    `String.fromUTF8?` and `Char.toString.toUTF8` are Lean `String`
//!    primitives; the core's `String` is a `Vec<u32>` of code points
//!    (DESIGN.md §3.3) and `str::from_utf8`/`char` are outside the subset, so
//!    `utf8_decode` and `utf8_of` spell the two conversions out.  They are
//!    the only new items of this module beyond the ones §3.4 forces.
//! 6. **The four `[{…}, …]` list loops stay four functions.**  The unverified
//!    twin shares them through a closure argument; a higher-order argument is
//!    outside the subset, and `Fast.lean` writes the four out separately in
//!    any case, so each Lean loop keeps its own Rust function.

use crate::frontend::scan_types::{
    key_beq, CVRec, DeclRec, ErrTag, ExprRec, HintsRec, IndCtorRec, IndRecRec, IndTypeRec, Key,
    LevelRec, LineRec, NameRec, PwRec, RuleRec, ScanErr, ScanRes,
};

/// con-leche: none — `ScanErr.mk` at a byte offset; con-leche writes the
/// anonymous-constructor literal `⟨i.toNat, .tag⟩` inline at every failure
/// site of `Scan/Fast.lean`.
pub fn err<T>(offset: usize, what: ErrTag) -> ScanRes<T> {
    Err(ScanErr { offset, what })
}

/// con-leche: ConLeche/Frontend/Scan/Fast.lean:72-76 byteAt
/// The byte at `i`, or `0` past the end.  A NUL byte never occurs in the
/// dialect, so `0` is a safe "nothing here" and lookahead needs no bounds
/// check at the call site.
pub fn byte_at(b: &[u8], i: usize) -> u8 {
    if i < b.len() {
        b[i]
    } else {
        0
    }
}

/// con-leche: ConLeche/Frontend/Scan/Fast.lean:78-80 isWs
/// JSON whitespace inside a line (a newline ends the line, so it is not one
/// here).
pub fn is_ws(c: u8) -> bool {
    c == 32 || c == 9 || c == 13
}

/// con-leche: ConLeche/Frontend/Scan/Fast.lean:82 isDigit
pub fn is_digit(c: u8) -> bool {
    48 <= c && c <= 57
}

/// con-leche: ConLeche/Frontend/Scan/Fast.lean:84-91 skipWs
/// The first non-whitespace position at or after `i`.
pub fn skip_ws(b: &[u8], i: usize) -> usize {
    let mut i = i;
    while i < b.len() && is_ws(b[i]) {
        i += 1;
    }
    i
}

/// con-leche: ConLeche/Frontend/Scan/Fast.lean:93-101 skipDigits
/// The position after the decimal digit run at `i`; `i` itself when there is
/// no digit there.
pub fn skip_digits(b: &[u8], i: usize) -> usize {
    let mut i = i;
    while i < b.len() && is_digit(b[i]) {
        i += 1;
    }
    i
}

/// con-leche: ConLeche/Frontend/Scan/Fast.lean:121-131 matchLit
/// con-leche: ConLeche/Frontend/Scan/Naive.lean:95-97 naiveLit
/// con-leche: ConLeche/Frontend/Scan/Naive.lean:71-73 lit
/// The bytes of `lit` match `b` from `i` on.  `byte_at` reads `0` past the
/// end and no literal of the dialect holds a `0`, so a compare that runs off
/// the line is `false` — which is `matchLit`'s own out-of-bounds arm.
pub fn match_lit(b: &[u8], i: usize, lit: &[u8]) -> bool {
    let n = lit.len();
    let mut k = 0usize;
    while k < n {
        if byte_at(b, i + k) != lit[k] {
            return false;
        }
        k += 1;
    }
    true
}

/// con-leche: ConLeche/Frontend/Scan/Fast.lean:133-146 keyEnd
/// con-leche: ConLeche/Frontend/Scan/Naive.lean:179-188 naiveKeyBody
/// The position of the closing quote of the key whose *contents* start at `j`;
/// `0` when there is none within the line (a key never carries an escape or a
/// control byte).
pub fn key_end(b: &[u8], j: usize) -> usize {
    let mut j = j;
    while j < b.len() {
        let c = b[j];
        if c == 34 {
            return j;
        }
        if c < 32 || c == 92 {
            return 0;
        }
        j += 1;
    }
    0
}

/// con-leche: ConLeche/Frontend/Scan/Fast.lean:224-446 keyAt
/// con-leche: ConLeche/Frontend/Scan/Fast.lean:160-162 lit1
/// con-leche: ConLeche/Frontend/Scan/Fast.lean:164-166 lit2
/// con-leche: ConLeche/Frontend/Scan/Fast.lean:168-171 lit3
/// con-leche: ConLeche/Frontend/Scan/Fast.lean:173-177 lit4
/// con-leche: ConLeche/Frontend/Scan/Fast.lean:179-183 lit5
/// con-leche: ConLeche/Frontend/Scan/Fast.lean:185-190 lit6
/// con-leche: ConLeche/Frontend/Scan/Fast.lean:192-197 lit7
/// con-leche: ConLeche/Frontend/Scan/Fast.lean:199-205 lit8
/// con-leche: ConLeche/Frontend/Scan/Fast.lean:207-213 lit9
/// con-leche: ConLeche/Frontend/Scan/Fast.lean:215-222 lit10
/// con-leche: ConLeche/Frontend/Scan/Naive.lean:190-210 keyTable
/// con-leche: ConLeche/Frontend/Scan/Naive.lean:212-216 keyOf
/// Classify the key whose opening quote is at `i` and whose contents are `kl`
/// bytes: a switch on the first byte, then on the length — which leaves at
/// most four candidates — and one `match_lit` of the whole key.  A key outside
/// the dialect is `KUnknown`, which every slot loop rejects.  Deviation 2 of
/// the module note: the switch is `keyAt`'s, the compare is one call rather
/// than an unrolled `litN` chain.
pub fn key_at(b: &[u8], i: usize, kl: usize) -> Key {
    let j = i + 1;
    match byte_at(b, j) {
        // 'a'
        97 => {
            if kl == 3 {
                const S_ALL: [u8; 3] = *b"all";
                const S_APP: [u8; 3] = *b"app";
                const S_ARG: [u8; 3] = *b"arg";
                if match_lit(b, j, &S_ALL) {
                    Key::KAll
                } else if match_lit(b, j, &S_APP) {
                    Key::KApp
                } else if match_lit(b, j, &S_ARG) {
                    Key::KArg
                } else {
                    Key::KUnknown
                }
            } else if kl == 5 {
                const S_AXIOM: [u8; 5] = *b"axiom";
                if match_lit(b, j, &S_AXIOM) {
                    Key::KAxiom
                } else {
                    Key::KUnknown
                }
            } else {
                Key::KUnknown
            }
        }
        // 'b'
        98 => {
            if kl == 4 {
                const S_BODY: [u8; 4] = *b"body";
                const S_BVAR: [u8; 4] = *b"bvar";
                if match_lit(b, j, &S_BODY) {
                    Key::KBody
                } else if match_lit(b, j, &S_BVAR) {
                    Key::KBvar
                } else {
                    Key::KUnknown
                }
            } else if kl == 10 {
                const S_BINDERINFO: [u8; 10] = *b"binderInfo";
                if match_lit(b, j, &S_BINDERINFO) {
                    Key::KBinderInfo
                } else {
                    Key::KUnknown
                }
            } else {
                Key::KUnknown
            }
        }
        // 'c'
        99 => {
            if kl == 4 {
                const S_CIDX: [u8; 4] = *b"cidx";
                const S_CTOR: [u8; 4] = *b"ctor";
                if match_lit(b, j, &S_CIDX) {
                    Key::KCidx
                } else if match_lit(b, j, &S_CTOR) {
                    Key::KCtor
                } else {
                    Key::KUnknown
                }
            } else if kl == 5 {
                const S_CONST: [u8; 5] = *b"const";
                const S_CTORS: [u8; 5] = *b"ctors";
                if match_lit(b, j, &S_CONST) {
                    Key::KConst
                } else if match_lit(b, j, &S_CTORS) {
                    Key::KCtors
                } else {
                    Key::KUnknown
                }
            } else {
                Key::KUnknown
            }
        }
        // 'd'
        100 => {
            if kl == 3 {
                const S_DEF: [u8; 3] = *b"def";
                if match_lit(b, j, &S_DEF) {
                    Key::KDef
                } else {
                    Key::KUnknown
                }
            } else {
                Key::KUnknown
            }
        }
        // 'f'
        102 => {
            if kl == 2 {
                const S_FN: [u8; 2] = *b"fn";
                if match_lit(b, j, &S_FN) {
                    Key::KFn
                } else {
                    Key::KUnknown
                }
            } else if kl == 7 {
                const S_FORALLE: [u8; 7] = *b"forallE";
                if match_lit(b, j, &S_FORALLE) {
                    Key::KForallE
                } else {
                    Key::KUnknown
                }
            } else {
                Key::KUnknown
            }
        }
        // 'h'
        104 => {
            if kl == 5 {
                const S_HINTS: [u8; 5] = *b"hints";
                if match_lit(b, j, &S_HINTS) {
                    Key::KHints
                } else {
                    Key::KUnknown
                }
            } else {
                Key::KUnknown
            }
        }
        // 'i'
        105 => {
            if kl == 1 {
                const S_I: [u8; 1] = *b"i";
                if match_lit(b, j, &S_I) {
                    Key::KI
                } else {
                    Key::KUnknown
                }
            } else if kl == 2 {
                const S_IE: [u8; 2] = *b"ie";
                const S_IL: [u8; 2] = *b"il";
                const S_IN: [u8; 2] = *b"in";
                if match_lit(b, j, &S_IE) {
                    Key::KIe
                } else if match_lit(b, j, &S_IL) {
                    Key::KIl
                } else if match_lit(b, j, &S_IN) {
                    Key::KIn
                } else {
                    Key::KUnknown
                }
            } else if kl == 3 {
                const S_IDX: [u8; 3] = *b"idx";
                if match_lit(b, j, &S_IDX) {
                    Key::KIdx
                } else {
                    Key::KUnknown
                }
            } else if kl == 4 {
                const S_IMAX: [u8; 4] = *b"imax";
                if match_lit(b, j, &S_IMAX) {
                    Key::KImax
                } else {
                    Key::KUnknown
                }
            } else if kl == 5 {
                const S_ISREC: [u8; 5] = *b"isRec";
                if match_lit(b, j, &S_ISREC) {
                    Key::KIsRec
                } else {
                    Key::KUnknown
                }
            } else if kl == 6 {
                const S_INDUCT: [u8; 6] = *b"induct";
                if match_lit(b, j, &S_INDUCT) {
                    Key::KInduct
                } else {
                    Key::KUnknown
                }
            } else if kl == 8 {
                const S_ISUNSAFE: [u8; 8] = *b"isUnsafe";
                if match_lit(b, j, &S_ISUNSAFE) {
                    Key::KIsUnsafe
                } else {
                    Key::KUnknown
                }
            } else if kl == 9 {
                const S_INDUCTIVE: [u8; 9] = *b"inductive";
                if match_lit(b, j, &S_INDUCTIVE) {
                    Key::KInductive
                } else {
                    Key::KUnknown
                }
            } else if kl == 11 {
                const S_ISREFLEXIVE: [u8; 11] = *b"isReflexive";
                if match_lit(b, j, &S_ISREFLEXIVE) {
                    Key::KIsReflexive
                } else {
                    Key::KUnknown
                }
            } else {
                Key::KUnknown
            }
        }
        // 'k'
        107 => {
            if kl == 1 {
                const S_K: [u8; 1] = *b"k";
                if match_lit(b, j, &S_K) {
                    Key::KK
                } else {
                    Key::KUnknown
                }
            } else if kl == 4 {
                const S_KIND: [u8; 4] = *b"kind";
                if match_lit(b, j, &S_KIND) {
                    Key::KKind
                } else {
                    Key::KUnknown
                }
            } else {
                Key::KUnknown
            }
        }
        // 'l'
        108 => {
            if kl == 3 {
                const S_LAM: [u8; 3] = *b"lam";
                if match_lit(b, j, &S_LAM) {
                    Key::KLam
                } else {
                    Key::KUnknown
                }
            } else if kl == 4 {
                const S_LETE: [u8; 4] = *b"letE";
                if match_lit(b, j, &S_LETE) {
                    Key::KLetE
                } else {
                    Key::KUnknown
                }
            } else if kl == 11 {
                const S_LEVELPARAMS: [u8; 11] = *b"levelParams";
                if match_lit(b, j, &S_LEVELPARAMS) {
                    Key::KLevelParams
                } else {
                    Key::KUnknown
                }
            } else {
                Key::KUnknown
            }
        }
        // 'm'
        109 => {
            if kl == 3 {
                const S_MAX: [u8; 3] = *b"max";
                if match_lit(b, j, &S_MAX) {
                    Key::KMax
                } else {
                    Key::KUnknown
                }
            } else if kl == 4 {
                const S_META: [u8; 4] = *b"meta";
                if match_lit(b, j, &S_META) {
                    Key::KMeta
                } else {
                    Key::KUnknown
                }
            } else {
                Key::KUnknown
            }
        }
        // 'n'
        110 => {
            if kl == 3 {
                const S_NUM: [u8; 3] = *b"num";
                if match_lit(b, j, &S_NUM) {
                    Key::KNum
                } else {
                    Key::KUnknown
                }
            } else if kl == 4 {
                const S_NAME: [u8; 4] = *b"name";
                if match_lit(b, j, &S_NAME) {
                    Key::KName
                } else {
                    Key::KUnknown
                }
            } else if kl == 6 {
                const S_NATVAL: [u8; 6] = *b"natVal";
                const S_NONDEP: [u8; 6] = *b"nondep";
                if match_lit(b, j, &S_NATVAL) {
                    Key::KNatVal
                } else if match_lit(b, j, &S_NONDEP) {
                    Key::KNondep
                } else {
                    Key::KUnknown
                }
            } else if kl == 7 {
                const S_NFIELDS: [u8; 7] = *b"nfields";
                if match_lit(b, j, &S_NFIELDS) {
                    Key::KNfields
                } else {
                    Key::KUnknown
                }
            } else if kl == 9 {
                const S_NUMFIELDS: [u8; 9] = *b"numFields";
                const S_NUMMINORS: [u8; 9] = *b"numMinors";
                const S_NUMNESTED: [u8; 9] = *b"numNested";
                const S_NUMPARAMS: [u8; 9] = *b"numParams";
                if match_lit(b, j, &S_NUMFIELDS) {
                    Key::KNumFields
                } else if match_lit(b, j, &S_NUMMINORS) {
                    Key::KNumMinors
                } else if match_lit(b, j, &S_NUMNESTED) {
                    Key::KNumNested
                } else if match_lit(b, j, &S_NUMPARAMS) {
                    Key::KNumParams
                } else {
                    Key::KUnknown
                }
            } else if kl == 10 {
                const S_NUMINDICES: [u8; 10] = *b"numIndices";
                const S_NUMMOTIVES: [u8; 10] = *b"numMotives";
                if match_lit(b, j, &S_NUMINDICES) {
                    Key::KNumIndices
                } else if match_lit(b, j, &S_NUMMOTIVES) {
                    Key::KNumMotives
                } else {
                    Key::KUnknown
                }
            } else {
                Key::KUnknown
            }
        }
        // 'o'
        111 => {
            if kl == 6 {
                const S_OPAQUE: [u8; 6] = *b"opaque";
                if match_lit(b, j, &S_OPAQUE) {
                    Key::KOpaque
                } else {
                    Key::KUnknown
                }
            } else {
                Key::KUnknown
            }
        }
        // 'p'
        112 => {
            if kl == 2 {
                const S_PW: [u8; 2] = *b"pw";
                if match_lit(b, j, &S_PW) {
                    Key::KPw
                } else {
                    Key::KUnknown
                }
            } else if kl == 3 {
                const S_PRE: [u8; 3] = *b"pre";
                if match_lit(b, j, &S_PRE) {
                    Key::KPre
                } else {
                    Key::KUnknown
                }
            } else if kl == 4 {
                const S_PROJ: [u8; 4] = *b"proj";
                if match_lit(b, j, &S_PROJ) {
                    Key::KProj
                } else {
                    Key::KUnknown
                }
            } else if kl == 5 {
                const S_PARAM: [u8; 5] = *b"param";
                if match_lit(b, j, &S_PARAM) {
                    Key::KParam
                } else {
                    Key::KUnknown
                }
            } else {
                Key::KUnknown
            }
        }
        // 'q'
        113 => {
            if kl == 4 {
                const S_QUOT: [u8; 4] = *b"quot";
                if match_lit(b, j, &S_QUOT) {
                    Key::KQuot
                } else {
                    Key::KUnknown
                }
            } else {
                Key::KUnknown
            }
        }
        // 'r'
        114 => {
            if kl == 3 {
                const S_RHS: [u8; 3] = *b"rhs";
                if match_lit(b, j, &S_RHS) {
                    Key::KRhs
                } else {
                    Key::KUnknown
                }
            } else if kl == 4 {
                const S_RECS: [u8; 4] = *b"recs";
                if match_lit(b, j, &S_RECS) {
                    Key::KRecs
                } else {
                    Key::KUnknown
                }
            } else if kl == 5 {
                const S_RULES: [u8; 5] = *b"rules";
                if match_lit(b, j, &S_RULES) {
                    Key::KRules
                } else {
                    Key::KUnknown
                }
            } else if kl == 7 {
                const S_REGULAR: [u8; 7] = *b"regular";
                if match_lit(b, j, &S_REGULAR) {
                    Key::KRegular
                } else {
                    Key::KUnknown
                }
            } else {
                Key::KUnknown
            }
        }
        // 's'
        115 => {
            if kl == 3 {
                const S_STR: [u8; 3] = *b"str";
                if match_lit(b, j, &S_STR) {
                    Key::KStr
                } else {
                    Key::KUnknown
                }
            } else if kl == 4 {
                const S_SORT: [u8; 4] = *b"sort";
                const S_SUCC: [u8; 4] = *b"succ";
                if match_lit(b, j, &S_SORT) {
                    Key::KSort
                } else if match_lit(b, j, &S_SUCC) {
                    Key::KSucc
                } else {
                    Key::KUnknown
                }
            } else if kl == 6 {
                const S_SAFETY: [u8; 6] = *b"safety";
                const S_STRVAL: [u8; 6] = *b"strVal";
                const S_STRUCT: [u8; 6] = *b"struct";
                if match_lit(b, j, &S_SAFETY) {
                    Key::KSafety
                } else if match_lit(b, j, &S_STRVAL) {
                    Key::KStrVal
                } else if match_lit(b, j, &S_STRUCT) {
                    Key::KStruct
                } else {
                    Key::KUnknown
                }
            } else {
                Key::KUnknown
            }
        }
        // 't'
        116 => {
            if kl == 3 {
                const S_THM: [u8; 3] = *b"thm";
                if match_lit(b, j, &S_THM) {
                    Key::KThm
                } else {
                    Key::KUnknown
                }
            } else if kl == 4 {
                const S_TYPE: [u8; 4] = *b"type";
                if match_lit(b, j, &S_TYPE) {
                    Key::KType
                } else {
                    Key::KUnknown
                }
            } else if kl == 5 {
                const S_TYPES: [u8; 5] = *b"types";
                if match_lit(b, j, &S_TYPES) {
                    Key::KTypes
                } else {
                    Key::KUnknown
                }
            } else if kl == 8 {
                const S_TYPENAME: [u8; 8] = *b"typeName";
                if match_lit(b, j, &S_TYPENAME) {
                    Key::KTypeName
                } else {
                    Key::KUnknown
                }
            } else {
                Key::KUnknown
            }
        }
        // 'u'
        117 => {
            if kl == 2 {
                const S_US: [u8; 2] = *b"us";
                if match_lit(b, j, &S_US) {
                    Key::KUs
                } else {
                    Key::KUnknown
                }
            } else {
                Key::KUnknown
            }
        }
        // 'v'
        118 => {
            if kl == 5 {
                const S_VALUE: [u8; 5] = *b"value";
                if match_lit(b, j, &S_VALUE) {
                    Key::KValue
                } else {
                    Key::KUnknown
                }
            } else {
                Key::KUnknown
            }
        }
        _ => Key::KUnknown,
    }
}

/// con-leche: ConLeche/Frontend/Scan/Fast.lean:448-453 valueAt
/// con-leche: ConLeche/Frontend/Scan/Naive.lean:218-223 naiveValue
/// The position of a key's value, given the key's closing quote at `ke`: past
/// the colon, whitespace skipped on both sides.  `i` when the colon is
/// missing, which every caller rejects.
pub fn value_at(b: &[u8], i: usize, ke: usize) -> usize {
    let p = skip_ws(b, ke + 1);
    if byte_at(b, p) == 58 {
        skip_ws(b, p + 1)
    } else {
        i
    }
}

/// con-leche: ConLeche/Frontend/Scan/Fast.lean:463-467 scanBool
/// con-leche: ConLeche/Frontend/Scan/Naive.lean:99-106 naiveBool
/// `true` or `false`.
pub fn scan_bool(b: &[u8], i: usize) -> ScanRes<bool> {
    const S_TRUE: [u8; 4] = *b"true";
    const S_FALSE: [u8; 5] = *b"false";
    if match_lit(b, i, &S_TRUE) {
        Ok((true, i + 4))
    } else if match_lit(b, i, &S_FALSE) {
        Ok((false, i + 5))
    } else {
        err(i, ErrTag::ExpectedBool)
    }
}

/// con-leche: ConLeche/Frontend/Scan/Fast.lean:483-494 numEnd
/// con-leche: ConLeche/Frontend/Scan/Naive.lean:81-86 naiveNum
/// The position after a JSON *number* at `i`, or `i` when there is none.  A
/// digit run, with JSON's own leading-zero rule: `0` stands alone, and no
/// other number starts with one.
pub fn num_end(b: &[u8], i: usize) -> usize {
    let e = skip_digits(b, i);
    if e == i {
        i
    } else if byte_at(b, i) == 48 && e != i + 1 {
        i
    } else {
        e
    }
}

/// con-leche: ConLeche/Frontend/Scan/Fast.lean:496-500 readNatAt
/// con-leche: ConLeche/Frontend/Scan/Fast.lean:469-481 readNat64
/// con-leche: ConLeche/Frontend/Scan/Fast.lean:103-112 readNat
/// con-leche: ConLeche/Frontend/Scan/Naive.lean:77-79 digitsVal
/// con-leche: ConLeche/Frontend/Scan/Naive.lean:88-93 naiveNat
/// The value of the decimal digit run `[i, e)`.  con-leche accumulates in a
/// machine word while the run is at most 18 digits and in `Nat` otherwise;
/// here the run is a `u64` and anything longer is `IndexOverflow` (deviation
/// 4 of the module note).  Only a `natVal` literal is unbounded, and it does
/// not come through here — `scan_quoted_nat` keeps its digits.
pub fn read_nat_at(b: &[u8], i: usize, e: usize) -> Result<u64, ScanErr> {
    let mut acc: u64 = 0;
    let mut k = i;
    while k < e && k < b.len() {
        let m = match acc.checked_mul(10) {
            None => {
                return Err(ScanErr {
                    offset: i,
                    what: ErrTag::IndexOverflow,
                })
            }
            Some(x) => x,
        };
        match m.checked_add((b[k] - 48) as u64) {
            None => {
                return Err(ScanErr {
                    offset: i,
                    what: ErrTag::IndexOverflow,
                })
            }
            Some(x) => acc = x,
        }
        k += 1;
    }
    Ok(acc)
}

/// con-leche: ConLeche/Frontend/Scan/Fast.lean:502-523 strClose
/// con-leche: ConLeche/Frontend/Scan/Naive.lean:108-126 naiveStrBody
/// The position of the closing quote of the string whose *contents* start at
/// `j`; `0` when it is unterminated or holds a raw control byte, **before or
/// after a backslash** (`0` is not a possible answer — a closing quote is at
/// least one byte past the opening one).
///
/// A control byte after a backslash is no escape the format has, so the
/// decoder would refuse it anyway; refusing it here is what keeps a line
/// inside its line (con-leche task #290: no scanner of the dialect steps over
/// a newline, so `\` + newline no longer consumes the newline).
pub fn str_close(b: &[u8], j: usize) -> usize {
    let mut j = j;
    while j < b.len() {
        let c = b[j];
        if c == 34 {
            return j;
        } else if c == 92 {
            if j + 1 < b.len() {
                if b[j + 1] < 32 {
                    return 0;
                }
                j += 2;
            } else {
                return 0;
            }
        } else if c < 32 {
            return 0;
        } else {
            j += 1;
        }
    }
    0
}

/// con-leche: ConLeche/Frontend/Scan/Fast.lean:525-534 hasEscape
/// Does the string body `[j, e)` contain a backslash?
pub fn has_escape(b: &[u8], j: usize, e: usize) -> bool {
    let mut j = j;
    while j < b.len() && j < e {
        if b[j] == 92 {
            return true;
        }
        j += 1;
    }
    false
}

/// con-leche: ConLeche/Frontend/Scan/Fast.lean:536-541 hexVal
/// The value of a hexadecimal digit.
pub fn hex_val(c: u8) -> Option<u32> {
    if 48 <= c && c <= 57 {
        Some((c - 48) as u32)
    } else if 97 <= c && c <= 102 {
        Some((c - 87) as u32)
    } else if 65 <= c && c <= 70 {
        Some((c - 55) as u32)
    } else {
        None
    }
}

/// con-leche: ConLeche/Frontend/Scan/Fast.lean:543-549 hex4
/// The value of the four hexadecimal digits at `j`.
pub fn hex4(b: &[u8], j: usize) -> Option<u32> {
    let a = match hex_val(byte_at(b, j)) {
        None => return None,
        Some(x) => x,
    };
    let c = match hex_val(byte_at(b, j + 1)) {
        None => return None,
        Some(x) => x,
    };
    let d = match hex_val(byte_at(b, j + 2)) {
        None => return None,
        Some(x) => x,
    };
    let e = match hex_val(byte_at(b, j + 3)) {
        None => return None,
        Some(x) => x,
    };
    Some((a << 12) | (c << 8) | (d << 4) | e)
}

/// con-leche: ConLeche/Frontend/Scan/Fast.lean:551-557 hex3
/// The value of the three hexadecimal digits at `j` (a surrogate continuation
/// `\uDxxx`, whose leading `d` the caller has matched).
pub fn hex3(b: &[u8], j: usize) -> Option<u32> {
    let a = match hex_val(byte_at(b, j)) {
        None => return None,
        Some(x) => x,
    };
    let c = match hex_val(byte_at(b, j + 1)) {
        None => return None,
        Some(x) => x,
    };
    let d = match hex_val(byte_at(b, j + 2)) {
        None => return None,
        Some(x) => x,
    };
    Some((a << 8) | (c << 4) | d)
}

/// con-leche: ConLeche/Frontend/Scan/Fast.lean:559-560 utf8Of
/// The UTF-8 bytes of a code point, appended to `acc`.  con-leche builds a
/// one-character `String` and takes its UTF-8; `char` and `encode_utf8` are
/// outside the subset (deviation 5 of the module note), so the four widths are
/// written out.  Every value that reaches here is a scalar value — the
/// surrogate range is replaced by `REPLACEMENT_CHAR` before the call — so the
/// encoding is the same bytes.
pub fn utf8_of(acc: Vec<u8>, val: u32) -> Vec<u8> {
    let mut out = acc;
    if val < 0x80 {
        out.push(val as u8);
    } else if val < 0x800 {
        out.push((0xC0 | (val >> 6)) as u8);
        out.push((0x80 | (val & 0x3F)) as u8);
    } else if val < 0x10000 {
        out.push((0xE0 | (val >> 12)) as u8);
        out.push((0x80 | ((val >> 6) & 0x3F)) as u8);
        out.push((0x80 | (val & 0x3F)) as u8);
    } else {
        out.push((0xF0 | (val >> 18)) as u8);
        out.push((0x80 | ((val >> 12) & 0x3F)) as u8);
        out.push((0x80 | ((val >> 6) & 0x3F)) as u8);
        out.push((0x80 | (val & 0x3F)) as u8);
    }
    out
}

/// con-leche: none — Lean's `String.fromUTF8?`, which `scanString` and
/// `unescape` call on the bytes they have collected.  The core's `String` is a
/// `Vec<u32>` of code points (DESIGN.md §3.3) and `str::from_utf8` is outside
/// the subset, so the validation is spelled out: continuation bytes, overlong
/// forms, the surrogate range and anything above U+10FFFF are all `None`,
/// which is exactly what the Lean primitive and Rust's own decoder refuse.
pub fn utf8_decode(b: &[u8], j: usize, e: usize) -> Option<Vec<u32>> {
    let n = if e < b.len() { e } else { b.len() };
    let mut out: Vec<u32> = Vec::new();
    let mut k = j;
    while k < n {
        let c0 = b[k];
        if c0 < 0x80 {
            out.push(c0 as u32);
            k += 1;
        } else if c0 < 0xC2 {
            return None;
        } else if c0 < 0xE0 {
            if n <= k + 1 {
                return None;
            }
            let c1 = b[k + 1];
            if c1 < 0x80 || 0xC0 <= c1 {
                return None;
            }
            out.push((((c0 as u32) & 0x1F) << 6) | ((c1 as u32) & 0x3F));
            k += 2;
        } else if c0 < 0xF0 {
            if n <= k + 2 {
                return None;
            }
            let c1 = b[k + 1];
            let c2 = b[k + 2];
            if c1 < 0x80 || 0xC0 <= c1 || c2 < 0x80 || 0xC0 <= c2 {
                return None;
            }
            let v =
                (((c0 as u32) & 0x0F) << 12) | (((c1 as u32) & 0x3F) << 6) | ((c2 as u32) & 0x3F);
            if v < 0x800 || (0xD800 <= v && v < 0xE000) {
                return None;
            }
            out.push(v);
            k += 3;
        } else if c0 < 0xF5 {
            if n <= k + 3 {
                return None;
            }
            let c1 = b[k + 1];
            let c2 = b[k + 2];
            let c3 = b[k + 3];
            if c1 < 0x80 || 0xC0 <= c1 || c2 < 0x80 || 0xC0 <= c2 || c3 < 0x80 || 0xC0 <= c3 {
                return None;
            }
            let v = (((c0 as u32) & 0x07) << 18)
                | (((c1 as u32) & 0x3F) << 12)
                | (((c2 as u32) & 0x3F) << 6)
                | ((c3 as u32) & 0x3F);
            if v < 0x10000 || 0x10FFFF < v {
                return None;
            }
            out.push(v);
            k += 4;
        } else {
            return None;
        }
    }
    Some(out)
}

/// con-leche: ConLeche/Frontend/Scan/Fast.lean:562-564 replacementChar
/// The Unicode replacement character, which is what a lone surrogate decodes
/// to (the toolchain's own `Lean.Json` reader does the same).
pub const REPLACEMENT_CHAR: u32 = 0xFFFD;

/// con-leche: ConLeche/Frontend/Scan/Fast.lean:566-625 unescape
/// The byte half of `unescape`: decode the string body `[j, e)` into UTF-8
/// bytes, resolving escapes.  con-leche's `unescape` is this loop followed by
/// `String.fromUTF8? acc`, and the two are separate functions here because
/// Aeneas copies the code after a loop into every exit (module note,
/// deviation 1); `unescape` below is the `fromUTF8?` line.
pub fn unescape_bytes(b: &[u8], j: usize, e: usize) -> Option<Vec<u8>> {
    let mut acc: Vec<u8> = Vec::new();
    let mut j = j;
    while j < b.len() && j < e {
        let c = b[j];
        if c != 92 {
            acc.push(c);
            j += 1;
        } else {
            let d = byte_at(b, j + 1);
            let simple: Option<u32> = match d {
                34 => Some(34),
                92 => Some(92),
                47 => Some(47),
                98 => Some(8),
                102 => Some(12),
                110 => Some(10),
                114 => Some(13),
                116 => Some(9),
                _ => None,
            };
            match simple {
                Some(val) => {
                    acc = utf8_of(acc, val);
                    j += 2;
                }
                None => {
                    if d != 117 {
                        return None;
                    }
                    let val = match hex4(b, j + 2) {
                        None => return None,
                        Some(x) => x,
                    };
                    let j6 = j + 6;
                    if val < 0xD800 || 0xE000 <= val {
                        acc = utf8_of(acc, val);
                        j = j6;
                    } else if 0xDC00 <= val {
                        acc = utf8_of(acc, REPLACEMENT_CHAR);
                        j = j6;
                    } else {
                        // a high surrogate: the toolchain's reader looks for a
                        // `\uDxxx` continuation and falls back to U+FFFD
                        let cont = byte_at(b, j6) == 92
                            && byte_at(b, j6 + 1) == 117
                            && (byte_at(b, j6 + 2) == 100 || byte_at(b, j6 + 2) == 68);
                        let v2 = if cont { hex3(b, j6 + 3) } else { None };
                        match v2 {
                            Some(w) => {
                                if w < 0xC00 {
                                    acc = utf8_of(acc, REPLACEMENT_CHAR);
                                    j = j6;
                                } else {
                                    let cv = (((val & 0x3FF) << 10) | (w & 0x3FF)) + 0x10000;
                                    acc = utf8_of(acc, cv);
                                    j = j6 + 6;
                                }
                            }
                            None => {
                                acc = utf8_of(acc, REPLACEMENT_CHAR);
                                j = j6;
                            }
                        }
                    }
                }
            }
        }
    }
    Some(acc)
}

/// con-leche: ConLeche/Frontend/Scan/Fast.lean:566-625 unescape
/// Decode the string body `[j, e)`, resolving escapes.  The no-escape case
/// never comes here (`scan_string` slices instead), so this is the rare path.
/// Bytes accumulate and the whole buffer is UTF-8-validated at the end,
/// exactly as con-leche's `String.fromUTF8? acc` does, so a literal
/// multi-byte sequence passes through byte by byte.
pub fn unescape(b: &[u8], j: usize, e: usize) -> Option<Vec<u32>> {
    match unescape_bytes(b, j, e) {
        None => None,
        Some(acc) => utf8_decode(&acc, 0, acc.len()),
    }
}

/// con-leche: ConLeche/Frontend/Scan/Fast.lean:627-647 scanString
/// con-leche: ConLeche/Frontend/Scan/Naive.lean:128-147 naiveStr
/// A JSON string at `i`: the no-escape body is sliced out of the chunk and
/// UTF-8-validated; a backslash diverts to `unescape`.  The value is the
/// port's string, a code-point vector (§3.3).
///
/// **The decoder is handed the BODY, sliced out** (con-leche task #290): its
/// `\u` lookahead then reads nothing outside the string, so the verdict on a
/// line is the line's alone, whatever follows it.  The slice is a borrow here
/// where con-leche's `ByteArray.extract` copies; the offsets are the same
/// `0 … body.size`.
pub fn scan_string(b: &[u8], i: usize) -> ScanRes<Vec<u32>> {
    if byte_at(b, i) != 34 {
        return err(i, ErrTag::ExpectedString);
    }
    let e = str_close(b, i + 1);
    if e == 0 {
        return err(i, ErrTag::ExpectedString);
    }
    if has_escape(b, i + 1, e) {
        let body = &b[i + 1..e];
        match unescape(body, 0, body.len()) {
            Some(s) => Ok((s, e + 1)),
            None => err(i, ErrTag::BadEscape),
        }
    } else {
        match utf8_decode(b, i + 1, e) {
            Some(s) => Ok((s, e + 1)),
            None => err(i, ErrTag::BadUtf8),
        }
    }
}

/// con-leche: ConLeche/Frontend/Scan/Fast.lean:649-655 scanQuotedNat
/// con-leche: ConLeche/Frontend/Scan/Naive.lean:149-157 naiveQuotedNat
/// A quoted decimal (`"natVal":"12"`).  Deviation 4 of the module note: the
/// digits, not their value — this is the dialect's one unbounded number and
/// `export_c` turns it into a `ron::Nat`.  The digits are ASCII by
/// construction (`skip_digits` accepted them), so the literal's BYTES are its
/// text and no decoding is needed.
pub fn scan_quoted_nat(b: &[u8], i: usize) -> ScanRes<Vec<u8>> {
    if byte_at(b, i) != 34 {
        return err(i, ErrTag::BadNatVal);
    }
    let e = skip_digits(b, i + 1);
    if e == i + 1 || byte_at(b, e) != 34 {
        return err(i, ErrTag::BadNatVal);
    }
    Ok((b[i + 1..e].to_vec(), e + 1))
}

/// con-leche: ConLeche/Frontend/Scan/Fast.lean:657-666 scanBinderInfo
/// con-leche: ConLeche/Frontend/Scan/Naive.lean:159-175 naiveBinderInfo
/// The four `binderInfo` spellings, validated and dropped (task #142): kernel
/// typing erases binder annotations, and an unknown spelling is a malformed
/// record rather than a silently ignored one.  `0` is the failure.
pub fn scan_binder_info(b: &[u8], i: usize) -> usize {
    // The literals below end in the JSON string's own closing quote, so they
    // could never have been `&str` constants: Aeneas emits a `&str` constant
    // as `toStr "..."` **without escaping a double quote inside it**, and the
    // Lean that comes out does not parse (AENEAS_FINDINGS §2.1's F17, found by
    // `lake build` at task #84).  Since task #86 every literal in this file is
    // a byte array, for the second half of §3.8's reason.
    const S_DEFAULT: [u8; 8] = *b"default\"";
    const S_IMPLICIT: [u8; 9] = *b"implicit\"";
    const S_STRICT: [u8; 15] = *b"strictImplicit\"";
    const S_INST: [u8; 13] = *b"instImplicit\"";
    if byte_at(b, i) != 34 {
        0
    } else if match_lit(b, i + 1, &S_DEFAULT) {
        i + 9
    } else if match_lit(b, i + 1, &S_IMPLICIT) {
        i + 10
    } else if match_lit(b, i + 1, &S_STRICT) {
        i + 16
    } else if match_lit(b, i + 1, &S_INST) {
        i + 14
    } else {
        0
    }
}

/// con-leche: ConLeche/Frontend/Scan/Fast.lean:670-698 scanNatListLoop
/// con-leche: ConLeche/Frontend/Scan/Naive.lean:227-250 naiveListLoop
/// `[n, …]`, the shape every index list of the format has.  `want_item` is
/// JSON's own alternation: no empty member, no trailing comma.
pub fn scan_nat_list_loop(b: &[u8], i: usize) -> ScanRes<Vec<u64>> {
    let mut i = i;
    let mut acc: Vec<u64> = Vec::new();
    let mut want_item = true;
    loop {
        if i >= b.len() {
            return err(i, ErrTag::ExpectedList);
        }
        let c = b[i];
        if is_ws(c) {
            i += 1;
        } else if c == 93 {
            if want_item && acc.len() != 0 {
                return err(i, ErrTag::ExpectedList);
            }
            return Ok((acc, i + 1));
        } else if c == 44 {
            if want_item {
                return err(i, ErrTag::ExpectedList);
            }
            i += 1;
            want_item = true;
        } else if is_digit(c) {
            if !want_item {
                return err(i, ErrTag::ExpectedList);
            }
            let e = num_end(b, i);
            if e == i {
                return err(i, ErrTag::ExpectedNat);
            }
            let x = match read_nat_at(b, i, e) {
                Err(er) => return Err(er),
                Ok(p) => p,
            };
            acc.push(x);
            i = e;
            want_item = false;
        } else {
            return err(i, ErrTag::ExpectedList);
        }
    }
}

/// con-leche: ConLeche/Frontend/Scan/Fast.lean:700-702 scanNatList
/// con-leche: ConLeche/Frontend/Scan/Naive.lean:252-257 naiveList
/// con-leche: ConLeche/Frontend/Scan/Naive.lean:259-260 naiveNatList
pub fn scan_nat_list(b: &[u8], i: usize) -> ScanRes<Vec<u64>> {
    if byte_at(b, i) == 91 {
        scan_nat_list_loop(b, i + 1)
    } else {
        err(i, ErrTag::ExpectedList)
    }
}

/// con-leche: ConLeche/Frontend/Scan/Fast.lean:706-715 scanPw
/// con-leche: ConLeche/Frontend/Scan/Naive.lean:264-272 naivePw
/// The `pw` datum: `"never"` or a list of name indices.
pub fn scan_pw(b: &[u8], i: usize) -> ScanRes<PwRec> {
    // The literals below end in the JSON string's own closing quote, so they
    // could never have been `&str` constants: Aeneas emits a `&str` constant
    // as `toStr "..."` **without escaping a double quote inside it**, and the
    // Lean that comes out does not parse (AENEAS_FINDINGS §2.1's F17, found by
    // `lake build` at task #84).  Since task #86 every literal in this file is
    // a byte array, for the second half of §3.8's reason.
    const S_NEVER: [u8; 6] = *b"never\"";
    if byte_at(b, i) == 91 {
        let (ns, j) = match scan_nat_list_loop(b, i + 1) {
            Err(er) => return Err(er),
            Ok(p) => p,
        };
        Ok((PwRec::IfAllZero(ns), j))
    } else if byte_at(b, i) == 34 {
        if match_lit(b, i + 1, &S_NEVER) {
            Ok((PwRec::Never, i + 7))
        } else {
            err(i, ErrTag::BadPw)
        }
    } else {
        err(i, ErrTag::BadPw)
    }
}

/// con-leche: ConLeche/Frontend/Scan/Fast.lean:717-742 scanHints
/// con-leche: ConLeche/Frontend/Scan/Naive.lean:274-303 naiveHints
/// A definition's `hints`: `"abbrev"`, `"opaque"` or `{"regular":n}`.
pub fn scan_hints(b: &[u8], i: usize) -> ScanRes<HintsRec> {
    // The literals below end in the JSON string's own closing quote, so they
    // could never have been `&str` constants: Aeneas emits a `&str` constant
    // as `toStr "..."` **without escaping a double quote inside it**, and the
    // Lean that comes out does not parse (AENEAS_FINDINGS §2.1's F17, found by
    // `lake build` at task #84).  Since task #86 every literal in this file is
    // a byte array, for the second half of §3.8's reason.
    const S_ABBREV: [u8; 7] = *b"abbrev\"";
    const S_OPAQUE: [u8; 7] = *b"opaque\"";
    if byte_at(b, i) == 34 {
        if match_lit(b, i + 1, &S_ABBREV) {
            Ok((HintsRec::Abbrev, i + 8))
        } else if match_lit(b, i + 1, &S_OPAQUE) {
            Ok((HintsRec::Opaque, i + 8))
        } else {
            err(i, ErrTag::BadHints)
        }
    } else if byte_at(b, i) == 123 {
        let p = skip_ws(b, i + 1);
        if byte_at(b, p) != 34 {
            return err(i, ErrTag::BadHints);
        }
        let ke = key_end(b, p + 1);
        if ke == 0 {
            return err(p, ErrTag::BadHints);
        }
        match key_at(b, p, ke - (p + 1)) {
            Key::KRegular => {
                let v = value_at(b, p, ke);
                if v == p {
                    return err(p, ErrTag::ExpectedColon);
                }
                let e = num_end(b, v);
                if e == v {
                    return err(v, ErrTag::ExpectedNat);
                }
                let n = match read_nat_at(b, v, e) {
                    Err(er) => return Err(er),
                    Ok(x) => x,
                };
                let q = skip_ws(b, e);
                if byte_at(b, q) == 125 {
                    Ok((HintsRec::Regular(n), q + 1))
                } else {
                    err(q, ErrTag::ExpectedComma)
                }
            }
            _ => err(p, ErrTag::BadHints),
        }
    } else {
        err(i, ErrTag::BadHints)
    }
}

/// con-leche: ConLeche/Frontend/Scan/Fast.lean:751-775 skipBraced
/// con-leche: ConLeche/Frontend/Scan/Naive.lean:310-330 naiveSkipBraced
/// Skip a `{`/`[`-opened value whose opening bracket is at `i - 1`, counting
/// brackets and stepping over strings; `0` when it does not close, **or when
/// a newline comes first**.  The `meta` header is validated *loosely* — its
/// value must be a bracket- and string-balanced JSON value — and skipped.
///
/// The newline arm is con-leche task #290: the header is one line like every
/// other record, and without it a header cut by a newline swallowed the
/// following lines into itself.
pub fn skip_braced(b: &[u8], i: usize, depth: u64) -> usize {
    let mut i = i;
    let mut depth = depth;
    while i < b.len() {
        let c = b[i];
        if c == 34 {
            let e = str_close(b, i + 1);
            if e == 0 {
                return 0;
            }
            i = e + 1;
        } else if c == 10 {
            return 0;
        } else if c == 123 || c == 91 {
            i += 1;
            depth += 1;
        } else if c == 125 || c == 93 {
            if depth == 0 {
                return i + 1;
            }
            i += 1;
            depth -= 1;
        } else {
            i += 1;
        }
    }
    0
}

// ---------------------------------------------------------------------------
// The objects
// ---------------------------------------------------------------------------

/// con-leche: none — one step of the slot loop every `scan*Loop` of
/// `Scan/Fast.lean` writes out inline, factored once as
/// `Scan/Naive.lean`'s `naiveObjLoop` factors it (module note, deviation 3).
pub enum Member {
    /// the closing brace, `i` on it
    Close,
    /// a key: its classification, the position of its opening quote (the
    /// `noProgress` guard's `i`), and the position of its value
    Key(Key, usize, usize),
}

/// con-leche: ConLeche/Frontend/Scan/Naive.lean:352-389 naiveObjLoop
/// con-leche: ConLeche/Frontend/Scan/Naive.lean:334-338 Slot
/// con-leche: ConLeche/Frontend/Scan/Naive.lean:340-345 Slot.of
/// con-leche: ConLeche/Frontend/Scan/Naive.lean:347-350 Slot.drop
/// The skeleton of every object's slot loop: skip whitespace, stop at `}`,
/// take JSON's own alternation at `,`, and classify the key at `"`.  Key order
/// is therefore irrelevant, a key outside the dialect is an error, and the
/// caller's closing-brace arm checks that every key its record kind requires
/// has been seen.  The position and `want_member` are threaded through the
/// RESULT — con-leche passes them as parameters of a tail call, and §3.4
/// reserves `&mut` for the parse state — so the caller's closing-brace arm
/// reads the same `wantMember` con-leche reads there.
pub fn next_member(
    b: &[u8],
    i: usize,
    want_member: bool,
) -> Result<(Member, usize, bool), ScanErr> {
    let mut i = i;
    let mut want_member = want_member;
    loop {
        if i >= b.len() {
            return Err(ScanErr {
                offset: i,
                what: ErrTag::ExpectedComma,
            });
        }
        let c = b[i];
        if is_ws(c) {
            i += 1;
        } else if c == 125 {
            return Ok((Member::Close, i, want_member));
        } else if c == 44 {
            if want_member {
                return Err(ScanErr {
                    offset: i,
                    what: ErrTag::ExpectedKey,
                });
            }
            i += 1;
            want_member = true;
        } else if c == 34 {
            if !want_member {
                return Err(ScanErr {
                    offset: i,
                    what: ErrTag::ExpectedComma,
                });
            }
            let ke = key_end(b, i + 1);
            if ke == 0 {
                return Err(ScanErr {
                    offset: i,
                    what: ErrTag::ExpectedKey,
                });
            }
            let v = value_at(b, i, ke);
            if v == i {
                return Err(ScanErr {
                    offset: i,
                    what: ErrTag::ExpectedColon,
                });
            }
            return Ok((
                Member::Key(key_at(b, i, ke - (i + 1)), i, v),
                i,
                want_member,
            ));
        } else {
            return Err(ScanErr {
                offset: i,
                what: ErrTag::ExpectedComma,
            });
        }
    }
}

/// con-leche: none — the duplicate-key test every slot of every `scan*Loop`
/// of `Scan/Fast.lean` opens with (`if (seen &&& bit) != 0 then .err
/// ⟨i.toNat, .duplicateKey⟩`).
pub fn dup(seen: u32, bit: u32) -> bool {
    seen & bit != 0
}

/// con-leche: none — the `noProgress` guard every slot of every `scan*Loop`
/// of `Scan/Fast.lean` closes with (`if _hj : i < e then … else .err
/// ⟨i.toNat, .noProgress⟩`).  Unreachable — a scanner consumes at least the
/// byte it dispatched on — and it is what makes the Rust loops terminate.
pub fn prog(ks: usize, e: usize) -> bool {
    ks < e
}

/// con-leche: none — the `numEnd`/`readNatAt`/`noProgress` chain every
/// `Nat`-valued slot of every `scan*Loop` of `Scan/Fast.lean` writes out.
pub fn slot_nat(b: &[u8], ks: usize, v: usize) -> ScanRes<u64> {
    let e = num_end(b, v);
    if e == v {
        return err(v, ErrTag::ExpectedNat);
    }
    if !prog(ks, e) {
        return err(ks, ErrTag::NoProgress);
    }
    match read_nat_at(b, v, e) {
        Err(er) => Err(er),
        Ok(x) => Ok((x, e)),
    }
}

/// con-leche: ConLeche/Frontend/Scan/Fast.lean:795-843 scanStrNameLoop
pub fn scan_str_name_loop(b: &[u8], i: usize) -> ScanRes<NameRec> {
    let mut i = i;
    let mut want_member = true;
    let mut seen: u32 = 0;
    let mut pre: u64 = 0;
    let mut s: Vec<u32> = Vec::new();
    loop {
        let (mem, ni, nw) = match next_member(b, i, want_member) {
            Err(er) => return Err(er),
            Ok(p) => p,
        };
        i = ni;
        want_member = nw;
        match mem {
            Member::Close => {
                if want_member && seen != 0 {
                    return err(i, ErrTag::ExpectedKey);
                }
                if seen & 3 != 3 {
                    return err(i, ErrTag::MissingKey);
                }
                return Ok((NameRec::Str(pre, s), i + 1));
            }
            Member::Key(k, ks, v) => match k {
                Key::KPre => {
                    if dup(seen, 1) {
                        return err(ks, ErrTag::DuplicateKey);
                    }
                    let (x, e) = match slot_nat(b, ks, v) {
                        Err(er) => return Err(er),
                        Ok(p) => p,
                    };
                    pre = x;
                    seen |= 1;
                    i = e;
                    want_member = false;
                }
                Key::KStr => {
                    if dup(seen, 2) {
                        return err(ks, ErrTag::DuplicateKey);
                    }
                    let (x, e) = match scan_string(b, v) {
                        Err(er) => return Err(er),
                        Ok(p) => p,
                    };
                    if !prog(ks, e) {
                        return err(ks, ErrTag::NoProgress);
                    }
                    s = x;
                    seen |= 2;
                    i = e;
                    want_member = false;
                }
                _ => return err(ks, ErrTag::UnknownKey),
            },
        }
    }
}

/// con-leche: ConLeche/Frontend/Scan/Fast.lean:845-849 scanStrName
/// con-leche: ConLeche/Frontend/Scan/Naive.lean:407-408 naiveStrName
/// `{"pre":p,"str":s}` — a name-table entry's string payload.
pub fn scan_str_name(b: &[u8], i: usize) -> ScanRes<NameRec> {
    if byte_at(b, i) == 123 {
        scan_str_name_loop(b, i + 1)
    } else {
        err(i, ErrTag::ExpectedObject)
    }
}

/// con-leche: ConLeche/Frontend/Scan/Fast.lean:851-898 scanNumNameLoop
pub fn scan_num_name_loop(b: &[u8], i: usize) -> ScanRes<NameRec> {
    let mut i = i;
    let mut want_member = true;
    let mut seen: u32 = 0;
    let mut n: u64 = 0;
    let mut pre: u64 = 0;
    loop {
        let (mem, ni, nw) = match next_member(b, i, want_member) {
            Err(er) => return Err(er),
            Ok(p) => p,
        };
        i = ni;
        want_member = nw;
        match mem {
            Member::Close => {
                if want_member && seen != 0 {
                    return err(i, ErrTag::ExpectedKey);
                }
                if seen & 3 != 3 {
                    return err(i, ErrTag::MissingKey);
                }
                return Ok((NameRec::Num(pre, n), i + 1));
            }
            Member::Key(k, ks, v) => match k {
                Key::KI => {
                    if dup(seen, 1) {
                        return err(ks, ErrTag::DuplicateKey);
                    }
                    let (x, e) = match slot_nat(b, ks, v) {
                        Err(er) => return Err(er),
                        Ok(p) => p,
                    };
                    n = x;
                    seen |= 1;
                    i = e;
                    want_member = false;
                }
                Key::KPre => {
                    if dup(seen, 2) {
                        return err(ks, ErrTag::DuplicateKey);
                    }
                    let (x, e) = match slot_nat(b, ks, v) {
                        Err(er) => return Err(er),
                        Ok(p) => p,
                    };
                    pre = x;
                    seen |= 2;
                    i = e;
                    want_member = false;
                }
                _ => return err(ks, ErrTag::UnknownKey),
            },
        }
    }
}

/// con-leche: ConLeche/Frontend/Scan/Fast.lean:900-904 scanNumName
/// con-leche: ConLeche/Frontend/Scan/Naive.lean:416-417 naiveNumName
/// `{"i":n,"pre":p}` — a name-table entry's numeric payload.
pub fn scan_num_name(b: &[u8], i: usize) -> ScanRes<NameRec> {
    if byte_at(b, i) == 123 {
        scan_num_name_loop(b, i + 1)
    } else {
        err(i, ErrTag::ExpectedObject)
    }
}

/// con-leche: ConLeche/Frontend/Scan/Fast.lean:906-953 scanAppExprLoop
pub fn scan_app_expr_loop(b: &[u8], i: usize) -> ScanRes<ExprRec> {
    let mut i = i;
    let mut want_member = true;
    let mut seen: u32 = 0;
    let mut arg: u64 = 0;
    let mut fnx: u64 = 0;
    loop {
        let (mem, ni, nw) = match next_member(b, i, want_member) {
            Err(er) => return Err(er),
            Ok(p) => p,
        };
        i = ni;
        want_member = nw;
        match mem {
            Member::Close => {
                if want_member && seen != 0 {
                    return err(i, ErrTag::ExpectedKey);
                }
                if seen & 3 != 3 {
                    return err(i, ErrTag::MissingKey);
                }
                return Ok((ExprRec::App(fnx, arg), i + 1));
            }
            Member::Key(k, ks, v) => match k {
                Key::KArg => {
                    if dup(seen, 1) {
                        return err(ks, ErrTag::DuplicateKey);
                    }
                    let (x, e) = match slot_nat(b, ks, v) {
                        Err(er) => return Err(er),
                        Ok(p) => p,
                    };
                    arg = x;
                    seen |= 1;
                    i = e;
                    want_member = false;
                }
                Key::KFn => {
                    if dup(seen, 2) {
                        return err(ks, ErrTag::DuplicateKey);
                    }
                    let (x, e) = match slot_nat(b, ks, v) {
                        Err(er) => return Err(er),
                        Ok(p) => p,
                    };
                    fnx = x;
                    seen |= 2;
                    i = e;
                    want_member = false;
                }
                _ => return err(ks, ErrTag::UnknownKey),
            },
        }
    }
}

/// con-leche: ConLeche/Frontend/Scan/Fast.lean:955-959 scanAppExpr
/// con-leche: ConLeche/Frontend/Scan/Naive.lean:427-428 naiveAppExpr
/// `{"arg":A,"fn":F}` — 80 % of every stream's lines.
pub fn scan_app_expr(b: &[u8], i: usize) -> ScanRes<ExprRec> {
    if byte_at(b, i) == 123 {
        scan_app_expr_loop(b, i + 1)
    } else {
        err(i, ErrTag::ExpectedObject)
    }
}

/// con-leche: ConLeche/Frontend/Scan/Fast.lean:961-1034 scanLamExprLoop
/// con-leche: ConLeche/Frontend/Scan/Fast.lean:1044-1117 scanForallExprLoop
/// The two binder loops are one function here: `Fast.lean`'s two copies
/// differ only in the constructor they return, and `Scan/Naive.lean` already
/// shares them (`binderFields`, one field table for both).  `lam` selects the
/// constructor.
pub fn scan_binder_expr_loop(b: &[u8], i: usize, lam: bool) -> ScanRes<ExprRec> {
    let mut i = i;
    let mut want_member = true;
    let mut seen: u32 = 0;
    let mut bd: u64 = 0;
    let mut ty: u64 = 0;
    let mut pw: PwRec = PwRec::Never;
    loop {
        let (mem, ni, nw) = match next_member(b, i, want_member) {
            Err(er) => return Err(er),
            Ok(p) => p,
        };
        i = ni;
        want_member = nw;
        match mem {
            Member::Close => {
                if want_member && seen != 0 {
                    return err(i, ErrTag::ExpectedKey);
                }
                if seen & 15 != 15 {
                    return err(i, ErrTag::MissingKey);
                }
                return Ok((
                    if lam {
                        ExprRec::Lam(ty, bd, pw)
                    } else {
                        ExprRec::ForallE(ty, bd, pw)
                    },
                    i + 1,
                ));
            }
            Member::Key(k, ks, v) => match k {
                Key::KBinderInfo => {
                    if dup(seen, 1) {
                        return err(ks, ErrTag::DuplicateKey);
                    }
                    let e = scan_binder_info(b, v);
                    if e == 0 {
                        return err(v, ErrTag::BadBinderInfo);
                    }
                    if !prog(ks, e) {
                        return err(ks, ErrTag::NoProgress);
                    }
                    seen |= 1;
                    i = e;
                    want_member = false;
                }
                Key::KBody => {
                    if dup(seen, 2) {
                        return err(ks, ErrTag::DuplicateKey);
                    }
                    let (x, e) = match slot_nat(b, ks, v) {
                        Err(er) => return Err(er),
                        Ok(p) => p,
                    };
                    bd = x;
                    seen |= 2;
                    i = e;
                    want_member = false;
                }
                Key::KName => {
                    if dup(seen, 4) {
                        return err(ks, ErrTag::DuplicateKey);
                    }
                    let (_x, e) = match slot_nat(b, ks, v) {
                        Err(er) => return Err(er),
                        Ok(p) => p,
                    };
                    seen |= 4;
                    i = e;
                    want_member = false;
                }
                Key::KType => {
                    if dup(seen, 8) {
                        return err(ks, ErrTag::DuplicateKey);
                    }
                    let (x, e) = match slot_nat(b, ks, v) {
                        Err(er) => return Err(er),
                        Ok(p) => p,
                    };
                    ty = x;
                    seen |= 8;
                    i = e;
                    want_member = false;
                }
                Key::KPw => {
                    if dup(seen, 16) {
                        return err(ks, ErrTag::DuplicateKey);
                    }
                    let (x, e) = match scan_pw(b, v) {
                        Err(er) => return Err(er),
                        Ok(p) => p,
                    };
                    if !prog(ks, e) {
                        return err(ks, ErrTag::NoProgress);
                    }
                    pw = x;
                    seen |= 16;
                    i = e;
                    want_member = false;
                }
                _ => return err(ks, ErrTag::UnknownKey),
            },
        }
    }
}

/// con-leche: ConLeche/Frontend/Scan/Fast.lean:1036-1042 scanLamExpr
/// con-leche: ConLeche/Frontend/Scan/Naive.lean:440-441 naiveLamExpr
/// A `lam` binder.  `binderInfo` and `name` are validated and dropped (tasks
/// #142, #203); `pw` is the checker's own annotation and is absent from a raw
/// export.
pub fn scan_lam_expr(b: &[u8], i: usize) -> ScanRes<ExprRec> {
    if byte_at(b, i) == 123 {
        scan_binder_expr_loop(b, i + 1, true)
    } else {
        err(i, ErrTag::ExpectedObject)
    }
}

/// con-leche: ConLeche/Frontend/Scan/Fast.lean:1119-1123 scanForallExpr
/// con-leche: ConLeche/Frontend/Scan/Naive.lean:443-444 naiveForallExpr
/// A `forallE` binder; as `lam`.
pub fn scan_forall_expr(b: &[u8], i: usize) -> ScanRes<ExprRec> {
    if byte_at(b, i) == 123 {
        scan_binder_expr_loop(b, i + 1, false)
    } else {
        err(i, ErrTag::ExpectedObject)
    }
}

/// con-leche: ConLeche/Frontend/Scan/Fast.lean:1125-1198 scanLetExprLoop
pub fn scan_let_expr_loop(b: &[u8], i: usize) -> ScanRes<ExprRec> {
    let mut i = i;
    let mut want_member = true;
    let mut seen: u32 = 0;
    let mut bd: u64 = 0;
    let mut ty: u64 = 0;
    let mut vl: u64 = 0;
    loop {
        let (mem, ni, nw) = match next_member(b, i, want_member) {
            Err(er) => return Err(er),
            Ok(p) => p,
        };
        i = ni;
        want_member = nw;
        match mem {
            Member::Close => {
                if want_member && seen != 0 {
                    return err(i, ErrTag::ExpectedKey);
                }
                if seen & 27 != 27 {
                    return err(i, ErrTag::MissingKey);
                }
                return Ok((ExprRec::LetE(ty, vl, bd), i + 1));
            }
            Member::Key(k, ks, v) => match k {
                Key::KBody => {
                    if dup(seen, 1) {
                        return err(ks, ErrTag::DuplicateKey);
                    }
                    let (x, e) = match slot_nat(b, ks, v) {
                        Err(er) => return Err(er),
                        Ok(p) => p,
                    };
                    bd = x;
                    seen |= 1;
                    i = e;
                    want_member = false;
                }
                Key::KName => {
                    if dup(seen, 2) {
                        return err(ks, ErrTag::DuplicateKey);
                    }
                    let (_x, e) = match slot_nat(b, ks, v) {
                        Err(er) => return Err(er),
                        Ok(p) => p,
                    };
                    seen |= 2;
                    i = e;
                    want_member = false;
                }
                Key::KNondep => {
                    if dup(seen, 4) {
                        return err(ks, ErrTag::DuplicateKey);
                    }
                    let (_x, e) = match scan_bool(b, v) {
                        Err(er) => return Err(er),
                        Ok(p) => p,
                    };
                    if !prog(ks, e) {
                        return err(ks, ErrTag::NoProgress);
                    }
                    seen |= 4;
                    i = e;
                    want_member = false;
                }
                Key::KType => {
                    if dup(seen, 8) {
                        return err(ks, ErrTag::DuplicateKey);
                    }
                    let (x, e) = match slot_nat(b, ks, v) {
                        Err(er) => return Err(er),
                        Ok(p) => p,
                    };
                    ty = x;
                    seen |= 8;
                    i = e;
                    want_member = false;
                }
                Key::KValue => {
                    if dup(seen, 16) {
                        return err(ks, ErrTag::DuplicateKey);
                    }
                    let (x, e) = match slot_nat(b, ks, v) {
                        Err(er) => return Err(er),
                        Ok(p) => p,
                    };
                    vl = x;
                    seen |= 16;
                    i = e;
                    want_member = false;
                }
                _ => return err(ks, ErrTag::UnknownKey),
            },
        }
    }
}

/// con-leche: ConLeche/Frontend/Scan/Fast.lean:1200-1204 scanLetExpr
/// con-leche: ConLeche/Frontend/Scan/Naive.lean:456-457 naiveLetExpr
/// A `letE` binder.  `nondep` is the format's field and is not read.
pub fn scan_let_expr(b: &[u8], i: usize) -> ScanRes<ExprRec> {
    if byte_at(b, i) == 123 {
        scan_let_expr_loop(b, i + 1)
    } else {
        err(i, ErrTag::ExpectedObject)
    }
}

/// con-leche: ConLeche/Frontend/Scan/Fast.lean:1206-1254 scanConstExprLoop
pub fn scan_const_expr_loop(b: &[u8], i: usize) -> ScanRes<ExprRec> {
    let mut i = i;
    let mut want_member = true;
    let mut seen: u32 = 0;
    let mut nm: u64 = 0;
    let mut us: Vec<u64> = Vec::new();
    loop {
        let (mem, ni, nw) = match next_member(b, i, want_member) {
            Err(er) => return Err(er),
            Ok(p) => p,
        };
        i = ni;
        want_member = nw;
        match mem {
            Member::Close => {
                if want_member && seen != 0 {
                    return err(i, ErrTag::ExpectedKey);
                }
                if seen & 3 != 3 {
                    return err(i, ErrTag::MissingKey);
                }
                return Ok((ExprRec::Const(nm, us), i + 1));
            }
            Member::Key(k, ks, v) => match k {
                Key::KName => {
                    if dup(seen, 1) {
                        return err(ks, ErrTag::DuplicateKey);
                    }
                    let (x, e) = match slot_nat(b, ks, v) {
                        Err(er) => return Err(er),
                        Ok(p) => p,
                    };
                    nm = x;
                    seen |= 1;
                    i = e;
                    want_member = false;
                }
                Key::KUs => {
                    if dup(seen, 2) {
                        return err(ks, ErrTag::DuplicateKey);
                    }
                    let (x, e) = match scan_nat_list(b, v) {
                        Err(er) => return Err(er),
                        Ok(p) => p,
                    };
                    if !prog(ks, e) {
                        return err(ks, ErrTag::NoProgress);
                    }
                    us = x;
                    seen |= 2;
                    i = e;
                    want_member = false;
                }
                _ => return err(ks, ErrTag::UnknownKey),
            },
        }
    }
}

/// con-leche: ConLeche/Frontend/Scan/Fast.lean:1256-1260 scanConstExpr
/// con-leche: ConLeche/Frontend/Scan/Naive.lean:465-466 naiveConstExpr
/// `{"name":N,"us":[…]}`.
pub fn scan_const_expr(b: &[u8], i: usize) -> ScanRes<ExprRec> {
    if byte_at(b, i) == 123 {
        scan_const_expr_loop(b, i + 1)
    } else {
        err(i, ErrTag::ExpectedObject)
    }
}

/// con-leche: ConLeche/Frontend/Scan/Fast.lean:1262-1318 scanProjExprLoop
pub fn scan_proj_expr_loop(b: &[u8], i: usize) -> ScanRes<ExprRec> {
    let mut i = i;
    let mut want_member = true;
    let mut seen: u32 = 0;
    let mut ix: u64 = 0;
    let mut st: u64 = 0;
    let mut tn: u64 = 0;
    loop {
        let (mem, ni, nw) = match next_member(b, i, want_member) {
            Err(er) => return Err(er),
            Ok(p) => p,
        };
        i = ni;
        want_member = nw;
        match mem {
            Member::Close => {
                if want_member && seen != 0 {
                    return err(i, ErrTag::ExpectedKey);
                }
                if seen & 7 != 7 {
                    return err(i, ErrTag::MissingKey);
                }
                return Ok((ExprRec::Proj(tn, ix, st), i + 1));
            }
            Member::Key(k, ks, v) => match k {
                Key::KIdx => {
                    if dup(seen, 1) {
                        return err(ks, ErrTag::DuplicateKey);
                    }
                    let (x, e) = match slot_nat(b, ks, v) {
                        Err(er) => return Err(er),
                        Ok(p) => p,
                    };
                    ix = x;
                    seen |= 1;
                    i = e;
                    want_member = false;
                }
                Key::KStruct => {
                    if dup(seen, 2) {
                        return err(ks, ErrTag::DuplicateKey);
                    }
                    let (x, e) = match slot_nat(b, ks, v) {
                        Err(er) => return Err(er),
                        Ok(p) => p,
                    };
                    st = x;
                    seen |= 2;
                    i = e;
                    want_member = false;
                }
                Key::KTypeName => {
                    if dup(seen, 4) {
                        return err(ks, ErrTag::DuplicateKey);
                    }
                    let (x, e) = match slot_nat(b, ks, v) {
                        Err(er) => return Err(er),
                        Ok(p) => p,
                    };
                    tn = x;
                    seen |= 4;
                    i = e;
                    want_member = false;
                }
                _ => return err(ks, ErrTag::UnknownKey),
            },
        }
    }
}

/// con-leche: ConLeche/Frontend/Scan/Fast.lean:1320-1324 scanProjExpr
/// con-leche: ConLeche/Frontend/Scan/Naive.lean:475-476 naiveProjExpr
/// `{"idx":i,"struct":S,"typeName":T}`.
pub fn scan_proj_expr(b: &[u8], i: usize) -> ScanRes<ExprRec> {
    if byte_at(b, i) == 123 {
        scan_proj_expr_loop(b, i + 1)
    } else {
        err(i, ErrTag::ExpectedObject)
    }
}

/// con-leche: ConLeche/Frontend/Scan/Fast.lean:1326-1382 scanRuleLoop
pub fn scan_rule_loop(b: &[u8], i: usize) -> ScanRes<RuleRec> {
    let mut i = i;
    let mut want_member = true;
    let mut seen: u32 = 0;
    let mut ct: u64 = 0;
    let mut nf: u64 = 0;
    let mut rhs: u64 = 0;
    loop {
        let (mem, ni, nw) = match next_member(b, i, want_member) {
            Err(er) => return Err(er),
            Ok(p) => p,
        };
        i = ni;
        want_member = nw;
        match mem {
            Member::Close => {
                if want_member && seen != 0 {
                    return err(i, ErrTag::ExpectedKey);
                }
                if seen & 7 != 7 {
                    return err(i, ErrTag::MissingKey);
                }
                return Ok((
                    RuleRec {
                        ctor: ct,
                        nfields: nf,
                        rhs,
                    },
                    i + 1,
                ));
            }
            Member::Key(k, ks, v) => match k {
                Key::KCtor => {
                    if dup(seen, 1) {
                        return err(ks, ErrTag::DuplicateKey);
                    }
                    let (x, e) = match slot_nat(b, ks, v) {
                        Err(er) => return Err(er),
                        Ok(p) => p,
                    };
                    ct = x;
                    seen |= 1;
                    i = e;
                    want_member = false;
                }
                Key::KNfields => {
                    if dup(seen, 2) {
                        return err(ks, ErrTag::DuplicateKey);
                    }
                    let (x, e) = match slot_nat(b, ks, v) {
                        Err(er) => return Err(er),
                        Ok(p) => p,
                    };
                    nf = x;
                    seen |= 2;
                    i = e;
                    want_member = false;
                }
                Key::KRhs => {
                    if dup(seen, 4) {
                        return err(ks, ErrTag::DuplicateKey);
                    }
                    let (x, e) = match slot_nat(b, ks, v) {
                        Err(er) => return Err(er),
                        Ok(p) => p,
                    };
                    rhs = x;
                    seen |= 4;
                    i = e;
                    want_member = false;
                }
                _ => return err(ks, ErrTag::UnknownKey),
            },
        }
    }
}

/// con-leche: ConLeche/Frontend/Scan/Fast.lean:1384-1388 scanRule
/// con-leche: ConLeche/Frontend/Scan/Naive.lean:486-487 naiveRule
/// One recursor rule of an inductive record.
pub fn scan_rule(b: &[u8], i: usize) -> ScanRes<RuleRec> {
    if byte_at(b, i) == 123 {
        scan_rule_loop(b, i + 1)
    } else {
        err(i, ErrTag::ExpectedObject)
    }
}

/// con-leche: ConLeche/Frontend/Scan/Fast.lean:1390-1416 scanRuleListLoop
/// con-leche: ConLeche/Frontend/Scan/Naive.lean:227-250 naiveListLoop
/// The `[{…}, …]` loop of Rule records.  Task #84 un-merges the four object
/// list loops the unverified twin shares through a closure: a higher-order
/// argument is outside the Aeneas subset (DESIGN.md §3.4), and `Fast.lean`
/// writes the four out separately anyway, so each Lean loop gets its own
/// Rust function and the refinement is one theorem per Lean declaration.
pub fn scan_rule_list_loop(b: &[u8], i: usize) -> ScanRes<Vec<RuleRec>> {
    let mut i = i;
    let mut acc: Vec<RuleRec> = Vec::new();
    let mut want_item = true;
    loop {
        if i >= b.len() {
            return err(i, ErrTag::ExpectedList);
        }
        let c = b[i];
        if is_ws(c) {
            i += 1;
        } else if c == 93 {
            if want_item && acc.len() != 0 {
                return err(i, ErrTag::ExpectedList);
            }
            return Ok((acc, i + 1));
        } else if c == 44 {
            if want_item {
                return err(i, ErrTag::ExpectedList);
            }
            i += 1;
            want_item = true;
        } else if c == 123 {
            if !want_item {
                return err(i, ErrTag::ExpectedList);
            }
            let (x, e) = match scan_rule(b, i) {
                Err(er) => return Err(er),
                Ok(p) => p,
            };
            if !prog(i, e) {
                return err(i, ErrTag::NoProgress);
            }
            acc.push(x);
            i = e;
            want_item = false;
        } else {
            return err(i, ErrTag::ExpectedList);
        }
    }
}

/// con-leche: ConLeche/Frontend/Scan/Fast.lean:1418-1422 scanRules
/// con-leche: ConLeche/Frontend/Scan/Naive.lean:489 naiveRules
/// The `[…]` of Rule records.
pub fn scan_rules(b: &[u8], i: usize) -> ScanRes<Vec<RuleRec>> {
    if byte_at(b, i) == 91 {
        scan_rule_list_loop(b, i + 1)
    } else {
        err(i, ErrTag::ExpectedList)
    }
}

/// con-leche: ConLeche/Frontend/Scan/Fast.lean:1424-1556 scanIndRecLoop
pub fn scan_ind_rec_loop(b: &[u8], i: usize) -> ScanRes<IndRecRec> {
    let mut i = i;
    let mut want_member = true;
    let mut seen: u32 = 0;
    let mut is_uns = false;
    let mut kf = false;
    let mut lps: Vec<u64> = Vec::new();
    let mut nm: u64 = 0;
    let mut n_idx: u64 = 0;
    let mut n_min: u64 = 0;
    let mut n_mot: u64 = 0;
    let mut n_p: u64 = 0;
    let mut rules: Vec<RuleRec> = Vec::new();
    let mut ty: u64 = 0;
    loop {
        let (mem, ni, nw) = match next_member(b, i, want_member) {
            Err(er) => return Err(er),
            Ok(p) => p,
        };
        i = ni;
        want_member = nw;
        match mem {
            Member::Close => {
                if want_member && seen != 0 {
                    return err(i, ErrTag::ExpectedKey);
                }
                if seen & 2046 != 2046 {
                    return err(i, ErrTag::MissingKey);
                }
                return Ok((
                    IndRecRec {
                        cv: CVRec {
                            name: nm,
                            level_params: lps,
                            ty,
                        },
                        is_unsafe: is_uns,
                        k: kf,
                        num_indices: n_idx,
                        num_minors: n_min,
                        num_motives: n_mot,
                        num_params: n_p,
                        rules,
                    },
                    i + 1,
                ));
            }
            Member::Key(k, ks, v) => match k {
                Key::KAll => {
                    if dup(seen, 1) {
                        return err(ks, ErrTag::DuplicateKey);
                    }
                    let (_x, e) = match scan_nat_list(b, v) {
                        Err(er) => return Err(er),
                        Ok(p) => p,
                    };
                    if !prog(ks, e) {
                        return err(ks, ErrTag::NoProgress);
                    }
                    seen |= 1;
                    i = e;
                    want_member = false;
                }
                Key::KIsUnsafe => {
                    if dup(seen, 2) {
                        return err(ks, ErrTag::DuplicateKey);
                    }
                    let (x, e) = match scan_bool(b, v) {
                        Err(er) => return Err(er),
                        Ok(p) => p,
                    };
                    if !prog(ks, e) {
                        return err(ks, ErrTag::NoProgress);
                    }
                    is_uns = x;
                    seen |= 2;
                    i = e;
                    want_member = false;
                }
                Key::KK => {
                    if dup(seen, 4) {
                        return err(ks, ErrTag::DuplicateKey);
                    }
                    let (x, e) = match scan_bool(b, v) {
                        Err(er) => return Err(er),
                        Ok(p) => p,
                    };
                    if !prog(ks, e) {
                        return err(ks, ErrTag::NoProgress);
                    }
                    kf = x;
                    seen |= 4;
                    i = e;
                    want_member = false;
                }
                Key::KLevelParams => {
                    if dup(seen, 8) {
                        return err(ks, ErrTag::DuplicateKey);
                    }
                    let (x, e) = match scan_nat_list(b, v) {
                        Err(er) => return Err(er),
                        Ok(p) => p,
                    };
                    if !prog(ks, e) {
                        return err(ks, ErrTag::NoProgress);
                    }
                    lps = x;
                    seen |= 8;
                    i = e;
                    want_member = false;
                }
                Key::KName => {
                    if dup(seen, 16) {
                        return err(ks, ErrTag::DuplicateKey);
                    }
                    let (x, e) = match slot_nat(b, ks, v) {
                        Err(er) => return Err(er),
                        Ok(p) => p,
                    };
                    nm = x;
                    seen |= 16;
                    i = e;
                    want_member = false;
                }
                Key::KNumIndices => {
                    if dup(seen, 32) {
                        return err(ks, ErrTag::DuplicateKey);
                    }
                    let (x, e) = match slot_nat(b, ks, v) {
                        Err(er) => return Err(er),
                        Ok(p) => p,
                    };
                    n_idx = x;
                    seen |= 32;
                    i = e;
                    want_member = false;
                }
                Key::KNumMinors => {
                    if dup(seen, 64) {
                        return err(ks, ErrTag::DuplicateKey);
                    }
                    let (x, e) = match slot_nat(b, ks, v) {
                        Err(er) => return Err(er),
                        Ok(p) => p,
                    };
                    n_min = x;
                    seen |= 64;
                    i = e;
                    want_member = false;
                }
                Key::KNumMotives => {
                    if dup(seen, 128) {
                        return err(ks, ErrTag::DuplicateKey);
                    }
                    let (x, e) = match slot_nat(b, ks, v) {
                        Err(er) => return Err(er),
                        Ok(p) => p,
                    };
                    n_mot = x;
                    seen |= 128;
                    i = e;
                    want_member = false;
                }
                Key::KNumParams => {
                    if dup(seen, 256) {
                        return err(ks, ErrTag::DuplicateKey);
                    }
                    let (x, e) = match slot_nat(b, ks, v) {
                        Err(er) => return Err(er),
                        Ok(p) => p,
                    };
                    n_p = x;
                    seen |= 256;
                    i = e;
                    want_member = false;
                }
                Key::KRules => {
                    if dup(seen, 512) {
                        return err(ks, ErrTag::DuplicateKey);
                    }
                    let (x, e) = match scan_rules(b, v) {
                        Err(er) => return Err(er),
                        Ok(p) => p,
                    };
                    if !prog(ks, e) {
                        return err(ks, ErrTag::NoProgress);
                    }
                    rules = x;
                    seen |= 512;
                    i = e;
                    want_member = false;
                }
                Key::KType => {
                    if dup(seen, 1024) {
                        return err(ks, ErrTag::DuplicateKey);
                    }
                    let (x, e) = match slot_nat(b, ks, v) {
                        Err(er) => return Err(er),
                        Ok(p) => p,
                    };
                    ty = x;
                    seen |= 1024;
                    i = e;
                    want_member = false;
                }
                _ => return err(ks, ErrTag::UnknownKey),
            },
        }
    }
}

/// con-leche: ConLeche/Frontend/Scan/Fast.lean:1558-1562 scanIndRec
/// con-leche: ConLeche/Frontend/Scan/Naive.lean:506-507 naiveIndRec
/// One member of an inductive record's `recs`.
pub fn scan_ind_rec(b: &[u8], i: usize) -> ScanRes<IndRecRec> {
    if byte_at(b, i) == 123 {
        scan_ind_rec_loop(b, i + 1)
    } else {
        err(i, ErrTag::ExpectedObject)
    }
}

/// con-leche: ConLeche/Frontend/Scan/Fast.lean:1564-1590 scanIndRecListLoop
/// con-leche: ConLeche/Frontend/Scan/Naive.lean:227-250 naiveListLoop
/// The `[{…}, …]` loop of IndRec records.
pub fn scan_ind_rec_list_loop(b: &[u8], i: usize) -> ScanRes<Vec<IndRecRec>> {
    let mut i = i;
    let mut acc: Vec<IndRecRec> = Vec::new();
    let mut want_item = true;
    loop {
        if i >= b.len() {
            return err(i, ErrTag::ExpectedList);
        }
        let c = b[i];
        if is_ws(c) {
            i += 1;
        } else if c == 93 {
            if want_item && acc.len() != 0 {
                return err(i, ErrTag::ExpectedList);
            }
            return Ok((acc, i + 1));
        } else if c == 44 {
            if want_item {
                return err(i, ErrTag::ExpectedList);
            }
            i += 1;
            want_item = true;
        } else if c == 123 {
            if !want_item {
                return err(i, ErrTag::ExpectedList);
            }
            let (x, e) = match scan_ind_rec(b, i) {
                Err(er) => return Err(er),
                Ok(p) => p,
            };
            if !prog(i, e) {
                return err(i, ErrTag::NoProgress);
            }
            acc.push(x);
            i = e;
            want_item = false;
        } else {
            return err(i, ErrTag::ExpectedList);
        }
    }
}

/// con-leche: ConLeche/Frontend/Scan/Fast.lean:1592-1596 scanIndRecs
/// con-leche: ConLeche/Frontend/Scan/Naive.lean:509 naiveIndRecs
/// The `[…]` of IndRec records.
pub fn scan_ind_recs(b: &[u8], i: usize) -> ScanRes<Vec<IndRecRec>> {
    if byte_at(b, i) == 91 {
        scan_ind_rec_list_loop(b, i + 1)
    } else {
        err(i, ErrTag::ExpectedList)
    }
}

/// con-leche: ConLeche/Frontend/Scan/Fast.lean:1598-1731 scanIndTypeLoop
pub fn scan_ind_type_loop(b: &[u8], i: usize) -> ScanRes<IndTypeRec> {
    let mut i = i;
    let mut want_member = true;
    let mut seen: u32 = 0;
    let mut ctors: Vec<u64> = Vec::new();
    let mut is_rec = false;
    let mut is_refl = false;
    let mut is_uns = false;
    let mut lps: Vec<u64> = Vec::new();
    let mut nm: u64 = 0;
    let mut n_idx: u64 = 0;
    let mut n_nest: u64 = 0;
    let mut n_p: u64 = 0;
    let mut ty: u64 = 0;
    loop {
        let (mem, ni, nw) = match next_member(b, i, want_member) {
            Err(er) => return Err(er),
            Ok(p) => p,
        };
        i = ni;
        want_member = nw;
        match mem {
            Member::Close => {
                if want_member && seen != 0 {
                    return err(i, ErrTag::ExpectedKey);
                }
                if seen & 2046 != 2046 {
                    return err(i, ErrTag::MissingKey);
                }
                return Ok((
                    IndTypeRec {
                        cv: CVRec {
                            name: nm,
                            level_params: lps,
                            ty,
                        },
                        ctors,
                        is_rec,
                        is_reflexive: is_refl,
                        is_unsafe: is_uns,
                        num_indices: n_idx,
                        num_nested: n_nest,
                        num_params: n_p,
                    },
                    i + 1,
                ));
            }
            Member::Key(k, ks, v) => match k {
                Key::KAll => {
                    if dup(seen, 1) {
                        return err(ks, ErrTag::DuplicateKey);
                    }
                    let (_x, e) = match scan_nat_list(b, v) {
                        Err(er) => return Err(er),
                        Ok(p) => p,
                    };
                    if !prog(ks, e) {
                        return err(ks, ErrTag::NoProgress);
                    }
                    seen |= 1;
                    i = e;
                    want_member = false;
                }
                Key::KCtors => {
                    if dup(seen, 2) {
                        return err(ks, ErrTag::DuplicateKey);
                    }
                    let (x, e) = match scan_nat_list(b, v) {
                        Err(er) => return Err(er),
                        Ok(p) => p,
                    };
                    if !prog(ks, e) {
                        return err(ks, ErrTag::NoProgress);
                    }
                    ctors = x;
                    seen |= 2;
                    i = e;
                    want_member = false;
                }
                Key::KIsRec => {
                    if dup(seen, 4) {
                        return err(ks, ErrTag::DuplicateKey);
                    }
                    let (x, e) = match scan_bool(b, v) {
                        Err(er) => return Err(er),
                        Ok(p) => p,
                    };
                    if !prog(ks, e) {
                        return err(ks, ErrTag::NoProgress);
                    }
                    is_rec = x;
                    seen |= 4;
                    i = e;
                    want_member = false;
                }
                Key::KIsReflexive => {
                    if dup(seen, 8) {
                        return err(ks, ErrTag::DuplicateKey);
                    }
                    let (x, e) = match scan_bool(b, v) {
                        Err(er) => return Err(er),
                        Ok(p) => p,
                    };
                    if !prog(ks, e) {
                        return err(ks, ErrTag::NoProgress);
                    }
                    is_refl = x;
                    seen |= 8;
                    i = e;
                    want_member = false;
                }
                Key::KIsUnsafe => {
                    if dup(seen, 16) {
                        return err(ks, ErrTag::DuplicateKey);
                    }
                    let (x, e) = match scan_bool(b, v) {
                        Err(er) => return Err(er),
                        Ok(p) => p,
                    };
                    if !prog(ks, e) {
                        return err(ks, ErrTag::NoProgress);
                    }
                    is_uns = x;
                    seen |= 16;
                    i = e;
                    want_member = false;
                }
                Key::KLevelParams => {
                    if dup(seen, 32) {
                        return err(ks, ErrTag::DuplicateKey);
                    }
                    let (x, e) = match scan_nat_list(b, v) {
                        Err(er) => return Err(er),
                        Ok(p) => p,
                    };
                    if !prog(ks, e) {
                        return err(ks, ErrTag::NoProgress);
                    }
                    lps = x;
                    seen |= 32;
                    i = e;
                    want_member = false;
                }
                Key::KName => {
                    if dup(seen, 64) {
                        return err(ks, ErrTag::DuplicateKey);
                    }
                    let (x, e) = match slot_nat(b, ks, v) {
                        Err(er) => return Err(er),
                        Ok(p) => p,
                    };
                    nm = x;
                    seen |= 64;
                    i = e;
                    want_member = false;
                }
                Key::KNumIndices => {
                    if dup(seen, 128) {
                        return err(ks, ErrTag::DuplicateKey);
                    }
                    let (x, e) = match slot_nat(b, ks, v) {
                        Err(er) => return Err(er),
                        Ok(p) => p,
                    };
                    n_idx = x;
                    seen |= 128;
                    i = e;
                    want_member = false;
                }
                Key::KNumNested => {
                    if dup(seen, 256) {
                        return err(ks, ErrTag::DuplicateKey);
                    }
                    let (x, e) = match slot_nat(b, ks, v) {
                        Err(er) => return Err(er),
                        Ok(p) => p,
                    };
                    n_nest = x;
                    seen |= 256;
                    i = e;
                    want_member = false;
                }
                Key::KNumParams => {
                    if dup(seen, 512) {
                        return err(ks, ErrTag::DuplicateKey);
                    }
                    let (x, e) = match slot_nat(b, ks, v) {
                        Err(er) => return Err(er),
                        Ok(p) => p,
                    };
                    n_p = x;
                    seen |= 512;
                    i = e;
                    want_member = false;
                }
                Key::KType => {
                    if dup(seen, 1024) {
                        return err(ks, ErrTag::DuplicateKey);
                    }
                    let (x, e) = match slot_nat(b, ks, v) {
                        Err(er) => return Err(er),
                        Ok(p) => p,
                    };
                    ty = x;
                    seen |= 1024;
                    i = e;
                    want_member = false;
                }
                _ => return err(ks, ErrTag::UnknownKey),
            },
        }
    }
}

/// con-leche: ConLeche/Frontend/Scan/Fast.lean:1733-1737 scanIndType
/// con-leche: ConLeche/Frontend/Scan/Naive.lean:526-527 naiveIndType
/// One member of an inductive record's `types`.
pub fn scan_ind_type(b: &[u8], i: usize) -> ScanRes<IndTypeRec> {
    if byte_at(b, i) == 123 {
        scan_ind_type_loop(b, i + 1)
    } else {
        err(i, ErrTag::ExpectedObject)
    }
}

/// con-leche: ConLeche/Frontend/Scan/Fast.lean:1739-1765 scanIndTypeListLoop
/// con-leche: ConLeche/Frontend/Scan/Naive.lean:227-250 naiveListLoop
/// The `[{…}, …]` loop of IndType records.
pub fn scan_ind_type_list_loop(b: &[u8], i: usize) -> ScanRes<Vec<IndTypeRec>> {
    let mut i = i;
    let mut acc: Vec<IndTypeRec> = Vec::new();
    let mut want_item = true;
    loop {
        if i >= b.len() {
            return err(i, ErrTag::ExpectedList);
        }
        let c = b[i];
        if is_ws(c) {
            i += 1;
        } else if c == 93 {
            if want_item && acc.len() != 0 {
                return err(i, ErrTag::ExpectedList);
            }
            return Ok((acc, i + 1));
        } else if c == 44 {
            if want_item {
                return err(i, ErrTag::ExpectedList);
            }
            i += 1;
            want_item = true;
        } else if c == 123 {
            if !want_item {
                return err(i, ErrTag::ExpectedList);
            }
            let (x, e) = match scan_ind_type(b, i) {
                Err(er) => return Err(er),
                Ok(p) => p,
            };
            if !prog(i, e) {
                return err(i, ErrTag::NoProgress);
            }
            acc.push(x);
            i = e;
            want_item = false;
        } else {
            return err(i, ErrTag::ExpectedList);
        }
    }
}

/// con-leche: ConLeche/Frontend/Scan/Fast.lean:1767-1771 scanIndTypes
/// con-leche: ConLeche/Frontend/Scan/Naive.lean:529 naiveIndTypes
/// The `[…]` of IndType records.
pub fn scan_ind_types(b: &[u8], i: usize) -> ScanRes<Vec<IndTypeRec>> {
    if byte_at(b, i) == 91 {
        scan_ind_type_list_loop(b, i + 1)
    } else {
        err(i, ErrTag::ExpectedList)
    }
}

/// con-leche: ConLeche/Frontend/Scan/Fast.lean:1773-1878 scanIndCtorLoop
pub fn scan_ind_ctor_loop(b: &[u8], i: usize) -> ScanRes<IndCtorRec> {
    let mut i = i;
    let mut want_member = true;
    let mut seen: u32 = 0;
    let mut is_uns = false;
    let mut lps: Vec<u64> = Vec::new();
    let mut nm: u64 = 0;
    let mut n_f: u64 = 0;
    let mut n_p: u64 = 0;
    let mut ty: u64 = 0;
    let mut ci: Option<u64> = None;
    let mut ind: Option<u64> = None;
    loop {
        let (mem, ni, nw) = match next_member(b, i, want_member) {
            Err(er) => return Err(er),
            Ok(p) => p,
        };
        i = ni;
        want_member = nw;
        match mem {
            Member::Close => {
                if want_member && seen != 0 {
                    return err(i, ErrTag::ExpectedKey);
                }
                if seen & 252 != 252 {
                    return err(i, ErrTag::MissingKey);
                }
                return Ok((
                    IndCtorRec {
                        cv: CVRec {
                            name: nm,
                            level_params: lps,
                            ty,
                        },
                        is_unsafe: is_uns,
                        num_fields: n_f,
                        num_params: n_p,
                        cidx: ci,
                        induct: ind,
                    },
                    i + 1,
                ));
            }
            Member::Key(k, ks, v) => match k {
                Key::KCidx => {
                    if dup(seen, 1) {
                        return err(ks, ErrTag::DuplicateKey);
                    }
                    let (x, e) = match slot_nat(b, ks, v) {
                        Err(er) => return Err(er),
                        Ok(p) => p,
                    };
                    ci = Some(x);
                    seen |= 1;
                    i = e;
                    want_member = false;
                }
                Key::KInduct => {
                    if dup(seen, 2) {
                        return err(ks, ErrTag::DuplicateKey);
                    }
                    let (x, e) = match slot_nat(b, ks, v) {
                        Err(er) => return Err(er),
                        Ok(p) => p,
                    };
                    ind = Some(x);
                    seen |= 2;
                    i = e;
                    want_member = false;
                }
                Key::KIsUnsafe => {
                    if dup(seen, 4) {
                        return err(ks, ErrTag::DuplicateKey);
                    }
                    let (x, e) = match scan_bool(b, v) {
                        Err(er) => return Err(er),
                        Ok(p) => p,
                    };
                    if !prog(ks, e) {
                        return err(ks, ErrTag::NoProgress);
                    }
                    is_uns = x;
                    seen |= 4;
                    i = e;
                    want_member = false;
                }
                Key::KLevelParams => {
                    if dup(seen, 8) {
                        return err(ks, ErrTag::DuplicateKey);
                    }
                    let (x, e) = match scan_nat_list(b, v) {
                        Err(er) => return Err(er),
                        Ok(p) => p,
                    };
                    if !prog(ks, e) {
                        return err(ks, ErrTag::NoProgress);
                    }
                    lps = x;
                    seen |= 8;
                    i = e;
                    want_member = false;
                }
                Key::KName => {
                    if dup(seen, 16) {
                        return err(ks, ErrTag::DuplicateKey);
                    }
                    let (x, e) = match slot_nat(b, ks, v) {
                        Err(er) => return Err(er),
                        Ok(p) => p,
                    };
                    nm = x;
                    seen |= 16;
                    i = e;
                    want_member = false;
                }
                Key::KNumFields => {
                    if dup(seen, 32) {
                        return err(ks, ErrTag::DuplicateKey);
                    }
                    let (x, e) = match slot_nat(b, ks, v) {
                        Err(er) => return Err(er),
                        Ok(p) => p,
                    };
                    n_f = x;
                    seen |= 32;
                    i = e;
                    want_member = false;
                }
                Key::KNumParams => {
                    if dup(seen, 64) {
                        return err(ks, ErrTag::DuplicateKey);
                    }
                    let (x, e) = match slot_nat(b, ks, v) {
                        Err(er) => return Err(er),
                        Ok(p) => p,
                    };
                    n_p = x;
                    seen |= 64;
                    i = e;
                    want_member = false;
                }
                Key::KType => {
                    if dup(seen, 128) {
                        return err(ks, ErrTag::DuplicateKey);
                    }
                    let (x, e) = match slot_nat(b, ks, v) {
                        Err(er) => return Err(er),
                        Ok(p) => p,
                    };
                    ty = x;
                    seen |= 128;
                    i = e;
                    want_member = false;
                }
                _ => return err(ks, ErrTag::UnknownKey),
            },
        }
    }
}

/// con-leche: ConLeche/Frontend/Scan/Fast.lean:1880-1886 scanIndCtor
/// con-leche: ConLeche/Frontend/Scan/Naive.lean:545-546 naiveIndCtor
/// One member of an inductive record's `ctors`.  `cidx` and `induct` are the
/// format's redundant fields and are optional in the dialect.
pub fn scan_ind_ctor(b: &[u8], i: usize) -> ScanRes<IndCtorRec> {
    if byte_at(b, i) == 123 {
        scan_ind_ctor_loop(b, i + 1)
    } else {
        err(i, ErrTag::ExpectedObject)
    }
}

/// con-leche: ConLeche/Frontend/Scan/Fast.lean:1888-1914 scanIndCtorListLoop
/// con-leche: ConLeche/Frontend/Scan/Naive.lean:227-250 naiveListLoop
/// The `[{…}, …]` loop of IndCtor records.
pub fn scan_ind_ctor_list_loop(b: &[u8], i: usize) -> ScanRes<Vec<IndCtorRec>> {
    let mut i = i;
    let mut acc: Vec<IndCtorRec> = Vec::new();
    let mut want_item = true;
    loop {
        if i >= b.len() {
            return err(i, ErrTag::ExpectedList);
        }
        let c = b[i];
        if is_ws(c) {
            i += 1;
        } else if c == 93 {
            if want_item && acc.len() != 0 {
                return err(i, ErrTag::ExpectedList);
            }
            return Ok((acc, i + 1));
        } else if c == 44 {
            if want_item {
                return err(i, ErrTag::ExpectedList);
            }
            i += 1;
            want_item = true;
        } else if c == 123 {
            if !want_item {
                return err(i, ErrTag::ExpectedList);
            }
            let (x, e) = match scan_ind_ctor(b, i) {
                Err(er) => return Err(er),
                Ok(p) => p,
            };
            if !prog(i, e) {
                return err(i, ErrTag::NoProgress);
            }
            acc.push(x);
            i = e;
            want_item = false;
        } else {
            return err(i, ErrTag::ExpectedList);
        }
    }
}

/// con-leche: ConLeche/Frontend/Scan/Fast.lean:1916-1920 scanIndCtors
/// con-leche: ConLeche/Frontend/Scan/Naive.lean:548 naiveIndCtors
/// The `[…]` of IndCtor records.
pub fn scan_ind_ctors(b: &[u8], i: usize) -> ScanRes<Vec<IndCtorRec>> {
    if byte_at(b, i) == 91 {
        scan_ind_ctor_list_loop(b, i + 1)
    } else {
        err(i, ErrTag::ExpectedList)
    }
}

/// con-leche: ConLeche/Frontend/Scan/Fast.lean:1922-1989 scanAxiomDeclLoop
pub fn scan_axiom_decl_loop(b: &[u8], i: usize) -> ScanRes<DeclRec> {
    let mut i = i;
    let mut want_member = true;
    let mut seen: u32 = 0;
    let mut is_uns = false;
    let mut lps: Vec<u64> = Vec::new();
    let mut nm: u64 = 0;
    let mut ty: u64 = 0;
    loop {
        let (mem, ni, nw) = match next_member(b, i, want_member) {
            Err(er) => return Err(er),
            Ok(p) => p,
        };
        i = ni;
        want_member = nw;
        match mem {
            Member::Close => {
                if want_member && seen != 0 {
                    return err(i, ErrTag::ExpectedKey);
                }
                if seen & 15 != 15 {
                    return err(i, ErrTag::MissingKey);
                }
                return Ok((
                    DeclRec::Ax(
                        CVRec {
                            name: nm,
                            level_params: lps,
                            ty,
                        },
                        is_uns,
                    ),
                    i + 1,
                ));
            }
            Member::Key(k, ks, v) => match k {
                Key::KIsUnsafe => {
                    if dup(seen, 1) {
                        return err(ks, ErrTag::DuplicateKey);
                    }
                    let (x, e) = match scan_bool(b, v) {
                        Err(er) => return Err(er),
                        Ok(p) => p,
                    };
                    if !prog(ks, e) {
                        return err(ks, ErrTag::NoProgress);
                    }
                    is_uns = x;
                    seen |= 1;
                    i = e;
                    want_member = false;
                }
                Key::KLevelParams => {
                    if dup(seen, 2) {
                        return err(ks, ErrTag::DuplicateKey);
                    }
                    let (x, e) = match scan_nat_list(b, v) {
                        Err(er) => return Err(er),
                        Ok(p) => p,
                    };
                    if !prog(ks, e) {
                        return err(ks, ErrTag::NoProgress);
                    }
                    lps = x;
                    seen |= 2;
                    i = e;
                    want_member = false;
                }
                Key::KName => {
                    if dup(seen, 4) {
                        return err(ks, ErrTag::DuplicateKey);
                    }
                    let (x, e) = match slot_nat(b, ks, v) {
                        Err(er) => return Err(er),
                        Ok(p) => p,
                    };
                    nm = x;
                    seen |= 4;
                    i = e;
                    want_member = false;
                }
                Key::KType => {
                    if dup(seen, 8) {
                        return err(ks, ErrTag::DuplicateKey);
                    }
                    let (x, e) = match slot_nat(b, ks, v) {
                        Err(er) => return Err(er),
                        Ok(p) => p,
                    };
                    ty = x;
                    seen |= 8;
                    i = e;
                    want_member = false;
                }
                _ => return err(ks, ErrTag::UnknownKey),
            },
        }
    }
}

/// con-leche: ConLeche/Frontend/Scan/Fast.lean:1991-1995 scanAxiomDecl
/// con-leche: ConLeche/Frontend/Scan/Naive.lean:578-579 naiveAxiomDecl
/// An `axiom` record.
pub fn scan_axiom_decl(b: &[u8], i: usize) -> ScanRes<DeclRec> {
    if byte_at(b, i) == 123 {
        scan_axiom_decl_loop(b, i + 1)
    } else {
        err(i, ErrTag::ExpectedObject)
    }
}

/// con-leche: ConLeche/Frontend/Scan/Fast.lean:1997-2092 scanDefDeclLoop
pub fn scan_def_decl_loop(b: &[u8], i: usize) -> ScanRes<DeclRec> {
    let mut i = i;
    let mut want_member = true;
    let mut seen: u32 = 0;
    let mut hints = HintsRec::Regular(0);
    let mut lps: Vec<u64> = Vec::new();
    let mut nm: u64 = 0;
    let mut safety: Vec<u32> = Vec::new();
    let mut ty: u64 = 0;
    let mut vl: u64 = 0;
    loop {
        let (mem, ni, nw) = match next_member(b, i, want_member) {
            Err(er) => return Err(er),
            Ok(p) => p,
        };
        i = ni;
        want_member = nw;
        match mem {
            Member::Close => {
                if want_member && seen != 0 {
                    return err(i, ErrTag::ExpectedKey);
                }
                if seen & 124 != 124 {
                    return err(i, ErrTag::MissingKey);
                }
                return Ok((
                    DeclRec::Defn(
                        CVRec {
                            name: nm,
                            level_params: lps,
                            ty,
                        },
                        vl,
                        hints,
                        safety,
                    ),
                    i + 1,
                ));
            }
            Member::Key(k, ks, v) => match k {
                Key::KAll => {
                    if dup(seen, 1) {
                        return err(ks, ErrTag::DuplicateKey);
                    }
                    let (_x, e) = match scan_nat_list(b, v) {
                        Err(er) => return Err(er),
                        Ok(p) => p,
                    };
                    if !prog(ks, e) {
                        return err(ks, ErrTag::NoProgress);
                    }
                    seen |= 1;
                    i = e;
                    want_member = false;
                }
                Key::KHints => {
                    if dup(seen, 2) {
                        return err(ks, ErrTag::DuplicateKey);
                    }
                    let (x, e) = match scan_hints(b, v) {
                        Err(er) => return Err(er),
                        Ok(p) => p,
                    };
                    if !prog(ks, e) {
                        return err(ks, ErrTag::NoProgress);
                    }
                    hints = x;
                    seen |= 2;
                    i = e;
                    want_member = false;
                }
                Key::KLevelParams => {
                    if dup(seen, 4) {
                        return err(ks, ErrTag::DuplicateKey);
                    }
                    let (x, e) = match scan_nat_list(b, v) {
                        Err(er) => return Err(er),
                        Ok(p) => p,
                    };
                    if !prog(ks, e) {
                        return err(ks, ErrTag::NoProgress);
                    }
                    lps = x;
                    seen |= 4;
                    i = e;
                    want_member = false;
                }
                Key::KName => {
                    if dup(seen, 8) {
                        return err(ks, ErrTag::DuplicateKey);
                    }
                    let (x, e) = match slot_nat(b, ks, v) {
                        Err(er) => return Err(er),
                        Ok(p) => p,
                    };
                    nm = x;
                    seen |= 8;
                    i = e;
                    want_member = false;
                }
                Key::KSafety => {
                    if dup(seen, 16) {
                        return err(ks, ErrTag::DuplicateKey);
                    }
                    let (x, e) = match scan_string(b, v) {
                        Err(er) => return Err(er),
                        Ok(p) => p,
                    };
                    if !prog(ks, e) {
                        return err(ks, ErrTag::NoProgress);
                    }
                    safety = x;
                    seen |= 16;
                    i = e;
                    want_member = false;
                }
                Key::KType => {
                    if dup(seen, 32) {
                        return err(ks, ErrTag::DuplicateKey);
                    }
                    let (x, e) = match slot_nat(b, ks, v) {
                        Err(er) => return Err(er),
                        Ok(p) => p,
                    };
                    ty = x;
                    seen |= 32;
                    i = e;
                    want_member = false;
                }
                Key::KValue => {
                    if dup(seen, 64) {
                        return err(ks, ErrTag::DuplicateKey);
                    }
                    let (x, e) = match slot_nat(b, ks, v) {
                        Err(er) => return Err(er),
                        Ok(p) => p,
                    };
                    vl = x;
                    seen |= 64;
                    i = e;
                    want_member = false;
                }
                _ => return err(ks, ErrTag::UnknownKey),
            },
        }
    }
}

/// con-leche: ConLeche/Frontend/Scan/Fast.lean:2094-2100 scanDefDecl
/// con-leche: ConLeche/Frontend/Scan/Naive.lean:589-590 naiveDefDecl
/// A `def` record.  A missing `hints` field is `regular 0` — hints steer only
/// the unfolding order of lazy delta, so any default is behaviourally safe.
pub fn scan_def_decl(b: &[u8], i: usize) -> ScanRes<DeclRec> {
    if byte_at(b, i) == 123 {
        scan_def_decl_loop(b, i + 1)
    } else {
        err(i, ErrTag::ExpectedObject)
    }
}

/// con-leche: ConLeche/Frontend/Scan/Fast.lean:2102-2177 scanThmDeclLoop
pub fn scan_thm_decl_loop(b: &[u8], i: usize) -> ScanRes<DeclRec> {
    let mut i = i;
    let mut want_member = true;
    let mut seen: u32 = 0;
    let mut lps: Vec<u64> = Vec::new();
    let mut nm: u64 = 0;
    let mut ty: u64 = 0;
    let mut vl: u64 = 0;
    loop {
        let (mem, ni, nw) = match next_member(b, i, want_member) {
            Err(er) => return Err(er),
            Ok(p) => p,
        };
        i = ni;
        want_member = nw;
        match mem {
            Member::Close => {
                if want_member && seen != 0 {
                    return err(i, ErrTag::ExpectedKey);
                }
                if seen & 30 != 30 {
                    return err(i, ErrTag::MissingKey);
                }
                return Ok((
                    DeclRec::Thm(
                        CVRec {
                            name: nm,
                            level_params: lps,
                            ty,
                        },
                        vl,
                    ),
                    i + 1,
                ));
            }
            Member::Key(k, ks, v) => match k {
                Key::KAll => {
                    if dup(seen, 1) {
                        return err(ks, ErrTag::DuplicateKey);
                    }
                    let (_x, e) = match scan_nat_list(b, v) {
                        Err(er) => return Err(er),
                        Ok(p) => p,
                    };
                    if !prog(ks, e) {
                        return err(ks, ErrTag::NoProgress);
                    }
                    seen |= 1;
                    i = e;
                    want_member = false;
                }
                Key::KLevelParams => {
                    if dup(seen, 2) {
                        return err(ks, ErrTag::DuplicateKey);
                    }
                    let (x, e) = match scan_nat_list(b, v) {
                        Err(er) => return Err(er),
                        Ok(p) => p,
                    };
                    if !prog(ks, e) {
                        return err(ks, ErrTag::NoProgress);
                    }
                    lps = x;
                    seen |= 2;
                    i = e;
                    want_member = false;
                }
                Key::KName => {
                    if dup(seen, 4) {
                        return err(ks, ErrTag::DuplicateKey);
                    }
                    let (x, e) = match slot_nat(b, ks, v) {
                        Err(er) => return Err(er),
                        Ok(p) => p,
                    };
                    nm = x;
                    seen |= 4;
                    i = e;
                    want_member = false;
                }
                Key::KType => {
                    if dup(seen, 8) {
                        return err(ks, ErrTag::DuplicateKey);
                    }
                    let (x, e) = match slot_nat(b, ks, v) {
                        Err(er) => return Err(er),
                        Ok(p) => p,
                    };
                    ty = x;
                    seen |= 8;
                    i = e;
                    want_member = false;
                }
                Key::KValue => {
                    if dup(seen, 16) {
                        return err(ks, ErrTag::DuplicateKey);
                    }
                    let (x, e) = match slot_nat(b, ks, v) {
                        Err(er) => return Err(er),
                        Ok(p) => p,
                    };
                    vl = x;
                    seen |= 16;
                    i = e;
                    want_member = false;
                }
                _ => return err(ks, ErrTag::UnknownKey),
            },
        }
    }
}

/// con-leche: ConLeche/Frontend/Scan/Fast.lean:2179-2183 scanThmDecl
/// con-leche: ConLeche/Frontend/Scan/Naive.lean:597-598 naiveThmDecl
/// A `thm` record.
pub fn scan_thm_decl(b: &[u8], i: usize) -> ScanRes<DeclRec> {
    if byte_at(b, i) == 123 {
        scan_thm_decl_loop(b, i + 1)
    } else {
        err(i, ErrTag::ExpectedObject)
    }
}

/// con-leche: ConLeche/Frontend/Scan/Fast.lean:2185-2270 scanOpaqueDeclLoop
pub fn scan_opaque_decl_loop(b: &[u8], i: usize) -> ScanRes<DeclRec> {
    let mut i = i;
    let mut want_member = true;
    let mut seen: u32 = 0;
    let mut is_uns = false;
    let mut lps: Vec<u64> = Vec::new();
    let mut nm: u64 = 0;
    let mut ty: u64 = 0;
    let mut vl: u64 = 0;
    loop {
        let (mem, ni, nw) = match next_member(b, i, want_member) {
            Err(er) => return Err(er),
            Ok(p) => p,
        };
        i = ni;
        want_member = nw;
        match mem {
            Member::Close => {
                if want_member && seen != 0 {
                    return err(i, ErrTag::ExpectedKey);
                }
                if seen & 62 != 62 {
                    return err(i, ErrTag::MissingKey);
                }
                return Ok((
                    DeclRec::Opaq(
                        CVRec {
                            name: nm,
                            level_params: lps,
                            ty,
                        },
                        vl,
                        is_uns,
                    ),
                    i + 1,
                ));
            }
            Member::Key(k, ks, v) => match k {
                Key::KAll => {
                    if dup(seen, 1) {
                        return err(ks, ErrTag::DuplicateKey);
                    }
                    let (_x, e) = match scan_nat_list(b, v) {
                        Err(er) => return Err(er),
                        Ok(p) => p,
                    };
                    if !prog(ks, e) {
                        return err(ks, ErrTag::NoProgress);
                    }
                    seen |= 1;
                    i = e;
                    want_member = false;
                }
                Key::KIsUnsafe => {
                    if dup(seen, 2) {
                        return err(ks, ErrTag::DuplicateKey);
                    }
                    let (x, e) = match scan_bool(b, v) {
                        Err(er) => return Err(er),
                        Ok(p) => p,
                    };
                    if !prog(ks, e) {
                        return err(ks, ErrTag::NoProgress);
                    }
                    is_uns = x;
                    seen |= 2;
                    i = e;
                    want_member = false;
                }
                Key::KLevelParams => {
                    if dup(seen, 4) {
                        return err(ks, ErrTag::DuplicateKey);
                    }
                    let (x, e) = match scan_nat_list(b, v) {
                        Err(er) => return Err(er),
                        Ok(p) => p,
                    };
                    if !prog(ks, e) {
                        return err(ks, ErrTag::NoProgress);
                    }
                    lps = x;
                    seen |= 4;
                    i = e;
                    want_member = false;
                }
                Key::KName => {
                    if dup(seen, 8) {
                        return err(ks, ErrTag::DuplicateKey);
                    }
                    let (x, e) = match slot_nat(b, ks, v) {
                        Err(er) => return Err(er),
                        Ok(p) => p,
                    };
                    nm = x;
                    seen |= 8;
                    i = e;
                    want_member = false;
                }
                Key::KType => {
                    if dup(seen, 16) {
                        return err(ks, ErrTag::DuplicateKey);
                    }
                    let (x, e) = match slot_nat(b, ks, v) {
                        Err(er) => return Err(er),
                        Ok(p) => p,
                    };
                    ty = x;
                    seen |= 16;
                    i = e;
                    want_member = false;
                }
                Key::KValue => {
                    if dup(seen, 32) {
                        return err(ks, ErrTag::DuplicateKey);
                    }
                    let (x, e) = match slot_nat(b, ks, v) {
                        Err(er) => return Err(er),
                        Ok(p) => p,
                    };
                    vl = x;
                    seen |= 32;
                    i = e;
                    want_member = false;
                }
                _ => return err(ks, ErrTag::UnknownKey),
            },
        }
    }
}

/// con-leche: ConLeche/Frontend/Scan/Fast.lean:2272-2276 scanOpaqueDecl
/// con-leche: ConLeche/Frontend/Scan/Naive.lean:606-607 naiveOpaqueDecl
/// An `opaque` record.
pub fn scan_opaque_decl(b: &[u8], i: usize) -> ScanRes<DeclRec> {
    if byte_at(b, i) == 123 {
        scan_opaque_decl_loop(b, i + 1)
    } else {
        err(i, ErrTag::ExpectedObject)
    }
}

/// con-leche: ConLeche/Frontend/Scan/Fast.lean:2278-2345 scanQuotDeclLoop
pub fn scan_quot_decl_loop(b: &[u8], i: usize) -> ScanRes<DeclRec> {
    let mut i = i;
    let mut want_member = true;
    let mut seen: u32 = 0;
    let mut kind: Vec<u32> = Vec::new();
    let mut lps: Vec<u64> = Vec::new();
    let mut nm: u64 = 0;
    let mut ty: u64 = 0;
    loop {
        let (mem, ni, nw) = match next_member(b, i, want_member) {
            Err(er) => return Err(er),
            Ok(p) => p,
        };
        i = ni;
        want_member = nw;
        match mem {
            Member::Close => {
                if want_member && seen != 0 {
                    return err(i, ErrTag::ExpectedKey);
                }
                if seen & 15 != 15 {
                    return err(i, ErrTag::MissingKey);
                }
                return Ok((
                    DeclRec::Quot(
                        CVRec {
                            name: nm,
                            level_params: lps,
                            ty,
                        },
                        kind,
                    ),
                    i + 1,
                ));
            }
            Member::Key(k, ks, v) => match k {
                Key::KKind => {
                    if dup(seen, 1) {
                        return err(ks, ErrTag::DuplicateKey);
                    }
                    let (x, e) = match scan_string(b, v) {
                        Err(er) => return Err(er),
                        Ok(p) => p,
                    };
                    if !prog(ks, e) {
                        return err(ks, ErrTag::NoProgress);
                    }
                    kind = x;
                    seen |= 1;
                    i = e;
                    want_member = false;
                }
                Key::KLevelParams => {
                    if dup(seen, 2) {
                        return err(ks, ErrTag::DuplicateKey);
                    }
                    let (x, e) = match scan_nat_list(b, v) {
                        Err(er) => return Err(er),
                        Ok(p) => p,
                    };
                    if !prog(ks, e) {
                        return err(ks, ErrTag::NoProgress);
                    }
                    lps = x;
                    seen |= 2;
                    i = e;
                    want_member = false;
                }
                Key::KName => {
                    if dup(seen, 4) {
                        return err(ks, ErrTag::DuplicateKey);
                    }
                    let (x, e) = match slot_nat(b, ks, v) {
                        Err(er) => return Err(er),
                        Ok(p) => p,
                    };
                    nm = x;
                    seen |= 4;
                    i = e;
                    want_member = false;
                }
                Key::KType => {
                    if dup(seen, 8) {
                        return err(ks, ErrTag::DuplicateKey);
                    }
                    let (x, e) = match slot_nat(b, ks, v) {
                        Err(er) => return Err(er),
                        Ok(p) => p,
                    };
                    ty = x;
                    seen |= 8;
                    i = e;
                    want_member = false;
                }
                _ => return err(ks, ErrTag::UnknownKey),
            },
        }
    }
}

/// con-leche: ConLeche/Frontend/Scan/Fast.lean:2347-2351 scanQuotDecl
/// con-leche: ConLeche/Frontend/Scan/Naive.lean:617-618 naiveQuotDecl
/// A `quot` record.
pub fn scan_quot_decl(b: &[u8], i: usize) -> ScanRes<DeclRec> {
    if byte_at(b, i) == 123 {
        scan_quot_decl_loop(b, i + 1)
    } else {
        err(i, ErrTag::ExpectedObject)
    }
}

/// con-leche: ConLeche/Frontend/Scan/Fast.lean:2353-2430 scanIndDeclLoop
pub fn scan_ind_decl_loop(b: &[u8], i: usize) -> ScanRes<DeclRec> {
    let mut i = i;
    let mut want_member = true;
    let mut seen: u32 = 0;
    let mut ctors: Vec<IndCtorRec> = Vec::new();
    let mut recs: Vec<IndRecRec> = Vec::new();
    let mut types: Vec<IndTypeRec> = Vec::new();
    loop {
        let (mem, ni, nw) = match next_member(b, i, want_member) {
            Err(er) => return Err(er),
            Ok(p) => p,
        };
        i = ni;
        want_member = nw;
        match mem {
            Member::Close => {
                if want_member && seen != 0 {
                    return err(i, ErrTag::ExpectedKey);
                }
                if seen & 26 != 26 {
                    return err(i, ErrTag::MissingKey);
                }
                return Ok((DeclRec::Ind(types, ctors, recs), i + 1));
            }
            Member::Key(k, ks, v) => match k {
                Key::KAll => {
                    if dup(seen, 1) {
                        return err(ks, ErrTag::DuplicateKey);
                    }
                    let (_x, e) = match scan_nat_list(b, v) {
                        Err(er) => return Err(er),
                        Ok(p) => p,
                    };
                    if !prog(ks, e) {
                        return err(ks, ErrTag::NoProgress);
                    }
                    seen |= 1;
                    i = e;
                    want_member = false;
                }
                Key::KCtors => {
                    if dup(seen, 2) {
                        return err(ks, ErrTag::DuplicateKey);
                    }
                    let (x, e) = match scan_ind_ctors(b, v) {
                        Err(er) => return Err(er),
                        Ok(p) => p,
                    };
                    if !prog(ks, e) {
                        return err(ks, ErrTag::NoProgress);
                    }
                    ctors = x;
                    seen |= 2;
                    i = e;
                    want_member = false;
                }
                Key::KIsUnsafe => {
                    if dup(seen, 4) {
                        return err(ks, ErrTag::DuplicateKey);
                    }
                    let (_x, e) = match scan_bool(b, v) {
                        Err(er) => return Err(er),
                        Ok(p) => p,
                    };
                    if !prog(ks, e) {
                        return err(ks, ErrTag::NoProgress);
                    }
                    seen |= 4;
                    i = e;
                    want_member = false;
                }
                Key::KRecs => {
                    if dup(seen, 8) {
                        return err(ks, ErrTag::DuplicateKey);
                    }
                    let (x, e) = match scan_ind_recs(b, v) {
                        Err(er) => return Err(er),
                        Ok(p) => p,
                    };
                    if !prog(ks, e) {
                        return err(ks, ErrTag::NoProgress);
                    }
                    recs = x;
                    seen |= 8;
                    i = e;
                    want_member = false;
                }
                Key::KTypes => {
                    if dup(seen, 16) {
                        return err(ks, ErrTag::DuplicateKey);
                    }
                    let (x, e) = match scan_ind_types(b, v) {
                        Err(er) => return Err(er),
                        Ok(p) => p,
                    };
                    if !prog(ks, e) {
                        return err(ks, ErrTag::NoProgress);
                    }
                    types = x;
                    seen |= 16;
                    i = e;
                    want_member = false;
                }
                _ => return err(ks, ErrTag::UnknownKey),
            },
        }
    }
}

/// con-leche: ConLeche/Frontend/Scan/Fast.lean:2432-2436 scanIndDecl
/// con-leche: ConLeche/Frontend/Scan/Naive.lean:630-631 naiveIndDecl
/// An `inductive` record: three arrays of member records.
pub fn scan_ind_decl(b: &[u8], i: usize) -> ScanRes<DeclRec> {
    if byte_at(b, i) == 123 {
        scan_ind_decl_loop(b, i + 1)
    } else {
        err(i, ErrTag::ExpectedObject)
    }
}

// ---------------------------------------------------------------------------
// The line
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Frontend/Scan/Fast.lean:2449-2456 LinePayload
/// A line's payload, before it is matched with its index key.  A line carries
/// at most one index key (`in`/`il`/`ie`) and exactly one payload key; the
/// payload keys of the three table kinds are disjoint, so the payload is read
/// before it is known which table it belongs to and the two are matched at the
/// closing brace.
pub enum LinePayload {
    Absent,
    Name(NameRec),
    Level(LevelRec),
    Expr(ExprRec),
    Decl(DeclRec),
    Header,
}

/// con-leche: ConLeche/Frontend/Scan/Fast.lean:2458-2460 LinePayload.isAbsent
pub fn line_payload_is_absent(p: &LinePayload) -> bool {
    match p {
        LinePayload::Absent => true,
        _ => false,
    }
}

/// con-leche: ConLeche/Frontend/Scan/Fast.lean:2462-2609 scanLineLoop
/// con-leche: ConLeche/Frontend/Scan/Naive.lean:645-784 naiveLineLoop
/// con-leche: ConLeche/Frontend/Scan/Naive.lean:639-643 IdxKey
/// The members of one line.  `idx_kind` is `0` for none, `1` for `in`, `2` for
/// `il`, `3` for `ie` (`Naive.lean` spells the same thing as an `IdxKey`
/// enumeration).  The closing brace's match of payload against index key is a
/// nested `match` where con-leche matches a pair, so that the extraction sees
/// one scrutinee per level.
pub fn scan_line_loop(b: &[u8], i: usize) -> ScanRes<LineRec> {
    let mut i = i;
    let mut want_member = true;
    let mut idx_kind: u8 = 0;
    let mut idx: u64 = 0;
    let mut pl = LinePayload::Absent;
    loop {
        let (mem, ni, nw) = match next_member(b, i, want_member) {
            Err(er) => return Err(er),
            Ok(p) => p,
        };
        i = ni;
        want_member = nw;
        match mem {
            Member::Close => {
                if want_member && (idx_kind != 0 || !line_payload_is_absent(&pl)) {
                    return err(i, ErrTag::ExpectedKey);
                }
                return match pl {
                    LinePayload::Name(r) => {
                        if idx_kind == 1 {
                            Ok((LineRec::Name(idx, r), i + 1))
                        } else {
                            err(i, ErrTag::MixedKeys)
                        }
                    }
                    LinePayload::Level(r) => {
                        if idx_kind == 2 {
                            Ok((LineRec::Level(idx, r), i + 1))
                        } else {
                            err(i, ErrTag::MixedKeys)
                        }
                    }
                    LinePayload::Expr(r) => {
                        if idx_kind == 3 {
                            Ok((LineRec::Expr(idx, r), i + 1))
                        } else {
                            err(i, ErrTag::MixedKeys)
                        }
                    }
                    LinePayload::Decl(d) => {
                        if idx_kind == 0 {
                            Ok((LineRec::Decl(d), i + 1))
                        } else {
                            err(i, ErrTag::MixedKeys)
                        }
                    }
                    LinePayload::Header => {
                        if idx_kind == 0 {
                            Ok((LineRec::Header, i + 1))
                        } else {
                            err(i, ErrTag::MixedKeys)
                        }
                    }
                    LinePayload::Absent => err(i, ErrTag::MissingKey),
                };
            }
            Member::Key(k, ks, v) => match k {
                Key::KIn | Key::KIl | Key::KIe => {
                    if idx_kind != 0 {
                        return err(ks, ErrTag::DuplicateKey);
                    }
                    let (n, e) = match slot_nat(b, ks, v) {
                        Err(er) => return Err(er),
                        Ok(p) => p,
                    };
                    idx_kind = match k {
                        Key::KIn => 1,
                        Key::KIl => 2,
                        _ => 3,
                    };
                    idx = n;
                    i = e;
                    want_member = false;
                }
                Key::KBvar | Key::KSort | Key::KSucc | Key::KParam => {
                    if !line_payload_is_absent(&pl) {
                        return err(ks, ErrTag::DuplicateKey);
                    }
                    let (n, e) = match slot_nat(b, ks, v) {
                        Err(er) => return Err(er),
                        Ok(p) => p,
                    };
                    pl = match k {
                        Key::KBvar => LinePayload::Expr(ExprRec::Bvar(n)),
                        Key::KSort => LinePayload::Expr(ExprRec::Sort(n)),
                        Key::KSucc => LinePayload::Level(LevelRec::Succ(n)),
                        _ => LinePayload::Level(LevelRec::Param(n)),
                    };
                    i = e;
                    want_member = false;
                }
                Key::KMax | Key::KImax => {
                    if !line_payload_is_absent(&pl) {
                        return err(ks, ErrTag::DuplicateKey);
                    }
                    let (us, e) = match scan_nat_list(b, v) {
                        Err(er) => return Err(er),
                        Ok(p) => p,
                    };
                    if us.len() != 2 {
                        return err(v, ErrTag::ExpectedList);
                    }
                    if !prog(ks, e) {
                        return err(ks, ErrTag::NoProgress);
                    }
                    pl = if key_beq(&k, &Key::KMax) {
                        LinePayload::Level(LevelRec::Max(us[0], us[1]))
                    } else {
                        LinePayload::Level(LevelRec::Imax(us[0], us[1]))
                    };
                    i = e;
                    want_member = false;
                }
                Key::KStr | Key::KNum => {
                    if !line_payload_is_absent(&pl) {
                        return err(ks, ErrTag::DuplicateKey);
                    }
                    let (r, e) = if key_beq(&k, &Key::KStr) {
                        match scan_str_name(b, v) {
                            Err(er) => return Err(er),
                            Ok(p) => p,
                        }
                    } else {
                        match scan_num_name(b, v) {
                            Err(er) => return Err(er),
                            Ok(p) => p,
                        }
                    };
                    if !prog(ks, e) {
                        return err(ks, ErrTag::NoProgress);
                    }
                    pl = LinePayload::Name(r);
                    i = e;
                    want_member = false;
                }
                Key::KApp | Key::KLam | Key::KForallE | Key::KLetE | Key::KConst | Key::KProj => {
                    if !line_payload_is_absent(&pl) {
                        return err(ks, ErrTag::DuplicateKey);
                    }
                    let (r, e) = match k {
                        Key::KApp => match scan_app_expr(b, v) {
                            Err(er) => return Err(er),
                            Ok(p) => p,
                        },
                        Key::KLam => match scan_lam_expr(b, v) {
                            Err(er) => return Err(er),
                            Ok(p) => p,
                        },
                        Key::KForallE => match scan_forall_expr(b, v) {
                            Err(er) => return Err(er),
                            Ok(p) => p,
                        },
                        Key::KLetE => match scan_let_expr(b, v) {
                            Err(er) => return Err(er),
                            Ok(p) => p,
                        },
                        Key::KConst => match scan_const_expr(b, v) {
                            Err(er) => return Err(er),
                            Ok(p) => p,
                        },
                        _ => match scan_proj_expr(b, v) {
                            Err(er) => return Err(er),
                            Ok(p) => p,
                        },
                    };
                    if !prog(ks, e) {
                        return err(ks, ErrTag::NoProgress);
                    }
                    pl = LinePayload::Expr(r);
                    i = e;
                    want_member = false;
                }
                Key::KNatVal => {
                    if !line_payload_is_absent(&pl) {
                        return err(ks, ErrTag::DuplicateKey);
                    }
                    let (n, e) = match scan_quoted_nat(b, v) {
                        Err(er) => return Err(er),
                        Ok(p) => p,
                    };
                    if !prog(ks, e) {
                        return err(ks, ErrTag::NoProgress);
                    }
                    pl = LinePayload::Expr(ExprRec::NatVal(n));
                    i = e;
                    want_member = false;
                }
                Key::KStrVal => {
                    if !line_payload_is_absent(&pl) {
                        return err(ks, ErrTag::DuplicateKey);
                    }
                    let (s, e) = match scan_string(b, v) {
                        Err(er) => return Err(er),
                        Ok(p) => p,
                    };
                    if !prog(ks, e) {
                        return err(ks, ErrTag::NoProgress);
                    }
                    pl = LinePayload::Expr(ExprRec::StrVal(s));
                    i = e;
                    want_member = false;
                }
                Key::KAxiom
                | Key::KDef
                | Key::KThm
                | Key::KOpaque
                | Key::KQuot
                | Key::KInductive => {
                    if !line_payload_is_absent(&pl) {
                        return err(ks, ErrTag::DuplicateKey);
                    }
                    let (d, e) = match k {
                        Key::KAxiom => match scan_axiom_decl(b, v) {
                            Err(er) => return Err(er),
                            Ok(p) => p,
                        },
                        Key::KDef => match scan_def_decl(b, v) {
                            Err(er) => return Err(er),
                            Ok(p) => p,
                        },
                        Key::KThm => match scan_thm_decl(b, v) {
                            Err(er) => return Err(er),
                            Ok(p) => p,
                        },
                        Key::KOpaque => match scan_opaque_decl(b, v) {
                            Err(er) => return Err(er),
                            Ok(p) => p,
                        },
                        Key::KQuot => match scan_quot_decl(b, v) {
                            Err(er) => return Err(er),
                            Ok(p) => p,
                        },
                        _ => match scan_ind_decl(b, v) {
                            Err(er) => return Err(er),
                            Ok(p) => p,
                        },
                    };
                    if !prog(ks, e) {
                        return err(ks, ErrTag::NoProgress);
                    }
                    pl = LinePayload::Decl(d);
                    i = e;
                    want_member = false;
                }
                Key::KMeta => {
                    if !line_payload_is_absent(&pl) {
                        return err(ks, ErrTag::DuplicateKey);
                    }
                    if byte_at(b, v) != 123 {
                        return err(v, ErrTag::ExpectedObject);
                    }
                    let e = skip_braced(b, v + 1, 0);
                    if e == 0 {
                        return err(v, ErrTag::ExpectedObject);
                    }
                    if !prog(ks, e) {
                        return err(ks, ErrTag::NoProgress);
                    }
                    pl = LinePayload::Header;
                    i = e;
                    want_member = false;
                }
                _ => return err(ks, ErrTag::UnknownKey),
            },
        }
    }
}

/// con-leche: ConLeche/Frontend/Scan/Fast.lean:2611-2634 scanLineFwd
/// con-leche: ConLeche/Frontend/Scan/Naive.lean:786-803 naiveLine
/// One line of the stream from `i`: the record, and **the position after its
/// newline** — or `0` when the buffer ran out before a newline did, which
/// tells the driver that these bytes are an incomplete tail to carry into the
/// next chunk rather than a line (a continue position is never `0`: it is at
/// least one past the newline).  A line of whitespace is `Blank`; anything
/// between the record's closing brace and the newline is an error.
pub fn scan_line_fwd(b: &[u8], i: usize) -> ScanRes<LineRec> {
    let s = skip_ws(b, i);
    if byte_at(b, s) == 10 {
        return Ok((LineRec::Blank, s + 1));
    }
    if b.len() <= s {
        return Ok((LineRec::Blank, 0));
    }
    if byte_at(b, s) != 123 {
        return err(s, ErrTag::ExpectedObject);
    }
    let (r, j) = match scan_line_loop(b, s + 1) {
        Err(er) => return Err(er),
        Ok(p) => p,
    };
    let p = skip_ws(b, j);
    if byte_at(b, p) == 10 {
        Ok((r, p + 1))
    } else if b.len() <= p {
        Ok((r, 0))
    } else {
        err(p, ErrTag::Trailing)
    }
}

/// con-leche: ConLeche/Frontend/Scan/Fast.lean:2636-2645 newlineFrom
/// Is there a newline at or after `i`?  Asked only when a line failed to
/// scan, to tell a malformed record from one a chunk boundary cut in half.
pub fn newline_from(b: &[u8], i: usize) -> bool {
    let mut k = i;
    while k < b.len() {
        if b[k] == 10 {
            return true;
        }
        k += 1;
    }
    false
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::frontend::scan_types::{err_tag_beq, scan_err_render};

    fn s(v: &[u32]) -> String {
        v.iter().filter_map(|c| char::from_u32(*c)).collect()
    }

    fn one(line: &str) -> LineRec {
        let b = line.as_bytes();
        match scan_line_fwd(b, 0) {
            Ok((r, _)) => r,
            Err(e) => panic!("{}: {}", line, s(&scan_err_render(&e))),
        }
    }

    fn bad(line: &str) -> ErrTag {
        let b = line.as_bytes();
        match scan_line_fwd(b, 0) {
            Ok(_) => panic!("{}: expected a failure", line),
            Err(e) => e.what,
        }
    }

    fn is_tag(line: &str, t: ErrTag) {
        let got = bad(line);
        assert!(
            err_tag_beq(&got, &t),
            "{}: {}, wanted {}",
            line,
            s(&crate::frontend::scan_types::err_tag_describe(&got)),
            s(&crate::frontend::scan_types::err_tag_describe(&t))
        );
    }

    /// The key alphabet: every key of the dialect classifies, and a key one
    /// byte off does not (the `"i"`/`"ie"` confusion `keyAt`'s
    /// first-byte-and-length switch exists to rule out).
    #[test]
    fn keys_classify() {
        for (t, k) in [
            ("\"i\"", Key::KI),
            ("\"ie\"", Key::KIe),
            ("\"in\"", Key::KIn),
            ("\"il\"", Key::KIl),
            ("\"isRec\"", Key::KIsRec),
            ("\"isReflexive\"", Key::KIsReflexive),
            ("\"numMotives\"", Key::KNumMotives),
            ("\"levelParams\"", Key::KLevelParams),
            ("\"binderInfo\"", Key::KBinderInfo),
            ("\"iex\"", Key::KUnknown),
            ("\"\"", Key::KUnknown),
        ] {
            let b = t.as_bytes();
            let ke = key_end(b, 1);
            assert!(key_beq(&key_at(b, 0, ke - 1), &k), "{}", t);
        }
    }

    /// Every key of the alphabet round-trips through `key_at`, and no key is
    /// classified as another's (the whole table, not a sample).
    #[test]
    fn every_key_of_the_alphabet_classifies() {
        let spellings = [
            "all",
            "app",
            "arg",
            "axiom",
            "binderInfo",
            "body",
            "bvar",
            "cidx",
            "const",
            "ctor",
            "ctors",
            "def",
            "fn",
            "forallE",
            "hints",
            "i",
            "idx",
            "ie",
            "il",
            "imax",
            "in",
            "induct",
            "inductive",
            "isRec",
            "isReflexive",
            "isUnsafe",
            "k",
            "kind",
            "lam",
            "letE",
            "levelParams",
            "max",
            "meta",
            "name",
            "natVal",
            "nfields",
            "nondep",
            "num",
            "numFields",
            "numIndices",
            "numMinors",
            "numMotives",
            "numNested",
            "numParams",
            "opaque",
            "param",
            "pre",
            "proj",
            "pw",
            "quot",
            "recs",
            "regular",
            "rhs",
            "rules",
            "safety",
            "sort",
            "str",
            "strVal",
            "struct",
            "succ",
            "thm",
            "type",
            "typeName",
            "types",
            "us",
            "value",
        ];
        let mut codes: Vec<u64> = Vec::new();
        for sp in spellings.iter() {
            let line = format!("\"{}\"", sp);
            let b = line.as_bytes();
            let ke = key_end(b, 1);
            let k = key_at(b, 0, ke - 1);
            assert!(!key_beq(&k, &Key::KUnknown), "{} is unknown", sp);
            let c = crate::frontend::scan_types::key_code(&k);
            assert!(!codes.contains(&c), "{} collides", sp);
            codes.push(c);
            // one byte longer or shorter is not this key
            let longer = format!("\"{}x\"", sp);
            let lb = longer.as_bytes();
            let lke = key_end(lb, 1);
            assert!(!key_beq(&key_at(lb, 0, lke - 1), &k), "{}x classifies", sp);
        }
        assert_eq!(codes.len(), 66);
    }

    /// The three table kinds and a declaration, in the raw exporter's key
    /// order (payload first) and in reverse — the recogniser is
    /// order-insensitive.
    #[test]
    fn lines_scan_in_any_key_order() {
        assert!(matches!(
            one("{\"str\":{\"pre\":0,\"str\":\"Nat\"},\"in\":1}\n"),
            LineRec::Name(1, NameRec::Str(0, _))
        ));
        assert!(matches!(
            one("{\"in\":1,\"str\":{\"str\":\"Nat\",\"pre\":0}}\n"),
            LineRec::Name(1, NameRec::Str(0, _))
        ));
        assert!(matches!(
            one("{\"num\":{\"i\":7,\"pre\":2},\"in\":3}\n"),
            LineRec::Name(3, NameRec::Num(2, 7))
        ));
        assert!(matches!(
            one("{\"succ\":4,\"il\":5}\n"),
            LineRec::Level(5, LevelRec::Succ(4))
        ));
        assert!(matches!(
            one("{\"imax\":[1,2],\"il\":6}\n"),
            LineRec::Level(6, LevelRec::Imax(1, 2))
        ));
        assert!(matches!(
            one("{\"app\":{\"arg\":1,\"fn\":7},\"ie\":8}\n"),
            LineRec::Expr(8, ExprRec::App(7, 1))
        ));
        assert!(matches!(
            one("{\"ie\":9,\"natVal\":\"123456789012345678901234\"}\n"),
            LineRec::Expr(9, ExprRec::NatVal(_))
        ));
        assert!(matches!(
            one("{\"meta\":{\"exporter\":{\"name\":\"lean4export\"}}}\n"),
            LineRec::Header
        ));
        assert!(matches!(one("   \n"), LineRec::Blank));
    }

    /// A `natVal` literal keeps its digit BYTES (task #84's change to
    /// `scan_types`: the one unbounded number of the dialect).
    #[test]
    fn nat_val_keeps_its_digits() {
        match one("{\"ie\":9,\"natVal\":\"123456789012345678901234\"}\n") {
            LineRec::Expr(_, ExprRec::NatVal(d)) => {
                assert_eq!(d, b"123456789012345678901234".to_vec());
            }
            _ => panic!("not a natVal"),
        }
    }

    /// A binder line: `binderInfo` and `name` are required and dropped, `pw`
    /// is optional and defaults to `never`.
    #[test]
    fn binder_lines() {
        assert!(matches!(
            one("{\"forallE\":{\"binderInfo\":\"instImplicit\",\"body\":2,\"name\":3,\"type\":4},\"ie\":5}\n"),
            LineRec::Expr(5, ExprRec::ForallE(4, 2, PwRec::Never))
        ));
        assert!(matches!(
            one("{\"lam\":{\"binderInfo\":\"default\",\"body\":2,\"name\":0,\"type\":4,\"pw\":[1,2]},\"ie\":5}\n"),
            LineRec::Expr(5, ExprRec::Lam(4, 2, PwRec::IfAllZero(_)))
        ));
        is_tag(
            "{\"lam\":{\"binderInfo\":\"weird\",\"body\":2,\"name\":0,\"type\":4},\"ie\":5}\n",
            ErrTag::BadBinderInfo,
        );
        is_tag(
            "{\"lam\":{\"body\":2,\"name\":0,\"type\":4},\"ie\":5}\n",
            ErrTag::MissingKey,
        );
    }

    /// Every way a line can be malformed that the dialect names.
    #[test]
    fn malformed_lines() {
        is_tag("[1,2]\n", ErrTag::ExpectedObject);
        is_tag("{\"nope\":1}\n", ErrTag::UnknownKey);
        is_tag("{\"in\":1,\"in\":2}\n", ErrTag::DuplicateKey);
        is_tag("{\"in\":1}\n", ErrTag::MissingKey);
        is_tag("{\"in\":1,\"succ\":2}\n", ErrTag::MixedKeys);
        is_tag("{\"in\" 1}\n", ErrTag::ExpectedColon);
        is_tag("{\"in\":1,}\n", ErrTag::ExpectedKey);
        is_tag("{\"in\":1 \"il\":2}\n", ErrTag::ExpectedComma);
        is_tag("{\"ie\":1,\"sort\":x}\n", ErrTag::ExpectedNat);
        is_tag("{\"ie\":06,\"sort\":1}\n", ErrTag::ExpectedNat);
        is_tag("{\"ie\":1,\"us\":[1,]}\n", ErrTag::UnknownKey);
        is_tag(
            "{\"ie\":1,\"const\":{\"name\":1,\"us\":[1,]}}\n",
            ErrTag::ExpectedList,
        );
        is_tag("{\"ie\":1,\"strVal\":\"\\q\"}\n", ErrTag::BadEscape);
        is_tag("{\"ie\":1,\"sort\":1} x\n", ErrTag::Trailing);
        // §3.3's machine-word split: a stream index too large is a failure,
        // never a truncation.  (A `natVal` literal of the same size is fine.)
        is_tag(
            "{\"ie\":99999999999999999999,\"sort\":1}\n",
            ErrTag::IndexOverflow,
        );
    }

    /// The string codec: the escapes the dialect has, the surrogate pair rule
    /// and the lone-surrogate fallback to U+FFFD (`Lean.Json`'s own).
    #[test]
    fn string_escapes() {
        let got = |t: &str| -> Vec<u32> {
            let line = format!("{{\"ie\":1,\"strVal\":\"{}\"}}\n", t);
            match one(&line) {
                LineRec::Expr(_, ExprRec::StrVal(v)) => v,
                _ => panic!("not a strVal"),
            }
        };
        assert_eq!(got("a\\nb"), vec!['a' as u32, 10, 'b' as u32]);
        assert_eq!(
            got("\\\\\\\"\\/\\b\\f\\r\\t"),
            vec![92, 34, 47, 8, 12, 13, 9]
        );
        assert_eq!(got("\\u0041"), vec![0x41]);
        assert_eq!(got("\\ud83d\\ude00"), vec![0x1F600]);
        assert_eq!(got("\\ud83d"), vec![REPLACEMENT_CHAR]);
        assert_eq!(got("\\ude00"), vec![REPLACEMENT_CHAR]);
        // a literal multi-byte sequence beside an escape: con-leche pushes
        // raw bytes and validates the whole buffer at the end, so this must
        // decode as one code point
        assert_eq!(got("é\\n"), vec![0xE9, 10]);
        // and without any escape at all, the slice path
        assert_eq!(got("é"), vec![0xE9]);
        // three- and four-byte literals, on both paths
        assert_eq!(got("→"), vec![0x2192]);
        assert_eq!(got("→\\n"), vec![0x2192, 10]);
        assert_eq!(got("😀"), vec![0x1F600]);
    }

    /// The port's own UTF-8 decoder is Rust's own on every input the scanner
    /// can hand it, valid or not (deviation 5 of the module note).
    #[test]
    fn utf8_decode_agrees_with_the_toolchain() {
        let cases: Vec<Vec<u8>> = vec![
            vec![],
            b"plain ascii".to_vec(),
            vec![0xC3, 0xA9],             // é
            vec![0xE2, 0x86, 0x92],       // →
            vec![0xF0, 0x9F, 0x98, 0x80], // 😀
            vec![0x80],                   // a bare continuation byte
            vec![0xC0, 0x80],             // an overlong NUL
            vec![0xC1, 0xBF],             // an overlong DEL
            vec![0xE0, 0x80, 0x80],       // an overlong three-byte form
            vec![0xED, 0xA0, 0x80],       // a surrogate
            vec![0xF4, 0x90, 0x80, 0x80], // above U+10FFFF
            vec![0xF5, 0x80, 0x80, 0x80], // an impossible lead
            vec![0xC3],                   // a truncated two-byte form
            vec![0xE2, 0x86],             // a truncated three-byte form
            vec![0xF0, 0x9F, 0x98],       // a truncated four-byte form
            vec![0xE2, 0x28, 0xA1],       // a bad continuation
            vec![0x41, 0xC3, 0xA9, 0x42],
        ];
        for c in cases.iter() {
            let want: Option<Vec<u32>> = match std::str::from_utf8(c) {
                Ok(t) => Some(t.chars().map(|ch| ch as u32).collect()),
                Err(_) => None,
            };
            assert_eq!(utf8_decode(c, 0, c.len()), want, "{:?}", c);
        }
    }

    /// `utf8_of` is `char::encode_utf8` on every scalar value.
    #[test]
    fn utf8_of_is_the_encoder() {
        let probes: Vec<u32> = vec![
            0, 1, 0x7F, 0x80, 0x7FF, 0x800, 0xFFF, 0xD7FF, 0xE000, 0xFFFD, 0xFFFF, 0x10000,
            0x1F600, 0x10FFFF,
        ];
        for v in probes.iter() {
            let mut buf = [0u8; 4];
            let want = char::from_u32(*v).unwrap().encode_utf8(&mut buf).as_bytes();
            assert_eq!(utf8_of(Vec::new(), *v), want.to_vec(), "{:x}", v);
        }
    }

    /// An inductive record, its three member arrays and their optional
    /// redundant fields.
    #[test]
    fn inductive_record() {
        let l = concat!(
            "{\"inductive\":{\"ctors\":[{\"isUnsafe\":false,\"levelParams\":[],",
            "\"name\":2,\"numFields\":1,\"numParams\":0,\"type\":3,\"cidx\":0,",
            "\"induct\":1}],\"recs\":[{\"isUnsafe\":false,\"k\":false,",
            "\"levelParams\":[],\"name\":4,\"numIndices\":0,\"numMinors\":1,",
            "\"numMotives\":1,\"numParams\":0,\"rules\":[{\"ctor\":2,",
            "\"nfields\":1,\"rhs\":5}],\"type\":6}],\"types\":[{\"ctors\":[2],",
            "\"isRec\":false,\"isReflexive\":false,\"isUnsafe\":false,",
            "\"levelParams\":[],\"name\":1,\"numIndices\":0,\"numNested\":0,",
            "\"numParams\":0,\"type\":7}]}}\n"
        );
        match one(l) {
            LineRec::Decl(DeclRec::Ind(tys, cts, rcs)) => {
                assert_eq!(tys.len(), 1);
                assert_eq!(cts.len(), 1);
                assert_eq!(rcs.len(), 1);
                assert_eq!(cts[0].cidx, Some(0));
                assert_eq!(cts[0].induct, Some(1));
                assert_eq!(rcs[0].rules.len(), 1);
                assert_eq!(rcs[0].rules[0].rhs, 5);
            }
            _ => panic!("not an inductive record"),
        }
    }

    /// `def` hints: the three spellings, and the `regular 0` default.
    #[test]
    fn def_hints() {
        let with = |h: &str| -> HintsRec {
            let line = format!(
                "{{\"def\":{{\"levelParams\":[],\"name\":1,\"safety\":\"safe\",\"type\":2,\"value\":3{}}}}}\n",
                h
            );
            match one(&line) {
                LineRec::Decl(DeclRec::Defn(_, _, h, sf)) => {
                    assert_eq!(s(&sf), "safe");
                    h
                }
                _ => panic!("not a def record"),
            }
        };
        assert!(matches!(with(""), HintsRec::Regular(0)));
        assert!(matches!(with(",\"hints\":\"abbrev\""), HintsRec::Abbrev));
        assert!(matches!(with(",\"hints\":\"opaque\""), HintsRec::Opaque));
        assert!(matches!(
            with(",\"hints\":{\"regular\":5}"),
            HintsRec::Regular(5)
        ));
    }

    /// A `quot` record keeps its `kind` spelling as code points.
    #[test]
    fn quot_kind_is_code_points() {
        let l = "{\"quot\":{\"kind\":\"ctor\",\"levelParams\":[],\"name\":1,\"type\":2}}\n";
        match one(l) {
            LineRec::Decl(DeclRec::Quot(cv, kind)) => {
                assert_eq!(cv.name, 1);
                assert_eq!(s(&kind), "ctor");
            }
            _ => panic!("not a quot record"),
        }
    }

    /// An incomplete tail is `0`, not an error: that is what tells
    /// `feed_chunk` to carry the bytes into the next chunk.
    #[test]
    fn incomplete_tail_is_position_zero() {
        let b = b"{\"in\":1,\"str\":{\"pre\":0,\"str\":\"Na";
        assert!(scan_line_fwd(b, 0).is_err());
        assert!(!newline_from(b, 0));
        let b2 = b"{\"il\":1,\"succ\":0}";
        match scan_line_fwd(b2, 0) {
            Ok((_, j)) => assert_eq!(j, 0),
            Err(e) => panic!("{}", s(&scan_err_render(&e))),
        }
    }

    /// **A line ends at the first newline, always** (con-leche task #290).
    /// Two scanners used to step over one, and each tightening only ever
    /// refuses more: a raw control byte after a backslash inside a string,
    /// and a newline inside the `meta` header's braced value.
    #[test]
    fn no_scanner_steps_over_a_newline() {
        // `\` + newline is no escape the format has, so the string does not
        // close and the bytes after the newline are not swallowed
        let body = b"a\\\nb\"";
        assert_eq!(str_close(body, 0), 0);
        // a string that closes on the same line still does
        let ok = b"a\\nb\"";
        assert_eq!(str_close(ok, 0), 4);
        // the header's braced value stops at a newline rather than
        // swallowing the next line into itself
        let hdr = b"{\"x\":\n{\"in\":1}}\n";
        assert_eq!(skip_braced(hdr, 1, 0), 0);
        is_tag("{\"meta\":{\"x\":\n{\"in\":1}}", ErrTag::ExpectedObject);
    }
}
