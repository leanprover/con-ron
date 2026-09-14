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
//! **Four standing deviations.**
//!
//! 1. **Recursion becomes `loop`.**  Every `scan*Loop` of `Fast.lean` is
//!    tail-recursive because Lean must prove termination from
//!    `b.size - i.toNat`; the Rust is a `while`/`loop` over the same
//!    positions, and the `noProgress` guard — con-leche's "unreachable, and
//!    it is what makes the measure a theorem rather than a comment" — is kept
//!    verbatim, because in Rust it is what makes the loop terminate.
//! 2. **`keyAt` is a slice compare.**  `Fast.lean` classifies a key by its
//!    first byte and its length and then compares the rest with an UNROLLED
//!    chain of byte literals (`lit1`…`lit10`, task #264) because a Lean
//!    string literal in that position is a heap object the code generator
//!    materialises through a `lean_obj_once` cell.  Rust has no such cost:
//!    `key_at` matches the key's byte slice against `b"…"` patterns, which is
//!    `keyOf`/`keyTable` of `Naive.lean` at `Fast.lean`'s speed.  `key_at`
//!    therefore carries the citations of `keyAt` and of all ten `litN`
//!    helpers (§3.7: "several lines are allowed when a Rust item merges …
//!    Lean ones"), and `matchLit` survives only where a *fixed* literal is
//!    matched (`scan_bool`, `scan_binder_info`, `scan_pw`, `scan_hints`).
//! 3. **The slot loop is factored out once** (`next_member`), as
//!    `naiveObjLoop` factors it in the specification, instead of being
//!    written out per object as `Fast.lean` does.  Each `scan_*_loop` is
//!    still its own function with its own `seen` bits and its own required
//!    mask, so it lines up with its Lean twin key for key.
//! 4. **Numbers are `u64`** and a `natVal` literal keeps its digits
//!    (`scan_types`' module note): `readNat`/`readNat64`/`readNatAt` collapse
//!    into one `read_nat_at` that fails with `ErrTag::IndexOverflow` rather
//!    than growing into a bignum, and `scan_quoted_nat` returns the digit
//!    text.

use crate::frontend::scan_types::{
    CVRec, DeclRec, ErrTag, ExprRec, HintsRec, IndCtorRec, IndRecRec, IndTypeRec, Key, LevelRec,
    LineRec, NameRec, PwRec, RuleRec, ScanErr, ScanRes,
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
    c.is_ascii_digit()
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
/// The bytes of `lit` match `b` from `i` on.
pub fn match_lit(b: &[u8], i: usize, lit: &[u8]) -> bool {
    i <= b.len() && b.len() - i >= lit.len() && &b[i..i + lit.len()] == lit
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
/// bytes.  A key outside the dialect is `KUnknown`, which every slot loop
/// rejects.  Deviation 2 of the module note: one slice compare, not the
/// first-byte/length switch plus an unrolled `litN` chain.
pub fn key_at(b: &[u8], i: usize, kl: usize) -> Key {
    let j = i + 1;
    if j > b.len() || b.len() - j < kl {
        return Key::KUnknown;
    }
    match &b[j..j + kl] {
        b"all" => Key::KAll,
        b"app" => Key::KApp,
        b"arg" => Key::KArg,
        b"axiom" => Key::KAxiom,
        b"binderInfo" => Key::KBinderInfo,
        b"body" => Key::KBody,
        b"bvar" => Key::KBvar,
        b"cidx" => Key::KCidx,
        b"const" => Key::KConst,
        b"ctor" => Key::KCtor,
        b"ctors" => Key::KCtors,
        b"def" => Key::KDef,
        b"fn" => Key::KFn,
        b"forallE" => Key::KForallE,
        b"hints" => Key::KHints,
        b"i" => Key::KI,
        b"idx" => Key::KIdx,
        b"ie" => Key::KIe,
        b"il" => Key::KIl,
        b"imax" => Key::KImax,
        b"in" => Key::KIn,
        b"induct" => Key::KInduct,
        b"inductive" => Key::KInductive,
        b"isRec" => Key::KIsRec,
        b"isReflexive" => Key::KIsReflexive,
        b"isUnsafe" => Key::KIsUnsafe,
        b"k" => Key::KK,
        b"kind" => Key::KKind,
        b"lam" => Key::KLam,
        b"letE" => Key::KLetE,
        b"levelParams" => Key::KLevelParams,
        b"max" => Key::KMax,
        b"meta" => Key::KMeta,
        b"name" => Key::KName,
        b"natVal" => Key::KNatVal,
        b"nfields" => Key::KNfields,
        b"nondep" => Key::KNondep,
        b"num" => Key::KNum,
        b"numFields" => Key::KNumFields,
        b"numIndices" => Key::KNumIndices,
        b"numMinors" => Key::KNumMinors,
        b"numMotives" => Key::KNumMotives,
        b"numNested" => Key::KNumNested,
        b"numParams" => Key::KNumParams,
        b"opaque" => Key::KOpaque,
        b"param" => Key::KParam,
        b"pre" => Key::KPre,
        b"proj" => Key::KProj,
        b"pw" => Key::KPw,
        b"quot" => Key::KQuot,
        b"recs" => Key::KRecs,
        b"regular" => Key::KRegular,
        b"rhs" => Key::KRhs,
        b"rules" => Key::KRules,
        b"safety" => Key::KSafety,
        b"sort" => Key::KSort,
        b"str" => Key::KStr,
        b"strVal" => Key::KStrVal,
        b"struct" => Key::KStruct,
        b"succ" => Key::KSucc,
        b"thm" => Key::KThm,
        b"type" => Key::KType,
        b"typeName" => Key::KTypeName,
        b"types" => Key::KTypes,
        b"us" => Key::KUs,
        b"value" => Key::KValue,
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
    if match_lit(b, i, b"true") {
        Ok((true, i + 4))
    } else if match_lit(b, i, b"false") {
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
        match acc
            .checked_mul(10)
            .and_then(|a| a.checked_add((b[k] - 48) as u64))
        {
            Some(a) => acc = a,
            None => {
                return Err(ScanErr {
                    offset: i,
                    what: ErrTag::IndexOverflow,
                })
            }
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
    if c.is_ascii_digit() {
        Some((c - 48) as u32)
    } else if (97..=102).contains(&c) {
        Some((c - 87) as u32)
    } else if (65..=70).contains(&c) {
        Some((c - 55) as u32)
    } else {
        None
    }
}

/// con-leche: ConLeche/Frontend/Scan/Fast.lean:543-549 hex4
/// The value of the four hexadecimal digits at `j`.
pub fn hex4(b: &[u8], j: usize) -> Option<u32> {
    let a = hex_val(byte_at(b, j))?;
    let c = hex_val(byte_at(b, j + 1))?;
    let d = hex_val(byte_at(b, j + 2))?;
    let e = hex_val(byte_at(b, j + 3))?;
    Some((a << 12) | (c << 8) | (d << 4) | e)
}

/// con-leche: ConLeche/Frontend/Scan/Fast.lean:551-557 hex3
/// The value of the three hexadecimal digits at `j` (a surrogate continuation
/// `\uDxxx`, whose leading `d` the caller has matched).
pub fn hex3(b: &[u8], j: usize) -> Option<u32> {
    let a = hex_val(byte_at(b, j))?;
    let c = hex_val(byte_at(b, j + 1))?;
    let d = hex_val(byte_at(b, j + 2))?;
    Some((a << 8) | (c << 4) | d)
}

/// con-leche: ConLeche/Frontend/Scan/Fast.lean:559-560 utf8Of
/// The UTF-8 bytes of a code point, appended to `acc`.  con-leche builds a
/// one-character `String` and takes its UTF-8; `char::encode_utf8` is the
/// same bytes without the intermediate object.
pub fn utf8_of(acc: &mut Vec<u8>, val: u32) {
    let mut buf = [0u8; 4];
    let c = char::from_u32(val).unwrap_or('\0');
    acc.extend_from_slice(c.encode_utf8(&mut buf).as_bytes());
}

/// con-leche: ConLeche/Frontend/Scan/Fast.lean:562-564 replacementChar
/// The Unicode replacement character, which is what a lone surrogate decodes
/// to (the toolchain's own `Lean.Json` reader does the same).
pub const REPLACEMENT_CHAR: u32 = 0xFFFD;

/// con-leche: ConLeche/Frontend/Scan/Fast.lean:566-625 unescape
/// Decode the string body `[j, e)`, resolving escapes.  The no-escape case
/// never comes here (`scan_string` slices instead), so this is the rare path.
/// Bytes accumulate and the whole buffer is UTF-8-validated at the end,
/// exactly as con-leche's `String.fromUTF8? acc` does, so a literal
/// multi-byte sequence passes through byte by byte.
pub fn unescape(b: &[u8], j: usize, e: usize) -> Option<Vec<u32>> {
    let mut acc: Vec<u8> = Vec::new();
    let mut j = j;
    while j < b.len() && j < e {
        let c = b[j];
        if c != 92 {
            acc.push(c);
            j += 1;
            continue;
        }
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
                utf8_of(&mut acc, val);
                j += 2;
            }
            None => {
                if d != 117 {
                    return None;
                }
                let val = hex4(b, j + 2)?;
                let j6 = j + 6;
                if val < 0xD800 || 0xE000 <= val {
                    utf8_of(&mut acc, val);
                    j = j6;
                } else if 0xDC00 <= val {
                    utf8_of(&mut acc, REPLACEMENT_CHAR);
                    j = j6;
                } else {
                    // a high surrogate: the toolchain's reader looks for a
                    // `\uDxxx` continuation and falls back to U+FFFD
                    let cont = byte_at(b, j6) == 92
                        && byte_at(b, j6 + 1) == 117
                        && (byte_at(b, j6 + 2) == 100 || byte_at(b, j6 + 2) == 68);
                    match if cont { hex3(b, j6 + 3) } else { None } {
                        Some(v2) => {
                            if v2 < 0xC00 {
                                utf8_of(&mut acc, REPLACEMENT_CHAR);
                                j = j6;
                            } else {
                                let cv = (((val & 0x3FF) << 10) | (v2 & 0x3FF)) + 0x10000;
                                utf8_of(&mut acc, cv);
                                j = j6 + 6;
                            }
                        }
                        None => {
                            utf8_of(&mut acc, REPLACEMENT_CHAR);
                            j = j6;
                        }
                    }
                }
            }
        }
    }
    match String::from_utf8(acc) {
        Ok(s) => Some(s.chars().map(|c| c as u32).collect()),
        Err(_) => None,
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
        match std::str::from_utf8(&b[i + 1..e]) {
            Ok(s) => Ok((s.chars().map(|c| c as u32).collect(), e + 1)),
            Err(_) => err(i, ErrTag::BadUtf8),
        }
    }
}

/// con-leche: none — `String.fromUTF8?`'s result is a Lean `String`, while the
/// port carries code points (§3.3); the dialect's two `String`-valued fields
/// (`safety`, `kind`) are compared with literals and reported verbatim, so
/// they become Rust `String`s here.
pub fn cps_to_string(s: &[u32]) -> String {
    s.iter()
        .map(|c| char::from_u32(*c).unwrap_or('\u{fffd}'))
        .collect()
}

/// con-leche: ConLeche/Frontend/Scan/Fast.lean:649-655 scanQuotedNat
/// con-leche: ConLeche/Frontend/Scan/Naive.lean:149-157 naiveQuotedNat
/// A quoted decimal (`"natVal":"12"`).  Deviation 4 of the module note: the
/// digits, not their value — this is the dialect's one unbounded number and
/// `export_c` turns it into a `ron::Nat`.
pub fn scan_quoted_nat(b: &[u8], i: usize) -> ScanRes<String> {
    if byte_at(b, i) != 34 {
        return err(i, ErrTag::BadNatVal);
    }
    let e = skip_digits(b, i + 1);
    if e == i + 1 || byte_at(b, e) != 34 {
        return err(i, ErrTag::BadNatVal);
    }
    match std::str::from_utf8(&b[i + 1..e]) {
        Ok(s) => Ok((s.to_string(), e + 1)),
        Err(_) => err(i, ErrTag::BadNatVal),
    }
}

/// con-leche: ConLeche/Frontend/Scan/Fast.lean:657-666 scanBinderInfo
/// con-leche: ConLeche/Frontend/Scan/Naive.lean:159-175 naiveBinderInfo
/// The four `binderInfo` spellings, validated and dropped (task #142): kernel
/// typing erases binder annotations, and an unknown spelling is a malformed
/// record rather than a silently ignored one.  `0` is the failure.
pub fn scan_binder_info(b: &[u8], i: usize) -> usize {
    if byte_at(b, i) != 34 {
        0
    } else if match_lit(b, i + 1, b"default\"") {
        i + 9
    } else if match_lit(b, i + 1, b"implicit\"") {
        i + 10
    } else if match_lit(b, i + 1, b"strictImplicit\"") {
        i + 16
    } else if match_lit(b, i + 1, b"instImplicit\"") {
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
            if want_item && !acc.is_empty() {
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
            acc.push(read_nat_at(b, i, e)?);
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
    if byte_at(b, i) == 91 {
        let (ns, j) = scan_nat_list_loop(b, i + 1)?;
        Ok((PwRec::IfAllZero(ns), j))
    } else if byte_at(b, i) == 34 {
        if match_lit(b, i + 1, b"never\"") {
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
    if byte_at(b, i) == 34 {
        if match_lit(b, i + 1, b"abbrev\"") {
            Ok((HintsRec::Abbrev, i + 8))
        } else if match_lit(b, i + 1, b"opaque\"") {
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
                let n = read_nat_at(b, v, e)?;
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
/// has been seen.  `want_member` is threaded by reference so the caller can
/// read it in that arm, as con-leche reads its `wantMember` parameter there.
pub fn next_member(b: &[u8], i: &mut usize, want_member: &mut bool) -> Result<Member, ScanErr> {
    loop {
        if *i >= b.len() {
            return Err(ScanErr {
                offset: *i,
                what: ErrTag::ExpectedComma,
            });
        }
        let c = b[*i];
        if is_ws(c) {
            *i += 1;
        } else if c == 125 {
            return Ok(Member::Close);
        } else if c == 44 {
            if *want_member {
                return Err(ScanErr {
                    offset: *i,
                    what: ErrTag::ExpectedKey,
                });
            }
            *i += 1;
            *want_member = true;
        } else if c == 34 {
            if !*want_member {
                return Err(ScanErr {
                    offset: *i,
                    what: ErrTag::ExpectedComma,
                });
            }
            let ke = key_end(b, *i + 1);
            if ke == 0 {
                return Err(ScanErr {
                    offset: *i,
                    what: ErrTag::ExpectedKey,
                });
            }
            let v = value_at(b, *i, ke);
            if v == *i {
                return Err(ScanErr {
                    offset: *i,
                    what: ErrTag::ExpectedColon,
                });
            }
            return Ok(Member::Key(key_at(b, *i, ke - (*i + 1)), *i, v));
        } else {
            return Err(ScanErr {
                offset: *i,
                what: ErrTag::ExpectedComma,
            });
        }
    }
}

/// con-leche: none — the duplicate-key test every slot of every `scan*Loop`
/// of `Scan/Fast.lean` opens with (`if (seen &&& bit) != 0 then .err
/// ⟨i.toNat, .duplicateKey⟩`).
pub fn dup(seen: u32, bit: u32, ks: usize) -> Result<(), ScanErr> {
    if seen & bit != 0 {
        Err(ScanErr {
            offset: ks,
            what: ErrTag::DuplicateKey,
        })
    } else {
        Ok(())
    }
}

/// con-leche: none — the `noProgress` guard every slot of every `scan*Loop`
/// of `Scan/Fast.lean` closes with (`if _hj : i < e then … else .err
/// ⟨i.toNat, .noProgress⟩`).  Unreachable — a scanner consumes at least the
/// byte it dispatched on — and it is what makes the Rust loops terminate.
pub fn prog(ks: usize, e: usize) -> Result<(), ScanErr> {
    if ks < e {
        Ok(())
    } else {
        Err(ScanErr {
            offset: ks,
            what: ErrTag::NoProgress,
        })
    }
}

/// con-leche: none — the `numEnd`/`readNatAt`/`noProgress` chain every
/// `Nat`-valued slot of every `scan*Loop` of `Scan/Fast.lean` writes out.
pub fn slot_nat(b: &[u8], ks: usize, v: usize) -> ScanRes<u64> {
    let e = num_end(b, v);
    if e == v {
        return err(v, ErrTag::ExpectedNat);
    }
    prog(ks, e)?;
    Ok((read_nat_at(b, v, e)?, e))
}

/// con-leche: ConLeche/Frontend/Scan/Fast.lean:795-843 scanStrNameLoop
pub fn scan_str_name_loop(b: &[u8], i: usize) -> ScanRes<NameRec> {
    let mut i = i;
    let mut want_member = true;
    let mut seen: u32 = 0;
    let mut pre: u64 = 0;
    let mut s: Vec<u32> = Vec::new();
    loop {
        match next_member(b, &mut i, &mut want_member)? {
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
                    dup(seen, 1, ks)?;
                    let (x, e) = slot_nat(b, ks, v)?;
                    pre = x;
                    seen |= 1;
                    i = e;
                    want_member = false;
                }
                Key::KStr => {
                    dup(seen, 2, ks)?;
                    let (x, e) = scan_string(b, v)?;
                    prog(ks, e)?;
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
        match next_member(b, &mut i, &mut want_member)? {
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
                    dup(seen, 1, ks)?;
                    let (x, e) = slot_nat(b, ks, v)?;
                    n = x;
                    seen |= 1;
                    i = e;
                    want_member = false;
                }
                Key::KPre => {
                    dup(seen, 2, ks)?;
                    let (x, e) = slot_nat(b, ks, v)?;
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
        match next_member(b, &mut i, &mut want_member)? {
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
                    dup(seen, 1, ks)?;
                    let (x, e) = slot_nat(b, ks, v)?;
                    arg = x;
                    seen |= 1;
                    i = e;
                    want_member = false;
                }
                Key::KFn => {
                    dup(seen, 2, ks)?;
                    let (x, e) = slot_nat(b, ks, v)?;
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
        match next_member(b, &mut i, &mut want_member)? {
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
                    dup(seen, 1, ks)?;
                    let e = scan_binder_info(b, v);
                    if e == 0 {
                        return err(v, ErrTag::BadBinderInfo);
                    }
                    prog(ks, e)?;
                    seen |= 1;
                    i = e;
                    want_member = false;
                }
                Key::KBody => {
                    dup(seen, 2, ks)?;
                    let (x, e) = slot_nat(b, ks, v)?;
                    bd = x;
                    seen |= 2;
                    i = e;
                    want_member = false;
                }
                Key::KName => {
                    dup(seen, 4, ks)?;
                    let (_x, e) = slot_nat(b, ks, v)?;
                    seen |= 4;
                    i = e;
                    want_member = false;
                }
                Key::KType => {
                    dup(seen, 8, ks)?;
                    let (x, e) = slot_nat(b, ks, v)?;
                    ty = x;
                    seen |= 8;
                    i = e;
                    want_member = false;
                }
                Key::KPw => {
                    dup(seen, 16, ks)?;
                    let (x, e) = scan_pw(b, v)?;
                    prog(ks, e)?;
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
        match next_member(b, &mut i, &mut want_member)? {
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
                    dup(seen, 1, ks)?;
                    let (x, e) = slot_nat(b, ks, v)?;
                    bd = x;
                    seen |= 1;
                    i = e;
                    want_member = false;
                }
                Key::KName => {
                    dup(seen, 2, ks)?;
                    let (_x, e) = slot_nat(b, ks, v)?;
                    seen |= 2;
                    i = e;
                    want_member = false;
                }
                Key::KNondep => {
                    dup(seen, 4, ks)?;
                    let (_x, e) = scan_bool(b, v)?;
                    prog(ks, e)?;
                    seen |= 4;
                    i = e;
                    want_member = false;
                }
                Key::KType => {
                    dup(seen, 8, ks)?;
                    let (x, e) = slot_nat(b, ks, v)?;
                    ty = x;
                    seen |= 8;
                    i = e;
                    want_member = false;
                }
                Key::KValue => {
                    dup(seen, 16, ks)?;
                    let (x, e) = slot_nat(b, ks, v)?;
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
        match next_member(b, &mut i, &mut want_member)? {
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
                    dup(seen, 1, ks)?;
                    let (x, e) = slot_nat(b, ks, v)?;
                    nm = x;
                    seen |= 1;
                    i = e;
                    want_member = false;
                }
                Key::KUs => {
                    dup(seen, 2, ks)?;
                    let (x, e) = scan_nat_list(b, v)?;
                    prog(ks, e)?;
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
        match next_member(b, &mut i, &mut want_member)? {
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
                    dup(seen, 1, ks)?;
                    let (x, e) = slot_nat(b, ks, v)?;
                    ix = x;
                    seen |= 1;
                    i = e;
                    want_member = false;
                }
                Key::KStruct => {
                    dup(seen, 2, ks)?;
                    let (x, e) = slot_nat(b, ks, v)?;
                    st = x;
                    seen |= 2;
                    i = e;
                    want_member = false;
                }
                Key::KTypeName => {
                    dup(seen, 4, ks)?;
                    let (x, e) = slot_nat(b, ks, v)?;
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
        match next_member(b, &mut i, &mut want_member)? {
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
                    dup(seen, 1, ks)?;
                    let (x, e) = slot_nat(b, ks, v)?;
                    ct = x;
                    seen |= 1;
                    i = e;
                    want_member = false;
                }
                Key::KNfields => {
                    dup(seen, 2, ks)?;
                    let (x, e) = slot_nat(b, ks, v)?;
                    nf = x;
                    seen |= 2;
                    i = e;
                    want_member = false;
                }
                Key::KRhs => {
                    dup(seen, 4, ks)?;
                    let (x, e) = slot_nat(b, ks, v)?;
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
/// con-leche: ConLeche/Frontend/Scan/Fast.lean:1564-1590 scanIndRecListLoop
/// con-leche: ConLeche/Frontend/Scan/Fast.lean:1739-1765 scanIndTypeListLoop
/// con-leche: ConLeche/Frontend/Scan/Fast.lean:1888-1914 scanIndCtorListLoop
/// con-leche: ConLeche/Frontend/Scan/Naive.lean:227-250 naiveListLoop
/// The four `[{…}, …]` loops of the dialect are one generic function here, as
/// `Scan/Naive.lean`'s `naiveListLoop` already is: `Fast.lean`'s four copies
/// differ only in the member scanner they call (Lean's code generator would
/// have boxed a function argument, which is what the copies avoid).
pub fn scan_obj_list_loop<T, F>(b: &[u8], i: usize, item: F) -> ScanRes<Vec<T>>
where
    F: Fn(&[u8], usize) -> ScanRes<T>,
{
    let mut i = i;
    let mut acc: Vec<T> = Vec::new();
    let mut want_item = true;
    loop {
        if i >= b.len() {
            return err(i, ErrTag::ExpectedList);
        }
        let c = b[i];
        if is_ws(c) {
            i += 1;
        } else if c == 93 {
            if want_item && !acc.is_empty() {
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
            let (x, e) = item(b, i)?;
            prog(i, e)?;
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
        scan_obj_list_loop(b, i + 1, scan_rule)
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
        match next_member(b, &mut i, &mut want_member)? {
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
                    dup(seen, 1, ks)?;
                    let (_x, e) = scan_nat_list(b, v)?;
                    prog(ks, e)?;
                    seen |= 1;
                    i = e;
                    want_member = false;
                }
                Key::KIsUnsafe => {
                    dup(seen, 2, ks)?;
                    let (x, e) = scan_bool(b, v)?;
                    prog(ks, e)?;
                    is_uns = x;
                    seen |= 2;
                    i = e;
                    want_member = false;
                }
                Key::KK => {
                    dup(seen, 4, ks)?;
                    let (x, e) = scan_bool(b, v)?;
                    prog(ks, e)?;
                    kf = x;
                    seen |= 4;
                    i = e;
                    want_member = false;
                }
                Key::KLevelParams => {
                    dup(seen, 8, ks)?;
                    let (x, e) = scan_nat_list(b, v)?;
                    prog(ks, e)?;
                    lps = x;
                    seen |= 8;
                    i = e;
                    want_member = false;
                }
                Key::KName => {
                    dup(seen, 16, ks)?;
                    let (x, e) = slot_nat(b, ks, v)?;
                    nm = x;
                    seen |= 16;
                    i = e;
                    want_member = false;
                }
                Key::KNumIndices => {
                    dup(seen, 32, ks)?;
                    let (x, e) = slot_nat(b, ks, v)?;
                    n_idx = x;
                    seen |= 32;
                    i = e;
                    want_member = false;
                }
                Key::KNumMinors => {
                    dup(seen, 64, ks)?;
                    let (x, e) = slot_nat(b, ks, v)?;
                    n_min = x;
                    seen |= 64;
                    i = e;
                    want_member = false;
                }
                Key::KNumMotives => {
                    dup(seen, 128, ks)?;
                    let (x, e) = slot_nat(b, ks, v)?;
                    n_mot = x;
                    seen |= 128;
                    i = e;
                    want_member = false;
                }
                Key::KNumParams => {
                    dup(seen, 256, ks)?;
                    let (x, e) = slot_nat(b, ks, v)?;
                    n_p = x;
                    seen |= 256;
                    i = e;
                    want_member = false;
                }
                Key::KRules => {
                    dup(seen, 512, ks)?;
                    let (x, e) = scan_rules(b, v)?;
                    prog(ks, e)?;
                    rules = x;
                    seen |= 512;
                    i = e;
                    want_member = false;
                }
                Key::KType => {
                    dup(seen, 1024, ks)?;
                    let (x, e) = slot_nat(b, ks, v)?;
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

/// con-leche: ConLeche/Frontend/Scan/Fast.lean:1592-1596 scanIndRecs
/// con-leche: ConLeche/Frontend/Scan/Naive.lean:509 naiveIndRecs
/// The `[…]` of IndRec records.
pub fn scan_ind_recs(b: &[u8], i: usize) -> ScanRes<Vec<IndRecRec>> {
    if byte_at(b, i) == 91 {
        scan_obj_list_loop(b, i + 1, scan_ind_rec)
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
        match next_member(b, &mut i, &mut want_member)? {
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
                    dup(seen, 1, ks)?;
                    let (_x, e) = scan_nat_list(b, v)?;
                    prog(ks, e)?;
                    seen |= 1;
                    i = e;
                    want_member = false;
                }
                Key::KCtors => {
                    dup(seen, 2, ks)?;
                    let (x, e) = scan_nat_list(b, v)?;
                    prog(ks, e)?;
                    ctors = x;
                    seen |= 2;
                    i = e;
                    want_member = false;
                }
                Key::KIsRec => {
                    dup(seen, 4, ks)?;
                    let (x, e) = scan_bool(b, v)?;
                    prog(ks, e)?;
                    is_rec = x;
                    seen |= 4;
                    i = e;
                    want_member = false;
                }
                Key::KIsReflexive => {
                    dup(seen, 8, ks)?;
                    let (x, e) = scan_bool(b, v)?;
                    prog(ks, e)?;
                    is_refl = x;
                    seen |= 8;
                    i = e;
                    want_member = false;
                }
                Key::KIsUnsafe => {
                    dup(seen, 16, ks)?;
                    let (x, e) = scan_bool(b, v)?;
                    prog(ks, e)?;
                    is_uns = x;
                    seen |= 16;
                    i = e;
                    want_member = false;
                }
                Key::KLevelParams => {
                    dup(seen, 32, ks)?;
                    let (x, e) = scan_nat_list(b, v)?;
                    prog(ks, e)?;
                    lps = x;
                    seen |= 32;
                    i = e;
                    want_member = false;
                }
                Key::KName => {
                    dup(seen, 64, ks)?;
                    let (x, e) = slot_nat(b, ks, v)?;
                    nm = x;
                    seen |= 64;
                    i = e;
                    want_member = false;
                }
                Key::KNumIndices => {
                    dup(seen, 128, ks)?;
                    let (x, e) = slot_nat(b, ks, v)?;
                    n_idx = x;
                    seen |= 128;
                    i = e;
                    want_member = false;
                }
                Key::KNumNested => {
                    dup(seen, 256, ks)?;
                    let (x, e) = slot_nat(b, ks, v)?;
                    n_nest = x;
                    seen |= 256;
                    i = e;
                    want_member = false;
                }
                Key::KNumParams => {
                    dup(seen, 512, ks)?;
                    let (x, e) = slot_nat(b, ks, v)?;
                    n_p = x;
                    seen |= 512;
                    i = e;
                    want_member = false;
                }
                Key::KType => {
                    dup(seen, 1024, ks)?;
                    let (x, e) = slot_nat(b, ks, v)?;
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

/// con-leche: ConLeche/Frontend/Scan/Fast.lean:1767-1771 scanIndTypes
/// con-leche: ConLeche/Frontend/Scan/Naive.lean:529 naiveIndTypes
/// The `[…]` of IndType records.
pub fn scan_ind_types(b: &[u8], i: usize) -> ScanRes<Vec<IndTypeRec>> {
    if byte_at(b, i) == 91 {
        scan_obj_list_loop(b, i + 1, scan_ind_type)
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
        match next_member(b, &mut i, &mut want_member)? {
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
                    dup(seen, 1, ks)?;
                    let (x, e) = slot_nat(b, ks, v)?;
                    ci = Some(x);
                    seen |= 1;
                    i = e;
                    want_member = false;
                }
                Key::KInduct => {
                    dup(seen, 2, ks)?;
                    let (x, e) = slot_nat(b, ks, v)?;
                    ind = Some(x);
                    seen |= 2;
                    i = e;
                    want_member = false;
                }
                Key::KIsUnsafe => {
                    dup(seen, 4, ks)?;
                    let (x, e) = scan_bool(b, v)?;
                    prog(ks, e)?;
                    is_uns = x;
                    seen |= 4;
                    i = e;
                    want_member = false;
                }
                Key::KLevelParams => {
                    dup(seen, 8, ks)?;
                    let (x, e) = scan_nat_list(b, v)?;
                    prog(ks, e)?;
                    lps = x;
                    seen |= 8;
                    i = e;
                    want_member = false;
                }
                Key::KName => {
                    dup(seen, 16, ks)?;
                    let (x, e) = slot_nat(b, ks, v)?;
                    nm = x;
                    seen |= 16;
                    i = e;
                    want_member = false;
                }
                Key::KNumFields => {
                    dup(seen, 32, ks)?;
                    let (x, e) = slot_nat(b, ks, v)?;
                    n_f = x;
                    seen |= 32;
                    i = e;
                    want_member = false;
                }
                Key::KNumParams => {
                    dup(seen, 64, ks)?;
                    let (x, e) = slot_nat(b, ks, v)?;
                    n_p = x;
                    seen |= 64;
                    i = e;
                    want_member = false;
                }
                Key::KType => {
                    dup(seen, 128, ks)?;
                    let (x, e) = slot_nat(b, ks, v)?;
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

/// con-leche: ConLeche/Frontend/Scan/Fast.lean:1916-1920 scanIndCtors
/// con-leche: ConLeche/Frontend/Scan/Naive.lean:548 naiveIndCtors
/// The `[…]` of IndCtor records.
pub fn scan_ind_ctors(b: &[u8], i: usize) -> ScanRes<Vec<IndCtorRec>> {
    if byte_at(b, i) == 91 {
        scan_obj_list_loop(b, i + 1, scan_ind_ctor)
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
        match next_member(b, &mut i, &mut want_member)? {
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
                    dup(seen, 1, ks)?;
                    let (x, e) = scan_bool(b, v)?;
                    prog(ks, e)?;
                    is_uns = x;
                    seen |= 1;
                    i = e;
                    want_member = false;
                }
                Key::KLevelParams => {
                    dup(seen, 2, ks)?;
                    let (x, e) = scan_nat_list(b, v)?;
                    prog(ks, e)?;
                    lps = x;
                    seen |= 2;
                    i = e;
                    want_member = false;
                }
                Key::KName => {
                    dup(seen, 4, ks)?;
                    let (x, e) = slot_nat(b, ks, v)?;
                    nm = x;
                    seen |= 4;
                    i = e;
                    want_member = false;
                }
                Key::KType => {
                    dup(seen, 8, ks)?;
                    let (x, e) = slot_nat(b, ks, v)?;
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
    let mut safety = String::new();
    let mut ty: u64 = 0;
    let mut vl: u64 = 0;
    loop {
        match next_member(b, &mut i, &mut want_member)? {
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
                    dup(seen, 1, ks)?;
                    let (_x, e) = scan_nat_list(b, v)?;
                    prog(ks, e)?;
                    seen |= 1;
                    i = e;
                    want_member = false;
                }
                Key::KHints => {
                    dup(seen, 2, ks)?;
                    let (x, e) = scan_hints(b, v)?;
                    prog(ks, e)?;
                    hints = x;
                    seen |= 2;
                    i = e;
                    want_member = false;
                }
                Key::KLevelParams => {
                    dup(seen, 4, ks)?;
                    let (x, e) = scan_nat_list(b, v)?;
                    prog(ks, e)?;
                    lps = x;
                    seen |= 4;
                    i = e;
                    want_member = false;
                }
                Key::KName => {
                    dup(seen, 8, ks)?;
                    let (x, e) = slot_nat(b, ks, v)?;
                    nm = x;
                    seen |= 8;
                    i = e;
                    want_member = false;
                }
                Key::KSafety => {
                    dup(seen, 16, ks)?;
                    let (x, e) = scan_string(b, v)?;
                    prog(ks, e)?;
                    safety = cps_to_string(&x);
                    seen |= 16;
                    i = e;
                    want_member = false;
                }
                Key::KType => {
                    dup(seen, 32, ks)?;
                    let (x, e) = slot_nat(b, ks, v)?;
                    ty = x;
                    seen |= 32;
                    i = e;
                    want_member = false;
                }
                Key::KValue => {
                    dup(seen, 64, ks)?;
                    let (x, e) = slot_nat(b, ks, v)?;
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
        match next_member(b, &mut i, &mut want_member)? {
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
                    dup(seen, 1, ks)?;
                    let (_x, e) = scan_nat_list(b, v)?;
                    prog(ks, e)?;
                    seen |= 1;
                    i = e;
                    want_member = false;
                }
                Key::KLevelParams => {
                    dup(seen, 2, ks)?;
                    let (x, e) = scan_nat_list(b, v)?;
                    prog(ks, e)?;
                    lps = x;
                    seen |= 2;
                    i = e;
                    want_member = false;
                }
                Key::KName => {
                    dup(seen, 4, ks)?;
                    let (x, e) = slot_nat(b, ks, v)?;
                    nm = x;
                    seen |= 4;
                    i = e;
                    want_member = false;
                }
                Key::KType => {
                    dup(seen, 8, ks)?;
                    let (x, e) = slot_nat(b, ks, v)?;
                    ty = x;
                    seen |= 8;
                    i = e;
                    want_member = false;
                }
                Key::KValue => {
                    dup(seen, 16, ks)?;
                    let (x, e) = slot_nat(b, ks, v)?;
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
        match next_member(b, &mut i, &mut want_member)? {
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
                    dup(seen, 1, ks)?;
                    let (_x, e) = scan_nat_list(b, v)?;
                    prog(ks, e)?;
                    seen |= 1;
                    i = e;
                    want_member = false;
                }
                Key::KIsUnsafe => {
                    dup(seen, 2, ks)?;
                    let (x, e) = scan_bool(b, v)?;
                    prog(ks, e)?;
                    is_uns = x;
                    seen |= 2;
                    i = e;
                    want_member = false;
                }
                Key::KLevelParams => {
                    dup(seen, 4, ks)?;
                    let (x, e) = scan_nat_list(b, v)?;
                    prog(ks, e)?;
                    lps = x;
                    seen |= 4;
                    i = e;
                    want_member = false;
                }
                Key::KName => {
                    dup(seen, 8, ks)?;
                    let (x, e) = slot_nat(b, ks, v)?;
                    nm = x;
                    seen |= 8;
                    i = e;
                    want_member = false;
                }
                Key::KType => {
                    dup(seen, 16, ks)?;
                    let (x, e) = slot_nat(b, ks, v)?;
                    ty = x;
                    seen |= 16;
                    i = e;
                    want_member = false;
                }
                Key::KValue => {
                    dup(seen, 32, ks)?;
                    let (x, e) = slot_nat(b, ks, v)?;
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
    let mut kind = String::new();
    let mut lps: Vec<u64> = Vec::new();
    let mut nm: u64 = 0;
    let mut ty: u64 = 0;
    loop {
        match next_member(b, &mut i, &mut want_member)? {
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
                    dup(seen, 1, ks)?;
                    let (x, e) = scan_string(b, v)?;
                    prog(ks, e)?;
                    kind = cps_to_string(&x);
                    seen |= 1;
                    i = e;
                    want_member = false;
                }
                Key::KLevelParams => {
                    dup(seen, 2, ks)?;
                    let (x, e) = scan_nat_list(b, v)?;
                    prog(ks, e)?;
                    lps = x;
                    seen |= 2;
                    i = e;
                    want_member = false;
                }
                Key::KName => {
                    dup(seen, 4, ks)?;
                    let (x, e) = slot_nat(b, ks, v)?;
                    nm = x;
                    seen |= 4;
                    i = e;
                    want_member = false;
                }
                Key::KType => {
                    dup(seen, 8, ks)?;
                    let (x, e) = slot_nat(b, ks, v)?;
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
        match next_member(b, &mut i, &mut want_member)? {
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
                    dup(seen, 1, ks)?;
                    let (_x, e) = scan_nat_list(b, v)?;
                    prog(ks, e)?;
                    seen |= 1;
                    i = e;
                    want_member = false;
                }
                Key::KCtors => {
                    dup(seen, 2, ks)?;
                    let (x, e) = scan_ind_ctors(b, v)?;
                    prog(ks, e)?;
                    ctors = x;
                    seen |= 2;
                    i = e;
                    want_member = false;
                }
                Key::KIsUnsafe => {
                    dup(seen, 4, ks)?;
                    let (_x, e) = scan_bool(b, v)?;
                    prog(ks, e)?;
                    seen |= 4;
                    i = e;
                    want_member = false;
                }
                Key::KRecs => {
                    dup(seen, 8, ks)?;
                    let (x, e) = scan_ind_recs(b, v)?;
                    prog(ks, e)?;
                    recs = x;
                    seen |= 8;
                    i = e;
                    want_member = false;
                }
                Key::KTypes => {
                    dup(seen, 16, ks)?;
                    let (x, e) = scan_ind_types(b, v)?;
                    prog(ks, e)?;
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
    matches!(p, LinePayload::Absent)
}

/// con-leche: ConLeche/Frontend/Scan/Fast.lean:2462-2609 scanLineLoop
/// con-leche: ConLeche/Frontend/Scan/Naive.lean:645-784 naiveLineLoop
/// con-leche: ConLeche/Frontend/Scan/Naive.lean:639-643 IdxKey
/// The members of one line.  `idx_kind` is `0` for none, `1` for `in`, `2` for
/// `il`, `3` for `ie` (`Naive.lean` spells the same thing as an `IdxKey`
/// enumeration).
pub fn scan_line_loop(b: &[u8], i: usize) -> ScanRes<LineRec> {
    let mut i = i;
    let mut want_member = true;
    let mut idx_kind: u8 = 0;
    let mut idx: u64 = 0;
    let mut pl = LinePayload::Absent;
    loop {
        match next_member(b, &mut i, &mut want_member)? {
            Member::Close => {
                if want_member && (idx_kind != 0 || !line_payload_is_absent(&pl)) {
                    return err(i, ErrTag::ExpectedKey);
                }
                return match (pl, idx_kind) {
                    (LinePayload::Name(r), 1) => Ok((LineRec::Name(idx, r), i + 1)),
                    (LinePayload::Level(r), 2) => Ok((LineRec::Level(idx, r), i + 1)),
                    (LinePayload::Expr(r), 3) => Ok((LineRec::Expr(idx, r), i + 1)),
                    (LinePayload::Decl(d), 0) => Ok((LineRec::Decl(d), i + 1)),
                    (LinePayload::Header, 0) => Ok((LineRec::Header, i + 1)),
                    (LinePayload::Absent, _) => err(i, ErrTag::MissingKey),
                    _ => err(i, ErrTag::MixedKeys),
                };
            }
            Member::Key(k, ks, v) => match k {
                Key::KIn | Key::KIl | Key::KIe => {
                    if idx_kind != 0 {
                        return err(ks, ErrTag::DuplicateKey);
                    }
                    let (n, e) = slot_nat(b, ks, v)?;
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
                    let (n, e) = slot_nat(b, ks, v)?;
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
                    let (us, e) = scan_nat_list(b, v)?;
                    if us.len() != 2 {
                        return err(v, ErrTag::ExpectedList);
                    }
                    prog(ks, e)?;
                    pl = if k == Key::KMax {
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
                    let (r, e) = if k == Key::KStr {
                        scan_str_name(b, v)?
                    } else {
                        scan_num_name(b, v)?
                    };
                    prog(ks, e)?;
                    pl = LinePayload::Name(r);
                    i = e;
                    want_member = false;
                }
                Key::KApp | Key::KLam | Key::KForallE | Key::KLetE | Key::KConst | Key::KProj => {
                    if !line_payload_is_absent(&pl) {
                        return err(ks, ErrTag::DuplicateKey);
                    }
                    let (r, e) = match k {
                        Key::KApp => scan_app_expr(b, v)?,
                        Key::KLam => scan_lam_expr(b, v)?,
                        Key::KForallE => scan_forall_expr(b, v)?,
                        Key::KLetE => scan_let_expr(b, v)?,
                        Key::KConst => scan_const_expr(b, v)?,
                        _ => scan_proj_expr(b, v)?,
                    };
                    prog(ks, e)?;
                    pl = LinePayload::Expr(r);
                    i = e;
                    want_member = false;
                }
                Key::KNatVal => {
                    if !line_payload_is_absent(&pl) {
                        return err(ks, ErrTag::DuplicateKey);
                    }
                    let (n, e) = scan_quoted_nat(b, v)?;
                    prog(ks, e)?;
                    pl = LinePayload::Expr(ExprRec::NatVal(n));
                    i = e;
                    want_member = false;
                }
                Key::KStrVal => {
                    if !line_payload_is_absent(&pl) {
                        return err(ks, ErrTag::DuplicateKey);
                    }
                    let (s, e) = scan_string(b, v)?;
                    prog(ks, e)?;
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
                        Key::KAxiom => scan_axiom_decl(b, v)?,
                        Key::KDef => scan_def_decl(b, v)?,
                        Key::KThm => scan_thm_decl(b, v)?,
                        Key::KOpaque => scan_opaque_decl(b, v)?,
                        Key::KQuot => scan_quot_decl(b, v)?,
                        _ => scan_ind_decl(b, v)?,
                    };
                    prog(ks, e)?;
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
                    prog(ks, e)?;
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
    let (r, j) = scan_line_loop(b, s + 1)?;
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
    b[i.min(b.len())..].contains(&10)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::frontend::scan_types::scan_err_render;

    fn one(line: &str) -> LineRec {
        let b = line.as_bytes();
        match scan_line_fwd(b, 0) {
            Ok((r, _)) => r,
            Err(e) => panic!("{}: {}", line, scan_err_render(&e)),
        }
    }

    fn bad(line: &str) -> ErrTag {
        let b = line.as_bytes();
        match scan_line_fwd(b, 0) {
            Ok(_) => panic!("{}: expected a failure", line),
            Err(e) => e.what,
        }
    }

    /// The key alphabet: every key of the dialect classifies, and a key one
    /// byte off does not (the `"i"`/`"ie"` confusion `keyAt`'s
    /// first-byte-and-length switch exists to rule out).
    #[test]
    fn keys_classify() {
        for (s, k) in [
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
            let b = s.as_bytes();
            let ke = key_end(b, 1);
            assert_eq!(key_at(b, 0, ke - 1), k, "{}", s);
        }
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
        assert_eq!(
            bad("{\"lam\":{\"binderInfo\":\"weird\",\"body\":2,\"name\":0,\"type\":4},\"ie\":5}\n"),
            ErrTag::BadBinderInfo
        );
        assert_eq!(
            bad("{\"lam\":{\"body\":2,\"name\":0,\"type\":4},\"ie\":5}\n"),
            ErrTag::MissingKey
        );
    }

    /// Every way a line can be malformed that the dialect names.
    #[test]
    fn malformed_lines() {
        assert_eq!(bad("[1,2]\n"), ErrTag::ExpectedObject);
        assert_eq!(bad("{\"nope\":1}\n"), ErrTag::UnknownKey);
        assert_eq!(bad("{\"in\":1,\"in\":2}\n"), ErrTag::DuplicateKey);
        assert_eq!(bad("{\"in\":1}\n"), ErrTag::MissingKey);
        assert_eq!(bad("{\"in\":1,\"succ\":2}\n"), ErrTag::MixedKeys);
        assert_eq!(bad("{\"in\" 1}\n"), ErrTag::ExpectedColon);
        assert_eq!(bad("{\"in\":1,}\n"), ErrTag::ExpectedKey);
        assert_eq!(bad("{\"in\":1 \"il\":2}\n"), ErrTag::ExpectedComma);
        assert_eq!(bad("{\"ie\":1,\"sort\":x}\n"), ErrTag::ExpectedNat);
        assert_eq!(bad("{\"ie\":06,\"sort\":1}\n"), ErrTag::ExpectedNat);
        assert_eq!(bad("{\"ie\":1,\"us\":[1,]}\n"), ErrTag::UnknownKey);
        assert_eq!(bad("{\"ie\":1,\"const\":{\"name\":1,\"us\":[1,]}}\n"), ErrTag::ExpectedList);
        assert_eq!(bad("{\"ie\":1,\"strVal\":\"\\q\"}\n"), ErrTag::BadEscape);
        assert_eq!(bad("{\"ie\":1,\"sort\":1} x\n"), ErrTag::Trailing);
        // §3.3's machine-word split: a stream index too large is a failure,
        // never a truncation.  (A `natVal` literal of the same size is fine.)
        assert_eq!(
            bad("{\"ie\":99999999999999999999,\"sort\":1}\n"),
            ErrTag::IndexOverflow
        );
    }

    /// The string codec: the escapes the dialect has, the surrogate pair rule
    /// and the lone-surrogate fallback to U+FFFD (`Lean.Json`'s own).
    #[test]
    fn string_escapes() {
        let got = |s: &str| -> Vec<u32> {
            let line = format!("{{\"ie\":1,\"strVal\":\"{}\"}}\n", s);
            match one(&line) {
                LineRec::Expr(_, ExprRec::StrVal(v)) => v,
                _ => panic!("not a strVal"),
            }
        };
        assert_eq!(got("a\\nb"), vec!['a' as u32, 10, 'b' as u32]);
        assert_eq!(got("\\\\\\\"\\/\\b\\f\\r\\t"), vec![92, 34, 47, 8, 12, 13, 9]);
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
                LineRec::Decl(DeclRec::Defn(_, _, h, s)) => {
                    assert_eq!(s, "safe");
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
            Err(e) => panic!("{}", scan_err_render(&e)),
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
        assert_eq!(bad("{\"meta\":{\"x\":\n{\"in\":1}}"), ErrTag::ExpectedObject);
    }
}
