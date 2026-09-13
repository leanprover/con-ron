//! The decoder of the embedded `con-ron-pins/1` text (DESIGN.md §3, task #43).
//!
//! `kernel::pins_text::PINS_TEXT` is con-leche's `natOpPinSets` as the text
//! format `proof/ConRon/Dump/FORMAT.md` specifies; this module is the
//! *verified* reader of that format, so that the pin list
//! `cached::installed::check_decls` folds with is computed **inside** the core
//! rather than handed in by the unverified driver (task #31's arrangement).
//! `con_ron_dump::parse_pins` is the same function outside the Aeneas subset —
//! iterators, `?`, `String` errors — and a unit test holds the two together on
//! the embedded text.
//!
//! **The grammar** is FORMAT.md's: the header line, then `N`/`L`/`W`/`E`
//! records (the interned `Name`/`Level`/`PropWhen`/`Expr` DAG), `S` records
//! (one per toolchain variant, in the order
//! `checker::check_div_mod_pin_loop` tries them) and the `end <count>` footer.
//! Ids are dense and backward-only, which is what lets a single forward pass
//! with one `Vec` per kind resolve every reference by indexing a table that is
//! already long enough — no fixups, no second pass.
//!
//! **Deliberately stricter than `ConRon/Dump/Pins.lean`.**  The Lean
//! reference reader splits the text into lines and each line into
//! space-separated tokens, so it tolerates empty lines and runs of spaces.
//! This decoder walks the bytes with an index and requires exactly what the
//! writer emits: single spaces between fields, one `'\n'` after each record
//! and nothing after the footer's newline.  That direction is free for the
//! theorem, whose
//! refinement statement is "if the Rust decoder returns `ok v` then the Lean
//! reader returns the same value" (DESIGN.md §3.5's exact-result shape): a
//! *stricter* decoder only has fewer cases to discharge, and the text it must
//! accept is a committed constant that `scripts/gen-pins.sh --check` keeps
//! byte-identical to the writer's output.
//!
//! **Errors.**  Every failure is `CheckError::Native` (task #67): con-leche
//! has no decoder at all — `natOpPinSets` is loaded at *elaboration* time by
//! `#load_natop_pins` (`ConLeche/Kernel/NatOpPins.lean:61-64`) from an
//! `include_str` JSON — so not one of this module's twenty-eight throws has a
//! `throw` behind it, and claiming any of them mirrors one would be false.
//! They are the port's own declines: a malformed text cannot happen for the
//! embedded constant (the freshness gate is what makes that a fact rather
//! than a hope), and the theorem runs the decoder on that constant, where it
//! returns `ok`.  All of them carry the same message; the theorem never reads
//! it, and the driver turns the error into exit 2.

use crate::kernel::core_types;
use crate::kernel::core_types::CheckError;
use crate::kernel::core_types::CheckM;
use crate::kernel::env;
use crate::kernel::expr;
use crate::kernel::expr::Expr;
use crate::kernel::level;
use crate::kernel::level::Level;
use crate::kernel::name;
use crate::kernel::name::Name;
use crate::kernel::nat_op_pins::NatOpPinSet;
use crate::kernel::pins_text::PINS_TEXT;
use crate::kernel::prop_when;
use crate::kernel::prop_when::PropWhen;
use crate::ron::nat;
use std::vec::Vec;

/// con-leche: none — `Read.lean`'s `RState`, restricted to the pin dump's four id spaces
/// The forward pass's state: one table per id space, in emission order, plus
/// the pin variants read so far.  A reference `<id>` is an index into a table
/// that already has `id` entries, which FORMAT.md §2's "ids are dense and
/// backward-only" invariant guarantees and `expect_id` re-checks.
pub struct Tables {
    pub names: Vec<Name>,
    pub levels: Vec<Level>,
    pub pws: Vec<PropWhen>,
    pub exprs: Vec<Expr>,
    pub sets: Vec<NatOpPinSet>,
}

/// con-leche: none — `Read.lean`'s initial `RState`
/// The empty tables the header leaves behind.
pub fn tables_new() -> Tables {
    Tables {
        names: Vec::new(),
        levels: Vec::new(),
        pws: Vec::new(),
        exprs: Vec::new(),
        sets: Vec::new(),
    }
}

/// con-leche: none — Rust-only failures, DESIGN.md §3
/// The one error this module reports: the embedded text is not a
/// `con-ron-pins/1` dump.  `Native` (task #67), because the cited checker has
/// no decoder to throw — the pins are elaboration-time data there — and
/// because the text is a committed constant (see the module note).  It is the
/// spelling of `Read.lean`'s `rerr`, with the line number dropped.
pub fn bad_text() -> CheckError {
    const M: [u32; 34] = [
        101, 109, 98, 101, 100, 100, 101, 100, 32, 112, 105, 110, 32, 116, 101,
        120, 116, 32, 105, 115, 32, 109, 97, 108, 102, 111, 114, 109, 101, 100,
        32, 40, 33, 41,
    ];
    core_types::native(core_types::code_points(&M))
}

// ---------------------------------------------------------------------------
// Bytes
// ---------------------------------------------------------------------------

/// con-leche: none — `String.get`, as a bounds-checked byte read
/// The byte at `i`, or `256` past the end: one sentinel keeps every caller's
/// "is this a space?" test a single comparison instead of a bounds test and a
/// comparison (§3.4 has no `Option` chaining without `?`).
pub fn byte_at(t: &[u8], i: usize) -> u64 {
    if i < t.len() {
        t[i] as u64
    } else {
        256
    }
}

/// con-leche: none — the literal comparison `hdr != pinsHeader` of `parsePins`
/// Does `t` start with `p`?  The index recursion a `&[u8]` comparison is.
pub fn starts_with_from(t: &[u8], p: &[u8], i: usize) -> bool {
    if i >= p.len() {
        true
    } else if byte_at(t, i) != p[i] as u64 {
        false
    } else {
        starts_with_from(t, p, i + 1)
    }
}

/// con-leche: none — the header line of `parsePins`
/// `con-ron-pins/1` and its newline, as the bytes the text must open with
/// (`Write.lean`'s `pinsHeader`).
pub fn pins_header() -> Vec<u8> {
    const H: [u8; 15] = [
        99, 111, 110, 45, 114, 111, 110, 45, 112, 105, 110, 115, 47, 49, 10,
    ];
    bytes_from(&H, 0, Vec::new())
}

/// con-leche: none — the index recursion behind `pins_header`
/// Copy a `const …: [u8; N]` into an owned `Vec<u8>` (`core_types::code_points`
/// for bytes).
pub fn bytes_from(bs: &[u8], i: usize, out: Vec<u8>) -> Vec<u8> {
    if i >= bs.len() {
        out
    } else {
        let mut out = out;
        out.push(bs[i]);
        bytes_from(bs, i + 1, out)
    }
}

/// con-leche: none — the `" "` of `Write.lean`'s field joins
/// Step over the single space that separates two fields of a record.
pub fn after_space(t: &[u8], i: usize) -> CheckM<usize> {
    if byte_at(t, i) == 32 {
        Ok(i + 1)
    } else {
        Err(bad_text())
    }
}

/// con-leche: none — `Read.lean`'s "trailing fields in a record"
/// Step over the newline that ends a record: this is where the reference
/// reader's `st.pos != st.toks.size` check lands.
pub fn after_newline(t: &[u8], i: usize) -> CheckM<usize> {
    if byte_at(t, i) == 10 {
        Ok(i + 1)
    } else {
        Err(bad_text())
    }
}

// ---------------------------------------------------------------------------
// Scalars
// ---------------------------------------------------------------------------

/// con-leche: none — `Read.lean`'s `natTok` for the fields DESIGN.md §3.3 makes machine words
/// A decimal `<nat>` field: at least one digit, ending at a space or a
/// newline.  The bound keeps the accumulator inside `u64` without relying on
/// the overflow check (§3.4 forbids a panic as control flow); an id or a count
/// in this format is at most 26 721.
pub fn read_nat(t: &[u8], i: usize) -> CheckM<(u64, usize)> {
    let b = byte_at(t, i);
    if b < 48 || b > 57 {
        Err(bad_text())
    } else {
        read_nat_from(t, i, 0)
    }
}

/// con-leche: none — the index recursion behind `read_nat`
pub fn read_nat_from(t: &[u8], i: usize, acc: u64) -> CheckM<(u64, usize)> {
    let b = byte_at(t, i);
    if b < 48 || b > 57 {
        if b == 32 || b == 10 {
            Ok((acc, i))
        } else {
            Err(bad_text())
        }
    } else if acc > 1000000000000000000 {
        Err(bad_text())
    } else {
        read_nat_from(t, i + 1, acc * 10 + (b - 48))
    }
}

/// con-leche: none — `read_nat` where the value is an index into a table
/// A `<nat>` used as an id or a list length, bounded to `u32::MAX` so that the
/// `as usize` below is a *widening* cast on every target.
///
/// The bound is not decoration (task #64).  `read_nat`'s accumulator guard
/// admits values up to `10^19 + 9` — inside `u64`, but well outside `u32` —
/// and Aeneas models `usize` platform-generically, knowing only
/// `Usize::MAX ∈ {u32::MAX, u64::MAX}` and modelling `as usize` as a
/// *truncating* cast.  Without this check the decoder therefore does not
/// refine `ConRon.Dump.parsePins` on a 32-bit target, and the failure is a
/// real one rather than an artefact of the model: at `usize = u32` the text
/// `4294967296` would pass `expect_id(_, _, 0)`, because it truncates to `0`.
/// With the check the cast is the identity on every accepted value on every
/// platform (`u32::MAX ≤ Usize::MAX` is what Aeneas's `scalar_tac` knows), so
/// `proof/ConRon/Refine/PinsBytes.lean`'s `read_index_refines` needs no
/// platform hypothesis and nothing above it does either.  Ids, counts and
/// string lengths in this format are at most 26 721, so nothing a dump can
/// legitimately contain is rejected.  `usize::try_from` would be a sixth
/// external hole for no gain.
pub fn read_index(t: &[u8], i: usize) -> CheckM<(usize, usize)> {
    match read_nat(t, i) {
        Err(e) => Err(e),
        Ok((n, j)) => {
            if n > 4294967295 {
                Err(bad_text())
            } else {
                Ok((n as usize, j))
            }
        }
    }
}

/// con-leche: none — `Read.lean`'s `natTok` for `Literal.natVal`, which is unbounded
/// The one field of the format that is a mathematical `Nat`: a nat literal's
/// value, built with the crate's own bignum (DESIGN.md §3.3).
pub fn read_big_nat(t: &[u8], i: usize) -> CheckM<(nat::Nat, usize)> {
    let b = byte_at(t, i);
    if b < 48 || b > 57 {
        Err(bad_text())
    } else {
        read_big_nat_from(t, i, nat::zero())
    }
}

/// con-leche: none — the index recursion behind `read_big_nat`
pub fn read_big_nat_from(
    t: &[u8],
    i: usize,
    acc: nat::Nat,
) -> CheckM<(nat::Nat, usize)> {
    let b = byte_at(t, i);
    if b < 48 || b > 57 {
        if b == 32 || b == 10 {
            Ok((acc, i))
        } else {
            Err(bad_text())
        }
    } else {
        let ten = nat::from_u64(10);
        let shifted = nat::mul(&acc, &ten);
        let digit = nat::from_u64(b - 48);
        read_big_nat_from(t, i + 1, nat::add(&shifted, &digit))
    }
}

/// con-leche: none — `Read.lean`'s `expectId`
/// A record's own id must be the next one of its kind: FORMAT.md §2's
/// invariant, the half a reader has to verify.
pub fn expect_id(t: &[u8], i: usize, want: usize) -> CheckM<usize> {
    match read_index(t, i) {
        Err(e) => Err(e),
        Ok((got, j)) => {
            if got == want {
                Ok(j)
            } else {
                Err(bad_text())
            }
        }
    }
}

// ---------------------------------------------------------------------------
// Strings (FORMAT.md §3's escape)
// ---------------------------------------------------------------------------

/// con-leche: none — `Read.lean`'s `hexDigit?`
/// The value of a lowercase hexadecimal digit, or `16` for "not one".
pub fn hex_digit(b: u64) -> u64 {
    if b >= 48 && b <= 57 {
        b - 48
    } else if b >= 97 && b <= 102 {
        b - 87
    } else {
        16
    }
}

/// con-leche: none — `Nat.isValidChar`, which `Read.lean`'s `unescapeGo` checks
/// A code point is a `Char`: below `0x110000` and outside the surrogate range.
/// Without this the abstraction of a stored string is not injective (DESIGN.md
/// §3.5's one extra `StrWF` clause).
pub fn is_valid_char(v: u64) -> bool {
    if v < 55296 {
        true
    } else {
        v > 57343 && v < 1114112
    }
}

/// con-leche: none — `Read.lean`'s `strTok`
/// A string field: the code-point count, a space, then the escaped text, which
/// runs to the next space or newline and may be empty (it is exactly when the
/// count is `0`).  The redundant count is cross-checked, which is what it is
/// for.
pub fn read_string(t: &[u8], i: usize) -> CheckM<(Vec<u32>, usize)> {
    match read_index(t, i) {
        Err(e) => Err(e),
        Ok((n, j)) => match after_space(t, j) {
            Err(e) => Err(e),
            Ok(k) => match unescape_from(t, k, 0, false, Vec::new()) {
                Err(e) => Err(e),
                Ok((s, m)) => {
                    if s.len() == n {
                        Ok((s, m))
                    } else {
                        Err(bad_text())
                    }
                }
            },
        },
    }
}

/// con-leche: none — `Read.lean`'s `unescapeGo`, over bytes instead of characters
/// Undo `Write.lean`'s `escapeString`: a printable non-backslash ASCII byte is
/// itself, `\<hex>;` is the code point the hexadecimal names.  `v` accumulates
/// an escape's value and `in_esc` says whether one is open; the token ends at
/// the first space or newline, and an escape open there is an error.
pub fn unescape_from(
    t: &[u8],
    i: usize,
    v: u64,
    in_esc: bool,
    out: Vec<u32>,
) -> CheckM<(Vec<u32>, usize)> {
    let b = byte_at(t, i);
    if b == 32 || b == 10 {
        if in_esc {
            Err(bad_text())
        } else {
            Ok((out, i))
        }
    } else if b == 256 {
        Err(bad_text())
    } else if in_esc {
        if b == 59 {
            if is_valid_char(v) {
                let mut out = out;
                out.push(v as u32);
                unescape_from(t, i + 1, 0, false, out)
            } else {
                Err(bad_text())
            }
        } else {
            let d = hex_digit(b);
            if d == 16 || v > 1114111 {
                Err(bad_text())
            } else {
                unescape_from(t, i + 1, v * 16 + d, true, out)
            }
        }
    } else if b == 92 {
        unescape_from(t, i + 1, 0, true, out)
    } else if b < 33 || b > 126 {
        // The format's unescaped bytes are printable ASCII; anything else in
        // the middle of a token means the text is not this writer's output.
        Err(bad_text())
    } else {
        let mut out = out;
        out.push(b as u32);
        unescape_from(t, i + 1, 0, false, out)
    }
}

// ---------------------------------------------------------------------------
// Backward references
// ---------------------------------------------------------------------------

/// con-leche: none — `Read.lean`'s `nameRef`
pub fn name_ref(t: &[u8], i: usize, tb: &Tables) -> CheckM<(Name, usize)> {
    match read_index(t, i) {
        Err(e) => Err(e),
        Ok((k, j)) => {
            if k < tb.names.len() {
                Ok((name::dup(&tb.names[k]), j))
            } else {
                Err(bad_text())
            }
        }
    }
}

/// con-leche: none — `Read.lean`'s `levelRef`
pub fn level_ref(t: &[u8], i: usize, tb: &Tables) -> CheckM<(Level, usize)> {
    match read_index(t, i) {
        Err(e) => Err(e),
        Ok((k, j)) => {
            if k < tb.levels.len() {
                Ok((level::dup(&tb.levels[k]), j))
            } else {
                Err(bad_text())
            }
        }
    }
}

/// con-leche: none — `Read.lean`'s `pwRef`
pub fn pw_ref(t: &[u8], i: usize, tb: &Tables) -> CheckM<(PropWhen, usize)> {
    match read_index(t, i) {
        Err(e) => Err(e),
        Ok((k, j)) => {
            if k < tb.pws.len() {
                Ok((prop_when::dup(&tb.pws[k]), j))
            } else {
                Err(bad_text())
            }
        }
    }
}

/// con-leche: none — `Read.lean`'s `exprRef`
pub fn expr_ref(t: &[u8], i: usize, tb: &Tables) -> CheckM<(Expr, usize)> {
    match read_index(t, i) {
        Err(e) => Err(e),
        Ok((k, j)) => {
            if k < tb.exprs.len() {
                Ok((expr::dup(&tb.exprs[k]), j))
            } else {
                Err(bad_text())
            }
        }
    }
}

/// con-leche: none — `Read.lean`'s `listTok nameRef`
/// A counted id list: the length, then that many space-separated ids
/// (`Write.lean`'s `idList`).
pub fn name_list(t: &[u8], i: usize, tb: &Tables) -> CheckM<(Vec<Name>, usize)> {
    match read_index(t, i) {
        Err(e) => Err(e),
        Ok((n, j)) => name_list_from(t, j, tb, n, Vec::new()),
    }
}

/// con-leche: none — the index recursion behind `name_list`
pub fn name_list_from(
    t: &[u8],
    i: usize,
    tb: &Tables,
    k: usize,
    out: Vec<Name>,
) -> CheckM<(Vec<Name>, usize)> {
    if k == 0 {
        Ok((out, i))
    } else {
        match after_space(t, i) {
            Err(e) => Err(e),
            Ok(j) => match name_ref(t, j, tb) {
                Err(e) => Err(e),
                Ok((n, m)) => {
                    let mut out = out;
                    out.push(n);
                    name_list_from(t, m, tb, k - 1, out)
                }
            },
        }
    }
}

/// con-leche: none — `Read.lean`'s `listTok levelRef`
pub fn level_list(
    t: &[u8],
    i: usize,
    tb: &Tables,
) -> CheckM<(Vec<Level>, usize)> {
    match read_index(t, i) {
        Err(e) => Err(e),
        Ok((n, j)) => level_list_from(t, j, tb, n, Vec::new()),
    }
}

/// con-leche: none — the index recursion behind `level_list`
pub fn level_list_from(
    t: &[u8],
    i: usize,
    tb: &Tables,
    k: usize,
    out: Vec<Level>,
) -> CheckM<(Vec<Level>, usize)> {
    if k == 0 {
        Ok((out, i))
    } else {
        match after_space(t, i) {
            Err(e) => Err(e),
            Ok(j) => match level_ref(t, j, tb) {
                Err(e) => Err(e),
                Ok((u, m)) => {
                    let mut out = out;
                    out.push(u);
                    level_list_from(t, m, tb, k - 1, out)
                }
            },
        }
    }
}

/// con-leche: none — `Read.lean`'s `listTok exprRef`
pub fn expr_list(t: &[u8], i: usize, tb: &Tables) -> CheckM<(Vec<Expr>, usize)> {
    match read_index(t, i) {
        Err(e) => Err(e),
        Ok((n, j)) => expr_list_from(t, j, tb, n, Vec::new()),
    }
}

/// con-leche: none — the index recursion behind `expr_list`
pub fn expr_list_from(
    t: &[u8],
    i: usize,
    tb: &Tables,
    k: usize,
    out: Vec<Expr>,
) -> CheckM<(Vec<Expr>, usize)> {
    if k == 0 {
        Ok((out, i))
    } else {
        match after_space(t, i) {
            Err(e) => Err(e),
            Ok(j) => match expr_ref(t, j, tb) {
                Err(e) => Err(e),
                Ok((e, m)) => {
                    let mut out = out;
                    out.push(e);
                    expr_list_from(t, m, tb, k - 1, out)
                }
            },
        }
    }
}

// ---------------------------------------------------------------------------
// The records (FORMAT.md §4, the kinds a pin dump uses)
// ---------------------------------------------------------------------------

/// con-leche: none — `Read.lean`'s `N` arm of `parseRecord`
/// `N <id> a` | `N <id> s <pre> <string>` | `N <id> n <pre> <k>`, and the
/// value is built with the port's own smart constructor, which is what pins
/// the stored hash word to the children (DESIGN.md §3.5).
pub fn record_name(t: &[u8], i: usize, tb: Tables) -> CheckM<(Tables, usize)> {
    match expect_id(t, i, tb.names.len()) {
        Err(e) => Err(e),
        Ok(i) => match after_space(t, i) {
            Err(e) => Err(e),
            Ok(i) => {
                let k = byte_at(t, i);
                if k == 97 {
                    // `a`: anonymous
                    match after_newline(t, i + 1) {
                        Err(e) => Err(e),
                        Ok(i) => {
                            let mut tb = tb;
                            tb.names.push(name::anonymous());
                            Ok((tb, i))
                        }
                    }
                } else if k == 115 {
                    // `s`: a string component
                    record_name_str(t, i + 1, tb)
                } else if k == 110 {
                    // `n`: a numeric component
                    record_name_num(t, i + 1, tb)
                } else {
                    Err(bad_text())
                }
            }
        },
    }
}

/// con-leche: none — the `s` arm of `Read.lean`'s `N` record
pub fn record_name_str(
    t: &[u8],
    i: usize,
    tb: Tables,
) -> CheckM<(Tables, usize)> {
    match after_space(t, i) {
        Err(e) => Err(e),
        Ok(i) => match name_ref(t, i, &tb) {
            Err(e) => Err(e),
            Ok((pre, i)) => match after_space(t, i) {
                Err(e) => Err(e),
                Ok(i) => match read_string(t, i) {
                    Err(e) => Err(e),
                    Ok((s, i)) => match after_newline(t, i) {
                        Err(e) => Err(e),
                        Ok(i) => {
                            let mut tb = tb;
                            tb.names.push(name::mk_str(pre, s));
                            Ok((tb, i))
                        }
                    },
                },
            },
        },
    }
}

/// con-leche: none — the `n` arm of `Read.lean`'s `N` record
pub fn record_name_num(
    t: &[u8],
    i: usize,
    tb: Tables,
) -> CheckM<(Tables, usize)> {
    match after_space(t, i) {
        Err(e) => Err(e),
        Ok(i) => match name_ref(t, i, &tb) {
            Err(e) => Err(e),
            Ok((pre, i)) => match after_space(t, i) {
                Err(e) => Err(e),
                Ok(i) => match read_nat(t, i) {
                    Err(e) => Err(e),
                    Ok((k, i)) => match after_newline(t, i) {
                        Err(e) => Err(e),
                        Ok(i) => {
                            let mut tb = tb;
                            tb.names.push(name::mk_num(pre, k));
                            Ok((tb, i))
                        }
                    },
                },
            },
        },
    }
}

/// con-leche: none — `Read.lean`'s `L` arm of `parseRecord`
/// `L <id> z` | `s <u>` | `m <u> <v>` | `i <u> <v>` | `p <name>`.
pub fn record_level(t: &[u8], i: usize, tb: Tables) -> CheckM<(Tables, usize)> {
    match expect_id(t, i, tb.levels.len()) {
        Err(e) => Err(e),
        Ok(i) => match after_space(t, i) {
            Err(e) => Err(e),
            Ok(i) => {
                let k = byte_at(t, i);
                if k == 122 {
                    // `z`: zero
                    match after_newline(t, i + 1) {
                        Err(e) => Err(e),
                        Ok(i) => {
                            let mut tb = tb;
                            tb.levels.push(level::zero());
                            Ok((tb, i))
                        }
                    }
                } else if k == 115 {
                    // `s`: succ
                    record_level_succ(t, i + 1, tb)
                } else if k == 109 || k == 105 {
                    // `m`/`i`: max and imax, which differ only in the node
                    record_level_binop(t, i + 1, tb, k == 109)
                } else if k == 112 {
                    // `p`: a parameter
                    record_level_param(t, i + 1, tb)
                } else {
                    Err(bad_text())
                }
            }
        },
    }
}

/// con-leche: none — the `s` arm of `Read.lean`'s `L` record
pub fn record_level_succ(
    t: &[u8],
    i: usize,
    tb: Tables,
) -> CheckM<(Tables, usize)> {
    match after_space(t, i) {
        Err(e) => Err(e),
        Ok(i) => match level_ref(t, i, &tb) {
            Err(e) => Err(e),
            Ok((u, i)) => match after_newline(t, i) {
                Err(e) => Err(e),
                Ok(i) => {
                    let mut tb = tb;
                    tb.levels.push(level::succ(u));
                    Ok((tb, i))
                }
            },
        },
    }
}

/// con-leche: none — the `m` and `i` arms of `Read.lean`'s `L` record
pub fn record_level_binop(
    t: &[u8],
    i: usize,
    tb: Tables,
    is_max: bool,
) -> CheckM<(Tables, usize)> {
    match after_space(t, i) {
        Err(e) => Err(e),
        Ok(i) => match level_ref(t, i, &tb) {
            Err(e) => Err(e),
            Ok((u, i)) => match after_space(t, i) {
                Err(e) => Err(e),
                Ok(i) => match level_ref(t, i, &tb) {
                    Err(e) => Err(e),
                    Ok((v, i)) => match after_newline(t, i) {
                        Err(e) => Err(e),
                        Ok(i) => {
                            let mut tb = tb;
                            if is_max {
                                tb.levels.push(level::max(u, v));
                            } else {
                                tb.levels.push(level::imax(u, v));
                            }
                            Ok((tb, i))
                        }
                    },
                },
            },
        },
    }
}

/// con-leche: none — the `p` arm of `Read.lean`'s `L` record
pub fn record_level_param(
    t: &[u8],
    i: usize,
    tb: Tables,
) -> CheckM<(Tables, usize)> {
    match after_space(t, i) {
        Err(e) => Err(e),
        Ok(i) => match name_ref(t, i, &tb) {
            Err(e) => Err(e),
            Ok((n, i)) => match after_newline(t, i) {
                Err(e) => Err(e),
                Ok(i) => {
                    let mut tb = tb;
                    tb.levels.push(level::param(n));
                    Ok((tb, i))
                }
            },
        },
    }
}

/// con-leche: none — `Read.lean`'s `W` arm of `parseRecord`
/// `W <id> n` | `W <id> z <names>`: the zero-ness datum, through its public
/// API exactly as the writer wrote it through `toList?`.
pub fn record_pw(t: &[u8], i: usize, tb: Tables) -> CheckM<(Tables, usize)> {
    match expect_id(t, i, tb.pws.len()) {
        Err(e) => Err(e),
        Ok(i) => match after_space(t, i) {
            Err(e) => Err(e),
            Ok(i) => {
                let k = byte_at(t, i);
                if k == 110 {
                    // `n`: never
                    match after_newline(t, i + 1) {
                        Err(e) => Err(e),
                        Ok(i) => {
                            let mut tb = tb;
                            tb.pws.push(prop_when::never());
                            Ok((tb, i))
                        }
                    }
                } else if k == 122 {
                    // `z`: if all of these parameters are zero
                    record_pw_zero(t, i + 1, tb)
                } else {
                    Err(bad_text())
                }
            }
        },
    }
}

/// con-leche: none — the `z` arm of `Read.lean`'s `W` record
pub fn record_pw_zero(
    t: &[u8],
    i: usize,
    tb: Tables,
) -> CheckM<(Tables, usize)> {
    match after_space(t, i) {
        Err(e) => Err(e),
        Ok(i) => match name_list(t, i, &tb) {
            Err(e) => Err(e),
            Ok((ps, i)) => match after_newline(t, i) {
                Err(e) => Err(e),
                Ok(i) => {
                    let mut tb = tb;
                    tb.pws.push(prop_when::if_all_zero(ps));
                    Ok((tb, i))
                }
            },
        },
    }
}

/// con-leche: none — `Read.lean`'s `E` arm of `parseRecord`
/// `E <id> <kind> …`, the ten `Expr` constructors of FORMAT.md §4.  Each node
/// is built by the port's own smart constructor, so the stored word (hash,
/// loose-bvar bound, free-variable bound) is the one the checker would have
/// computed — the reader never writes a cached datum itself.
pub fn record_expr(t: &[u8], i: usize, tb: Tables) -> CheckM<(Tables, usize)> {
    match expect_id(t, i, tb.exprs.len()) {
        Err(e) => Err(e),
        Ok(i) => match after_space(t, i) {
            Err(e) => Err(e),
            Ok(i) => {
                let k = byte_at(t, i);
                if k == 98 {
                    record_expr_bvar(t, i + 1, tb)
                } else if k == 118 {
                    record_expr_fvar(t, i + 1, tb)
                } else if k == 115 {
                    record_expr_sort(t, i + 1, tb)
                } else if k == 99 {
                    record_expr_const(t, i + 1, tb)
                } else if k == 97 {
                    record_expr_app(t, i + 1, tb)
                } else if k == 108 || k == 102 {
                    // `l`/`f`: lambda and forall, which differ only in the node
                    record_expr_binder(t, i + 1, tb, k == 108)
                } else if k == 116 {
                    record_expr_let(t, i + 1, tb)
                } else if k == 110 {
                    record_expr_nat_lit(t, i + 1, tb)
                } else if k == 103 {
                    record_expr_str_lit(t, i + 1, tb)
                } else if k == 112 {
                    record_expr_proj(t, i + 1, tb)
                } else {
                    Err(bad_text())
                }
            }
        },
    }
}

/// con-leche: none — the `b` arm of `Read.lean`'s `E` record
pub fn record_expr_bvar(
    t: &[u8],
    i: usize,
    tb: Tables,
) -> CheckM<(Tables, usize)> {
    match after_space(t, i) {
        Err(e) => Err(e),
        Ok(i) => match read_nat(t, i) {
            Err(e) => Err(e),
            Ok((k, i)) => match after_newline(t, i) {
                Err(e) => Err(e),
                Ok(i) => {
                    let mut tb = tb;
                    tb.exprs.push(expr::bvar(k));
                    Ok((tb, i))
                }
            },
        },
    }
}

/// con-leche: none — the `v` arm of `Read.lean`'s `E` record
pub fn record_expr_fvar(
    t: &[u8],
    i: usize,
    tb: Tables,
) -> CheckM<(Tables, usize)> {
    match after_space(t, i) {
        Err(e) => Err(e),
        Ok(i) => match read_nat(t, i) {
            Err(e) => Err(e),
            Ok((idx, i)) => match after_space(t, i) {
                Err(e) => Err(e),
                Ok(i) => match expr_ref(t, i, &tb) {
                    Err(e) => Err(e),
                    Ok((ty, i)) => match after_newline(t, i) {
                        Err(e) => Err(e),
                        Ok(i) => {
                            let mut tb = tb;
                            tb.exprs.push(expr::fvar(idx, ty));
                            Ok((tb, i))
                        }
                    },
                },
            },
        },
    }
}

/// con-leche: none — the `s` arm of `Read.lean`'s `E` record
pub fn record_expr_sort(
    t: &[u8],
    i: usize,
    tb: Tables,
) -> CheckM<(Tables, usize)> {
    match after_space(t, i) {
        Err(e) => Err(e),
        Ok(i) => match level_ref(t, i, &tb) {
            Err(e) => Err(e),
            Ok((u, i)) => match after_newline(t, i) {
                Err(e) => Err(e),
                Ok(i) => {
                    let mut tb = tb;
                    tb.exprs.push(expr::sort(u));
                    Ok((tb, i))
                }
            },
        },
    }
}

/// con-leche: none — the `c` arm of `Read.lean`'s `E` record
pub fn record_expr_const(
    t: &[u8],
    i: usize,
    tb: Tables,
) -> CheckM<(Tables, usize)> {
    match after_space(t, i) {
        Err(e) => Err(e),
        Ok(i) => match name_ref(t, i, &tb) {
            Err(e) => Err(e),
            Ok((n, i)) => match after_space(t, i) {
                Err(e) => Err(e),
                Ok(i) => match level_list(t, i, &tb) {
                    Err(e) => Err(e),
                    Ok((us, i)) => match after_newline(t, i) {
                        Err(e) => Err(e),
                        Ok(i) => {
                            let mut tb = tb;
                            tb.exprs.push(expr::mk_const(n, us));
                            Ok((tb, i))
                        }
                    },
                },
            },
        },
    }
}

/// con-leche: none — the `a` arm of `Read.lean`'s `E` record
pub fn record_expr_app(
    t: &[u8],
    i: usize,
    tb: Tables,
) -> CheckM<(Tables, usize)> {
    match after_space(t, i) {
        Err(e) => Err(e),
        Ok(i) => match expr_ref(t, i, &tb) {
            Err(e) => Err(e),
            Ok((f, i)) => match after_space(t, i) {
                Err(e) => Err(e),
                Ok(i) => match expr_ref(t, i, &tb) {
                    Err(e) => Err(e),
                    Ok((a, i)) => match after_newline(t, i) {
                        Err(e) => Err(e),
                        Ok(i) => {
                            let mut tb = tb;
                            tb.exprs.push(expr::app(f, a));
                            Ok((tb, i))
                        }
                    },
                },
            },
        },
    }
}

/// con-leche: none — the `l` and `f` arms of `Read.lean`'s `E` record
pub fn record_expr_binder(
    t: &[u8],
    i: usize,
    tb: Tables,
    is_lam: bool,
) -> CheckM<(Tables, usize)> {
    match after_space(t, i) {
        Err(e) => Err(e),
        Ok(i) => match expr_ref(t, i, &tb) {
            Err(e) => Err(e),
            Ok((ty, i)) => match after_space(t, i) {
                Err(e) => Err(e),
                Ok(i) => match expr_ref(t, i, &tb) {
                    Err(e) => Err(e),
                    Ok((body, i)) => match after_space(t, i) {
                        Err(e) => Err(e),
                        Ok(i) => match pw_ref(t, i, &tb) {
                            Err(e) => Err(e),
                            Ok((pw, i)) => match after_newline(t, i) {
                                Err(e) => Err(e),
                                Ok(i) => {
                                    let m = expr::binder_meta(pw);
                                    let mut tb = tb;
                                    if is_lam {
                                        tb.exprs.push(expr::lam(ty, body, m));
                                    } else {
                                        tb.exprs
                                            .push(expr::forall_e(ty, body, m));
                                    }
                                    Ok((tb, i))
                                }
                            },
                        },
                    },
                },
            },
        },
    }
}

/// con-leche: none — the `t` arm of `Read.lean`'s `E` record
pub fn record_expr_let(
    t: &[u8],
    i: usize,
    tb: Tables,
) -> CheckM<(Tables, usize)> {
    match after_space(t, i) {
        Err(e) => Err(e),
        Ok(i) => match expr_ref(t, i, &tb) {
            Err(e) => Err(e),
            Ok((ty, i)) => match after_space(t, i) {
                Err(e) => Err(e),
                Ok(i) => match expr_ref(t, i, &tb) {
                    Err(e) => Err(e),
                    Ok((v, i)) => match after_space(t, i) {
                        Err(e) => Err(e),
                        Ok(i) => match expr_ref(t, i, &tb) {
                            Err(e) => Err(e),
                            Ok((body, i)) => match after_newline(t, i) {
                                Err(e) => Err(e),
                                Ok(i) => {
                                    let mut tb = tb;
                                    tb.exprs.push(expr::let_e(ty, v, body));
                                    Ok((tb, i))
                                }
                            },
                        },
                    },
                },
            },
        },
    }
}

/// con-leche: none — the `n` arm of `Read.lean`'s `E` record
pub fn record_expr_nat_lit(
    t: &[u8],
    i: usize,
    tb: Tables,
) -> CheckM<(Tables, usize)> {
    match after_space(t, i) {
        Err(e) => Err(e),
        Ok(i) => match read_big_nat(t, i) {
            Err(e) => Err(e),
            Ok((n, i)) => match after_newline(t, i) {
                Err(e) => Err(e),
                Ok(i) => {
                    let mut tb = tb;
                    tb.exprs.push(expr::lit(expr::literal_nat(n)));
                    Ok((tb, i))
                }
            },
        },
    }
}

/// con-leche: none — the `g` arm of `Read.lean`'s `E` record
pub fn record_expr_str_lit(
    t: &[u8],
    i: usize,
    tb: Tables,
) -> CheckM<(Tables, usize)> {
    match after_space(t, i) {
        Err(e) => Err(e),
        Ok(i) => match read_string(t, i) {
            Err(e) => Err(e),
            Ok((s, i)) => match after_newline(t, i) {
                Err(e) => Err(e),
                Ok(i) => {
                    let mut tb = tb;
                    tb.exprs.push(expr::lit(expr::literal_str(s)));
                    Ok((tb, i))
                }
            },
        },
    }
}

/// con-leche: none — the `p` arm of `Read.lean`'s `E` record
pub fn record_expr_proj(
    t: &[u8],
    i: usize,
    tb: Tables,
) -> CheckM<(Tables, usize)> {
    match after_space(t, i) {
        Err(e) => Err(e),
        Ok(i) => match name_ref(t, i, &tb) {
            Err(e) => Err(e),
            Ok((sn, i)) => match after_space(t, i) {
                Err(e) => Err(e),
                Ok(i) => match read_nat(t, i) {
                    Err(e) => Err(e),
                    Ok((idx, i)) => match after_space(t, i) {
                        Err(e) => Err(e),
                        Ok(i) => match expr_ref(t, i, &tb) {
                            Err(e) => Err(e),
                            Ok((s, i)) => match after_newline(t, i) {
                                Err(e) => Err(e),
                                Ok(i) => {
                                    let mut tb = tb;
                                    tb.exprs.push(expr::proj(sn, idx, s));
                                    Ok((tb, i))
                                }
                            },
                        },
                    },
                },
            },
        },
    }
}

// ---------------------------------------------------------------------------
// The payload record (FORMAT.md §4)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/NatOpPinSet.lean:28-51 NatOpPinSet
/// con-leche: none — `Read.lean`'s `S` arm of `parseRecord`
/// `S <string> <expr>×8 (<k> <expr>*)×8`: one toolchain's pins.  An `S` record
/// carries no id — the record *is* the payload and its position in the text is
/// its position in the list `checker::check_div_mod_pin_loop` walks.
pub fn record_pin_set(t: &[u8], i: usize, tb: Tables) -> CheckM<(Tables, usize)> {
    match read_string(t, i) {
        Err(e) => Err(e),
        Ok((toolchain, i)) => match pins_eight(t, i, &tb) {
            Err(e) => Err(e),
            Ok((pins, i)) => match proofs_eight(t, i, &tb) {
                Err(e) => Err(e),
                Ok((proofs, i)) => match after_newline(t, i) {
                    Err(e) => Err(e),
                    Ok(i) => {
                        if pins.len() != 8 || proofs.len() != 8 {
                            // Unreachable: both readers are counted loops of
                            // exactly eight steps.  Spelled out because the
                            // model's indexing below is a `Result` too.
                            Err(bad_text())
                        } else {
                            let s = NatOpPinSet {
                                toolchain,
                                div_pin: expr::dup(&pins[0]),
                                mod_pin: expr::dup(&pins[1]),
                                gcd_pin: expr::dup(&pins[2]),
                                land_pin: expr::dup(&pins[3]),
                                lor_pin: expr::dup(&pins[4]),
                                xor_pin: expr::dup(&pins[5]),
                                shift_left_pin: expr::dup(&pins[6]),
                                shift_right_pin: expr::dup(&pins[7]),
                                div_proofs: env::exprs_copy(&proofs[0]),
                                mod_proofs: env::exprs_copy(&proofs[1]),
                                gcd_proofs: env::exprs_copy(&proofs[2]),
                                land_proofs: env::exprs_copy(&proofs[3]),
                                lor_proofs: env::exprs_copy(&proofs[4]),
                                xor_proofs: env::exprs_copy(&proofs[5]),
                                shift_left_proofs: env::exprs_copy(&proofs[6]),
                                shift_right_proofs: env::exprs_copy(&proofs[7]),
                            };
                            let mut tb = tb;
                            tb.sets.push(s);
                            Ok((tb, i))
                        }
                    }
                },
            },
        },
    }
}

/// con-leche: none — the eight `<expr>` fields of `Read.lean`'s `S` arm
/// The eight pinned defining expressions, each preceded by its space.
pub fn pins_eight(t: &[u8], i: usize, tb: &Tables) -> CheckM<(Vec<Expr>, usize)> {
    pins_eight_from(t, i, tb, 8, Vec::new())
}

/// con-leche: none — the index recursion behind `pins_eight`
pub fn pins_eight_from(
    t: &[u8],
    i: usize,
    tb: &Tables,
    k: usize,
    out: Vec<Expr>,
) -> CheckM<(Vec<Expr>, usize)> {
    if k == 0 {
        Ok((out, i))
    } else {
        match after_space(t, i) {
            Err(e) => Err(e),
            Ok(j) => match expr_ref(t, j, tb) {
                Err(e) => Err(e),
                Ok((e, m)) => {
                    let mut out = out;
                    out.push(e);
                    pins_eight_from(t, m, tb, k - 1, out)
                }
            },
        }
    }
}

/// con-leche: none — the eight counted proof lists of `Read.lean`'s `S` arm
pub fn proofs_eight(
    t: &[u8],
    i: usize,
    tb: &Tables,
) -> CheckM<(Vec<Vec<Expr>>, usize)> {
    proofs_eight_from(t, i, tb, 8, Vec::new())
}

/// con-leche: none — the index recursion behind `proofs_eight`
pub fn proofs_eight_from(
    t: &[u8],
    i: usize,
    tb: &Tables,
    k: usize,
    out: Vec<Vec<Expr>>,
) -> CheckM<(Vec<Vec<Expr>>, usize)> {
    if k == 0 {
        Ok((out, i))
    } else {
        match after_space(t, i) {
            Err(e) => Err(e),
            Ok(j) => match expr_list(t, j, tb) {
                Err(e) => Err(e),
                Ok((es, m)) => {
                    let mut out = out;
                    out.push(es);
                    proofs_eight_from(t, m, tb, k - 1, out)
                }
            },
        }
    }
}

// ---------------------------------------------------------------------------
// The pass
// ---------------------------------------------------------------------------

/// con-leche: none — `Read.lean`'s `runLines`
/// One record per step, stopping at the `end <count>` footer, whose count must
/// be the number of `S` records read and after whose newline the text must
/// end.  The recursion is the file's length, which is why the driver runs the
/// whole check on a thread with a 1 GiB stack (`con_ron::driver::STACK_BYTES`).
pub fn run_records(t: &[u8], i: usize, tb: Tables) -> CheckM<Vec<NatOpPinSet>> {
    let k = byte_at(t, i);
    if k == 101 {
        // `end <count>`: the footer, and with it the end of the text.
        run_footer(t, i + 1, tb)
    } else {
        match after_space(t, i + 1) {
            Err(e) => Err(e),
            Ok(j) => {
                let step = if k == 78 {
                    record_name(t, j, tb)
                } else if k == 76 {
                    record_level(t, j, tb)
                } else if k == 87 {
                    record_pw(t, j, tb)
                } else if k == 69 {
                    record_expr(t, j, tb)
                } else if k == 83 {
                    record_pin_set(t, j, tb)
                } else {
                    Err(bad_text())
                };
                match step {
                    Err(e) => Err(e),
                    Ok((tb, m)) => run_records(t, m, tb),
                }
            }
        }
    }
}

/// con-leche: none — the `end` arm of `Read.lean`'s `runLines`
/// `nd <count>\n` and nothing after it (the `e` is already consumed).
pub fn run_footer(t: &[u8], i: usize, tb: Tables) -> CheckM<Vec<NatOpPinSet>> {
    if byte_at(t, i) != 110 || byte_at(t, i + 1) != 100 {
        Err(bad_text())
    } else {
        match after_space(t, i + 2) {
            Err(e) => Err(e),
            Ok(i) => match read_index(t, i) {
                Err(e) => Err(e),
                Ok((n, i)) => match after_newline(t, i) {
                    Err(e) => Err(e),
                    Ok(i) => {
                        if i != t.len() || n != tb.sets.len() {
                            Err(bad_text())
                        } else {
                            Ok(tb.sets)
                        }
                    }
                },
            },
        }
    }
}

/// con-leche: none — `Read.lean`'s `parsePins`
/// **The decoder.**  `con-ron-pins/1` text in, con-leche's pin variants out,
/// in file order — which is the order `checker::check_div_mod_pin_loop` tries
/// them in, and therefore the order the list has to be in.
pub fn decode(t: &[u8]) -> CheckM<Vec<NatOpPinSet>> {
    let hdr = pins_header();
    if !starts_with_from(t, &hdr, 0) {
        Err(bad_text())
    } else {
        run_records(t, hdr.len(), tables_new())
    }
}

/// con-leche: ConLeche/Kernel/NatOpPins.lean:62-65 _
/// (The cited range is the `#load_natop_pins` command that *produces*
/// `natOpPinSets` while `NatOpPins.lean` elaborates; the declaration is not
/// written there, hence the `_`.)
/// **The pin list the binary checks with**: the embedded text, decoded.  This
/// is what `cached::installed::check_decls`' `pins` parameter is given for a
/// real run (`con_ron::driver`), and `proof/ConRon/Refine/Pins.lean` is where
/// what it equals is stated.  `--pins FILE` overrides it for testing only.
pub fn decode_embedded() -> CheckM<Vec<NatOpPinSet>> {
    decode(PINS_TEXT.as_bytes())
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Run `f` on a thread with the driver's stack: the pass recurses once per
    /// record and the embedded text has 26 721 of them.
    fn on_a_big_stack<T: Send + 'static>(f: impl FnOnce() -> T + Send + 'static) -> T {
        std::thread::Builder::new()
            .stack_size(1 << 30)
            .spawn(f)
            .unwrap()
            .join()
            .unwrap()
    }

    #[test]
    fn the_empty_pin_list_decodes() {
        let v = decode(b"con-ron-pins/1\nend 0\n").ok().unwrap();
        assert_eq!(v.len(), 0);
    }

    #[test]
    fn the_embedded_text_decodes_to_three_variants() {
        let n = on_a_big_stack(|| match decode_embedded() {
            Ok(v) => v.len(),
            Err(_) => 0,
        });
        assert_eq!(n, 3);
    }

    /// The toolchain strings, the one field of a variant a human reads: the
    /// decline message names them.
    #[test]
    fn the_variants_are_the_three_pinned_toolchains() {
        let names = on_a_big_stack(|| {
            let v = decode_embedded().ok().unwrap();
            let mut out: Vec<String> = Vec::new();
            for s in v.iter() {
                let mut t = String::new();
                for c in s.toolchain.iter() {
                    t.push(char::from_u32(*c).unwrap());
                }
                out.push(t);
            }
            out
        });
        assert_eq!(names.len(), 3);
        assert_eq!(names[0], "leanprover/lean4:v4.33.0");
        assert!(names[2].contains("nightly"));
    }

    /// A text that is not this writer's output is rejected, not half-read: a
    /// wrong header, a wrong footer count, a `D` record (a declaration dump's
    /// payload), an id that is not the next one, a forward reference, content
    /// after the footer and a missing final newline.
    #[test]
    fn malformed_texts_are_rejected() {
        assert!(decode(b"con-ron-pins/2\nend 0\n").is_err());
        assert!(decode(b"con-ron-pins/1\nend 1\n").is_err());
        assert!(decode(b"con-ron-pins/1\nD a 0\nend 0\n").is_err());
        assert!(decode(b"con-ron-pins/1\nN 1 a\nend 0\n").is_err());
        assert!(decode(b"con-ron-pins/1\nN 0 s 0 1 a\nend 0\n").is_err());
        assert!(decode(b"con-ron-pins/1\nend 0\nN 0 a\n").is_err());
        assert!(decode(b"con-ron-pins/1\nend 0").is_err());
        // a string field whose declared length disagrees with its text
        assert!(decode(b"con-ron-pins/1\nN 0 a\nN 1 s 0 2 a\nend 0\n").is_err());
    }

    /// An index field wider than `u32` is rejected at the cast rather than
    /// truncated (task #64).  On this 64-bit host every one of these texts
    /// would have been rejected anyway — a truncated id fails `expect_id`'s
    /// comparison, a truncated length fails the cross-check — which is the
    /// point: the guard is free here, and it is what makes the decoder refine
    /// `ConRon.Dump.parsePins` on a 32-bit target too, where `4294967296`
    /// would otherwise truncate to `0` and *pass* `expect_id(_, _, 0)`.
    #[test]
    fn an_index_wider_than_u32_is_rejected() {
        assert!(decode(b"con-ron-pins/1\nN 4294967296 a\nend 0\n").is_err());
        assert!(decode(b"con-ron-pins/1\nN 0 a\nN 1 s 0 4294967296 x\nend 0\n").is_err());
        assert!(decode(b"con-ron-pins/1\nend 4294967296\n").is_err());
        // the largest value the guard still admits is read, not rejected at
        // the cast (it fails later, on the id comparison)
        assert!(decode(b"con-ron-pins/1\nN 4294967295 a\nend 0\n").is_err());
    }

    /// The escape of FORMAT.md §3, the part of the format a byte reader has to
    /// get right: a space inside a name component, a backslash and a code
    /// point above the BMP all come back.
    #[test]
    fn the_string_escape_round_trips() {
        let t = b"con-ron-pins/1\nN 0 a\nN 1 s 0 3 a\\20;b\nN 2 s 1 1 \\5c;\nN 3 s 2 1 \\10ffff;\nend 0\n";
        assert!(decode(t).is_ok());
        // ... and an escape that is not a code point does not
        let bad = b"con-ron-pins/1\nN 0 a\nN 1 s 0 1 \\d800;\nend 0\n";
        assert!(decode(bad).is_err());
    }
}
