//! Port of `ConLeche/Kernel/Name.lean` — hierarchical names.
//!
//! Brought into the crate at task #9 from the task-#3 scale spike (`spikes/`, removed at task #76),
//! which stays untouched as task #3's recorded evidence; this copy is the
//! living code, and it additionally carries the `crate::ron::hashmap`
//! dictionaries (`Hashable`, `Eq2`) at the end of the file.
//!
//! Representation notes (DESIGN.md §3.2, §3.3):
//! * a `Name` is a `P` tree; the `@[computed_field] hashData` of the Lean
//!   inductive is the stored `NameNode::hash`, written by the smart
//!   constructors below and by nothing else;
//! * strings are `Vec<u32>` code points, not `String`: the checker only ever
//!   compares and hashes them, and Aeneas's `String` support is thin;
//! * every function takes its `Name` arguments by shared reference and
//!   returns owned `Name`s, because Rust cannot pattern-match through an
//!   a handle and therefore cannot give back a borrowed subterm.

use crate::ron::hashmap::Eq2;
use crate::ron::hashmap::Hashable;
use crate::ron::ptr;
use crate::ron::ptr::P;

/// con-leche: ConLeche/Kernel/Name.lean:26-45 Name
/// The three constructors of `inductive Name`; the cached hash they carry
/// in Lean's `@[computed_field]` sits in `NameNode` (DESIGN.md §3.2).
pub enum NameKind {
    Anonymous,
    Str(Name, Vec<u32>),
    Num(Name, u64),
}

/// con-leche: ConLeche/Kernel/Name.lean:26-45 Name
/// The heap node of a `Name`: the cited inductive's `@[computed_field]
/// hashData` beside the constructor data.
pub struct NameNode {
    pub hash: u64,
    pub kind: NameKind,
}

/// con-leche: ConLeche/Kernel/Name.lean:26-45 Name
/// A hierarchical name: a `P` tree, Lean's value semantics made sharing
/// (DESIGN.md §3.2).
pub struct Name(pub P<NameNode>);

/// con-leche: none — Lean's `mixHash`, a runtime primitive, not a con-leche definition
/// Lean's `mixHash`, i.e. the runtime's `lean_uint64_mix_hash`
/// (`include/lean/lean.h:2036`, a MurmurHash2 64-bit mix step).
pub fn mix_hash(h: u64, k: u64) -> u64 {
    let m: u64 = 0xc6a4a7935bd1e995;
    let k1: u64 = k.wrapping_mul(m);
    let k2: u64 = k1 ^ (k1 >> 47);
    let k3: u64 = k2 ^ m;
    let h1: u64 = h ^ k3;
    h1.wrapping_mul(m)
}

/// con-leche: none — Lean's `hash : String → UInt64`, a runtime primitive; see below for why any function of the value will do
/// Lean's `hash : String → UInt64`.  The runtime hashes the UTF-8 bytes
/// (`lean_string_hash`, not inlineable from the toolchain headers); we hash
/// the code points instead.  Hash values are verdict-neutral (DESIGN.md §3.2:
/// `mixHash` is opaque in the proofs, the hash guard in `beq` is provably
/// redundant, and hashes only move memo entries between buckets), so this is
/// a free choice — it must simply be *a* function of the value.
pub fn str_hash(s: &Vec<u32>) -> u64 {
    str_hash_from(s, 0, 11)
}

/// con-leche: none — the tail-recursive fold behind `str_hash`; Lean has no counterpart
/// No loops (DESIGN.md §3.4).
pub fn str_hash_from(s: &Vec<u32>, i: usize, acc: u64) -> u64 {
    if i >= s.len() {
        acc
    } else {
        str_hash_from(s, i + 1, mix_hash(acc, s[i] as u64))
    }
}

/// con-leche: none — Lean's `hash : Nat → UInt64`, a runtime primitive
/// On the indices that DESIGN.md §3.3 makes
/// `u64`: the identity, as `Nat.hash` is for machine-sized naturals.
pub fn nat_hash(n: u64) -> u64 {
    n
}

/// con-leche: ConLeche/Kernel/Name.lean:26-45 Name
/// The cached `@[computed_field] hashData`, an `O(1)` field read.
pub fn hash_data(n: &Name) -> u64 {
    n.0.hash
}

/// con-leche: ConLeche/Kernel/Name.lean:26-45 Name
/// `Name.anonymous`, hash `1723`.
pub fn anonymous() -> Name {
    Name(ptr::new(NameNode { hash: 1723, kind: NameKind::Anonymous }))
}

/// con-leche: ConLeche/Kernel/Name.lean:26-45 Name
/// `Name.str`; the smart constructor computes the cited computed-field
/// equation `mixHash (mixHash 1 p.hashData) (hash s)`, which in Lean the
/// elaborator writes for you.
pub fn mk_str(pre: Name, s: Vec<u32>) -> Name {
    let h: u64 = mix_hash(mix_hash(1, hash_data(&pre)), str_hash(&s));
    Name(ptr::new(NameNode { hash: h, kind: NameKind::Str(pre, s) }))
}

/// con-leche: ConLeche/Kernel/Name.lean:26-45 Name
/// `Name.num`; the smart constructor computes the cited computed-field
/// equation `mixHash (mixHash 2 p.hashData) (hash n)`.
pub fn mk_num(pre: Name, n: u64) -> Name {
    let h: u64 = mix_hash(mix_hash(2, hash_data(&pre)), nat_hash(n));
    Name(ptr::new(NameNode { hash: h, kind: NameKind::Num(pre, n) }))
}

/// con-leche: none — the `P` bump that Lean's value semantics hides (DESIGN.md §3.2)
/// Share a name.
pub fn dup(n: &Name) -> Name {
    Name(ptr::clone(&n.0))
}

/// con-leche: ConLeche/Kernel/Name.lean:51-59 Name.beqPtr
/// The pointer test behind the cited `withPtrEq`.  Deviation: modeled as
/// `false` in the generated Lean (DESIGN.md §3.2), where Lean discharges
/// `withPtrEq`'s obligation instead.
pub fn ptr_eq(a: &Name, b: &Name) -> bool {
    ptr::ptr_eq(&a.0, &b.0)
}

/// con-leche: none — `String` equality; strings are `Vec<u32>` code points here (DESIGN.md §3.3)
/// Code-point string equality.
pub fn str_eq(a: &Vec<u32>, b: &Vec<u32>) -> bool {
    if a.len() != b.len() {
        false
    } else {
        str_eq_from(a, b, 0)
    }
}

/// con-leche: none — the index recursion behind `str_eq`
/// No loops (DESIGN.md §3.4).
pub fn str_eq_from(a: &Vec<u32>, b: &Vec<u32>, i: usize) -> bool {
    if i >= a.len() {
        true
    } else if a[i] != b[i] {
        false
    } else {
        str_eq_from(a, b, i + 1)
    }
}

/// con-leche: ConLeche/Kernel/Name.lean:51-59 Name.beqPtr
/// con-leche: ConLeche/Kernel/Name.lean:70-74 Name.beq
/// `Name.beqPtr` is the *executed* `Name.beq` (`@[csimp]`-substituted):
/// pointer, then the cached hash, then the structural walk.  Deviation:
/// unlike Lean's `decide (a = b)` the descent keeps the pointer fast path
/// at every level; DESIGN.md §3.2's reflexivity obligation is what makes
/// that transparent.
pub fn beq(a: &Name, b: &Name) -> bool {
    if ptr_eq(a, b) {
        true
    } else if hash_data(a) != hash_data(b) {
        false
    } else {
        match (&a.0.kind, &b.0.kind) {
            (NameKind::Anonymous, NameKind::Anonymous) => true,
            (NameKind::Str(p, s), NameKind::Str(q, t)) => beq(p, q) && str_eq(s, t),
            (NameKind::Num(p, m), NameKind::Num(q, n)) => beq(p, q) && m == n,
            _ => false,
        }
    }
}

/// con-leche: none — `List.contains` on names, from index `i` on; `List` is a `Vec` walked by index (DESIGN.md §3.3)
/// Lean writes `ns.contains n`.
pub fn contains_from(ns: &Vec<Name>, i: usize, n: &Name) -> bool {
    if i >= ns.len() {
        false
    } else if beq(&ns[i], n) {
        true
    } else {
        contains_from(ns, i + 1, n)
    }
}

/// con-leche: none — `List.contains` on names
/// The entry point of the index recursion above.
pub fn contains(ns: &Vec<Name>, n: &Name) -> bool {
    contains_from(ns, 0, n)
}

/// con-leche: none — a one-element `Vec` for the `[p]` literal in `Level.byCases`
/// A one-element name list.
pub fn singleton(n: &Name) -> Vec<Name> {
    let mut v: Vec<Name> = Vec::new();
    v.push(dup(n));
    v
}

/* Not ported here:
   * `Name.ofLeanName` (Name.lean:189) — frontend only, outside the theorem. */

// ---------------------------------------------------------------------------
// Display rendering (`Name.lean:95-219`)
// ---------------------------------------------------------------------------
//
// Everything the checker prints that comes from the input — names, raw
// strings — goes through `DisplayAcc`, so no input reaches the terminal (or a
// CI log, where a line starting with `::` is a workflow command) as a control
// sequence, an invisible character or a spoofed separator.  Inside the
// delimiters of a quoted component or string, `\` is written `\\` and every
// *unsafe* character (`display_unsafe_char`), and the closing delimiter, as
// `\u{XXXX}` (upper-case hex, at least four digits).  A rendering is capped at
// `display_max_len()` characters; what does not fit is replaced by
// `…[N more characters]`.  A message decides no verdict (DESIGN.md §3.1), so
// the refinement relates none of this; it is ported so that the port prints
// what con-leche prints.

/// con-leche: none — the range test `lo ≤ v && v ≤ hi` of the predicates below
/// One range test, so that each predicate below is a linear `if` chain (a
/// chain of `||` is a tree of continuations in the generated model).
pub fn display_in_range(v: u32, lo: u32, hi: u32) -> bool {
    lo <= v && v <= hi
}

/// con-leche: ConLeche/Kernel/Name.lean:113-124 Display.unsafeChar
/// The characters a display never prints raw: Unicode's control (Cc) and
/// format (Cf, Unicode 15.1) characters, the line and paragraph separators
/// (Zl, Zp) and every space separator (Zs) other than the ASCII space.
/// Deviation: a `u32` that is not a Unicode scalar value (a surrogate, or past
/// `0x10FFFF`) is unsafe too.  A Lean `Char` cannot hold one; a `Vec<u32>`
/// component can, and the driver's conversion to a Rust `String` would drop it
/// silently (DESIGN.md §3.3).
pub fn display_unsafe_char(v: u32) -> bool {
    if v < 0x20 {
        true
    } else if display_in_range(v, 0x7F, 0xA0) {
        true
    } else if v == 0xAD {
        true
    } else if display_in_range(v, 0x600, 0x605) {
        true
    } else if v == 0x61C {
        true
    } else if v == 0x6DD {
        true
    } else if v == 0x70F {
        true
    } else if display_in_range(v, 0x890, 0x891) {
        true
    } else if v == 0x8E2 {
        true
    } else if v == 0x1680 {
        true
    } else if v == 0x180E {
        true
    } else if display_in_range(v, 0x2000, 0x200F) {
        true
    } else if display_in_range(v, 0x2028, 0x202F) {
        true
    } else if display_in_range(v, 0x205F, 0x2064) {
        true
    } else if display_in_range(v, 0x2066, 0x206F) {
        true
    } else if v == 0x3000 {
        true
    } else if display_in_range(v, 0xD800, 0xDFFF) {
        true
    } else if v == 0xFEFF {
        true
    } else if display_in_range(v, 0xFFF9, 0xFFFB) {
        true
    } else if v == 0x110BD {
        true
    } else if v == 0x110CD {
        true
    } else if display_in_range(v, 0x13430, 0x1343F) {
        true
    } else if display_in_range(v, 0x1BCA0, 0x1BCA3) {
        true
    } else if display_in_range(v, 0x1D173, 0x1D17A) {
        true
    } else if v == 0xE0001 {
        true
    } else if display_in_range(v, 0xE0020, 0xE007F) {
        true
    } else if v > 0x10FFFF {
        true
    } else {
        false
    }
}

/// con-leche: ConLeche/Kernel/Name.lean:126 Display.maxLen
/// The cap on one rendering, in characters (before the marker).
pub fn display_max_len() -> u64 {
    512
}

/// con-leche: ConLeche/Kernel/Name.lean:129-131 Display.codeEscape
/// `\u{XXXX}`: the code point in upper-case hex, at least four digits.  The
/// cited `Nat.toDigits 16` padded by `List.replicate (4 - ds.length) '0'` is
/// the digit count `display_hex_width` and the nibble recursion
/// `display_hex_from`.
pub fn display_code_escape(c: u32) -> Vec<u32> {
    const OPEN: [u32; 3] = [92, 117, 123];
    let out = display_hex_from(c, display_hex_width(c), crate::kernel::core_types::code_points(&OPEN));
    let mut out = out;
    out.push(125);
    out
}

/// con-leche: none — `max 4 (Nat.toDigits 16 v).length` for a `u32`
/// The number of hex digits `display_code_escape` writes.
pub fn display_hex_width(v: u32) -> u32 {
    if v < 0x10000 {
        4
    } else if v < 0x100000 {
        5
    } else if v < 0x1000000 {
        6
    } else if v < 0x10000000 {
        7
    } else {
        8
    }
}

/// con-leche: none — the digit walk of `Nat.toDigits 16`, upper-cased
/// Pushes the low `k` hex digits of `v`, most significant first.
pub fn display_hex_from(v: u32, k: u32, out: Vec<u32>) -> Vec<u32> {
    if k == 0 {
        out
    } else {
        let d: u32 = (v >> (4 * (k - 1))) & 15;
        let mut o = out;
        if d < 10 {
            o.push(48 + d);
        } else {
            o.push(55 + d);
        }
        display_hex_from(v, k - 1, o)
    }
}

/// con-leche: ConLeche/Kernel/Name.lean:135-139 Display.Acc
/// A capped rendering under construction: the output, its length, the input
/// characters dropped since the cap was reached, and whether it was.
pub struct DisplayAcc {
    pub out: Vec<u32>,
    pub len: u64,
    pub dropped: u64,
    pub full: bool,
}

/// con-leche: ConLeche/Kernel/Name.lean:135-139 Display.Acc
/// `Display.Acc.mk "" 0 0 false`, the empty rendering.
pub fn display_acc_empty() -> DisplayAcc {
    DisplayAcc { out: Vec::new(), len: 0, dropped: 0, full: false }
}

/// con-leche: ConLeche/Kernel/Name.lean:143-146 Display.Acc.piece
/// Appends `p`, which stands for `raw` characters of the input, unless the
/// cap is reached; past the cap only the count grows.
pub fn display_acc_piece(a: DisplayAcc, p: &Vec<u32>, raw: u64) -> DisplayAcc {
    let n = p.len() as u64;
    if a.full || a.len + n > display_max_len() {
        DisplayAcc { out: a.out, len: a.len, dropped: a.dropped + raw, full: true }
    } else {
        DisplayAcc {
            out: crate::frontend::text::cat(a.out, p),
            len: a.len + n,
            dropped: a.dropped,
            full: a.full,
        }
    }
}

/// con-leche: ConLeche/Kernel/Name.lean:143-146 Display.Acc.piece
/// `a.piece c.toString 1`: one input character, unescaped.
pub fn display_acc_char(a: DisplayAcc, c: u32) -> DisplayAcc {
    let mut p: Vec<u32> = Vec::new();
    p.push(c);
    display_acc_piece(a, &p, 1)
}

/// con-leche: ConLeche/Kernel/Name.lean:149-150 Display.Acc.chars
/// Appends characters that need no escaping (an identifier, a numeral).
pub fn display_acc_chars(a: DisplayAcc, s: &Vec<u32>) -> DisplayAcc {
    display_acc_chars_from(a, s, 0)
}

/// con-leche: none — the index recursion behind `display_acc_chars` (`String.foldl`)
pub fn display_acc_chars_from(a: DisplayAcc, s: &Vec<u32>, i: usize) -> DisplayAcc {
    if i >= s.len() {
        a
    } else {
        display_acc_chars_from(display_acc_char(a, s[i]), s, i + 1)
    }
}

/// con-leche: ConLeche/Kernel/Name.lean:154-158 Display.Acc.escaped
/// Appends the inside of a quoted component or string closed by `close`: `\`
/// doubled, `close` and the unsafe characters as `\u{XXXX}`.
pub fn display_acc_escaped(a: DisplayAcc, close: u32, s: &Vec<u32>) -> DisplayAcc {
    display_acc_escaped_from(a, close, s, 0)
}

/// con-leche: none — the index recursion behind `display_acc_escaped` (`String.foldl`)
pub fn display_acc_escaped_from(a: DisplayAcc, close: u32, s: &Vec<u32>, i: usize) -> DisplayAcc {
    if i >= s.len() {
        a
    } else {
        let c = s[i];
        let a1 = if c == 92 {
            const BACKSLASHES: [u32; 2] = [92, 92];
            display_acc_piece(a, &crate::kernel::core_types::code_points(&BACKSLASHES), 1)
        } else if c == close || display_unsafe_char(c) {
            display_acc_piece(a, &display_code_escape(c), 1)
        } else {
            display_acc_char(a, c)
        };
        display_acc_escaped_from(a1, close, s, i + 1)
    }
}

/// con-leche: ConLeche/Kernel/Name.lean:161-162 Display.Acc.finish
/// The rendering, with the elision marker when the cap was reached.
pub fn display_acc_finish(a: DisplayAcc) -> Vec<u32> {
    if a.full {
        // `…[`
        const PRE: [u32; 2] = [8230, 91];
        // ` more characters]`
        const POST: [u32; 17] = [
            32, 109, 111, 114, 101, 32, 99, 104, 97, 114, 97, 99, 116, 101, 114, 115, 93,
        ];
        let s = crate::frontend::text::cat3(
            a.out,
            &crate::kernel::core_types::code_points(&PRE),
            &crate::kernel::core_k::nat_to_dec(a.dropped),
        );
        crate::frontend::text::cat(s, &crate::kernel::core_types::code_points(&POST))
    } else {
        a.out
    }
}

/// con-leche: none — Lean's `isLetterLike` (`Init/Meta/Defs.lean`), on a code point
pub fn display_letter_like(v: u32) -> bool {
    if display_in_range(v, 0x3b1, 0x3c9) && v != 0x3bb {
        true
    } else if display_in_range(v, 0x391, 0x3A9) && v != 0x3A0 && v != 0x3A3 {
        true
    } else if display_in_range(v, 0x3ca, 0x3fb) {
        true
    } else if display_in_range(v, 0x1f00, 0x1ffe) {
        true
    } else if display_in_range(v, 0x2100, 0x214f) {
        true
    } else if display_in_range(v, 0x1d49c, 0x1d59f) {
        true
    } else if display_in_range(v, 0x00c0, 0x00ff) && v != 0x00d7 && v != 0x00f7 {
        true
    } else if display_in_range(v, 0x0100, 0x017f) {
        true
    } else {
        false
    }
}

/// con-leche: none — Lean's `isSubScriptAlnum` (`Init/Meta/Defs.lean`), on a code point
pub fn display_subscript_alnum(v: u32) -> bool {
    if display_in_range(v, 0x2080, 0x2089) {
        true
    } else if display_in_range(v, 0x2090, 0x209c) {
        true
    } else if display_in_range(v, 0x1d62, 0x1d6a) {
        true
    } else if v == 0x2c7c {
        true
    } else {
        false
    }
}

/// con-leche: none — Lean's `Char.isAlpha` (ASCII letters), on a code point
pub fn display_ascii_alpha(v: u32) -> bool {
    if display_in_range(v, 97, 122) {
        true
    } else if display_in_range(v, 65, 90) {
        true
    } else {
        false
    }
}

/// con-leche: none — Lean's `isIdFirst` (`Init/Meta/Defs.lean`), on a code point
pub fn display_id_first(v: u32) -> bool {
    if display_ascii_alpha(v) {
        true
    } else if v == 95 {
        true
    } else if display_letter_like(v) {
        true
    } else {
        false
    }
}

/// con-leche: none — Lean's `isIdRest` (`Init/Meta/Defs.lean`), on a code point
pub fn display_id_rest(v: u32) -> bool {
    if display_ascii_alpha(v) {
        true
    } else if display_in_range(v, 48, 57) {
        true
    } else if v == 95 {
        true
    } else if v == 39 {
        true
    } else if v == 33 {
        true
    } else if v == 63 {
        true
    } else if display_letter_like(v) {
        true
    } else if display_subscript_alnum(v) {
        true
    } else {
        false
    }
}

/// con-leche: ConLeche/Kernel/Name.lean:168-171 Display.idShaped
/// Whether a string component prints bare: Lean's own rule
/// (`Lean.Name.escapePart`) — a nonempty identifier, `isIdFirst` then
/// `isIdRest`.  No such component contains a `.`, a control, format or
/// separator character, a `«`, a `»` or a `\`.
pub fn display_id_shaped(s: &Vec<u32>) -> bool {
    if s.len() == 0 {
        false
    } else {
        display_id_first(s[0]) && display_id_rest_from(s, 1)
    }
}

/// con-leche: none — the index recursion behind `cs.all Lean.isIdRest`
pub fn display_id_rest_from(s: &Vec<u32>, i: usize) -> bool {
    if i >= s.len() {
        true
    } else if display_id_rest(s[i]) {
        display_id_rest_from(s, i + 1)
    } else {
        false
    }
}

/// con-leche: ConLeche/Kernel/Name.lean:176-178 Display.Acc.component
/// Pushes one component.  An identifier-shaped one bare; any other (including
/// the empty one, a numeral-looking one and one with a `.`) between `«`…`»`,
/// with `»` escaped like an unsafe character.
pub fn display_acc_component(a: DisplayAcc, s: &Vec<u32>) -> DisplayAcc {
    if display_id_shaped(s) {
        display_acc_chars(a, s)
    } else {
        const OPEN: [u32; 1] = [171];
        const CLOSE: [u32; 1] = [187];
        let a1 = display_acc_piece(a, &crate::kernel::core_types::code_points(&OPEN), 0);
        let a2 = display_acc_escaped(a1, 187, s);
        display_acc_piece(a2, &crate::kernel::core_types::code_points(&CLOSE), 0)
    }
}

/// con-leche: ConLeche/Kernel/Name.lean:183-184 Display.str
/// **The display rendering of a raw string from the input** (a `safety`
/// field, a quotient kind, a command-line word): between `"`…`"`, escaped and
/// capped like a quoted name component.
pub fn display_str(s: &Vec<u32>) -> Vec<u32> {
    const QUOTE: [u32; 1] = [34];
    let a1 = display_acc_piece(display_acc_empty(), &crate::kernel::core_types::code_points(&QUOTE), 0);
    let a2 = display_acc_escaped(a1, 34, s);
    let a3 = display_acc_piece(a2, &crate::kernel::core_types::code_points(&QUOTE), 0);
    display_acc_finish(a3)
}

/// con-leche: ConLeche/Kernel/Name.lean:196-199 componentList
/// One element of `componentList`'s `List (String ⊕ Nat)`.
pub enum NameComponent {
    Str(Vec<u32>),
    Num(u64),
}

/// con-leche: ConLeche/Kernel/Name.lean:196-199 componentList
/// The name's components.  Deviation: the cited walk conses each component
/// onto the front of a `List`, so its answer is root first; the port pushes
/// onto the END of a `Vec`, so the same walk leaves the components LEAF
/// first, and `render_from` reads them back from the end.
pub fn component_list(n: &Name, acc: Vec<NameComponent>) -> Vec<NameComponent> {
    match &n.0.kind {
        NameKind::Anonymous => acc,
        NameKind::Str(p, s) => {
            let mut acc = acc;
            acc.push(NameComponent::Str(crate::kernel::expr::str_copy(s)));
            component_list(p, acc)
        }
        NameKind::Num(p, k) => {
            let mut acc = acc;
            acc.push(NameComponent::Num(*k));
            component_list(p, acc)
        }
    }
}

/// con-leche: ConLeche/Kernel/Name.lean:207-217 render
/// **The one display rendering of a name** (con-leche's `ToString Name`):
/// the components joined by `.`, each bare when identifier-shaped and
/// otherwise `«…»` with its unsafe characters escaped (`DisplayAcc`), numeric
/// components as decimals, the anonymous name `[anonymous]`, the whole capped
/// at `display_max_len()` characters.  Display only: nothing compares, hashes
/// or parses the result.
pub fn render(n: &Name) -> Vec<u32> {
    match &n.0.kind {
        NameKind::Anonymous => {
            const A: [u32; 11] = [91, 97, 110, 111, 110, 121, 109, 111, 117, 115, 93];
            crate::kernel::core_types::code_points(&A)
        }
        _ => {
            let cs = component_list(n, Vec::new());
            let k = cs.len();
            display_acc_finish(render_from(&cs, k, display_acc_empty()))
        }
    }
}

/// con-leche: ConLeche/Kernel/Name.lean:207-217 render
/// The cited `foldl` over the components, root first: `component_list`'s
/// leaf-first `Vec` read from index `k - 1` down to `0`.  The `first` flag of
/// the cited fold is `k == cs.len()`.
pub fn render_from(cs: &Vec<NameComponent>, k: usize, a: DisplayAcc) -> DisplayAcc {
    if k == 0 {
        a
    } else {
        let a1 = if k == cs.len() {
            a
        } else {
            const DOT: [u32; 1] = [46];
            display_acc_piece(a, &crate::kernel::core_types::code_points(&DOT), 1)
        };
        let a2 = match &cs[k - 1] {
            NameComponent::Str(s) => display_acc_component(a1, s),
            NameComponent::Num(m) => display_acc_chars(a1, &crate::kernel::core_k::nat_to_dec(*m)),
        };
        render_from(cs, k - 1, a2)
    }
}

// ---------------------------------------------------------------------------
// The hash-map dictionaries (`crate::ron::hashmap`'s own traits, task #7)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/Name.lean:47-49 _
/// The cited `instance : Hashable Name := ⟨Name.hashData⟩`, as the key
/// dictionary of `crate::ron::hashmap`.  Deviation: `Hashable` is our own
/// one-method trait rather than Lean's class (task #7).
impl Hashable for Name {
    /// con-leche: ConLeche/Kernel/Name.lean:47-49 _
    /// The stored word, an `O(1)` field read.
    fn hash64(&self) -> u64 {
        hash_data(self)
    }
}

/// con-leche: ConLeche/Kernel/Name.lean:88 _
/// The cited `instance : BEq Name := ⟨Name.beq⟩`, as the key dictionary of
/// `crate::ron::hashmap`.  Deviation: `Eq2` is our own one-method trait rather
/// than `core::cmp::PartialEq` — which is exactly what lets the instance be
/// `beq` with its pointer and hash fast paths (DESIGN.md §3.2, task #7).
impl Eq2 for Name {
    /// con-leche: ConLeche/Kernel/Name.lean:70-74 Name.beq
    /// `Name.beq`, i.e. the `@[csimp]`-substituted `Name.beqPtr`.
    fn eq2(&self, other: &Self) -> bool {
        beq(self, other)
    }
}

#[cfg(test)]
mod tests {
    use crate::ron::hashmap::Eq2;
    use crate::ron::hashmap::Hashable;
    use crate::kernel::name;
    use crate::kernel::name::Name;

    /// A single `str` component under `anonymous` — `nm("foo")` is `` `foo ``.
    pub fn nm(s: &str) -> Name {
        let cs: Vec<u32> = s.chars().map(|c| c as u32).collect();
        name::mk_str(name::anonymous(), cs)
    }

    #[test]
    fn name_beq_is_structural() {
        let a = nm("foo");
        let b = nm("foo");
        let c = nm("bar");
        assert!(!name::ptr_eq(&a, &b));
        assert!(name::beq(&a, &b));
        assert!(!name::beq(&a, &c));
        assert_eq!(name::hash_data(&a), name::hash_data(&b));
    }

    #[test]
    fn the_hash_map_dictionaries_are_hash_data_and_beq() {
        let a = nm("foo");
        let b = nm("foo");
        assert!(a.eq2(&b));
        assert!(!a.eq2(&nm("bar")));
        assert_eq!(a.hash64(), name::hash_data(&b));
    }

    // ---- The display rendering: con-leche's `tests/ConLecheTests/DisplayTests.lean`
    // guard for guard (task #131).

    fn cps(s: &str) -> Vec<u32> {
        s.chars().map(|c| c as u32).collect()
    }

    fn st(v: &[u32]) -> String {
        v.iter().map(|c| char::from_u32(*c).unwrap()).collect()
    }

    /// A name from its string components, root first.
    fn mk(cs: &[&str]) -> Name {
        let mut n = name::anonymous();
        for c in cs {
            n = name::mk_str(n, cps(c));
        }
        n
    }

    fn r(n: &Name) -> String {
        st(&name::render(n))
    }

    fn clean(s: &str) -> bool {
        !s.chars().any(|c| name::display_unsafe_char(c as u32))
    }

    #[test]
    fn ordinary_names_print_as_lean_does() {
        assert_eq!(r(&mk(&["Nat", "add_comm"])), "Nat.add_comm");
        assert_eq!(r(&mk(&["α₁", "ℕ", "x'", "h?", "ok!"])), "α₁.ℕ.x'.h?.ok!");
        assert_eq!(r(&mk(&["_private"])), "_private");
        assert_eq!(r(&name::anonymous()), "[anonymous]");
        assert_eq!(r(&mk(&["[anonymous]"])), "«[anonymous]»");
    }

    #[test]
    fn numeric_components_and_separators() {
        assert_eq!(r(&name::mk_num(mk(&["x"]), 3)), "x.3");
        assert_eq!(r(&mk(&["x", "3"])), "x.«3»");
        assert_eq!(r(&name::mk_num(name::anonymous(), 7)), "7");
        assert_eq!(r(&mk(&["a.b"])), "«a.b»");
        assert_eq!(r(&mk(&["a", "b"])), "a.b");
        assert_eq!(r(&mk(&["«x»"])), "««x\\u{00BB}»");
        assert_eq!(r(&mk(&["a\\u{001B}"])), "«a\\\\u{001B}»");
        assert_eq!(r(&mk(&[""])), "«»");
    }

    #[test]
    fn controls_and_invisibles_are_escaped() {
        assert_eq!(r(&mk(&["a\x1b[31mb"])), "«a\\u{001B}[31mb»");
        assert_eq!(r(&mk(&["c\nd\re"])), "«c\\u{000A}d\\u{000D}e»");
        assert_eq!(r(&mk(&["\x7f\u{85}"])), "«\\u{007F}\\u{0085}»");
        assert_eq!(r(&mk(&["admin\u{202e}txt.exe"])), "«admin\\u{202E}txt.exe»");
        assert_eq!(r(&mk(&["a\u{200b}b"])), "«a\\u{200B}b»");
        assert_eq!(
            r(&mk(&["\u{2066}\u{2069}\u{200e}\u{200f}\u{61c}"])),
            "«\\u{2066}\\u{2069}\\u{200E}\\u{200F}\\u{061C}»"
        );
        assert_eq!(r(&mk(&["\u{feff}\u{2060}\u{200d}"])), "«\\u{FEFF}\\u{2060}\\u{200D}»");
        assert_eq!(r(&mk(&["a\u{a0}b"])), "«a\\u{00A0}b»");
        assert_eq!(r(&mk(&["tag\u{e0041}"])), "«tag\\u{E0041}»");
        assert_eq!(r(&mk(&["a b"])), "«a b»");
        assert_eq!(r(&mk(&["ok\n::error::pwned"])), "«ok\\u{000A}::error::pwned»");
        assert!(clean(&r(&mk(&["ok\n::error::pwned", "\x1b]0;t\x07"]))));
    }

    /// The port's own deviation: a code point no `char` can hold is escaped.
    #[test]
    fn non_scalar_code_points_are_escaped() {
        let n = name::mk_str(name::anonymous(), vec![0x61, 0xD800, 0x110000]);
        assert_eq!(r(&n), "«a\\u{D800}\\u{110000}»");
    }

    #[test]
    fn the_cap() {
        let x600: String = "x".repeat(600);
        assert_eq!(r(&mk(&[&x600])), format!("{}…[88 more characters]", "x".repeat(512)));
        let e600: String = "\x1b".repeat(600);
        assert!(r(&mk(&[&e600])).chars().count() <= 512 + 30);
        let abs: Vec<&str> = vec!["ab"; 1000];
        assert!(r(&mk(&abs)).ends_with("…[2487 more characters]"));
    }

    #[test]
    fn raw_strings() {
        assert_eq!(st(&name::display_str(&cps("unsafe"))), "\"unsafe\"");
        assert_eq!(
            st(&name::display_str(&cps("a\x1b[1;32m\n\"b\"\\"))),
            "\"a\\u{001B}[1;32m\\u{000A}\\u{0022}b\\u{0022}\\\\\""
        );
        assert!(clean(&st(&name::display_str(&cps("\x1b[2K\rcon-leche: accepted\n::error::x")))));
    }
}
