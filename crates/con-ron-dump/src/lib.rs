//! The Rust reader (test-only) and writer for the `con-ron-pins/2` dump format
//! (DESIGN.md §3.6, task #31; `proof/ConRon/Dump/FORMAT.md` specifies it and
//! `proof/ConRon/Dump/Pins.lean` is the Lean writer this file mirrors
//! function for function).
//!
//! A pin dump is con-leche's `natOpPinSets` as text: three `S` records, one
//! per pinned toolchain, over the shared `N`/`L`/`E` DAG of the `Expr`s
//! they name.  `scripts/gen-pins.sh` wraps those bytes in the verified core's
//! embedded `kernel::pins_text::PINS_TEXT`, which the verified core decodes
//! (`kernel::pins_decode::decode`, in DESIGN.md §3.4's subset).  The reader
//! here (`read`, test-only) is the oracle that decoder and the writer
//! (`write`) are tested against.
//!
//! **The declaration dump is gone (task #80).**  Until then this crate also
//! carried `con-ron-decls/1`, the `List Declaration` format of task #10, which fed
//! the checker-only differential seam (`con-ron-check`, `con-ron-dump-check`,
//! `scripts/diff-fixtures.sh`).  `scripts/diff-e2e.sh` runs the whole binary
//! on every fixture's raw export against con-leche's own expectations and
//! subsumes that seam, so the format and its two readers were retired and
//! what is left is the pins half, which nothing subsumes: it is what
//! `gen-pins.sh` speaks.
//!
//! **This crate is NOT part of the verified core.**  It sits outside
//! `crates/con-ron-core` on purpose: it is test and porting infrastructure,
//! Charon never sees it, no refinement lemma mentions it, and DESIGN.md §3.4's
//! Aeneas subset does not apply — `for`, `while`, `?`, `std::collections`,
//! `derive(Debug)` and closures are all used freely below.  What *is* still
//! forbidden is `unsafe` (there is none) and reaching into the core's
//! representation: every value is built through the core's own constructors,
//! so the terms this reader produces are exactly the terms the core builds
//! for itself, with the same `@[computed_field]` words.
//!
//! Two properties FORMAT.md §6 asks for and this reader delivers:
//!
//! * **The DAG stays a DAG.**  `N`, `L` and `E` records are interned by
//!   the writer, so each shared subterm appears once; the reader builds each
//!   such node once, pushes it onto the `Vec` for its id space, and every
//!   later reference hands back a `clone` of the `Rc` handle
//!   (`name::dup`/`level::dup`/`expr::dup`).  The in-memory term is therefore
//!   the same DAG the Lean side had, not its tree expansion — which matters:
//!   as a tree the v4.33.0 pin variant is 5.1 M nodes.
//! * **Computed fields are recomputed, never read off the file.**  The
//!   constructors (`name::mk_str`, `level::succ`, `expr::app`, …) are the only
//!   way a node is made here, and they are what write `NameNode::hash`,
//!   `LevelNode::hash` and `ExprNode::data`.  The hash *bits* of
//!   `ExprNode::data` differ from Lean's by design (DESIGN.md task #3, note 6)
//!   and nothing compares them.
//!
//! Deviations from the Lean reader, deliberate and tested:
//!
//! * ids, lengths and the `bvar`/`fvar`/`proj`/`Name.num` indices are `u64`
//!   (DESIGN.md §3.3), so a dump that overflows one is a *reader* failure with
//!   a line number rather than a bignum;
//! * `Literal.natVal` goes through [`natdec::from_decimal`], the crate's own
//!   decimal parser — `ron::Nat` has none and DESIGN.md §3.4 says not to grow
//!   the core for tooling's sake;
//! * a literal byte inside a string field must be printable non-backslash
//!   ASCII (`0x21..=0x7e`, not `0x5c`).  The Lean reader accepts any non-`\`
//!   character there; the format never produces one, so rejecting it is the
//!   loud failure FORMAT.md §6 wants.  The degenerate escape `\;` (no hex
//!   digits, i.e. `U+0000`) is accepted exactly as the Lean reader accepts it.
//!
//! The reader is one forward pass: four `Vec`s that only ever grow by one, and
//! every reference an index into a `Vec` that is already long enough.  No
//! fixups, no cycles, no recursion over the term (the `E` records are already
//! topologically sorted, so the reader needs no worklist either — the writer's
//! is enough).  What the reader's resident set *is*, after that, is the terms
//! themselves: the `node_sizes` test pins what one node of each kind weighs.

// ---------------------------------------------------------------------------
// The global allocator (task #35).
//
// glibc `malloc`/`free` was a third of `init`'s instructions (task #34's
// profile: `__libc_malloc2` 15.1 %, `_int_free_chunk` 11.7 %, plus the
// surrounding glue), and the checker's traffic is exactly what a modern
// thread-caching allocator is built for: millions of small, short-lived
// `Rc<Node>`s, `Vec`s and `AList` cells on one thread.
//
// This attribute lives **here**, in the unverified `con-ron-dump` crate, and
// therefore applies to the `con-ron` binary, which links it.  It is invisible to the
// verified core: Charon extracts `con-ron-core` alone, the allocator is not a
// Rust item of that crate, and the Aeneas model has no heap to begin with
// (`Rc`/`Box`/`Vec` are modeled by their contents, DESIGN.md §3.2), so
// `proof/ConRon/Generated/*` is byte-identical whichever allocator is chosen.
// It cannot change the verdict either: the allocator only decides *where*
// bytes go, and the core reads no address (`ptr_eq` aside, which compares
// identity, not order).
//
// Which allocator that is, is **decided in `crates/con-ron/Cargo.toml`**
// (task #89): the binary takes this crate over a `default-features = false`
// edge and forwards features of the same names, so `cargo build --release` is
// mimalloc (it measured best on `init`), `--no-default-features` is glibc
// `malloc`, and `--no-default-features --features jemalloc` is jemalloc.  The
// `default = ["mimalloc"]` in this crate's own manifest governs only a build
// of this library on its own; task #88 §5 found the claim that the flag
// worked through this crate's default to be false as it then stood.
// `con-ron --help` prints `ALLOCATOR`, so a measured run can name its own.
/// **mimalloc, entered by `mi_malloc` rather than `mi_malloc_aligned`**
/// (task #92).
///
/// The `mimalloc` crate's own `GlobalAlloc` sends *every* request through
/// `mi_malloc_aligned(size, align)`, whatever the alignment is.  That is
/// correct but it costs twice over, and con-ron pays it on every node:
///
/// * **A size class.**  Measured resident bytes per live block (20 M blocks,
///   `VmHWM`, this machine, mimalloc v3 as `libmimalloc-sys` builds it):
///   through `mi_malloc` a 48-byte request occupies **48** bytes, through
///   `mi_malloc_aligned(48, 8)` it occupies **64**.  mimalloc's own bin for a
///   48-byte block is 48 and its stride keeps every block 16-aligned (audited:
///   100 000 `mi_malloc(48)` pointers, all 16-aligned), so the aligned wrapper
///   is being conservative about an alignment the plain bin already has.
/// * **A slow path.**  `mi_malloc_aligned` is a `noinline` function that
///   re-checks and may over-allocate; `mi_malloc` is the inlined fast path.
///   Measured on `_tmp/corpus/core.ndjson`, `--verified --jobs=1`: **−4.5 %
///   instructions, −5.6 % cycles, −7.4 % wall**, with peak RSS unchanged
///   (−0.2 %) because con-ron's *current* block sizes do not straddle a class
///   boundary — 56 and 64 are one class either way.  DESIGN.md's task-#92
///   entry has the table and the size-class measurements behind it.
///
/// The fallback is kept for `align > 16`.  Task #92 drew the line at 8,
/// because nothing con-ron allocated then was more aligned than a machine
/// word; tasks #94-#97-SWAP allocated `align(16)` blocks, whose low four bits
/// carried an `Expr`'s constructor, and drawing it at 8 would have sent every
/// `Expr` allocation down exactly the slow, class-losing path this type
/// exists to avoid.  **Task #97-SWAP-2 retired the tagged handle**, so
/// nothing depends on the alignment for soundness any more and the line at 16
/// is a size-class choice again; `mi_malloc_gives_16_aligned_blocks` below
/// still checks it, at the sizes con-ron allocates.
///
/// This is the same `unsafe impl GlobalAlloc` the `mimalloc` crate itself
/// writes, minus the one conservative branch; it is in the *unverified*
/// crate, invisible to Charon, and cannot change a verdict (see the note
/// above).
#[cfg(all(feature = "mimalloc", not(feature = "jemalloc")))]
pub struct MiMallocTight;

#[cfg(all(feature = "mimalloc", not(feature = "jemalloc")))]
unsafe impl std::alloc::GlobalAlloc for MiMallocTight {
    #[inline]
    unsafe fn alloc(&self, layout: std::alloc::Layout) -> *mut u8 {
        if layout.align() <= 16 {
            libmimalloc_sys::mi_malloc(layout.size()) as *mut u8
        } else {
            libmimalloc_sys::mi_malloc_aligned(layout.size(), layout.align()) as *mut u8
        }
    }

    #[inline]
    unsafe fn alloc_zeroed(&self, layout: std::alloc::Layout) -> *mut u8 {
        if layout.align() <= 16 {
            libmimalloc_sys::mi_zalloc(layout.size()) as *mut u8
        } else {
            libmimalloc_sys::mi_zalloc_aligned(layout.size(), layout.align()) as *mut u8
        }
    }

    #[inline]
    unsafe fn dealloc(&self, ptr: *mut u8, _layout: std::alloc::Layout) {
        libmimalloc_sys::mi_free(ptr as *mut std::ffi::c_void);
    }

    #[inline]
    unsafe fn realloc(
        &self,
        ptr: *mut u8,
        layout: std::alloc::Layout,
        new_size: usize,
    ) -> *mut u8 {
        if layout.align() <= 16 {
            libmimalloc_sys::mi_realloc(ptr as *mut std::ffi::c_void, new_size) as *mut u8
        } else {
            libmimalloc_sys::mi_realloc_aligned(
                ptr as *mut std::ffi::c_void,
                new_size,
                layout.align(),
            ) as *mut u8
        }
    }
}

#[cfg(all(feature = "mimalloc", not(feature = "jemalloc")))]
#[global_allocator]
static GLOBAL_ALLOC: MiMallocTight = MiMallocTight;

#[cfg(feature = "jemalloc")]
#[global_allocator]
static GLOBAL_ALLOC: tikv_jemallocator::Jemalloc = tikv_jemallocator::Jemalloc;

/// The name of the allocator this build uses, for `--version`-style output and
/// for the task-log numbers to be reproducible.
pub const ALLOCATOR: &str = if cfg!(feature = "jemalloc") {
    "jemalloc"
} else if cfg!(feature = "mimalloc") {
    "mimalloc"
} else {
    "system"
};

use con_ron_core::kernel::name;

#[cfg(test)]
mod dag;
pub mod natdec;
pub mod write;

pub use write::dump_pins;

/// The version header, the whole first line of a pin dump (`Pins.lean`'s
/// `pinsHeader`, FORMAT.md §1).
pub const PINS_HEADER: &str = "con-ron-pins/2";

#[cfg(test)]
mod read;
#[cfg(test)]
use read::*;

/// A token of the file being read, for an error message: the core's
/// `name::display_str` (con-leche's `Display.str`), so that no byte of a pins
/// file reaches the terminal raw (task #131).
pub fn shown(t: &str) -> String {
    let cs: Vec<u32> = t.chars().map(|c| c as u32).collect();
    name::display_str(&cs)
        .iter()
        .filter_map(|c| char::from_u32(*c))
        .collect()
}


// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use con_ron_core::kernel::expr;
    use con_ron_core::kernel::expr::Expr;
    use con_ron_core::kernel::expr::Literal;
    use con_ron_core::kernel::level::Level;
    use con_ron_core::ron::nat::Nat;
    use con_ron_core::kernel::name::Name;
    use con_ron_core::kernel::nat_op_pins::NatOpPinSet;
    use con_ron_core::ron::nat;
    use con_ron_core::ron::ptr::P;
    use con_ron_core::kernel::env::ConstantInfo;
    use con_ron_core::kernel::env::ConstantVal;
    use con_ron_core::kernel::expr::ExprKind;
    use con_ron_core::kernel::expr::ExprNode;
    use con_ron_core::kernel::level::LevelKind;
    use con_ron_core::kernel::level::LevelNode;
    use con_ron_core::kernel::name::NameKind;
    use con_ron_core::kernel::name::NameNode;

    // ---------------------------------------------------------------------------
    // What a node weighs (task #36; test-only since task #105, when nothing but
    // `the_node_sizes_are_what_the_accounting_assumes` read it any more)
    // ---------------------------------------------------------------------------

    /// How many machine words a counted pointer's heap block carries in front of
    /// the value.  One impl per pointer the core may be aliased to
    /// (`ron::ptr::P`, task #44), so `--sizes` follows the alias with no edit
    /// here: two words for `std::rc::Rc` and `std::sync::Arc` (a strong and a
    /// weak count), one for a single-count pointer.  This is a *fact about the
    /// standard library's layout*, restated here because the block type is
    /// private; nothing reads it but the size report.
    trait CountHeader {
        const WORDS: usize;
    }

    impl<T> CountHeader for std::rc::Rc<T> {
        const WORDS: usize = 2;
    }

    impl<T> CountHeader for std::sync::Arc<T> {
        const WORDS: usize = 2;
    }

    /// `P<T>`'s heap block: the reference counts in front of the value
    /// (`alloc::rc::RcInner`/`alloc::sync::ArcInner`, `#[repr(C)] { strong,
    /// weak, value }`).  This is a *model* of that private type, used only to
    /// report a size — nothing is allocated through it and no pointer is cast to
    /// it.  The header width is the alias's own, so swapping `ron::ptr::P`
    /// (task #44) moves the reported node size with it.
    /// The header width of the alias in force.  Not generic in the payload: the
    /// counts sit in front of any `T`.
    const P_HEADER_WORDS: usize = <P<u8> as CountHeader>::WORDS;

    #[repr(C)]
    #[allow(dead_code)]
    struct PBlock<T> {
        header: [usize; P_HEADER_WORDS],
        value: T,
    }

    /// One row of the size report: a type, its `size_of`, and — for a type the
    /// core holds behind an `Rc` — what one heap block of it costs including the
    /// two counts.  `heap == 0` means the type is stored inline, in its owner.
    #[derive(Debug, Clone, Copy, PartialEq, Eq)]
    struct NodeSize {
        what: &'static str,
        size: usize,
        heap: usize,
    }

    /// **What the core's terms weigh, per node** (DESIGN.md tasks #36, #38, #90
    /// and #94).  At Mathlib scale these are multiplied by 103 M.
    ///
    /// **Task #97-SWAP-2 put the row back.**  Tasks #94-#97-SWAP split it: the
    /// kind lived in the handle and each constructor had a cell of its own size,
    /// which bought 32 bytes for an `app` against 64.  That representation cost
    /// the verified crate its only `unsafe`, and task #97-SWAP measured that the
    /// checking path builds no `Expr` at all — the arena's own records do — so it
    /// was retired.  A node is one `ExprNode` as wide as the widest `ExprKind`
    /// arm again, behind a `P` whose two counts make the heap block.  The rows
    /// below are the real structs, and the test pins them, so a further
    /// repacking shows up here with its saving attached.
    fn node_sizes() -> Vec<NodeSize> {
        fn row<T>(what: &'static str, rc: bool) -> NodeSize {
            NodeSize {
                what,
                size: std::mem::size_of::<T>(),
                heap: if rc { std::mem::size_of::<PBlock<T>>() } else { 0 },
            }
        }
        vec![
            row::<ExprNode>("ExprNode (data + kind)", true),
            row::<ExprKind>("  ExprKind", false),
            row::<(Expr, Expr)>("    app payload", false),
            row::<(Name, P<Vec<Level>>)>("    const payload", false),
            row::<Literal>("    lit payload", false),
            row::<(Expr, Expr)>("    lam/forallE payload", false),
            row::<(Expr, Expr, Expr)>("    letE payload", false),
            row::<(Name, u64, Expr)>("    proj payload", false),
            row::<NameNode>("NameNode (hash + kind)", true),
            row::<NameKind>("  NameKind", false),
            row::<LevelNode>("LevelNode (hash + kind)", true),
            row::<LevelKind>("  LevelKind", false),
            row::<Vec<u32>>("Vec<u32> (a string's header)", false),
            row::<Nat>("Nat (limb Vec header)", false),
            row::<ConstantInfo>("ConstantInfo (inline)", false),
            row::<ConstantVal>("ConstantVal (inline)", false),
        ]
    }

    /// The `P` heap block of an `ExprNode` — the reader's dominant cost, one per
    /// `E` record.  Separate from [`node_sizes`] so a caller can multiply it by
    /// the record count without searching the table.
    fn expr_node_bytes() -> usize {
        std::mem::size_of::<PBlock<ExprNode>>()
    }

    fn nm(s: &str) -> Name {
        let cps: Vec<u32> = s.chars().map(|c| c as u32).collect();
        name::mk_str(name::anonymous(), cps)
    }

    fn cps(s: &str) -> Vec<u32> {
        s.chars().map(|c| c as u32).collect()
    }

    /// The error of a failed parse.  `unwrap_err` is unavailable:
    /// `NatOpPinSet` does not derive `Debug` (DESIGN.md §3.4).
    fn pins_err(text: &str) -> String {
        match parse_pins(text) {
            Ok(_) => panic!("this dump must not parse"),
            Err(e) => e,
        }
    }

    /// A pin variant whose eight pins and sixteen proof blobs are distinct
    /// terms, plus one node deliberately *shared* between two of them: the
    /// sharing is what FORMAT.md §2 is for, so the round trip has to keep it.
    fn a_pin_set(tag: &str) -> NatOpPinSet {
        let shared = expr::app(
            expr::mk_const(nm("Nat.rec"), Vec::new()),
            expr::mk_const(nm("Nat.zero"), Vec::new()),
        );
        let p = |i: u64| expr::app(expr::dup(&shared), expr::bvar(i));
        NatOpPinSet {
            toolchain: cps(tag),
            div_pin: p(0),
            mod_pin: p(1),
            gcd_pin: p(2),
            land_pin: p(3),
            lor_pin: p(4),
            xor_pin: p(5),
            shift_left_pin: p(6),
            shift_right_pin: p(7),
            div_proofs: vec![p(8), p(9)],
            mod_proofs: vec![p(10)],
            gcd_proofs: Vec::new(),
            land_proofs: vec![p(11)],
            lor_proofs: vec![p(12)],
            xor_proofs: vec![p(13)],
            shift_left_proofs: vec![p(14)],
            shift_right_proofs: vec![expr::dup(&shared)],
            div_type_pins: vec![(nm("Decidable.rec"), p(15))],
            mod_type_pins: vec![(nm("Decidable.rec"), p(15)), (nm("Decidable.casesOn"), p(16))],
            gcd_type_pins: Vec::new(),
            land_type_pins: vec![(nm("Decidable.casesOn"), p(16))],
            lor_type_pins: Vec::new(),
            xor_type_pins: Vec::new(),
            shift_left_type_pins: Vec::new(),
            shift_right_type_pins: Vec::new(),
        }
    }

    // --- `con-ron-pins/2` (FORMAT.md §4) -----------------------------------

    #[test]
    fn a_pin_dump_round_trips() {
        let ss = vec![a_pin_set("lean4:v4.33.0"), a_pin_set("lean4-nightly")];
        let text = dump_pins(&ss);
        assert!(text.starts_with("con-ron-pins/2\n"));
        assert!(text.ends_with("end 2\n"));
        let (back, counts) = parse_pins_counted(&text).unwrap();
        assert_eq!(counts.pin_sets, 2);
        assert_eq!(back.len(), 2);
        // byte-identical re-dump: every id, every list length, every escape
        assert_eq!(dump_pins(&back), text);
        // and the sharing survived — the census counts heap nodes
        let cen = dag::census_pins(&back);
        assert_eq!(cen.exprs, counts.exprs);
        assert_eq!(back[0].toolchain, cps("lean4:v4.33.0"));
        assert_eq!(back[0].gcd_proofs.len(), 0);
        assert_eq!(back[0].div_proofs.len(), 2);
        assert_eq!(back[0].mod_type_pins.len(), 2);
        assert_eq!(back[0].gcd_type_pins.len(), 0);
    }

    /// The **embedded** pin text (task #43) decoded by the *verified* decoder
    /// in the core, against this crate's unverified reader on the same bytes.
    /// The two readers agree if and only if the writer maps their outputs to
    /// the same bytes, and the DAG census is what says the verified decoder
    /// kept the sharing (as a tree the v4.33.0 variant is 5.1 M nodes, so a
    /// reader that lost it would be caught here and nowhere else).
    ///
    /// The decode runs on a thread with the driver's stack
    /// (`con_ron::driver::STACK_BYTES` is 1 GiB): the core decoder's recursion
    /// is one frame per record, and 26 721 of them do not fit a test thread's
    /// default stack.
    #[test]
    fn the_embedded_pin_text_decodes_to_the_same_pins() {
        let text = con_ron_core::kernel::pins_text::PINS_TEXT;
        let h = std::thread::Builder::new()
            .stack_size(1 << 30)
            .spawn(move || {
                let core = match con_ron_core::kernel::pins_decode::decode_embedded() {
                    Ok(v) => v,
                    Err(_) => panic!("the embedded pin text does not decode"),
                };
                let (mine, counts) = parse_pins_counted(text).unwrap();
                assert_eq!(core.len(), mine.len());
                // Value equality through the writer: same ids, same lengths,
                // same escapes, same order.
                assert_eq!(dump_pins(&core), dump_pins(&mine));
                // ... and the embedded text is exactly what the writer writes.
                assert_eq!(dump_pins(&core), text);
                // The sharing: one heap node per `E` record, not one per use.
                let cen = dag::census_pins(&core);
                assert_eq!(cen.exprs, counts.exprs);
                assert_eq!(cen.names, counts.names);
                core.len()
            })
            .unwrap();
        assert_eq!(h.join().unwrap(), 4);
    }

    #[test]
    fn an_empty_pin_list_round_trips() {
        let text = dump_pins(&Vec::new());
        assert_eq!(text, "con-ron-pins/2\nend 0\n");
        assert_eq!(parse_pins(&text).unwrap().len(), 0);
    }

    /// The header is the whole version check, and the footer counts the `S`
    /// records: neither is advisory.  (Until task #80 this file also carried
    /// the declaration payload of task #10, and the test that the two payload
    /// kinds did not mix.)
    #[test]
    fn the_header_and_the_footer_are_checked() {
        // a record letter this format does not have
        let bad = "con-ron-pins/2\nD b nat\nend 0\n";
        assert!(pins_err(bad).contains("unknown record kind \"D\""), "{}", pins_err(bad));
        // a foreign header, and the previous version
        assert!(parse_pins("lean4export/1\nend 0\n").is_err());
        assert!(parse_pins("con-ron-pins/1\nend 0\n").is_err());
        // and the footer counts the pin sets
        let ss = vec![a_pin_set("t")];
        let text = dump_pins(&ss).replace("end 1", "end 2");
        assert!(pins_err(&text).contains("pin sets read"), "{}", pins_err(&text));
    }

    // --- the string codec, mirroring the Lean reader's `#guard`s ----------

    #[test]
    fn escape_matches_the_lean_guards() {
        assert_eq!(write::escape_string(&cps("")), "");
        assert_eq!(write::escape_string(&cps(" ")), "\\20;");
        assert_eq!(write::escape_string(&cps("\\")), "\\5c;");
        assert_eq!(write::escape_string(&cps("A.b_1")), "A.b_1");
        assert_eq!(write::escape_string(&cps("é")), "\\e9;");
        assert_eq!(write::escape_string(&cps("∀")), "\\2200;");
        assert_eq!(write::escape_string(&cps("\n")), "\\a;");
    }

    #[test]
    fn the_string_codec_round_trips() {
        for s in [
            "",
            " ",
            "\\",
            "a b\nc\t;",
            "∀ x, x ≤ x₁ · y",
            "\u{0}",
            "\u{10ffff}",
        ] {
            let v = cps(s);
            assert_eq!(unescape(&write::escape_string(&v)).unwrap(), v, "{:?}", s);
        }
    }

    #[test]
    fn the_string_codec_rejects_surrogates_and_truncation() {
        assert!(unescape("\\d800;").is_err());
        assert!(unescape("\\20").is_err());
        assert!(unescape("\\zz;").is_err());
        // an unescaped byte that the writer would have escaped
        assert!(unescape("a\u{7f}b").is_err());
        // the degenerate escape `Pins.lean` accepts: no digits, i.e. U+0000
        assert_eq!(unescape("\\;").unwrap(), vec![0u32]);
    }

    // --- the decimal codec -------------------------------------------------

    #[test]
    fn the_decimal_codec_round_trips() {
        for s in [
            "0",
            "1",
            "9",
            "12345",
            "18446744073709551615",
            "18446744073709551616",
            "340282366920938463463374607431768211456",
            "99999999999999999999999999999999999999999999999999999999999",
        ] {
            let n = natdec::from_decimal(s).unwrap();
            assert_eq!(natdec::to_decimal(&n), s, "{}", s);
        }
        assert!(nat::beq(
            &natdec::from_decimal("18446744073709551616").unwrap(),
            &nat::mul(&nat::from_u64(1 << 32), &nat::from_u64(1 << 32))
        ));
        assert!(natdec::from_decimal("").is_err());
        assert!(natdec::from_decimal("1a").is_err());
        assert!(natdec::from_decimal("-1").is_err());
    }

    // --- the failure modes -------------------------------------------------

    fn perr(text: &str) -> String {
        pins_err(text)
    }

    /// A token of the file reaches a message only escaped (task #131).
    #[test]
    fn parse_errors_escape_the_file() {
        assert_eq!(
            perr("con-ron-pins/2\u{1b}[2K\n"),
            "bad header: expected 'con-ron-pins/2', got \"con-ron-pins/2\\u{001B}[2K\""
        );
        let e = perr("con-ron-pins/2\nQ\u{7}\u{202e}x 0\nend 0\n");
        assert!(e.contains("\\u{0007}\\u{202E}"), "{}", e);
        assert!(!e.chars().any(|c| con_ron_core::kernel::name::display_unsafe_char(c as u32)));
        let n = perr("con-ron-pins/2\nN 1 n 0 9\u{1b}\nend 0\n");
        assert!(!n.contains('\u{1b}'), "{}", n);
    }

    #[test]
    fn parse_errors_name_the_line() {
        assert!(perr("").contains("bad header"));
        assert!(perr("con-ron-pins/1\nend 0\n").contains("bad header"));
        assert!(perr("con-ron-pins/2\n").contains("no 'end' footer"));

        // a forward reference
        assert_eq!(
            perr("con-ron-pins/2\nN 0 s 0 1 a\nend 0\n"),
            "line 2: name id 0 is not defined yet"
        );
        // a wrong own id
        assert_eq!(
            perr("con-ron-pins/2\nN 1 a\nend 0\n"),
            "line 2: name id 1, expected 0"
        );
        // an unknown kind letter, and an unknown constructor letter
        assert_eq!(
            perr("con-ron-pins/2\nX 0 a\nend 0\n"),
            "line 2: unknown record kind \"X\""
        );
        assert_eq!(
            perr("con-ron-pins/2\nN 0 q\nend 0\n"),
            "line 2: unknown name record \"q\""
        );
        // a bad footer count, trailing fields, content after the footer
        assert!(perr("con-ron-pins/2\nN 0 a\nend 1\n")
            .starts_with("line 3: footer count 1 != the 0"));
        assert_eq!(
            perr("con-ron-pins/2\nN 0 a 7\nend 0\n"),
            "line 2: trailing fields in a record"
        );
        assert_eq!(
            perr("con-ron-pins/2\nend 0\nN 0 a\n"),
            "line 3: content after the footer"
        );
        // the redundant string length is cross-checked
        assert_eq!(
            perr("con-ron-pins/2\nN 0 a\nN 1 s 0 2 a\nend 0\n"),
            "line 3: string length 1 != the declared 2"
        );
        // an index that does not fit a machine word (DESIGN.md §3.3)
        assert!(
            perr("con-ron-pins/2\nE 0 b 99999999999999999999999\nend 0\n")
                .contains("does not fit a 64-bit index")
        );
        // but an unbounded `natVal` literal does fit
        assert!(
            parse_pins("con-ron-pins/2\nE 0 n 99999999999999999999999\nend 0\n").is_ok()
        );
        // every record kind's own truncation, and a bad reference
        assert!(perr("con-ron-pins/2\nE 0 a 0 0\nend 0\n")
            .contains("expr id 0 is not defined yet"));
        assert!(perr("con-ron-pins/2\nL 0\nend 0\n").contains("unexpected end of record"));
        // task #119: the binder datum's `W` record is gone from the format
        assert!(perr("con-ron-pins/2\nW 0 n\nend 0\n").contains("unknown record kind"));

        // a mutilated real dump fails, never silently succeeds
        let ok = dump_pins(&[a_pin_set("t"), a_pin_set("u")]);
        assert!(perr(&ok.replace("end 2", "end 1")).contains("footer count"));
        assert!(!perr(&ok.lines().take(4).collect::<Vec<_>>().join("\n")).is_empty());
    }

    /// **The audit behind `MiMallocTight`'s `align <= 16`** (task #94).
    ///
    /// `MiMallocTight::alloc` sends a 16-aligned request to plain
    /// `mi_malloc`, which is what keeps a small block in its own size class
    /// instead of the aligned entry's next one up.
    /// That is sound by mimalloc's construction — `MI_MAX_ALIGN_SIZE` is 16
    /// on x86-64, so `MI_ALIGN2W` rounds every request of eight words or
    /// fewer to an even word count and every bin in that range strides by a
    /// multiple of 16 from a 16-aligned page start — and this checks it
    /// rather than trusting it, at exactly the sizes con-ron allocates.
    #[test]
    #[cfg(all(feature = "mimalloc", not(feature = "jemalloc")))]
    fn mi_malloc_gives_16_aligned_blocks() {
        use std::alloc::GlobalAlloc;
        use std::alloc::Layout;
        for size in [16usize, 24, 32, 40, 48, 56, 64, 128] {
            let l = Layout::from_size_align(size, 16).unwrap();
            let mut ps: Vec<*mut u8> = Vec::with_capacity(100_000);
            for _ in 0..100_000 {
                let p = unsafe { MiMallocTight.alloc(l) };
                assert!(!p.is_null());
                assert_eq!(
                    (p as usize) % 16,
                    0,
                    "a {size}-byte block came back {}-aligned",
                    1usize << (p as usize).trailing_zeros()
                );
                ps.push(p);
            }
            for p in ps {
                unsafe { MiMallocTight.dealloc(p, l) };
            }
        }
    }

    /// Task #36: what one node weighs.  The numbers are the *reason* the
    /// Mathlib parse costs what it does — 103 M `E` records times
    /// `ExprNode`'s heap block — and they are asserted, not just printed, so
    /// that a core-type repacking (which this crate may not do) announces
    /// itself here with its saving.
    #[test]
    fn the_node_sizes_are_what_the_accounting_assumes() {
        for r in node_sizes() {
            eprintln!("{:<32} size {:>3}  rc block {:>3}", r.what, r.size, r.heap);
        }
        for r in node_sizes() {
            assert_eq!(r.size % 8, 0, "{} is not word-sized", r.what);
        }
        // Task #97-SWAP-2: one node as wide as the widest arm, behind a `P`.
        // Task #119: the binder datum is gone, so `lam`/`forallE` are two
        // words and the widest arms (`letE`, `proj`) three.
        assert_eq!(std::mem::size_of::<ExprKind>(), 32);
        assert_eq!(std::mem::size_of::<ExprNode>(), 40);
        assert_eq!(expr_node_bytes(), 56);
        assert_eq!(std::mem::size_of::<Literal>(), 16);
        assert_eq!(std::mem::size_of::<NameNode>(), 40);
        assert_eq!(std::mem::size_of::<LevelNode>(), 32);
        // the id tables cost one machine word per record, the `P` handle
        assert_eq!(std::mem::size_of::<Expr>(), 8);
        assert_eq!(std::mem::size_of::<Name>(), 8);
        assert_eq!(std::mem::size_of::<Level>(), 8);
    }
}
