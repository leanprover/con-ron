//! The Rust reader for the `con-ron-decls/1` dump format (DESIGN.md §3.6,
//! P1.6; the Lean half is task #10).  The format is specified by
//! `proof/ConRon/Dump/FORMAT.md`; the Lean writer is
//! `proof/ConRon/Dump/Write.lean` and the Lean reader — the format's
//! validator, which this file mirrors function for function — is
//! `proof/ConRon/Dump/Read.lean`.
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
//! * **The DAG stays a DAG.**  `N`, `L`, `W` and `E` records are interned by
//!   the writer, so each shared subterm appears once; the reader builds each
//!   such node once, pushes it onto the `Vec` for its id space, and every
//!   later reference hands back a `clone` of the `Rc` handle
//!   (`name::dup`/`level::dup`/`expr::dup`).  The in-memory term is therefore
//!   the same DAG the Lean side had, not its tree expansion.
//! * **Computed fields are recomputed, never read off the file.**  The
//!   constructors (`name::mk_str`, `level::succ`, `expr::app`, …) are the only
//!   way a node is made here, and they are what write `NameNode::hash`,
//!   `LevelNode::hash` and `ExprNode::data`.  The hash *bits* of
//!   `ExprNode::data` differ from Lean's by design (DESIGN.md task #3, note 6)
//!   and nothing compares them.
//!
//! Deviations from `Read.lean`, deliberate and tested:
//!
//! * ids, lengths and the `bvar`/`fvar`/`proj`/`Name.num` indices are `u64`
//!   (DESIGN.md §3.3), so a dump that overflows one is a *reader* failure with
//!   a line number rather than a bignum;
//! * `Literal.natVal` goes through [`natdec::from_decimal`], the crate's own
//!   decimal parser — `ron::Nat` has none and DESIGN.md §3.4 says not to grow
//!   the core for tooling's sake;
//! * a literal byte inside a string field must be printable non-backslash
//!   ASCII (`0x21..=0x7e`, not `0x5c`).  `Read.lean` accepts any non-`\`
//!   character there; the format never produces one, so rejecting it is the
//!   loud failure FORMAT.md §6 wants.  The degenerate escape `\;` (no hex
//!   digits, i.e. `U+0000`) is accepted exactly as `Read.lean` accepts it.
//!
//! The sibling format **`con-ron-pins/1`** (FORMAT.md §7) is read by
//! [`parse_pins`], and it is the same function: the record grammar below the
//! payload is identical, so the reader carries a `pins` flag that swaps the
//! payload record (`S` for `D`) and what the footer counts.  Its consumer is
//! `con-ron-check --pins FILE`, which hands the `Vec<NatOpPinSet>` to
//! `check_decls` as DESIGN.md §3.6's pin-list *parameter*.
//!
//! The reader is one forward pass: nine `Vec`s that only ever grow by one, and
//! every reference an index into a `Vec` that is already long enough.  No
//! fixups, no cycles, no recursion over the term (the `E` records are already
//! topologically sorted, so the reader needs no worklist either — the writer's
//! is enough).
//!
//! And because the pass is forward, **the dump is never held in memory**
//! (task #36): [`parse_decls_file`] streams it a line at a time, so a 3 GB
//! Mathlib dump costs one line buffer rather than 3 GB of `String` plus 2 GB
//! of `Vec<&str>` line index.  [`parse_decls`] still takes a `&str` — the
//! round-trip tests and the pin reader want that — and the two drivers share
//! every record function below, so they accept the same files with the same
//! messages and the same line numbers.  What the reader's resident set *is*,
//! after that, is the terms themselves: `con-ron-dump-check --sizes`
//! ([`node_sizes`]) prints what one node of each kind weighs, and
//! [`peak_rss_kb`] is what the binaries report it against.

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
// therefore applies to the two binaries that link it.  It is invisible to the
// verified core: Charon extracts `con-ron-core` alone, the allocator is not a
// Rust item of that crate, and the Aeneas model has no heap to begin with
// (`Rc`/`Box`/`Vec` are modeled by their contents, DESIGN.md §3.2), so
// `proof/ConRon/Generated/*` is byte-identical whichever allocator is chosen.
// It cannot change the verdict either: the allocator only decides *where*
// bytes go, and the core reads no address (`ptr_eq` aside, which compares
// identity, not order).
//
// `mimalloc` is the default (it measured best on `init`);
// `--no-default-features` restores glibc `malloc`, and
// `--no-default-features --features jemalloc` selects jemalloc.
#[cfg(all(feature = "mimalloc", not(feature = "jemalloc")))]
#[global_allocator]
static GLOBAL_ALLOC: mimalloc::MiMalloc = mimalloc::MiMalloc;

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

use con_ron_core::cached::parsed_c::DeclC;
use con_ron_core::kernel::env;
use con_ron_core::kernel::env::BasisKind;
use con_ron_core::kernel::env::ConstantInfo;
use con_ron_core::kernel::env::ConstantVal;
use con_ron_core::kernel::env::IndCaps;
use con_ron_core::kernel::env::ProjTable;
use con_ron_core::kernel::env::RecRule;
use con_ron_core::kernel::env::RecRuleFire;
use con_ron_core::kernel::env::ReducibilityHint;
use con_ron_core::kernel::expr;
use con_ron_core::kernel::expr::BinderMeta;
use con_ron_core::kernel::expr::Expr;
use con_ron_core::kernel::expr::Literal;
use con_ron_core::kernel::expr::ExprKind;
use con_ron_core::kernel::expr::ExprNode;
use con_ron_core::kernel::level;
use con_ron_core::kernel::level::Level;
use con_ron_core::kernel::level::LevelKind;
use con_ron_core::kernel::level::LevelNode;
use con_ron_core::kernel::name;
use con_ron_core::kernel::name::Name;
use con_ron_core::kernel::name::NameKind;
use con_ron_core::kernel::name::NameNode;
use con_ron_core::kernel::nat_op_pins::NatOpPinSet;
use con_ron_core::kernel::prop_when;
use con_ron_core::kernel::prop_when::PropWhen;
use con_ron_core::ron::nat::Nat;

pub mod dag;
pub mod natdec;
pub mod write;

pub use write::dump_decls;
pub use write::dump_pins;

/// The version header, the whole first line of a declaration dump
/// (`Write.lean`'s `header`).
pub const HEADER: &str = "con-ron-decls/1";

/// The version header of the sibling pin dump (`Write.lean`'s `pinsHeader`,
/// FORMAT.md §7).
pub const PINS_HEADER: &str = "con-ron-pins/1";

// ---------------------------------------------------------------------------
// String fields
// ---------------------------------------------------------------------------

/// Is `c` a Lean `Char`?  `Nat.isValidChar`: below `U+D800`, or above
/// `U+DFFF` and below `U+110000`.  The surrogate range is not a code point on
/// either side of the format.
pub fn is_valid_char(c: u32) -> bool {
    c < 0xd800 || (0xdfff < c && c < 0x11_0000)
}

/// Undo `Write.lean`'s `escapeString`: a literal printable non-backslash
/// ASCII byte is itself, `\<lowercase-hex>;` is the code point it names.  The
/// result is the code-point vector the core stores (DESIGN.md §3.3), so no
/// UTF-8 decoder is involved: the input is pure ASCII by construction and a
/// byte that is not is an error.
pub fn unescape(t: &str) -> Result<Vec<u32>, String> {
    let b = t.as_bytes();
    let mut out: Vec<u32> = Vec::new();
    let mut i: usize = 0;
    while i < b.len() {
        let c = b[i];
        if c == b'\\' {
            i += 1;
            let mut v: u64 = 0;
            loop {
                if i >= b.len() {
                    return Err("unterminated string escape".to_string());
                }
                let d = b[i];
                i += 1;
                if d == b';' {
                    break;
                }
                let hv: u64 = match d {
                    b'0'..=b'9' => (d - b'0') as u64,
                    b'a'..=b'f' => (d - b'a' + 10) as u64,
                    _ => return Err("bad character in a string escape".to_string()),
                };
                v = v * 16 + hv;
                if v > 0x11_0000 {
                    return Err(format!("string escape \\{:x}; is out of range", v));
                }
            }
            if !is_valid_char(v as u32) {
                return Err(format!("escape \\{:x}; is not a code point", v));
            }
            out.push(v as u32);
        } else if (0x21..=0x7e).contains(&c) && c != 0x5c {
            out.push(c as u32);
            i += 1;
        } else {
            return Err(format!(
                "byte 0x{:02x} must be escaped inside a string field",
                c
            ));
        }
    }
    Ok(out)
}

// ---------------------------------------------------------------------------
// What a parse reports
// ---------------------------------------------------------------------------

/// The census of one dump: how many records each id space holds, and how many
/// declarations of each kind.  `con-ron-dump-check` prints it; nothing in the
/// reader depends on it.
#[derive(Debug, Default, Clone, Copy, PartialEq, Eq)]
pub struct Counts {
    pub names: usize,
    pub levels: usize,
    pub pws: usize,
    pub exprs: usize,
    pub cvs: usize,
    pub rules: usize,
    pub caps: usize,
    pub tables: usize,
    pub infos: usize,
    pub decls: usize,
    pub axiom_decls: usize,
    pub defn_decls: usize,
    pub thm_decls: usize,
    pub opaque_decls: usize,
    pub basis_decls: usize,
    pub ind_decls: usize,
    /// The `ConstantInfo`s summed over every `indDecl` block.
    pub block_infos: usize,
    /// `con-ron-pins/1` only: the `S` records, i.e. the pin variants.
    pub pin_sets: usize,
}

impl Counts {
    fn tally_decls(&mut self, ds: &[DeclC]) {
        self.decls = ds.len();
        for d in ds {
            match d {
                DeclC::AxiomDecl(_) => self.axiom_decls += 1,
                DeclC::DefnDecl(_, _, _) => self.defn_decls += 1,
                DeclC::ThmDecl(_, _) => self.thm_decls += 1,
                DeclC::OpaqueDecl(_, _) => self.opaque_decls += 1,
                DeclC::BasisDecl(_) => self.basis_decls += 1,
                DeclC::IndDecl(block, _) => {
                    self.ind_decls += 1;
                    self.block_infos += block.len();
                }
            }
        }
    }
}

// ---------------------------------------------------------------------------
// What a node weighs (task #36)
// ---------------------------------------------------------------------------

/// `Rc<T>`'s heap block: the two reference counts in front of the value
/// (`alloc::rc::RcInner`, `#[repr(C)] { strong, weak, value }`).  This is a
/// *model* of that private type, used only to report a size — nothing is
/// allocated through it and no pointer is cast to it.
#[repr(C)]
#[allow(dead_code)]
struct RcBlock<T> {
    strong: usize,
    weak: usize,
    value: T,
}

/// One row of the size report: a type, its `size_of`, and — for a type the
/// core holds behind an `Rc` — what one heap block of it costs including the
/// two counts.  `heap == 0` means the type is stored inline, in its owner.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct NodeSize {
    pub what: &'static str,
    pub size: usize,
    pub heap: usize,
}

/// **What the reader's terms weigh, per node** (`con-ron-dump-check --sizes`,
/// DESIGN.md tasks #36 and #38).  The interesting number is `ExprNode`'s
/// `heap`: at Mathlib scale it is multiplied by 103 M.  Task #38 repacked the
/// core types this measures — the binder datum, a `const`'s level list and a
/// literal's payload each went behind an `Rc` — so the widest `ExprKind` arm
/// is 24 bytes (`lam`/`forallE`, `letE`, `proj` all are) and the block is 56
/// rather than 72.  The rows are the *real* arm types, and the test below
/// pins them, so a further repacking shows up as a diff with its saving
/// attached.
pub fn node_sizes() -> Vec<NodeSize> {
    fn row<T>(what: &'static str, rc: bool) -> NodeSize {
        NodeSize {
            what,
            size: std::mem::size_of::<T>(),
            heap: if rc { std::mem::size_of::<RcBlock<T>>() } else { 0 },
        }
    }
    vec![
        row::<ExprNode>("ExprNode (data + kind)", true),
        row::<ExprKind>("  ExprKind", false),
        row::<(Expr, Expr)>("    app payload", false),
        row::<(Name, std::rc::Rc<Vec<Level>>)>("    const payload", false),
        row::<Literal>("    lit payload", false),
        row::<(Expr, Expr, BinderMeta)>("    lam/forallE payload", false),
        row::<(Expr, Expr, Expr)>("    letE payload", false),
        row::<(Name, u64, Expr)>("    proj payload", false),
        row::<NameNode>("NameNode (hash + kind)", true),
        row::<NameKind>("  NameKind", false),
        row::<LevelNode>("LevelNode (hash + kind)", true),
        row::<LevelKind>("  LevelKind", false),
        row::<PropWhen>("PropWhen (behind a binder's handle)", true),
        row::<Vec<u32>>("Vec<u32> (a string's header)", false),
        row::<Nat>("Nat (limb Vec header)", false),
        row::<DeclC>("DeclC", false),
        row::<ConstantInfo>("ConstantInfo (inline)", false),
        row::<ConstantVal>("ConstantVal (inline)", false),
    ]
}

/// The `Rc` heap block of an `ExprNode` — the reader's dominant cost, one per
/// `E` record.  Separate from [`node_sizes`] so the binaries can multiply it
/// by the record count without searching the table.
pub fn expr_node_bytes() -> usize {
    std::mem::size_of::<RcBlock<ExprNode>>()
}

/// The peak resident set of this process in KB, `VmHWM` from
/// `/proc/self/status` — a high-water mark, so it survives every `free` and
/// is the number DESIGN.md's memory budgets are stated in.  `0` where the
/// file is not readable.
pub fn peak_rss_kb() -> u64 {
    match std::fs::read_to_string("/proc/self/status") {
        Err(_) => 0,
        Ok(t) => {
            for l in t.lines() {
                if let Some(rest) = l.strip_prefix("VmHWM:") {
                    let mut it = rest.split_whitespace();
                    if let Some(n) = it.next() {
                        return n.parse::<u64>().unwrap_or(0);
                    }
                }
            }
            0
        }
    }
}

// ---------------------------------------------------------------------------
// The reader's state
// ---------------------------------------------------------------------------

/// One `Vec` per id space: the reader's whole persistent state, the mirror of
/// `Read.lean`'s `RState` minus the current record.  It is deliberately free
/// of any borrow of the input (task #36): the reader reads the dump one line
/// at a time and never holds the text, so this struct outlives every line
/// buffer and the cursor over the current line ([`Rec`]) is built fresh per
/// record.
struct Tables {
    names: Vec<Name>,
    levels: Vec<Level>,
    /// The `W` space, as binder data: the datum is behind a handle since task
    /// #38, so a `lam`/`forallE` record shares the entry (`bm_ref`) instead
    /// of copying a `PropWhen` per binder node.
    pws: Vec<BinderMeta>,
    exprs: Vec<Expr>,
    cvs: Vec<ConstantVal>,
    rules: Vec<RecRule>,
    caps: Vec<IndCaps>,
    tables: Vec<ProjTable>,
    infos: Vec<ConstantInfo>,
    decls: Vec<DeclC>,
    /// The `con-ron-pins/1` payload (FORMAT.md §7).  A file has one payload
    /// kind or the other, never both.
    pin_sets: Vec<NatOpPinSet>,
    /// Which file is being read: `false` a `con-ron-decls/1` dump (payload
    /// `D`), `true` a `con-ron-pins/1` one (payload `S`).  `Read.lean`'s
    /// `RState.pins`.
    pins: bool,
}

impl Tables {
    fn new(pins: bool) -> Tables {
        Tables {
            names: Vec::new(),
            levels: Vec::new(),
            pws: Vec::new(),
            exprs: Vec::new(),
            cvs: Vec::new(),
            rules: Vec::new(),
            caps: Vec::new(),
            tables: Vec::new(),
            infos: Vec::new(),
            decls: Vec::new(),
            pin_sets: Vec::new(),
            pins,
        }
    }

    /// The payload count the footer must agree with: declarations in a
    /// `con-ron-decls/1` dump, pin variants in a `con-ron-pins/1` one.
    fn payload_len(&self) -> usize {
        if self.pins {
            self.pin_sets.len()
        } else {
            self.decls.len()
        }
    }

    fn counts(&self) -> Counts {
        let mut c = Counts {
            names: self.names.len(),
            levels: self.levels.len(),
            pws: self.pws.len(),
            exprs: self.exprs.len(),
            cvs: self.cvs.len(),
            rules: self.rules.len(),
            caps: self.caps.len(),
            tables: self.tables.len(),
            infos: self.infos.len(),
            pin_sets: self.pin_sets.len(),
            ..Counts::default()
        };
        c.tally_decls(&self.decls);
        c
    }
}


/// The cursor over **one** record: the tables it grows, the line's text, the
/// token spans [`split_spans`] found in it, and how far the record has been
/// consumed.  `'l` is the line buffer's lifetime and is *not* the tables' —
/// that separation is what lets the driver reuse a single line buffer instead
/// of keeping the whole dump in memory (task #36).
struct Rec<'s, 'l> {
    st: &'s mut Tables,
    line: &'l str,
    spans: &'s [(u32, u32)],
    pos: usize,
    line_no: usize,
}

impl<'s, 'l> Rec<'s, 'l> {
    /// `Read.lean`'s `rerr`: fail, naming the line.
    fn err<T>(&self, msg: String) -> Result<T, String> {
        Err(format!("line {}: {}", self.line_no, msg))
    }

    // --- tokens ------------------------------------------------------------

    fn next_tok(&mut self) -> Result<&'l str, String> {
        if self.pos < self.spans.len() {
            // `line` is a `&'l str` *copied* out of `self`, so the token the
            // caller gets back outlives this `&mut self` borrow and the
            // record functions can go on matching on it while they push.
            let l: &'l str = self.line;
            let (a, b) = self.spans[self.pos];
            self.pos += 1;
            Ok(&l[a as usize..b as usize])
        } else {
            self.err("unexpected end of record".to_string())
        }
    }

    /// A `<nat>` field that DESIGN.md §3.3 makes a machine word.  An overflow
    /// is a Rust-side failure, reported with its line.
    fn nat(&mut self) -> Result<u64, String> {
        let t = self.next_tok()?;
        if t.is_empty() || !t.bytes().all(|c| c.is_ascii_digit()) {
            return self.err(format!("expected a decimal number, got '{}'", t));
        }
        match t.parse::<u64>() {
            Ok(n) => Ok(n),
            Err(_) => self.err(format!(
                "decimal number '{}' does not fit a 64-bit index (DESIGN.md §3.3)",
                t
            )),
        }
    }

    /// An unbounded `<nat>` field — only `Literal.natVal` is one.
    fn nat_big(&mut self) -> Result<Nat, String> {
        let t = self.next_tok()?;
        match natdec::from_decimal(t) {
            Ok(n) => Ok(n),
            Err(e) => self.err(e),
        }
    }

    /// A `<nat>` used as a list length or an id, i.e. as an index.
    fn count(&mut self) -> Result<usize, String> {
        let n = self.nat()?;
        match usize::try_from(n) {
            Ok(i) => Ok(i),
            Err(_) => self.err(format!("count {} does not fit a machine index", n)),
        }
    }

    fn boolean(&mut self) -> Result<bool, String> {
        let t = self.next_tok()?;
        if t == "0" {
            Ok(false)
        } else if t == "1" {
            Ok(true)
        } else {
            self.err(format!("expected 0 or 1, got '{}'", t))
        }
    }

    /// A `<string>` field: the code-point count, then the escaped text.  The
    /// count is redundant and is cross-checked, which is what it is for.
    fn string(&mut self) -> Result<Vec<u32>, String> {
        let n = self.count()?;
        let t = self.next_tok()?;
        let s = match unescape(t) {
            Ok(s) => s,
            Err(e) => return self.err(e),
        };
        if s.len() != n {
            return self.err(format!(
                "string length {} != the declared {}",
                s.len(),
                n
            ));
        }
        Ok(s)
    }

    /// Check that a record's own id is the next one of its kind (FORMAT.md §2's
    /// invariant, the half a reader must verify).
    fn expect_id(&mut self, want: usize, what: &str) -> Result<(), String> {
        let got = self.count()?;
        if got == want {
            Ok(())
        } else {
            self.err(format!("{} id {}, expected {}", what, got, want))
        }
    }

    // --- backward references ----------------------------------------------

    fn name_ref(&mut self) -> Result<Name, String> {
        let i = self.count()?;
        if i < self.st.names.len() {
            Ok(name::dup(&self.st.names[i]))
        } else {
            self.err(format!("name id {} is not defined yet", i))
        }
    }

    fn level_ref(&mut self) -> Result<Level, String> {
        let i = self.count()?;
        if i < self.st.levels.len() {
            Ok(level::dup(&self.st.levels[i]))
        } else {
            self.err(format!("level id {} is not defined yet", i))
        }
    }

    /// A `W` reference as a `PropWhen` *value* — what a `V` record's `sortZ`
    /// field wants.  The table holds binder data (see `bm_ref`), so this
    /// copies out of the handle; a dump has a few hundred thousand `V`
    /// records against a hundred million binders, so this is the rare side.
    fn pw_ref(&mut self) -> Result<PropWhen, String> {
        let i = self.count()?;
        if i < self.st.pws.len() {
            Ok(prop_when::dup(&self.st.pws[i].pw))
        } else {
            self.err(format!("propwhen id {} is not defined yet", i))
        }
    }

    /// A `W` reference as a binder datum: since task #38 that is a handle, so
    /// a `lam`/`forallE` node *shares* the table's datum instead of copying
    /// it.  The `W` space is tiny — 3 records for `init`, 4 for Mathlib — so
    /// every binder in a dump points at one of a handful of `PropWhen`s and
    /// the parse allocates none of its own.
    fn bm_ref(&mut self) -> Result<BinderMeta, String> {
        let i = self.count()?;
        if i < self.st.pws.len() {
            Ok(expr::binder_meta_dup(&self.st.pws[i]))
        } else {
            self.err(format!("propwhen id {} is not defined yet", i))
        }
    }

    fn expr_ref(&mut self) -> Result<Expr, String> {
        let i = self.count()?;
        if i < self.st.exprs.len() {
            Ok(expr::dup(&self.st.exprs[i]))
        } else {
            self.err(format!("expr id {} is not defined yet", i))
        }
    }

    fn cv_ref(&mut self) -> Result<ConstantVal, String> {
        let i = self.count()?;
        if i < self.st.cvs.len() {
            Ok(env::constant_val_dup(&self.st.cvs[i]))
        } else {
            self.err(format!("constval id {} is not defined yet", i))
        }
    }

    fn rule_ref(&mut self) -> Result<RecRule, String> {
        let i = self.count()?;
        if i < self.st.rules.len() {
            Ok(env::rec_rule_dup(&self.st.rules[i]))
        } else {
            self.err(format!("recrule id {} is not defined yet", i))
        }
    }

    fn caps_ref(&mut self) -> Result<IndCaps, String> {
        let i = self.count()?;
        if i < self.st.caps.len() {
            Ok(env::ind_caps_dup(&self.st.caps[i]))
        } else {
            self.err(format!("indcaps id {} is not defined yet", i))
        }
    }

    fn table_ref(&mut self) -> Result<ProjTable, String> {
        let i = self.count()?;
        if i < self.st.tables.len() {
            Ok(env::proj_table_dup(&self.st.tables[i]))
        } else {
            self.err(format!("projtable id {} is not defined yet", i))
        }
    }

    fn info_ref(&mut self) -> Result<ConstantInfo, String> {
        let i = self.count()?;
        if i < self.st.infos.len() {
            Ok(env::constant_info_dup(&self.st.infos[i]))
        } else {
            self.err(format!("constinfo id {} is not defined yet", i))
        }
    }

    // --- counted lists -----------------------------------------------------

    fn name_list(&mut self) -> Result<Vec<Name>, String> {
        let n = self.count()?;
        let mut v: Vec<Name> = Vec::new();
        for _ in 0..n {
            v.push(self.name_ref()?);
        }
        Ok(v)
    }

    fn level_list(&mut self) -> Result<Vec<Level>, String> {
        let n = self.count()?;
        let mut v: Vec<Level> = Vec::new();
        for _ in 0..n {
            v.push(self.level_ref()?);
        }
        Ok(v)
    }

    fn expr_list(&mut self) -> Result<Vec<Expr>, String> {
        let n = self.count()?;
        let mut v: Vec<Expr> = Vec::new();
        for _ in 0..n {
            v.push(self.expr_ref()?);
        }
        Ok(v)
    }

    fn rule_list(&mut self) -> Result<Vec<RecRule>, String> {
        let n = self.count()?;
        let mut v: Vec<RecRule> = Vec::new();
        for _ in 0..n {
            v.push(self.rule_ref()?);
        }
        Ok(v)
    }

    fn info_list(&mut self) -> Result<Vec<ConstantInfo>, String> {
        let n = self.count()?;
        let mut v: Vec<ConstantInfo> = Vec::new();
        for _ in 0..n {
            v.push(self.info_ref()?);
        }
        Ok(v)
    }

    // --- inline enumerations ----------------------------------------------

    fn hint(&mut self) -> Result<ReducibilityHint, String> {
        let t = self.next_tok()?;
        if t == "o" {
            Ok(ReducibilityHint::Opaque)
        } else if t == "b" {
            Ok(ReducibilityHint::Abbrev)
        } else if t == "r" {
            Ok(ReducibilityHint::Regular(self.nat()?))
        } else {
            self.err(format!("unknown reducibility hint '{}'", t))
        }
    }

    fn basis(&mut self) -> Result<BasisKind, String> {
        let t = self.next_tok()?;
        match t {
            "eq" => Ok(BasisKind::EqK),
            "nat" => Ok(BasisKind::NatK),
            "punit" => Ok(BasisKind::PunitK),
            "empty" => Ok(BasisKind::EmptyK),
            "false" => Ok(BasisKind::FalseK),
            "quot" => Ok(BasisKind::QuotK),
            _ => self.err(format!("unknown basis kind '{}'", t)),
        }
    }

    fn fire(&mut self) -> Result<RecRuleFire, String> {
        let t = self.next_tok()?;
        if t == "i" {
            Ok(RecRuleFire::Inert)
        } else if t == "p" {
            Ok(RecRuleFire::Plain)
        } else if t == "n" {
            let lvls = self.level_list()?;
            let pins = self.expr_list()?;
            Ok(RecRuleFire::Nested(lvls, pins))
        } else {
            self.err(format!("unknown recursor-rule fire '{}'", t))
        }
    }

    // --- the records -------------------------------------------------------

    /// `N` — `ConLeche/Kernel/Name.lean`.  `hashData` is recomputed by the
    /// smart constructors, never read off the file.
    fn record_name(&mut self) -> Result<(), String> {
        self.expect_id(self.st.names.len(), "name")?;
        let t = self.next_tok()?;
        let v = if t == "a" {
            name::anonymous()
        } else if t == "s" {
            let p = self.name_ref()?;
            let s = self.string()?;
            name::mk_str(p, s)
        } else if t == "n" {
            let p = self.name_ref()?;
            let k = self.nat()?;
            name::mk_num(p, k)
        } else {
            return self.err(format!("unknown name record '{}'", t));
        };
        self.st.names.push(v);
        Ok(())
    }

    /// `L` — `ConLeche/Kernel/Expr.lean:39`.
    fn record_level(&mut self) -> Result<(), String> {
        self.expect_id(self.st.levels.len(), "level")?;
        let t = self.next_tok()?;
        let v = if t == "z" {
            level::zero()
        } else if t == "s" {
            let a = self.level_ref()?;
            level::succ(a)
        } else if t == "m" {
            let a = self.level_ref()?;
            let b = self.level_ref()?;
            level::max(a, b)
        } else if t == "i" {
            let a = self.level_ref()?;
            let b = self.level_ref()?;
            level::imax(a, b)
        } else if t == "p" {
            let n = self.name_ref()?;
            level::param(n)
        } else {
            return self.err(format!("unknown level record '{}'", t));
        };
        self.st.levels.push(v);
        Ok(())
    }

    /// `W` — `ConLeche/Kernel/PropWhen.lean`.  The list arrives canonical
    /// (sorted by `Name.cmp`, duplicate-free) and is rebuilt through the
    /// core's smart constructor, which re-normalises; on a canonical list that
    /// is the identity (`PropWhen.ifAllZero_toList`, checked by
    /// `canonical_list_renormalises_to_itself` below).
    fn record_pw(&mut self) -> Result<(), String> {
        self.expect_id(self.st.pws.len(), "propwhen")?;
        let t = self.next_tok()?;
        let v = if t == "n" {
            prop_when::never()
        } else if t == "z" {
            let ps = self.name_list()?;
            prop_when::if_all_zero(ps)
        } else {
            return self.err(format!("unknown propwhen record '{}'", t));
        };
        self.st.pws.push(expr::binder_meta(v));
        Ok(())
    }

    /// `E` — `ConLeche/Kernel/Expr.lean:343`.  The packed `data` word is
    /// recomputed by the constructors from the children (`pack_data`,
    /// `sat_succ`, `sat_pred`, `hash32`); its hash bits are the port's own
    /// (DESIGN.md task #3, note 6) and nothing compares them with Lean's.
    fn record_expr(&mut self) -> Result<(), String> {
        self.expect_id(self.st.exprs.len(), "expr")?;
        let t = self.next_tok()?;
        let v = if t == "b" {
            let i = self.nat()?;
            expr::mk_bvar(i)
        } else if t == "v" {
            let idx = self.nat()?;
            let ty = self.expr_ref()?;
            expr::fvar(idx, ty)
        } else if t == "s" {
            let u = self.level_ref()?;
            expr::sort(u)
        } else if t == "c" {
            let n = self.name_ref()?;
            let us = self.level_list()?;
            expr::mk_const(n, us)
        } else if t == "a" {
            let f = self.expr_ref()?;
            let a = self.expr_ref()?;
            expr::app(f, a)
        } else if t == "l" {
            let ty = self.expr_ref()?;
            let b = self.expr_ref()?;
            let m = self.bm_ref()?;
            expr::lam(ty, b, m)
        } else if t == "f" {
            let ty = self.expr_ref()?;
            let b = self.expr_ref()?;
            let m = self.bm_ref()?;
            expr::forall_e(ty, b, m)
        } else if t == "t" {
            let ty = self.expr_ref()?;
            let val = self.expr_ref()?;
            let b = self.expr_ref()?;
            expr::let_e(ty, val, b)
        } else if t == "n" {
            let n = self.nat_big()?;
            expr::lit(expr::literal_nat(n))
        } else if t == "g" {
            let s = self.string()?;
            expr::lit(expr::literal_str(s))
        } else if t == "p" {
            let sn = self.name_ref()?;
            let i = self.nat()?;
            let s = self.expr_ref()?;
            expr::proj(sn, i, s)
        } else {
            return self.err(format!("unknown expr record '{}'", t));
        };
        self.st.exprs.push(v);
        Ok(())
    }

    /// `V` — `ConLeche/Kernel/Env.lean:197`.
    fn record_cv(&mut self) -> Result<(), String> {
        self.expect_id(self.st.cvs.len(), "constval")?;
        let n = self.name_ref()?;
        let lps = self.name_list()?;
        let ty = self.expr_ref()?;
        self.st.cvs.push(ConstantVal {
            name: n,
            level_params: lps,
            ty,
        });
        Ok(())
    }

    /// `R` — `ConLeche/Kernel/Env.lean:255`.  `ctor_params`, `fire`, `k`,
    /// `eta` and `params_blind` are install-computed and carry their parse
    /// placeholders in a dump (FORMAT.md §6.6); the format writes them anyway,
    /// so the reader reads them and assumes nothing.
    fn record_rule(&mut self) -> Result<(), String> {
        self.expect_id(self.st.rules.len(), "recrule")?;
        let ctor = self.name_ref()?;
        let nfields = self.nat()?;
        let ctor_params = self.nat()?;
        let fire = self.fire()?;
        let rhs = self.expr_ref()?;
        let k = self.boolean()?;
        let eta = self.boolean()?;
        let params_blind = self.boolean()?;
        self.st.rules.push(RecRule {
            ctor,
            nfields,
            ctor_params,
            fire,
            rhs,
            k,
            eta,
            params_blind,
        });
        Ok(())
    }

    /// `C` — `ConLeche/Kernel/Env.lean:359`.
    fn record_caps(&mut self) -> Result<(), String> {
        self.expect_id(self.st.caps.len(), "indcaps")?;
        let eta = self.boolean()?;
        let eta_ctor = self.name_ref()?;
        let eta_params = self.nat()?;
        let eta_fields = self.nat()?;
        let unitlike = self.boolean()?;
        let unit_params = self.nat()?;
        let rule_k = self.boolean()?;
        let sort_z = self.pw_ref()?;
        self.st.caps.push(IndCaps {
            eta,
            eta_ctor,
            eta_params,
            eta_fields,
            unitlike,
            unit_params,
            rule_k,
            sort_z,
        });
        Ok(())
    }

    /// `P` — `ConLeche/Kernel/Env.lean:397`.  `bodies` is an `Array Expr` in
    /// Lean and a `Vec<Expr>` here; the format writes it as a counted list and
    /// the port does not inherit the asymmetry with `guards` (task #10,
    /// surprise 8).
    fn record_table(&mut self) -> Result<(), String> {
        self.expect_id(self.st.tables.len(), "projtable")?;
        let struct_name = self.name_ref()?;
        let level_params = self.name_list()?;
        let num_params = self.nat()?;
        let ctor = self.name_ref()?;
        let num_fields = self.nat()?;
        let struct_sort = self.level_ref()?;
        let bodies = self.expr_list()?;
        let guards = self.level_list()?;
        let off = self.nat()?;
        self.st.tables.push(ProjTable {
            struct_name,
            level_params,
            num_params,
            ctor,
            num_fields,
            struct_sort,
            bodies,
            guards,
            off,
        });
        Ok(())
    }

    /// `I` — `ConLeche/Kernel/Env.lean:471`.  All seven constructors, and
    /// every field of each: the four the corpus never produces inside an
    /// `indDecl` block (`axiomInfo`, `defnInfo`, `thmInfo`, `projInfo`) are
    /// constructors of the type `check_decls` takes, so they are read here
    /// (task #10, surprise 3).
    fn record_info(&mut self) -> Result<(), String> {
        self.expect_id(self.st.infos.len(), "constinfo")?;
        let t = self.next_tok()?;
        let v = if t == "a" {
            let cv = self.cv_ref()?;
            ConstantInfo::AxiomInfo(cv)
        } else if t == "d" {
            let cv = self.cv_ref()?;
            let e = self.expr_ref()?;
            let h = self.hint()?;
            ConstantInfo::DefnInfo(cv, e, h)
        } else if t == "t" {
            let cv = self.cv_ref()?;
            let e = self.expr_ref()?;
            ConstantInfo::ThmInfo(cv, e)
        } else if t == "i" {
            let cv = self.cv_ref()?;
            let c = self.caps_ref()?;
            ConstantInfo::IndInfo(cv, c)
        } else if t == "c" {
            let cv = self.cv_ref()?;
            let np = self.nat()?;
            let nf = self.nat()?;
            ConstantInfo::CtorInfo(cv, np, nf)
        } else if t == "r" {
            let cv = self.cv_ref()?;
            let mi = self.nat()?;
            let rp = self.nat()?;
            let rules = self.rule_list()?;
            ConstantInfo::RecInfo(cv, mi, rp, rules)
        } else if t == "p" {
            let tbl = self.table_ref()?;
            ConstantInfo::ProjInfo(tbl)
        } else {
            return self.err(format!("unknown constinfo record '{}'", t));
        };
        self.st.infos.push(v);
        Ok(())
    }

    /// `D` — `ConLeche/Cached/ParsedC.lean:55`.  No id: the order is the
    /// payload, and it is the order `check_decls` folds in.
    fn record_decl(&mut self) -> Result<(), String> {
        let t = self.next_tok()?;
        let v = if t == "a" {
            let cv = self.cv_ref()?;
            DeclC::AxiomDecl(cv)
        } else if t == "d" {
            let cv = self.cv_ref()?;
            let e = self.expr_ref()?;
            let h = self.hint()?;
            DeclC::DefnDecl(cv, e, h)
        } else if t == "t" {
            let cv = self.cv_ref()?;
            let e = self.expr_ref()?;
            DeclC::ThmDecl(cv, e)
        } else if t == "o" {
            let cv = self.cv_ref()?;
            let e = self.expr_ref()?;
            DeclC::OpaqueDecl(cv, e)
        } else if t == "b" {
            let k = self.basis()?;
            DeclC::BasisDecl(k)
        } else if t == "i" {
            let np = self.nat()?;
            let block = self.info_list()?;
            DeclC::IndDecl(block, np)
        } else {
            return self.err(format!("unknown declaration record '{}'", t));
        };
        self.st.decls.push(v);
        Ok(())
    }

    /// `S` — `ConLeche/Kernel/NatOpPinSet.lean:30` (FORMAT.md §7).  No id,
    /// for `D`'s reason: the record is the payload, and its position in the
    /// file is its position in `natOpPinSets`, which is the order
    /// `check_div_mod_pin_loop` tries the variants in.
    fn record_pin_set(&mut self) -> Result<(), String> {
        let toolchain = self.string()?;
        let div_pin = self.expr_ref()?;
        let mod_pin = self.expr_ref()?;
        let gcd_pin = self.expr_ref()?;
        let land_pin = self.expr_ref()?;
        let lor_pin = self.expr_ref()?;
        let xor_pin = self.expr_ref()?;
        let shift_left_pin = self.expr_ref()?;
        let shift_right_pin = self.expr_ref()?;
        let div_proofs = self.expr_list()?;
        let mod_proofs = self.expr_list()?;
        let gcd_proofs = self.expr_list()?;
        let land_proofs = self.expr_list()?;
        let lor_proofs = self.expr_list()?;
        let xor_proofs = self.expr_list()?;
        let shift_left_proofs = self.expr_list()?;
        let shift_right_proofs = self.expr_list()?;
        self.st.pin_sets.push(NatOpPinSet {
            toolchain,
            div_pin,
            mod_pin,
            gcd_pin,
            land_pin,
            lor_pin,
            xor_pin,
            shift_left_pin,
            shift_right_pin,
            div_proofs,
            mod_proofs,
            gcd_proofs,
            land_proofs,
            lor_proofs,
            xor_proofs,
            shift_left_proofs,
            shift_right_proofs,
        });
        Ok(())
    }

    /// Read one record, its kind letter already consumed.
    fn record(&mut self, kind: &str) -> Result<(), String> {
        // A file has ONE payload kind (FORMAT.md §7): the header decided
        // which, so the other one's record is an error, not an ignored line.
        if kind == "D" && self.st.pins {
            return self.err("a declaration record 'D' in a con-ron-pins/1 dump".to_string());
        }
        if kind == "S" && !self.st.pins {
            return self.err("a pin-set record 'S' in a con-ron-decls/1 dump".to_string());
        }
        match kind {
            "N" => self.record_name(),
            "L" => self.record_level(),
            "W" => self.record_pw(),
            "E" => self.record_expr(),
            "V" => self.record_cv(),
            "R" => self.record_rule(),
            "C" => self.record_caps(),
            "P" => self.record_table(),
            "I" => self.record_info(),
            "D" => self.record_decl(),
            "S" => self.record_pin_set(),
            _ => self.err(format!("unknown record kind '{}'", kind)),
        }
    }

}

// ---------------------------------------------------------------------------
// The driver
// ---------------------------------------------------------------------------

/// **The reader.**  The inverse of `Write.lean`'s `dumpDecls` and of
/// [`dump_decls`]: `parse_decls(&dump_decls(&ds))` rebuilds `ds`, and
/// `dump_decls(&parse_decls(text)?)` is `text` byte for byte (which is what
/// `con-ron-dump-check --roundtrip` checks on every fixture).
///
/// Errors are `String`s that start with the one-based line number of the
/// offending line, as `Read.lean`'s do.
pub fn parse_decls(text: &str) -> Result<Vec<DeclC>, String> {
    let (ds, _) = parse_decls_counted(text)?;
    Ok(ds)
}

/// [`parse_decls`] plus the record census `con-ron-dump-check` prints.
pub fn parse_decls_counted(text: &str) -> Result<(Vec<DeclC>, Counts), String> {
    let (st, counts) = run_lines_str(text, HEADER, false)?;
    Ok((st.decls, counts))
}

/// **The streaming reader** (task #36).  [`parse_decls_counted`] for a file
/// that is never held in memory: the dump is read a line at a time through a
/// [`BufReader`](std::io::BufReader), so the reader's resident set is the
/// terms it builds plus one line buffer, not the terms *plus the 3 GB of
/// text*.  The format allows it — every reference is backward and every
/// record is one line (FORMAT.md §2) — and the two drivers share every record
/// function below, so they accept exactly the same files with exactly the
/// same messages.
pub fn parse_decls_file(path: &str) -> Result<(Vec<DeclC>, Counts), String> {
    // The path is *not* in the message: both callers prefix it, as they do
    // for a parse error's `line N:`.
    let f = match std::fs::File::open(path) {
        Ok(f) => f,
        Err(e) => return Err(format!("{}", e)),
    };
    let (st, counts) = run_lines_read(std::io::BufReader::with_capacity(1 << 20, f), HEADER, false)?;
    Ok((st.decls, counts))
}

/// [`parse_decls_file`] for any reader, so a test can put the streaming
/// driver and the in-memory one side by side.
pub fn parse_decls_reader<R: std::io::BufRead>(r: R) -> Result<(Vec<DeclC>, Counts), String> {
    let (st, counts) = run_lines_read(r, HEADER, false)?;
    Ok((st.decls, counts))
}

/// **The pin reader** (FORMAT.md §7).  The inverse of [`dump_pins`] and of
/// `Write.lean`'s `dumpPins`: the `Vec<NatOpPinSet>` that
/// `con-ron-check --pins FILE` hands to `check_decls` as its pin-list
/// parameter (DESIGN.md §3.6).
pub fn parse_pins(text: &str) -> Result<Vec<NatOpPinSet>, String> {
    let (ps, _) = parse_pins_counted(text)?;
    Ok(ps)
}

/// [`parse_pins`] plus the record census.
pub fn parse_pins_counted(text: &str) -> Result<(Vec<NatOpPinSet>, Counts), String> {
    let (st, counts) = run_lines_str(text, PINS_HEADER, true)?;
    Ok((st.pin_sets, counts))
}

/// The token spans of one record line, `line.split(' ')` without the `Vec` of
/// `&str`s: the spans carry no lifetime, so one buffer serves every line of
/// the file.  Empty fields are kept, exactly as `split` keeps them, because
/// the record functions reject them by name.
fn split_spans(line: &str, out: &mut Vec<(u32, u32)>) {
    out.clear();
    let b = line.as_bytes();
    let mut start: usize = 0;
    let mut i: usize = 0;
    while i < b.len() {
        if b[i] == b' ' {
            out.push((start as u32, i as u32));
            start = i + 1;
        }
        i += 1;
    }
    out.push((start as u32, b.len() as u32));
}

/// `Read.lean`'s `runLines` minus the line source: the tables, the reusable
/// span buffer, and whether the `end` footer has been seen.  One [`feed`]
/// call per line is the whole pass.
///
/// [`feed`]: Session::feed
struct Session {
    st: Tables,
    spans: Vec<(u32, u32)>,
    saw_footer: bool,
}

impl Session {
    fn new(pins: bool) -> Session {
        Session { st: Tables::new(pins), spans: Vec::new(), saw_footer: false }
    }

    /// One line of the record stream, `line_no` its one-based number in the
    /// file (the header is line 1).  A line's tokens are borrowed only for
    /// the duration of this call, which is what makes the streaming driver
    /// possible.
    fn feed(&mut self, line: &str, line_no: usize) -> Result<(), String> {
        if self.saw_footer {
            if !line.is_empty() {
                return Err(format!("line {}: content after the footer", line_no));
            }
            return Ok(());
        }
        if line.is_empty() {
            return Ok(());
        }
        if line.len() > u32::MAX as usize {
            return Err(format!("line {}: record line is absurdly long", line_no));
        }
        split_spans(line, &mut self.spans);
        let mut r = Rec { st: &mut self.st, line, spans: &self.spans, pos: 0, line_no };
        let kind = r.next_tok()?;
        if kind == "end" {
            let n = r.count()?;
            let want = r.st.payload_len();
            if n != want {
                return r.err(format!(
                    "footer count {} != the {} {} read",
                    n,
                    want,
                    if r.st.pins { "pin sets" } else { "declarations" }
                ));
            }
            if r.pos != r.spans.len() {
                return r.err("trailing fields in the footer".to_string());
            }
            self.saw_footer = true;
        } else {
            r.record(kind)?;
            if r.pos != r.spans.len() {
                return r.err("trailing fields in a record".to_string());
            }
        }
        Ok(())
    }

    /// The end of the file: the footer must have been seen.  `pieces` is how
    /// many `'\n'`-separated pieces followed the header, which is the line
    /// number `Read.lean` names here.
    fn finish(self, pieces: usize) -> Result<(Tables, Counts), String> {
        if !self.saw_footer {
            return Err(format!(
                "line {}: the dump has no 'end' footer",
                pieces + 1
            ));
        }
        let counts = self.st.counts();
        Ok((self.st, counts))
    }
}

/// The header check both drivers do.
fn check_header(hdr: &str, header: &str) -> Result<(), String> {
    if hdr == header {
        Ok(())
    } else {
        Err(format!("bad header: expected '{}', got '{}'", header, hdr))
    }
}

/// `Read.lean`'s `runLines` over a string: check the header, then a single
/// forward pass over the records, stopping at the `end` footer, whose count
/// is the payload's (`Tables::payload_len`).  Unlike task #19's version this
/// no longer collects the lines into a `Vec<&str>` — 1.7 GB of the Mathlib
/// dump's peak was that index (task #36).
fn run_lines_str(text: &str, header: &str, pins: bool) -> Result<(Tables, Counts), String> {
    let mut lines = text.split('\n');
    let hdr = match lines.next() {
        Some(h) => h,
        None => return Err("empty input".to_string()),
    };
    check_header(hdr, header)?;
    let mut sess = Session::new(pins);
    let mut pieces: usize = 0;
    for line in lines {
        pieces += 1;
        sess.feed(line, pieces + 1)?;
    }
    sess.finish(pieces)
}

/// `run_lines_str`'s twin on an `io::BufRead`: the same pass, one line buffer
/// reused for the whole file (task #36).  The piece count is kept equal to
/// the string driver's — a file whose last line ends in `'\n'` has one more
/// `'\n'`-separated piece than it has lines — so the two report the same line
/// numbers, the missing-footer one included.
fn run_lines_read<R: std::io::BufRead>(
    mut rd: R,
    header: &str,
    pins: bool,
) -> Result<(Tables, Counts), String> {
    let mut buf = String::new();
    let mut nl: bool = false;
    let mut read = |buf: &mut String, nl: &mut bool| -> Result<bool, String> {
        buf.clear();
        match rd.read_line(buf) {
            Err(e) => Err(format!("read error: {}", e)),
            Ok(0) => Ok(false),
            Ok(_) => {
                *nl = buf.ends_with('\n');
                if *nl {
                    buf.pop();
                }
                Ok(true)
            }
        }
    };
    if !read(&mut buf, &mut nl)? {
        // An empty file has one empty piece, as `"".split('\n')` does.
        check_header("", header)?;
        return Err("empty input".to_string());
    }
    check_header(&buf, header)?;
    let mut sess = Session::new(pins);
    let mut pieces: usize = 0;
    while read(&mut buf, &mut nl)? {
        pieces += 1;
        sess.feed(&buf, pieces + 1)?;
    }
    if nl {
        // The empty piece after the file's final newline: the string driver
        // sees it (and skips it), so the line count must count it too.
        pieces += 1;
    }
    sess.finish(pieces)
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use con_ron_core::ron::nat;

    fn nm(s: &str) -> Name {
        let cps: Vec<u32> = s.chars().map(|c| c as u32).collect();
        name::mk_str(name::anonymous(), cps)
    }

    fn cps(s: &str) -> Vec<u32> {
        s.chars().map(|c| c as u32).collect()
    }

    fn cv(s: &str) -> ConstantVal {
        ConstantVal {
            name: nm(s),
            level_params: Vec::new(),
            ty: expr::sort(level::zero()),
        }
    }

    /// The error of a failed parse.  `unwrap_err` is unavailable: neither
    /// `DeclC` nor `NatOpPinSet` derives `Debug` (DESIGN.md §3.4).
    fn decls_err(text: &str) -> String {
        match parse_decls(text) {
            Ok(_) => panic!("this dump must not parse"),
            Err(e) => e,
        }
    }

    fn pins_err(text: &str) -> String {
        match parse_pins(text) {
            Ok(_) => panic!("this dump must not parse"),
            Err(e) => e,
        }
    }

    /// A pin variant whose eight pins and sixteen proof blobs are distinct
    /// terms, plus one node deliberately *shared* between two of them: the
    /// sharing is what FORMAT.md §7 is for, so the round trip has to keep it.
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
        }
    }

    // --- `con-ron-pins/1` (FORMAT.md §7) -----------------------------------

    #[test]
    fn a_pin_dump_round_trips() {
        let ss = vec![a_pin_set("lean4:v4.33.0"), a_pin_set("lean4-nightly")];
        let text = dump_pins(&ss);
        assert!(text.starts_with("con-ron-pins/1\n"));
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
        assert_eq!(h.join().unwrap(), 3);
    }

    #[test]
    fn an_empty_pin_list_round_trips() {
        let text = dump_pins(&Vec::new());
        assert_eq!(text, "con-ron-pins/1\nend 0\n");
        assert_eq!(parse_pins(&text).unwrap().len(), 0);
    }

    /// A file has one payload kind: the header decides, and the wrong payload
    /// record is an error rather than a silently ignored line.
    #[test]
    fn the_two_payloads_do_not_mix() {
        // an `S` record in a declaration dump
        let bad = "con-ron-decls/1\nS 0  0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0\nend 0\n";
        assert!(decls_err(bad).contains("con-ron-decls/1 dump"), "{}", decls_err(bad));
        // a `D` record in a pin dump
        let bad = "con-ron-pins/1\nD b nat\nend 0\n";
        assert!(pins_err(bad).contains("con-ron-pins/1 dump"), "{}", pins_err(bad));
        // each reader rejects the other's header
        assert!(parse_pins(&dump_decls(&Vec::new())).is_err());
        assert!(parse_decls(&dump_pins(&Vec::new())).is_err());
        // and the footer counts the pin sets
        let ss = vec![a_pin_set("t")];
        let text = dump_pins(&ss).replace("end 1", "end 2");
        assert!(pins_err(&text).contains("pin sets read"), "{}", pins_err(&text));
    }

    // --- the string codec, mirroring `Read.lean`'s `#guard`s ---------------

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
        // the degenerate escape `Read.lean` accepts: no digits, i.e. U+0000
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

    // --- task #9's normalisation claim, on the reader's side ---------------

    /// FORMAT.md §4's `W` record says the list is canonical on the wire and
    /// that `if_all_zero` re-normalising it is the identity
    /// (`PropWhen.ifAllZero_toList`).  The port normalises too (task #9), so
    /// this is the check that re-normalising a canonical list changes nothing
    /// — which is what lets the reader hand the list straight to the smart
    /// constructor.
    #[test]
    fn canonical_list_renormalises_to_itself() {
        let raw: Vec<Name> = vec![
            nm("c"),
            nm("a"),
            nm("b"),
            nm("a"),
            name::mk_num(nm("a"), 3),
            nm("zz"),
        ];
        let pw = prop_when::if_all_zero(raw);
        let canonical = prop_when::to_list(&pw);
        // canonical: sorted by `Name.cmp`, duplicate-free
        assert_eq!(canonical.len(), 5);
        for i in 1..canonical.len() {
            assert!(prop_when::name_lt(&canonical[i - 1], &canonical[i]));
        }
        // ... and feeding it back is the identity, on the datum and on the list
        let again = prop_when::if_all_zero(prop_when::to_list(&pw));
        assert!(prop_when::beq(&pw, &again));
        assert!(prop_when::names_beq(&canonical, &prop_when::to_list(&again)));
        assert_eq!(prop_when::hash_pw(&pw), prop_when::hash_pw(&again));
        // `never` is not `if_all_zero []` (task #10, surprise 6)
        assert!(prop_when::to_list_opt(&prop_when::never()).is_none());
        assert!(!prop_when::beq(
            &prop_when::never(),
            &prop_when::if_all_zero(Vec::new())
        ));
    }

    // --- the round trip over every constructor -----------------------------

    /// A `DeclC` list that uses **every** `DeclC` constructor, every
    /// `ConstantInfo` constructor, every `ExprKind`, every `LevelKind`, every
    /// `Name` constructor, both `Literal`s, all three `ReducibilityHint`s, all
    /// three `RecRuleFire`s, all six `BasisKind`s, and a `ProjTable` — none of
    /// which the fixture corpus produces in full (task #10, surprise 3).
    fn kitchen_sink() -> Vec<DeclC> {
        let u = level::param(nm("u"));
        let lvls = vec![
            level::zero(),
            level::succ(level::zero()),
            level::max(level::dup(&u), level::zero()),
            level::imax(level::dup(&u), level::succ(level::dup(&u))),
        ];
        let pw = prop_when::if_all_zero(vec![nm("u"), nm("v")]);
        let big = natdec::from_decimal("123456789012345678901234567890").unwrap();
        let deep = expr::app(
            expr::app(
                expr::mk_const(nm("f"), vec![level::dup(&u)]),
                expr::mk_bvar(0),
            ),
            expr::lam(
                expr::sort(level::dup(&u)),
                expr::forall_e(
                    expr::mk_bvar(1),
                    expr::let_e(
                        expr::sort(level::zero()),
                        expr::lit(expr::literal_nat(big)),
                        expr::proj(nm("S"), 2, expr::mk_bvar(0)),
                    ),
                    expr::binder_meta(prop_when::never()),
                ),
                expr::binder_meta(prop_when::dup(&pw)),
            ),
        );
        let with_fvar = expr::fvar(7, expr::lit(expr::literal_str(cps("a b\\c\n∀"))));
        let tbl = ProjTable {
            struct_name: nm("S"),
            level_params: vec![nm("u"), nm("v")],
            num_params: 1,
            ctor: nm("S.mk"),
            num_fields: 2,
            struct_sort: level::dup(&u),
            bodies: vec![expr::mk_bvar(0), expr::dup(&deep)],
            guards: vec![level::zero(), level::dup(&u)],
            off: 3,
        };
        let caps = IndCaps {
            eta: true,
            eta_ctor: nm("S.mk"),
            eta_params: 1,
            eta_fields: 2,
            unitlike: true,
            unit_params: 4,
            rule_k: true,
            sort_z: prop_when::dup(&pw),
        };
        let rules = vec![
            env::rec_rule_parsed(nm("T.mk"), 0, expr::mk_bvar(0)),
            RecRule {
                ctor: nm("T.mk2"),
                nfields: 2,
                ctor_params: 1,
                fire: RecRuleFire::Plain,
                rhs: expr::dup(&deep),
                k: true,
                eta: false,
                params_blind: true,
            },
            RecRule {
                ctor: nm("T.mk3"),
                nfields: 1,
                ctor_params: 2,
                fire: RecRuleFire::Nested(
                    vec![level::dup(&u), level::zero()],
                    vec![expr::dup(&with_fvar), expr::mk_bvar(3)],
                ),
                rhs: expr::mk_bvar(1),
                k: false,
                eta: true,
                params_blind: false,
            },
        ];
        let block = vec![
            ConstantInfo::IndInfo(cv("T"), caps),
            ConstantInfo::CtorInfo(cv("T.mk"), 1, 2),
            ConstantInfo::RecInfo(cv("T.rec"), 3, 4, rules),
            ConstantInfo::AxiomInfo(cv("T.ax")),
            ConstantInfo::DefnInfo(
                cv("T.d"),
                expr::dup(&deep),
                ReducibilityHint::Regular(17),
            ),
            ConstantInfo::ThmInfo(cv("T.t"), expr::dup(&with_fvar)),
            ConstantInfo::ProjInfo(tbl),
        ];
        vec![
            DeclC::AxiomDecl(ConstantVal {
                name: name::mk_num(nm("ax"), 9),
                level_params: vec![nm("u"), nm("v")],
                ty: expr::sort(level::dup(&lvls[3])),
            }),
            DeclC::DefnDecl(cv("d1"), expr::dup(&deep), ReducibilityHint::Opaque),
            DeclC::DefnDecl(cv("d2"), expr::mk_bvar(0), ReducibilityHint::Abbrev),
            DeclC::DefnDecl(
                cv("d3"),
                expr::sort(level::dup(&lvls[2])),
                ReducibilityHint::Regular(0),
            ),
            DeclC::ThmDecl(cv("t1"), expr::dup(&with_fvar)),
            DeclC::OpaqueDecl(cv("o1"), expr::lit(expr::literal_str(Vec::new()))),
            DeclC::BasisDecl(BasisKind::EqK),
            DeclC::BasisDecl(BasisKind::NatK),
            DeclC::BasisDecl(BasisKind::PunitK),
            DeclC::BasisDecl(BasisKind::EmptyK),
            DeclC::BasisDecl(BasisKind::FalseK),
            DeclC::BasisDecl(BasisKind::QuotK),
            DeclC::IndDecl(block, 1),
        ]
    }

    #[test]
    fn the_kitchen_sink_round_trips_byte_for_byte() {
        let ds = kitchen_sink();
        let text = dump_decls(&ds);
        assert!(text.starts_with("con-ron-decls/1\n"));
        assert!(text.ends_with("\nend 13\n"));
        let (back, counts) = parse_decls_counted(&text).unwrap();
        assert_eq!(counts.decls, 13);
        assert_eq!(counts.axiom_decls, 1);
        assert_eq!(counts.defn_decls, 3);
        assert_eq!(counts.thm_decls, 1);
        assert_eq!(counts.opaque_decls, 1);
        assert_eq!(counts.basis_decls, 6);
        assert_eq!(counts.ind_decls, 1);
        assert_eq!(counts.block_infos, 7);
        assert_eq!(counts.tables, 1);
        assert_eq!(counts.caps, 1);
        assert_eq!(counts.rules, 3);
        let again = dump_decls(&back);
        assert_eq!(text, again);
        // and a second pass is still a fixed point
        assert_eq!(dump_decls(&parse_decls(&again).unwrap()), again);
    }

    /// The reader must hand back the *DAG*, not its tree expansion: the
    /// sub-term shared between `d1`'s value and the `indDecl` block's
    /// `defnInfo` value has to come back as one `Rc`.
    #[test]
    fn sharing_survives_the_round_trip() {
        let ds = kitchen_sink();
        let back = parse_decls(&dump_decls(&ds)).unwrap();
        let a = match &back[1] {
            DeclC::DefnDecl(_, v, _) => expr::dup(v),
            _ => panic!("expected d1"),
        };
        let b = match &back[12] {
            DeclC::IndDecl(block, _) => match &block[4] {
                ConstantInfo::DefnInfo(_, v, _) => expr::dup(v),
                _ => panic!("expected T.d"),
            },
            _ => panic!("expected the block"),
        };
        assert!(expr::ptr_eq(&a, &b), "the shared subterm was duplicated");
        // ... and the bvar 0 under it is the same node as the top-level one
        let d2 = match &back[2] {
            DeclC::DefnDecl(_, v, _) => expr::dup(v),
            _ => panic!("expected d2"),
        };
        match &a.0.kind {
            expr::ExprKind::App(f, _) => match &f.0.kind {
                expr::ExprKind::App(_, arg) => {
                    assert!(expr::ptr_eq(arg, &d2), "bvar 0 was not interned")
                }
                _ => panic!("shape"),
            },
            _ => panic!("shape"),
        }
    }

    /// FORMAT.md §6.1 on real-ish data: the parsed term reaches exactly as many
    /// distinct heap nodes as the dump has records, so nothing was duplicated.
    #[test]
    fn the_dag_census_matches_the_record_counts() {
        let (ds, counts) = parse_decls_counted(&dump_decls(&kitchen_sink())).unwrap();
        let cen = dag::census(&ds);
        assert_eq!(
            (cen.names, cen.levels, cen.exprs),
            (counts.names, counts.levels, counts.exprs)
        );
        // ... whereas the *hand-built* list shares less than the dump does:
        // `kitchen_sink` writes `expr::mk_bvar(0)` several times over, and the
        // dump interns them, so the round trip strictly increases sharing.
        let before = dag::census(&kitchen_sink());
        assert!(before.exprs > cen.exprs);
    }

    // --- the failure modes -------------------------------------------------

    /// `DeclC` derives no `Debug` (con-leche derives nothing on it, task #10),
    /// so `Result::unwrap_err` is unavailable: this is it, by hand.
    fn perr(text: &str) -> String {
        match parse_decls(text) {
            Ok(_) => panic!("expected a parse error"),
            Err(e) => e,
        }
    }

    #[test]
    fn parse_errors_name_the_line() {
        assert!(perr("").contains("bad header"));
        assert!(perr("con-ron-decls/2\nend 0\n").contains("bad header"));
        assert!(perr("con-ron-decls/1\n").contains("no 'end' footer"));

        // a forward reference
        assert_eq!(
            perr("con-ron-decls/1\nN 0 s 0 1 a\nend 0\n"),
            "line 2: name id 0 is not defined yet"
        );
        // a wrong own id
        assert_eq!(
            perr("con-ron-decls/1\nN 1 a\nend 0\n"),
            "line 2: name id 1, expected 0"
        );
        // an unknown kind letter, and an unknown constructor letter
        assert_eq!(
            perr("con-ron-decls/1\nX 0 a\nend 0\n"),
            "line 2: unknown record kind 'X'"
        );
        assert_eq!(
            perr("con-ron-decls/1\nN 0 q\nend 0\n"),
            "line 2: unknown name record 'q'"
        );
        // a bad footer count, trailing fields, content after the footer
        assert!(perr("con-ron-decls/1\nN 0 a\nend 1\n")
            .starts_with("line 3: footer count 1 != the 0"));
        assert_eq!(
            perr("con-ron-decls/1\nN 0 a 7\nend 0\n"),
            "line 2: trailing fields in a record"
        );
        assert_eq!(
            perr("con-ron-decls/1\nend 0\nN 0 a\n"),
            "line 3: content after the footer"
        );
        // the redundant string length is cross-checked
        assert_eq!(
            perr("con-ron-decls/1\nN 0 a\nN 1 s 0 2 a\nend 0\n"),
            "line 3: string length 1 != the declared 2"
        );
        // an index that does not fit a machine word (DESIGN.md §3.3)
        assert!(
            perr("con-ron-decls/1\nE 0 b 99999999999999999999999\nend 0\n")
                .contains("does not fit a 64-bit index")
        );
        // but an unbounded `natVal` literal does fit
        assert!(
            parse_decls("con-ron-decls/1\nE 0 n 99999999999999999999999\nend 0\n")
                .is_ok()
        );
        // every record kind's own truncation, and a bad bool
        assert!(perr("con-ron-decls/1\nE 0 a 0 0\nend 0\n")
            .contains("expr id 0 is not defined yet"));
        assert!(perr("con-ron-decls/1\nL 0\nend 0\n").contains("unexpected end of record"));
        assert!(perr("con-ron-decls/1\nW 0 x\nend 0\n").contains("unknown propwhen record"));
        assert!(perr("con-ron-decls/1\nD b bogus\nend 1\n").contains("unknown basis kind"));

        // a mutilated real dump fails, never silently succeeds
        let ok = dump_decls(&kitchen_sink());
        assert!(perr(&ok.replace("end 13", "end 12")).contains("footer count"));
        assert!(!perr(&ok.lines().take(20).collect::<Vec<_>>().join("\n")).is_empty());
    }

    #[test]
    fn an_empty_declaration_list_round_trips() {
        let ds: Vec<DeclC> = Vec::new();
        let t = dump_decls(&ds);
        assert_eq!(t, "con-ron-decls/1\nend 0\n");
        assert!(parse_decls(&t).unwrap().is_empty());
        // blank lines are ignored
        assert!(parse_decls("con-ron-decls/1\n\n\nend 0\n\n").unwrap().is_empty());
    }

    /// Task #36: the streaming driver is the same reader.  Every sample this
    /// module has — the kitchen sink, an empty list, a pin dump — must come
    /// back identical through `parse_decls_reader`, and every error must come
    /// back with the same message *and the same line number*, which is the
    /// part the two line-counting conventions could break.
    #[test]
    fn the_streaming_driver_agrees_with_the_string_one() {
        fn both(text: &str) -> (Result<usize, String>, Result<usize, String>) {
            let a = parse_decls_counted(text).map(|(ds, _)| ds.len());
            let b = parse_decls_reader(std::io::Cursor::new(text.as_bytes()))
                .map(|(ds, _)| ds.len());
            (a, b)
        }
        let ok = dump_decls(&kitchen_sink());
        let (a, b) = both(&ok);
        assert_eq!(a, b);
        assert_eq!(b.unwrap(), kitchen_sink().len());
        // the re-dump off the streamed parse is byte-identical too
        let ds = parse_decls_reader(std::io::Cursor::new(ok.as_bytes())).unwrap().0;
        assert_eq!(dump_decls(&ds), ok);
        assert_eq!(dag::census(&ds).exprs, parse_decls_counted(&ok).unwrap().1.exprs);

        for text in [
            "",
            "con-ron-decls/1",
            "con-ron-decls/1\n",
            "con-ron-decls/1\nend 0\n",
            "con-ron-decls/1\n\n\nend 0\n\n",
            "con-ron-pins/1\nend 0\n",
            "con-ron-decls/1\nN 0 a\nend 0",
            "con-ron-decls/1\nN 0 a\n",
            "con-ron-decls/1\nN 1 a\nend 0\n",
            "con-ron-decls/1\nN 0 a\nX 0\nend 0\n",
            "con-ron-decls/1\nend 0\nN 0 a\n",
            "con-ron-decls/1\nend 0 7\n",
            &ok.replace("end 13", "end 12"),
        ] {
            let (a, b) = both(text);
            assert_eq!(a, b, "the two drivers disagree on {:?}", text);
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
        // An `ExprKind` is as wide as its widest variant.  Before task #38
        // that was `lam`/`forallE`, whose `BinderMeta` was a `PropWhen` *by
        // value* — 24 bytes, since `PropWhenRepr::Many(Vec<Name>)` is 24 and
        // the other four arms hide in the `Vec`'s niche — so 40 bytes of
        // payload, 48 with the discriminant, 56 with the cached `data` word
        // and 72 of heap once `Rc`'s two counts were in front, while 85 % of
        // the nodes are `app`, which needs 16.
        //
        // With the binder datum, a `const`'s level list and a literal's two
        // payloads behind handles, **three** arms are the widest and all are
        // 24 bytes: `lam`/`forallE` (two handles and the datum's), `letE`
        // (three handles) and `proj` (a name, a `u64` and a handle).  24 + 8
        // of discriminant is 32, + 8 of `data` is 40, + 16 of counts is 56.
        // Going below that means a handle for those three arms too, which
        // buys 8 bytes a node and costs a 40-byte block per binder — see
        // DESIGN.md's task-#38 entry for why that is not worth it.
        assert_eq!(std::mem::size_of::<PropWhen>(), 24);
        assert_eq!(std::mem::size_of::<BinderMeta>(), 8);
        assert_eq!(std::mem::size_of::<Literal>(), 16);
        assert_eq!(std::mem::size_of::<ExprKind>(), 32);
        assert_eq!(std::mem::size_of::<ExprNode>(), 40);
        assert_eq!(expr_node_bytes(), 56);
        assert_eq!(std::mem::size_of::<NameNode>(), 40);
        assert_eq!(std::mem::size_of::<LevelNode>(), 32);
        // the id tables cost one machine word per record, the `Rc` handle
        assert_eq!(std::mem::size_of::<Expr>(), 8);
        assert_eq!(std::mem::size_of::<Name>(), 8);
        assert_eq!(std::mem::size_of::<Level>(), 8);
    }
}
