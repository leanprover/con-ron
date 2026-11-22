//! The Rust reader of the `con-ron-pins/2` dump format: test-only, the oracle
//! the verified decoder (`kernel::pins_decode::decode`) and the writer
//! (`crate::write`) are checked against.

use con_ron_core::kernel::expr;
use con_ron_core::kernel::expr::Expr;
use con_ron_core::kernel::level;
use con_ron_core::kernel::level::Level;
use con_ron_core::kernel::name;
use con_ron_core::kernel::name::Name;
use con_ron_core::kernel::nat_op_pins::NatOpPinSet;
use con_ron_core::ron::nat::Nat;

use crate::natdec;
use crate::shown;
use crate::PINS_HEADER;

// ---------------------------------------------------------------------------
// String fields
// ---------------------------------------------------------------------------

/// Is `c` a Lean `Char`?  `Nat.isValidChar`: below `U+D800`, or above
/// `U+DFFF` and below `U+110000`.  The surrogate range is not a code point on
/// either side of the format.
pub fn is_valid_char(c: u32) -> bool {
    c < 0xd800 || (0xdfff < c && c < 0x11_0000)
}

/// Undo `Pins.lean`'s `escapeString`: a literal printable non-backslash
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
/// pin variants the payload has.  Nothing in the reader depends on it; it is
/// what a caller prints and what the round-trip tests compare the DAG census
/// against.
#[derive(Debug, Default, Clone, Copy, PartialEq, Eq)]
pub struct Counts {
    pub names: usize,
    pub levels: usize,
    pub exprs: usize,
    /// The `S` records, i.e. the pin variants.
    pub pin_sets: usize,
}

// ---------------------------------------------------------------------------
// The reader's state
// ---------------------------------------------------------------------------

/// One `Vec` per id space: the reader's whole persistent state, the mirror of
/// the Lean reader's `RState` minus the current record.  It is deliberately free
/// of any borrow of the input (task #36): the reader reads the dump one line
/// at a time and never holds the text, so this struct outlives every line
/// buffer and the cursor over the current line ([`Rec`]) is built fresh per
/// record.
struct Tables {
    names: Vec<Name>,
    levels: Vec<Level>,
    exprs: Vec<Expr>,
    /// The payload: the `S` records (FORMAT.md §4).
    pin_sets: Vec<NatOpPinSet>,
}

impl Tables {
    fn new() -> Tables {
        Tables {
            names: Vec::new(),
            levels: Vec::new(),
            exprs: Vec::new(),
            pin_sets: Vec::new(),
        }
    }

    fn counts(&self) -> Counts {
        Counts {
            names: self.names.len(),
            levels: self.levels.len(),
            exprs: self.exprs.len(),
            pin_sets: self.pin_sets.len(),
        }
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
    /// `Pins.lean`'s `rerr`: fail, naming the line.
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
            return self.err(format!("expected a decimal number, got {}", crate::shown(t)));
        }
        match t.parse::<u64>() {
            Ok(n) => Ok(n),
            Err(_) => self.err(format!(
                "decimal number {} does not fit a 64-bit index (DESIGN.md §3.3)",
                crate::shown(t)
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

    fn expr_ref(&mut self) -> Result<Expr, String> {
        let i = self.count()?;
        if i < self.st.exprs.len() {
            Ok(expr::dup(&self.st.exprs[i]))
        } else {
            self.err(format!("expr id {} is not defined yet", i))
        }
    }

    // --- counted lists -----------------------------------------------------

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

    fn type_pin_list(&mut self) -> Result<Vec<(Name, Expr)>, String> {
        let n = self.count()?;
        let mut v: Vec<(Name, Expr)> = Vec::new();
        for _ in 0..n {
            let nm = self.name_ref()?;
            let ty = self.expr_ref()?;
            v.push((nm, ty));
        }
        Ok(v)
    }

    // --- inline enumerations ----------------------------------------------

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
            return self.err(format!("unknown name record {}", crate::shown(t)));
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
            return self.err(format!("unknown level record {}", crate::shown(t)));
        };
        self.st.levels.push(v);
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
            expr::bvar(i)
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
            expr::lam(ty, b)
        } else if t == "f" {
            let ty = self.expr_ref()?;
            let b = self.expr_ref()?;
            expr::forall_e(ty, b)
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
            return self.err(format!("unknown expr record {}", crate::shown(t)));
        };
        self.st.exprs.push(v);
        Ok(())
    }

    /// `S` — `ConLeche/Kernel/NatOpPinSet.lean:30` (FORMAT.md §4).  No id,
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
        let div_type_pins = self.type_pin_list()?;
        let mod_type_pins = self.type_pin_list()?;
        let gcd_type_pins = self.type_pin_list()?;
        let land_type_pins = self.type_pin_list()?;
        let lor_type_pins = self.type_pin_list()?;
        let xor_type_pins = self.type_pin_list()?;
        let shift_left_type_pins = self.type_pin_list()?;
        let shift_right_type_pins = self.type_pin_list()?;
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
            div_type_pins,
            mod_type_pins,
            gcd_type_pins,
            land_type_pins,
            lor_type_pins,
            xor_type_pins,
            shift_left_type_pins,
            shift_right_type_pins,
        });
        Ok(())
    }

    /// Read one record, its kind letter already consumed.
    fn record(&mut self, kind: &str) -> Result<(), String> {
        match kind {
            "N" => self.record_name(),
            "L" => self.record_level(),
            "E" => self.record_expr(),
            "S" => self.record_pin_set(),
            _ => self.err(format!("unknown record kind {}", crate::shown(kind))),
        }
    }
}

// ---------------------------------------------------------------------------
// The driver
// ---------------------------------------------------------------------------

/// **The reader** (FORMAT.md).  The inverse of [`dump_pins`] and of
/// `Pins.lean`'s `dumpPins`: `parse_pins(&dump_pins(&ss))` rebuilds `ss`, and
/// `dump_pins(&parse_pins(text)?)` is `text` byte for byte, and on the embedded
/// text it is `kernel::pins_decode::decode_embedded`'s answer.
///
/// Errors are `String`s that start with the one-based line number of the
/// offending line, as the Lean reader's do.
pub fn parse_pins(text: &str) -> Result<Vec<NatOpPinSet>, String> {
    let (ps, _) = parse_pins_counted(text)?;
    Ok(ps)
}

/// [`parse_pins`] plus the record census.
pub fn parse_pins_counted(text: &str) -> Result<(Vec<NatOpPinSet>, Counts), String> {
    let (st, counts) = run_lines_str(text, PINS_HEADER)?;
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

/// `Pins.lean`'s `runLines` minus the line source: the tables, the reusable
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
    fn new() -> Session {
        Session { st: Tables::new(), spans: Vec::new(), saw_footer: false }
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
            let want = r.st.pin_sets.len();
            if n != want {
                return r.err(format!("footer count {} != the {} pin sets read", n, want));
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
    /// number `Pins.lean` names here.
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
        Err(format!("bad header: expected '{}', got {}", header, shown(hdr)))
    }
}

/// `Pins.lean`'s `runLines` over a string: check the header, then a single
/// forward pass over the records, stopping at the `end` footer, whose count
/// is the payload's (`Tables::payload_len`).  Unlike task #19's version this
/// no longer collects the lines into a `Vec<&str>` — 1.7 GB of the Mathlib
/// dump's peak was that index (task #36).
fn run_lines_str(text: &str, header: &str) -> Result<(Tables, Counts), String> {
    let mut lines = text.split('\n');
    let hdr = match lines.next() {
        Some(h) => h,
        None => return Err("empty input".to_string()),
    };
    check_header(hdr, header)?;
    let mut sess = Session::new();
    let mut pieces: usize = 0;
    for line in lines {
        pieces += 1;
        sess.feed(line, pieces + 1)?;
    }
    sess.finish(pieces)
}

