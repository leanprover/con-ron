//! The Rust writer for `con-ron-pins/1` — a transliteration of the Lean
//! writer in `proof/ConRon/Dump/Pins.lean`, emission order included.
//!
//! It exists to make the reader testable without the Lean side: `dump_pins`
//! is a left inverse of [`crate::parse_pins`] *on the nose*, so a re-dump can
//! be diffed against the input file byte for byte and a single wrong field
//! anywhere shows up as a diff.  That is a much sharper test than "it
//! parsed": every id, every list length, every escape and the whole emission
//! order have to agree with Lean's writer.  `scripts/gen-pins.sh` depends on
//! exactly that agreement — the embedded `PINS_TEXT` of the verified core is
//! the Lean writer's bytes, and the unit tests here re-derive them.
//!
//! Byte-identity needs three things to match the Lean writer exactly:
//!
//! 1. **The interning tables.**  `N`, `L`, `W` and `E` are keyed by *value*
//!    (the core's own `beq` and cached hash, via the key wrappers below), as
//!    Lean's `Std.HashMap Expr Nat` is; the `S` payload records are merely
//!    counted.
//! 2. **The `Expr` worklist.**  The Lean writer pushes `(e, false)`, pops from
//!    the end, and on a first visit pushes `(e, true)` and then the children in
//!    constructor order — so the *last* child is emitted first.  The loop below
//!    is that loop.  It is a worklist and not recursion for the same reason:
//!    application spines tens of thousands of nodes deep (task #10).
//! 3. **The order within a node.**  `wName`/`wLevel`/`wPw` run at *emit* time,
//!    so `N`, `L` and `W` records interleave with the `E` records exactly where
//!    Lean puts them.
//!
//! Nothing here is part of the verified core; see the crate docs.

use std::collections::HashMap;
use std::hash::Hash;
use std::hash::Hasher;

use con_ron_core::kernel::expr;
use con_ron_core::kernel::expr::Expr;
use con_ron_core::kernel::expr::ExprView;
use con_ron_core::kernel::expr::Literal;
use con_ron_core::kernel::level;
use con_ron_core::kernel::level::Level;
use con_ron_core::kernel::level::LevelKind;
use con_ron_core::kernel::name;
use con_ron_core::kernel::name::Name;
use con_ron_core::kernel::name::NameKind;
use con_ron_core::kernel::nat_op_pins::NatOpPinSet;
use con_ron_core::kernel::prop_when;
use con_ron_core::kernel::prop_when::PropWhen;

use crate::natdec;
use crate::PINS_HEADER;

// ---------------------------------------------------------------------------
// Scalars
// ---------------------------------------------------------------------------

/// One code point, escaped: a literal printable non-backslash ASCII byte, or
/// `\<lowercase-hex>;`.  `Pins.lean`'s `escChar` and `escapeString`.
pub fn escape_string(s: &[u32]) -> String {
    let mut out = String::new();
    for &c in s {
        if (0x21..=0x7e).contains(&c) && c != 0x5c {
            out.push(c as u8 as char);
        } else {
            out.push('\\');
            out.push_str(&format!("{:x}", c));
            out.push(';');
        }
    }
    out
}

/// A string as the *two* fields the format uses: the code-point count, then
/// the escaped text (empty exactly when the count is `0`, which is why a
/// record can end in a space).
pub fn str_field(s: &[u32]) -> String {
    format!("{} {}", s.len(), escape_string(s))
}

/// A counted id list: the length, then the ids.
fn id_list(ids: &[usize]) -> String {
    let mut out = ids.len().to_string();
    for i in ids {
        out.push(' ');
        out.push_str(&i.to_string());
    }
    out
}

// ---------------------------------------------------------------------------
// Interning keys
// ---------------------------------------------------------------------------
//
// The core deliberately does not implement `PartialEq`/`Hash`: its equality is
// `beq` (pointer, then cached hash, then structure) and its hash is the stored
// computed field, both as one-method traits of its own (task #7).  These
// wrappers hand those to `std::collections::HashMap`, so the writer interns by
// the same notion of equality `Pins.lean`'s `Std.HashMap` uses.

macro_rules! key {
    ($k:ident, $t:ty, $hash:path, $eq:path) => {
        struct $k($t);
        impl Hash for $k {
            fn hash<H: Hasher>(&self, st: &mut H) {
                st.write_u64($hash(&self.0));
            }
        }
        impl PartialEq for $k {
            fn eq(&self, other: &Self) -> bool {
                $eq(&self.0, &other.0)
            }
        }
        impl Eq for $k {}
    };
}

key!(NameKey, Name, name::hash_data, name::beq);
key!(LevelKey, Level, level::hash_data, level::beq);
key!(ExprKey, Expr, expr::hash, expr::beq);
key!(PwKey, PropWhen, prop_when::hash_pw, prop_when::beq);

// ---------------------------------------------------------------------------
// The writer's state
// ---------------------------------------------------------------------------

/// `Pins.lean`'s `WState`: the output, one interning table per interned id
/// space and one counter per numbered one.
struct Writer {
    buf: String,
    names: HashMap<NameKey, usize>,
    levels: HashMap<LevelKey, usize>,
    pws: HashMap<PwKey, usize>,
    exprs: HashMap<ExprKey, usize>,
    n_s: usize,
}

impl Writer {
    fn new() -> Writer {
        Writer {
            buf: String::new(),
            names: HashMap::new(),
            levels: HashMap::new(),
            pws: HashMap::new(),
            exprs: HashMap::new(),
            n_s: 0,
        }
    }

    fn emit(&mut self, line: &str) {
        self.buf.push_str(line);
        self.buf.push('\n');
    }

    // --- names, levels, the zero-ness datum -------------------------------

    /// Emit a name and its prefix chain, returning its id.  Recursion is fine
    /// here: a `Name` is a prefix list, not a term.
    fn w_name(&mut self, n: &Name) -> usize {
        if let Some(&i) = self.names.get(&NameKey(name::dup(n))) {
            return i;
        }
        let body = match &n.0.kind {
            NameKind::Anonymous => "a".to_string(),
            NameKind::Str(p, s) => {
                let pi = self.w_name(p);
                format!("s {} {}", pi, str_field(s))
            }
            NameKind::Num(p, k) => {
                let pi = self.w_name(p);
                format!("n {} {}", pi, k)
            }
        };
        let id = self.names.len();
        self.names.insert(NameKey(name::dup(n)), id);
        self.emit(&format!("N {} {}", id, body));
        id
    }

    /// Emit a level, returning its id.
    fn w_level(&mut self, u: &Level) -> usize {
        if let Some(&i) = self.levels.get(&LevelKey(level::dup(u))) {
            return i;
        }
        let body = match &u.0.kind {
            LevelKind::Zero => "z".to_string(),
            LevelKind::Succ(v) => {
                let i = self.w_level(v);
                format!("s {}", i)
            }
            LevelKind::Max(a, b) => {
                let i = self.w_level(a);
                let j = self.w_level(b);
                format!("m {} {}", i, j)
            }
            LevelKind::Imax(a, b) => {
                let i = self.w_level(a);
                let j = self.w_level(b);
                format!("i {} {}", i, j)
            }
            LevelKind::Param(n) => {
                let i = self.w_name(n);
                format!("p {}", i)
            }
        };
        let id = self.levels.len();
        self.levels.insert(LevelKey(level::dup(u)), id);
        self.emit(&format!("L {} {}", id, body));
        id
    }

    /// Emit a `PropWhen` through its public API (`to_list_opt`), returning its
    /// id.  The representation is private on both sides; the wire form is the
    /// canonical name list.
    fn w_pw(&mut self, pw: &PropWhen) -> usize {
        if let Some(&i) = self.pws.get(&PwKey(prop_when::dup(pw))) {
            return i;
        }
        let body = match prop_when::to_list_opt(pw) {
            None => "n".to_string(),
            Some(ps) => {
                let ids: Vec<usize> = ps.iter().map(|p| self.w_name(p)).collect();
                format!("z {}", id_list(&ids))
            }
        };
        let id = self.pws.len();
        self.pws.insert(PwKey(prop_when::dup(pw)), id);
        self.emit(&format!("W {} {}", id, body));
        id
    }

    // --- expressions -------------------------------------------------------

    /// The id of an already-emitted node (`Pins.lean`'s `eid`, `getD e 0`).
    fn eid(&self, e: &Expr) -> usize {
        match self.exprs.get(&ExprKey(expr::dup(e))) {
            Some(&i) => i,
            None => 0,
        }
    }

    /// Emit one node, all of whose `Expr` children are already emitted.
    fn emit_expr_node(&mut self, e: &Expr) {
        let body = match expr::view(&e) {
            ExprView::Bvar(i) => format!("b {}", i),
            ExprView::Fvar(idx, ty) => format!("v {} {}", idx, self.eid(ty)),
            ExprView::Sort(u) => {
                let l = self.w_level(u);
                format!("s {}", l)
            }
            ExprView::Const(n, us) => {
                let ni = self.w_name(n);
                let ls: Vec<usize> = us.iter().map(|u| self.w_level(u)).collect();
                format!("c {} {}", ni, id_list(&ls))
            }
            ExprView::App(f, a) => format!("a {} {}", self.eid(f), self.eid(a)),
            ExprView::Lam(ty, b, m) => {
                let t = self.eid(ty);
                let bi = self.eid(b);
                let p = self.w_pw(&m.pw);
                format!("l {} {} {}", t, bi, p)
            }
            ExprView::ForallE(ty, b, m) => {
                let t = self.eid(ty);
                let bi = self.eid(b);
                let p = self.w_pw(&m.pw);
                format!("f {} {} {}", t, bi, p)
            }
            ExprView::LetE(ty, v, b) => {
                format!("t {} {} {}", self.eid(ty), self.eid(v), self.eid(b))
            }
            ExprView::Lit(Literal::NatVal(n)) => format!("n {}", natdec::to_decimal(n)),
            ExprView::Lit(Literal::StrVal(s)) => format!("g {}", str_field(s)),
            ExprView::Proj(sn, i, s) => {
                let ni = self.w_name(sn);
                let si = self.eid(s);
                format!("p {} {} {}", ni, i, si)
            }
        };
        let id = self.exprs.len();
        self.exprs.insert(ExprKey(expr::dup(e)), id);
        self.emit(&format!("E {} {}", id, body));
    }

    /// Emit an expression DAG, returning the root's id.  `Pins.lean`'s
    /// `wExprGo`: `(e, false)` means "visit", `(e, true)` means "children done,
    /// emit".
    fn w_expr(&mut self, root: &Expr) -> usize {
        let mut stack: Vec<(Expr, bool)> = vec![(expr::dup(root), false)];
        while let Some((e, done)) = stack.pop() {
            if self.exprs.contains_key(&ExprKey(expr::dup(&e))) {
                continue;
            }
            if done {
                self.emit_expr_node(&e);
                continue;
            }
            let mut kids: Vec<Expr> = Vec::new();
            match expr::view(&e) {
                ExprView::Bvar(_)
                | ExprView::Sort(_)
                | ExprView::Const(_, _)
                | ExprView::Lit(_) => {}
                ExprView::Fvar(_, ty) => kids.push(expr::dup(ty)),
                ExprView::App(f, a) => {
                    kids.push(expr::dup(f));
                    kids.push(expr::dup(a));
                }
                ExprView::Lam(ty, b, _) | ExprView::ForallE(ty, b, _) => {
                    kids.push(expr::dup(ty));
                    kids.push(expr::dup(b));
                }
                ExprView::LetE(ty, v, b) => {
                    kids.push(expr::dup(ty));
                    kids.push(expr::dup(v));
                    kids.push(expr::dup(b));
                }
                ExprView::Proj(_, _, s) => kids.push(expr::dup(s)),
            }
            stack.push((e, true));
            for k in kids {
                stack.push((k, false));
            }
        }
        self.eid(root)
    }

    // --- the records above expressions ------------------------------------

    /// An `S` record (FORMAT.md §4) has no id: the record *is* the payload.
    /// The eight
    /// pins are emitted first and the eight proof lists after, in the field
    /// order of `NatOpPinSet`, which is what `Pins.lean`'s `wPinSet` does.
    fn w_pin_set(&mut self, s: &NatOpPinSet) {
        let dv = self.w_expr(&s.div_pin);
        let md = self.w_expr(&s.mod_pin);
        let gc = self.w_expr(&s.gcd_pin);
        let la = self.w_expr(&s.land_pin);
        let lo = self.w_expr(&s.lor_pin);
        let xo = self.w_expr(&s.xor_pin);
        let sl = self.w_expr(&s.shift_left_pin);
        let sr = self.w_expr(&s.shift_right_pin);
        let dvp = self.w_expr_list(&s.div_proofs);
        let mdp = self.w_expr_list(&s.mod_proofs);
        let gcp = self.w_expr_list(&s.gcd_proofs);
        let lap = self.w_expr_list(&s.land_proofs);
        let lop = self.w_expr_list(&s.lor_proofs);
        let xop = self.w_expr_list(&s.xor_proofs);
        let slp = self.w_expr_list(&s.shift_left_proofs);
        let srp = self.w_expr_list(&s.shift_right_proofs);
        let line = format!(
            "S {} {} {} {} {} {} {} {} {} {} {} {} {} {} {} {} {}",
            str_field(&s.toolchain),
            dv,
            md,
            gc,
            la,
            lo,
            xo,
            sl,
            sr,
            id_list(&dvp),
            id_list(&mdp),
            id_list(&gcp),
            id_list(&lap),
            id_list(&lop),
            id_list(&xop),
            id_list(&slp),
            id_list(&srp)
        );
        self.emit(&line);
        self.n_s += 1;
    }

    /// The ids of a counted `Expr` list, emitted left to right (`mapM wExpr`).
    fn w_expr_list(&mut self, es: &[Expr]) -> Vec<usize> {
        let mut out: Vec<usize> = Vec::new();
        for e in es {
            out.push(self.w_expr(e));
        }
        out
    }
}

// ---------------------------------------------------------------------------
// The entry point
// ---------------------------------------------------------------------------

/// **The writer** (FORMAT.md).  `dump_pins(&parse_pins(text)?)` is
/// `text`, byte for byte, for the `con-ron-pins/1` dump `lake exe
/// con-ron-dump-pins` produces — which is how the tests exercise the pin
/// reader without the Lean side, and how they check the core's embedded
/// `PINS_TEXT` against both.
pub fn dump_pins(ss: &[NatOpPinSet]) -> String {
    let mut w = Writer::new();
    w.emit(PINS_HEADER);
    for s in ss {
        w.w_pin_set(s);
    }
    let n = w.n_s;
    w.emit(&format!("end {}", n));
    w.buf
}
