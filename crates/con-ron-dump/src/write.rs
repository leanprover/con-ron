//! The Rust writer for `con-ron-decls/1` — a transliteration of
//! `proof/ConRon/Dump/Write.lean`, emission order included.
//!
//! It exists to make the reader testable without the Lean side: `dump_decls`
//! is a left inverse of [`crate::parse_decls`] *on the nose*, so
//! `con-ron-dump-check --roundtrip` can diff a re-dump against the input file
//! byte for byte and a single wrong field anywhere shows up as a diff.  That
//! is a much sharper test than "it parsed": every id, every list length, every
//! escape and the whole emission order have to agree with Lean's writer.
//!
//! Byte-identity needs three things to match `Write.lean` exactly:
//!
//! 1. **The interning tables.**  `N`, `L`, `W` and `E` are keyed by *value*
//!    (the core's own `beq` and cached hash, via the key wrappers below), as
//!    Lean's `Std.HashMap Expr Nat` is; `V`, `R`, `C`, `P` and `I` are merely
//!    counted.
//! 2. **The `Expr` worklist.**  `Write.lean` pushes `(e, false)`, pops from
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

use con_ron_core::cached::parsed_c::DeclC;
use con_ron_core::kernel::env::BasisKind;
use con_ron_core::kernel::env::ConstantInfo;
use con_ron_core::kernel::env::ConstantVal;
use con_ron_core::kernel::env::IndCaps;
use con_ron_core::kernel::env::ProjTable;
use con_ron_core::kernel::env::RecRule;
use con_ron_core::kernel::env::RecRuleFire;
use con_ron_core::kernel::env::ReducibilityHint;
use con_ron_core::kernel::expr;
use con_ron_core::kernel::expr::Expr;
use con_ron_core::kernel::expr::ExprKind;
use con_ron_core::kernel::expr::Literal;
use con_ron_core::kernel::level;
use con_ron_core::kernel::level::Level;
use con_ron_core::kernel::level::LevelKind;
use con_ron_core::kernel::name;
use con_ron_core::kernel::name::Name;
use con_ron_core::kernel::name::NameKind;
use con_ron_core::kernel::prop_when;
use con_ron_core::kernel::prop_when::PropWhen;

use crate::natdec;
use crate::HEADER;

// ---------------------------------------------------------------------------
// Scalars
// ---------------------------------------------------------------------------

/// `false`/`true` as `0`/`1`.
fn bool_str(b: bool) -> &'static str {
    if b {
        "1"
    } else {
        "0"
    }
}

/// One code point, escaped: a literal printable non-backslash ASCII byte, or
/// `\<lowercase-hex>;`.  `Write.lean`'s `escChar` and `escapeString`.
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

fn hint_str(h: &ReducibilityHint) -> String {
    match h {
        ReducibilityHint::Opaque => "o".to_string(),
        ReducibilityHint::Abbrev => "b".to_string(),
        ReducibilityHint::Regular(n) => format!("r {}", n),
    }
}

fn basis_str(k: &BasisKind) -> &'static str {
    match k {
        BasisKind::EqK => "eq",
        BasisKind::NatK => "nat",
        BasisKind::PunitK => "punit",
        BasisKind::EmptyK => "empty",
        BasisKind::FalseK => "false",
        BasisKind::QuotK => "quot",
    }
}

// ---------------------------------------------------------------------------
// Interning keys
// ---------------------------------------------------------------------------
//
// The core deliberately does not implement `PartialEq`/`Hash`: its equality is
// `beq` (pointer, then cached hash, then structure) and its hash is the stored
// computed field, both as one-method traits of its own (task #7).  These
// wrappers hand those to `std::collections::HashMap`, so the writer interns by
// the same notion of equality `Write.lean`'s `Std.HashMap` uses.

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

/// `Write.lean`'s `WState`: the output, one interning table per interned id
/// space and one counter per numbered one.
struct Writer {
    buf: String,
    names: HashMap<NameKey, usize>,
    levels: HashMap<LevelKey, usize>,
    pws: HashMap<PwKey, usize>,
    exprs: HashMap<ExprKey, usize>,
    n_v: usize,
    n_r: usize,
    n_c: usize,
    n_p: usize,
    n_i: usize,
    n_d: usize,
}

impl Writer {
    fn new() -> Writer {
        Writer {
            buf: String::new(),
            names: HashMap::new(),
            levels: HashMap::new(),
            pws: HashMap::new(),
            exprs: HashMap::new(),
            n_v: 0,
            n_r: 0,
            n_c: 0,
            n_p: 0,
            n_i: 0,
            n_d: 0,
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

    /// The id of an already-emitted node (`Write.lean`'s `eid`, `getD e 0`).
    fn eid(&self, e: &Expr) -> usize {
        match self.exprs.get(&ExprKey(expr::dup(e))) {
            Some(&i) => i,
            None => 0,
        }
    }

    /// Emit one node, all of whose `Expr` children are already emitted.
    fn emit_expr_node(&mut self, e: &Expr) {
        let body = match &e.0.kind {
            ExprKind::Bvar(i) => format!("b {}", i),
            ExprKind::Fvar(idx, ty) => format!("v {} {}", idx, self.eid(ty)),
            ExprKind::Sort(u) => {
                let l = self.w_level(u);
                format!("s {}", l)
            }
            ExprKind::Const(n, us) => {
                let ni = self.w_name(n);
                let ls: Vec<usize> = us.iter().map(|u| self.w_level(u)).collect();
                format!("c {} {}", ni, id_list(&ls))
            }
            ExprKind::App(f, a) => format!("a {} {}", self.eid(f), self.eid(a)),
            ExprKind::Lam(ty, b, m) => {
                let t = self.eid(ty);
                let bi = self.eid(b);
                let p = self.w_pw(&m.pw);
                format!("l {} {} {}", t, bi, p)
            }
            ExprKind::ForallE(ty, b, m) => {
                let t = self.eid(ty);
                let bi = self.eid(b);
                let p = self.w_pw(&m.pw);
                format!("f {} {} {}", t, bi, p)
            }
            ExprKind::LetE(ty, v, b) => {
                format!("t {} {} {}", self.eid(ty), self.eid(v), self.eid(b))
            }
            ExprKind::Lit(Literal::NatVal(n)) => format!("n {}", natdec::to_decimal(n)),
            ExprKind::Lit(Literal::StrVal(s)) => format!("g {}", str_field(s)),
            ExprKind::Proj(sn, i, s) => {
                let ni = self.w_name(sn);
                let si = self.eid(s);
                format!("p {} {} {}", ni, i, si)
            }
        };
        let id = self.exprs.len();
        self.exprs.insert(ExprKey(expr::dup(e)), id);
        self.emit(&format!("E {} {}", id, body));
    }

    /// Emit an expression DAG, returning the root's id.  `Write.lean`'s
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
            match &e.0.kind {
                ExprKind::Bvar(_)
                | ExprKind::Sort(_)
                | ExprKind::Const(_, _)
                | ExprKind::Lit(_) => {}
                ExprKind::Fvar(_, ty) => kids.push(expr::dup(ty)),
                ExprKind::App(f, a) => {
                    kids.push(expr::dup(f));
                    kids.push(expr::dup(a));
                }
                ExprKind::Lam(ty, b, _) | ExprKind::ForallE(ty, b, _) => {
                    kids.push(expr::dup(ty));
                    kids.push(expr::dup(b));
                }
                ExprKind::LetE(ty, v, b) => {
                    kids.push(expr::dup(ty));
                    kids.push(expr::dup(v));
                    kids.push(expr::dup(b));
                }
                ExprKind::Proj(_, _, s) => kids.push(expr::dup(s)),
            }
            stack.push((e, true));
            for k in kids {
                stack.push((k, false));
            }
        }
        self.eid(root)
    }

    // --- the records above expressions ------------------------------------

    fn w_cv(&mut self, cv: &ConstantVal) -> usize {
        let ni = self.w_name(&cv.name);
        let lps: Vec<usize> = cv.level_params.iter().map(|n| self.w_name(n)).collect();
        let ti = self.w_expr(&cv.ty);
        let id = self.n_v;
        self.n_v += 1;
        self.emit(&format!("V {} {} {} {}", id, ni, id_list(&lps), ti));
        id
    }

    fn w_rule(&mut self, r: &RecRule) -> usize {
        let ci = self.w_name(&r.ctor);
        let fire = match &r.fire {
            RecRuleFire::Inert => "i".to_string(),
            RecRuleFire::Plain => "p".to_string(),
            RecRuleFire::Nested(lvls, pins) => {
                let ls: Vec<usize> = lvls.iter().map(|u| self.w_level(u)).collect();
                let ps: Vec<usize> = pins.iter().map(|e| self.w_expr(e)).collect();
                format!("n {} {}", id_list(&ls), id_list(&ps))
            }
        };
        let rhs = self.w_expr(&r.rhs);
        let id = self.n_r;
        self.n_r += 1;
        self.emit(&format!(
            "R {} {} {} {} {} {} {} {} {}",
            id,
            ci,
            r.nfields,
            r.ctor_params,
            fire,
            rhs,
            bool_str(r.k),
            bool_str(r.eta),
            bool_str(r.params_blind)
        ));
        id
    }

    fn w_caps(&mut self, c: &IndCaps) -> usize {
        let ec = self.w_name(&c.eta_ctor);
        let sz = self.w_pw(&c.sort_z);
        let id = self.n_c;
        self.n_c += 1;
        self.emit(&format!(
            "C {} {} {} {} {} {} {} {} {}",
            id,
            bool_str(c.eta),
            ec,
            c.eta_params,
            c.eta_fields,
            bool_str(c.unitlike),
            c.unit_params,
            bool_str(c.rule_k),
            sz
        ));
        id
    }

    fn w_table(&mut self, t: &ProjTable) -> usize {
        let sn = self.w_name(&t.struct_name);
        let lps: Vec<usize> = t.level_params.iter().map(|n| self.w_name(n)).collect();
        let ct = self.w_name(&t.ctor);
        let ss = self.w_level(&t.struct_sort);
        let bs: Vec<usize> = t.bodies.iter().map(|e| self.w_expr(e)).collect();
        let gs: Vec<usize> = t.guards.iter().map(|u| self.w_level(u)).collect();
        let id = self.n_p;
        self.n_p += 1;
        self.emit(&format!(
            "P {} {} {} {} {} {} {} {} {} {}",
            id,
            sn,
            id_list(&lps),
            t.num_params,
            ct,
            t.num_fields,
            ss,
            id_list(&bs),
            id_list(&gs),
            t.off
        ));
        id
    }

    fn w_info(&mut self, ci: &ConstantInfo) -> usize {
        let body = match ci {
            ConstantInfo::AxiomInfo(v) => {
                let i = self.w_cv(v);
                format!("a {}", i)
            }
            ConstantInfo::DefnInfo(v, val, h) => {
                let i = self.w_cv(v);
                let e = self.w_expr(val);
                format!("d {} {} {}", i, e, hint_str(h))
            }
            ConstantInfo::ThmInfo(v, val) => {
                let i = self.w_cv(v);
                let e = self.w_expr(val);
                format!("t {} {}", i, e)
            }
            ConstantInfo::IndInfo(v, caps) => {
                let i = self.w_cv(v);
                let c = self.w_caps(caps);
                format!("i {} {}", i, c)
            }
            ConstantInfo::CtorInfo(v, np, nf) => {
                let i = self.w_cv(v);
                format!("c {} {} {}", i, np, nf)
            }
            ConstantInfo::RecInfo(v, mi, rp, rules) => {
                let i = self.w_cv(v);
                let rs: Vec<usize> = rules.iter().map(|r| self.w_rule(r)).collect();
                format!("r {} {} {} {}", i, mi, rp, id_list(&rs))
            }
            ConstantInfo::ProjInfo(t) => {
                let ti = self.w_table(t);
                format!("p {}", ti)
            }
        };
        let id = self.n_i;
        self.n_i += 1;
        self.emit(&format!("I {} {}", id, body));
        id
    }

    /// A `D` record has no id: the order is the payload.
    fn w_decl(&mut self, d: &DeclC) {
        let body = match d {
            DeclC::AxiomDecl(v) => {
                let i = self.w_cv(v);
                format!("a {}", i)
            }
            DeclC::DefnDecl(v, val, h) => {
                let i = self.w_cv(v);
                let e = self.w_expr(val);
                format!("d {} {} {}", i, e, hint_str(h))
            }
            DeclC::ThmDecl(v, val) => {
                let i = self.w_cv(v);
                let e = self.w_expr(val);
                format!("t {} {}", i, e)
            }
            DeclC::OpaqueDecl(v, val) => {
                let i = self.w_cv(v);
                let e = self.w_expr(val);
                format!("o {} {}", i, e)
            }
            DeclC::BasisDecl(k) => format!("b {}", basis_str(k)),
            DeclC::IndDecl(block, np) => {
                let is: Vec<usize> = block.iter().map(|ci| self.w_info(ci)).collect();
                format!("i {} {}", np, id_list(&is))
            }
        };
        self.emit(&format!("D {}", body));
        self.n_d += 1;
    }
}

// ---------------------------------------------------------------------------
// The entry point
// ---------------------------------------------------------------------------

/// **The writer.**  `dump_decls(&parse_decls(text)?)` is `text`, byte for
/// byte, for every `con-ron-decls/1` dump the Lean writer produces.
pub fn dump_decls(ds: &[DeclC]) -> String {
    let mut w = Writer::new();
    w.emit(HEADER);
    for d in ds {
        w.w_decl(d);
    }
    let n = w.n_d;
    w.emit(&format!("end {}", n));
    w.buf
}
