//! The DAG census — the check that the reader really did hand back a DAG.
//!
//! FORMAT.md §2 exists because con-leche's terms are shared heavily and writing
//! the tree out would blow up exponentially; the reader's job (FORMAT.md §6.1)
//! is to put that sharing back.  A byte-identical re-dump does *not* prove it:
//! `write.rs` interns by value, so it would collapse a tree expansion back into
//! the same bytes.  What proves it is counting **distinct heap nodes** reachable
//! from the parsed declarations and finding exactly as many as the file has
//! records — one `N`, `L` or `E` record, one allocation, every later reference a
//! cloned `Rc` handle.
//!
//! The walk therefore compares pointers, via `Rc::as_ptr`.  Raw pointers are
//! only ever hashed and compared here, never dereferenced, so there is no
//! `unsafe` — and none is allowed in this crate (see the crate docs).
//!
//! The `Expr` walk is a worklist for the same reason `Write.lean`'s is: term
//! depth reaches the thousands.  `Name` and `Level` are shallow and recur.

use std::collections::HashSet;
use std::rc::Rc;

use con_ron_core::cached::parsed_c::DeclC;
use con_ron_core::kernel::env::ConstantInfo;
use con_ron_core::kernel::env::ConstantVal;
use con_ron_core::kernel::env::IndCaps;
use con_ron_core::kernel::env::ProjTable;
use con_ron_core::kernel::env::RecRule;
use con_ron_core::kernel::env::RecRuleFire;
use con_ron_core::kernel::expr;
use con_ron_core::kernel::expr::Expr;
use con_ron_core::kernel::expr::ExprKind;
use con_ron_core::kernel::expr::ExprNode;
use con_ron_core::kernel::level::Level;
use con_ron_core::kernel::level::LevelKind;
use con_ron_core::kernel::level::LevelNode;
use con_ron_core::kernel::name::Name;
use con_ron_core::kernel::name::NameKind;
use con_ron_core::kernel::name::NameNode;
use con_ron_core::kernel::prop_when;
use con_ron_core::kernel::prop_when::PropWhen;

/// How many *distinct* heap nodes a declaration list reaches.
#[derive(Debug, Default, Clone, Copy, PartialEq, Eq)]
pub struct Census {
    pub names: usize,
    pub levels: usize,
    pub exprs: usize,
}

#[derive(Default)]
struct Walk {
    names: HashSet<*const NameNode>,
    levels: HashSet<*const LevelNode>,
    exprs: HashSet<*const ExprNode>,
}

impl Walk {
    fn name(&mut self, x: &Name) {
        if !self.names.insert(Rc::as_ptr(&x.0)) {
            return;
        }
        match &x.0.kind {
            NameKind::Anonymous => {}
            NameKind::Str(p, _) => self.name(p),
            NameKind::Num(p, _) => self.name(p),
        }
    }

    fn names_of(&mut self, xs: &[Name]) {
        for x in xs {
            self.name(x);
        }
    }

    fn level(&mut self, u: &Level) {
        if !self.levels.insert(Rc::as_ptr(&u.0)) {
            return;
        }
        match &u.0.kind {
            LevelKind::Zero => {}
            LevelKind::Succ(a) => self.level(a),
            LevelKind::Max(a, b) | LevelKind::Imax(a, b) => {
                self.level(a);
                self.level(b);
            }
            LevelKind::Param(n) => self.name(n),
        }
    }

    fn levels_of(&mut self, us: &[Level]) {
        for u in us {
            self.level(u);
        }
    }

    /// The datum is not an `Rc` node; only the names in it are.
    fn pw(&mut self, pw: &PropWhen) {
        for p in prop_when::to_list(pw) {
            self.name(&p);
        }
    }

    fn expr(&mut self, root: &Expr) {
        let mut stack: Vec<Expr> = vec![expr::dup(root)];
        while let Some(e) = stack.pop() {
            if !self.exprs.insert(Rc::as_ptr(&e.0)) {
                continue;
            }
            match &e.0.kind {
                ExprKind::Bvar(_) | ExprKind::Lit(_) => {}
                ExprKind::Fvar(_, ty) => stack.push(expr::dup(ty)),
                ExprKind::Sort(u) => self.level(u),
                ExprKind::Const(n, us) => {
                    self.name(n);
                    self.levels_of(us);
                }
                ExprKind::App(f, a) => {
                    stack.push(expr::dup(f));
                    stack.push(expr::dup(a));
                }
                ExprKind::Lam(ty, b, m) | ExprKind::ForallE(ty, b, m) => {
                    stack.push(expr::dup(ty));
                    stack.push(expr::dup(b));
                    self.pw(&m.pw);
                }
                ExprKind::LetE(ty, v, b) => {
                    stack.push(expr::dup(ty));
                    stack.push(expr::dup(v));
                    stack.push(expr::dup(b));
                }
                ExprKind::Proj(n, _, s) => {
                    self.name(n);
                    stack.push(expr::dup(s));
                }
            }
        }
    }

    fn exprs_of(&mut self, es: &[Expr]) {
        for e in es {
            self.expr(e);
        }
    }

    fn cv(&mut self, cv: &ConstantVal) {
        self.name(&cv.name);
        self.names_of(&cv.level_params);
        self.expr(&cv.ty);
    }

    fn rule(&mut self, r: &RecRule) {
        self.name(&r.ctor);
        match &r.fire {
            RecRuleFire::Inert | RecRuleFire::Plain => {}
            RecRuleFire::Nested(lvls, pins) => {
                self.levels_of(lvls);
                self.exprs_of(pins);
            }
        }
        self.expr(&r.rhs);
    }

    fn caps(&mut self, c: &IndCaps) {
        self.name(&c.eta_ctor);
        self.pw(&c.sort_z);
    }

    fn table(&mut self, t: &ProjTable) {
        self.name(&t.struct_name);
        self.names_of(&t.level_params);
        self.name(&t.ctor);
        self.level(&t.struct_sort);
        self.exprs_of(&t.bodies);
        self.levels_of(&t.guards);
    }

    fn info(&mut self, ci: &ConstantInfo) {
        match ci {
            ConstantInfo::AxiomInfo(v) => self.cv(v),
            ConstantInfo::DefnInfo(v, val, _) => {
                self.cv(v);
                self.expr(val);
            }
            ConstantInfo::ThmInfo(v, val) => {
                self.cv(v);
                self.expr(val);
            }
            ConstantInfo::IndInfo(v, c) => {
                self.cv(v);
                self.caps(c);
            }
            ConstantInfo::CtorInfo(v, _, _) => self.cv(v),
            ConstantInfo::RecInfo(v, _, _, rules) => {
                self.cv(v);
                for r in rules {
                    self.rule(r);
                }
            }
            ConstantInfo::ProjInfo(t) => self.table(t),
        }
    }

    fn decl(&mut self, d: &DeclC) {
        match d {
            DeclC::AxiomDecl(v) => self.cv(v),
            DeclC::DefnDecl(v, val, _) => {
                self.cv(v);
                self.expr(val);
            }
            DeclC::ThmDecl(v, val) | DeclC::OpaqueDecl(v, val) => {
                self.cv(v);
                self.expr(val);
            }
            DeclC::BasisDecl(_) => {}
            DeclC::IndDecl(block, _) => {
                for ci in block {
                    self.info(ci);
                }
            }
        }
    }
}

/// Count the distinct `Name`, `Level` and `Expr` heap nodes the list reaches.
/// For a list that came out of [`crate::parse_decls`] this equals the dump's
/// `N`, `L` and `E` record counts exactly: the reader allocated one node per
/// record and shared it everywhere else.
pub fn census(ds: &[DeclC]) -> Census {
    let mut w = Walk::default();
    for d in ds {
        w.decl(d);
    }
    Census {
        names: w.names.len(),
        levels: w.levels.len(),
        exprs: w.exprs.len(),
    }
}
