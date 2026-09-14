//! The DAG census — the check that the reader really did hand back a DAG.
//!
//! FORMAT.md §2 exists because con-leche's terms are shared heavily and writing
//! the tree out would blow up exponentially — as a tree one pin variant is
//! 5.1 M nodes — and the reader's job (FORMAT.md §6.1) is to put that sharing
//! back.  A byte-identical re-dump does *not* prove it: `write.rs` interns by
//! value, so it would collapse a tree expansion back into the same bytes.
//! What proves it is counting **distinct heap nodes** reachable from the
//! parsed pin variants and finding exactly as many as the file has records —
//! one `N`, `L` or `E` record, one allocation, every later reference a cloned
//! `Rc` handle.
//!
//! The walk therefore compares pointers, taken through `Deref` (so they
//! follow `ron::ptr`'s alias, task #44).  Raw pointers are
//! only ever hashed and compared here, never dereferenced, so there is no
//! `unsafe` — and none is allowed in this crate (see the crate docs).
//!
//! The `Expr` walk is a worklist for the same reason the Lean writer's is:
//! term depth reaches the thousands.  `Name` and `Level` are shallow and
//! recur.

use std::collections::HashSet;

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
use con_ron_core::kernel::nat_op_pins::NatOpPinSet;
use con_ron_core::kernel::prop_when;
use con_ron_core::kernel::prop_when::PropWhen;

/// How many *distinct* heap nodes a pin list reaches.
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
        if !self.names.insert(&*x.0 as *const NameNode) {
            return;
        }
        match &x.0.kind {
            NameKind::Anonymous => {}
            NameKind::Str(p, _) => self.name(p),
            NameKind::Num(p, _) => self.name(p),
        }
    }

    fn level(&mut self, u: &Level) {
        if !self.levels.insert(&*u.0 as *const LevelNode) {
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
            if !self.exprs.insert(&*e.0 as *const ExprNode) {
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

}

/// The census of a `con-ron-pins/1` payload (FORMAT.md §4).  A pin
/// variant is where the sharing matters most: as a *tree* the v4.33.0 variant
/// is 5.1 M nodes against 20 183 in the DAG (DESIGN.md task #22), so a reader
/// that lost the sharing would be found here and nowhere else.
pub fn census_pins(ss: &[NatOpPinSet]) -> Census {
    let mut w = Walk::default();
    for s in ss {
        w.expr(&s.div_pin);
        w.expr(&s.mod_pin);
        w.expr(&s.gcd_pin);
        w.expr(&s.land_pin);
        w.expr(&s.lor_pin);
        w.expr(&s.xor_pin);
        w.expr(&s.shift_left_pin);
        w.expr(&s.shift_right_pin);
        w.exprs_of(&s.div_proofs);
        w.exprs_of(&s.mod_proofs);
        w.exprs_of(&s.gcd_proofs);
        w.exprs_of(&s.land_proofs);
        w.exprs_of(&s.lor_proofs);
        w.exprs_of(&s.xor_proofs);
        w.exprs_of(&s.shift_left_proofs);
        w.exprs_of(&s.shift_right_proofs);
    }
    Census {
        names: w.names.len(),
        levels: w.levels.len(),
        exprs: w.exprs.len(),
    }
}
