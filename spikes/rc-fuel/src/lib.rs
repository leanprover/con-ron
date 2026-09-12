//! Spike: the Rust style intended for the con-ron port, pushed through Charon/Aeneas.
use std::rc::Rc;

#[derive(Clone)]
pub enum Expr {
    BVar(u64),
    App(Rc<Node>, Rc<Node>),
    Lam(Rc<Node>),
}

/// A node carries a precomputed data word (hash | bounds), like con-leche's `Expr.data`.

pub struct Node {
    pub data: u64,
    pub expr: Expr,
}

pub fn mix_hash(a: u64, b: u64) -> u64 {
    a.wrapping_mul(0x9E3779B97F4A7C15).wrapping_add(b).rotate_left(17)
}

pub fn mk_bvar(i: u64) -> Rc<Node> {
    Rc::new(Node { data: mix_hash(3, i), expr: Expr::BVar(i) })
}
pub fn mk_app(f: Rc<Node>, a: Rc<Node>) -> Rc<Node> {
    let d = mix_hash(17, mix_hash(f.data, a.data));
    Rc::new(Node { data: d, expr: Expr::App(f, a) })
}
pub fn mk_lam(b: Rc<Node>) -> Rc<Node> {
    let d = mix_hash(19, b.data);
    Rc::new(Node { data: d, expr: Expr::Lam(b) })
}

/// Structural equality with a pointer fast path (modeled as `false` in Lean).
pub fn ptr_eq(a: &Rc<Node>, b: &Rc<Node>) -> bool {
    Rc::ptr_eq(a, b)
}

pub fn beq(a: &Rc<Node>, b: &Rc<Node>) -> bool {
    if ptr_eq(a, b) {
        return true;
    }
    if a.data != b.data {
        return false;
    }
    match (&a.expr, &b.expr) {
        (Expr::BVar(i), Expr::BVar(j)) => i == j,
        (Expr::App(f1, a1), Expr::App(f2, a2)) => beq(f1, f2) && beq(a1, a2),
        (Expr::Lam(b1), Expr::Lam(b2)) => beq(b1, b2),
        _ => false,
    }
}

/// A tiny association-list "hash map" standing in for the real one.
pub struct Memo {
    pub entries: Vec<(Rc<Node>, u64)>,
    pub hits: u64,
}

pub fn memo_find(m: &Memo, k: &Rc<Node>) -> Option<u64> {
    let mut i: usize = 0;
    while i < m.entries.len() {
        if beq(&m.entries[i].0, k) {
            return Some(m.entries[i].1);
        }
        i += 1;
    }
    None
}

#[derive(Clone, Copy, PartialEq, Eq)]
pub enum CheckError {
    FuelExhausted,
    Overflow,
}

/// Size of a term with fuel-indexed recursion and a memo threaded as `&mut` state.
pub fn size(fuel: u64, st: &mut Memo, e: &Rc<Node>) -> Result<u64, CheckError> {
    if fuel == 0 {
        return Err(CheckError::FuelExhausted);
    }
    if let Some(v) = memo_find(st, e) {
        st.hits += 1;
        return Ok(v);
    }
    let r = size_core(fuel - 1, st, e)?;
    st.entries.push((e.clone(), r));
    Ok(r)
}

pub fn size_core(fuel: u64, st: &mut Memo, e: &Rc<Node>) -> Result<u64, CheckError> {
    match &e.expr {
        Expr::BVar(_) => Ok(1),
        Expr::App(f, a) => {
            let x = size(fuel, st, f)?;
            let y = size(fuel, st, a)?;
            match x.checked_add(y) {
                None => Err(CheckError::Overflow),
                Some(s) => match s.checked_add(1) {
                    None => Err(CheckError::Overflow),
                    Some(t) => Ok(t),
                },
            }
        }
        Expr::Lam(b) => {
            let x = size(fuel, st, b)?;
            match x.checked_add(1) {
                None => Err(CheckError::Overflow),
                Some(t) => Ok(t),
            }
        }
    }
}
