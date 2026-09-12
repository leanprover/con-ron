//! `ConLeche/Kernel/Basis/Builder.lean` — the tiny builder the *raw* pins are
//! written with.
//!
//! Every helper here is, in con-leche's own words, "a `def` whose body is a
//! single `Expr` constructor application": `pi`/`piI`/`piA` are
//! `.forallE ty body ⟨.never⟩`, `lm`/`lmI` are `.lam ty body ⟨.never⟩`,
//! `ap2`…`ap4` are nested `.app`s.  They exist so a reader can line a pinned
//! declaration up against `Init.Prelude` binder by binder.
//!
//! **Two standing deviations.**
//!
//! 1. **The binder-name argument is gone.**  `pi "a" ty body` takes the
//!    `Init.Prelude` spelling purely for the reader — `Expr` carries neither
//!    a binder name nor a binder info (con-leche task #205) and the argument
//!    is `_x`, unused.  A `&str` parameter would also be the one shape task
//!    #14 measured Aeneas failing on, so the port drops it.  With the name
//!    gone `pi`, `piI` and `piA` are the *same function*, and so are `lm`
//!    and `lmI`; each Rust function therefore carries every citation it
//!    stands for (task #18's pattern).
//! 2. **`rule` is `env::rec_rule_parsed`.**  The builder's raw iota rule at
//!    the parse placeholders is exactly the constructor task #14 wrote for
//!    `RecRule`'s field defaults, so it gained a citation there rather than a
//!    duplicate here.

use crate::kernel::core_types;
use crate::kernel::expr;
use crate::kernel::expr::{BinderMeta, Expr};
use crate::kernel::level;
use crate::kernel::level::Level;
use crate::kernel::name;
use crate::kernel::name::Name;
use crate::kernel::prop_when;
use std::vec::Vec;

/// con-leche: ConLeche/Kernel/Basis/Builder.lean:41-42 BasisDSL.bn
/// A top-level (single-component) name: `bn "Eq"` is `Eq`.  Deviation: the
/// argument is the code-point spelling of the string (DESIGN.md §3.3).
pub fn bn(s: Vec<u32>) -> Name {
    name::mk_str(name::anonymous(), s)
}

/// con-leche: ConLeche/Kernel/Basis/Builder.lean:44-45 BasisDSL.uN
/// The universe parameter `u` — every basis block's first one.
pub fn u_n() -> Name {
    bn({ const S: [u32; 1] = [117]; core_types::code_points(&S) })
}

/// con-leche: ConLeche/Kernel/Basis/Builder.lean:47-48 BasisDSL.u
/// The universe parameter `u`, as a level.
pub fn u() -> Level {
    level::param(u_n())
}

/// con-leche: ConLeche/Kernel/Basis/Builder.lean:50-51 BasisDSL.vN
/// The universe parameter `v` (`Quot.lift`'s target sort).
pub fn v_n() -> Name {
    bn({ const S: [u32; 1] = [118]; core_types::code_points(&S) })
}

/// con-leche: ConLeche/Kernel/Basis/Builder.lean:53-54 BasisDSL.v
/// The universe parameter `v`, as a level.
pub fn v() -> Level {
    level::param(v_n())
}

/// con-leche: ConLeche/Kernel/Basis/Builder.lean:56-58 BasisDSL.u1N
/// The universe parameter `u_1` — the motive sort the exporter names for a
/// recursor whose type former already spends `u`.
pub fn u1_n() -> Name {
    bn({ const S: [u32; 3] = [117, 95, 49]; core_types::code_points(&S) })
}

/// con-leche: ConLeche/Kernel/Basis/Builder.lean:60-61 BasisDSL.u1
/// The universe parameter `u_1`, as a level.
pub fn u1() -> Level {
    level::param(u1_n())
}

/// con-leche: ConLeche/Kernel/Basis/Builder.lean:63-64 BasisDSL.bv
/// A bound variable, by de Bruijn index.
pub fn bv(i: u64) -> Expr {
    expr::bvar(i)
}

/// con-leche: ConLeche/Kernel/Basis/Builder.lean:66-67 BasisDSL.srt
/// `Sort u`.
pub fn srt(u: Level) -> Expr {
    expr::sort(u)
}

/// con-leche: ConLeche/Kernel/Basis/Builder.lean:69-70 BasisDSL.prop
/// `Prop` = `Sort 0`.
pub fn prop() -> Expr {
    expr::sort(level::zero())
}

/// con-leche: ConLeche/Kernel/Basis/Builder.lean:72-73 BasisDSL.type1
/// `Type` = `Sort 1`.
pub fn type1() -> Expr {
    expr::sort(level::succ(level::zero()))
}

/// con-leche: ConLeche/Kernel/Basis/Builder.lean:75-76 BasisDSL.cnst
/// A constant, at the given universe arguments.  Deviation: Lean's `us`
/// default `[]` is spelled at every call site (Rust has no default argument).
pub fn cnst(n: Name, us: Vec<Level>) -> Expr {
    expr::mk_const(n, us)
}

/// con-leche: none — the `⟨.never⟩` binder datum every raw-pin binder carries
/// The parse placeholder: "nothing is known about this codomain's
/// prop-ness".  Lean writes it inline as an anonymous-constructor literal in
/// `pi`/`piI`/`piA`/`lm`/`lmI`.
pub fn never_meta() -> BinderMeta {
    expr::binder_meta(prop_when::never())
}

/// con-leche: ConLeche/Kernel/Basis/Builder.lean:85-88 BasisDSL.pi
/// con-leche: ConLeche/Kernel/Basis/Builder.lean:90-93 BasisDSL.piI
/// con-leche: ConLeche/Kernel/Basis/Builder.lean:95-97 BasisDSL.piA
/// `∀ (x : ty), body` at the *raw* binder annotation (`pw` at the parse
/// placeholder `.never`).  The three cited helpers build the same node and
/// differ only in the binder name they document, which `Expr` does not carry
/// — see the module note.
pub fn pi(ty: Expr, body: Expr) -> Expr {
    expr::forall_e(ty, body, never_meta())
}

/// con-leche: ConLeche/Kernel/Basis/Builder.lean:99-101 BasisDSL.lm
/// con-leche: ConLeche/Kernel/Basis/Builder.lean:103-106 BasisDSL.lmI
/// `fun (x : ty) => body` at the raw binder annotation (see `pi`).
pub fn lm(ty: Expr, body: Expr) -> Expr {
    expr::lam(ty, body, never_meta())
}

/// con-leche: ConLeche/Kernel/Basis/Builder.lean:108-109 BasisDSL.ap2
/// Binary application.
pub fn ap2(f: Expr, a: Expr, b: Expr) -> Expr {
    expr::app(expr::app(f, a), b)
}

/// con-leche: ConLeche/Kernel/Basis/Builder.lean:111-112 BasisDSL.ap3
/// Ternary application.
pub fn ap3(f: Expr, a: Expr, b: Expr, c: Expr) -> Expr {
    expr::app(ap2(f, a, b), c)
}

/// con-leche: ConLeche/Kernel/Basis/Builder.lean:114-115 BasisDSL.ap4
/// Quaternary application.
pub fn ap4(f: Expr, a: Expr, b: Expr, c: Expr, d: Expr) -> Expr {
    expr::app(ap3(f, a, b, c), d)
}
