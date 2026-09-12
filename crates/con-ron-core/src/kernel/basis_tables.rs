//! The annotated basis blocks, generated (DESIGN.md §5 P1.5, task #22).
//!
//! con-leche: ConLeche/Kernel/BasisA.lean:50-57 BasisKind.declsA
//!
//! **Generated file — do not edit.**  Written by
//! `proof/ConRon/Gen/Main.lean` (`cd proof && lake exe con-ron-gen-tables`)
//! from con-leche's own `BasisKind.declsA`, which con-leche computes while
//! `ConLeche/Kernel/BasisA.lean` elaborates: the `#annotate_basis` command
//! (`ConLeche/Kernel/BasisGen.lean`) runs the checker's annotation pass over
//! the hand-written raw pins (`ConLeche/Kernel/Basis/*.lean`) in install
//! order.  The Rust core has no elaborator, so the *result* is carried as
//! source; `proof/ConRon/Refine/BasisTables.lean` proves that what these
//! functions build abstracts to `ConLeche.BasisKind.declsA`.
//!
//! The module-level citation above covers every item in the file: the whole
//! module is one Lean declaration's value (DESIGN.md §3.7, task #22).
//!
//! Shape: one `let` per distinct interned node (`Name`, `Level`,
//! `PropWhen`, `Expr`), in dependency order, each a call to the port's own
//! smart constructor, each use a `dup` — so the table is the same DAG
//! con-leche's value is, and the generated Lean model is a `do` chain of
//! constructor calls that the refinement lemmas evaluate.

use crate::kernel::env::BasisKind;
use crate::kernel::env::ConstantInfo;
use crate::kernel::env::ConstantVal;
use crate::kernel::env::IndCaps;
use crate::kernel::env::RecRule;
use crate::kernel::env::RecRuleFire;
use crate::kernel::expr;
use crate::kernel::level;
use crate::kernel::level::Level;
use crate::kernel::name;
use crate::kernel::name::Name;
use crate::kernel::prop_when;

/// con-leche: ConLeche/Kernel/BasisA.lean:50-57 BasisKind.declsA
/// con-leche: ConLeche/Kernel/Basis/Eq.lean:22-28 eqRaw
/// con-leche: ConLeche/Kernel/Basis/Eq.lean:30-36 eqReflRaw
/// con-leche: ConLeche/Kernel/Basis/Eq.lean:38-42 eqRecMotive
/// con-leche: ConLeche/Kernel/Basis/Eq.lean:44-61 eqRecRaw
/// con-leche: ConLeche/Kernel/Basis/Eq.lean:63-64 eqBasis
/// The annotated `eq` block (`BasisKind.declsA .eqK` = [eqA, eqReflA, eqRecA]).
///
/// `#annotate_basis` (`ConLeche/Kernel/BasisGen.lean`) computes those 3
/// constants from the 5 raw declarations cited above, while
/// `ConLeche/Kernel/BasisA.lean` elaborates; this function is that value,
/// emitted as source (the module note).
pub fn basis_decls_eq() -> Vec<ConstantInfo> {
    let n0 = name::anonymous();
    let mut s0: Vec<u32> = Vec::new();  // "Eq"
    s0.push(69);
    s0.push(113);
    let n1 = name::mk_str(name::dup(&n0), s0);
    let mut s1: Vec<u32> = Vec::new();  // "u"
    s1.push(117);
    let n2 = name::mk_str(name::dup(&n0), s1);
    let mut ns0: Vec<Name> = Vec::new();
    ns0.push(name::dup(&n2));
    let u0 = level::zero();
    let e0 = expr::sort(level::dup(&u0));
    let e1 = expr::mk_bvar(1);
    let w0 = prop_when::never();
    let e2 = expr::forall_e(expr::dup(&e1), expr::dup(&e0), expr::binder_meta(w0));
    let e3 = expr::mk_bvar(0);
    let w1 = prop_when::never();
    let e4 = expr::forall_e(expr::dup(&e3), expr::dup(&e2), expr::binder_meta(w1));
    let u1 = level::param(name::dup(&n2));
    let e5 = expr::sort(level::dup(&u1));
    let w2 = prop_when::never();
    let e6 = expr::forall_e(expr::dup(&e5), expr::dup(&e4), expr::binder_meta(w2));
    let cv0 = ConstantVal { name: name::dup(&n1), level_params: ns0, ty: expr::dup(&e6) };
    let ns1: Vec<Name> = Vec::new();
    let w3 = prop_when::if_all_zero(ns1);
    let ic0 = IndCaps { eta: false, eta_ctor: name::dup(&n0), eta_params: 0, eta_fields: 0, unitlike: false, unit_params: 0, rule_k: true, sort_z: w3 };
    let ci0 = ConstantInfo::IndInfo(cv0, ic0);
    let mut s2: Vec<u32> = Vec::new();  // "refl"
    s2.push(114);
    s2.push(101);
    s2.push(102);
    s2.push(108);
    let n3 = name::mk_str(name::dup(&n1), s2);
    let mut ns2: Vec<Name> = Vec::new();
    ns2.push(name::dup(&n2));
    let mut us0: Vec<Level> = Vec::new();
    us0.push(level::dup(&u1));
    let e7 = expr::mk_const(name::dup(&n1), us0);
    let e8 = expr::app(expr::dup(&e7), expr::dup(&e1));
    let e9 = expr::app(expr::dup(&e8), expr::dup(&e3));
    let e10 = expr::app(expr::dup(&e9), expr::dup(&e3));
    let ns3: Vec<Name> = Vec::new();
    let w4 = prop_when::if_all_zero(ns3);
    let e11 = expr::forall_e(expr::dup(&e3), expr::dup(&e10), expr::binder_meta(w4));
    let ns4: Vec<Name> = Vec::new();
    let w5 = prop_when::if_all_zero(ns4);
    let e12 = expr::forall_e(expr::dup(&e5), expr::dup(&e11), expr::binder_meta(w5));
    let cv1 = ConstantVal { name: name::dup(&n3), level_params: ns2, ty: expr::dup(&e12) };
    let ci1 = ConstantInfo::CtorInfo(cv1, 2, 0);
    let mut s3: Vec<u32> = Vec::new();  // "rec"
    s3.push(114);
    s3.push(101);
    s3.push(99);
    let n4 = name::mk_str(name::dup(&n1), s3);
    let mut s4: Vec<u32> = Vec::new();  // "u_1"
    s4.push(117);
    s4.push(95);
    s4.push(49);
    let n5 = name::mk_str(name::dup(&n0), s4);
    let mut ns5: Vec<Name> = Vec::new();
    ns5.push(name::dup(&n5));
    ns5.push(name::dup(&n2));
    let e13 = expr::mk_bvar(3);
    let e14 = expr::app(expr::dup(&e13), expr::dup(&e1));
    let e15 = expr::app(expr::dup(&e14), expr::dup(&e3));
    let e16 = expr::mk_bvar(4);
    let e17 = expr::app(expr::dup(&e7), expr::dup(&e16));
    let e18 = expr::app(expr::dup(&e17), expr::dup(&e13));
    let e19 = expr::app(expr::dup(&e18), expr::dup(&e3));
    let mut ns6: Vec<Name> = Vec::new();
    ns6.push(name::dup(&n5));
    let w6 = prop_when::if_all_zero(ns6);
    let e20 = expr::forall_e(expr::dup(&e19), expr::dup(&e15), expr::binder_meta(w6));
    let mut ns7: Vec<Name> = Vec::new();
    ns7.push(name::dup(&n5));
    let w7 = prop_when::if_all_zero(ns7);
    let e21 = expr::forall_e(expr::dup(&e13), expr::dup(&e20), expr::binder_meta(w7));
    let e22 = expr::mk_bvar(2);
    let mut us1: Vec<Level> = Vec::new();
    us1.push(level::dup(&u1));
    let e23 = expr::mk_const(name::dup(&n3), us1);
    let e24 = expr::app(expr::dup(&e23), expr::dup(&e22));
    let e25 = expr::app(expr::dup(&e24), expr::dup(&e1));
    let e26 = expr::app(expr::dup(&e3), expr::dup(&e1));
    let e27 = expr::app(expr::dup(&e26), expr::dup(&e25));
    let mut ns8: Vec<Name> = Vec::new();
    ns8.push(name::dup(&n5));
    let w8 = prop_when::if_all_zero(ns8);
    let e28 = expr::forall_e(expr::dup(&e27), expr::dup(&e21), expr::binder_meta(w8));
    let u2 = level::param(name::dup(&n5));
    let e29 = expr::sort(level::dup(&u2));
    let e30 = expr::app(expr::dup(&e7), expr::dup(&e22));
    let e31 = expr::app(expr::dup(&e30), expr::dup(&e1));
    let e32 = expr::app(expr::dup(&e31), expr::dup(&e3));
    let w9 = prop_when::never();
    let e33 = expr::forall_e(expr::dup(&e32), expr::dup(&e29), expr::binder_meta(w9));
    let w10 = prop_when::never();
    let e34 = expr::forall_e(expr::dup(&e1), expr::dup(&e33), expr::binder_meta(w10));
    let mut ns9: Vec<Name> = Vec::new();
    ns9.push(name::dup(&n5));
    let w11 = prop_when::if_all_zero(ns9);
    let e35 = expr::forall_e(expr::dup(&e34), expr::dup(&e28), expr::binder_meta(w11));
    let mut ns10: Vec<Name> = Vec::new();
    ns10.push(name::dup(&n5));
    let w12 = prop_when::if_all_zero(ns10);
    let e36 = expr::forall_e(expr::dup(&e3), expr::dup(&e35), expr::binder_meta(w12));
    let mut ns11: Vec<Name> = Vec::new();
    ns11.push(name::dup(&n5));
    let w13 = prop_when::if_all_zero(ns11);
    let e37 = expr::forall_e(expr::dup(&e5), expr::dup(&e36), expr::binder_meta(w13));
    let cv2 = ConstantVal { name: name::dup(&n4), level_params: ns5, ty: expr::dup(&e37) };
    let mut ns12: Vec<Name> = Vec::new();
    ns12.push(name::dup(&n5));
    let w14 = prop_when::if_all_zero(ns12);
    let e38 = expr::lam(expr::dup(&e27), expr::dup(&e3), expr::binder_meta(w14));
    let mut ns13: Vec<Name> = Vec::new();
    ns13.push(name::dup(&n5));
    let w15 = prop_when::if_all_zero(ns13);
    let e39 = expr::lam(expr::dup(&e34), expr::dup(&e38), expr::binder_meta(w15));
    let mut ns14: Vec<Name> = Vec::new();
    ns14.push(name::dup(&n5));
    let w16 = prop_when::if_all_zero(ns14);
    let e40 = expr::lam(expr::dup(&e3), expr::dup(&e39), expr::binder_meta(w16));
    let mut ns15: Vec<Name> = Vec::new();
    ns15.push(name::dup(&n5));
    let w17 = prop_when::if_all_zero(ns15);
    let e41 = expr::lam(expr::dup(&e5), expr::dup(&e40), expr::binder_meta(w17));
    let rr0 = RecRule { ctor: name::dup(&n3), nfields: 0, ctor_params: 2, fire: RecRuleFire::Plain, rhs: expr::dup(&e41), k: true, eta: false, params_blind: true };
    let mut rs0: Vec<RecRule> = Vec::new();
    rs0.push(rr0);
    let ci2 = ConstantInfo::RecInfo(cv2, 5, 4, rs0);
    let mut out0: Vec<ConstantInfo> = Vec::new();
    out0.push(ci0);
    out0.push(ci1);
    out0.push(ci2);
    out0
}

/// con-leche: ConLeche/Kernel/BasisA.lean:50-57 BasisKind.declsA
/// con-leche: ConLeche/Kernel/Basis/Nat.lean:21-22 natT
/// con-leche: ConLeche/Kernel/Basis/Nat.lean:24-26 natRaw
/// con-leche: ConLeche/Kernel/Basis/Nat.lean:28-30 natZeroRaw
/// con-leche: ConLeche/Kernel/Basis/Nat.lean:32-34 natSuccRaw
/// con-leche: ConLeche/Kernel/Basis/Nat.lean:36-37 natRecMotive
/// con-leche: ConLeche/Kernel/Basis/Nat.lean:39-44 natRecSucc
/// con-leche: ConLeche/Kernel/Basis/Nat.lean:46-65 natRecRaw
/// con-leche: ConLeche/Kernel/Basis/Nat.lean:67-68 natBasis
/// The annotated `nat` block (`BasisKind.declsA .natK` = [natA, natZeroA, natSuccA, natRecA]).
///
/// `#annotate_basis` (`ConLeche/Kernel/BasisGen.lean`) computes those 4
/// constants from the 8 raw declarations cited above, while
/// `ConLeche/Kernel/BasisA.lean` elaborates; this function is that value,
/// emitted as source (the module note).
pub fn basis_decls_nat() -> Vec<ConstantInfo> {
    let n0 = name::anonymous();
    let mut s0: Vec<u32> = Vec::new();  // "Nat"
    s0.push(78);
    s0.push(97);
    s0.push(116);
    let n1 = name::mk_str(name::dup(&n0), s0);
    let ns0: Vec<Name> = Vec::new();
    let u0 = level::zero();
    let u1 = level::succ(level::dup(&u0));
    let e0 = expr::sort(level::dup(&u1));
    let cv0 = ConstantVal { name: name::dup(&n1), level_params: ns0, ty: expr::dup(&e0) };
    let ns1: Vec<Name> = Vec::new();
    let w0 = prop_when::if_all_zero(ns1);
    let ic0 = IndCaps { eta: false, eta_ctor: name::dup(&n0), eta_params: 0, eta_fields: 0, unitlike: false, unit_params: 0, rule_k: false, sort_z: w0 };
    let ci0 = ConstantInfo::IndInfo(cv0, ic0);
    let mut s1: Vec<u32> = Vec::new();  // "zero"
    s1.push(122);
    s1.push(101);
    s1.push(114);
    s1.push(111);
    let n2 = name::mk_str(name::dup(&n1), s1);
    let ns2: Vec<Name> = Vec::new();
    let us0: Vec<Level> = Vec::new();
    let e1 = expr::mk_const(name::dup(&n1), us0);
    let cv1 = ConstantVal { name: name::dup(&n2), level_params: ns2, ty: expr::dup(&e1) };
    let ci1 = ConstantInfo::CtorInfo(cv1, 0, 0);
    let mut s2: Vec<u32> = Vec::new();  // "succ"
    s2.push(115);
    s2.push(117);
    s2.push(99);
    s2.push(99);
    let n3 = name::mk_str(name::dup(&n1), s2);
    let ns3: Vec<Name> = Vec::new();
    let w1 = prop_when::never();
    let e2 = expr::forall_e(expr::dup(&e1), expr::dup(&e1), expr::binder_meta(w1));
    let cv2 = ConstantVal { name: name::dup(&n3), level_params: ns3, ty: expr::dup(&e2) };
    let ci2 = ConstantInfo::CtorInfo(cv2, 0, 1);
    let mut s3: Vec<u32> = Vec::new();  // "rec"
    s3.push(114);
    s3.push(101);
    s3.push(99);
    let n4 = name::mk_str(name::dup(&n1), s3);
    let mut s4: Vec<u32> = Vec::new();  // "u"
    s4.push(117);
    let n5 = name::mk_str(name::dup(&n0), s4);
    let mut ns4: Vec<Name> = Vec::new();
    ns4.push(name::dup(&n5));
    let e3 = expr::mk_bvar(0);
    let e4 = expr::mk_bvar(3);
    let e5 = expr::app(expr::dup(&e4), expr::dup(&e3));
    let mut ns5: Vec<Name> = Vec::new();
    ns5.push(name::dup(&n5));
    let w2 = prop_when::if_all_zero(ns5);
    let e6 = expr::forall_e(expr::dup(&e1), expr::dup(&e5), expr::binder_meta(w2));
    let e7 = expr::mk_bvar(1);
    let us1: Vec<Level> = Vec::new();
    let e8 = expr::mk_const(name::dup(&n3), us1);
    let e9 = expr::app(expr::dup(&e8), expr::dup(&e7));
    let e10 = expr::app(expr::dup(&e4), expr::dup(&e9));
    let e11 = expr::mk_bvar(2);
    let e12 = expr::app(expr::dup(&e11), expr::dup(&e3));
    let mut ns6: Vec<Name> = Vec::new();
    ns6.push(name::dup(&n5));
    let w3 = prop_when::if_all_zero(ns6);
    let e13 = expr::forall_e(expr::dup(&e12), expr::dup(&e10), expr::binder_meta(w3));
    let mut ns7: Vec<Name> = Vec::new();
    ns7.push(name::dup(&n5));
    let w4 = prop_when::if_all_zero(ns7);
    let e14 = expr::forall_e(expr::dup(&e1), expr::dup(&e13), expr::binder_meta(w4));
    let mut ns8: Vec<Name> = Vec::new();
    ns8.push(name::dup(&n5));
    let w5 = prop_when::if_all_zero(ns8);
    let e15 = expr::forall_e(expr::dup(&e14), expr::dup(&e6), expr::binder_meta(w5));
    let us2: Vec<Level> = Vec::new();
    let e16 = expr::mk_const(name::dup(&n2), us2);
    let e17 = expr::app(expr::dup(&e3), expr::dup(&e16));
    let mut ns9: Vec<Name> = Vec::new();
    ns9.push(name::dup(&n5));
    let w6 = prop_when::if_all_zero(ns9);
    let e18 = expr::forall_e(expr::dup(&e17), expr::dup(&e15), expr::binder_meta(w6));
    let u2 = level::param(name::dup(&n5));
    let e19 = expr::sort(level::dup(&u2));
    let w7 = prop_when::never();
    let e20 = expr::forall_e(expr::dup(&e1), expr::dup(&e19), expr::binder_meta(w7));
    let mut ns10: Vec<Name> = Vec::new();
    ns10.push(name::dup(&n5));
    let w8 = prop_when::if_all_zero(ns10);
    let e21 = expr::forall_e(expr::dup(&e20), expr::dup(&e18), expr::binder_meta(w8));
    let cv3 = ConstantVal { name: name::dup(&n4), level_params: ns4, ty: expr::dup(&e21) };
    let mut ns11: Vec<Name> = Vec::new();
    ns11.push(name::dup(&n5));
    let w9 = prop_when::if_all_zero(ns11);
    let e22 = expr::lam(expr::dup(&e14), expr::dup(&e7), expr::binder_meta(w9));
    let mut ns12: Vec<Name> = Vec::new();
    ns12.push(name::dup(&n5));
    let w10 = prop_when::if_all_zero(ns12);
    let e23 = expr::lam(expr::dup(&e17), expr::dup(&e22), expr::binder_meta(w10));
    let mut ns13: Vec<Name> = Vec::new();
    ns13.push(name::dup(&n5));
    let w11 = prop_when::if_all_zero(ns13);
    let e24 = expr::lam(expr::dup(&e20), expr::dup(&e23), expr::binder_meta(w11));
    let rr0 = RecRule { ctor: name::dup(&n2), nfields: 0, ctor_params: 0, fire: RecRuleFire::Plain, rhs: expr::dup(&e24), k: false, eta: false, params_blind: true };
    let mut us3: Vec<Level> = Vec::new();
    us3.push(level::dup(&u2));
    let e25 = expr::mk_const(name::dup(&n4), us3);
    let e26 = expr::app(expr::dup(&e25), expr::dup(&e4));
    let e27 = expr::app(expr::dup(&e26), expr::dup(&e11));
    let e28 = expr::app(expr::dup(&e27), expr::dup(&e7));
    let e29 = expr::app(expr::dup(&e28), expr::dup(&e3));
    let e30 = expr::app(expr::dup(&e7), expr::dup(&e3));
    let e31 = expr::app(expr::dup(&e30), expr::dup(&e29));
    let mut ns14: Vec<Name> = Vec::new();
    ns14.push(name::dup(&n5));
    let w12 = prop_when::if_all_zero(ns14);
    let e32 = expr::lam(expr::dup(&e1), expr::dup(&e31), expr::binder_meta(w12));
    let mut ns15: Vec<Name> = Vec::new();
    ns15.push(name::dup(&n5));
    let w13 = prop_when::if_all_zero(ns15);
    let e33 = expr::lam(expr::dup(&e14), expr::dup(&e32), expr::binder_meta(w13));
    let mut ns16: Vec<Name> = Vec::new();
    ns16.push(name::dup(&n5));
    let w14 = prop_when::if_all_zero(ns16);
    let e34 = expr::lam(expr::dup(&e17), expr::dup(&e33), expr::binder_meta(w14));
    let mut ns17: Vec<Name> = Vec::new();
    ns17.push(name::dup(&n5));
    let w15 = prop_when::if_all_zero(ns17);
    let e35 = expr::lam(expr::dup(&e20), expr::dup(&e34), expr::binder_meta(w15));
    let rr1 = RecRule { ctor: name::dup(&n3), nfields: 1, ctor_params: 0, fire: RecRuleFire::Plain, rhs: expr::dup(&e35), k: false, eta: false, params_blind: true };
    let mut rs0: Vec<RecRule> = Vec::new();
    rs0.push(rr0);
    rs0.push(rr1);
    let ci3 = ConstantInfo::RecInfo(cv3, 3, 3, rs0);
    let mut out0: Vec<ConstantInfo> = Vec::new();
    out0.push(ci0);
    out0.push(ci1);
    out0.push(ci2);
    out0.push(ci3);
    out0
}

/// con-leche: ConLeche/Kernel/BasisA.lean:50-57 BasisKind.declsA
/// con-leche: ConLeche/Kernel/Basis/PUnit.lean:24-29 punitRaw
/// con-leche: ConLeche/Kernel/Basis/PUnit.lean:31-33 punitUnitRaw
/// con-leche: ConLeche/Kernel/Basis/PUnit.lean:35-37 punitRecMotive
/// con-leche: ConLeche/Kernel/Basis/PUnit.lean:39-50 punitRecRaw
/// con-leche: ConLeche/Kernel/Basis/PUnit.lean:52-53 punitBasis
/// The annotated `punit` block (`BasisKind.declsA .punitK` = [punitA, punitUnitA, punitRecA]).
///
/// `#annotate_basis` (`ConLeche/Kernel/BasisGen.lean`) computes those 3
/// constants from the 5 raw declarations cited above, while
/// `ConLeche/Kernel/BasisA.lean` elaborates; this function is that value,
/// emitted as source (the module note).
pub fn basis_decls_punit() -> Vec<ConstantInfo> {
    let n0 = name::anonymous();
    let mut s0: Vec<u32> = Vec::new();  // "PUnit"
    s0.push(80);
    s0.push(85);
    s0.push(110);
    s0.push(105);
    s0.push(116);
    let n1 = name::mk_str(name::dup(&n0), s0);
    let mut s1: Vec<u32> = Vec::new();  // "u"
    s1.push(117);
    let n2 = name::mk_str(name::dup(&n0), s1);
    let mut ns0: Vec<Name> = Vec::new();
    ns0.push(name::dup(&n2));
    let u0 = level::param(name::dup(&n2));
    let e0 = expr::sort(level::dup(&u0));
    let cv0 = ConstantVal { name: name::dup(&n1), level_params: ns0, ty: expr::dup(&e0) };
    let mut s2: Vec<u32> = Vec::new();  // "unit"
    s2.push(117);
    s2.push(110);
    s2.push(105);
    s2.push(116);
    let n3 = name::mk_str(name::dup(&n1), s2);
    let mut ns1: Vec<Name> = Vec::new();
    ns1.push(name::dup(&n2));
    let w0 = prop_when::if_all_zero(ns1);
    let ic0 = IndCaps { eta: true, eta_ctor: name::dup(&n3), eta_params: 0, eta_fields: 0, unitlike: true, unit_params: 0, rule_k: false, sort_z: w0 };
    let ci0 = ConstantInfo::IndInfo(cv0, ic0);
    let mut ns2: Vec<Name> = Vec::new();
    ns2.push(name::dup(&n2));
    let mut us0: Vec<Level> = Vec::new();
    us0.push(level::dup(&u0));
    let e1 = expr::mk_const(name::dup(&n1), us0);
    let cv1 = ConstantVal { name: name::dup(&n3), level_params: ns2, ty: expr::dup(&e1) };
    let ci1 = ConstantInfo::CtorInfo(cv1, 0, 0);
    let mut s3: Vec<u32> = Vec::new();  // "rec"
    s3.push(114);
    s3.push(101);
    s3.push(99);
    let n4 = name::mk_str(name::dup(&n1), s3);
    let mut s4: Vec<u32> = Vec::new();  // "u_1"
    s4.push(117);
    s4.push(95);
    s4.push(49);
    let n5 = name::mk_str(name::dup(&n0), s4);
    let mut ns3: Vec<Name> = Vec::new();
    ns3.push(name::dup(&n5));
    ns3.push(name::dup(&n2));
    let e2 = expr::mk_bvar(0);
    let e3 = expr::mk_bvar(2);
    let e4 = expr::app(expr::dup(&e3), expr::dup(&e2));
    let mut ns4: Vec<Name> = Vec::new();
    ns4.push(name::dup(&n5));
    let w1 = prop_when::if_all_zero(ns4);
    let e5 = expr::forall_e(expr::dup(&e1), expr::dup(&e4), expr::binder_meta(w1));
    let mut us1: Vec<Level> = Vec::new();
    us1.push(level::dup(&u0));
    let e6 = expr::mk_const(name::dup(&n3), us1);
    let e7 = expr::app(expr::dup(&e2), expr::dup(&e6));
    let mut ns5: Vec<Name> = Vec::new();
    ns5.push(name::dup(&n5));
    let w2 = prop_when::if_all_zero(ns5);
    let e8 = expr::forall_e(expr::dup(&e7), expr::dup(&e5), expr::binder_meta(w2));
    let u1 = level::param(name::dup(&n5));
    let e9 = expr::sort(level::dup(&u1));
    let w3 = prop_when::never();
    let e10 = expr::forall_e(expr::dup(&e1), expr::dup(&e9), expr::binder_meta(w3));
    let mut ns6: Vec<Name> = Vec::new();
    ns6.push(name::dup(&n5));
    let w4 = prop_when::if_all_zero(ns6);
    let e11 = expr::forall_e(expr::dup(&e10), expr::dup(&e8), expr::binder_meta(w4));
    let cv2 = ConstantVal { name: name::dup(&n4), level_params: ns3, ty: expr::dup(&e11) };
    let mut ns7: Vec<Name> = Vec::new();
    ns7.push(name::dup(&n5));
    let w5 = prop_when::if_all_zero(ns7);
    let e12 = expr::lam(expr::dup(&e7), expr::dup(&e2), expr::binder_meta(w5));
    let mut ns8: Vec<Name> = Vec::new();
    ns8.push(name::dup(&n5));
    let w6 = prop_when::if_all_zero(ns8);
    let e13 = expr::lam(expr::dup(&e10), expr::dup(&e12), expr::binder_meta(w6));
    let rr0 = RecRule { ctor: name::dup(&n3), nfields: 0, ctor_params: 0, fire: RecRuleFire::Plain, rhs: expr::dup(&e13), k: false, eta: true, params_blind: true };
    let mut rs0: Vec<RecRule> = Vec::new();
    rs0.push(rr0);
    let ci2 = ConstantInfo::RecInfo(cv2, 2, 2, rs0);
    let mut out0: Vec<ConstantInfo> = Vec::new();
    out0.push(ci0);
    out0.push(ci1);
    out0.push(ci2);
    out0
}

/// con-leche: ConLeche/Kernel/BasisA.lean:50-57 BasisKind.declsA
/// con-leche: ConLeche/Kernel/Basis/Empty.lean:21-23 emptyRaw
/// con-leche: ConLeche/Kernel/Basis/Empty.lean:25-32 emptyRecRaw
/// con-leche: ConLeche/Kernel/Basis/Empty.lean:34-35 emptyBasis
/// The annotated `empty` block (`BasisKind.declsA .emptyK` = [emptyA, emptyRecA]).
///
/// `#annotate_basis` (`ConLeche/Kernel/BasisGen.lean`) computes those 2
/// constants from the 3 raw declarations cited above, while
/// `ConLeche/Kernel/BasisA.lean` elaborates; this function is that value,
/// emitted as source (the module note).
pub fn basis_decls_empty() -> Vec<ConstantInfo> {
    let n0 = name::anonymous();
    let mut s0: Vec<u32> = Vec::new();  // "Empty"
    s0.push(69);
    s0.push(109);
    s0.push(112);
    s0.push(116);
    s0.push(121);
    let n1 = name::mk_str(name::dup(&n0), s0);
    let ns0: Vec<Name> = Vec::new();
    let u0 = level::zero();
    let u1 = level::succ(level::dup(&u0));
    let e0 = expr::sort(level::dup(&u1));
    let cv0 = ConstantVal { name: name::dup(&n1), level_params: ns0, ty: expr::dup(&e0) };
    let ns1: Vec<Name> = Vec::new();
    let w0 = prop_when::if_all_zero(ns1);
    let ic0 = IndCaps { eta: false, eta_ctor: name::dup(&n0), eta_params: 0, eta_fields: 0, unitlike: false, unit_params: 0, rule_k: false, sort_z: w0 };
    let ci0 = ConstantInfo::IndInfo(cv0, ic0);
    let mut s1: Vec<u32> = Vec::new();  // "rec"
    s1.push(114);
    s1.push(101);
    s1.push(99);
    let n2 = name::mk_str(name::dup(&n1), s1);
    let mut s2: Vec<u32> = Vec::new();  // "u"
    s2.push(117);
    let n3 = name::mk_str(name::dup(&n0), s2);
    let mut ns2: Vec<Name> = Vec::new();
    ns2.push(name::dup(&n3));
    let e1 = expr::mk_bvar(0);
    let e2 = expr::mk_bvar(1);
    let e3 = expr::app(expr::dup(&e2), expr::dup(&e1));
    let us0: Vec<Level> = Vec::new();
    let e4 = expr::mk_const(name::dup(&n1), us0);
    let mut ns3: Vec<Name> = Vec::new();
    ns3.push(name::dup(&n3));
    let w1 = prop_when::if_all_zero(ns3);
    let e5 = expr::forall_e(expr::dup(&e4), expr::dup(&e3), expr::binder_meta(w1));
    let u2 = level::param(name::dup(&n3));
    let e6 = expr::sort(level::dup(&u2));
    let w2 = prop_when::never();
    let e7 = expr::forall_e(expr::dup(&e4), expr::dup(&e6), expr::binder_meta(w2));
    let mut ns4: Vec<Name> = Vec::new();
    ns4.push(name::dup(&n3));
    let w3 = prop_when::if_all_zero(ns4);
    let e8 = expr::forall_e(expr::dup(&e7), expr::dup(&e5), expr::binder_meta(w3));
    let cv1 = ConstantVal { name: name::dup(&n2), level_params: ns2, ty: expr::dup(&e8) };
    let rs0: Vec<RecRule> = Vec::new();
    let ci1 = ConstantInfo::RecInfo(cv1, 1, 1, rs0);
    let mut out0: Vec<ConstantInfo> = Vec::new();
    out0.push(ci0);
    out0.push(ci1);
    out0
}

/// con-leche: ConLeche/Kernel/BasisA.lean:50-57 BasisKind.declsA
/// con-leche: ConLeche/Kernel/Basis/False.lean:38-40 falseRaw
/// con-leche: ConLeche/Kernel/Basis/False.lean:42-49 falseRecRaw
/// con-leche: ConLeche/Kernel/Basis/False.lean:51-52 falseBasis
/// The annotated `false` block (`BasisKind.declsA .falseK` = [falseA, falseRecA]).
///
/// `#annotate_basis` (`ConLeche/Kernel/BasisGen.lean`) computes those 2
/// constants from the 3 raw declarations cited above, while
/// `ConLeche/Kernel/BasisA.lean` elaborates; this function is that value,
/// emitted as source (the module note).
pub fn basis_decls_false() -> Vec<ConstantInfo> {
    let n0 = name::anonymous();
    let mut s0: Vec<u32> = Vec::new();  // "False"
    s0.push(70);
    s0.push(97);
    s0.push(108);
    s0.push(115);
    s0.push(101);
    let n1 = name::mk_str(name::dup(&n0), s0);
    let ns0: Vec<Name> = Vec::new();
    let u0 = level::zero();
    let e0 = expr::sort(level::dup(&u0));
    let cv0 = ConstantVal { name: name::dup(&n1), level_params: ns0, ty: expr::dup(&e0) };
    let ns1: Vec<Name> = Vec::new();
    let w0 = prop_when::if_all_zero(ns1);
    let ic0 = IndCaps { eta: false, eta_ctor: name::dup(&n0), eta_params: 0, eta_fields: 0, unitlike: false, unit_params: 0, rule_k: false, sort_z: w0 };
    let ci0 = ConstantInfo::IndInfo(cv0, ic0);
    let mut s1: Vec<u32> = Vec::new();  // "rec"
    s1.push(114);
    s1.push(101);
    s1.push(99);
    let n2 = name::mk_str(name::dup(&n1), s1);
    let mut s2: Vec<u32> = Vec::new();  // "u"
    s2.push(117);
    let n3 = name::mk_str(name::dup(&n0), s2);
    let mut ns2: Vec<Name> = Vec::new();
    ns2.push(name::dup(&n3));
    let e1 = expr::mk_bvar(0);
    let e2 = expr::mk_bvar(1);
    let e3 = expr::app(expr::dup(&e2), expr::dup(&e1));
    let us0: Vec<Level> = Vec::new();
    let e4 = expr::mk_const(name::dup(&n1), us0);
    let mut ns3: Vec<Name> = Vec::new();
    ns3.push(name::dup(&n3));
    let w1 = prop_when::if_all_zero(ns3);
    let e5 = expr::forall_e(expr::dup(&e4), expr::dup(&e3), expr::binder_meta(w1));
    let u1 = level::param(name::dup(&n3));
    let e6 = expr::sort(level::dup(&u1));
    let w2 = prop_when::never();
    let e7 = expr::forall_e(expr::dup(&e4), expr::dup(&e6), expr::binder_meta(w2));
    let mut ns4: Vec<Name> = Vec::new();
    ns4.push(name::dup(&n3));
    let w3 = prop_when::if_all_zero(ns4);
    let e8 = expr::forall_e(expr::dup(&e7), expr::dup(&e5), expr::binder_meta(w3));
    let cv1 = ConstantVal { name: name::dup(&n2), level_params: ns2, ty: expr::dup(&e8) };
    let rs0: Vec<RecRule> = Vec::new();
    let ci1 = ConstantInfo::RecInfo(cv1, 1, 1, rs0);
    let mut out0: Vec<ConstantInfo> = Vec::new();
    out0.push(ci0);
    out0.push(ci1);
    out0
}

/// con-leche: ConLeche/Kernel/BasisA.lean:50-57 BasisKind.declsA
/// con-leche: ConLeche/Kernel/Basis/Quot.lean:26-28 quotRel
/// con-leche: ConLeche/Kernel/Basis/Quot.lean:30-34 quotRaw
/// con-leche: ConLeche/Kernel/Basis/Quot.lean:36-42 quotMkRaw
/// con-leche: ConLeche/Kernel/Basis/Quot.lean:44-45 quotLiftF
/// con-leche: ConLeche/Kernel/Basis/Quot.lean:47-53 quotLiftH
/// con-leche: ConLeche/Kernel/Basis/Quot.lean:55-72 quotLiftRaw
/// con-leche: ConLeche/Kernel/Basis/Quot.lean:74-77 quotIndMotive
/// con-leche: ConLeche/Kernel/Basis/Quot.lean:79-83 quotIndMk
/// con-leche: ConLeche/Kernel/Basis/Quot.lean:85-100 quotIndRaw
/// con-leche: ConLeche/Kernel/Basis/Quot.lean:102-114 quotSoundRaw
/// con-leche: ConLeche/Kernel/Basis/Quot.lean:116-118 quotBasis
/// The annotated `quot` block (`BasisKind.declsA .quotK` = [quotA, quotMkA, quotLiftA, quotIndA, quotSoundA]).
///
/// `#annotate_basis` (`ConLeche/Kernel/BasisGen.lean`) computes those 5
/// constants from the 11 raw declarations cited above, while
/// `ConLeche/Kernel/BasisA.lean` elaborates; this function is that value,
/// emitted as source (the module note).
pub fn basis_decls_quot() -> Vec<ConstantInfo> {
    let n0 = name::anonymous();
    let mut s0: Vec<u32> = Vec::new();  // "Quot"
    s0.push(81);
    s0.push(117);
    s0.push(111);
    s0.push(116);
    let n1 = name::mk_str(name::dup(&n0), s0);
    let mut s1: Vec<u32> = Vec::new();  // "u"
    s1.push(117);
    let n2 = name::mk_str(name::dup(&n0), s1);
    let mut ns0: Vec<Name> = Vec::new();
    ns0.push(name::dup(&n2));
    let u0 = level::param(name::dup(&n2));
    let e0 = expr::sort(level::dup(&u0));
    let u1 = level::zero();
    let e1 = expr::sort(level::dup(&u1));
    let e2 = expr::mk_bvar(1);
    let w0 = prop_when::never();
    let e3 = expr::forall_e(expr::dup(&e2), expr::dup(&e1), expr::binder_meta(w0));
    let e4 = expr::mk_bvar(0);
    let w1 = prop_when::never();
    let e5 = expr::forall_e(expr::dup(&e4), expr::dup(&e3), expr::binder_meta(w1));
    let w2 = prop_when::never();
    let e6 = expr::forall_e(expr::dup(&e5), expr::dup(&e0), expr::binder_meta(w2));
    let w3 = prop_when::never();
    let e7 = expr::forall_e(expr::dup(&e0), expr::dup(&e6), expr::binder_meta(w3));
    let cv0 = ConstantVal { name: name::dup(&n1), level_params: ns0, ty: expr::dup(&e7) };
    let ns1: Vec<Name> = Vec::new();
    let w4 = prop_when::if_all_zero(ns1);
    let ic0 = IndCaps { eta: false, eta_ctor: name::dup(&n0), eta_params: 0, eta_fields: 0, unitlike: false, unit_params: 0, rule_k: false, sort_z: w4 };
    let ci0 = ConstantInfo::IndInfo(cv0, ic0);
    let mut s2: Vec<u32> = Vec::new();  // "mk"
    s2.push(109);
    s2.push(107);
    let n3 = name::mk_str(name::dup(&n1), s2);
    let mut ns2: Vec<Name> = Vec::new();
    ns2.push(name::dup(&n2));
    let e8 = expr::mk_bvar(2);
    let mut us0: Vec<Level> = Vec::new();
    us0.push(level::dup(&u0));
    let e9 = expr::mk_const(name::dup(&n1), us0);
    let e10 = expr::app(expr::dup(&e9), expr::dup(&e8));
    let e11 = expr::app(expr::dup(&e10), expr::dup(&e2));
    let mut ns3: Vec<Name> = Vec::new();
    ns3.push(name::dup(&n2));
    let w5 = prop_when::if_all_zero(ns3);
    let e12 = expr::forall_e(expr::dup(&e2), expr::dup(&e11), expr::binder_meta(w5));
    let mut ns4: Vec<Name> = Vec::new();
    ns4.push(name::dup(&n2));
    let w6 = prop_when::if_all_zero(ns4);
    let e13 = expr::forall_e(expr::dup(&e5), expr::dup(&e12), expr::binder_meta(w6));
    let mut ns5: Vec<Name> = Vec::new();
    ns5.push(name::dup(&n2));
    let w7 = prop_when::if_all_zero(ns5);
    let e14 = expr::forall_e(expr::dup(&e0), expr::dup(&e13), expr::binder_meta(w7));
    let cv1 = ConstantVal { name: name::dup(&n3), level_params: ns2, ty: expr::dup(&e14) };
    let ci1 = ConstantInfo::CtorInfo(cv1, 2, 1);
    let mut s3: Vec<u32> = Vec::new();  // "lift"
    s3.push(108);
    s3.push(105);
    s3.push(102);
    s3.push(116);
    let n4 = name::mk_str(name::dup(&n1), s3);
    let mut s4: Vec<u32> = Vec::new();  // "v"
    s4.push(118);
    let n5 = name::mk_str(name::dup(&n0), s4);
    let mut ns6: Vec<Name> = Vec::new();
    ns6.push(name::dup(&n2));
    ns6.push(name::dup(&n5));
    let e15 = expr::mk_bvar(3);
    let e16 = expr::mk_bvar(4);
    let e17 = expr::app(expr::dup(&e9), expr::dup(&e16));
    let e18 = expr::app(expr::dup(&e17), expr::dup(&e15));
    let mut ns7: Vec<Name> = Vec::new();
    ns7.push(name::dup(&n5));
    let w8 = prop_when::if_all_zero(ns7);
    let e19 = expr::forall_e(expr::dup(&e18), expr::dup(&e15), expr::binder_meta(w8));
    let e20 = expr::app(expr::dup(&e15), expr::dup(&e2));
    let e21 = expr::app(expr::dup(&e15), expr::dup(&e8));
    let mut s5: Vec<u32> = Vec::new();  // "Eq"
    s5.push(69);
    s5.push(113);
    let n6 = name::mk_str(name::dup(&n0), s5);
    let u2 = level::param(name::dup(&n5));
    let mut us1: Vec<Level> = Vec::new();
    us1.push(level::dup(&u2));
    let e22 = expr::mk_const(name::dup(&n6), us1);
    let e23 = expr::app(expr::dup(&e22), expr::dup(&e16));
    let e24 = expr::app(expr::dup(&e23), expr::dup(&e21));
    let e25 = expr::app(expr::dup(&e24), expr::dup(&e20));
    let e26 = expr::app(expr::dup(&e16), expr::dup(&e2));
    let e27 = expr::app(expr::dup(&e26), expr::dup(&e4));
    let ns8: Vec<Name> = Vec::new();
    let w9 = prop_when::if_all_zero(ns8);
    let e28 = expr::forall_e(expr::dup(&e27), expr::dup(&e25), expr::binder_meta(w9));
    let ns9: Vec<Name> = Vec::new();
    let w10 = prop_when::if_all_zero(ns9);
    let e29 = expr::forall_e(expr::dup(&e16), expr::dup(&e28), expr::binder_meta(w10));
    let ns10: Vec<Name> = Vec::new();
    let w11 = prop_when::if_all_zero(ns10);
    let e30 = expr::forall_e(expr::dup(&e15), expr::dup(&e29), expr::binder_meta(w11));
    let mut ns11: Vec<Name> = Vec::new();
    ns11.push(name::dup(&n5));
    let w12 = prop_when::if_all_zero(ns11);
    let e31 = expr::forall_e(expr::dup(&e30), expr::dup(&e19), expr::binder_meta(w12));
    let mut ns12: Vec<Name> = Vec::new();
    ns12.push(name::dup(&n5));
    let w13 = prop_when::if_all_zero(ns12);
    let e32 = expr::forall_e(expr::dup(&e8), expr::dup(&e2), expr::binder_meta(w13));
    let mut ns13: Vec<Name> = Vec::new();
    ns13.push(name::dup(&n5));
    let w14 = prop_when::if_all_zero(ns13);
    let e33 = expr::forall_e(expr::dup(&e32), expr::dup(&e31), expr::binder_meta(w14));
    let e34 = expr::sort(level::dup(&u2));
    let mut ns14: Vec<Name> = Vec::new();
    ns14.push(name::dup(&n5));
    let w15 = prop_when::if_all_zero(ns14);
    let e35 = expr::forall_e(expr::dup(&e34), expr::dup(&e33), expr::binder_meta(w15));
    let mut ns15: Vec<Name> = Vec::new();
    ns15.push(name::dup(&n5));
    let w16 = prop_when::if_all_zero(ns15);
    let e36 = expr::forall_e(expr::dup(&e5), expr::dup(&e35), expr::binder_meta(w16));
    let mut ns16: Vec<Name> = Vec::new();
    ns16.push(name::dup(&n5));
    let w17 = prop_when::if_all_zero(ns16);
    let e37 = expr::forall_e(expr::dup(&e0), expr::dup(&e36), expr::binder_meta(w17));
    let cv2 = ConstantVal { name: name::dup(&n4), level_params: ns6, ty: expr::dup(&e37) };
    let e38 = expr::app(expr::dup(&e8), expr::dup(&e4));
    let mut ns17: Vec<Name> = Vec::new();
    ns17.push(name::dup(&n5));
    let w18 = prop_when::if_all_zero(ns17);
    let e39 = expr::lam(expr::dup(&e16), expr::dup(&e38), expr::binder_meta(w18));
    let mut ns18: Vec<Name> = Vec::new();
    ns18.push(name::dup(&n5));
    let w19 = prop_when::if_all_zero(ns18);
    let e40 = expr::lam(expr::dup(&e30), expr::dup(&e39), expr::binder_meta(w19));
    let mut ns19: Vec<Name> = Vec::new();
    ns19.push(name::dup(&n5));
    let w20 = prop_when::if_all_zero(ns19);
    let e41 = expr::lam(expr::dup(&e32), expr::dup(&e40), expr::binder_meta(w20));
    let mut ns20: Vec<Name> = Vec::new();
    ns20.push(name::dup(&n5));
    let w21 = prop_when::if_all_zero(ns20);
    let e42 = expr::lam(expr::dup(&e34), expr::dup(&e41), expr::binder_meta(w21));
    let mut ns21: Vec<Name> = Vec::new();
    ns21.push(name::dup(&n5));
    let w22 = prop_when::if_all_zero(ns21);
    let e43 = expr::lam(expr::dup(&e5), expr::dup(&e42), expr::binder_meta(w22));
    let mut ns22: Vec<Name> = Vec::new();
    ns22.push(name::dup(&n5));
    let w23 = prop_when::if_all_zero(ns22);
    let e44 = expr::lam(expr::dup(&e0), expr::dup(&e43), expr::binder_meta(w23));
    let rr0 = RecRule { ctor: name::dup(&n3), nfields: 1, ctor_params: 2, fire: RecRuleFire::Plain, rhs: expr::dup(&e44), k: false, eta: false, params_blind: true };
    let mut rs0: Vec<RecRule> = Vec::new();
    rs0.push(rr0);
    let ci2 = ConstantInfo::RecInfo(cv2, 5, 5, rs0);
    let mut s6: Vec<u32> = Vec::new();  // "ind"
    s6.push(105);
    s6.push(110);
    s6.push(100);
    let n7 = name::mk_str(name::dup(&n1), s6);
    let mut ns23: Vec<Name> = Vec::new();
    ns23.push(name::dup(&n2));
    let e45 = expr::app(expr::dup(&e9), expr::dup(&e15));
    let e46 = expr::app(expr::dup(&e45), expr::dup(&e8));
    let ns24: Vec<Name> = Vec::new();
    let w24 = prop_when::if_all_zero(ns24);
    let e47 = expr::forall_e(expr::dup(&e46), expr::dup(&e38), expr::binder_meta(w24));
    let mut us2: Vec<Level> = Vec::new();
    us2.push(level::dup(&u0));
    let e48 = expr::mk_const(name::dup(&n3), us2);
    let e49 = expr::app(expr::dup(&e48), expr::dup(&e15));
    let e50 = expr::app(expr::dup(&e49), expr::dup(&e8));
    let e51 = expr::app(expr::dup(&e50), expr::dup(&e4));
    let e52 = expr::app(expr::dup(&e2), expr::dup(&e51));
    let ns25: Vec<Name> = Vec::new();
    let w25 = prop_when::if_all_zero(ns25);
    let e53 = expr::forall_e(expr::dup(&e8), expr::dup(&e52), expr::binder_meta(w25));
    let ns26: Vec<Name> = Vec::new();
    let w26 = prop_when::if_all_zero(ns26);
    let e54 = expr::forall_e(expr::dup(&e53), expr::dup(&e47), expr::binder_meta(w26));
    let e55 = expr::app(expr::dup(&e9), expr::dup(&e2));
    let e56 = expr::app(expr::dup(&e55), expr::dup(&e4));
    let w27 = prop_when::never();
    let e57 = expr::forall_e(expr::dup(&e56), expr::dup(&e1), expr::binder_meta(w27));
    let ns27: Vec<Name> = Vec::new();
    let w28 = prop_when::if_all_zero(ns27);
    let e58 = expr::forall_e(expr::dup(&e57), expr::dup(&e54), expr::binder_meta(w28));
    let ns28: Vec<Name> = Vec::new();
    let w29 = prop_when::if_all_zero(ns28);
    let e59 = expr::forall_e(expr::dup(&e5), expr::dup(&e58), expr::binder_meta(w29));
    let ns29: Vec<Name> = Vec::new();
    let w30 = prop_when::if_all_zero(ns29);
    let e60 = expr::forall_e(expr::dup(&e0), expr::dup(&e59), expr::binder_meta(w30));
    let cv3 = ConstantVal { name: name::dup(&n7), level_params: ns23, ty: expr::dup(&e60) };
    let e61 = expr::app(expr::dup(&e2), expr::dup(&e4));
    let ns30: Vec<Name> = Vec::new();
    let w31 = prop_when::if_all_zero(ns30);
    let e62 = expr::lam(expr::dup(&e15), expr::dup(&e61), expr::binder_meta(w31));
    let ns31: Vec<Name> = Vec::new();
    let w32 = prop_when::if_all_zero(ns31);
    let e63 = expr::lam(expr::dup(&e53), expr::dup(&e62), expr::binder_meta(w32));
    let ns32: Vec<Name> = Vec::new();
    let w33 = prop_when::if_all_zero(ns32);
    let e64 = expr::lam(expr::dup(&e57), expr::dup(&e63), expr::binder_meta(w33));
    let ns33: Vec<Name> = Vec::new();
    let w34 = prop_when::if_all_zero(ns33);
    let e65 = expr::lam(expr::dup(&e5), expr::dup(&e64), expr::binder_meta(w34));
    let ns34: Vec<Name> = Vec::new();
    let w35 = prop_when::if_all_zero(ns34);
    let e66 = expr::lam(expr::dup(&e0), expr::dup(&e65), expr::binder_meta(w35));
    let rr1 = RecRule { ctor: name::dup(&n3), nfields: 1, ctor_params: 2, fire: RecRuleFire::Plain, rhs: expr::dup(&e66), k: false, eta: false, params_blind: true };
    let mut rs1: Vec<RecRule> = Vec::new();
    rs1.push(rr1);
    let ci3 = ConstantInfo::RecInfo(cv3, 4, 4, rs1);
    let mut s7: Vec<u32> = Vec::new();  // "sound"
    s7.push(115);
    s7.push(111);
    s7.push(117);
    s7.push(110);
    s7.push(100);
    let n8 = name::mk_str(name::dup(&n1), s7);
    let mut ns35: Vec<Name> = Vec::new();
    ns35.push(name::dup(&n2));
    let e67 = expr::app(expr::dup(&e48), expr::dup(&e16));
    let e68 = expr::app(expr::dup(&e67), expr::dup(&e15));
    let e69 = expr::app(expr::dup(&e68), expr::dup(&e2));
    let e70 = expr::app(expr::dup(&e68), expr::dup(&e8));
    let mut us3: Vec<Level> = Vec::new();
    us3.push(level::dup(&u0));
    let e71 = expr::mk_const(name::dup(&n6), us3);
    let e72 = expr::app(expr::dup(&e71), expr::dup(&e18));
    let e73 = expr::app(expr::dup(&e72), expr::dup(&e70));
    let e74 = expr::app(expr::dup(&e73), expr::dup(&e69));
    let e75 = expr::app(expr::dup(&e8), expr::dup(&e2));
    let e76 = expr::app(expr::dup(&e75), expr::dup(&e4));
    let ns36: Vec<Name> = Vec::new();
    let w36 = prop_when::if_all_zero(ns36);
    let e77 = expr::forall_e(expr::dup(&e76), expr::dup(&e74), expr::binder_meta(w36));
    let ns37: Vec<Name> = Vec::new();
    let w37 = prop_when::if_all_zero(ns37);
    let e78 = expr::forall_e(expr::dup(&e8), expr::dup(&e77), expr::binder_meta(w37));
    let ns38: Vec<Name> = Vec::new();
    let w38 = prop_when::if_all_zero(ns38);
    let e79 = expr::forall_e(expr::dup(&e2), expr::dup(&e78), expr::binder_meta(w38));
    let ns39: Vec<Name> = Vec::new();
    let w39 = prop_when::if_all_zero(ns39);
    let e80 = expr::forall_e(expr::dup(&e5), expr::dup(&e79), expr::binder_meta(w39));
    let ns40: Vec<Name> = Vec::new();
    let w40 = prop_when::if_all_zero(ns40);
    let e81 = expr::forall_e(expr::dup(&e0), expr::dup(&e80), expr::binder_meta(w40));
    let cv4 = ConstantVal { name: name::dup(&n8), level_params: ns35, ty: expr::dup(&e81) };
    let ci4 = ConstantInfo::AxiomInfo(cv4);
    let mut out0: Vec<ConstantInfo> = Vec::new();
    out0.push(ci0);
    out0.push(ci1);
    out0.push(ci2);
    out0.push(ci3);
    out0.push(ci4);
    out0
}

/// The annotated constants of one basis block, in dependency order.
pub fn basis_decls_a(k: &BasisKind) -> Vec<ConstantInfo> {
    match k {
        BasisKind::EqK => basis_decls_eq(),
        BasisKind::NatK => basis_decls_nat(),
        BasisKind::PunitK => basis_decls_punit(),
        BasisKind::EmptyK => basis_decls_empty(),
        BasisKind::FalseK => basis_decls_false(),
        BasisKind::QuotK => basis_decls_quot(),
    }
}

