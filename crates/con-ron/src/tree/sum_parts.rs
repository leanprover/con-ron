//! `ConLeche/Kernel/Inductives/SumParts.lean` — the block-shape record every
//! direct (fixpoint-route) install is read into, and the member split that
//! recognises it.
//!
//! The file's other 15 declarations are the `@[simp]` projection equations of
//! `InductiveShape.withSort` plus `withSort_self`; they are the *spec* this
//! port will be proved against and carry no code (task #18's rule).

use con_ron_core::kernel::env;
use con_ron_core::kernel::env::{ConstantInfo, ConstantVal, RecRule};
use con_ron_core::kernel::expr::Expr;
use con_ron_core::kernel::level;
use con_ron_core::kernel::level::Level;
use con_ron_core::kernel::name;
use con_ron_core::kernel::name::Name;
use std::vec::Vec;

/// con-leche: ConLeche/Kernel/Inductives/SumParts.lean:78-101 InductiveShape
/// The pieces of a recognised direct block: the type former, the
/// constructors in declaration order with their field counts, the parameter
/// and index counts, the recursor, its fresh elimination level parameter
/// (`.anonymous` at a small eliminator), the result sort, the rules'
/// right-hand sides as exported, and the two flags.
///
/// Deviations: `deriving Repr` is dropped (rendering only; §3.4 forbids
/// `derive` on the core types), `List` is `Vec`, and every count is `u64`
/// (§3.3).
pub struct InductiveShape {
    pub cv_t: ConstantVal,
    pub ctors: Vec<(ConstantVal, u64)>,
    pub n_p: u64,
    pub n_idx: u64,
    pub cv_r: ConstantVal,
    pub elim: Name,
    pub res_sort: Level,
    pub rhss: Vec<Expr>,
    pub large: bool,
    pub is_prop: bool,
}

/// con-leche: ConLeche/Kernel/Inductives/SumParts.lean:78-101 InductiveShape
/// The record copy — what Lean's value semantics gives for free.
pub fn inductive_shape_dup(p: &InductiveShape) -> InductiveShape {
    InductiveShape {
        cv_t: env::constant_val_dup(&p.cv_t),
        ctors: ctors_copy(&p.ctors),
        n_p: p.n_p,
        n_idx: p.n_idx,
        cv_r: env::constant_val_dup(&p.cv_r),
        elim: name::dup(&p.elim),
        res_sort: level::dup(&p.res_sort),
        rhss: env::exprs_copy(&p.rhss),
        large: p.large,
        is_prop: p.is_prop,
    }
}

/// con-leche: none — a `Vec<(ConstantVal, u64)>` copy; Lean shares the list
/// The entry point of the index recursion below.
pub fn ctors_copy(cs: &Vec<(ConstantVal, u64)>) -> Vec<(ConstantVal, u64)> {
    ctors_copy_from(cs, 0, Vec::new())
}

/// con-leche: none — the index recursion behind `ctors_copy`
pub fn ctors_copy_from(
    cs: &Vec<(ConstantVal, u64)>,
    i: usize,
    out: Vec<(ConstantVal, u64)>,
) -> Vec<(ConstantVal, u64)> {
    if i >= cs.len() {
        out
    } else {
        let mut out = out;
        out.push((env::constant_val_dup(&cs[i].0), cs[i].1));
        ctors_copy_from(cs, i + 1, out)
    }
}

/// con-leche: ConLeche/Kernel/Inductives/SumParts.lean:103-110 sumSplit
/// The block's members after the type former: the constructors (each with
/// its parameter and field count), then the closing recursor with its two
/// argument sums and its rules.
///
/// Deviations: the `List` recursion becomes the index recursion below
/// (task #3's pattern), and the nested `Option`-of-tuple return is flattened
/// into one five-component tuple — Lean's `q.2` is the same thing.
pub fn sum_split(
    block: &Vec<ConstantInfo>,
) -> Option<(
    Vec<(ConstantVal, u64, u64)>,
    ConstantVal,
    u64,
    u64,
    Vec<RecRule>,
)> {
    sum_split_from(block, 0, Vec::new())
}

/// con-leche: ConLeche/Kernel/Inductives/SumParts.lean:103-110 sumSplit
/// The index recursion behind `sum_split`.  Lean conses the constructor on
/// the way *out* (`(cvC, nP, nF) :: q.1`); the port accumulates on the way
/// *in*, which produces the same declaration-order list (task #13's
/// pattern 3).  The one-element `[.recInfo …]` arm is "the cursor is at the
/// last member and it is a recursor"; anything else — a recursor that is not
/// last, a non-constructor member, an exhausted list — is `none`.
pub fn sum_split_from(
    block: &Vec<ConstantInfo>,
    i: usize,
    out: Vec<(ConstantVal, u64, u64)>,
) -> Option<(
    Vec<(ConstantVal, u64, u64)>,
    ConstantVal,
    u64,
    u64,
    Vec<RecRule>,
)> {
    if i >= block.len() {
        None
    } else {
        match &block[i] {
            ConstantInfo::RecInfo(cv_r, m_i, r_p, rules) => {
                if i + 1 == block.len() {
                    Some((
                        out,
                        env::constant_val_dup(cv_r),
                        *m_i,
                        *r_p,
                        env::rec_rules_copy(rules),
                    ))
                } else {
                    None
                }
            }
            ConstantInfo::CtorInfo(cv_c, n_p, n_f) => {
                let mut out = out;
                out.push((env::constant_val_dup(cv_c), *n_p, *n_f));
                sum_split_from(block, i + 1, out)
            }
            _ => None,
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/SumParts.lean:112-119 InductiveShape.withSort
/// The record completed with the former's result sort, which the install
/// stage reads off the checked telescope.  `isProp` is recomputed so that
/// the recogniser's invariant `isProp = (isEquiv resSort zero == some true)`
/// holds by definition.
///
/// Deviation: the record is taken *by value* and returned, which is the
/// cited `{ p with … }` exactly (task #14's `FEnv` ruling: a Lean record
/// update is a move plus one field, not a `&mut`).
pub fn with_sort(p: InductiveShape, s: Level) -> InductiveShape {
    let is_prop = crate::tree::struct_parts::level_is_prop(&s);
    let mut p = p;
    p.res_sort = s;
    p.is_prop = is_prop;
    p
}

/// con-leche: ConLeche/Kernel/Inductives/SumInstall.lean:292-294 InductiveShape.rulePrefix
/// The recursor's rule prefix: the parameters, the motive and the minors.
/// Ported with its record rather than with `SumInstall.lean`'s install
/// stages (the cited file defines it beside the stages that consume it, but
/// it is a reader of this record and nothing else).
pub fn rule_prefix(p: &InductiveShape) -> u64 {
    p.n_p + 1 + p.ctors.len() as u64
}

/// con-leche: ConLeche/Kernel/Inductives/SumInstall.lean:295-295 InductiveShape.majorIdx
/// The major premise's index: the rule prefix, then the indices.
pub fn major_idx(p: &InductiveShape) -> u64 {
    rule_prefix(p) + p.n_idx
}
