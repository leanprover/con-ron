//! `arena::inductives::sum_parts` — the block's shape record.
//!
//! The Rust twin of `proof/ConRon/Arena/Inductives/SumParts.lean`, which is
//! `ConLeche/Kernel/Inductives/SumParts.lean` whole over handles: the record a
//! recognised direct block is read into, the member split that reads it, and
//! the completion with the result sort the former's install stage measured.
//!
//! **The twin's one deviation carries over**: `sumSplit` stays PURE — it
//! matches on the members' CONSTRUCTORS and moves their fields, touching no
//! term, so it takes no state.  `InductiveShape.withSort` does not: `isProp`
//! is `lvlEq? s zero`, which reads the level store and caches its verdict.
//!
//! Two shapes are the port's, and both are `con_ron_core::kernel::inductives::
//! sum_parts`' as well: the `List` recursion is a cursor recursion, and the
//! nested `Option`-of-tuple return of `sumSplit` is one five-component tuple
//! (Lean's `q.2` is the same thing).

use crate::arena::core;
use crate::arena::env;
use crate::arena::env::{IConstantInfo, IConstantVal, IRecRule};
use crate::arena::handle::{EIdx, LIdx, NIdx};
use crate::arena::monad::AState;
use crate::kernel::core_types::CheckError;
use crate::ron::hashmap::Dup;
use crate::arena::store::PersTier;

/// con-leche: ConLeche/Kernel/Inductives/SumParts.lean:78-101 InductiveShape
/// Lean twin: `proof/ConRon/Arena/Inductives/SumParts.lean:24-45 InductiveShape`
/// — the pieces of a recognised direct sum block, over handles.
pub struct InductiveShape {
    /// the type former
    pub cv_t: IConstantVal,
    /// the constructors in declaration order, each with its field count
    pub ctors: Vec<(IConstantVal, u64)>,
    /// parameter count
    pub n_p: u64,
    /// index count (`0` at a plain sum)
    pub n_idx: u64,
    /// the recursor
    pub cv_r: IConstantVal,
    /// the recursor's fresh elimination level parameter (`large` only)
    pub elim: NIdx,
    /// the result sort
    pub res_sort: LIdx,
    /// the rules' right-hand sides as exported, in constructor order
    pub rhss: Vec<EIdx>,
    /// large eliminator (a fresh elimination level parameter in front)
    pub large: bool,
    /// the result sort is provably `Prop`
    pub is_prop: bool,
}

/// con-leche: ConLeche/Kernel/Inductives/SumParts.lean:78-101 InductiveShape
/// Lean twin: `proof/ConRon/Arena/Inductives/SumParts.lean:24-45 InductiveShape`
/// — the record copy, which Lean's value semantics gives for free.
pub fn inductive_shape_dup(p: &InductiveShape) -> InductiveShape {
    InductiveShape {
        cv_t: env::i_constant_val_dup(&p.cv_t),
        ctors: ctors_copy(&p.ctors),
        n_p: p.n_p,
        n_idx: p.n_idx,
        cv_r: env::i_constant_val_dup(&p.cv_r),
        elim: p.elim.dup2(),
        res_sort: p.res_sort.dup2(),
        rhss: env::eidx_vec_dup(&p.rhss),
        large: p.large,
        is_prop: p.is_prop,
    }
}

/// con-leche: none — a `Vec<(IConstantVal, u64)>` copy; Lean shares the list
/// Lean twin: `proof/ConRon/Arena/Inductives/SumParts.lean:29 InductiveShape`
/// — the constructors' spine, copied.
pub fn ctors_copy(cs: &Vec<(IConstantVal, u64)>) -> Vec<(IConstantVal, u64)> {
    ctors_copy_from(cs, 0, Vec::new())
}

/// con-leche: none — a `Vec<(IConstantVal, u64)>` copy
/// Lean twin: `proof/ConRon/Arena/Inductives/SumParts.lean:29 InductiveShape`
/// — the cursor recursion behind `ctors_copy`.
pub fn ctors_copy_from(
    cs: &Vec<(IConstantVal, u64)>,
    i: usize,
    out: Vec<(IConstantVal, u64)>,
) -> Vec<(IConstantVal, u64)> {
    if i >= cs.len() {
        out
    } else {
        let mut o: Vec<(IConstantVal, u64)> = out;
        o.push((env::i_constant_val_dup(&cs[i].0), cs[i].1));
        ctors_copy_from(cs, i + 1, o)
    }
}

/// con-leche: ConLeche/Kernel/Inductives/SumParts.lean:103-110 sumSplit
/// Lean twin: `proof/ConRon/Arena/Inductives/SumParts.lean:50-55 sumSplit` —
/// the block's members after the type former: the constructors, then the
/// closing recursor.  Pure; see the module note.
pub fn sum_split(
    block: &Vec<IConstantInfo>,
) -> Option<(
    Vec<(IConstantVal, u64, u64)>,
    IConstantVal,
    u64,
    u64,
    Vec<IRecRule>,
)> {
    sum_split_from(block, 0, Vec::new())
}

/// con-leche: ConLeche/Kernel/Inductives/SumParts.lean:103-110 sumSplit
/// Lean twin: `proof/ConRon/Arena/Inductives/SumParts.lean:50-55 sumSplit` —
/// the cursor recursion behind `sum_split`.  Lean conses the constructor on
/// the way *out*; the port accumulates on the way *in*, which is the same
/// declaration-order list.  The one-element `[.recInfo …]` arm is "the cursor
/// is at the last member and it is a recursor"; anything else — a recursor
/// that is not last, a non-constructor member, an exhausted list — is `none`.
pub fn sum_split_from(
    block: &Vec<IConstantInfo>,
    i: usize,
    out: Vec<(IConstantVal, u64, u64)>,
) -> Option<(
    Vec<(IConstantVal, u64, u64)>,
    IConstantVal,
    u64,
    u64,
    Vec<IRecRule>,
)> {
    if i >= block.len() {
        None
    } else {
        match &block[i] {
            IConstantInfo::RecInfo(cv_r, m_i, r_p, rules) => {
                if i + 1 == block.len() {
                    Some((
                        out,
                        env::i_constant_val_dup(cv_r),
                        *m_i,
                        *r_p,
                        env::i_rec_rules_dup(rules),
                    ))
                } else {
                    None
                }
            }
            IConstantInfo::CtorInfo(cv_c, n_p, n_f) => {
                let mut o: Vec<(IConstantVal, u64, u64)> = out;
                o.push((env::i_constant_val_dup(cv_c), *n_p, *n_f));
                sum_split_from(block, i + 1, o)
            }
            _ => None,
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/SumParts.lean:112-119 InductiveShape.withSort
/// Lean twin: `proof/ConRon/Arena/Inductives/SumParts.lean:60-62 InductiveShape.withSort`
/// — the record completed with the former's result sort (con-leche's task
/// #195); `isProp` is recomputed so that the recogniser's invariant holds by
/// definition.  The record is taken by value and returned, which is the cited
/// `{ p with … }` exactly.
pub fn with_sort(
    pers: &PersTier,
    st: &mut AState,
    p: InductiveShape,
    s: LIdx,
) -> Result<InductiveShape, CheckError> {
    match core::zero_level(st) {
        Err(e) => Err(e),
        Ok(z) => match core::lvl_eq(pers, st, &s, &z) {
            Err(e) => Err(e),
            Ok(eq) => {
                let is_prop: bool = match eq {
                    Some(true) => true,
                    Some(false) => false,
                    None => false,
                };
                let mut p2: InductiveShape = p;
                p2.res_sort = s;
                p2.is_prop = is_prop;
                Ok(p2)
            }
        },
    }
}

/// con-leche: ConLeche/Kernel/Inductives/SumInstall.lean:292-294 InductiveShape.rulePrefix
/// Lean twin: `proof/ConRon/Arena/Inductives/SumInstall.lean:322 InductiveShape.rulePrefix`
/// — the recursor's rule prefix (parameters, motive, minors).  Ported with its
/// record rather than with `SumInstall.lean`'s install stages: it is a reader
/// of this record and nothing else.
pub fn rule_prefix(p: &InductiveShape) -> u64 {
    p.n_p + 1 + p.ctors.len() as u64
}

/// con-leche: ConLeche/Kernel/Inductives/SumInstall.lean:295 InductiveShape.majorIdx
/// Lean twin: `proof/ConRon/Arena/Inductives/SumInstall.lean:326 InductiveShape.majorIdx`
/// — the recursor's major index (the rule prefix, then the indices).
pub fn major_idx(p: &InductiveShape) -> u64 {
    rule_prefix(p) + p.n_idx
}
