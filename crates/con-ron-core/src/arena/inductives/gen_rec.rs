//! `arena::inductives::gen_rec` — the recursor family, GENERATED.
//!
//! The Rust twin of `proof/ConRon/Arena/Inductives/GenRec.lean`, which is
//! `ConLeche/Kernel/Inductives/GenRec.lean` over handles: the classes read and
//! checked (`checkBlockClasses`), per class and constructor the positivity
//! table's datum and node agreement (`classCtorOf`), the generator
//! (`ClassGen`: the shared prefix, each recursor's type, each rule), the
//! generated types checked and compared with the stream's (`classRecTyOk`),
//! and the generated rules installed (`classRuleOk`) — `genRecCheck`.
//!
//! ## The twin's deviations
//!
//! * **The operations are the core's, with `genRecCheckC`'s flushes**
//!   (`arena::inductives::rec_check`'s module note): the specification
//!   `genRecCheck` takes the checker's operations and does not flush; the
//!   cached twin `genRecCheckC` flushes (`core::flush_caches`) around the
//!   rule stage, whose inference is the core at the rule-less recursors'
//!   environment with a flush LEAVING its `inferType` (`sharedOpsRuleR`).
//!   This port runs the cached twin's sequence.
//! * **`feR` is `fe` with the rule-less recursors pushed TEMPORARILY**
//!   (`env::ifenv_push_temp`) and popped once the rules are typed —
//!   `consBlockRecsBareF`'s cons onto a copy, without the copy (task
//!   #97-P6-5's lever 4).  The one read at `feT` while they are pushed, a
//!   rule's λ-domains resolving, is "resolves at `feR` and names no pushed
//!   recursor" (`domains_resolve`).  `genRecCheck` threads the index by value
//!   and hands it back.
//! * **`recOf` is `classRecOf recCls cvGs`, specialised**; `classRead`'s
//!   `nPc` is `classNPcOf p fe₁`.
//! * **A `getD … default` out of range** reads the interned default
//!   (`.bvar 0` for a term, `target_major_default` for a class); the stage
//!   never forms such an index.

use super::block_shape;
use super::block_shape::{shape_k, shape_member_names, BlockShape, RecShape};
use super::block_rec::block_large_elim_allowed;
use super::class_read;
use super::class_read::{ClassKey, ClassRead, ClassSlot};
use super::positivity;
use super::positivity::{close_telescope, inst_pis_with, nest_occ, params_closed, NestCtorNf, NestCtx, NestKey};
use super::rec_check;
use super::rec_check::TargetMajor;
use super::field_tele::pi_binders;
use super::struct_parts;
use crate::arena::checker_base;
use crate::arena::core;
use crate::arena::core::CORE_WALK_FUEL;
use crate::arena::env;
use crate::arena::env::{IConstantInfo, IConstantVal, IFEnv};
use crate::arena::expr_ops;
use crate::arena::handle::{EIdx, LIdx, LsIdx, NIdx, ETAG_CONST};
use crate::arena::monad::{
    fail, fail_dangling_e, intern_e_bvar, intern_e_const, intern_e_forall_e, intern_e_fvar, intern_e_lam,
    intern_e_sort, view_const, AState,
};
use crate::arena::store::PersTier;
use crate::kernel::core_types;
use crate::kernel::core_types::{code_points, CheckError};
use crate::kernel::env::CheckMode;
use crate::ron::hashmap::{Dup, Eq2};

// ---------------------------------------------------------------------------
// The messages (con-leche's own, interpolation dropped)
// ---------------------------------------------------------------------------

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `a declaration at a literal's name with another shape ()`, as code points.
pub const M_LIT_SHAPE: [u32; 55] = [
    97, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 97, 116, 32, 97, 32, 108,
    105, 116, 101, 114, 97, 108, 39, 115, 32, 110, 97, 109, 101, 32, 119, 105, 116, 104, 32, 97,
    110, 111, 116, 104, 101, 114, 32, 115, 104, 97, 112, 101, 32, 40, 41,
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `generated recursor: the recursors' prefix does not have exactly one minor premise for  (official: invalid recursor)`, as code points.
pub const M_MINOR_SLOT: [u32; 115] = [
    103, 101, 110, 101, 114, 97, 116, 101, 100, 32, 114, 101, 99, 117, 114, 115, 111, 114, 58, 32,
    116, 104, 101, 32, 114, 101, 99, 117, 114, 115, 111, 114, 115, 39, 32, 112, 114, 101, 102, 105,
    120, 32, 100, 111, 101, 115, 32, 110, 111, 116, 32, 104, 97, 118, 101, 32, 101, 120, 97, 99,
    116, 108, 121, 32, 111, 110, 101, 32, 109, 105, 110, 111, 114, 32, 112, 114, 101, 109, 105,
    115, 101, 32, 102, 111, 114, 32, 32, 40, 111, 102, 102, 105, 99, 105, 97, 108, 58, 32, 105,
    110, 118, 97, 108, 105, 100, 32, 114, 101, 99, 117, 114, 115, 111, 114, 41,
];
/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `generated recursor: the inductive hypotheses of 's minor premise are not its recursive fields (official: invalid recursor)`, as code points.
pub const M_IHS: [u32; 122] = [
    103, 101, 110, 101, 114, 97, 116, 101, 100, 32, 114, 101, 99, 117, 114, 115, 111, 114, 58, 32,
    116, 104, 101, 32, 105, 110, 100, 117, 99, 116, 105, 118, 101, 32, 104, 121, 112, 111, 116,
    104, 101, 115, 101, 115, 32, 111, 102, 32, 39, 115, 32, 109, 105, 110, 111, 114, 32, 112, 114,
    101, 109, 105, 115, 101, 32, 97, 114, 101, 32, 110, 111, 116, 32, 105, 116, 115, 32, 114, 101,
    99, 117, 114, 115, 105, 118, 101, 32, 102, 105, 101, 108, 100, 115, 32, 40, 111, 102, 102, 105,
    99, 105, 97, 108, 58, 32, 105, 110, 118, 97, 108, 105, 100, 32, 114, 101, 99, 117, 114, 115,
    111, 114, 41,
];
/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `generated recursor: a recorded normal form of  is too short`, as code points.
pub const M_NF_SHORT: [u32; 59] = [
    103, 101, 110, 101, 114, 97, 116, 101, 100, 32, 114, 101, 99, 117, 114, 115, 111, 114, 58, 32,
    97, 32, 114, 101, 99, 111, 114, 100, 101, 100, 32, 110, 111, 114, 109, 97, 108, 32, 102, 111,
    114, 109, 32, 111, 102, 32, 32, 105, 115, 32, 116, 111, 111, 32, 115, 104, 111, 114, 116,
];
/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `generated recursor: field  of  does not land at its inductive hypothesis's class at every node of the positivity check (official: invalid recursor)`, as code points.
pub const M_NODES: [u32; 147] = [
    103, 101, 110, 101, 114, 97, 116, 101, 100, 32, 114, 101, 99, 117, 114, 115, 111, 114, 58, 32,
    102, 105, 101, 108, 100, 32, 32, 111, 102, 32, 32, 100, 111, 101, 115, 32, 110, 111, 116, 32,
    108, 97, 110, 100, 32, 97, 116, 32, 105, 116, 115, 32, 105, 110, 100, 117, 99, 116, 105, 118,
    101, 32, 104, 121, 112, 111, 116, 104, 101, 115, 105, 115, 39, 115, 32, 99, 108, 97, 115, 115,
    32, 97, 116, 32, 101, 118, 101, 114, 121, 32, 110, 111, 100, 101, 32, 111, 102, 32, 116, 104,
    101, 32, 112, 111, 115, 105, 116, 105, 118, 105, 116, 121, 32, 99, 104, 101, 99, 107, 32, 40,
    111, 102, 102, 105, 99, 105, 97, 108, 58, 32, 105, 110, 118, 97, 108, 105, 100, 32, 114, 101,
    99, 117, 114, 115, 111, 114, 41,
];
/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `generated recursor: field telescope`, as code points.
pub const M_FIELD_TELE: [u32; 35] = [
    103, 101, 110, 101, 114, 97, 116, 101, 100, 32, 114, 101, 99, 117, 114, 115, 111, 114, 58, 32,
    102, 105, 101, 108, 100, 32, 116, 101, 108, 101, 115, 99, 111, 112, 101,
];
/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `generated recursor: field  of  does not end in its inductive hypothesis's class (official: invalid recursor)`, as code points.
pub const M_LEAF: [u32; 108] = [
    103, 101, 110, 101, 114, 97, 116, 101, 100, 32, 114, 101, 99, 117, 114, 115, 111, 114, 58, 32,
    102, 105, 101, 108, 100, 32, 32, 111, 102, 32, 32, 100, 111, 101, 115, 32, 110, 111, 116, 32,
    101, 110, 100, 32, 105, 110, 32, 105, 116, 115, 32, 105, 110, 100, 117, 99, 116, 105, 118, 101,
    32, 104, 121, 112, 111, 116, 104, 101, 115, 105, 115, 39, 115, 32, 99, 108, 97, 115, 115, 32,
    40, 111, 102, 102, 105, 99, 105, 97, 108, 58, 32, 105, 110, 118, 97, 108, 105, 100, 32, 114,
    101, 99, 117, 114, 115, 111, 114, 41,
];
/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `generated recursor: the constructor  of a class has no entry in the positivity check's table`, as code points.
pub const M_NO_ENTRY: [u32; 92] = [
    103, 101, 110, 101, 114, 97, 116, 101, 100, 32, 114, 101, 99, 117, 114, 115, 111, 114, 58, 32,
    116, 104, 101, 32, 99, 111, 110, 115, 116, 114, 117, 99, 116, 111, 114, 32, 32, 111, 102, 32,
    97, 32, 99, 108, 97, 115, 115, 32, 104, 97, 115, 32, 110, 111, 32, 101, 110, 116, 114, 121, 32,
    105, 110, 32, 116, 104, 101, 32, 112, 111, 115, 105, 116, 105, 118, 105, 116, 121, 32, 99, 104,
    101, 99, 107, 39, 115, 32, 116, 97, 98, 108, 101,
];
/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `generated recursor: datum telescope`, as code points.
pub const M_DATUM: [u32; 35] = [
    103, 101, 110, 101, 114, 97, 116, 101, 100, 32, 114, 101, 99, 117, 114, 115, 111, 114, 58, 32,
    100, 97, 116, 117, 109, 32, 116, 101, 108, 101, 115, 99, 111, 112, 101,
];
/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `generated recursor: constructor parameter telescope`, as code points.
pub const M_CTOR_PARAMS: [u32; 51] = [
    103, 101, 110, 101, 114, 97, 116, 101, 100, 32, 114, 101, 99, 117, 114, 115, 111, 114, 58, 32,
    99, 111, 110, 115, 116, 114, 117, 99, 116, 111, 114, 32, 112, 97, 114, 97, 109, 101, 116, 101,
    114, 32, 116, 101, 108, 101, 115, 99, 111, 112, 101,
];
/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `generated recursor: a class's former vanished`, as code points.
pub const M_FORMER: [u32; 45] = [
    103, 101, 110, 101, 114, 97, 116, 101, 100, 32, 114, 101, 99, 117, 114, 115, 111, 114, 58, 32,
    97, 32, 99, 108, 97, 115, 115, 39, 115, 32, 102, 111, 114, 109, 101, 114, 32, 118, 97, 110,
    105, 115, 104, 101, 100,
];
/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `duplicate declaration`, as code points.
pub const M_DUP_DECL: [u32; 21] = [
    100, 117, 112, 108, 105, 99, 97, 116, 101, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111,
    110,
];
/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `duplicate universe parameters in`, as code points.
pub const M_DUP_UNIV: [u32; 32] = [
    100, 117, 112, 108, 105, 99, 97, 116, 101, 32, 117, 110, 105, 118, 101, 114, 115, 101, 32, 112,
    97, 114, 97, 109, 101, 116, 101, 114, 115, 32, 105, 110,
];
/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `generated recursor: loose bound variable in type of`, as code points.
pub const M_LOOSE: [u32; 51] = [
    103, 101, 110, 101, 114, 97, 116, 101, 100, 32, 114, 101, 99, 117, 114, 115, 111, 114, 58, 32,
    108, 111, 111, 115, 101, 32, 98, 111, 117, 110, 100, 32, 118, 97, 114, 105, 97, 98, 108, 101,
    32, 105, 110, 32, 116, 121, 112, 101, 32, 111, 102,
];
/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `generated recursor: free variable in type of`, as code points.
pub const M_FVAR: [u32; 44] = [
    103, 101, 110, 101, 114, 97, 116, 101, 100, 32, 114, 101, 99, 117, 114, 115, 111, 114, 58, 32,
    102, 114, 101, 101, 32, 118, 97, 114, 105, 97, 98, 108, 101, 32, 105, 110, 32, 116, 121, 112,
    101, 32, 111, 102,
];
/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `undeclared universe parameter in type of`, as code points.
pub const M_UNDECL: [u32; 40] = [
    117, 110, 100, 101, 99, 108, 97, 114, 101, 100, 32, 117, 110, 105, 118, 101, 114, 115, 101, 32,
    112, 97, 114, 97, 109, 101, 116, 101, 114, 32, 105, 110, 32, 116, 121, 112, 101, 32, 111, 102,
];
/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `generated recursor: the recursor record's member is not its class's`, as code points.
pub const M_REC_MEMBER: [u32; 67] = [
    103, 101, 110, 101, 114, 97, 116, 101, 100, 32, 114, 101, 99, 117, 114, 115, 111, 114, 58, 32,
    116, 104, 101, 32, 114, 101, 99, 117, 114, 115, 111, 114, 32, 114, 101, 99, 111, 114, 100, 39,
    115, 32, 109, 101, 109, 98, 101, 114, 32, 105, 115, 32, 110, 111, 116, 32, 105, 116, 115, 32,
    99, 108, 97, 115, 115, 39, 115,
];
/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `generated recursor: the recursor record's rule prefix or major index is not the generated one`, as code points.
pub const M_REC_PREFIX: [u32; 93] = [
    103, 101, 110, 101, 114, 97, 116, 101, 100, 32, 114, 101, 99, 117, 114, 115, 111, 114, 58, 32,
    116, 104, 101, 32, 114, 101, 99, 117, 114, 115, 111, 114, 32, 114, 101, 99, 111, 114, 100, 39,
    115, 32, 114, 117, 108, 101, 32, 112, 114, 101, 102, 105, 120, 32, 111, 114, 32, 109, 97, 106,
    111, 114, 32, 105, 110, 100, 101, 120, 32, 105, 115, 32, 110, 111, 116, 32, 116, 104, 101, 32,
    103, 101, 110, 101, 114, 97, 116, 101, 100, 32, 111, 110, 101,
];
/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `generated recursor: recursor type`, as code points.
pub const M_REC_TY: [u32; 33] = [
    103, 101, 110, 101, 114, 97, 116, 101, 100, 32, 114, 101, 99, 117, 114, 115, 111, 114, 58, 32,
    114, 101, 99, 117, 114, 115, 111, 114, 32, 116, 121, 112, 101,
];
/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `generated recursor: the type of  is not the generated one (official: invalid recursor)`, as code points.
pub const M_REC_DEFEQ: [u32; 86] = [
    103, 101, 110, 101, 114, 97, 116, 101, 100, 32, 114, 101, 99, 117, 114, 115, 111, 114, 58, 32,
    116, 104, 101, 32, 116, 121, 112, 101, 32, 111, 102, 32, 32, 105, 115, 32, 110, 111, 116, 32,
    116, 104, 101, 32, 103, 101, 110, 101, 114, 97, 116, 101, 100, 32, 111, 110, 101, 32, 40, 111,
    102, 102, 105, 99, 105, 97, 108, 58, 32, 105, 110, 118, 97, 108, 105, 100, 32, 114, 101, 99,
    117, 114, 115, 111, 114, 41,
];
/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `generated recursor: recursor list`, as code points.
pub const M_REC_LIST: [u32; 33] = [
    103, 101, 110, 101, 114, 97, 116, 101, 100, 32, 114, 101, 99, 117, 114, 115, 111, 114, 58, 32,
    114, 101, 99, 117, 114, 115, 111, 114, 32, 108, 105, 115, 116,
];
/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `generated recursor: a rule of  is not closed`, as code points.
pub const M_RULE_OPEN: [u32; 44] = [
    103, 101, 110, 101, 114, 97, 116, 101, 100, 32, 114, 101, 99, 117, 114, 115, 111, 114, 58, 32,
    97, 32, 114, 117, 108, 101, 32, 111, 102, 32, 32, 105, 115, 32, 110, 111, 116, 32, 99, 108,
    111, 115, 101, 100,
];
/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `generated recursor: a rule of  names an undeclared universe parameter`, as code points.
pub const M_RULE_ULP: [u32; 69] = [
    103, 101, 110, 101, 114, 97, 116, 101, 100, 32, 114, 101, 99, 117, 114, 115, 111, 114, 58, 32,
    97, 32, 114, 117, 108, 101, 32, 111, 102, 32, 32, 110, 97, 109, 101, 115, 32, 97, 110, 32, 117,
    110, 100, 101, 99, 108, 97, 114, 101, 100, 32, 117, 110, 105, 118, 101, 114, 115, 101, 32, 112,
    97, 114, 97, 109, 101, 116, 101, 114,
];
/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `generated recursor: a rule of  is not a λ-telescope over the recursor's prefix and the constructor's fields`, as code points.
pub const M_RULE_TELE: [u32; 107] = [
    103, 101, 110, 101, 114, 97, 116, 101, 100, 32, 114, 101, 99, 117, 114, 115, 111, 114, 58, 32,
    97, 32, 114, 117, 108, 101, 32, 111, 102, 32, 32, 105, 115, 32, 110, 111, 116, 32, 97, 32, 955,
    45, 116, 101, 108, 101, 115, 99, 111, 112, 101, 32, 111, 118, 101, 114, 32, 116, 104, 101, 32,
    114, 101, 99, 117, 114, 115, 111, 114, 39, 115, 32, 112, 114, 101, 102, 105, 120, 32, 97, 110,
    100, 32, 116, 104, 101, 32, 99, 111, 110, 115, 116, 114, 117, 99, 116, 111, 114, 39, 115, 32,
    102, 105, 101, 108, 100, 115,
];
/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `generated recursor: the rule of  calls a class whose recursor the stream omits (official: unknown constant)`, as code points.
pub const M_RULE_OMIT: [u32; 107] = [
    103, 101, 110, 101, 114, 97, 116, 101, 100, 32, 114, 101, 99, 117, 114, 115, 111, 114, 58, 32,
    116, 104, 101, 32, 114, 117, 108, 101, 32, 111, 102, 32, 32, 99, 97, 108, 108, 115, 32, 97, 32,
    99, 108, 97, 115, 115, 32, 119, 104, 111, 115, 101, 32, 114, 101, 99, 117, 114, 115, 111, 114,
    32, 116, 104, 101, 32, 115, 116, 114, 101, 97, 109, 32, 111, 109, 105, 116, 115, 32, 40, 111,
    102, 102, 105, 99, 105, 97, 108, 58, 32, 117, 110, 107, 110, 111, 119, 110, 32, 99, 111, 110,
    115, 116, 97, 110, 116, 41,
];
/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `generated recursor: the recursor family is not of the generated shape (official: invalid recursor)`, as code points.
pub const M_SHAPE: [u32; 98] = [
    103, 101, 110, 101, 114, 97, 116, 101, 100, 32, 114, 101, 99, 117, 114, 115, 111, 114, 58, 32,
    116, 104, 101, 32, 114, 101, 99, 117, 114, 115, 111, 114, 32, 102, 97, 109, 105, 108, 121, 32,
    105, 115, 32, 110, 111, 116, 32, 111, 102, 32, 116, 104, 101, 32, 103, 101, 110, 101, 114, 97,
    116, 101, 100, 32, 115, 104, 97, 112, 101, 32, 40, 111, 102, 102, 105, 99, 105, 97, 108, 58,
    32, 105, 110, 118, 97, 108, 105, 100, 32, 114, 101, 99, 117, 114, 115, 111, 114, 41,
];
/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `generated recursor: the recursor family does not have exactly one class per member (official: invalid recursor)`, as code points.
pub const M_ONE_CLASS: [u32; 111] = [
    103, 101, 110, 101, 114, 97, 116, 101, 100, 32, 114, 101, 99, 117, 114, 115, 111, 114, 58, 32,
    116, 104, 101, 32, 114, 101, 99, 117, 114, 115, 111, 114, 32, 102, 97, 109, 105, 108, 121, 32,
    100, 111, 101, 115, 32, 110, 111, 116, 32, 104, 97, 118, 101, 32, 101, 120, 97, 99, 116, 108,
    121, 32, 111, 110, 101, 32, 99, 108, 97, 115, 115, 32, 112, 101, 114, 32, 109, 101, 109, 98,
    101, 114, 32, 40, 111, 102, 102, 105, 99, 105, 97, 108, 58, 32, 105, 110, 118, 97, 108, 105,
    100, 32, 114, 101, 99, 117, 114, 115, 111, 114, 41,
];
/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `generated recursor: the block declares no family`, as code points.
pub const M_NO_FAMILY: [u32; 48] = [
    103, 101, 110, 101, 114, 97, 116, 101, 100, 32, 114, 101, 99, 117, 114, 115, 111, 114, 58, 32,
    116, 104, 101, 32, 98, 108, 111, 99, 107, 32, 100, 101, 99, 108, 97, 114, 101, 115, 32, 110,
    111, 32, 102, 97, 109, 105, 108, 121,
];
/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `generated recursor: large eliminator on a block whose sort may be Prop (official: elim_only_at_universe_zero)`, as code points.
pub const M_ELIM: [u32; 109] = [
    103, 101, 110, 101, 114, 97, 116, 101, 100, 32, 114, 101, 99, 117, 114, 115, 111, 114, 58, 32,
    108, 97, 114, 103, 101, 32, 101, 108, 105, 109, 105, 110, 97, 116, 111, 114, 32, 111, 110, 32,
    97, 32, 98, 108, 111, 99, 107, 32, 119, 104, 111, 115, 101, 32, 115, 111, 114, 116, 32, 109,
    97, 121, 32, 98, 101, 32, 80, 114, 111, 112, 32, 40, 111, 102, 102, 105, 99, 105, 97, 108, 58,
    32, 101, 108, 105, 109, 95, 111, 110, 108, 121, 95, 97, 116, 95, 117, 110, 105, 118, 101, 114,
    115, 101, 95, 122, 101, 114, 111, 41,
];
/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `generated recursor: the recursors' prefix has a minor premise for no constructor of a class (official: invalid recursor)`, as code points.
pub const M_MINOR_COUNT: [u32; 120] = [
    103, 101, 110, 101, 114, 97, 116, 101, 100, 32, 114, 101, 99, 117, 114, 115, 111, 114, 58, 32,
    116, 104, 101, 32, 114, 101, 99, 117, 114, 115, 111, 114, 115, 39, 32, 112, 114, 101, 102, 105,
    120, 32, 104, 97, 115, 32, 97, 32, 109, 105, 110, 111, 114, 32, 112, 114, 101, 109, 105, 115,
    101, 32, 102, 111, 114, 32, 110, 111, 32, 99, 111, 110, 115, 116, 114, 117, 99, 116, 111, 114,
    32, 111, 102, 32, 97, 32, 99, 108, 97, 115, 115, 32, 40, 111, 102, 102, 105, 99, 105, 97, 108,
    58, 32, 105, 110, 118, 97, 108, 105, 100, 32, 114, 101, 99, 117, 114, 115, 111, 114, 41,
];
/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `generated recursor: recursor prefix`, as code points.
pub const M_PREFIX: [u32; 35] = [
    103, 101, 110, 101, 114, 97, 116, 101, 100, 32, 114, 101, 99, 117, 114, 115, 111, 114, 58, 32,
    114, 101, 99, 117, 114, 115, 111, 114, 32, 112, 114, 101, 102, 105, 120,
];
/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `target rec: the major's parameters mention more than the recursor's parameters`, as code points.
pub const M_MAJOR_PARAMS: [u32; 78] = [
    116, 97, 114, 103, 101, 116, 32, 114, 101, 99, 58, 32, 116, 104, 101, 32, 109, 97, 106, 111,
    114, 39, 115, 32, 112, 97, 114, 97, 109, 101, 116, 101, 114, 115, 32, 109, 101, 110, 116, 105,
    111, 110, 32, 109, 111, 114, 101, 32, 116, 104, 97, 110, 32, 116, 104, 101, 32, 114, 101, 99,
    117, 114, 115, 111, 114, 39, 115, 32, 112, 97, 114, 97, 109, 101, 116, 101, 114, 115,
];

// ---------------------------------------------------------------------------
// The generator
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/Inductives/GenRec.lean:63-69 ClassField
/// Lean twin: `proof/ConRon/Arena/Inductives/GenRec.lean:56-62 ClassField` — a field of a
/// class's constructor, as the generator reads it: ordinary, or recursive at
/// class `cls` with a telescope of `tele` binders.
pub enum ClassField {
    Ordinary,
    Recursive(u64, u64),
}

/// con-leche: ConLeche/Kernel/Inductives/GenRec.lean:63-69 ClassField
/// The copy.
pub fn class_field_dup(k: &ClassField) -> ClassField {
    match k {
        ClassField::Ordinary => ClassField::Ordinary,
        ClassField::Recursive(c, t) => ClassField::Recursive(*c, *t),
    }
}

/// con-leche: none — a `List ClassField` copy; Lean shares the list
/// Lean twin: `proof/ConRon/Arena/Inductives/GenRec.lean:56-62 ClassField`.
pub fn class_fields_dup(ks: &Vec<ClassField>, i: usize, out: Vec<ClassField>) -> Vec<ClassField> {
    if i >= ks.len() {
        out
    } else {
        let mut o: Vec<ClassField> = out;
        o.push(class_field_dup(&ks[i]));
        class_fields_dup(ks, i + 1, o)
    }
}

/// con-leche: ConLeche/Kernel/Inductives/GenRec.lean:71-84 ClassCtor
/// Lean twin: `proof/ConRon/Arena/Inductives/GenRec.lean:64-74 ClassCtor` — a class's
/// constructor as the generator reads it: its DECLARED type at the class's
/// levels and parameters `ty_d`, the datum's WALKED telescope `ty_n`, the
/// field count and the fields' kinds.
pub struct ClassCtor {
    pub cv: IConstantVal,
    pub n_f: u64,
    pub kinds: Vec<ClassField>,
    pub ty_d: EIdx,
    pub ty_n: EIdx,
}

/// con-leche: ConLeche/Kernel/Inductives/GenRec.lean:71-84 ClassCtor
/// The record copy.
pub fn class_ctor_dup(x: &ClassCtor) -> ClassCtor {
    ClassCtor {
        cv: env::i_constant_val_dup(&x.cv),
        n_f: x.n_f,
        kinds: class_fields_dup(&x.kinds, 0, Vec::new()),
        ty_d: x.ty_d.dup2(),
        ty_n: x.ty_n.dup2(),
    }
}

/// con-leche: ConLeche/Cached/ExprOpsC.lean:2120-2122 closeLamsGoC
/// con-leche: ConLeche/Kernel/Inductives/GenRec.lean:86-89 closeLams
/// Lean twin: `proof/ConRon/Arena/Inductives/GenRec.lean:76-85 closeLamsGo` —
/// `close_telescope_go` with `λ` binders: each domain and the body
/// abstracted once over the `k` (= `j`) binders outside it.
pub fn close_lams_go(
    pers: &PersTier,
    st: &mut AState,
    bs: &Vec<EIdx>,
    j: usize,
    i: u64,
    k: u64,
    body: &EIdx,
) -> Result<EIdx, CheckError> {
    if j >= bs.len() {
        expr_ops::abstract_range_fast(pers, st, CORE_WALK_FUEL, body, i, k, 0)
    } else {
        match expr_ops::abstract_range_fast(pers, st, CORE_WALK_FUEL, &bs[j], i, k, 0) {
            Err(e) => Err(e),
            Ok(dom) => match close_lams_go(pers, st, bs, j + 1, i, k + 1, body) {
                Err(e) => Err(e),
                Ok(inner) => intern_e_lam(pers, st, dom, inner),
            },
        }
    }
}

/// con-leche: ConLeche/Cached/ExprOpsC.lean:2125-2126 closeLamsC
/// con-leche: ConLeche/Kernel/Inductives/GenRec.lean:86-89 closeLams
/// Lean twin: `proof/ConRon/Arena/Inductives/GenRec.lean:87-91 closeLams` — close a
/// telescope of `λ`s opened at `i ..< i + bs.len()` (`close_lams_go` from
/// the outermost binder).
pub fn close_lams(
    pers: &PersTier,
    st: &mut AState,
    bs: &Vec<EIdx>,
    i: u64,
    body: &EIdx,
) -> Result<EIdx, CheckError> {
    close_lams_go(pers, st, bs, 0, i, 0, body)
}

/// con-leche: ConLeche/Kernel/Inductives/GenRec.lean:91-103 ClassGen
/// Lean twin: `proof/ConRon/Arena/Inductives/GenRec.lean:93-106 ClassGen` — what
/// generation reads: the block, the classes, the layout, the constructors,
/// the elimination level, the generated prefix.
pub struct ClassGen {
    pub n_p: u64,
    pub params: Vec<EIdx>,
    pub cls: Vec<TargetMajor>,
    pub former_tys: Vec<EIdx>,
    pub slots: Vec<ClassSlot>,
    pub ctors: Vec<Vec<ClassCtor>>,
    pub elim: LIdx,
    pub pre: Vec<EIdx>,
}

/// con-leche: none — `xs.getD i default` on a term list, the default interned (`.bvar 0`)
/// Lean twin: `List.getD … default`.
pub fn expr_get_d(pers: &PersTier, st: &mut AState, xs: &Vec<EIdx>, i: u64) -> Result<EIdx, CheckError> {
    if i < xs.len() as u64 {
        Ok(xs[i as usize].dup2())
    } else {
        intern_e_bvar(pers, st, 0)
    }
}

/// con-leche: ConLeche/Kernel/Inductives/GenRec.lean:105-107 classBinder
/// Lean twin: `proof/ConRon/Arena/Inductives/GenRec.lean:116-119 classBinder` — the binders
/// of opened variables (their types), `xs.map classBinder`.
pub fn class_binders(
    pers: &PersTier,
    st: &AState,
    xs: &Vec<EIdx>,
    i: usize,
    out: Vec<EIdx>,
) -> Result<Vec<EIdx>, CheckError> {
    if i >= xs.len() {
        Ok(out)
    } else {
        match expr_ops::fvar_type_d(pers, st, &xs[i]) {
            Err(e) => Err(e),
            Ok(t) => {
                let mut o: Vec<EIdx> = out;
                o.push(t);
                class_binders(pers, st, xs, i + 1, o)
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/GenRec.lean:109-110 ClassGen.binder
/// Lean twin: `proof/ConRon/Arena/Inductives/GenRec.lean:121-124 ClassGen.binder` — the
/// generated binders of opened variables, `xs.map g.binder`, appended to `out`.
pub fn gen_binders(
    pers: &PersTier,
    st: &AState,
    g: &ClassGen,
    xs: &Vec<EIdx>,
    i: usize,
    out: Vec<EIdx>,
) -> Result<Vec<EIdx>, CheckError> {
    if i >= xs.len() {
        Ok(out)
    } else {
        match expr_ops::fvar_type_d(pers, st, &xs[i]) {
            Err(e) => Err(e),
            Ok(t) => {
                let mut o: Vec<EIdx> = out;
                o.push(t);
                gen_binders(pers, st, g, xs, i + 1, o)
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/GenRec.lean:112-113 ClassGen.slotVar
/// Lean twin: `proof/ConRon/Arena/Inductives/GenRec.lean:126-130 ClassGen.slotVar` — the
/// prefix variable of slot `s`.
pub fn slot_var(pers: &PersTier, st: &mut AState, g: &ClassGen, s: u64) -> Result<EIdx, CheckError> {
    match positivity::sort_zero(pers, st) {
        Err(e) => Err(e),
        Ok(z) => intern_e_fvar(pers, st, g.n_p + s, z),
    }
}

/// con-leche: ConLeche/Kernel/Inductives/GenRec.lean:115-117 ClassGen.motVar
/// Lean twin: `proof/ConRon/Arena/Inductives/GenRec.lean:132-135 ClassGen.motVar` — class
/// `c`'s motive variable.
pub fn mot_var(pers: &PersTier, st: &mut AState, g: &ClassGen, c: u64) -> Result<EIdx, CheckError> {
    let s: u64 = match class_read::motive_slot(&g.slots, c) {
        Some(s) => s,
        None => 0,
    };
    slot_var(pers, st, g, s)
}

/// con-leche: none — `xs ++ ys` on term lists
/// Lean twin: `List.append`.
pub fn eidx_append(xs: &Vec<EIdx>, ys: &Vec<EIdx>) -> Vec<EIdx> {
    core::append_eidx(env::eidx_vec_dup(xs), ys)
}

/// con-leche: ConLeche/Kernel/Inductives/GenRec.lean:119-124 ClassGen.major
/// con-leche: ConLeche/Cached/IndRec.lean:68-74 _root_.ConLeche.ClassGen.majorC
/// Lean twin: `proof/ConRon/Arena/Inductives/GenRec.lean:137-151 ClassGen.major` — class
/// `c`'s index telescope opened at `d`, and its major domain.
pub fn gen_major(
    pers: &PersTier,
    st: &mut AState,
    g: &ClassGen,
    c: u64,
    d: u64,
) -> Result<Option<(Vec<EIdx>, EIdx)>, CheckError> {
    match rec_check::target_major_at(pers, st, &g.cls, c) {
        Err(e) => Err(e),
        Ok(ci) => match expr_get_d(pers, st, &g.former_tys, c) {
            Err(e) => Err(e),
            Ok(fty) => match inst_pis_with(pers, st, &ci.ds, 0, &fty) {
                Err(e) => Err(e),
                Ok(None) => Ok(None),
                Ok(Some(ty)) => match core::open_pis_at_fvars_f(pers, st, ci.n_idx, &ty, d) {
                    Err(e) => Err(e),
                    Ok(None) => Ok(None),
                    Ok(Some((ifs, _))) => match intern_e_const(pers, st, ci.ind.dup2(), ci.lvls.dup2()) {
                        Err(e) => Err(e),
                        Ok(hd) => {
                            let args: Vec<EIdx> = eidx_append(&ci.ds, &ifs);
                            match expr_ops::mk_app_n(pers, st, &hd, &args) {
                                Err(e) => Err(e),
                                Ok(maj) => Ok(Some((ifs, maj))),
                            }
                        }
                    },
                },
            },
        },
    }
}

/// con-leche: ConLeche/Kernel/Inductives/GenRec.lean:126-129 ClassGen.motiveTy
/// con-leche: ConLeche/Cached/IndRec.lean:76-79 _root_.ConLeche.ClassGen.motiveTyC
/// Lean twin: `proof/ConRon/Arena/Inductives/GenRec.lean:153-164 ClassGen.motiveTy` — class
/// `c`'s motive type at depth `d`: `∀ ı⃗ (t : I D⃗ ı⃗), Sort ℓ`.
pub fn motive_ty(pers: &PersTier, st: &mut AState, g: &ClassGen, c: u64, d: u64) -> Result<Option<EIdx>, CheckError> {
    match gen_major(pers, st, g, c, d) {
        Err(e) => Err(e),
        Ok(None) => Ok(None),
        Ok(Some((ifs, maj))) => match intern_e_sort(pers, st, g.elim.dup2()) {
            Err(e) => Err(e),
            Ok(srt) => match intern_e_forall_e(pers, st, maj, srt) {
                Err(e) => Err(e),
                Ok(body) => match class_binders(pers, st, &ifs, 0, Vec::new()) {
                    Err(e) => Err(e),
                    Ok(bs) => match close_telescope(pers, st, &bs, d, &body) {
                        Err(e) => Err(e),
                        Ok(r) => Ok(Some(r)),
                    },
                },
            },
        },
    }
}

/// con-leche: ConLeche/Kernel/Inductives/GenRec.lean:131-137 ClassGen.ihParts
/// con-leche: ConLeche/Cached/IndRec.lean:81-85 _root_.ConLeche.ClassGen.ihPartsC
/// Lean twin: `proof/ConRon/Arena/Inductives/GenRec.lean:166-179 ClassGen.ihParts` — the
/// inductive hypothesis of a recursive field whose WALKED type is `w`
/// (landing at class `t`), opened at `d`: its telescope and its index
/// arguments.
#[allow(clippy::too_many_arguments)]
pub fn ih_parts(
    pers: &PersTier,
    st: &mut AState,
    g: &ClassGen,
    t: u64,
    tele: u64,
    w: &EIdx,
    d: u64,
) -> Result<Option<(Vec<EIdx>, Vec<EIdx>)>, CheckError> {
    match core::open_pis_at_fvars_f(pers, st, tele, w, d) {
        Err(e) => Err(e),
        Ok(None) => Ok(None),
        Ok(Some((xs, leaf))) => {
            // `(g.cls.getD t default).nPc`: the default class has none
            let n_pc: u64 = if t < g.cls.len() as u64 { g.cls[t as usize].n_pc } else { 0 };
            match expr_ops::get_app_args(pers, st, CORE_WALK_FUEL, &leaf) {
                Err(e) => Err(e),
                Ok(args) => Ok(Some((xs, core::drop_eidx_n(&args, n_pc)))),
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/GenRec.lean:139-159 ClassGen.minorTy
/// con-leche: ConLeche/Cached/IndRec.lean:87-106 _root_.ConLeche.ClassGen.minorTyC
/// Lean twin: `(List.range x.nF).filterMap …` — the recursive fields `(i, t,
/// tele)` of a constructor, in field order.
pub fn rec_fields(ks: &Vec<ClassField>, n_f: u64, i: u64, out: Vec<(u64, u64, u64)>) -> Vec<(u64, u64, u64)> {
    if i >= n_f {
        out
    } else if i < ks.len() as u64 {
        match &ks[i as usize] {
            ClassField::Recursive(t, tele) => {
                let mut o: Vec<(u64, u64, u64)> = out;
                o.push((i, *t, *tele));
                rec_fields(ks, n_f, i + 1, o)
            }
            ClassField::Ordinary => rec_fields(ks, n_f, i + 1, out),
        }
    } else {
        rec_fields(ks, n_f, i + 1, out)
    }
}

/// con-leche: ConLeche/Kernel/Inductives/GenRec.lean:139-159 ClassGen.minorTy
/// con-leche: ConLeche/Cached/IndRec.lean:87-106 _root_.ConLeche.ClassGen.minorTyC
/// Lean twin: `proof/ConRon/Arena/Inductives/GenRec.lean:181-229 ClassGen.minorTy` — the
/// minor premise's inductive hypotheses from recursive field `l` on: per
/// field `f` (walked type `w`), `∀ a⃗, motive_t e⃗ (f a⃗)` at depth `d + nF + l`.
#[allow(clippy::too_many_arguments)]
pub fn minor_ihs(
    pers: &PersTier,
    st: &mut AState,
    g: &ClassGen,
    x: &ClassCtor,
    d: u64,
    fvs: &Vec<EIdx>,
    ws: &Vec<EIdx>,
    recs: &Vec<(u64, u64, u64)>,
    l: usize,
    out: Vec<EIdx>,
) -> Result<Option<Vec<EIdx>>, CheckError> {
    if l >= recs.len() {
        Ok(Some(out))
    } else {
        let i: u64 = recs[l].0;
        let t: u64 = recs[l].1;
        let tele: u64 = recs[l].2;
        let e: u64 = d + x.n_f + (l as u64);
        match expr_get_d(pers, st, ws, i) {
            Err(er) => Err(er),
            Ok(w) => match ih_parts(pers, st, g, t, tele, &w, e) {
                Err(er) => Err(er),
                Ok(None) => Ok(None),
                Ok(Some((xs, idx))) => match expr_get_d(pers, st, fvs, i) {
                    Err(er) => Err(er),
                    Ok(f) => match expr_ops::mk_app_n(pers, st, &f, &xs) {
                        Err(er) => Err(er),
                        Ok(fx) => match mot_var(pers, st, g, t) {
                            Err(er) => Err(er),
                            Ok(mt) => {
                                let mut args: Vec<EIdx> = idx;
                                args.push(fx);
                                match expr_ops::mk_app_n(pers, st, &mt, &args) {
                                    Err(er) => Err(er),
                                    Ok(body) => match gen_binders(pers, st, g, &xs, 0, Vec::new()) {
                                        Err(er) => Err(er),
                                        Ok(bs) => match close_telescope(pers, st, &bs, e, &body) {
                                            Err(er) => Err(er),
                                            Ok(ih) => {
                                                let mut o: Vec<EIdx> = out;
                                                o.push(ih);
                                                minor_ihs(pers, st, g, x, d, fvs, ws, recs, l + 1, o)
                                            }
                                        },
                                    },
                                }
                            }
                        },
                    },
                },
            },
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/GenRec.lean:139-159 ClassGen.minorTy
/// con-leche: ConLeche/Cached/IndRec.lean:87-106 _root_.ConLeche.ClassGen.minorTyC
/// Lean twin: `proof/ConRon/Arena/Inductives/GenRec.lean:181-229 ClassGen.minorTy` —
/// constructor `x`'s minor premise type at depth `d`, of class `c`: its
/// declared fields, then per recursive field its inductive hypothesis, over
/// the motive at the declared result indices and the constructor applied.
pub fn minor_ty(
    pers: &PersTier,
    st: &mut AState,
    g: &ClassGen,
    c: u64,
    x: &ClassCtor,
    d: u64,
) -> Result<Option<EIdx>, CheckError> {
    match rec_check::target_major_at(pers, st, &g.cls, c) {
        Err(e) => Err(e),
        Ok(ci) => match core::open_pis_at_fvars_f(pers, st, x.n_f, &x.ty_d, d) {
            Err(e) => Err(e),
            Ok(None) => Ok(None),
            Ok(Some((fvs, res))) => match rec_check::target_pi_doms_with(pers, st, &fvs, 0, &x.ty_n, Vec::new()) {
                Err(e) => Err(e),
                Ok(None) => Ok(None),
                Ok(Some(ws)) => {
                    let recs: Vec<(u64, u64, u64)> = rec_fields(&x.kinds, x.n_f, 0, Vec::new());
                    match minor_ihs(pers, st, g, x, d, &fvs, &ws, &recs, 0, Vec::new()) {
                        Err(e) => Err(e),
                        Ok(None) => Ok(None),
                        Ok(Some(ihs)) => minor_ty_concl(pers, st, g, c, x, d, &ci, &fvs, &res, ihs),
                    }
                }
            },
        },
    }
}

/// con-leche: ConLeche/Kernel/Inductives/GenRec.lean:139-159 ClassGen.minorTy
/// con-leche: ConLeche/Cached/IndRec.lean:87-106 _root_.ConLeche.ClassGen.minorTyC
/// Lean twin: `proof/ConRon/Arena/Inductives/GenRec.lean:181-229 ClassGen.minorTy` — the
/// conclusion `motive_c (res.args.drop nPc) (C ds fvs)` and the closed
/// telescope.
#[allow(clippy::too_many_arguments)]
pub fn minor_ty_concl(
    pers: &PersTier,
    st: &mut AState,
    g: &ClassGen,
    c: u64,
    x: &ClassCtor,
    d: u64,
    ci: &TargetMajor,
    fvs: &Vec<EIdx>,
    res: &EIdx,
    ihs: Vec<EIdx>,
) -> Result<Option<EIdx>, CheckError> {
    match expr_ops::get_app_args(pers, st, CORE_WALK_FUEL, res) {
        Err(e) => Err(e),
        Ok(ra) => match intern_e_const(pers, st, x.cv.name.dup2(), ci.lvls.dup2()) {
            Err(e) => Err(e),
            Ok(cc) => {
                let cargs: Vec<EIdx> = eidx_append(&ci.ds, fvs);
                match expr_ops::mk_app_n(pers, st, &cc, &cargs) {
                    Err(e) => Err(e),
                    Ok(capp) => match mot_var(pers, st, g, c) {
                        Err(e) => Err(e),
                        Ok(mc) => {
                            let mut args: Vec<EIdx> = core::drop_eidx_n(&ra, ci.n_pc);
                            args.push(capp);
                            match expr_ops::mk_app_n(pers, st, &mc, &args) {
                                Err(e) => Err(e),
                                Ok(concl) => match gen_binders(pers, st, g, fvs, 0, Vec::new()) {
                                    Err(e) => Err(e),
                                    Ok(fbs) => {
                                        let bs: Vec<EIdx> = expr_ops::binder_copy_from(&ihs, 0, fbs);
                                        match close_telescope(pers, st, &bs, d, &concl) {
                                            Err(e) => Err(e),
                                            Ok(r) => Ok(Some(r)),
                                        }
                                    }
                                },
                            }
                        }
                    },
                }
            }
        },
    }
}

/// con-leche: ConLeche/Kernel/Inductives/GenRec.lean:161-174 ClassGen.prefixBinders
/// con-leche: ConLeche/Cached/IndRec.lean:108-120 _root_.ConLeche.ClassGen.prefixBindersC
/// Lean twin: `((List.range s).filter (motive at ·)).length` — the motives
/// before slot `s`.
pub fn motives_before(slots: &Vec<ClassSlot>, s: usize, i: usize, acc: u64) -> u64 {
    if i >= s || i >= slots.len() {
        acc
    } else if class_read::is_motive(&slots[i]) {
        motives_before(slots, s, i + 1, acc + 1)
    } else {
        motives_before(slots, s, i + 1, acc)
    }
}

/// con-leche: ConLeche/Kernel/Inductives/GenRec.lean:161-174 ClassGen.prefixBinders
/// con-leche: ConLeche/Cached/IndRec.lean:108-120 _root_.ConLeche.ClassGen.prefixBindersC
/// Lean twin: `(g.ctors.getD c []).find? (·.cv.name == C)`.
pub fn find_class_ctor(g: &ClassGen, c: u64, cn: &NIdx) -> Option<ClassCtor> {
    if c < g.ctors.len() as u64 {
        find_class_ctor_in(&g.ctors[c as usize], cn, 0)
    } else {
        None
    }
}

/// con-leche: ConLeche/Kernel/Inductives/GenRec.lean:161-174 ClassGen.prefixBinders
/// con-leche: ConLeche/Cached/IndRec.lean:108-120 _root_.ConLeche.ClassGen.prefixBindersC
/// Lean twin: the `find?`'s index recursion.
pub fn find_class_ctor_in(xs: &Vec<ClassCtor>, cn: &NIdx, i: usize) -> Option<ClassCtor> {
    if i >= xs.len() {
        None
    } else if xs[i].cv.name.eq2(cn) {
        Some(class_ctor_dup(&xs[i]))
    } else {
        find_class_ctor_in(xs, cn, i + 1)
    }
}

/// con-leche: ConLeche/Kernel/Inductives/GenRec.lean:161-174 ClassGen.prefixBinders
/// con-leche: ConLeche/Cached/IndRec.lean:108-120 _root_.ConLeche.ClassGen.prefixBindersC
/// Lean twin: `proof/ConRon/Arena/Inductives/GenRec.lean:231-261 ClassGen.prefixBinders` —
/// slot `s`'s binder type at depth `nP + s`: a motive's type (its class the
/// count of motives before it), or the minor premise of its constructor.
pub fn slot_binder(pers: &PersTier, st: &mut AState, g: &ClassGen, s: usize) -> Result<Option<EIdx>, CheckError> {
    let d: u64 = g.n_p + (s as u64);
    match &g.slots[s] {
        ClassSlot::Motive(_) => motive_ty(pers, st, g, motives_before(&g.slots, s, 0, 0), d),
        ClassSlot::Minor(c, cn, _) => match find_class_ctor(g, *c, cn) {
            None => Ok(None),
            Some(x) => minor_ty(pers, st, g, *c, &x, d),
        },
    }
}

/// con-leche: ConLeche/Kernel/Inductives/GenRec.lean:161-174 ClassGen.prefixBinders
/// con-leche: ConLeche/Cached/IndRec.lean:108-120 _root_.ConLeche.ClassGen.prefixBindersC
/// Lean twin: `proof/ConRon/Arena/Inductives/GenRec.lean:231-261 ClassGen.prefixBinders` —
/// the slot binders from `s` on (each at depth `nP + s`).
pub fn slot_binders(
    pers: &PersTier,
    st: &mut AState,
    g: &ClassGen,
    s: usize,
    out: Vec<EIdx>,
) -> Result<Option<Vec<EIdx>>, CheckError> {
    if s >= g.slots.len() {
        Ok(Some(out))
    } else {
        match slot_binder(pers, st, g, s) {
            Err(e) => Err(e),
            Ok(None) => Ok(None),
            Ok(Some(ty)) => {
                let mut o: Vec<EIdx> = out;
                o.push(ty);
                slot_binders(pers, st, g, s + 1, o)
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/GenRec.lean:161-174 ClassGen.prefixBinders
/// con-leche: ConLeche/Cached/IndRec.lean:108-120 _root_.ConLeche.ClassGen.prefixBindersC
/// Lean twin: `proof/ConRon/Arena/Inductives/GenRec.lean:231-261 ClassGen.prefixBinders` —
/// the prefix binders: the parameters, then every slot in the stream's order.
pub fn prefix_binders(pers: &PersTier, st: &mut AState, g: &ClassGen) -> Result<Option<Vec<EIdx>>, CheckError> {
    match gen_binders(pers, st, g, &g.params, 0, Vec::new()) {
        Err(e) => Err(e),
        Ok(pbs) => slot_binders(pers, st, g, 0, pbs),
    }
}

/// con-leche: ConLeche/Kernel/Inductives/GenRec.lean:176-183 classGenRecTy
/// con-leche: ConLeche/Cached/IndRec.lean:122-129 classGenRecTyC
/// Lean twin: `proof/ConRon/Arena/Inductives/GenRec.lean:263-278 classGenRecTy` — **the
/// generated recursor type** at class `c`: the prefix, the class's indices
/// and its major, over the motive applied to them.
pub fn class_gen_rec_ty(pers: &PersTier, st: &mut AState, g: &ClassGen, c: u64) -> Result<Option<EIdx>, CheckError> {
    let r_p: u64 = g.pre.len() as u64;
    match gen_major(pers, st, g, c, r_p) {
        Err(e) => Err(e),
        Ok(None) => Ok(None),
        Ok(Some((ifs, maj))) => match intern_e_fvar(pers, st, r_p + (ifs.len() as u64), maj.dup2()) {
            Err(e) => Err(e),
            Ok(t) => match gen_binders(pers, st, g, &ifs, 0, expr_ops::binder_copy_from(&g.pre, 0, Vec::new())) {
                Err(e) => Err(e),
                Ok(bs) => {
                    let mut bs2: Vec<EIdx> = bs;
                    bs2.push(maj);
                    match mot_var(pers, st, g, c) {
                        Err(e) => Err(e),
                        Ok(mv) => {
                            let mut args: Vec<EIdx> = env::eidx_vec_dup(&ifs);
                            args.push(t);
                            match expr_ops::mk_app_n(pers, st, &mv, &args) {
                                Err(e) => Err(e),
                                Ok(body) => match close_telescope(pers, st, &bs2, 0, &body) {
                                    Err(e) => Err(e),
                                    Ok(r) => Ok(Some(r)),
                                },
                            }
                        }
                    }
                }
            },
        },
    }
}

/// con-leche: ConLeche/Kernel/Inductives/GenRec.lean:185-208 classGenRule
/// con-leche: ConLeche/Cached/IndRec.lean:131-151 classGenRuleC
/// Lean twin: `(List.range g.slots.length).zip g.slots |>.find? …` — the minor
/// premise slot of class `c`'s constructor `cn`.
pub fn find_minor_slot(slots: &Vec<ClassSlot>, c: u64, cn: &NIdx, s: usize) -> Option<u64> {
    if s >= slots.len() {
        None
    } else if minor_is(&slots[s], c, cn) {
        Some(s as u64)
    } else {
        find_minor_slot(slots, c, cn, s + 1)
    }
}

/// con-leche: ConLeche/Kernel/Inductives/GenRec.lean:185-208 classGenRule
/// con-leche: ConLeche/Cached/IndRec.lean:131-151 classGenRuleC
/// Lean twin: `match sl with | .minor c' C _ => c' == c && C == x.cv.name | _ => false`.
pub fn minor_is(s: &ClassSlot, c: u64, cn: &NIdx) -> bool {
    match s {
        ClassSlot::Minor(c2, n2, _) => *c2 == c && n2.eq2(cn),
        ClassSlot::Motive(_) => false,
    }
}

/// con-leche: ConLeche/Kernel/Inductives/GenRec.lean:185-208 classGenRule
/// con-leche: ConLeche/Cached/IndRec.lean:131-151 classGenRuleC
/// Lean twin: `(List.range rP).map fun i => if i < g.nP then g.params.getD i
/// default else g.slotVar (i - g.nP)` — the prefix variables from `i` on.
pub fn prefix_vars(pers: &PersTier, st: &mut AState, g: &ClassGen, r_p: u64, i: u64, out: Vec<EIdx>) -> Result<Vec<EIdx>, CheckError> {
    if i >= r_p {
        Ok(out)
    } else if i < g.n_p {
        match expr_get_d(pers, st, &g.params, i) {
            Err(e) => Err(e),
            Ok(v) => {
                let mut o: Vec<EIdx> = out;
                o.push(v);
                prefix_vars(pers, st, g, r_p, i + 1, o)
            }
        }
    } else {
        match slot_var(pers, st, g, i - g.n_p) {
            Err(e) => Err(e),
            Ok(v) => {
                let mut o: Vec<EIdx> = out;
                o.push(v);
                prefix_vars(pers, st, g, r_p, i + 1, o)
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/GenRec.lean:536-541 classRecOf
/// Lean twin: `proof/ConRon/Arena/Inductives/GenRec.lean:280-286 classRecOf` — the
/// recursor a call at class `t` names: the family's first recursor at that
/// class.
pub fn class_rec_of(rec_cls: &Vec<u64>, cv_gs: &Vec<IConstantVal>, t: u64, r: usize) -> Option<NIdx> {
    if r >= cv_gs.len() {
        None
    } else {
        let c: u64 = if r < rec_cls.len() { rec_cls[r] } else { 0 };
        if c == t {
            Some(cv_gs[r].name.dup2())
        } else {
            class_rec_of(rec_cls, cv_gs, t, r + 1)
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/GenRec.lean:185-208 classGenRule
/// con-leche: ConLeche/Cached/IndRec.lean:131-151 classGenRuleC
/// Lean twin: `(List.range x.nF).filterMapM …` — the rule's recursive calls from
/// field `i` on: per recursive field `f` (walked type `w`), `λ a⃗, rec_t p⃗ e⃗
/// (f a⃗)`, the callee the family's recursor at the landing class; `none` when
/// a part fails or the class has no recursor.
#[allow(clippy::too_many_arguments)]
pub fn rule_calls(
    pers: &PersTier,
    st: &mut AState,
    g: &ClassGen,
    rec_cls: &Vec<u64>,
    cv_gs: &Vec<IConstantVal>,
    rlvls: &LsIdx,
    x: &ClassCtor,
    r_p: u64,
    fvs: &Vec<EIdx>,
    ws: &Vec<EIdx>,
    pvars: &Vec<EIdx>,
    i: u64,
    out: Vec<EIdx>,
) -> Result<Option<Vec<EIdx>>, CheckError> {
    if i >= x.n_f {
        Ok(Some(out))
    } else {
        let k: ClassField = if i < x.kinds.len() as u64 {
            class_field_dup(&x.kinds[i as usize])
        } else {
            ClassField::Ordinary
        };
        match k {
            ClassField::Ordinary => rule_calls(pers, st, g, rec_cls, cv_gs, rlvls, x, r_p, fvs, ws, pvars, i + 1, out),
            ClassField::Recursive(t, tele) => match expr_get_d(pers, st, ws, i) {
                Err(e) => Err(e),
                Ok(w) => match ih_parts(pers, st, g, t, tele, &w, r_p + x.n_f) {
                    Err(e) => Err(e),
                    Ok(None) => Ok(None),
                    Ok(Some((xs, idx))) => match class_rec_of(rec_cls, cv_gs, t, 0) {
                        None => Ok(None),
                        Some(r) => rule_call(pers, st, g, rec_cls, cv_gs, rlvls, x, r_p, fvs, ws, pvars, i, out, xs, idx, r),
                    },
                },
            },
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/GenRec.lean:185-208 classGenRule
/// con-leche: ConLeche/Cached/IndRec.lean:131-151 classGenRuleC
/// Lean twin: `proof/ConRon/Arena/Inductives/GenRec.lean:288-342 classGenRule` — one
/// recursive call, built and closed, then the rest.
#[allow(clippy::too_many_arguments)]
pub fn rule_call(
    pers: &PersTier,
    st: &mut AState,
    g: &ClassGen,
    rec_cls: &Vec<u64>,
    cv_gs: &Vec<IConstantVal>,
    rlvls: &LsIdx,
    x: &ClassCtor,
    r_p: u64,
    fvs: &Vec<EIdx>,
    ws: &Vec<EIdx>,
    pvars: &Vec<EIdx>,
    i: u64,
    out: Vec<EIdx>,
    xs: Vec<EIdx>,
    idx: Vec<EIdx>,
    r: NIdx,
) -> Result<Option<Vec<EIdx>>, CheckError> {
    match expr_get_d(pers, st, fvs, i) {
        Err(e) => Err(e),
        Ok(f) => match expr_ops::mk_app_n(pers, st, &f, &xs) {
            Err(e) => Err(e),
            Ok(fx) => match intern_e_const(pers, st, r, rlvls.dup2()) {
                Err(e) => Err(e),
                Ok(rc) => {
                    let mut args: Vec<EIdx> = eidx_append(pvars, &idx);
                    args.push(fx);
                    match expr_ops::mk_app_n(pers, st, &rc, &args) {
                        Err(e) => Err(e),
                        Ok(app) => match gen_binders(pers, st, g, &xs, 0, Vec::new()) {
                            Err(e) => Err(e),
                            Ok(bs) => match close_lams(pers, st, &bs, r_p + x.n_f, &app) {
                                Err(e) => Err(e),
                                Ok(call) => {
                                    let mut o: Vec<EIdx> = out;
                                    o.push(call);
                                    rule_calls(pers, st, g, rec_cls, cv_gs, rlvls, x, r_p, fvs, ws, pvars, i + 1, o)
                                }
                            },
                        },
                    }
                }
            },
        },
    }
}

/// con-leche: ConLeche/Kernel/Inductives/GenRec.lean:185-208 classGenRule
/// con-leche: ConLeche/Cached/IndRec.lean:131-151 classGenRuleC
/// Lean twin: `proof/ConRon/Arena/Inductives/GenRec.lean:288-342 classGenRule` — **the
/// generated rule** of a recursor at class `c` for its constructor `x`: `λ p⃗
/// (prefix) f⃗, minor f⃗ (λ a⃗, rec_t p⃗ (prefix) e⃗ (f a⃗))…`.
#[allow(clippy::too_many_arguments)]
pub fn class_gen_rule(
    pers: &PersTier,
    st: &mut AState,
    g: &ClassGen,
    rec_cls: &Vec<u64>,
    cv_gs: &Vec<IConstantVal>,
    rlvls: &LsIdx,
    c: u64,
    x: &ClassCtor,
) -> Result<Option<EIdx>, CheckError> {
    let r_p: u64 = g.pre.len() as u64;
    match find_minor_slot(&g.slots, c, &x.cv.name, 0) {
        None => Ok(None),
        Some(s) => match core::open_pis_at_fvars_f(pers, st, x.n_f, &x.ty_d, r_p) {
            Err(e) => Err(e),
            Ok(None) => Ok(None),
            Ok(Some((fvs, _))) => match rec_check::target_pi_doms_with(pers, st, &fvs, 0, &x.ty_n, Vec::new()) {
                Err(e) => Err(e),
                Ok(None) => Ok(None),
                Ok(Some(ws)) => match prefix_vars(pers, st, g, r_p, 0, Vec::new()) {
                    Err(e) => Err(e),
                    Ok(pvars) => match rule_calls(pers, st, g, rec_cls, cv_gs, rlvls, x, r_p, &fvs, &ws, &pvars, 0, Vec::new()) {
                        Err(e) => Err(e),
                        Ok(None) => Ok(None),
                        Ok(Some(ihs)) => class_gen_rule_close(pers, st, g, s, &fvs, &ihs),
                    },
                },
            },
        },
    }
}

/// con-leche: ConLeche/Kernel/Inductives/GenRec.lean:185-208 classGenRule
/// con-leche: ConLeche/Cached/IndRec.lean:131-151 classGenRuleC
/// Lean twin: `proof/ConRon/Arena/Inductives/GenRec.lean:288-342 classGenRule` — the
/// minor premise `slot s` applied to the fields and the calls, closed over the
/// prefix and the fields.
pub fn class_gen_rule_close(
    pers: &PersTier,
    st: &mut AState,
    g: &ClassGen,
    s: u64,
    fvs: &Vec<EIdx>,
    ihs: &Vec<EIdx>,
) -> Result<Option<EIdx>, CheckError> {
    match slot_var(pers, st, g, s) {
        Err(e) => Err(e),
        Ok(sv) => {
            let args: Vec<EIdx> = eidx_append(fvs, ihs);
            match expr_ops::mk_app_n(pers, st, &sv, &args) {
                Err(e) => Err(e),
                Ok(body) => match gen_binders(pers, st, g, fvs, 0, expr_ops::binder_copy_from(&g.pre, 0, Vec::new())) {
                    Err(e) => Err(e),
                    Ok(bs) => match close_lams(pers, st, &bs, 0, &body) {
                        Err(e) => Err(e),
                        Ok(r) => Ok(Some(r)),
                    },
                },
            }
        }
    }
}

// ---------------------------------------------------------------------------
// The stage
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/Inductives/GenRec.lean:214-217 ClassSlot.isMinor
/// Lean twin: `proof/ConRon/Arena/Inductives/GenRec.lean:346-350 ClassSlot.isMinor` — a
/// minor premise's slot.
pub fn slot_is_minor(s: &ClassSlot) -> bool {
    match s {
        ClassSlot::Minor(_, _, _) => true,
        ClassSlot::Motive(_) => false,
    }
}

/// con-leche: ConLeche/Kernel/Inductives/GenRec.lean:219-228 classMinorSlot
/// Lean twin: the cited `filterMap`'s hits `(s, ihs)` from slot `s` on.
pub fn minor_hits(
    slots: &Vec<ClassSlot>,
    c: u64,
    cn: &NIdx,
    s: usize,
    out: Vec<(u64, Vec<(u64, u64)>)>,
) -> Vec<(u64, Vec<(u64, u64)>)> {
    if s >= slots.len() {
        out
    } else {
        match &slots[s] {
            ClassSlot::Minor(c2, n2, ihs) => {
                if *c2 == c && n2.eq2(cn) {
                    let mut o: Vec<(u64, Vec<(u64, u64)>)> = out;
                    o.push((s as u64, class_read::pairs_dup(ihs, 0, Vec::new())));
                    minor_hits(slots, c, cn, s + 1, o)
                } else {
                    minor_hits(slots, c, cn, s + 1, out)
                }
            }
            ClassSlot::Motive(_) => minor_hits(slots, c, cn, s + 1, out),
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/GenRec.lean:219-228 classMinorSlot
/// Lean twin: `proof/ConRon/Arena/Inductives/GenRec.lean:352-362 classMinorSlot` — the minor
/// premise slot of class `c`'s constructor `cn`: exactly one.
pub fn class_minor_slot(rd: &ClassRead, c: u64, cn: &NIdx) -> Result<(u64, Vec<(u64, u64)>), CheckError> {
    let hits: Vec<(u64, Vec<(u64, u64)>)> = minor_hits(&rd.slots, c, cn, 0, Vec::new());
    if hits.len() == 1 {
        Ok((hits[0].0, class_read::pairs_dup(&hits[0].1, 0, Vec::new())))
    } else {
        fail(core_types::invalid(code_points(&M_MINOR_SLOT)))
    }
}

/// con-leche: ConLeche/Kernel/Inductives/GenRec.lean:230-250 classFieldsOf
/// con-leche: ConLeche/Cached/IndRec.lean:227-240 classFieldsOfC
/// Lean twin: `ihs.filter (·.1 == i)` — the inductive hypotheses at field `i`.
pub fn ihs_at(ihs: &Vec<(u64, u64)>, i: u64, k: usize, out: Vec<(u64, u64)>) -> Vec<(u64, u64)> {
    if k >= ihs.len() {
        out
    } else if ihs[k].0 == i {
        let mut o: Vec<(u64, u64)> = out;
        o.push((ihs[k].0, ihs[k].1));
        ihs_at(ihs, i, k + 1, o)
    } else {
        ihs_at(ihs, i, k + 1, out)
    }
}

/// con-leche: ConLeche/Kernel/Inductives/GenRec.lean:230-250 classFieldsOf
/// con-leche: ConLeche/Cached/IndRec.lean:227-240 classFieldsOfC
/// Lean twin: `proof/ConRon/Arena/Inductives/GenRec.lean:364-386 classFieldsOf` — **the
/// minor premise's inductive hypotheses are the datum's recursive fields**,
/// one each: a field whose walked type names a member has exactly one, at
/// the class it names; an ordinary one none.
#[allow(clippy::too_many_arguments)]
pub fn class_fields_of(
    pers: &PersTier,
    st: &AState,
    p: &BlockShape,
    ihs: &Vec<(u64, u64)>,
    i: u64,
    fs: &Vec<EIdx>,
    out: Vec<ClassField>,
) -> Result<Vec<ClassField>, CheckError> {
    if i >= fs.len() as u64 {
        Ok(out)
    } else {
        match expr_ops::fvar_type_d(pers, st, &fs[i as usize]) {
            Err(e) => Err(e),
            Ok(w) => match nest_occ(pers, st, &shape_member_names(p), 0, 0, &w) {
                Err(e) => Err(e),
                Ok(occ) => {
                    let hits: Vec<(u64, u64)> = ihs_at(ihs, i, 0, Vec::new());
                    if !occ && hits.len() == 0 {
                        let mut o: Vec<ClassField> = out;
                        o.push(ClassField::Ordinary);
                        class_fields_of(pers, st, p, ihs, i + 1, fs, o)
                    } else if occ && hits.len() == 1 {
                        match pi_binders(pers, st, CORE_WALK_FUEL, &w, Vec::new()) {
                            Err(e) => Err(e),
                            Ok((bs, _)) => {
                                let mut o: Vec<ClassField> = out;
                                o.push(ClassField::Recursive(hits[0].1, bs.len() as u64));
                                class_fields_of(pers, st, p, ihs, i + 1, fs, o)
                            }
                        }
                    } else {
                        fail(core_types::invalid(code_points(&M_IHS)))
                    }
                }
            },
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/GenRec.lean:252-267 classNodesAgree
/// con-leche: ConLeche/Cached/IndRec.lean:242-253 classNodesAgreeC
/// Lean twin: `proof/ConRon/Arena/Inductives/GenRec.lean:388-407 classNodesAgree` — **node
/// agreement at one recursive field** (K.53′): at every entry of the
/// constructor from `j` on, field `i` (opened at the datum's variables `fvs`)
/// passes `targetK53` against the inductive hypothesis's class `mc`.
#[allow(clippy::too_many_arguments)]
pub fn class_nodes_agree(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    fe: &IFEnv,
    p: &BlockShape,
    former_tys: &Vec<EIdx>,
    mc: &TargetMajor,
    tele: &Vec<EIdx>,
    leaf: &EIdx,
    fvs: &Vec<EIdx>,
    i: u64,
    es: &Vec<NestCtorNf>,
    j: usize,
) -> Result<(), CheckError> {
    if j >= es.len() {
        Ok(())
    } else {
        let ty: EIdx = es[j].ty.dup2();
        match rec_check::target_pi_doms_with(pers, st, fvs, 0, &ty, Vec::new()) {
            Err(e) => Err(e),
            Ok(o) => {
                let doms: Vec<EIdx> = match o {
                    Some(ds) => ds,
                    None => Vec::new(),
                };
                match positivity::eidx_get(&doms, i) {
                    None => fail(core_types::invalid(code_points(&M_NF_SHORT))),
                    Some(f) => match rec_check::target_k53(pers, st, mode, fe, p, former_tys, mc, tele, leaf, &f) {
                        Err(e) => Err(e),
                        Ok(false) => fail(core_types::invalid(code_points(&M_NODES))),
                        Ok(true) => class_nodes_agree(pers, st, mode, fe, p, former_tys, mc, tele, leaf, fvs, i, es, j + 1),
                    },
                }
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/GenRec.lean:269-273 classLeafAt
/// Lean twin: `proof/ConRon/Arena/Inductives/GenRec.lean:409-417 classLeafAt` — a walked
/// field's leaf is headed by class `m`'s inductive.
pub fn class_leaf_at(pers: &PersTier, st: &AState, m: &TargetMajor, leaf: &EIdx) -> Result<bool, CheckError> {
    match expr_ops::get_app_fn(pers, st, CORE_WALK_FUEL, leaf) {
        Err(e) => Err(e),
        Ok(hd) => {
            if hd.tag() == ETAG_CONST {
                match view_const(pers, st, &hd) {
                    None => fail_dangling_e(),
                    Some((i_name, _)) => Ok(i_name.eq2(&m.ind)),
                }
            } else {
                Ok(false)
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/GenRec.lean:275-289 classFieldsAgree
/// con-leche: ConLeche/Cached/IndRec.lean:255-268 classFieldsAgreeC
/// Lean twin: `proof/ConRon/Arena/Inductives/GenRec.lean:419-440 classFieldsAgree` — node
/// agreement at every recursive field of the datum from field `i` on.
#[allow(clippy::too_many_arguments)]
pub fn class_fields_agree(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    fe: &IFEnv,
    p: &BlockShape,
    former_tys: &Vec<EIdx>,
    ms: &Vec<TargetMajor>,
    fvs: &Vec<EIdx>,
    es: &Vec<NestCtorNf>,
    i: u64,
    ks: &Vec<ClassField>,
) -> Result<(), CheckError> {
    if i >= ks.len() as u64 {
        Ok(())
    } else {
        match class_field_dup(&ks[i as usize]) {
            ClassField::Ordinary => class_fields_agree(pers, st, mode, fe, p, former_tys, ms, fvs, es, i + 1, ks),
            ClassField::Recursive(t, tele) => match expr_get_d(pers, st, fvs, i) {
                Err(e) => Err(e),
                Ok(fv) => match expr_ops::fvar_type_d(pers, st, &fv) {
                    Err(e) => Err(e),
                    Ok(fty) => match expr_ops::strip_pis(pers, st, tele, &fty) {
                        Err(e) => Err(e),
                        Ok(None) => fail(core_types::internal(code_points(&M_FIELD_TELE))),
                        Ok(Some((tele_b, leaf))) => match rec_check::target_major_at(pers, st, ms, t) {
                            Err(e) => Err(e),
                            Ok(mt) => match class_leaf_at(pers, st, &mt, &leaf) {
                                Err(e) => Err(e),
                                Ok(false) => fail(core_types::invalid(code_points(&M_LEAF))),
                                Ok(true) => match class_nodes_agree(
                                    pers, st, mode, fe, p, former_tys, &mt, &tele_b, &leaf, fvs, i, es, 0,
                                ) {
                                    Err(e) => Err(e),
                                    Ok(()) => class_fields_agree(pers, st, mode, fe, p, former_tys, ms, fvs, es, i + 1, ks),
                                },
                            },
                        },
                    },
                },
            },
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/GenRec.lean:291-309 classCtorOf
/// con-leche: ConLeche/Cached/IndRec.lean:270-285 classCtorOfC
/// Lean twin: `M.nfs.filter (·.ctor == c)` — a class's table entries of one
/// constructor, in table order.
pub fn nfs_of_ctor(es: &Vec<NestCtorNf>, c: &NIdx, i: usize, out: Vec<NestCtorNf>) -> Vec<NestCtorNf> {
    if i >= es.len() {
        out
    } else if es[i].ctor.eq2(c) {
        let mut o: Vec<NestCtorNf> = out;
        o.push(positivity::nest_ctor_nf_dup(&es[i]));
        nfs_of_ctor(es, c, i + 1, o)
    } else {
        nfs_of_ctor(es, c, i + 1, out)
    }
}

/// con-leche: ConLeche/Kernel/Inductives/GenRec.lean:291-309 classCtorOf
/// con-leche: ConLeche/Cached/IndRec.lean:270-285 classCtorOfC
/// Lean twin: `proof/ConRon/Arena/Inductives/GenRec.lean:442-467 classCtorOf` — **one
/// constructor of class `c`, read for the generator**: its entries in the
/// class's table (the first the DATUM), the minor premise's inductive
/// hypotheses against the datum's recursive fields, node agreement at every
/// entry, and the constructor's declared type at the class.
#[allow(clippy::too_many_arguments)]
pub fn class_ctor_of(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    fe: &IFEnv,
    p: &BlockShape,
    former_tys: &Vec<EIdx>,
    rd: &ClassRead,
    ms: &Vec<TargetMajor>,
    c: u64,
    ctor: &(IConstantVal, u64),
) -> Result<ClassCtor, CheckError> {
    match rec_check::target_major_at(pers, st, ms, c) {
        Err(e) => Err(e),
        Ok(m) => {
            let es: Vec<NestCtorNf> = nfs_of_ctor(&m.nfs, &ctor.0.name, 0, Vec::new());
            if es.len() == 0 {
                fail(core_types::internal(code_points(&M_NO_ENTRY)))
            } else {
                let e0: EIdx = es[0].ty.dup2();
                match class_minor_slot(rd, c, &ctor.0.name) {
                    Err(e) => Err(e),
                    Ok((_, ihs)) => {
                        match core::open_pis_at_fvars_f(pers, st, ctor.1, &e0, p.n_p + shape_k(p)) {
                            Err(e) => Err(e),
                            Ok(None) => fail(core_types::internal(code_points(&M_DATUM))),
                            Ok(Some((fvs, _))) => match class_fields_of(pers, st, p, &ihs, 0, &fvs, Vec::new()) {
                                Err(e) => Err(e),
                                Ok(kinds) => match class_fields_agree(pers, st, mode, fe, p, former_tys, ms, &fvs, &es, 0, &kinds) {
                                    Err(e) => Err(e),
                                    Ok(()) => match rec_check::target_ctor_at(pers, st, &m, &ctor.0) {
                                        Err(e) => Err(e),
                                        Ok(t0) => match inst_pis_with(pers, st, &m.ds, 0, &t0) {
                                            Err(e) => Err(e),
                                            Ok(None) => fail(core_types::internal(code_points(&M_CTOR_PARAMS))),
                                            Ok(Some(ty_d)) => Ok(ClassCtor {
                                                cv: env::i_constant_val_dup(&ctor.0),
                                                n_f: ctor.1,
                                                kinds,
                                                ty_d,
                                                ty_n: e0,
                                            }),
                                        },
                                    },
                                },
                            },
                        }
                    }
                }
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/GenRec.lean:311-319 classCtorsOf
/// con-leche: ConLeche/Cached/IndRec.lean:287-295 classCtorsOfC
/// Lean twin: `proof/ConRon/Arena/Inductives/GenRec.lean:469-479 classCtorsOf` — every
/// constructor of class `c` from `i` on.
#[allow(clippy::too_many_arguments)]
pub fn class_ctors_of(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    fe: &IFEnv,
    p: &BlockShape,
    former_tys: &Vec<EIdx>,
    rd: &ClassRead,
    ms: &Vec<TargetMajor>,
    c: u64,
    cs: &Vec<(IConstantVal, u64)>,
    i: usize,
    out: Vec<ClassCtor>,
) -> Result<Vec<ClassCtor>, CheckError> {
    if i >= cs.len() {
        Ok(out)
    } else {
        match class_ctor_of(pers, st, mode, fe, p, former_tys, rd, ms, c, &cs[i]) {
            Err(e) => Err(e),
            Ok(x) => {
                let mut o: Vec<ClassCtor> = out;
                o.push(x);
                class_ctors_of(pers, st, mode, fe, p, former_tys, rd, ms, c, cs, i + 1, o)
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/GenRec.lean:321-328 classesCtors
/// con-leche: ConLeche/Cached/IndRec.lean:297-305 classesCtorsC
/// Lean twin: `proof/ConRon/Arena/Inductives/GenRec.lean:481-491 classesCtors` — every
/// class's constructors, from class `c` on.
#[allow(clippy::too_many_arguments)]
pub fn classes_ctors(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    fe: &IFEnv,
    p: &BlockShape,
    former_tys: &Vec<EIdx>,
    rd: &ClassRead,
    ms: &Vec<TargetMajor>,
    c: usize,
    out: Vec<Vec<ClassCtor>>,
) -> Result<Vec<Vec<ClassCtor>>, CheckError> {
    if c >= ms.len() {
        Ok(out)
    } else {
        let cs: Vec<(IConstantVal, u64)> = block_shape::ctors_dup(&ms[c].ctors, 0, Vec::new());
        match class_ctors_of(pers, st, mode, fe, p, former_tys, rd, ms, c as u64, &cs, 0, Vec::new()) {
            Err(e) => Err(e),
            Ok(xs) => {
                let mut o: Vec<Vec<ClassCtor>> = out;
                o.push(xs);
                classes_ctors(pers, st, mode, fe, p, former_tys, rd, ms, c + 1, o)
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/GenRec.lean:330-339 classMajors
/// con-leche: ConLeche/Cached/IndBlock.lean:339-347 classMajorsC
/// Lean twin: `proof/ConRon/Arena/Inductives/GenRec.lean:493-506 classMajors` — every class
/// checked as a major (`targetMajorOf`, `targetMajorPins`), over the block's
/// canonical parameters `pfvs`.
#[allow(clippy::too_many_arguments)]
pub fn class_majors(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    fe: &IFEnv,
    p: &BlockShape,
    pfvs: &Vec<EIdx>,
    keys: &Vec<ClassKey>,
    i: usize,
    out: Vec<TargetMajor>,
) -> Result<Vec<TargetMajor>, CheckError> {
    if i >= keys.len() {
        Ok(out)
    } else {
        match intern_e_const(pers, st, keys[i].ind.dup2(), keys[i].lvls.dup2()) {
            Err(e) => Err(e),
            Ok(hd) => match expr_ops::mk_app_n(pers, st, &hd, &keys[i].ds) {
                Err(e) => Err(e),
                Ok(mty) => match rec_check::target_major_of(pers, st, mode, fe, p, pfvs, pfvs, &mty) {
                    Err(e) => Err(e),
                    Ok(m) => match rec_check::target_major_pins(pers, st, mode, fe, p.n_p, &m) {
                        Err(e) => Err(e),
                        Ok(()) => {
                            let mut o: Vec<TargetMajor> = out;
                            o.push(m);
                            class_majors(pers, st, mode, fe, p, pfvs, keys, i + 1, o)
                        }
                    },
                },
            },
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/GenRec.lean:341-348 classesNfs
/// con-leche: ConLeche/Cached/IndRec.lean:307-314 classesNfsC
/// Lean twin: `proof/ConRon/Arena/Inductives/GenRec.lean:508-517 classesNfs` — every class
/// with its entries of the table (`targetMajorNfs`), from `i` on.
#[allow(clippy::too_many_arguments)]
pub fn classes_nfs(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    fe: &IFEnv,
    p: &BlockShape,
    former_tys: &Vec<EIdx>,
    tbl: &Vec<NestCtorNf>,
    ms: &Vec<TargetMajor>,
    i: usize,
    out: Vec<TargetMajor>,
) -> Result<Vec<TargetMajor>, CheckError> {
    if i >= ms.len() {
        Ok(out)
    } else {
        let m: TargetMajor = rec_check::target_major_dup(&ms[i]);
        match rec_check::target_major_nfs(pers, st, mode, fe, p, former_tys, &m.pfvs, &m.lvls, &m.ds, &m.ctors, tbl) {
            Err(e) => Err(e),
            Ok(es) => {
                let mut m2: TargetMajor = m;
                m2.nfs = es;
                let mut o: Vec<TargetMajor> = out;
                o.push(m2);
                classes_nfs(pers, st, mode, fe, p, former_tys, tbl, ms, i + 1, o)
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/GenRec.lean:350-360 classFormerTy
/// con-leche: ConLeche/Cached/IndRec.lean:316-324 classFormerTyC
/// Lean twin: `proof/ConRon/Arena/Inductives/GenRec.lean:519-537 classFormerTy` — a class's
/// former type: a member's own (`formers`, the block's formers at the
/// telescopes the check reads), an outside class's stored former at its
/// telescope (`positivity::family_telescope`) at the class's levels.
pub fn class_former_ty(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    fe: &IFEnv,
    formers: &Vec<IConstantVal>,
    m: &TargetMajor,
) -> Result<EIdx, CheckError> {
    match m.member {
        Some(t) => {
            if t < formers.len() as u64 {
                Ok(formers[t as usize].ty.dup2())
            } else {
                intern_e_bvar(pers, st, 0)
            }
        }
        None => match env::ifenv_find(pers, fe, &m.ind) {
            Some(IConstantInfo::IndInfo(cv, caps)) => match positivity::family_telescope(pers, st, mode, fe, cv, caps) {
                Err(e) => Err(e),
                Ok(ty) => expr_ops::inst_lp_fast(pers, st, CORE_WALK_FUEL, &cv.level_params, &m.lvls, &ty),
            },
            _ => fail(core_types::internal(code_points(&M_FORMER))),
        },
    }
}

/// con-leche: ConLeche/Kernel/Inductives/GenRec.lean:350-360 classFormerTy
/// con-leche: ConLeche/Cached/IndRec.lean:316-324 classFormerTyC
/// Lean twin: `Ms.mapM (classFormerTy ops fe p.formers)`.
pub fn class_former_tys(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    fe: &IFEnv,
    formers: &Vec<IConstantVal>,
    ms: &Vec<TargetMajor>,
    i: usize,
    out: Vec<EIdx>,
) -> Result<Vec<EIdx>, CheckError> {
    if i >= ms.len() {
        Ok(out)
    } else {
        match class_former_ty(pers, st, mode, fe, formers, &ms[i]) {
            Err(e) => Err(e),
            Ok(t) => {
                let mut o: Vec<EIdx> = out;
                o.push(t);
                class_former_tys(pers, st, mode, fe, formers, ms, i + 1, o)
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/GenRec.lean:362-381 classConstOk
/// con-leche: ConLeche/Cached/IndRec.lean:328-345 classConstOkC
/// Lean twin: `proof/ConRon/Arena/Inductives/GenRec.lean:539-562 classConstOk` — **a
/// generated constant, checked**: `checkConstantValF` — the generated type is
/// stored as the generator built it; inference validates it like any other
/// declared type: the guards in the cited order (a literal's name only at
/// its shape, `core::lit_shape_ok`), then its type inferred and a sort.
pub fn class_const_ok(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    fe: &IFEnv,
    cv: &IConstantVal,
) -> Result<(), CheckError> {
    if env::ifenv_find(pers, fe, &cv.name).is_some() {
        fail(core_types::invalid(code_points(&M_DUP_DECL)))
    } else {
        match core::lit_shape_ok(pers, st, &IConstantInfo::AxiomInfo(env::i_constant_val_dup(cv))) {
            Err(e) => Err(e),
            Ok(false) => fail(core_types::not_implemented(code_points(&M_LIT_SHAPE))),
            Ok(true) => class_const_ok_type(pers, st, mode, fe, cv),
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/GenRec.lean:362-381 classConstOk
/// con-leche: ConLeche/Cached/IndRec.lean:328-345 classConstOkC
/// Lean twin: `proof/ConRon/Arena/Inductives/GenRec.lean:539-562 classConstOk` — the
/// type's guards and its inference.
pub fn class_const_ok_type(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    fe: &IFEnv,
    cv: &IConstantVal,
) -> Result<(), CheckError> {
    if !checker_base::name_nodup(&cv.level_params) {
        fail(core_types::invalid(code_points(&M_DUP_UNIV)))
    } else {
        match expr_ops::loose_bvars_bounded_fast(pers, st, CORE_WALK_FUEL, 0, &cv.ty) {
            Err(e) => Err(e),
            Ok(false) => fail(core_types::internal(code_points(&M_LOOSE))),
            Ok(true) => match expr_ops::has_fvar_fast(pers, st, CORE_WALK_FUEL, &cv.ty) {
                Err(e) => Err(e),
                Ok(true) => fail(core_types::internal(code_points(&M_FVAR))),
                Ok(false) => match checker_base::all_level_params_defined(pers, st, &cv.level_params, &cv.ty) {
                    Err(e) => Err(e),
                    Ok(false) => fail(core_types::invalid(code_points(&M_UNDECL))),
                    Ok(true) => match checker_base::consts_resolve_f_fast(pers, st, fe, &cv.ty) {
                        Err(e) => Err(e),
                        Ok(false) => match checker_base::unresolved_consts_error(pers, st, &cv.ty) {
                            Err(e) => Err(e),
                            Ok(er) => fail(er),
                        },
                        Ok(true) => match core::infer_type_core(pers, st, mode, fe, core::CHECK_FUEL, 0, &cv.ty) {
                            Err(e) => Err(e),
                            Ok(stype) => match core::ensure_sort_core(pers, st, mode, fe, core::CHECK_FUEL, 0, &stype) {
                                Err(e) => Err(e),
                                Ok(_) => Ok(()),
                            },
                        },
                    },
                },
            },
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/GenRec.lean:383-390 classRecTyCheck
/// con-leche: ConLeche/Cached/IndRec.lean:347-352 classRecTyCheckC
/// Lean twin: `proof/ConRon/Arena/Inductives/GenRec.lean:564-572 classRecTyCheck` — **the
/// check of a generated recursor type**: checked as a constant and defeq to the
/// stream's checked type `cv_ri`.
pub fn class_rec_ty_check(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    fe: &IFEnv,
    cv_ri: &IConstantVal,
    cv_g: &IConstantVal,
) -> Result<(), CheckError> {
    match class_const_ok(pers, st, mode, fe, cv_g) {
        Err(e) => Err(e),
        Ok(()) => match core::is_def_eq_core(
            pers,
            st,
            mode,
            fe,
            core::CHECK_FUEL,
            0,
            &cv_ri.ty,
            &cv_g.ty,
        ) {
            Err(e) => Err(e),
            Ok(false) => fail(core_types::invalid(code_points(&M_REC_DEFEQ))),
            Ok(true) => Ok(()),
        },
    }
}

/// con-leche: ConLeche/Kernel/Inductives/GenRec.lean:392-408 classRecTyOk
/// con-leche: ConLeche/Cached/IndRec.lean:354-366 classRecTyOkC
/// Lean twin: `proof/ConRon/Arena/Inductives/GenRec.lean:574-593 classRecTyOk` — **one
/// recursor's generated type, checked and compared**: the record's member,
/// rule prefix and major index are the generated ones; the generated type is
/// checked as a constant under the record's name and level parameters and
/// must be defeq to the stream's checked type `cv_ri`.
#[allow(clippy::too_many_arguments)]
pub fn class_rec_ty_ok(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    fe: &IFEnv,
    g: &ClassGen,
    k: u64,
    rc: &RecShape,
    cv_ri: &IConstantVal,
    c: u64,
) -> Result<IConstantVal, CheckError> {
    match rec_check::target_major_at(pers, st, &g.cls, c) {
        Err(e) => Err(e),
        Ok(ci) => {
            let want: u64 = match ci.member {
                Some(t) => t,
                None => k,
            };
            if rc.tgt != want {
                fail(core_types::invalid(code_points(&M_REC_MEMBER)))
            } else if !(rc.r_p == g.n_p + (g.slots.len() as u64) && rc.m_i == rc.r_p + ci.n_idx) {
                fail(core_types::invalid(code_points(&M_REC_PREFIX)))
            } else {
                match class_gen_rec_ty(pers, st, g, c) {
                    Err(e) => Err(e),
                    Ok(None) => fail(core_types::internal(code_points(&M_REC_TY))),
                    Ok(Some(gty)) => {
                        let cv: IConstantVal = IConstantVal {
                            name: rc.cv_r.name.dup2(),
                            level_params: env::nidx_vec_dup(&rc.cv_r.level_params),
                            ty: gty,
                        };
                        match class_rec_ty_check(pers, st, mode, fe, cv_ri, &cv) {
                            Err(e) => Err(e),
                            Ok(()) => Ok(cv),
                        }
                    }
                }
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/GenRec.lean:410-419 classRecTysOk
/// con-leche: ConLeche/Cached/IndRec.lean:368-376 classRecTysOkC
/// Lean twin: `proof/ConRon/Arena/Inductives/GenRec.lean:595-606 classRecTysOk` — every
/// recursor's generated type, pairwise with the stream's checked types and
/// the recursors' classes; the lists running out unevenly is internal.
#[allow(clippy::too_many_arguments)]
pub fn class_rec_tys_ok(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    fe: &IFEnv,
    g: &ClassGen,
    k: u64,
    rcs: &Vec<RecShape>,
    cvs: &Vec<IConstantVal>,
    cs: &Vec<u64>,
    i: usize,
    out: Vec<IConstantVal>,
) -> Result<Vec<IConstantVal>, CheckError> {
    if i >= rcs.len() {
        Ok(out)
    } else if i >= cvs.len() || i >= cs.len() {
        fail(core_types::internal(code_points(&M_REC_LIST)))
    } else {
        match class_rec_ty_ok(pers, st, mode, fe, g, k, &rcs[i], &cvs[i], cs[i]) {
            Err(e) => Err(e),
            Ok(x) => {
                let mut o: Vec<IConstantVal> = out;
                o.push(x);
                class_rec_tys_ok(pers, st, mode, fe, g, k, rcs, cvs, cs, i + 1, o)
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/GenRec.lean:421-440 classRuleCheck
/// con-leche: ConLeche/Cached/IndRec.lean:378-398 classRuleCheckC
/// Lean twin: `rbs.all (fun b => b.1.constsResolveF feT)` — the rule's λ-domains
/// resolve at the constructors' environment `feT`.  The port holds only the
/// rule-less recursors' environment `fe` (`feT` with the generated recursors
/// `pushed` pushed on it, `class_fe_r_push`), so a domain resolves at `feT`
/// exactly when it resolves at `fe` and names none of `pushed` (no generated
/// recursor is a constant of `feT`: `class_const_ok` refused a duplicate).
pub fn domains_resolve(
    pers: &PersTier,
    st: &mut AState,
    fe: &IFEnv,
    pushed: &Vec<NIdx>,
    rbs: &Vec<EIdx>,
    i: usize,
) -> Result<bool, CheckError> {
    if i >= rbs.len() {
        Ok(true)
    } else {
        let d: EIdx = rbs[i].dup2();
        match checker_base::consts_resolve_f_fast(pers, st, fe, &d) {
            Err(e) => Err(e),
            Ok(false) => Ok(false),
            Ok(true) => match positivity::mentions_any_const(pers, st, pushed, &d) {
                Err(e) => Err(e),
                Ok(true) => Ok(false),
                Ok(false) => domains_resolve(pers, st, fe, pushed, rbs, i + 1),
            },
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/GenRec.lean:421-440 classRuleCheck
/// con-leche: ConLeche/Cached/IndRec.lean:378-398 classRuleCheckC
/// con-leche: ConLeche/Cached/CheckerC.lean:155-181 sharedOpsRuleR
/// Lean twin: `proof/ConRon/Arena/Inductives/GenRec.lean:608-638 classRuleCheck` — **the
/// check of a generated rule**: closed, its level parameters the recursor's,
/// resolving and typed at the rule-less recursors' environment `fe`
/// (`sharedOpsRuleR`'s flush leaving the inference), its λ-telescope `n` long,
/// its λ-domains resolving at the constructors' environment (`fe` without
/// `pushed`, `domains_resolve`).
#[allow(clippy::too_many_arguments)]
pub fn class_rule_check(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    fe: &IFEnv,
    pushed: &Vec<NIdx>,
    cv_r: &IConstantVal,
    n: u64,
    gen: &EIdx,
) -> Result<(), CheckError> {
    match expr_ops::loose_bvars_bounded_fast(pers, st, CORE_WALK_FUEL, 0, gen) {
        Err(e) => Err(e),
        Ok(false) => fail(core_types::internal(code_points(&M_RULE_OPEN))),
        Ok(true) => match expr_ops::has_fvar_fast(pers, st, CORE_WALK_FUEL, gen) {
            Err(e) => Err(e),
            Ok(true) => fail(core_types::internal(code_points(&M_RULE_OPEN))),
            Ok(false) => match checker_base::all_level_params_defined(pers, st, &cv_r.level_params, gen) {
                Err(e) => Err(e),
                Ok(false) => fail(core_types::internal(code_points(&M_RULE_ULP))),
                Ok(true) => match checker_base::consts_resolve_f_fast(pers, st, fe, gen) {
                    Err(e) => Err(e),
                    Ok(false) => match checker_base::unresolved_consts_error(pers, st, gen) {
                        Err(e) => Err(e),
                        Ok(er) => fail(er),
                    },
                    Ok(true) => match core::infer_type_core(pers, st, mode, fe, core::CHECK_FUEL, 0, gen) {
                        Err(e) => Err(e),
                        Ok(_) => {
                            // `sharedOpsRuleR`'s `inferType`: the flush leaving the
                            // rule-less recursors' environment
                            core::flush_caches(st);
                            class_rule_check_tail(pers, st, fe, pushed, n, gen)
                        }
                    },
                },
            },
        },
    }
}

/// con-leche: ConLeche/Kernel/Inductives/GenRec.lean:421-440 classRuleCheck
/// con-leche: ConLeche/Cached/IndRec.lean:378-398 classRuleCheckC
/// Lean twin: `proof/ConRon/Arena/Inductives/GenRec.lean:608-638 classRuleCheck` — the
/// λ-telescope and its domains' resolution.
pub fn class_rule_check_tail(
    pers: &PersTier,
    st: &mut AState,
    fe: &IFEnv,
    pushed: &Vec<NIdx>,
    n: u64,
    gen: &EIdx,
) -> Result<(), CheckError> {
    match expr_ops::strip_lams(pers, st, n, gen) {
        Err(e) => Err(e),
        Ok(None) => fail(core_types::internal(code_points(&M_RULE_TELE))),
        Ok(Some((rbs, _))) => match domains_resolve(pers, st, fe, pushed, &rbs, 0) {
            Err(e) => Err(e),
            Ok(false) => match checker_base::unresolved_consts_error(pers, st, gen) {
                Err(e) => Err(e),
                Ok(er) => fail(er),
            },
            Ok(true) => Ok(()),
        },
    }
}

/// con-leche: ConLeche/Kernel/Inductives/GenRec.lean:442-447 classRuleOk
/// Lean twin: `proof/ConRon/Arena/Inductives/GenRec.lean:640-645 classRuleOk` — **one
/// generated rule, installed as generated**, after its check.
#[allow(clippy::too_many_arguments)]
pub fn class_rule_ok(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    fe: &IFEnv,
    pushed: &Vec<NIdx>,
    cv_r: &IConstantVal,
    n: u64,
    gen: EIdx,
) -> Result<EIdx, CheckError> {
    match class_rule_check(pers, st, mode, fe, pushed, cv_r, n, &gen) {
        Err(e) => Err(e),
        Ok(()) => Ok(gen),
    }
}

/// con-leche: ConLeche/Kernel/Inductives/GenRec.lean:449-460 classRulesOk
/// con-leche: ConLeche/Cached/IndRec.lean:400-411 classRulesOkC
/// Lean twin: `proof/ConRon/Arena/Inductives/GenRec.lean:647-662 classRulesOk` — a
/// recursor's generated rules, one per constructor of its class, from `i` on.
#[allow(clippy::too_many_arguments)]
pub fn class_rules_ok(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    fe: &IFEnv,
    pushed: &Vec<NIdx>,
    g: &ClassGen,
    rec_cls: &Vec<u64>,
    cv_gs: &Vec<IConstantVal>,
    cv_r: &IConstantVal,
    c: u64,
    xs: &Vec<ClassCtor>,
    i: usize,
    out: Vec<EIdx>,
) -> Result<Vec<EIdx>, CheckError> {
    if i >= xs.len() {
        Ok(out)
    } else {
        match struct_parts::param_levels(pers, st, &cv_r.level_params) {
            Err(e) => Err(e),
            Ok(rlvls) => match class_gen_rule(pers, st, g, rec_cls, cv_gs, &rlvls, c, &xs[i]) {
                Err(e) => Err(e),
                Ok(None) => fail(core_types::invalid(code_points(&M_RULE_OMIT))),
                Ok(Some(gen)) => {
                    let n: u64 = g.n_p + (g.slots.len() as u64) + xs[i].n_f;
                    match class_rule_ok(pers, st, mode, fe, pushed, cv_r, n, gen) {
                        Err(e) => Err(e),
                        Ok(r) => {
                            let mut o: Vec<EIdx> = out;
                            o.push(r);
                            class_rules_ok(pers, st, mode, fe, pushed, g, rec_cls, cv_gs, cv_r, c, xs, i + 1, o)
                        }
                    }
                }
            },
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/GenRec.lean:462-471 classRecsRulesOk
/// con-leche: ConLeche/Cached/IndRec.lean:413-420 classRecsRulesOkC
/// Lean twin: `proof/ConRon/Arena/Inductives/GenRec.lean:664-678 classRecsRulesOk` — every
/// recursor's generated rules, with its class, from `i` on (the shorter of
/// the two lists decides, as the cited zip does).
#[allow(clippy::too_many_arguments)]
pub fn class_recs_rules_ok(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    fe: &IFEnv,
    pushed: &Vec<NIdx>,
    g: &ClassGen,
    rec_cls: &Vec<u64>,
    cv_gs: &Vec<IConstantVal>,
    i: usize,
    out: Vec<(IConstantVal, TargetMajor, Vec<EIdx>)>,
) -> Result<Vec<(IConstantVal, TargetMajor, Vec<EIdx>)>, CheckError> {
    if i >= cv_gs.len() || i >= rec_cls.len() {
        Ok(out)
    } else {
        let c: u64 = rec_cls[i];
        let xs: Vec<ClassCtor> = if c < g.ctors.len() as u64 {
            class_ctors_dup(&g.ctors[c as usize], 0, Vec::new())
        } else {
            Vec::new()
        };
        match class_rules_ok(pers, st, mode, fe, pushed, g, rec_cls, cv_gs, &cv_gs[i], c, &xs, 0, Vec::new()) {
            Err(e) => Err(e),
            Ok(rhss) => match rec_check::target_major_at(pers, st, &g.cls, c) {
                Err(e) => Err(e),
                Ok(m) => {
                    let mut o: Vec<(IConstantVal, TargetMajor, Vec<EIdx>)> = out;
                    o.push((env::i_constant_val_dup(&cv_gs[i]), m, rhss));
                    class_recs_rules_ok(pers, st, mode, fe, pushed, g, rec_cls, cv_gs, i + 1, o)
                }
            },
        }
    }
}

/// con-leche: none — a `List ClassCtor` copy; Lean shares the list
/// Lean twin: `proof/ConRon/Arena/Inductives/GenRec.lean:64-74 ClassCtor`.
pub fn class_ctors_dup(xs: &Vec<ClassCtor>, i: usize, out: Vec<ClassCtor>) -> Vec<ClassCtor> {
    if i >= xs.len() {
        out
    } else {
        let mut o: Vec<ClassCtor> = out;
        o.push(class_ctor_dup(&xs[i]));
        class_ctors_dup(xs, i + 1, o)
    }
}

/// con-leche: ConLeche/Kernel/Inductives/GenRec.lean:473-481 classStreamRecs
/// con-leche: ConLeche/Cached/IndRec.lean:422-428 classStreamRecsC
/// Lean twin: `proof/ConRon/Arena/Inductives/GenRec.lean:680-688 classStreamRecs` — the
/// stream's recursor constants, checked (`checkConstantValF`), from `i` on.
pub fn class_stream_recs(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    fe: &IFEnv,
    rcs: &Vec<RecShape>,
    i: usize,
    out: Vec<IConstantVal>,
) -> Result<Vec<IConstantVal>, CheckError> {
    if i >= rcs.len() {
        Ok(out)
    } else {
        match checker_base::check_constant_val(pers, st, mode, fe, &rcs[i].cv_r, false) {
            Err(e) => Err(e),
            Ok(()) => {
                let mut o: Vec<IConstantVal> = out;
                o.push(env::i_constant_val_dup(&rcs[i].cv_r));
                class_stream_recs(pers, st, mode, fe, rcs, i + 1, o)
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/GenRec.lean:483-486 classKeyCanon
/// con-leche: ConLeche/Cached/IndBlock.lean:258-260 classKeyCanonC
/// Lean twin: `proof/ConRon/Arena/Inductives/GenRec.lean:690-696 classKeyCanon` — a class
/// key's parameters moved to the block's canonical parameter variables.
pub fn class_key_canon(
    pers: &PersTier,
    st: &mut AState,
    params: &Vec<EIdx>,
    k: &ClassKey,
    i: usize,
    out: Vec<EIdx>,
) -> Result<ClassKey, CheckError> {
    if i >= k.ds.len() {
        Ok(ClassKey {
            ind: k.ind.dup2(),
            lvls: k.lvls.dup2(),
            ds: out,
        })
    } else {
        let x: EIdx = k.ds[i].dup2();
        match rec_check::target_canon_params(pers, st, params, &x) {
            Err(e) => Err(e),
            Ok(y) => {
                let mut o: Vec<EIdx> = out;
                o.push(y);
                class_key_canon(pers, st, params, k, i + 1, o)
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/GenRec.lean:488-494 classNPcOf
/// Lean twin: `proof/ConRon/Arena/Inductives/ClassRead.lean:153-162 classNPcOf` — an
/// inductive's parameter count as the pre-pass reads it: the block's at a
/// member, the stored `IndCaps`' otherwise (`0` at no inductive).
pub fn class_n_pc_of(pers: &PersTier, p: &BlockShape, fe: &IFEnv, i_name: &NIdx) -> u64 {
    if positivity::names_contain(&shape_member_names(p), i_name, 0) {
        p.n_p
    } else {
        match env::ifenv_find(pers, fe, i_name) {
            Some(IConstantInfo::IndInfo(_, caps)) => caps.nparams,
            _ => 0,
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/GenRec.lean:496-501 classSeeds
/// con-leche: ConLeche/Cached/IndPositivity.lean:549-553 classSeedsC
/// Lean twin: `proof/ConRon/Arena/Inductives/GenRec.lean:698-710 classSeeds` — the seeds:
/// every OUTSIDE class in the positivity check's representation, in order.
pub fn class_seeds(
    pers: &PersTier,
    st: &mut AState,
    ctx: &NestCtx,
    holes: &Vec<EIdx>,
    ms: &Vec<TargetMajor>,
    i: usize,
    out: Vec<(NestKey, u64)>,
) -> Result<Vec<(NestKey, u64)>, CheckError> {
    if i >= ms.len() {
        Ok(out)
    } else {
        match ms[i].member {
            Some(_) => class_seeds(pers, st, ctx, holes, ms, i + 1, out),
            None => match positivity::nest_seed_of(pers, st, ctx, holes, &ms[i].ind, &ms[i].lvls, &ms[i].ds, ms[i].n_pc) {
                Err(e) => Err(e),
                Ok(sd) => {
                    let mut o: Vec<(NestKey, u64)> = out;
                    o.push(sd);
                    class_seeds(pers, st, ctx, holes, ms, i + 1, o)
                }
            },
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/GenRec.lean:503-514 classKeyOf
/// con-leche: ConLeche/Cached/IndBlock.lean:262-268 classKeyOfC
/// Lean twin: `proof/ConRon/Arena/Inductives/GenRec.lean:712-725 classKeyOf` — **a class
/// key, made checkable**: moved to the canonical parameter variables, its
/// parameters closed over them.  (Task #119: no longer annotated — the
/// `mode`/`fe` parameters went with it.)
pub fn class_key_of(
    pers: &PersTier,
    st: &mut AState,
    n_p: u64,
    params: &Vec<EIdx>,
    k: &ClassKey,
) -> Result<ClassKey, CheckError> {
    match class_key_canon(pers, st, params, k, 0, Vec::new()) {
        Err(e) => Err(e),
        Ok(k2) => match params_closed(pers, st, &k2.ds, n_p, 0) {
            Err(e) => Err(e),
            Ok(false) => fail(core_types::invalid(code_points(&M_MAJOR_PARAMS))),
            Ok(true) => Ok(k2),
        },
    }
}

/// con-leche: ConLeche/Kernel/Inductives/GenRec.lean:503-514 classKeyOf
/// con-leche: ConLeche/Cached/IndBlock.lean:262-268 classKeyOfC
/// Lean twin: `rd.classes.mapM (classKeyOf p.nP params)`.
pub fn class_keys_of(
    pers: &PersTier,
    st: &mut AState,
    n_p: u64,
    params: &Vec<EIdx>,
    ks: &Vec<ClassKey>,
    i: usize,
    out: Vec<ClassKey>,
) -> Result<Vec<ClassKey>, CheckError> {
    if i >= ks.len() {
        Ok(out)
    } else {
        match class_key_of(pers, st, n_p, params, &ks[i]) {
            Err(e) => Err(e),
            Ok(k) => {
                let mut o: Vec<ClassKey> = out;
                o.push(k);
                class_keys_of(pers, st, n_p, params, ks, i + 1, o)
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/GenRec.lean:516-534 checkBlockClasses
/// con-leche: ConLeche/Cached/IndBlock.lean:349-361 checkBlockClassesC
/// Lean twin: `(Ms.filter (·.member == some t)).length` — the classes at member
/// `t`, counted.
pub fn classes_at_member(ms: &Vec<TargetMajor>, t: u64, i: usize, acc: u64) -> u64 {
    if i >= ms.len() {
        acc
    } else {
        let hit: bool = match ms[i].member {
            Some(u) => u == t,
            None => false,
        };
        if hit {
            classes_at_member(ms, t, i + 1, acc + 1)
        } else {
            classes_at_member(ms, t, i + 1, acc)
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/GenRec.lean:516-534 checkBlockClasses
/// con-leche: ConLeche/Cached/IndBlock.lean:349-361 checkBlockClassesC
/// Lean twin: `(List.range p.k).all fun t => … == 1` — exactly one class per
/// member, from member `t` on.
pub fn one_class_per_member(ms: &Vec<TargetMajor>, k: u64, t: u64) -> bool {
    if t >= k {
        true
    } else if classes_at_member(ms, t, 0, 0) == 1 {
        one_class_per_member(ms, k, t + 1)
    } else {
        false
    }
}

/// con-leche: ConLeche/Kernel/Inductives/GenRec.lean:516-534 checkBlockClasses
/// con-leche: ConLeche/Cached/IndBlock.lean:349-361 checkBlockClassesC
/// Lean twin: `proof/ConRon/Arena/Inductives/GenRec.lean:727-747 checkBlockClasses` — **the
/// classes, read and checked** at the formers' environment `fe`: the
/// pre-pass on the stream's raw recursor types, every class key made
/// checkable, every class checked as a major over the canonical parameters,
/// exactly one class per member.
pub fn check_block_classes(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    fe: &IFEnv,
    p: &BlockShape,
    params: &Vec<EIdx>,
) -> Result<(ClassRead, Vec<TargetMajor>), CheckError> {
    match class_read::class_read(pers, st, p, fe, p.n_p, &p.recs) {
        Err(e) => Err(e),
        Ok(None) => fail(core_types::invalid(code_points(&M_SHAPE))),
        Ok(Some(rd)) => {
            let ks: Vec<ClassKey> = class_read::classes(&rd.slots, 0, Vec::new());
            match class_keys_of(pers, st, p.n_p, params, &ks, 0, Vec::new()) {
                Err(e) => Err(e),
                Ok(keys) => match class_majors(pers, st, mode, fe, p, params, &keys, 0, Vec::new()) {
                    Err(e) => Err(e),
                    Ok(ms) => {
                        if one_class_per_member(&ms, shape_k(p), 0) {
                            Ok((rd, ms))
                        } else {
                            fail(core_types::invalid(code_points(&M_ONE_CLASS)))
                        }
                    }
                },
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/RecCheck.lean:125-129 classFeR
/// con-leche: ConLeche/Kernel/Inductives/BlockInstall.lean:328-336 consBlockRecsBare
/// con-leche: ConLeche/Kernel/Inductives/RecCheck.lean:117-123 consBlockRecsBareF
/// Lean twin: `proof/ConRon/Arena/Inductives/GenRec.lean:749-766 classFeR` — **the
/// rule-less generated recursors consed onto the constructors' environment**
/// (K flag `false`, no rule), pushed
/// TEMPORARILY in place (the module note): each recursor `m` at its record's
/// major index and rule prefix.  Returns the rows the pushes displaced, for
/// `class_fe_r_pop`.
pub fn class_fe_r_push(
    p: &BlockShape,
    cv_gs: &Vec<IConstantVal>,
    rec_cls: &Vec<u64>,
    m: usize,
    fe: IFEnv,
    prevs: Vec<(NIdx, Option<u64>)>,
) -> (IFEnv, Vec<(NIdx, Option<u64>)>) {
    if m >= cv_gs.len() || m >= rec_cls.len() {
        (fe, prevs)
    } else {
        let mut fe2: IFEnv = fe;
        let n: NIdx = cv_gs[m].name.dup2();
        let prev: Option<u64> = env::ifenv_push_temp(
            &mut fe2,
            IConstantInfo::RecInfo(
                env::i_constant_val_dup(&cv_gs[m]),
                block_shape::major_idx_at(p, m as u64),
                block_shape::rule_prefix_at(p, m as u64),
                false,
                Vec::new(),
            ),
        );
        let mut ps: Vec<(NIdx, Option<u64>)> = prevs;
        ps.push((n, prev));
        class_fe_r_push(p, cv_gs, rec_cls, m + 1, fe2, ps)
    }
}

/// con-leche: ConLeche/Kernel/Inductives/RecCheck.lean:125-129 classFeR
/// Lean twin: the inverse of `class_fe_r_push`: the pushes popped in reverse
/// order, every displaced row restored, so the index is the constructors'
/// again exactly.
pub fn class_fe_r_pop(fe: IFEnv, prevs: &Vec<(NIdx, Option<u64>)>, i: usize) -> IFEnv {
    if i == 0 {
        fe
    } else {
        let mut fe2: IFEnv = fe;
        let prev: Option<u64> = match prevs[i - 1].1 {
            Some(r) => Some(r),
            None => None,
        };
        env::ifenv_pop_temp(&mut fe2, &prevs[i - 1].0, prev);
        class_fe_r_pop(fe2, prevs, i - 1)
    }
}

/// con-leche: none — `cvGs.map (·.name)`, the names `class_fe_r_push` pushes
/// Lean twin: the generated recursors' names, in order.
pub fn const_val_names(cvs: &Vec<IConstantVal>, i: usize, out: Vec<NIdx>) -> Vec<NIdx> {
    if i >= cvs.len() {
        out
    } else {
        let mut o: Vec<NIdx> = out;
        o.push(cvs[i].name.dup2());
        const_val_names(cvs, i + 1, o)
    }
}

/// con-leche: ConLeche/Kernel/Inductives/GenRec.lean:543-581 genRecCheck
/// con-leche: ConLeche/Cached/IndRec.lean:432-467 genRecCheckC
/// Lean twin: `Ms.any (·.member.isNone)`.
pub fn some_outside(ms: &Vec<TargetMajor>, i: usize) -> bool {
    if i >= ms.len() {
        false
    } else {
        match ms[i].member {
            None => true,
            Some(_) => some_outside(ms, i + 1),
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/GenRec.lean:543-581 genRecCheck
/// con-leche: ConLeche/Cached/IndRec.lean:432-467 genRecCheckC
/// Lean twin: `(rd.slots.filter ClassSlot.isMinor).length`.
pub fn minor_count(slots: &Vec<ClassSlot>, i: usize, acc: u64) -> u64 {
    if i >= slots.len() {
        acc
    } else if slot_is_minor(&slots[i]) {
        minor_count(slots, i + 1, acc + 1)
    } else {
        minor_count(slots, i + 1, acc)
    }
}

/// con-leche: ConLeche/Kernel/Inductives/GenRec.lean:543-581 genRecCheck
/// con-leche: ConLeche/Cached/IndRec.lean:432-467 genRecCheckC
/// Lean twin: `(ctors.map List.length).sum`.
pub fn ctor_count(xss: &Vec<Vec<ClassCtor>>, i: usize, acc: u64) -> u64 {
    if i >= xss.len() {
        acc
    } else {
        ctor_count(xss, i + 1, acc + (xss[i].len() as u64))
    }
}

/// con-leche: none — `p.formers.map (·.type)`
/// Lean twin: the formers' types, in block order.
pub fn former_types(cvs: &Vec<IConstantVal>, i: usize, out: Vec<EIdx>) -> Vec<EIdx> {
    if i >= cvs.len() {
        out
    } else {
        let mut o: Vec<EIdx> = out;
        o.push(cvs[i].ty.dup2());
        former_types(cvs, i + 1, o)
    }
}

/// con-leche: ConLeche/Kernel/Inductives/GenRec.lean:543-581 genRecCheck
/// con-leche: ConLeche/Cached/IndRec.lean:432-467 genRecCheckC
/// Lean twin: `proof/ConRon/Arena/Inductives/GenRec.lean:768-822 genRecCheck` — **the
/// generated recursor stage**, at the constructors' environment `fe`, on the
/// classes and the positivity check's table: the pins, the stream's recursor
/// types checked, the elimination guard, the classes' table entries and
/// constructors, then generation (`gen_rec_generate`).  Threads the index by
/// value (the module note).
#[allow(clippy::too_many_arguments)]
pub fn gen_rec_check(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    fe: IFEnv,
    p: &BlockShape,
    nested_bit: bool,
    params: &Vec<EIdx>,
    tbl: &Vec<NestCtorNf>,
    rd: &ClassRead,
    ms: &Vec<TargetMajor>,
    block: &Vec<IConstantInfo>,
) -> Result<(IFEnv, Vec<(IConstantVal, TargetMajor, Vec<EIdx>)>), CheckError> {
    match rec_check::target_rec_pins(pers, st, p, block) {
        Err(e) => Err(e),
        Ok(()) => match class_stream_recs(pers, st, mode, &fe, &p.recs, 0, Vec::new()) {
            Err(e) => Err(e),
            Ok(cv_ris) => {
                if shape_k(p) == 0 {
                    fail(core_types::invalid(code_points(&M_NO_FAMILY)))
                } else if p.large {
                    let nb: bool = if nested_bit { true } else { some_outside(ms, 0) };
                    match block_large_elim_allowed(pers, st, p, nb) {
                        Err(e) => Err(e),
                        Ok(false) => fail(core_types::invalid(code_points(&M_ELIM))),
                        Ok(true) => gen_rec_classes(pers, st, mode, fe, p, params, tbl, rd, ms, cv_ris),
                    }
                } else {
                    gen_rec_classes(pers, st, mode, fe, p, params, tbl, rd, ms, cv_ris)
                }
            }
        },
    }
}

/// con-leche: ConLeche/Kernel/Inductives/GenRec.lean:543-581 genRecCheck
/// con-leche: ConLeche/Cached/IndRec.lean:432-467 genRecCheckC
/// Lean twin: `proof/ConRon/Arena/Inductives/GenRec.lean:768-822 genRecCheck` — per class
/// and constructor: the table's entries, the datum, the inductive hypotheses,
/// node agreement; every minor premise a constructor's.
#[allow(clippy::too_many_arguments)]
pub fn gen_rec_classes(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    fe: IFEnv,
    p: &BlockShape,
    params: &Vec<EIdx>,
    tbl: &Vec<NestCtorNf>,
    rd: &ClassRead,
    ms: &Vec<TargetMajor>,
    cv_ris: Vec<IConstantVal>,
) -> Result<(IFEnv, Vec<(IConstantVal, TargetMajor, Vec<EIdx>)>), CheckError> {
    let formers: Vec<IConstantVal> = block_shape::shape_formers(&p.members, 0, Vec::new());
    let former_tys: Vec<EIdx> = former_types(&formers, 0, Vec::new());
    match classes_nfs(pers, st, mode, &fe, p, &former_tys, tbl, ms, 0, Vec::new()) {
        Err(e) => Err(e),
        Ok(ms2) => match classes_ctors(pers, st, mode, &fe, p, &former_tys, rd, &ms2, 0, Vec::new()) {
            Err(e) => Err(e),
            Ok(ctors) => {
                if minor_count(&rd.slots, 0, 0) != ctor_count(&ctors, 0, 0) {
                    fail(core_types::invalid(code_points(&M_MINOR_COUNT)))
                } else {
                    match class_former_tys(pers, st, mode, &fe, &formers, &ms2, 0, Vec::new()) {
                        Err(e) => Err(e),
                        Ok(former_tys_c) => match struct_parts::struct_elim_level(pers, st, &p.elim, p.large) {
                            Err(e) => Err(e),
                            Ok(elim) => {
                                let g0: ClassGen = ClassGen {
                                    n_p: p.n_p,
                                    params: env::eidx_vec_dup(params),
                                    cls: ms2,
                                    former_tys: former_tys_c,
                                    slots: class_read::slots_dup(&rd.slots, 0, Vec::new()),
                                    ctors,
                                    elim,
                                    pre: Vec::new(),
                                };
                                gen_rec_generate(pers, st, mode, fe, p, rd, cv_ris, g0)
                            }
                        },
                    }
                }
            }
        },
    }
}

/// con-leche: ConLeche/Kernel/Inductives/GenRec.lean:543-581 genRecCheck
/// con-leche: ConLeche/Cached/IndRec.lean:432-467 genRecCheckC
/// Lean twin: `proof/ConRon/Arena/Inductives/GenRec.lean:768-822 genRecCheck` —
/// generation: the prefix, every recursor's type checked and compared, the
/// rule-less recursors pushed, the flush entering them, every rule
/// installed, the recursors popped and the flush leaving them.  The rule-less
/// recursors' environment is `classFeR` in the specification (pushed, as
/// here) and the overlay `classFeROvl` in `genRecCheckC`, which answers
/// `find?` as the push would; the port's temporary push and pop is its own
/// answer to the same index copy.
#[allow(clippy::too_many_arguments)]
pub fn gen_rec_generate(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    fe: IFEnv,
    p: &BlockShape,
    rd: &ClassRead,
    cv_ris: Vec<IConstantVal>,
    g0: ClassGen,
) -> Result<(IFEnv, Vec<(IConstantVal, TargetMajor, Vec<EIdx>)>), CheckError> {
    match prefix_binders(pers, st, &g0) {
        Err(e) => Err(e),
        Ok(None) => fail(core_types::internal(code_points(&M_PREFIX))),
        Ok(Some(pre)) => {
            let mut g: ClassGen = g0;
            g.pre = pre;
            match class_rec_tys_ok(pers, st, mode, &fe, &g, shape_k(p), &p.recs, &cv_ris, &rd.rec_cls, 0, Vec::new()) {
                Err(e) => Err(e),
                Ok(cv_gs) => {
                    let pushed = class_fe_r_push(p, &cv_gs, &rd.rec_cls, 0, fe, Vec::new());
                    let fe_r: IFEnv = pushed.0;
                    let prevs: Vec<(NIdx, Option<u64>)> = pushed.1;
                    let names: Vec<NIdx> = const_val_names(&cv_gs, 0, Vec::new());
                    core::flush_caches(st);
                    match class_recs_rules_ok(pers, st, mode, &fe_r, &names, &g, &rd.rec_cls, &cv_gs, 0, Vec::new()) {
                        Err(e) => Err(e),
                        Ok(out) => {
                            let fe2: IFEnv = class_fe_r_pop(fe_r, &prevs, prevs.len());
                            core::flush_caches(st);
                            Ok((fe2, out))
                        }
                    }
                }
            }
        }
    }
}
