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
//! * **The shadow operations are the core's, with `shadowOpsC`'s flushes**
//!   (`arena::inductives::rec_check`'s module note): `so.flush` is
//!   `core::flush_caches`, and the rule stage's `opsRuleR feR` is the core at
//!   the rule-less recursors' visibility bound with a flush LEAVING its
//!   `inferType` (`sharedOpsRuleR`; the stage never calls its `annotate`).
//! * **`feR` is `fe` with the rule-less recursors pushed TEMPORARILY**
//!   (`env::ifenv_push_temp`) and popped once the rules are typed, so `feT`
//!   (the constructors' environment) is the same index at its lower
//!   visibility bound — `consBlockRecsBareF`'s cons onto a copy, without the
//!   copy (task #97-P6-5's lever 4).  `genRecCheck` threads the index by
//!   value and hands it back.
//! * **`recOf` is `classRecOf recCls cvGs`, specialised**; `classRead`'s
//!   `nPc` is `classNPcOf p fe₁`.
//! * **`ClassGen.bm` is a field**, computed once from `elim` where con-leche
//!   recomputes the pure `⟨Level.zeronessOf g.elim⟩` at every use.
//! * **A `getD … default` out of range** reads the interned default
//!   (`.bvar 0` for a term, `target_major_default` for a class); the stage
//!   never forms such an index.

use super::block_parts;
use super::block_parts::{shape_k, shape_member_names, BlockShape, RecShape};
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
    intern_e_sort, read_level_m, view_const, AState,
};
use crate::arena::store::PersTier;
use crate::kernel::core_types;
use crate::kernel::core_types::{code_points, CheckError};
use crate::kernel::env::CheckMode;
use crate::kernel::expr;
use crate::kernel::expr::BinderMeta;
use crate::kernel::level;
use crate::kernel::prop_when;
use crate::ron::hashmap::{Dup, Eq2};

// ---------------------------------------------------------------------------
// The messages (con-leche's own, interpolation dropped)
// ---------------------------------------------------------------------------

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
/// `reserved basis name`, as code points.
pub const M_RESERVED: [u32; 19] = [
    114, 101, 115, 101, 114, 118, 101, 100, 32, 98, 97, 115, 105, 115, 32, 110, 97, 109, 101,
];
/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `reserved projection name`, as code points.
pub const M_RESERVED_PROJ: [u32; 24] = [
    114, 101, 115, 101, 114, 118, 101, 100, 32, 112, 114, 111, 106, 101, 99, 116, 105, 111, 110,
    32, 110, 97, 109, 101,
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
/// `generated recursor: a rule of  does not annotate its λ-binders with the family's elimination datum`, as code points.
pub const M_RULE_PW: [u32; 98] = [
    103, 101, 110, 101, 114, 97, 116, 101, 100, 32, 114, 101, 99, 117, 114, 115, 111, 114, 58, 32,
    97, 32, 114, 117, 108, 101, 32, 111, 102, 32, 32, 100, 111, 101, 115, 32, 110, 111, 116, 32,
    97, 110, 110, 111, 116, 97, 116, 101, 32, 105, 116, 115, 32, 955, 45, 98, 105, 110, 100, 101,
    114, 115, 32, 119, 105, 116, 104, 32, 116, 104, 101, 32, 102, 97, 109, 105, 108, 121, 39, 115,
    32, 101, 108, 105, 109, 105, 110, 97, 116, 105, 111, 110, 32, 100, 97, 116, 117, 109,
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

/// con-leche: ConLeche/Kernel/Inductives/GenRec.lean:60-66 ClassField
/// Lean twin: `proof/ConRon/Arena/Inductives/GenRec.lean:46-52 ClassField` — a field of a
/// class's constructor, as the generator reads it: ordinary, or recursive at
/// class `cls` with a telescope of `tele` binders.
pub enum ClassField {
    Ordinary,
    Recursive(u64, u64),
}

/// con-leche: ConLeche/Kernel/Inductives/GenRec.lean:60-66 ClassField
/// The copy.
pub fn class_field_dup(k: &ClassField) -> ClassField {
    match k {
        ClassField::Ordinary => ClassField::Ordinary,
        ClassField::Recursive(c, t) => ClassField::Recursive(*c, *t),
    }
}

/// con-leche: none — a `List ClassField` copy; Lean shares the list
/// Lean twin: `proof/ConRon/Arena/Inductives/GenRec.lean:46-52 ClassField`.
pub fn class_fields_dup(ks: &Vec<ClassField>, i: usize, out: Vec<ClassField>) -> Vec<ClassField> {
    if i >= ks.len() {
        out
    } else {
        let mut o: Vec<ClassField> = out;
        o.push(class_field_dup(&ks[i]));
        class_fields_dup(ks, i + 1, o)
    }
}

/// con-leche: ConLeche/Kernel/Inductives/GenRec.lean:68-81 ClassCtor
/// Lean twin: `proof/ConRon/Arena/Inductives/GenRec.lean:54-64 ClassCtor` — a class's
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

/// con-leche: ConLeche/Kernel/Inductives/GenRec.lean:68-81 ClassCtor
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

/// con-leche: ConLeche/Kernel/Inductives/GenRec.lean:83-86 closeLams
/// Lean twin: `proof/ConRon/Arena/Inductives/GenRec.lean:66-74 closeLams` — close a
/// telescope of `λ`s opened at `i ..< i + bs.length` (`closeTelescope`'s
/// twin), innermost first.
pub fn close_lams(
    pers: &PersTier,
    st: &mut AState,
    bs: &Vec<(EIdx, BinderMeta)>,
    k: usize,
    i: u64,
    body: &EIdx,
) -> Result<EIdx, CheckError> {
    if k >= bs.len() {
        Ok(body.dup2())
    } else {
        match close_lams(pers, st, bs, k + 1, i + 1, body) {
            Err(e) => Err(e),
            Ok(inner) => match expr_ops::abstract1_fast(pers, st, CORE_WALK_FUEL, &inner, i, 0) {
                Err(e) => Err(e),
                Ok(closed) => {
                    let dom: EIdx = bs[k].0.dup2();
                    let bm: BinderMeta = expr::binder_meta_dup(&bs[k].1);
                    intern_e_lam(pers, st, dom, closed, bm)
                }
            },
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/GenRec.lean:88-100 ClassGen
/// Lean twin: `proof/ConRon/Arena/Inductives/GenRec.lean:76-92 ClassGen` — what
/// generation reads: the block, the classes, the layout, the constructors,
/// the elimination level, the generated prefix; `bm` is `ClassGen.bm`,
/// computed once (the module note).
pub struct ClassGen {
    pub n_p: u64,
    pub params: Vec<EIdx>,
    pub cls: Vec<TargetMajor>,
    pub former_tys: Vec<EIdx>,
    pub slots: Vec<ClassSlot>,
    pub ctors: Vec<Vec<ClassCtor>>,
    pub elim: LIdx,
    pub bm: BinderMeta,
    pub pre: Vec<(EIdx, BinderMeta)>,
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

/// con-leche: ConLeche/Kernel/Inductives/GenRec.lean:102-104 classBinder
/// Lean twin: `proof/ConRon/Arena/Inductives/GenRec.lean:102-107 classBinder` — the binders
/// of opened variables at the default datum (`.never`), `xs.map classBinder`.
pub fn class_binders(
    pers: &PersTier,
    st: &AState,
    xs: &Vec<EIdx>,
    i: usize,
    out: Vec<(EIdx, BinderMeta)>,
) -> Result<Vec<(EIdx, BinderMeta)>, CheckError> {
    if i >= xs.len() {
        Ok(out)
    } else {
        match expr_ops::fvar_type_d(pers, st, &xs[i]) {
            Err(e) => Err(e),
            Ok(t) => {
                let mut o: Vec<(EIdx, BinderMeta)> = out;
                o.push((t, expr::binder_meta(prop_when::never())));
                class_binders(pers, st, xs, i + 1, o)
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/GenRec.lean:106-111 ClassGen.bm
/// Lean twin: `proof/ConRon/Arena/Inductives/GenRec.lean:89-90 ClassGen.bm` — **the
/// generated binders' datum**: the elimination level's zero-ness.
pub fn class_gen_bm(pers: &PersTier, st: &mut AState, elim: &LIdx) -> Result<BinderMeta, CheckError> {
    match read_level_m(pers, st, elim) {
        Err(e) => Err(e),
        Ok(l) => Ok(expr::binder_meta(level::zeroness_of(&l))),
    }
}

/// con-leche: ConLeche/Kernel/Inductives/GenRec.lean:113-114 ClassGen.binder
/// Lean twin: `proof/ConRon/Arena/Inductives/GenRec.lean:116-121 ClassGen.binder` — the
/// generated binders of opened variables, `xs.map g.binder`, appended to `out`.
pub fn gen_binders(
    pers: &PersTier,
    st: &AState,
    g: &ClassGen,
    xs: &Vec<EIdx>,
    i: usize,
    out: Vec<(EIdx, BinderMeta)>,
) -> Result<Vec<(EIdx, BinderMeta)>, CheckError> {
    if i >= xs.len() {
        Ok(out)
    } else {
        match expr_ops::fvar_type_d(pers, st, &xs[i]) {
            Err(e) => Err(e),
            Ok(t) => {
                let mut o: Vec<(EIdx, BinderMeta)> = out;
                o.push((t, expr::binder_meta_dup(&g.bm)));
                gen_binders(pers, st, g, xs, i + 1, o)
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/GenRec.lean:116-117 ClassGen.slotVar
/// Lean twin: `proof/ConRon/Arena/Inductives/GenRec.lean:123-127 ClassGen.slotVar` — the
/// prefix variable of slot `s`.
pub fn slot_var(pers: &PersTier, st: &mut AState, g: &ClassGen, s: u64) -> Result<EIdx, CheckError> {
    match positivity::sort_zero(pers, st) {
        Err(e) => Err(e),
        Ok(z) => intern_e_fvar(pers, st, g.n_p + s, z),
    }
}

/// con-leche: ConLeche/Kernel/Inductives/GenRec.lean:119-121 ClassGen.motVar
/// Lean twin: `proof/ConRon/Arena/Inductives/GenRec.lean:129-132 ClassGen.motVar` — class
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

/// con-leche: ConLeche/Kernel/Inductives/GenRec.lean:123-128 ClassGen.major
/// Lean twin: `proof/ConRon/Arena/Inductives/GenRec.lean:134-147 ClassGen.major` — class
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
                Ok(Some(ty)) => match checker_base::open_pis_at_fvars_f(pers, st, ci.n_idx, &ty, d) {
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

/// con-leche: ConLeche/Kernel/Inductives/GenRec.lean:130-133 ClassGen.motiveTy
/// Lean twin: `proof/ConRon/Arena/Inductives/GenRec.lean:149-159 ClassGen.motiveTy` — class
/// `c`'s motive type at depth `d`: `∀ ı⃗ (t : I D⃗ ı⃗), Sort ℓ`.
pub fn motive_ty(pers: &PersTier, st: &mut AState, g: &ClassGen, c: u64, d: u64) -> Result<Option<EIdx>, CheckError> {
    match gen_major(pers, st, g, c, d) {
        Err(e) => Err(e),
        Ok(None) => Ok(None),
        Ok(Some((ifs, maj))) => match intern_e_sort(pers, st, g.elim.dup2()) {
            Err(e) => Err(e),
            Ok(srt) => match intern_e_forall_e(pers, st, maj, srt, expr::binder_meta(prop_when::never())) {
                Err(e) => Err(e),
                Ok(body) => match class_binders(pers, st, &ifs, 0, Vec::new()) {
                    Err(e) => Err(e),
                    Ok(bs) => match close_telescope(pers, st, &bs, 0, d, &body) {
                        Err(e) => Err(e),
                        Ok(r) => Ok(Some(r)),
                    },
                },
            },
        },
    }
}

/// con-leche: ConLeche/Kernel/Inductives/GenRec.lean:135-141 ClassGen.ihParts
/// Lean twin: `proof/ConRon/Arena/Inductives/GenRec.lean:161-173 ClassGen.ihParts` — the
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
    match checker_base::open_pis_at_fvars_f(pers, st, tele, w, d) {
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

/// con-leche: ConLeche/Kernel/Inductives/GenRec.lean:143-163 ClassGen.minorTy
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

/// con-leche: ConLeche/Kernel/Inductives/GenRec.lean:143-163 ClassGen.minorTy
/// Lean twin: `proof/ConRon/Arena/Inductives/GenRec.lean:175-222 ClassGen.minorTy` — the
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
    out: Vec<(EIdx, BinderMeta)>,
) -> Result<Option<Vec<(EIdx, BinderMeta)>>, CheckError> {
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
                                        Ok(bs) => match close_telescope(pers, st, &bs, 0, e, &body) {
                                            Err(er) => Err(er),
                                            Ok(ih) => {
                                                let mut o: Vec<(EIdx, BinderMeta)> = out;
                                                o.push((ih, expr::binder_meta_dup(&g.bm)));
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

/// con-leche: ConLeche/Kernel/Inductives/GenRec.lean:143-163 ClassGen.minorTy
/// Lean twin: `proof/ConRon/Arena/Inductives/GenRec.lean:175-222 ClassGen.minorTy` —
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
        Ok(ci) => match checker_base::open_pis_at_fvars_f(pers, st, x.n_f, &x.ty_d, d) {
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

/// con-leche: ConLeche/Kernel/Inductives/GenRec.lean:143-163 ClassGen.minorTy
/// Lean twin: `proof/ConRon/Arena/Inductives/GenRec.lean:175-222 ClassGen.minorTy` — the
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
    ihs: Vec<(EIdx, BinderMeta)>,
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
                                        let bs: Vec<(EIdx, BinderMeta)> = expr_ops::binder_copy_from(&ihs, 0, fbs);
                                        match close_telescope(pers, st, &bs, 0, d, &concl) {
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

/// con-leche: ConLeche/Kernel/Inductives/GenRec.lean:165-178 ClassGen.prefixBinders
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

/// con-leche: ConLeche/Kernel/Inductives/GenRec.lean:165-178 ClassGen.prefixBinders
/// Lean twin: `(g.ctors.getD c []).find? (·.cv.name == C)`.
pub fn find_class_ctor(g: &ClassGen, c: u64, cn: &NIdx) -> Option<ClassCtor> {
    if c < g.ctors.len() as u64 {
        find_class_ctor_in(&g.ctors[c as usize], cn, 0)
    } else {
        None
    }
}

/// con-leche: ConLeche/Kernel/Inductives/GenRec.lean:165-178 ClassGen.prefixBinders
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

/// con-leche: ConLeche/Kernel/Inductives/GenRec.lean:165-178 ClassGen.prefixBinders
/// Lean twin: `proof/ConRon/Arena/Inductives/GenRec.lean:224-253 ClassGen.prefixBinders` —
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

/// con-leche: ConLeche/Kernel/Inductives/GenRec.lean:165-178 ClassGen.prefixBinders
/// Lean twin: `proof/ConRon/Arena/Inductives/GenRec.lean:224-253 ClassGen.prefixBinders` —
/// the slot binders from `s` on (each at depth `nP + s`).
pub fn slot_binders(
    pers: &PersTier,
    st: &mut AState,
    g: &ClassGen,
    s: usize,
    out: Vec<(EIdx, BinderMeta)>,
) -> Result<Option<Vec<(EIdx, BinderMeta)>>, CheckError> {
    if s >= g.slots.len() {
        Ok(Some(out))
    } else {
        match slot_binder(pers, st, g, s) {
            Err(e) => Err(e),
            Ok(None) => Ok(None),
            Ok(Some(ty)) => {
                let mut o: Vec<(EIdx, BinderMeta)> = out;
                o.push((ty, expr::binder_meta_dup(&g.bm)));
                slot_binders(pers, st, g, s + 1, o)
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/GenRec.lean:165-178 ClassGen.prefixBinders
/// Lean twin: `proof/ConRon/Arena/Inductives/GenRec.lean:224-253 ClassGen.prefixBinders` —
/// the prefix binders: the parameters, then every slot in the stream's order.
pub fn prefix_binders(pers: &PersTier, st: &mut AState, g: &ClassGen) -> Result<Option<Vec<(EIdx, BinderMeta)>>, CheckError> {
    match gen_binders(pers, st, g, &g.params, 0, Vec::new()) {
        Err(e) => Err(e),
        Ok(pbs) => slot_binders(pers, st, g, 0, pbs),
    }
}

/// con-leche: ConLeche/Kernel/Inductives/GenRec.lean:180-187 classGenRecTy
/// Lean twin: `proof/ConRon/Arena/Inductives/GenRec.lean:255-269 classGenRecTy` — **the
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
                    let mut bs2: Vec<(EIdx, BinderMeta)> = bs;
                    bs2.push((maj, expr::binder_meta_dup(&g.bm)));
                    match mot_var(pers, st, g, c) {
                        Err(e) => Err(e),
                        Ok(mv) => {
                            let mut args: Vec<EIdx> = env::eidx_vec_dup(&ifs);
                            args.push(t);
                            match expr_ops::mk_app_n(pers, st, &mv, &args) {
                                Err(e) => Err(e),
                                Ok(body) => match close_telescope(pers, st, &bs2, 0, 0, &body) {
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

/// con-leche: ConLeche/Kernel/Inductives/GenRec.lean:189-212 classGenRule
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

/// con-leche: ConLeche/Kernel/Inductives/GenRec.lean:189-212 classGenRule
/// Lean twin: `match sl with | .minor c' C _ => c' == c && C == x.cv.name | _ => false`.
pub fn minor_is(s: &ClassSlot, c: u64, cn: &NIdx) -> bool {
    match s {
        ClassSlot::Minor(c2, n2, _) => *c2 == c && n2.eq2(cn),
        ClassSlot::Motive(_) => false,
    }
}

/// con-leche: ConLeche/Kernel/Inductives/GenRec.lean:189-212 classGenRule
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

/// con-leche: ConLeche/Kernel/Inductives/GenRec.lean:538-543 classRecOf
/// Lean twin: `proof/ConRon/Arena/Inductives/GenRec.lean:271-277 classRecOf` — the
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

/// con-leche: ConLeche/Kernel/Inductives/GenRec.lean:189-212 classGenRule
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

/// con-leche: ConLeche/Kernel/Inductives/GenRec.lean:189-212 classGenRule
/// Lean twin: `proof/ConRon/Arena/Inductives/GenRec.lean:279-332 classGenRule` — one
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
                            Ok(bs) => match close_lams(pers, st, &bs, 0, r_p + x.n_f, &app) {
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

/// con-leche: ConLeche/Kernel/Inductives/GenRec.lean:189-212 classGenRule
/// Lean twin: `proof/ConRon/Arena/Inductives/GenRec.lean:279-332 classGenRule` — **the
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
        Some(s) => match checker_base::open_pis_at_fvars_f(pers, st, x.n_f, &x.ty_d, r_p) {
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

/// con-leche: ConLeche/Kernel/Inductives/GenRec.lean:189-212 classGenRule
/// Lean twin: `proof/ConRon/Arena/Inductives/GenRec.lean:279-332 classGenRule` — the
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
                    Ok(bs) => match close_lams(pers, st, &bs, 0, 0, &body) {
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

/// con-leche: ConLeche/Kernel/Inductives/GenRec.lean:218-221 ClassSlot.isMinor
/// Lean twin: `proof/ConRon/Arena/Inductives/GenRec.lean:336-340 ClassSlot.isMinor` — a
/// minor premise's slot.
pub fn slot_is_minor(s: &ClassSlot) -> bool {
    match s {
        ClassSlot::Minor(_, _, _) => true,
        ClassSlot::Motive(_) => false,
    }
}

/// con-leche: ConLeche/Kernel/Inductives/GenRec.lean:223-232 classMinorSlot
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

/// con-leche: ConLeche/Kernel/Inductives/GenRec.lean:223-232 classMinorSlot
/// Lean twin: `proof/ConRon/Arena/Inductives/GenRec.lean:342-352 classMinorSlot` — the minor
/// premise slot of class `c`'s constructor `cn`: exactly one.
pub fn class_minor_slot(rd: &ClassRead, c: u64, cn: &NIdx) -> Result<(u64, Vec<(u64, u64)>), CheckError> {
    let hits: Vec<(u64, Vec<(u64, u64)>)> = minor_hits(&rd.slots, c, cn, 0, Vec::new());
    if hits.len() == 1 {
        Ok((hits[0].0, class_read::pairs_dup(&hits[0].1, 0, Vec::new())))
    } else {
        fail(core_types::invalid(code_points(&M_MINOR_SLOT)))
    }
}

/// con-leche: ConLeche/Kernel/Inductives/GenRec.lean:234-254 classFieldsOf
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

/// con-leche: ConLeche/Kernel/Inductives/GenRec.lean:234-254 classFieldsOf
/// Lean twin: `proof/ConRon/Arena/Inductives/GenRec.lean:354-375 classFieldsOf` — **the
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

/// con-leche: ConLeche/Kernel/Inductives/GenRec.lean:256-271 classNodesAgree
/// Lean twin: `proof/ConRon/Arena/Inductives/GenRec.lean:377-395 classNodesAgree` — **node
/// agreement at one recursive field** (K.53′): at every entry of the
/// constructor from `j` on, field `i` (opened at the datum's variables `fvs`)
/// passes `targetK53` against the inductive hypothesis's class `mc`.
#[allow(clippy::too_many_arguments)]
pub fn class_nodes_agree(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    vis: u64,
    fe: &IFEnv,
    p: &BlockShape,
    former_tys: &Vec<EIdx>,
    mc: &TargetMajor,
    tele: &Vec<(EIdx, BinderMeta)>,
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
                    Some(f) => match rec_check::target_k53(pers, st, mode, vis, fe, p, former_tys, mc, tele, leaf, &f) {
                        Err(e) => Err(e),
                        Ok(false) => fail(core_types::invalid(code_points(&M_NODES))),
                        Ok(true) => class_nodes_agree(pers, st, mode, vis, fe, p, former_tys, mc, tele, leaf, fvs, i, es, j + 1),
                    },
                }
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/GenRec.lean:273-277 classLeafAt
/// Lean twin: `proof/ConRon/Arena/Inductives/GenRec.lean:397-405 classLeafAt` — a walked
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

/// con-leche: ConLeche/Kernel/Inductives/GenRec.lean:279-293 classFieldsAgree
/// Lean twin: `proof/ConRon/Arena/Inductives/GenRec.lean:407-427 classFieldsAgree` — node
/// agreement at every recursive field of the datum from field `i` on.
#[allow(clippy::too_many_arguments)]
pub fn class_fields_agree(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    vis: u64,
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
            ClassField::Ordinary => class_fields_agree(pers, st, mode, vis, fe, p, former_tys, ms, fvs, es, i + 1, ks),
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
                                    pers, st, mode, vis, fe, p, former_tys, &mt, &tele_b, &leaf, fvs, i, es, 0,
                                ) {
                                    Err(e) => Err(e),
                                    Ok(()) => class_fields_agree(pers, st, mode, vis, fe, p, former_tys, ms, fvs, es, i + 1, ks),
                                },
                            },
                        },
                    },
                },
            },
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/GenRec.lean:295-313 classCtorOf
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

/// con-leche: ConLeche/Kernel/Inductives/GenRec.lean:295-313 classCtorOf
/// Lean twin: `proof/ConRon/Arena/Inductives/GenRec.lean:429-453 classCtorOf` — **one
/// constructor of class `c`, read for the generator**: its entries in the
/// class's table (the first the DATUM), the minor premise's inductive
/// hypotheses against the datum's recursive fields, node agreement at every
/// entry, and the constructor's declared type at the class.
#[allow(clippy::too_many_arguments)]
pub fn class_ctor_of(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    vis: u64,
    fe: &IFEnv,
    p: &BlockShape,
    former_tys: &Vec<EIdx>,
    rd: &ClassRead,
    ms: &Vec<TargetMajor>,
    c: u64,
    c_a: &(IConstantVal, u64),
) -> Result<ClassCtor, CheckError> {
    match rec_check::target_major_at(pers, st, ms, c) {
        Err(e) => Err(e),
        Ok(m) => {
            let es: Vec<NestCtorNf> = nfs_of_ctor(&m.nfs, &c_a.0.name, 0, Vec::new());
            if es.len() == 0 {
                fail(core_types::internal(code_points(&M_NO_ENTRY)))
            } else {
                let e0: EIdx = es[0].ty.dup2();
                match class_minor_slot(rd, c, &c_a.0.name) {
                    Err(e) => Err(e),
                    Ok((_, ihs)) => {
                        match checker_base::open_pis_at_fvars_f(pers, st, c_a.1, &e0, p.n_p + shape_k(p)) {
                            Err(e) => Err(e),
                            Ok(None) => fail(core_types::internal(code_points(&M_DATUM))),
                            Ok(Some((fvs, _))) => match class_fields_of(pers, st, p, &ihs, 0, &fvs, Vec::new()) {
                                Err(e) => Err(e),
                                Ok(kinds) => match class_fields_agree(pers, st, mode, vis, fe, p, former_tys, ms, &fvs, &es, 0, &kinds) {
                                    Err(e) => Err(e),
                                    Ok(()) => match rec_check::target_ctor_at(pers, st, &m, &c_a.0) {
                                        Err(e) => Err(e),
                                        Ok(t0) => match inst_pis_with(pers, st, &m.ds, 0, &t0) {
                                            Err(e) => Err(e),
                                            Ok(None) => fail(core_types::internal(code_points(&M_CTOR_PARAMS))),
                                            Ok(Some(ty_d)) => Ok(ClassCtor {
                                                cv: env::i_constant_val_dup(&c_a.0),
                                                n_f: c_a.1,
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

/// con-leche: ConLeche/Kernel/Inductives/GenRec.lean:315-323 classCtorsOf
/// Lean twin: `proof/ConRon/Arena/Inductives/GenRec.lean:455-464 classCtorsOf` — every
/// constructor of class `c` from `i` on.
#[allow(clippy::too_many_arguments)]
pub fn class_ctors_of(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    vis: u64,
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
        match class_ctor_of(pers, st, mode, vis, fe, p, former_tys, rd, ms, c, &cs[i]) {
            Err(e) => Err(e),
            Ok(x) => {
                let mut o: Vec<ClassCtor> = out;
                o.push(x);
                class_ctors_of(pers, st, mode, vis, fe, p, former_tys, rd, ms, c, cs, i + 1, o)
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/GenRec.lean:325-332 classesCtors
/// Lean twin: `proof/ConRon/Arena/Inductives/GenRec.lean:466-475 classesCtors` — every
/// class's constructors, from class `c` on.
#[allow(clippy::too_many_arguments)]
pub fn classes_ctors(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    vis: u64,
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
        let cs: Vec<(IConstantVal, u64)> = block_parts::ctors_dup(&ms[c].ctors, 0, Vec::new());
        match class_ctors_of(pers, st, mode, vis, fe, p, former_tys, rd, ms, c as u64, &cs, 0, Vec::new()) {
            Err(e) => Err(e),
            Ok(xs) => {
                let mut o: Vec<Vec<ClassCtor>> = out;
                o.push(xs);
                classes_ctors(pers, st, mode, vis, fe, p, former_tys, rd, ms, c + 1, o)
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/GenRec.lean:334-344 classMajors
/// Lean twin: `proof/ConRon/Arena/Inductives/GenRec.lean:477-490 classMajors` — every class
/// checked as a major (`targetMajorOf`, `targetMajorPins`), over the block's
/// canonical parameters `pfvs`.
#[allow(clippy::too_many_arguments)]
pub fn class_majors(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    fe: &IFEnv,
    p: &BlockShape,
    ctors_as: &Vec<Vec<(IConstantVal, u64)>>,
    pfvs: &Vec<EIdx>,
    keys: &Vec<ClassKey>,
    i: usize,
    out: Vec<TargetMajor>,
) -> Result<Vec<TargetMajor>, CheckError> {
    if i >= keys.len() {
        Ok(out)
    } else {
        let vis: u64 = fe.visible_below;
        match intern_e_const(pers, st, keys[i].ind.dup2(), keys[i].lvls.dup2()) {
            Err(e) => Err(e),
            Ok(hd) => match expr_ops::mk_app_n(pers, st, &hd, &keys[i].ds) {
                Err(e) => Err(e),
                Ok(mty) => match rec_check::target_major_of(pers, st, vis, fe, p, ctors_as, pfvs, pfvs, &mty) {
                    Err(e) => Err(e),
                    Ok(m) => match rec_check::target_major_pins(pers, st, mode, vis, fe, p.n_p, &m) {
                        Err(e) => Err(e),
                        Ok(()) => {
                            let mut o: Vec<TargetMajor> = out;
                            o.push(m);
                            class_majors(pers, st, mode, fe, p, ctors_as, pfvs, keys, i + 1, o)
                        }
                    },
                },
            },
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/GenRec.lean:346-353 classesNfs
/// Lean twin: `proof/ConRon/Arena/Inductives/GenRec.lean:492-500 classesNfs` — every class
/// with its entries of the table (`targetMajorNfs`), from `i` on.
#[allow(clippy::too_many_arguments)]
pub fn classes_nfs(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    vis: u64,
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
        match rec_check::target_major_nfs(pers, st, mode, vis, fe, p, former_tys, &m.pfvs, &m.lvls, &m.ds, &m.ctors, tbl) {
            Err(e) => Err(e),
            Ok(es) => {
                let mut m2: TargetMajor = m;
                m2.nfs = es;
                let mut o: Vec<TargetMajor> = out;
                o.push(m2);
                classes_nfs(pers, st, mode, vis, fe, p, former_tys, tbl, ms, i + 1, o)
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/GenRec.lean:355-362 classFormerTy
/// Lean twin: `proof/ConRon/Arena/Inductives/GenRec.lean:502-514 classFormerTy` — a class's
/// former type: a member's own, an outside class's stored former at the
/// class's levels.
pub fn class_former_ty(
    pers: &PersTier,
    st: &mut AState,
    fe: &IFEnv,
    cv_tas: &Vec<IConstantVal>,
    m: &TargetMajor,
) -> Result<EIdx, CheckError> {
    match m.member {
        Some(t) => {
            if t < cv_tas.len() as u64 {
                Ok(cv_tas[t as usize].ty.dup2())
            } else {
                intern_e_bvar(pers, st, 0)
            }
        }
        None => match positivity::ind_cv_of(fe.visible_below, fe, &m.ind) {
            None => fail(core_types::internal(code_points(&M_FORMER))),
            Some(cv) => expr_ops::inst_lp_fast(pers, st, CORE_WALK_FUEL, &cv.level_params, &m.lvls, &cv.ty),
        },
    }
}

/// con-leche: ConLeche/Kernel/Inductives/GenRec.lean:355-362 classFormerTy
/// Lean twin: `Ms.mapM (classFormerTy fe cvTas)`.
pub fn class_former_tys(
    pers: &PersTier,
    st: &mut AState,
    fe: &IFEnv,
    cv_tas: &Vec<IConstantVal>,
    ms: &Vec<TargetMajor>,
    i: usize,
    out: Vec<EIdx>,
) -> Result<Vec<EIdx>, CheckError> {
    if i >= ms.len() {
        Ok(out)
    } else {
        match class_former_ty(pers, st, fe, cv_tas, &ms[i]) {
            Err(e) => Err(e),
            Ok(t) => {
                let mut o: Vec<EIdx> = out;
                o.push(t);
                class_former_tys(pers, st, fe, cv_tas, ms, i + 1, o)
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/GenRec.lean:364-387 classConstOk
/// Lean twin: `proof/ConRon/Arena/Inductives/GenRec.lean:516-540 classConstOk` — **a
/// generated constant, checked**: `checkConstantValF` without the annotation
/// pass (the generator writes every binder datum), the guards in the cited
/// order, then its type inferred and a sort.
pub fn class_const_ok(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    fe: &IFEnv,
    cv: IConstantVal,
) -> Result<IConstantVal, CheckError> {
    let vis: u64 = fe.visible_below;
    if env::ifenv_find(vis, fe, &cv.name).is_some() {
        fail(core_types::invalid(code_points(&M_DUP_DECL)))
    } else {
        match core::reserved_basis_names(st) {
            Err(e) => Err(e),
            Ok(rs) => {
                if positivity::names_contain(&rs, &cv.name, 0) {
                    fail(core_types::invalid(code_points(&M_RESERVED)))
                } else {
                    match checker_base::nidx_is_proj_fn_shape(pers, st, &cv.name) {
                        Err(e) => Err(e),
                        Ok(true) => fail(core_types::invalid(code_points(&M_RESERVED_PROJ))),
                        Ok(false) => class_const_ok_type(pers, st, mode, fe, cv),
                    }
                }
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/GenRec.lean:364-387 classConstOk
/// Lean twin: `proof/ConRon/Arena/Inductives/GenRec.lean:516-540 classConstOk` — the
/// type's guards and its inference.
pub fn class_const_ok_type(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    fe: &IFEnv,
    cv: IConstantVal,
) -> Result<IConstantVal, CheckError> {
    let vis: u64 = fe.visible_below;
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
                    Ok(true) => match checker_base::consts_resolve_f_fast(pers, vis, st, fe, &cv.ty) {
                        Err(e) => Err(e),
                        Ok(false) => match checker_base::unresolved_consts_error(pers, st, &cv.ty) {
                            Err(e) => Err(e),
                            Ok(er) => fail(er),
                        },
                        Ok(true) => match core::infer_type_core(pers, vis, st, mode, fe, core::CHECK_FUEL, 0, &cv.ty) {
                            Err(e) => Err(e),
                            Ok(stype) => match core::ensure_sort_core(pers, vis, st, mode, fe, core::CHECK_FUEL, 0, &stype) {
                                Err(e) => Err(e),
                                Ok(_) => Ok(cv),
                            },
                        },
                    },
                },
            },
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/GenRec.lean:389-407 classRecTyOk
/// Lean twin: `proof/ConRon/Arena/Inductives/GenRec.lean:542-561 classRecTyOk` — **one
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
                        match class_const_ok(pers, st, mode, fe, cv) {
                            Err(e) => Err(e),
                            Ok(cv_g) => match core::is_def_eq_core(
                                pers,
                                fe.visible_below,
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
                                Ok(true) => Ok(cv_g),
                            },
                        }
                    }
                }
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/GenRec.lean:409-418 classRecTysOk
/// Lean twin: `proof/ConRon/Arena/Inductives/GenRec.lean:563-573 classRecTysOk` — every
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

/// con-leche: ConLeche/Kernel/Inductives/GenRec.lean:420-446 classRuleOk
/// Lean twin: `rbs.all (fun b => w.resolve feT b.1)` — the rule's λ-domains
/// resolve at the constructors' environment (visibility bound `vis_t`).
pub fn domains_resolve(
    pers: &PersTier,
    vis_t: u64,
    st: &mut AState,
    fe: &IFEnv,
    rbs: &Vec<(EIdx, BinderMeta)>,
    i: usize,
) -> Result<bool, CheckError> {
    if i >= rbs.len() {
        Ok(true)
    } else {
        let d: EIdx = rbs[i].0.dup2();
        match checker_base::consts_resolve_f_fast(pers, vis_t, st, fe, &d) {
            Err(e) => Err(e),
            Ok(false) => Ok(false),
            Ok(true) => domains_resolve(pers, vis_t, st, fe, rbs, i + 1),
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/GenRec.lean:420-446 classRuleOk
/// Lean twin: `rbs.all (fun b => b.2.pw == pw)`.
pub fn domains_pw(rbs: &Vec<(EIdx, BinderMeta)>, pw: &crate::kernel::prop_when::PropWhen, i: usize) -> bool {
    if i >= rbs.len() {
        true
    } else if prop_when::beq(&rbs[i].1.pw, pw) {
        domains_pw(rbs, pw, i + 1)
    } else {
        false
    }
}

/// con-leche: ConLeche/Kernel/Inductives/GenRec.lean:420-446 classRuleOk
/// con-leche: ConLeche/Cached/CheckerC.lean:98-126 sharedOpsRuleR
/// Lean twin: `proof/ConRon/Arena/Inductives/GenRec.lean:575-605 classRuleOk` — **one
/// generated rule, installed as generated**: closed, its level parameters the
/// recursor's, resolving and typed at the rule-less recursors' environment
/// (bound `vis_r`; `sharedOpsRuleR`'s flush leaving the inference), its
/// λ-telescope `n` long, its λ-domains resolving at the constructors'
/// environment (bound `vis_t`) and annotated with the family's datum `pw`.
#[allow(clippy::too_many_arguments)]
pub fn class_rule_ok(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    vis_t: u64,
    vis_r: u64,
    fe: &IFEnv,
    cv_r: &IConstantVal,
    pw: &crate::kernel::prop_when::PropWhen,
    n: u64,
    gen: EIdx,
) -> Result<EIdx, CheckError> {
    match expr_ops::loose_bvars_bounded_fast(pers, st, CORE_WALK_FUEL, 0, &gen) {
        Err(e) => Err(e),
        Ok(false) => fail(core_types::internal(code_points(&M_RULE_OPEN))),
        Ok(true) => match expr_ops::has_fvar_fast(pers, st, CORE_WALK_FUEL, &gen) {
            Err(e) => Err(e),
            Ok(true) => fail(core_types::internal(code_points(&M_RULE_OPEN))),
            Ok(false) => match checker_base::all_level_params_defined(pers, st, &cv_r.level_params, &gen) {
                Err(e) => Err(e),
                Ok(false) => fail(core_types::internal(code_points(&M_RULE_ULP))),
                Ok(true) => match checker_base::consts_resolve_f_fast(pers, vis_r, st, fe, &gen) {
                    Err(e) => Err(e),
                    Ok(false) => match checker_base::unresolved_consts_error(pers, st, &gen) {
                        Err(e) => Err(e),
                        Ok(er) => fail(er),
                    },
                    Ok(true) => match core::infer_type_core(pers, vis_r, st, mode, fe, core::CHECK_FUEL, 0, &gen) {
                        Err(e) => Err(e),
                        Ok(_) => {
                            // `sharedOpsRuleR`'s `inferType`: the flush leaving the
                            // rule-less recursors' environment
                            core::flush_caches(st);
                            class_rule_ok_tail(pers, st, vis_t, fe, cv_r, pw, n, gen)
                        }
                    },
                },
            },
        },
    }
}

/// con-leche: ConLeche/Kernel/Inductives/GenRec.lean:420-446 classRuleOk
/// Lean twin: `proof/ConRon/Arena/Inductives/GenRec.lean:575-605 classRuleOk` — the
/// λ-telescope, its domains' resolution and their datum.
#[allow(clippy::too_many_arguments)]
pub fn class_rule_ok_tail(
    pers: &PersTier,
    st: &mut AState,
    vis_t: u64,
    fe: &IFEnv,
    _cv_r: &IConstantVal,
    pw: &crate::kernel::prop_when::PropWhen,
    n: u64,
    gen: EIdx,
) -> Result<EIdx, CheckError> {
    match expr_ops::strip_lams(pers, st, n, &gen) {
        Err(e) => Err(e),
        Ok(None) => fail(core_types::internal(code_points(&M_RULE_TELE))),
        Ok(Some((rbs, _))) => match domains_resolve(pers, vis_t, st, fe, &rbs, 0) {
            Err(e) => Err(e),
            Ok(false) => match checker_base::unresolved_consts_error(pers, st, &gen) {
                Err(e) => Err(e),
                Ok(er) => fail(er),
            },
            Ok(true) => {
                if domains_pw(&rbs, pw, 0) {
                    Ok(gen)
                } else {
                    fail(core_types::internal(code_points(&M_RULE_PW)))
                }
            }
        },
    }
}

/// con-leche: ConLeche/Kernel/Inductives/GenRec.lean:448-459 classRulesOk
/// Lean twin: `proof/ConRon/Arena/Inductives/GenRec.lean:607-621 classRulesOk` — a
/// recursor's generated rules, one per constructor of its class, from `i` on.
#[allow(clippy::too_many_arguments)]
pub fn class_rules_ok(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    vis_t: u64,
    vis_r: u64,
    fe: &IFEnv,
    g: &ClassGen,
    rec_cls: &Vec<u64>,
    cv_gs: &Vec<IConstantVal>,
    cv_r: &IConstantVal,
    pw: &crate::kernel::prop_when::PropWhen,
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
                    match class_rule_ok(pers, st, mode, vis_t, vis_r, fe, cv_r, pw, n, gen) {
                        Err(e) => Err(e),
                        Ok(r) => {
                            let mut o: Vec<EIdx> = out;
                            o.push(r);
                            class_rules_ok(pers, st, mode, vis_t, vis_r, fe, g, rec_cls, cv_gs, cv_r, pw, c, xs, i + 1, o)
                        }
                    }
                }
            },
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/GenRec.lean:461-470 classRecsRulesOk
/// Lean twin: `proof/ConRon/Arena/Inductives/GenRec.lean:623-636 classRecsRulesOk` — every
/// recursor's generated rules, with its class, from `i` on (the shorter of
/// the two lists decides, as the cited zip does).
#[allow(clippy::too_many_arguments)]
pub fn class_recs_rules_ok(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    vis_t: u64,
    vis_r: u64,
    fe: &IFEnv,
    g: &ClassGen,
    rec_cls: &Vec<u64>,
    pw: &crate::kernel::prop_when::PropWhen,
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
        match class_rules_ok(pers, st, mode, vis_t, vis_r, fe, g, rec_cls, cv_gs, &cv_gs[i], pw, c, &xs, 0, Vec::new()) {
            Err(e) => Err(e),
            Ok(rhss) => match rec_check::target_major_at(pers, st, &g.cls, c) {
                Err(e) => Err(e),
                Ok(m) => {
                    let mut o: Vec<(IConstantVal, TargetMajor, Vec<EIdx>)> = out;
                    o.push((env::i_constant_val_dup(&cv_gs[i]), m, rhss));
                    class_recs_rules_ok(pers, st, mode, vis_t, vis_r, fe, g, rec_cls, pw, cv_gs, i + 1, o)
                }
            },
        }
    }
}

/// con-leche: none — a `List ClassCtor` copy; Lean shares the list
/// Lean twin: `proof/ConRon/Arena/Inductives/GenRec.lean:54-64 ClassCtor`.
pub fn class_ctors_dup(xs: &Vec<ClassCtor>, i: usize, out: Vec<ClassCtor>) -> Vec<ClassCtor> {
    if i >= xs.len() {
        out
    } else {
        let mut o: Vec<ClassCtor> = out;
        o.push(class_ctor_dup(&xs[i]));
        class_ctors_dup(xs, i + 1, o)
    }
}

/// con-leche: ConLeche/Kernel/Inductives/GenRec.lean:472-479 classStreamRecs
/// Lean twin: `proof/ConRon/Arena/Inductives/GenRec.lean:638-645 classStreamRecs` — the
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
        match checker_base::check_constant_val(pers, fe.visible_below, st, mode, fe, &rcs[i].cv_r) {
            Err(e) => Err(e),
            Ok(cv) => {
                let mut o: Vec<IConstantVal> = out;
                o.push(cv);
                class_stream_recs(pers, st, mode, fe, rcs, i + 1, o)
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/GenRec.lean:481-484 classKeyCanon
/// Lean twin: `proof/ConRon/Arena/Inductives/GenRec.lean:647-652 classKeyCanon` — a class
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

/// con-leche: ConLeche/Kernel/Inductives/GenRec.lean:486-492 classNPcOf
/// Lean twin: `proof/ConRon/Arena/Inductives/ClassRead.lean:147-156 classNPcOf` — an
/// inductive's parameter count as the pre-pass reads it: the block's at a
/// member, the stored `IndCaps`' otherwise (`0` at no inductive).
pub fn class_n_pc_of(p: &BlockShape, fe: &IFEnv, i_name: &NIdx) -> u64 {
    if positivity::names_contain(&shape_member_names(p), i_name, 0) {
        p.n_p
    } else {
        match env::ifenv_find(fe.visible_below, fe, i_name) {
            Some(IConstantInfo::IndInfo(_, caps)) => caps.nparams,
            _ => 0,
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/GenRec.lean:494-499 classSeeds
/// Lean twin: `proof/ConRon/Arena/Inductives/GenRec.lean:654-665 classSeeds` — the seeds:
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

/// con-leche: ConLeche/Kernel/Inductives/GenRec.lean:501-516 classKeyOf
/// Lean twin: `k.ds.mapM (ops.annotate env nP)` — the key's parameters
/// annotated at the formers' environment over the parameters, in order.
pub fn annotate_list(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    fe: &IFEnv,
    d: u64,
    xs: &Vec<EIdx>,
    i: usize,
    out: Vec<EIdx>,
) -> Result<Vec<EIdx>, CheckError> {
    if i >= xs.len() {
        Ok(out)
    } else {
        let x: EIdx = xs[i].dup2();
        match core::annotate_core(pers, fe.visible_below, st, mode, fe, core::CHECK_FUEL, d, &x) {
            Err(e) => Err(e),
            Ok(y) => {
                let mut o: Vec<EIdx> = out;
                o.push(y);
                annotate_list(pers, st, mode, fe, d, xs, i + 1, o)
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/GenRec.lean:501-516 classKeyOf
/// Lean twin: `proof/ConRon/Arena/Inductives/GenRec.lean:667-682 classKeyOf` — **a class
/// key, made checkable**: moved to the canonical parameter variables, its
/// parameters closed over them, and annotated at the formers' environment.
pub fn class_key_of(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    fe: &IFEnv,
    n_p: u64,
    params: &Vec<EIdx>,
    k: &ClassKey,
) -> Result<ClassKey, CheckError> {
    match class_key_canon(pers, st, params, k, 0, Vec::new()) {
        Err(e) => Err(e),
        Ok(k2) => match params_closed(pers, st, &k2.ds, n_p, 0) {
            Err(e) => Err(e),
            Ok(false) => fail(core_types::invalid(code_points(&M_MAJOR_PARAMS))),
            Ok(true) => match annotate_list(pers, st, mode, fe, n_p, &k2.ds, 0, Vec::new()) {
                Err(e) => Err(e),
                Ok(ds) => Ok(ClassKey {
                    ind: k2.ind,
                    lvls: k2.lvls,
                    ds,
                }),
            },
        },
    }
}

/// con-leche: ConLeche/Kernel/Inductives/GenRec.lean:501-516 classKeyOf
/// Lean twin: `rd.classes.mapM (classKeyOf ops env₁ p.nP params)`.
#[allow(clippy::too_many_arguments)]
pub fn class_keys_of(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    fe: &IFEnv,
    n_p: u64,
    params: &Vec<EIdx>,
    ks: &Vec<ClassKey>,
    i: usize,
    out: Vec<ClassKey>,
) -> Result<Vec<ClassKey>, CheckError> {
    if i >= ks.len() {
        Ok(out)
    } else {
        match class_key_of(pers, st, mode, fe, n_p, params, &ks[i]) {
            Err(e) => Err(e),
            Ok(k) => {
                let mut o: Vec<ClassKey> = out;
                o.push(k);
                class_keys_of(pers, st, mode, fe, n_p, params, ks, i + 1, o)
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/GenRec.lean:518-536 checkBlockClasses
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

/// con-leche: ConLeche/Kernel/Inductives/GenRec.lean:518-536 checkBlockClasses
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

/// con-leche: ConLeche/Kernel/Inductives/GenRec.lean:518-536 checkBlockClasses
/// Lean twin: `proof/ConRon/Arena/Inductives/GenRec.lean:684-703 checkBlockClasses` — **the
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
    ctors_as: &Vec<Vec<(IConstantVal, u64)>>,
) -> Result<(ClassRead, Vec<TargetMajor>), CheckError> {
    match class_read::class_read(pers, st, p, fe, p.n_p, &p.recs) {
        Err(e) => Err(e),
        Ok(None) => fail(core_types::invalid(code_points(&M_SHAPE))),
        Ok(Some(rd)) => {
            let ks: Vec<ClassKey> = class_read::classes(&rd.slots, 0, Vec::new());
            match class_keys_of(pers, st, mode, fe, p.n_p, params, &ks, 0, Vec::new()) {
                Err(e) => Err(e),
                Ok(keys) => match class_majors(pers, st, mode, fe, p, ctors_as, params, &keys, 0, Vec::new()) {
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

/// con-leche: ConLeche/Kernel/Inductives/GenRec.lean:545-549 classFeR
/// con-leche: ConLeche/Kernel/Inductives/BlockInstall.lean:338-346 consBlockRecsBare
/// con-leche: ConLeche/Kernel/Inductives/BlockInstallF.lean:175-180 consBlockRecsBareF
/// Lean twin: `proof/ConRon/Arena/Inductives/GenRec.lean:705-722 classFeR` — **the
/// rule-less generated recursors consed onto the constructors' environment**,
/// pushed TEMPORARILY in place (the module note): each recursor `m` at its
/// record's major index and rule prefix, with no rule.  Returns the rows the
/// pushes displaced, for `class_fe_r_pop`.
pub fn class_fe_r_push(
    p: &BlockShape,
    cv_gs: &Vec<IConstantVal>,
    rec_cls: &Vec<u64>,
    m: usize,
    fe: IFEnv,
    prevs: Vec<(NIdx, Option<(u64, u64)>)>,
) -> (IFEnv, Vec<(NIdx, Option<(u64, u64)>)>) {
    if m >= cv_gs.len() || m >= rec_cls.len() {
        (fe, prevs)
    } else {
        let mut fe2: IFEnv = fe;
        let n: NIdx = cv_gs[m].name.dup2();
        let prev: Option<(u64, u64)> = env::ifenv_push_temp(
            &mut fe2,
            IConstantInfo::RecInfo(
                env::i_constant_val_dup(&cv_gs[m]),
                block_parts::major_idx_at(p, m as u64),
                block_parts::rule_prefix_at(p, m as u64),
                Vec::new(),
            ),
        );
        let mut ps: Vec<(NIdx, Option<(u64, u64)>)> = prevs;
        ps.push((n, prev));
        class_fe_r_push(p, cv_gs, rec_cls, m + 1, fe2, ps)
    }
}

/// con-leche: ConLeche/Kernel/Inductives/GenRec.lean:545-549 classFeR
/// Lean twin: the inverse of `class_fe_r_push`: the pushes popped in reverse
/// order, every displaced row restored, so the index is the constructors'
/// again exactly.
pub fn class_fe_r_pop(fe: IFEnv, prevs: &Vec<(NIdx, Option<(u64, u64)>)>, i: usize) -> IFEnv {
    if i == 0 {
        fe
    } else {
        let mut fe2: IFEnv = fe;
        let prev: Option<(u64, u64)> = match prevs[i - 1].1 {
            Some(r) => Some(r),
            None => None,
        };
        env::ifenv_pop_temp(&mut fe2, &prevs[i - 1].0, prev);
        class_fe_r_pop(fe2, prevs, i - 1)
    }
}

/// con-leche: ConLeche/Kernel/Inductives/GenRec.lean:551-593 genRecCheck
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

/// con-leche: ConLeche/Kernel/Inductives/GenRec.lean:551-593 genRecCheck
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

/// con-leche: ConLeche/Kernel/Inductives/GenRec.lean:551-593 genRecCheck
/// Lean twin: `(ctors.map List.length).sum`.
pub fn ctor_count(xss: &Vec<Vec<ClassCtor>>, i: usize, acc: u64) -> u64 {
    if i >= xss.len() {
        acc
    } else {
        ctor_count(xss, i + 1, acc + (xss[i].len() as u64))
    }
}

/// con-leche: none — `cvTas.map (·.type)`
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

/// con-leche: ConLeche/Kernel/Inductives/GenRec.lean:551-593 genRecCheck
/// Lean twin: `proof/ConRon/Arena/Inductives/GenRec.lean:724-773 genRecCheck` — **the
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
    cv_tas: &Vec<IConstantVal>,
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
                        Ok(true) => gen_rec_classes(pers, st, mode, fe, p, params, tbl, rd, ms, cv_tas, cv_ris),
                    }
                } else {
                    gen_rec_classes(pers, st, mode, fe, p, params, tbl, rd, ms, cv_tas, cv_ris)
                }
            }
        },
    }
}

/// con-leche: ConLeche/Kernel/Inductives/GenRec.lean:551-593 genRecCheck
/// Lean twin: `proof/ConRon/Arena/Inductives/GenRec.lean:724-773 genRecCheck` — per class
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
    cv_tas: &Vec<IConstantVal>,
    cv_ris: Vec<IConstantVal>,
) -> Result<(IFEnv, Vec<(IConstantVal, TargetMajor, Vec<EIdx>)>), CheckError> {
    let vis: u64 = fe.visible_below;
    let former_tys: Vec<EIdx> = former_types(cv_tas, 0, Vec::new());
    match classes_nfs(pers, st, mode, vis, &fe, p, &former_tys, tbl, ms, 0, Vec::new()) {
        Err(e) => Err(e),
        Ok(ms2) => match classes_ctors(pers, st, mode, vis, &fe, p, &former_tys, rd, &ms2, 0, Vec::new()) {
            Err(e) => Err(e),
            Ok(ctors) => {
                if minor_count(&rd.slots, 0, 0) != ctor_count(&ctors, 0, 0) {
                    fail(core_types::invalid(code_points(&M_MINOR_COUNT)))
                } else {
                    match class_former_tys(pers, st, &fe, cv_tas, &ms2, 0, Vec::new()) {
                        Err(e) => Err(e),
                        Ok(former_tys_c) => match struct_parts::struct_elim_level(pers, st, &p.elim, p.large) {
                            Err(e) => Err(e),
                            Ok(elim) => match class_gen_bm(pers, st, &elim) {
                                Err(e) => Err(e),
                                Ok(bm) => {
                                    let g0: ClassGen = ClassGen {
                                        n_p: p.n_p,
                                        params: env::eidx_vec_dup(params),
                                        cls: ms2,
                                        former_tys: former_tys_c,
                                        slots: class_read::slots_dup(&rd.slots, 0, Vec::new()),
                                        ctors,
                                        elim,
                                        bm,
                                        pre: Vec::new(),
                                    };
                                    gen_rec_generate(pers, st, mode, fe, p, rd, cv_ris, g0)
                                }
                            },
                        },
                    }
                }
            }
        },
    }
}

/// con-leche: ConLeche/Kernel/Inductives/GenRec.lean:551-593 genRecCheck
/// con-leche: ConLeche/Cached/CheckerC.lean:128-134 shadowOpsC
/// Lean twin: `proof/ConRon/Arena/Inductives/GenRec.lean:724-773 genRecCheck` —
/// generation: the prefix, every recursor's type checked and compared, the
/// rule-less recursors pushed, the flush entering them, every rule
/// installed, the recursors popped and the flush leaving them.
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
                    let vis_t: u64 = fe.visible_below;
                    let pushed = class_fe_r_push(p, &cv_gs, &rd.rec_cls, 0, fe, Vec::new());
                    let fe_r: IFEnv = pushed.0;
                    let prevs: Vec<(NIdx, Option<(u64, u64)>)> = pushed.1;
                    let vis_r: u64 = fe_r.visible_below;
                    core::flush_caches(st);
                    let pw: crate::kernel::prop_when::PropWhen = prop_when::dup(&g.bm.pw);
                    match class_recs_rules_ok(pers, st, mode, vis_t, vis_r, &fe_r, &g, &rd.rec_cls, &pw, &cv_gs, 0, Vec::new()) {
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
