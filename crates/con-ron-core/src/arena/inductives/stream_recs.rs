//! `arena::inductives::stream_recs` — the stream's recursors, against the
//! generated ones.
//!
//! The Rust twin of `proof/ConRon/Arena/Inductives/StreamRecs.lean`, which is
//! `ConLeche/Kernel/Inductives/StreamRecs.lean` over handles.  The block's
//! check GENERATES every recursor of a block (`gen_rec::gen_rec_check`) and
//! compares the stream's records with them up to definitional equality.  What
//! is installed is the record, read off the block (`install::decl_constants`,
//! upstream `blockRecs`); these checks say that it is the generated recursor.
//! The records' K flags are checked against the block (`stream_k_check`), and
//! the block's declared feature flags are validated (`block_flags_check`).
//!
//! ## The twin's deviations
//!
//! * **The operations are not a record**: `ops` and `w` are `core`'s entry
//!   points and `checker_base::consts_resolve_f_fast` at the `IFEnv` in hand,
//!   which holds the constructors and the generated recursors.
//! * **The messages are constants** (§3.1 drops the interpolation), so the
//!   `rec`/`ctor` arguments that only name the slot are gone.
//! * **Upstream's `==` on terms and names is handle equality**, as everywhere
//!   in the arena.
//! * **Terms read from the store take the state**: `streamNestedOk` and
//!   `generatedFire` intern, so they are monadic.
//! * **`stream_closed`** is the closedness test `recTyCheck` and `ruleAgree`
//!   both open with, one function.
//! * **The declared flags' checks fail in the state** (`block_flags_check`):
//!   the cited pure check, run through `ofExcept`, reads the block's sort, a
//!   handle here (`large_elim_flag_ok`); its `for` loop is
//!   `majors_flags_check`, its `hasProj` the environment's `findTable?`, and
//!   `BlockShape.headName` (which only names the block in a message) is not
//!   ported.

use super::block_shape;
use super::block_shape::{BlockShape, MemberShape, RecShape};
use super::rec_check;
use super::rec_check::TargetMajor;
use crate::arena::canon;
use crate::arena::checker_base;
use crate::arena::core;
use crate::arena::core::CORE_WALK_FUEL;
use crate::arena::env;
use crate::arena::env::{IConstantVal, IFEnv, IRecRule, IRecRuleFire};
use crate::arena::expr_ops;
use crate::arena::handle::{EIdx, LIdx, NIdx, ETAG_CONST, ETAG_FORALL_E};
use crate::arena::monad::{fail, fail_dangling_e, intern_e_bvar, read_level_m, view_bind, view_const, view_ls, AState};
use crate::arena::store::PersTier;
use crate::kernel::core_types;
use crate::kernel::core_types::{code_points, CheckError};
use crate::kernel::env::{ind_flags_dup, CheckMode, IndFlags};
use crate::kernel::level;
use crate::kernel::expr_ops::sub_nat;
use crate::ron::hashmap::Eq2;

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `stored recursor: domain index`, as code points.
pub const M_DOM_INDEX: [u32; 29] = [
    115, 116, 111, 114, 101, 100, 32, 114, 101, 99, 117, 114, 115, 111, 114, 58, 32, 100, 111, 109,
    97, 105, 110, 32, 105, 110, 100, 101, 120,
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `the type of the recursor  is not the generated one: the domain of binder  differs`, as code points.
pub const M_TY_DOM: [u32; 81] = [
    116, 104, 101, 32, 116, 121, 112, 101, 32, 111, 102, 32, 116, 104, 101, 32, 114, 101, 99, 117,
    114, 115, 111, 114, 32, 32, 105, 115, 32, 110, 111, 116, 32, 116, 104, 101, 32, 103, 101, 110,
    101, 114, 97, 116, 101, 100, 32, 111, 110, 101, 58, 32, 116, 104, 101, 32, 100, 111, 109, 97,
    105, 110, 32, 111, 102, 32, 98, 105, 110, 100, 101, 114, 32, 32, 100, 105, 102, 102, 101, 114,
    115,
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `the type of the recursor  is not the generated one: its body after the major differs`, as code points.
pub const M_TY_BODY: [u32; 84] = [
    116, 104, 101, 32, 116, 121, 112, 101, 32, 111, 102, 32, 116, 104, 101, 32, 114, 101, 99, 117,
    114, 115, 111, 114, 32, 32, 105, 115, 32, 110, 111, 116, 32, 116, 104, 101, 32, 103, 101, 110,
    101, 114, 97, 116, 101, 100, 32, 111, 110, 101, 58, 32, 105, 116, 115, 32, 98, 111, 100, 121,
    32, 97, 102, 116, 101, 114, 32, 116, 104, 101, 32, 109, 97, 106, 111, 114, 32, 100, 105, 102,
    102, 101, 114, 115,
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `the type of the recursor  is not the generated one: it has fewer than  binders`, as code points.
pub const M_TY_SHORT: [u32; 78] = [
    116, 104, 101, 32, 116, 121, 112, 101, 32, 111, 102, 32, 116, 104, 101, 32, 114, 101, 99, 117,
    114, 115, 111, 114, 32, 32, 105, 115, 32, 110, 111, 116, 32, 116, 104, 101, 32, 103, 101, 110,
    101, 114, 97, 116, 101, 100, 32, 111, 110, 101, 58, 32, 105, 116, 32, 104, 97, 115, 32, 102,
    101, 119, 101, 114, 32, 116, 104, 97, 110, 32, 32, 98, 105, 110, 100, 101, 114, 115,
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `the generated type of the recursor  has fewer than  binders`, as code points.
pub const M_GEN_SHORT: [u32; 59] = [
    116, 104, 101, 32, 103, 101, 110, 101, 114, 97, 116, 101, 100, 32, 116, 121, 112, 101, 32, 111,
    102, 32, 116, 104, 101, 32, 114, 101, 99, 117, 114, 115, 111, 114, 32, 32, 104, 97, 115, 32,
    102, 101, 119, 101, 114, 32, 116, 104, 97, 110, 32, 32, 98, 105, 110, 100, 101, 114, 115,
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `"the type of the recursor"`, as code points (the slot `unresolved_consts_error` names).
pub const M_W_REC_TYPE: [u32; 24] = [
    116, 104, 101, 32, 116, 121, 112, 101, 32, 111, 102, 32, 116, 104, 101, 32, 114, 101, 99, 117,
    114, 115, 111, 114,
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `"the recursor's rule"`, as code points (the slot `unresolved_consts_error` names).
pub const M_W_REC_RULE: [u32; 19] = [
    116, 104, 101, 32, 114, 101, 99, 117, 114, 115, 111, 114, 39, 115, 32, 114, 117, 108, 101,
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `the type of the recursor  is not closed`, as code points.
pub const M_TY_OPEN: [u32; 39] = [
    116, 104, 101, 32, 116, 121, 112, 101, 32, 111, 102, 32, 116, 104, 101, 32, 114, 101, 99, 117,
    114, 115, 111, 114, 32, 32, 105, 115, 32, 110, 111, 116, 32, 99, 108, 111, 115, 101, 100,
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `undeclared universe parameter in the type of the recursor `, as code points.
pub const M_TY_ULP: [u32; 58] = [
    117, 110, 100, 101, 99, 108, 97, 114, 101, 100, 32, 117, 110, 105, 118, 101, 114, 115, 101, 32,
    112, 97, 114, 97, 109, 101, 116, 101, 114, 32, 105, 110, 32, 116, 104, 101, 32, 116, 121, 112,
    101, 32, 111, 102, 32, 116, 104, 101, 32, 114, 101, 99, 117, 114, 115, 111, 114, 32,
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `the recursor 's rule for  has a right-hand side that is not closed`, as code points.
pub const M_RULE_OPEN: [u32; 66] = [
    116, 104, 101, 32, 114, 101, 99, 117, 114, 115, 111, 114, 32, 39, 115, 32, 114, 117, 108, 101,
    32, 102, 111, 114, 32, 32, 104, 97, 115, 32, 97, 32, 114, 105, 103, 104, 116, 45, 104, 97,
    110, 100, 32, 115, 105, 100, 101, 32, 116, 104, 97, 116, 32, 105, 115, 32, 110, 111, 116, 32,
    99, 108, 111, 115, 101, 100,
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `the recursor 's rule for  has an undeclared universe parameter`, as code points.
pub const M_RULE_ULP: [u32; 62] = [
    116, 104, 101, 32, 114, 101, 99, 117, 114, 115, 111, 114, 32, 39, 115, 32, 114, 117, 108, 101,
    32, 102, 111, 114, 32, 32, 104, 97, 115, 32, 97, 110, 32, 117, 110, 100, 101, 99, 108, 97,
    114, 101, 100, 32, 117, 110, 105, 118, 101, 114, 115, 101, 32, 112, 97, 114, 97, 109, 101, 116,
    101, 114,
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `the recursor 's rule for  has a right-hand side whose type is not the generated one's`, as code points.
pub const M_RULE_TY: [u32; 85] = [
    116, 104, 101, 32, 114, 101, 99, 117, 114, 115, 111, 114, 32, 39, 115, 32, 114, 117, 108, 101,
    32, 102, 111, 114, 32, 32, 104, 97, 115, 32, 97, 32, 114, 105, 103, 104, 116, 45, 104, 97,
    110, 100, 32, 115, 105, 100, 101, 32, 119, 104, 111, 115, 101, 32, 116, 121, 112, 101, 32, 105,
    115, 32, 110, 111, 116, 32, 116, 104, 101, 32, 103, 101, 110, 101, 114, 97, 116, 101, 100, 32,
    111, 110, 101, 39, 115,
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `the recursor 's rule for  has a right-hand side that is not definitionally equal to the generated one`, as code points.
pub const M_RULE_DEFEQ: [u32; 101] = [
    116, 104, 101, 32, 114, 101, 99, 117, 114, 115, 111, 114, 32, 39, 115, 32, 114, 117, 108, 101,
    32, 102, 111, 114, 32, 32, 104, 97, 115, 32, 97, 32, 114, 105, 103, 104, 116, 45, 104, 97,
    110, 100, 32, 115, 105, 100, 101, 32, 116, 104, 97, 116, 32, 105, 115, 32, 110, 111, 116, 32,
    100, 101, 102, 105, 110, 105, 116, 105, 111, 110, 97, 108, 108, 121, 32, 101, 113, 117, 97, 108,
    32, 116, 111, 32, 116, 104, 101, 32, 103, 101, 110, 101, 114, 97, 116, 101, 100, 32, 111, 110,
    101,
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `the recursor 's rule for  is not the generated one's (constructor ,  fields)`, as code points.
pub const M_RULE_SHAPE: [u32; 76] = [
    116, 104, 101, 32, 114, 101, 99, 117, 114, 115, 111, 114, 32, 39, 115, 32, 114, 117, 108, 101,
    32, 102, 111, 114, 32, 32, 105, 115, 32, 110, 111, 116, 32, 116, 104, 101, 32, 103, 101, 110,
    101, 114, 97, 116, 101, 100, 32, 111, 110, 101, 39, 115, 32, 40, 99, 111, 110, 115, 116, 114,
    117, 99, 116, 111, 114, 32, 44, 32, 32, 102, 105, 101, 108, 100, 115, 41,
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `the recursor  carries  more or fewer rules than the generated one ( unmatched)`, as code points.
pub const M_RULE_COUNT: [u32; 78] = [
    116, 104, 101, 32, 114, 101, 99, 117, 114, 115, 111, 114, 32, 32, 99, 97, 114, 114, 105, 101,
    115, 32, 32, 109, 111, 114, 101, 32, 111, 114, 32, 102, 101, 119, 101, 114, 32, 114, 117, 108,
    101, 115, 32, 116, 104, 97, 110, 32, 116, 104, 101, 32, 103, 101, 110, 101, 114, 97, 116, 101,
    100, 32, 111, 110, 101, 32, 40, 32, 117, 110, 109, 97, 116, 99, 104, 101, 100, 41,
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `the recursor : the generated rules are not one per stored rule`, as code points.
pub const M_RULES_GEN: [u32; 62] = [
    116, 104, 101, 32, 114, 101, 99, 117, 114, 115, 111, 114, 32, 58, 32, 116, 104, 101, 32, 103,
    101, 110, 101, 114, 97, 116, 101, 100, 32, 114, 117, 108, 101, 115, 32, 97, 114, 101, 32, 110,
    111, 116, 32, 111, 110, 101, 32, 112, 101, 114, 32, 115, 116, 111, 114, 101, 100, 32, 114, 117,
    108, 101,
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `the recursor 's stored type does not apply its major's container at the generated firing data`, as code points.
pub const M_NESTED: [u32; 93] = [
    116, 104, 101, 32, 114, 101, 99, 117, 114, 115, 111, 114, 32, 39, 115, 32, 115, 116, 111, 114,
    101, 100, 32, 116, 121, 112, 101, 32, 100, 111, 101, 115, 32, 110, 111, 116, 32, 97, 112, 112,
    108, 121, 32, 105, 116, 115, 32, 109, 97, 106, 111, 114, 39, 115, 32, 99, 111, 110, 116, 97,
    105, 110, 101, 114, 32, 97, 116, 32, 116, 104, 101, 32, 103, 101, 110, 101, 114, 97, 116, 101,
    100, 32, 102, 105, 114, 105, 110, 103, 32, 100, 97, 116, 97,
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `stored recursors: the generated family is not the records'`, as code points.
pub const M_FAMILY: [u32; 58] = [
    115, 116, 111, 114, 101, 100, 32, 114, 101, 99, 117, 114, 115, 111, 114, 115, 58, 32, 116, 104,
    101, 32, 103, 101, 110, 101, 114, 97, 116, 101, 100, 32, 102, 97, 109, 105, 108, 121, 32, 105,
    115, 32, 110, 111, 116, 32, 116, 104, 101, 32, 114, 101, 99, 111, 114, 100, 115, 39,
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `recursor  declares k := ; the generated recursor of this block is K-like`, as code points.
pub const M_K_FLAG: [u32; 72] = [
    114, 101, 99, 117, 114, 115, 111, 114, 32, 32, 100, 101, 99, 108, 97, 114, 101, 115, 32, 107,
    32, 58, 61, 32, 59, 32, 116, 104, 101, 32, 103, 101, 110, 101, 114, 97, 116, 101, 100, 32,
    114, 101, 99, 117, 114, 115, 111, 114, 32, 111, 102, 32, 116, 104, 105, 115, 32, 98, 108, 111,
    99, 107, 32, 105, 115, 32, 75, 45, 108, 105, 107, 101,
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `the recursor  carries reduction rules, but its block has no large eliminator (hasLargeElim is false), so its recursors have none`, as code points.
pub const M_RULES_NO_LARGE: [u32; 128] = [
    116, 104, 101, 32, 114, 101, 99, 117, 114, 115, 111, 114, 32, 32, 99, 97, 114, 114, 105, 101,
    115, 32, 114, 101, 100, 117, 99, 116, 105, 111, 110, 32, 114, 117, 108, 101, 115, 44, 32, 98,
    117, 116, 32, 105, 116, 115, 32, 98, 108, 111, 99, 107, 32, 104, 97, 115, 32, 110, 111, 32,
    108, 97, 114, 103, 101, 32, 101, 108, 105, 109, 105, 110, 97, 116, 111, 114, 32, 40, 104, 97,
    115, 76, 97, 114, 103, 101, 69, 108, 105, 109, 32, 105, 115, 32, 102, 97, 108, 115, 101, 41,
    44, 32, 115, 111, 32, 105, 116, 115, 32, 114, 101, 99, 117, 114, 115, 111, 114, 115, 32, 104,
    97, 118, 101, 32, 110, 111, 110, 101,
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `inductive type  is declared with K-like reduction (isK), but it is not a proposition alone in its block with one constructor without fields`, as code points.
pub const M_FLAG_K: [u32; 139] = [
    105, 110, 100, 117, 99, 116, 105, 118, 101, 32, 116, 121, 112, 101, 32, 32, 105, 115, 32, 100,
    101, 99, 108, 97, 114, 101, 100, 32, 119, 105, 116, 104, 32, 75, 45, 108, 105, 107, 101, 32,
    114, 101, 100, 117, 99, 116, 105, 111, 110, 32, 40, 105, 115, 75, 41, 44, 32, 98, 117, 116,
    32, 105, 116, 32, 105, 115, 32, 110, 111, 116, 32, 97, 32, 112, 114, 111, 112, 111, 115, 105,
    116, 105, 111, 110, 32, 97, 108, 111, 110, 101, 32, 105, 110, 32, 105, 116, 115, 32, 98, 108,
    111, 99, 107, 32, 119, 105, 116, 104, 32, 111, 110, 101, 32, 99, 111, 110, 115, 116, 114, 117,
    99, 116, 111, 114, 32, 119, 105, 116, 104, 111, 117, 116, 32, 102, 105, 101, 108, 100, 115,
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `inductive type  is declared with projections (hasProjections), but it does not have exactly one constructor and no indices, or it is impredicative`, as code points.
pub const M_FLAG_PROJ: [u32; 146] = [
    105, 110, 100, 117, 99, 116, 105, 118, 101, 32, 116, 121, 112, 101, 32, 32, 105, 115, 32, 100,
    101, 99, 108, 97, 114, 101, 100, 32, 119, 105, 116, 104, 32, 112, 114, 111, 106, 101, 99, 116,
    105, 111, 110, 115, 32, 40, 104, 97, 115, 80, 114, 111, 106, 101, 99, 116, 105, 111, 110, 115,
    41, 44, 32, 98, 117, 116, 32, 105, 116, 32, 100, 111, 101, 115, 32, 110, 111, 116, 32, 104,
    97, 118, 101, 32, 101, 120, 97, 99, 116, 108, 121, 32, 111, 110, 101, 32, 99, 111, 110, 115,
    116, 114, 117, 99, 116, 111, 114, 32, 97, 110, 100, 32, 110, 111, 32, 105, 110, 100, 105, 99,
    101, 115, 44, 32, 111, 114, 32, 105, 116, 32, 105, 115, 32, 105, 109, 112, 114, 101, 100, 105,
    99, 97, 116, 105, 118, 101,
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `inductive type  is declared with eta (hasEta), but it has no projections or is recursive`, as code points.
pub const M_FLAG_ETA: [u32; 88] = [
    105, 110, 100, 117, 99, 116, 105, 118, 101, 32, 116, 121, 112, 101, 32, 32, 105, 115, 32, 100,
    101, 99, 108, 97, 114, 101, 100, 32, 119, 105, 116, 104, 32, 101, 116, 97, 32, 40, 104, 97,
    115, 69, 116, 97, 41, 44, 32, 98, 117, 116, 32, 105, 116, 32, 104, 97, 115, 32, 110, 111,
    32, 112, 114, 111, 106, 101, 99, 116, 105, 111, 110, 115, 32, 111, 114, 32, 105, 115, 32, 114,
    101, 99, 117, 114, 115, 105, 118, 101,
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `inductive block : flags for  of  types`, as code points.
pub const M_FLAGS_COUNT: [u32; 38] = [
    105, 110, 100, 117, 99, 116, 105, 118, 101, 32, 98, 108, 111, 99, 107, 32, 58, 32, 102, 108,
    97, 103, 115, 32, 102, 111, 114, 32, 32, 111, 102, 32, 32, 116, 121, 112, 101, 115,
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `inductive block : its types disagree on isImpredicative or hasLargeElim`, as code points.
pub const M_FLAGS_DISAGREE: [u32; 71] = [
    105, 110, 100, 117, 99, 116, 105, 118, 101, 32, 98, 108, 111, 99, 107, 32, 58, 32, 105, 116,
    115, 32, 116, 121, 112, 101, 115, 32, 100, 105, 115, 97, 103, 114, 101, 101, 32, 111, 110, 32,
    105, 115, 73, 109, 112, 114, 101, 100, 105, 99, 97, 116, 105, 118, 101, 32, 111, 114, 32, 104,
    97, 115, 76, 97, 114, 103, 101, 69, 108, 105, 109,
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `inductive block  is declared impredicative (isImpredicative), but its type is not a proposition`, as code points.
pub const M_FLAG_IMPRED: [u32; 95] = [
    105, 110, 100, 117, 99, 116, 105, 118, 101, 32, 98, 108, 111, 99, 107, 32, 32, 105, 115, 32,
    100, 101, 99, 108, 97, 114, 101, 100, 32, 105, 109, 112, 114, 101, 100, 105, 99, 97, 116, 105,
    118, 101, 32, 40, 105, 115, 73, 109, 112, 114, 101, 100, 105, 99, 97, 116, 105, 118, 101, 41,
    44, 32, 98, 117, 116, 32, 105, 116, 115, 32, 116, 121, 112, 101, 32, 105, 115, 32, 110, 111,
    116, 32, 97, 32, 112, 114, 111, 112, 111, 115, 105, 116, 105, 111, 110,
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `inductive block : hasLargeElim is , but its recursors eliminate `, as code points.
pub const M_FLAG_LARGE_REC: [u32; 64] = [
    105, 110, 100, 117, 99, 116, 105, 118, 101, 32, 98, 108, 111, 99, 107, 32, 58, 32, 104, 97,
    115, 76, 97, 114, 103, 101, 69, 108, 105, 109, 32, 105, 115, 32, 44, 32, 98, 117, 116, 32,
    105, 116, 115, 32, 114, 101, 99, 117, 114, 115, 111, 114, 115, 32, 101, 108, 105, 109, 105, 110,
    97, 116, 101, 32,
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `inductive block  is declared with a large eliminator (hasLargeElim), but it may be a proposition and is not a single type with no constructor, or with one constructor that has eta or K-like reduction`, as code points.
pub const M_FLAG_LARGE: [u32; 199] = [
    105, 110, 100, 117, 99, 116, 105, 118, 101, 32, 98, 108, 111, 99, 107, 32, 32, 105, 115, 32,
    100, 101, 99, 108, 97, 114, 101, 100, 32, 119, 105, 116, 104, 32, 97, 32, 108, 97, 114, 103,
    101, 32, 101, 108, 105, 109, 105, 110, 97, 116, 111, 114, 32, 40, 104, 97, 115, 76, 97, 114,
    103, 101, 69, 108, 105, 109, 41, 44, 32, 98, 117, 116, 32, 105, 116, 32, 109, 97, 121, 32,
    98, 101, 32, 97, 32, 112, 114, 111, 112, 111, 115, 105, 116, 105, 111, 110, 32, 97, 110, 100,
    32, 105, 115, 32, 110, 111, 116, 32, 97, 32, 115, 105, 110, 103, 108, 101, 32, 116, 121, 112,
    101, 32, 119, 105, 116, 104, 32, 110, 111, 32, 99, 111, 110, 115, 116, 114, 117, 99, 116, 111,
    114, 44, 32, 111, 114, 32, 119, 105, 116, 104, 32, 111, 110, 101, 32, 99, 111, 110, 115, 116,
    114, 117, 99, 116, 111, 114, 32, 116, 104, 97, 116, 32, 104, 97, 115, 32, 101, 116, 97, 32,
    111, 114, 32, 75, 45, 108, 105, 107, 101, 32, 114, 101, 100, 117, 99, 116, 105, 111, 110,
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `inductive block  nests , a proposition with one constructor without fields; its K-like reduction cannot be kept inside the block`, as code points.
pub const M_FLAG_NEST_K: [u32; 128] = [
    105, 110, 100, 117, 99, 116, 105, 118, 101, 32, 98, 108, 111, 99, 107, 32, 32, 110, 101, 115,
    116, 115, 32, 44, 32, 97, 32, 112, 114, 111, 112, 111, 115, 105, 116, 105, 111, 110, 32, 119,
    105, 116, 104, 32, 111, 110, 101, 32, 99, 111, 110, 115, 116, 114, 117, 99, 116, 111, 114, 32,
    119, 105, 116, 104, 111, 117, 116, 32, 102, 105, 101, 108, 100, 115, 59, 32, 105, 116, 115, 32,
    75, 45, 108, 105, 107, 101, 32, 114, 101, 100, 117, 99, 116, 105, 111, 110, 32, 99, 97, 110,
    110, 111, 116, 32, 98, 101, 32, 107, 101, 112, 116, 32, 105, 110, 115, 105, 100, 101, 32, 116,
    104, 101, 32, 98, 108, 111, 99, 107,
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `inductive block  is impredicative (isImpredicative) and nests , which has projections; an impredicative type cannot have projections`, as code points.
pub const M_FLAG_NEST_PROJ: [u32; 132] = [
    105, 110, 100, 117, 99, 116, 105, 118, 101, 32, 98, 108, 111, 99, 107, 32, 32, 105, 115, 32,
    105, 109, 112, 114, 101, 100, 105, 99, 97, 116, 105, 118, 101, 32, 40, 105, 115, 73, 109, 112,
    114, 101, 100, 105, 99, 97, 116, 105, 118, 101, 41, 32, 97, 110, 100, 32, 110, 101, 115, 116,
    115, 32, 44, 32, 119, 104, 105, 99, 104, 32, 104, 97, 115, 32, 112, 114, 111, 106, 101, 99,
    116, 105, 111, 110, 115, 59, 32, 97, 110, 32, 105, 109, 112, 114, 101, 100, 105, 99, 97, 116,
    105, 118, 101, 32, 116, 121, 112, 101, 32, 99, 97, 110, 110, 111, 116, 32, 104, 97, 118, 101,
    32, 112, 114, 111, 106, 101, 99, 116, 105, 111, 110, 115,
];

/// con-leche: ConLeche/Kernel/Inductives/StreamRecs.lean:44-58 recDomsAt
/// con-leche: ConLeche/Cached/IndTail.lean:82-92 recDomsAtC
/// Lean twin: `proof/ConRon/Arena/Inductives/StreamRecs.lean:41-57 recDomsAt` — **a
/// record's type's domains against the generated one's**, binder by binder from
/// binder `j` on (`k` of them): each stored domain `isDefEq` to the generated
/// one at its depth, both telescopes opened at their own locals.
#[allow(clippy::too_many_arguments)]
pub fn rec_doms_at(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    fe: &IFEnv,
    sfvs: &Vec<EIdx>,
    gfvs: &Vec<EIdx>,
    j: u64,
    k: u64,
) -> Result<(), CheckError> {
    if k == 0 {
        Ok(())
    } else if j >= sfvs.len() as u64 || j >= gfvs.len() as u64 {
        fail(core_types::internal(code_points(&M_DOM_INDEX)))
    } else {
        match expr_ops::fvar_type_d(pers, st, &sfvs[j as usize]) {
            Err(e) => Err(e),
            Ok(a) => match expr_ops::fvar_type_d(pers, st, &gfvs[j as usize]) {
                Err(e) => Err(e),
                Ok(b) => match core::is_def_eq_core(pers, st, mode, fe, core::CHECK_FUEL, j, &a, &b) {
                    Err(e) => Err(e),
                    Ok(false) => fail(core_types::invalid(code_points(&M_TY_DOM))),
                    Ok(true) => rec_doms_at(pers, st, mode, fe, sfvs, gfvs, j + 1, k - 1),
                },
            },
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/StreamRecs.lean:60-73 recTyOpened
/// con-leche: ConLeche/Cached/IndTail.lean:94-106 recTyOpenedC
/// Lean twin: `proof/ConRon/Arena/Inductives/StreamRecs.lean:59-70 recTyOpened` — the
/// record's and the generated type, opened `n` binders deep: the domains, then
/// the residues.
pub fn rec_ty_opened(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    fe: &IFEnv,
    n: u64,
    s: &Option<(Vec<EIdx>, EIdx)>,
    g: &Option<(Vec<EIdx>, EIdx)>,
) -> Result<(), CheckError> {
    match s {
        None => fail(core_types::invalid(code_points(&M_TY_SHORT))),
        Some((sfvs, srest)) => match g {
            None => fail(core_types::internal(code_points(&M_GEN_SHORT))),
            Some((gfvs, grest)) => match rec_doms_at(pers, st, mode, fe, sfvs, gfvs, 0, n) {
                Err(e) => Err(e),
                Ok(()) => match core::is_def_eq_core(pers, st, mode, fe, core::CHECK_FUEL, n, srest, grest) {
                    Err(e) => Err(e),
                    Ok(false) => fail(core_types::invalid(code_points(&M_TY_BODY))),
                    Ok(true) => Ok(()),
                },
            },
        },
    }
}

/// con-leche: ConLeche/Kernel/Inductives/StreamRecs.lean:75-89 recTyCheck
/// con-leche: ConLeche/Cached/IndTail.lean:108-120 recTyCheckC
/// con-leche: ConLeche/Kernel/Inductives/StreamRecs.lean:91-112 ruleAgree
/// con-leche: ConLeche/Cached/IndTail.lean:122-140 ruleAgreeC
/// Lean twin: `proof/ConRon/Arena/Inductives/StreamRecs.lean:72-83 streamClosed` — the
/// test both open with: `s.looseBVarsBounded 0 && !s.hasFvar && !g.hasFvar`.
pub fn stream_closed(pers: &PersTier, st: &mut AState, s: &EIdx, g: &EIdx) -> Result<bool, CheckError> {
    match expr_ops::loose_bvars_bounded_fast(pers, st, CORE_WALK_FUEL, 0, s) {
        Err(e) => Err(e),
        Ok(false) => Ok(false),
        Ok(true) => match expr_ops::has_fvar_fast(pers, st, CORE_WALK_FUEL, s) {
            Err(e) => Err(e),
            Ok(true) => Ok(false),
            Ok(false) => match expr_ops::has_fvar_fast(pers, st, CORE_WALK_FUEL, g) {
                Err(e) => Err(e),
                Ok(h) => Ok(!h),
            },
        },
    }
}

/// con-leche: ConLeche/Kernel/Inductives/StreamRecs.lean:75-89 recTyCheck
/// con-leche: ConLeche/Cached/IndTail.lean:108-120 recTyCheckC
/// Lean twin: `proof/ConRon/Arena/Inductives/StreamRecs.lean:85-102 recTyCheck` — **a
/// record's type's check**: closed, at the record's level parameters `lps`,
/// resolving, a type (inferred, a sort), and the generated one binder by binder
/// up to the major (`n` binders): the domains, then the residues.
#[allow(clippy::too_many_arguments)]
pub fn rec_ty_check(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    fe: &IFEnv,
    lps: &Vec<NIdx>,
    n: u64,
    s: &EIdx,
    g: &EIdx,
) -> Result<(), CheckError> {
    match stream_closed(pers, st, s, g) {
        Err(e) => Err(e),
        Ok(false) => fail(core_types::invalid(code_points(&M_TY_OPEN))),
        Ok(true) => match checker_base::all_level_params_defined(pers, st, lps, s) {
            Err(e) => Err(e),
            Ok(false) => fail(core_types::invalid(code_points(&M_TY_ULP))),
            Ok(true) => match checker_base::consts_resolve_f_fast(pers, st, fe, s) {
                Err(e) => Err(e),
                Ok(false) => match checker_base::unresolved_consts_error(pers, st, &code_points(&M_W_REC_TYPE), s) {
                    Err(e) => Err(e),
                    Ok(er) => fail(er),
                },
                Ok(true) => match core::infer_type_core(pers, st, mode, fe, core::CHECK_FUEL, 0, s) {
                    Err(e) => Err(e),
                    Ok(st_ty) => match core::ensure_sort_core(pers, st, mode, fe, core::CHECK_FUEL, 0, &st_ty) {
                        Err(e) => Err(e),
                        Ok(_) => match core::open_pis_at_fvars(pers, st, n, s, 0) {
                            Err(e) => Err(e),
                            Ok(so) => match core::open_pis_at_fvars(pers, st, n, g, 0) {
                                Err(e) => Err(e),
                                Ok(go) => rec_ty_opened(pers, st, mode, fe, n, &so, &go),
                            },
                        },
                    },
                },
            },
        },
    }
}

/// con-leche: ConLeche/Kernel/Inductives/StreamRecs.lean:91-112 ruleAgree
/// con-leche: ConLeche/Cached/IndTail.lean:122-140 ruleAgreeC
/// Lean twin: `proof/ConRon/Arena/Inductives/StreamRecs.lean:104-121 ruleAgree` — **one
/// rule's check**: the record's right-hand side `s` is closed, at the
/// record's level parameters `lps`, resolving; it and the generated `g` are
/// inferred, their types are definitionally equal, and so are they.
pub fn rule_agree(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    fe: &IFEnv,
    lps: &Vec<NIdx>,
    s: &EIdx,
    g: &EIdx,
) -> Result<(), CheckError> {
    match stream_closed(pers, st, s, g) {
        Err(e) => Err(e),
        Ok(false) => fail(core_types::invalid(code_points(&M_RULE_OPEN))),
        Ok(true) => match checker_base::all_level_params_defined(pers, st, lps, s) {
            Err(e) => Err(e),
            Ok(false) => fail(core_types::invalid(code_points(&M_RULE_ULP))),
            Ok(true) => match checker_base::consts_resolve_f_fast(pers, st, fe, s) {
                Err(e) => Err(e),
                Ok(false) => match checker_base::unresolved_consts_error(pers, st, &code_points(&M_W_REC_RULE), s) {
                    Err(e) => Err(e),
                    Ok(er) => fail(er),
                },
                Ok(true) => match core::infer_type_core(pers, st, mode, fe, core::CHECK_FUEL, 0, s) {
                    Err(e) => Err(e),
                    Ok(ts) => match core::infer_type_core(pers, st, mode, fe, core::CHECK_FUEL, 0, g) {
                        Err(e) => Err(e),
                        Ok(tg) => match core::is_def_eq_core(pers, st, mode, fe, core::CHECK_FUEL, 0, &ts, &tg) {
                            Err(e) => Err(e),
                            Ok(false) => fail(core_types::invalid(code_points(&M_RULE_TY))),
                            Ok(true) => match core::is_def_eq_core(pers, st, mode, fe, core::CHECK_FUEL, 0, s, g) {
                                Err(e) => Err(e),
                                Ok(false) => fail(core_types::invalid(code_points(&M_RULE_DEFEQ))),
                                Ok(true) => Ok(()),
                            },
                        },
                    },
                },
            },
        },
    }
}

/// con-leche: ConLeche/Kernel/Inductives/StreamRecs.lean:114-131 streamNestedOk
/// con-leche: ConLeche/Cached/IndTail.lean:66-80 streamNestedOkC
/// Lean twin: `pins.map (Expr.liftLooseBVars amount 0)` — the firing pins lifted
/// past the index binders, from `i` on, pushed onto `out`.
pub fn stream_nested_pins(
    pers: &PersTier,
    st: &mut AState,
    amount: u64,
    pins: &Vec<EIdx>,
    i: usize,
    out: Vec<EIdx>,
) -> Result<Vec<EIdx>, CheckError> {
    if i >= pins.len() {
        Ok(out)
    } else {
        match expr_ops::lift_loose_bvars_fast(pers, st, CORE_WALK_FUEL, amount, 0, &pins[i]) {
            Err(e) => Err(e),
            Ok(p) => {
                let mut o: Vec<EIdx> = out;
                o.push(p);
                stream_nested_pins(pers, st, amount, pins, i + 1, o)
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/StreamRecs.lean:114-131 streamNestedOk
/// con-leche: ConLeche/Cached/IndTail.lean:66-80 streamNestedOkC
/// Lean twin: `(List.range n).map (fun i => Expr.bvar (n - 1 - i))` — the index
/// variables, `k` of them still to come, pushed onto `out`.
pub fn stream_nested_bvars(pers: &PersTier, st: &mut AState, k: u64, out: Vec<EIdx>) -> Result<Vec<EIdx>, CheckError> {
    if k == 0 {
        Ok(out)
    } else {
        match intern_e_bvar(pers, st, k - 1) {
            Err(e) => Err(e),
            Ok(b) => {
                let mut o: Vec<EIdx> = out;
                o.push(b);
                stream_nested_bvars(pers, st, k - 1, o)
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/StreamRecs.lean:114-131 streamNestedOk
/// con-leche: ConLeche/Cached/IndTail.lean:66-80 streamNestedOkC
/// Lean twin: `proof/ConRon/Arena/Inductives/StreamRecs.lean:123-142 streamNestedDom` — the
/// major's domain against the firing data: its head a constant at the firing
/// levels, its arguments the pins lifted past the index binders and the index
/// variables.
pub fn stream_nested_dom(
    pers: &PersTier,
    st: &mut AState,
    dom: &EIdx,
    n: u64,
    lvls: &Vec<LIdx>,
    pins: &Vec<EIdx>,
) -> Result<bool, CheckError> {
    match expr_ops::get_app_fn(pers, st, CORE_WALK_FUEL, dom) {
        Err(e) => Err(e),
        Ok(hd) => {
            if hd.tag() == ETAG_CONST {
                match view_const(pers, st, &hd) {
                    None => fail_dangling_e(),
                    Some((_, us)) => match view_ls(pers, st, &us) {
                        Err(e) => Err(e),
                        Ok(usv) => {
                            if canon::lidx_vec_beq(&usv, lvls, 0) {
                                match expr_ops::get_app_args(pers, st, CORE_WALK_FUEL, dom) {
                                    Err(e) => Err(e),
                                    Ok(args) => match stream_nested_pins(pers, st, n, pins, 0, Vec::new()) {
                                        Err(e) => Err(e),
                                        Ok(ps) => match stream_nested_bvars(pers, st, n, ps) {
                                            Err(e) => Err(e),
                                            Ok(want) => Ok(canon::eidx_vec_beq(&args, &want, 0)),
                                        },
                                    },
                                }
                            } else {
                                Ok(false)
                            }
                        }
                    },
                }
            } else {
                Ok(false)
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/StreamRecs.lean:114-131 streamNestedOk
/// con-leche: ConLeche/Cached/IndTail.lean:66-80 streamNestedOkC
/// Lean twin: `proof/ConRon/Arena/Inductives/StreamRecs.lean:144-161 streamNestedOk` — **an
/// auxiliary recursor's type fires where the generated one does**: its major's
/// domain (binder `m_i`) is the container at the firing data's levels, applied
/// to the pins lifted past the index binders and the index variables.  `true`
/// at a member major (its rules fire `.plain`) and at `.levels`.
pub fn stream_nested_ok(
    pers: &PersTier,
    st: &mut AState,
    ty: &EIdx,
    m_i: u64,
    r_p: u64,
    fire: &IRecRuleFire,
) -> Result<bool, CheckError> {
    match fire {
        IRecRuleFire::Plain => Ok(true),
        IRecRuleFire::Levels(_) => Ok(true),
        IRecRuleFire::Nested(lvls, pins) => match expr_ops::strip_pis(pers, st, m_i, ty) {
            Err(e) => Err(e),
            Ok(None) => Ok(false),
            Ok(Some((_, rest))) => {
                if rest.tag() == ETAG_FORALL_E {
                    match view_bind(pers, st, &rest) {
                        None => fail_dangling_e(),
                        Some((dom, _)) => stream_nested_dom(pers, st, &dom, sub_nat(m_i, r_p), lvls, pins),
                    }
                } else {
                    Ok(false)
                }
            }
        },
    }
}

/// con-leche: ConLeche/Kernel/Inductives/StreamRecs.lean:133-138 generatedFire
/// con-leche: ConLeche/Cached/IndTail.lean:58-62 generatedFireC
/// Lean twin: `proof/ConRon/Arena/Inductives/StreamRecs.lean:163-170 generatedFire` — the
/// firing mode the generated recursor's rules carry at its major
/// (`rec_check::generated_rules`): `.nested` at an outside major, `.plain` at a
/// member.
pub fn generated_fire(pers: &PersTier, st: &mut AState, m: &TargetMajor, r_p: u64) -> Result<IRecRuleFire, CheckError> {
    match m.member {
        None => rec_check::aux_rule_fire(pers, st, m, r_p),
        Some(_) => Ok(IRecRuleFire::Plain),
    }
}

/// con-leche: ConLeche/Kernel/Inductives/StreamRecs.lean:140-152 streamRulesShape
/// con-leche: ConLeche/Cached/IndTail.lean:142-152 streamRulesShapeC
/// Lean twin: `proof/ConRon/Arena/Inductives/StreamRecs.lean:172-182 streamRulesShape` — the
/// record's rules' shape against the generated recursor's class, from `i` on:
/// one rule per constructor of the class, in order, each with its field count.
pub fn stream_rules_shape(rs: &Vec<IRecRule>, cs: &Vec<(IConstantVal, u64)>, i: usize) -> Result<(), CheckError> {
    if i >= rs.len() && i >= cs.len() {
        Ok(())
    } else if i >= rs.len() || i >= cs.len() {
        fail(core_types::invalid(code_points(&M_RULE_COUNT)))
    } else if rs[i].ctor.eq2(&cs[i].0.name) && rs[i].nfields == cs[i].1 {
        stream_rules_shape(rs, cs, i + 1)
    } else {
        fail(core_types::invalid(code_points(&M_RULE_SHAPE)))
    }
}

/// con-leche: ConLeche/Kernel/Inductives/StreamRecs.lean:154-165 streamRulesCheck
/// con-leche: ConLeche/Cached/IndTail.lean:154-164 streamRulesCheckC
/// Lean twin: `proof/ConRon/Arena/Inductives/StreamRecs.lean:184-197 streamRulesCheck` — the
/// record's rules' checks from `i` on: each binds its arguments
/// (`rule_binds`) and agrees with the generated right-hand side at its position
/// (a rule equal to the generated one needs no comparison).
#[allow(clippy::too_many_arguments)]
pub fn stream_rules_check(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    fe: &IFEnv,
    lps: &Vec<NIdx>,
    r_p: u64,
    rs: &Vec<IRecRule>,
    gs: &Vec<EIdx>,
    i: usize,
) -> Result<(), CheckError> {
    if i >= rs.len() && i >= gs.len() {
        Ok(())
    } else if i >= rs.len() || i >= gs.len() {
        fail(core_types::internal(code_points(&M_RULES_GEN)))
    } else {
        match rec_check::rule_binds(pers, st, r_p, &rs[i]) {
            Err(e) => Err(e),
            Ok(()) => {
                if rs[i].rhs.eq2(&gs[i]) {
                    stream_rules_check(pers, st, mode, fe, lps, r_p, rs, gs, i + 1)
                } else {
                    match rule_agree(pers, st, mode, fe, lps, &rs[i].rhs, &gs[i]) {
                        Err(e) => Err(e),
                        Ok(()) => stream_rules_check(pers, st, mode, fe, lps, r_p, rs, gs, i + 1),
                    }
                }
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/StreamRecs.lean:167-172 streamRecCompare
/// con-leche: ConLeche/Cached/IndTail.lean:166-171 streamRecCompareC
/// Lean twin: `proof/ConRon/Arena/Inductives/StreamRecs.lean:199-207 streamRecCompare` — **the
/// comparison of one recursor**: its type unless it is the generated one, and
/// its rules.
pub fn stream_rec_compare(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    fe: &IFEnv,
    rc: &RecShape,
    g: &(IConstantVal, TargetMajor, Vec<EIdx>),
) -> Result<(), CheckError> {
    if rc.cv_r.ty.eq2(&g.0.ty) {
        stream_rules_check(pers, st, mode, fe, &g.0.level_params, rc.r_p, &rc.rules, &g.2, 0)
    } else {
        match rec_ty_check(pers, st, mode, fe, &g.0.level_params, rc.m_i + 1, &rc.cv_r.ty, &g.0.ty) {
            Err(e) => Err(e),
            Ok(()) => stream_rules_check(pers, st, mode, fe, &g.0.level_params, rc.r_p, &rc.rules, &g.2, 0),
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/StreamRecs.lean:174-183 streamRecCheck
/// con-leche: ConLeche/Cached/IndTail.lean:173-180 streamRecCheckC
/// Lean twin: `proof/ConRon/Arena/Inductives/StreamRecs.lean:209-219 streamRecCheck` — **one
/// recursor, the stream's against the generated one**: the rules' shape and the
/// record's major's container, then the comparison.
pub fn stream_rec_check(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    fe: &IFEnv,
    rc: &RecShape,
    g: &(IConstantVal, TargetMajor, Vec<EIdx>),
) -> Result<(), CheckError> {
    match stream_rules_shape(&rc.rules, &g.1.ctors, 0) {
        Err(e) => Err(e),
        Ok(()) => match generated_fire(pers, st, &g.1, rc.r_p) {
            Err(e) => Err(e),
            Ok(fire) => match stream_nested_ok(pers, st, &rc.cv_r.ty, rc.m_i, rc.r_p, &fire) {
                Err(e) => Err(e),
                Ok(false) => fail(core_types::invalid(code_points(&M_NESTED))),
                Ok(true) => stream_rec_compare(pers, st, mode, fe, rc, g),
            },
        },
    }
}

/// con-leche: ConLeche/Kernel/Inductives/StreamRecs.lean:185-193 streamRecsCheck
/// con-leche: ConLeche/Cached/IndTail.lean:182-189 streamRecsCheckC
/// Lean twin: `proof/ConRon/Arena/Inductives/StreamRecs.lean:221-231 streamRecsCheck` — **the
/// block's recursors against the generated ones**, record by record from `i` on
/// (the generated family is in the records' order).
pub fn stream_recs_check(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    fe: &IFEnv,
    rcs: &Vec<RecShape>,
    gs: &Vec<(IConstantVal, TargetMajor, Vec<EIdx>)>,
    i: usize,
) -> Result<(), CheckError> {
    if i >= rcs.len() && i >= gs.len() {
        Ok(())
    } else if i >= rcs.len() || i >= gs.len() {
        fail(core_types::internal(code_points(&M_FAMILY)))
    } else {
        match stream_rec_check(pers, st, mode, fe, &rcs[i], &gs[i]) {
            Err(e) => Err(e),
            Ok(()) => stream_recs_check(pers, st, mode, fe, rcs, gs, i + 1),
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/StreamRecs.lean:195-211 streamKCheck
/// Lean twin: `proof/ConRon/Arena/Inductives/StreamRecs.lean:233-248 streamKCheck` — **the
/// records' K flags against the block**, from `i` on: each record's flag is the
/// one the generated recursor has (`rec_check::rec_k_expected`), and at a block
/// whose recursors carry no rules (`block_shape::no_rules`) a record with rules
/// is rejected.  The shorter of the two lists decides, as the cited catch-all
/// `| _, _ => pure ()` does.
pub fn stream_k_check(
    p: &BlockShape,
    rcs: &Vec<RecShape>,
    gs: &Vec<(IConstantVal, TargetMajor, Vec<EIdx>)>,
    i: usize,
) -> Result<(), CheckError> {
    if i >= rcs.len() || i >= gs.len() {
        Ok(())
    } else if block_shape::no_rules(p) && rcs[i].rules.len() != 0 {
        fail(core_types::invalid(code_points(&M_RULES_NO_LARGE)))
    } else if rcs[i].is_k == rec_check::rec_k_expected(p, &gs[i].1) {
        stream_k_check(p, rcs, gs, i + 1)
    } else {
        fail(core_types::invalid(code_points(&M_K_FLAG)))
    }
}

// ---------------------------------------------------------------------------
// The declared feature flags
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/Inductives/StreamRecs.lean:219-235 memberFlagsCheck
/// Lean twin: `proof/ConRon/Arena/Inductives/StreamRecs.lean:252-277 memberFlagsCheck` — **one
/// member's flags** (official's checks of lean4 PR #16595): `is_k` only at the
/// first member of a block of one, a proposition with one constructor without
/// fields; `has_projections` only at one constructor, no index, not
/// impredicative; `has_eta` only with `has_projections`, at a block that is
/// not recursive.
pub fn member_flags_check(p: &BlockShape, is_rec: bool, i: u64, ms: &MemberShape, f: &IndFlags) -> Result<(), CheckError> {
    let one: bool = ms.ctors.len() == 1;
    let k_ok: bool = if i == 0 && block_shape::shape_k(p) == 1 && p.is_prop && one {
        ms.ctors[0].1 == 0
    } else {
        false
    };
    let proj_ok: bool = if one && ms.n_idx == 0 {
        if f.is_impredicative {
            false
        } else {
            true
        }
    } else {
        false
    };
    let eta_ok: bool = if f.has_projections {
        if is_rec {
            false
        } else {
            true
        }
    } else {
        false
    };
    if f.is_k && !k_ok {
        fail(core_types::invalid(code_points(&M_FLAG_K)))
    } else if f.has_projections && !proj_ok {
        fail(core_types::invalid(code_points(&M_FLAG_PROJ)))
    } else if f.has_eta && !eta_ok {
        fail(core_types::invalid(code_points(&M_FLAG_ETA)))
    } else {
        Ok(())
    }
}

/// con-leche: ConLeche/Kernel/Inductives/StreamRecs.lean:237-243 membersFlagsCheck
/// Lean twin: `proof/ConRon/Arena/Inductives/StreamRecs.lean:279-287 membersFlagsCheck` — the
/// members' flags, from position `i` on, pairwise, stopping at the shorter
/// list.
pub fn members_flags_check(
    p: &BlockShape,
    is_rec: bool,
    i: usize,
    ms: &Vec<MemberShape>,
    fl: &Vec<IndFlags>,
) -> Result<(), CheckError> {
    if i >= ms.len() || i >= fl.len() {
        Ok(())
    } else {
        match member_flags_check(p, is_rec, i as u64, &ms[i], &fl[i]) {
            Err(e) => Err(e),
            Ok(()) => members_flags_check(p, is_rec, i + 1, ms, fl),
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/StreamRecs.lean:245-288 blockFlagsCheck
/// Lean twin: `fl.all fun f => f.isImpredicative == f0.isImpredicative &&
/// f.hasLargeElim == f0.hasLargeElim`, from `i` on.
pub fn flags_uniform(fl: &Vec<IndFlags>, f0: &IndFlags, i: usize) -> bool {
    if i >= fl.len() {
        true
    } else if fl[i].is_impredicative == f0.is_impredicative && fl[i].has_large_elim == f0.has_large_elim {
        flags_uniform(fl, f0, i + 1)
    } else {
        false
    }
}

/// con-leche: ConLeche/Kernel/Inductives/StreamRecs.lean:245-288 blockFlagsCheck
/// Lean twin: `proof/ConRon/Arena/Inductives/StreamRecs.lean:289-303 largeElimFlagOk` — is
/// the declared `has_large_elim` allowed?  Only at a block that is not
/// impredicative and whose sort is never zero, or of one type with no
/// constructor, or with one constructor and `has_eta` or `is_k`.  The sort is
/// read only where the flag is on and the block not impredicative.
pub fn large_elim_flag_ok(pers: &PersTier, st: &mut AState, p: &BlockShape, f0: &IndFlags) -> Result<bool, CheckError> {
    if f0.has_large_elim {
        if f0.is_impredicative {
            Ok(false)
        } else {
            match read_level_m(pers, st, &p.res_sort) {
                Err(e) => Err(e),
                Ok(l) => {
                    if level::is_never_zero(&l) {
                        Ok(true)
                    } else {
                        let n: u64 = block_shape::shape_num_ctors(p);
                        Ok(block_shape::shape_k(p) == 1 && (n == 0 || (n == 1 && (f0.has_eta || f0.is_k))))
                    }
                }
            }
        }
    } else {
        Ok(true)
    }
}

/// con-leche: ConLeche/Kernel/Inductives/StreamRecs.lean:245-288 blockFlagsCheck
/// Lean twin: `proof/ConRon/Arena/Inductives/StreamRecs.lean:305-325 majorsFlagsCheck` — the
/// cited `for M in Ms do`, from class `i` on: an outside class that is a
/// proposition with one constructor without fields is rejected, and so is an
/// outside class with a projection table (`hasProj`, the environment's
/// `findTable?`) at an impredicative block.
pub fn majors_flags_check(
    pers: &PersTier,
    p: &BlockShape,
    f0: &IndFlags,
    ms: &Vec<TargetMajor>,
    fe: &IFEnv,
    i: usize,
) -> Result<(), CheckError> {
    if i >= ms.len() {
        Ok(())
    } else {
        match ms[i].member {
            Some(_) => majors_flags_check(pers, p, f0, ms, fe, i + 1),
            None => {
                let k_shape: bool = if p.is_prop && ms[i].ctors.len() == 1 {
                    ms[i].ctors[0].1 == 0
                } else {
                    false
                };
                if k_shape {
                    fail(core_types::invalid(code_points(&M_FLAG_NEST_K)))
                } else if f0.is_impredicative {
                    match env::ifenv_find_table(pers, fe, &ms[i].ind) {
                        Some(_) => fail(core_types::invalid(code_points(&M_FLAG_NEST_PROJ))),
                        None => majors_flags_check(pers, p, f0, ms, fe, i + 1),
                    }
                } else {
                    majors_flags_check(pers, p, f0, ms, fe, i + 1)
                }
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/StreamRecs.lean:245-288 blockFlagsCheck
/// Lean twin: `proof/ConRon/Arena/Inductives/StreamRecs.lean:327-361 blockFlagsCheck` — **the
/// block's declared feature flags, validated** (lean4 PR #16595; nothing at
/// a block without them): `is_impredicative` and `has_large_elim` agree
/// across the block; `is_impredicative` only at a proposition;
/// `has_large_elim` is what the recursor records eliminate at, and allowed
/// only where `large_elim_flag_ok` says; the members' own flags; the outside
/// classes (`majors_flags_check`).  `is_rec` is official's `is_rec`, `ms` the
/// classes the recursors eliminate, `fe` the environment whose projection
/// tables say whether a stored type has projections.  A handle read (the
/// sort), so it takes the state and fails in it, where the cited pure check
/// is run through `ofExcept`.
pub fn block_flags_check(
    pers: &PersTier,
    st: &mut AState,
    p: &BlockShape,
    is_rec: bool,
    ms: &Vec<TargetMajor>,
    fe: &IFEnv,
) -> Result<(), CheckError> {
    match &p.flags {
        None => Ok(()),
        Some(fl) => {
            let f0: IndFlags = if fl.len() == 0 {
                IndFlags {
                    is_impredicative: false,
                    is_k: false,
                    has_projections: false,
                    has_eta: false,
                    has_large_elim: false,
                }
            } else {
                ind_flags_dup(&fl[0])
            };
            if fl.len() as u64 != block_shape::shape_k(p) {
                fail(core_types::internal(code_points(&M_FLAGS_COUNT)))
            } else if !flags_uniform(fl, &f0, 0) {
                fail(core_types::invalid(code_points(&M_FLAGS_DISAGREE)))
            } else if f0.is_impredicative && !p.is_prop {
                fail(core_types::invalid(code_points(&M_FLAG_IMPRED)))
            } else if f0.has_large_elim != p.large {
                fail(core_types::invalid(code_points(&M_FLAG_LARGE_REC)))
            } else {
                match large_elim_flag_ok(pers, st, p, &f0) {
                    Err(e) => Err(e),
                    Ok(false) => fail(core_types::invalid(code_points(&M_FLAG_LARGE))),
                    Ok(true) => match members_flags_check(p, is_rec, 0, &p.members, fl) {
                        Err(e) => Err(e),
                        Ok(()) => majors_flags_check(pers, p, &f0, ms, fe, 0),
                    },
                }
            }
        }
    }
}
